module DefinitionElaboration where 

import qualified Presyntax as R 
import Common
import Syntax 
import Value
import Definition
import qualified Elaboration as E
import Evaluation
import Cxt
import Cxt.Type
import qualified Data.Map.Strict as M
import Errors
import Control.Exception
import Control.Monad (forM, when, unless)
import GHC.Stack (HasCallStack)
import Pretty (displayMetas)
import Data.IORef (readIORef)
import Metacontext (nextMeta)
import System.Exit (exitSuccess)

-- Check the Pattern Matching
-------------------------------
{-
Consider the following function definition:

```
f : (x : A) (y : B) (z : C) -> D 
f p1 p2 p3 = rhs
```

Each pattern corresponds to a variable in the telescope.
The former pattern will affect the later types. 
For example, when we matching `x` with the pattern `p1`, the later type becomes `(y : B[p1/x]) (z : C[p1/x]) -> D[p1/x]`.
After all three patterns are matched, we check `rhs : D [p1/x] [p2/y] [p3/z]`.

On the other hand, we need to consider the dependency of the patterns.
The former variable pattern can be re-assigned by the later patterns.
Many systems use special annotations to indicate patterns that are assigned values, commonly referred to as Inaccessible Patterns.
We do not use inaccessible patterns here, simply using variable patterns instead and adding new bindings in rhs Cxt.

For example,

```
sym : (x y : A) -> x = y -> y = x
sym x y (refl u) = ?0
```

The rhs looks like,

x = u : A
y = u : A
u : A
-----------
?0 : u = u

Using de Bruijn index and level, it looks like,

Name  | Index  | Val (Level)
-------------------------------
u     | 0      | VVar 2
y     | 1      | VVar 2 
x     | 2      | VVar 2

The weired thing is that the some of the outer variables are assigned by inner values.
This would not be a problem when we implementing it, since we are using de Bruijn levels as values.
-}

data UnifRes 
  = UnifOk Cxt 
  | UnifStuck  -- When Agda would say : I'm not sure if there should be a case for the constructor 
  | UnifFail   -- Absurd pattern

-- unify ctx u v t = ctx'
-- 其中 ctx 是当前语境, u 和 v 是我们试图 unify 的两个值, t 是它们的类型, ctx' 是 unify 之后的新语境, 
-- 我们要更新被 unify 的变量之后的语境部分. 
unify :: Cxt -> Val -> Val -> VTy -> IO UnifRes
unify ctx u v t = 
  case (force' ctx u, force' ctx v) of
    (VVar x, v)
      | x `notElem` fv (defs ctx) (lvl ctx) v ->
          pure . UnifOk $ updateCxt ctx x v
    (v, VVar x)
      | x `notElem` fv (defs ctx) (lvl ctx) v ->
          pure . UnifOk $ updateCxt ctx x v
    (VCons c us, VCons c' vs)
      | consName c == consName c' ->
          unifySp ctx us vs $ evalCxt ctx (consType c)
      | otherwise -> pure UnifFail
    (u, v) -> 
      (E.unify (defs ctx) (env ctx) (lvl ctx) u v >> pure (UnifOk ctx))
      `catch` \ UnifyError -> 
          pure UnifStuck

unifySp :: HasCallStack => Cxt -> Spine -> Spine -> VTy -> IO UnifRes
unifySp ctx us vs ts = case (reverse us, reverse vs, ts) of
  ([], [], _) -> pure $ UnifOk ctx
  ((force' ctx -> u,i1):us, (force' ctx -> v, i2):vs, VPi x i3 t b) | i1 == i2 && i2 == i3 -> do
    uni_res <- unify ctx (updateVal ctx u) (updateVal ctx v) t
    case uni_res of 
      UnifOk ctx' -> 
        let u' = updateVal ctx' u in 
        unifySp ctx' us vs ((defs ctx, b) $$ u')
      e -> pure e
  _ -> throwIO $ DefError ctx $ PatArgMismatch

freshVal :: Defs -> [Val] -> [Val] -> Val -> Val 
freshVal def from to = eval def to . quote def from (Lvl (length from))

-- Note. This is a very bad function, it refresh the hole context.
updateCxt :: Cxt -> Lvl -> Val -> Cxt
updateCxt ctx x v = if length env' /= length bds' then error "!!!" else ctx {env = env', types = typ', bds = bds'} where
  env1 = env ctx
  typ = types ctx
  def = defs ctx
  x' = unIx $ lvl2Ix (lvl ctx) x
  (postenv, xval_old:prenv) = splitAt x' env1

  changeTail :: [a] -> [a] -> [a]
  changeTail orig new = take (length orig - length new) orig ++ new

  -- 只更换了 x 的值的语境.
  env2 = postenv ++ v : prenv 

  -- 用上面那个语境去更新被他影响到的语境.
  -- 注意前方的语境也可能被影响, 所以这里需要对语境整体进行刷新.
  -- 先前的版本只更新了后方的语境.
  refresh :: [Val] -> Types -> ([Val], Types) 
  refresh [] [] = ([], [])
  refresh (v:es) ((x,ori,t):tys) = 
    let (es', tys') = refresh es tys 
        env'' = changeTail env2 es' 
    in (freshVal def env1 env'' v :es', (x, ori,freshVal def env1 env'' t): tys')
  refresh _ _ = error "refresh: impossible"

  (env', typ') = refresh env1 typ 

  genBDs :: [(Ix, Val)] -> [BD]
  genBDs = map checkBD where 
    checkBD (ix, VVar lv) | ix == lvl2Ix (lvl ctx) lv = Bound
    checkBD _ = Defined
  
  bds' = genBDs [ (Ix x, v) | (x, v) <- zip [0 .. length env' - 1] env' ]

-- | Pattern match against given type, returning the rest type (rhs type) and rhs Cxt.
checkPat :: Bool -> Cxt -> RPatterns -> VTy -> IO ([(Pattern, Icit)], Cxt, VTy)
checkPat isCons ctx [] ty 
  | isCons = case force' ctx ty of 
      VPi x Impl a b -> do
        let ctx' = bind ctx ('_':x) a
        let b' = (defs ctx, b) $$ VVar (lvl ctx)
        (rps, rctx, rty) <- checkPat isCons ctx' [] b'
        pure ((PatVar ('_':x), Impl): rps, rctx, rty)
      _ -> pure ([], ctx, ty)
  | otherwise = pure ([], ctx, ty)
checkPat isCons ctx ((Right i, RPat c c_arg):ps) (force' ctx -> VPi x' i' (force' ctx -> a) b) | i == i' =
  case M.lookup c (defs ctx) of
    Just (DefCons _) -> 
      case a of
        VData d d_arg -> do
          (c_tele, c_ix) <- case lookupCons d c of
            Just r -> pure r  
            Nothing -> throwIO $ DefError ctx $ NameIsNotCons c (Just d)
          let c_ty = evalCxt ctx $ getConsType d c_tele c_ix
          (ps', ctx', c_ty') <- checkPat True ctx c_arg c_ty
          d_arg' <- case c_ty' of
            VData _ x -> pure x
            e -> throwIO $ DefError ctx $ PMNoneData (quoteCxt ctx' e)
          let d_type = evalCxt ctx' (dataType d)
          -- Here we try to unify the returning indexes of constructor pattern with the type
          uni_res <- unifySp ctx' d_arg d_arg' d_type
          ctx'' <- case uni_res of
            UnifOk c -> pure c
            UnifStuck -> throwIO $ DefError ctx $ UnsurePattern c (quoteCxt ctx a)
            UnifFail -> throwIO $ DefError ctx $ WrongPattern c (quoteCxt ctx a)
          -- b_rest is using an old Cxt in its closure, so we need to update it.
          -- So we have to refresh the Cxt.
          -- Note. Here p2v start from the level of ctx, not ctx''.
          let p = PatCon c ps'
          let patVal = p2v (defs ctx'') (lvl ctx) p
          let patVal' = evalCxt ctx'' (quoteCxt ctx'' patVal)
          let b_rest = (defs ctx'', b) $$ patVal'
          let b_rest_updated = evalCxt ctx'' (quoteCxt ctx'' b_rest)
          (rps, rctx, rty) <- checkPat isCons ctx'' ps b_rest_updated
          pure ((p, i) : rps, rctx, rty)
        _ -> throwIO $ DefError ctx $ PMNoneData (quoteCxt ctx a)
    _ | null c_arg    -> do -- Var pattern.
          let x = c
          let ctx' = bind ctx x a
          let b' = (defs ctx, b) $$ VVar (lvl ctx)
          (ps', rest, rhs) <- checkPat isCons ctx' ps b'
          pure ((PatVar x, i):ps', rest, rhs)
      | otherwise     -> throwIO $ DefError ctx $ NameIsNotCons c Nothing
checkPat isCons ctx ps@((Left x, p):ps') (force' ctx -> VPi x' i' (force' ctx -> a) b) 
  | i' == Impl && x == x' = checkPat isCons ctx ((Right Impl, p):ps') (VPi x' Impl a b) -- Jump to the former clause
  | otherwise             = do
      let ctx' = bind ctx ('_':x') a
      let b' = (defs ctx, b) $$ VVar (lvl ctx)
      (rps, rctx, rty) <- checkPat isCons ctx' ps b'
      pure ((PatVar ('_':x'), Impl): rps, rctx, rty)
checkPat isCons ctx ps@((Right Expl, _):ps') (force' ctx -> VPi x' Impl (force' ctx -> a) b) = do
    let ctx' = bind ctx ('_':x') a
    let b' = (defs ctx, b) $$ VVar (lvl ctx)
    (rps, rctx, rty) <- checkPat isCons ctx' ps b'
    pure ((PatVar ('_':x'), Impl): rps, rctx, rty)
checkPat isCons ctx ps t = throwIO $ DefError ctx $ PatArgMismatch

checkCls :: HasCallStack => Cxt -> Id -> Ty -> RClause -> IO Clause
checkCls ctx func_name func_typ (RClause rps rhs) = do
  let func_typ' = evalCxt ctx func_typ
  (ps, ctx', rhs_ty) <- checkPat False ctx rps func_typ'
  rhs' <- E.check ctx' rhs rhs_ty
  let rhs'' = nf (defs ctx') (env ctx') rhs'
  -- NOTE. The @nf@ here should remove all the metas.
  if noMetas rhs'' then 
    pure $ Clause ps rhs''
  else do
    throwIO $ DefError ctx $ UnsolvedMetaInFuncDef func_name


checkFunc1 :: Cxt -> RFuncDef -> IO FuncDef
checkFunc1 ctx (RFuncDef func_name func_typ cls) = do 
  func_typ' <- E.check ctx func_typ VU
  let func_typ'' = nf (defs ctx) (env ctx) func_typ'
  unless (noMetas func_typ'') $ do 
    throwIO $ DefError ctx $ UnsolvedMetaInFuncDef func_name
  let go = \case 
        [] -> pure [] 
        (rcls : rrest) -> do 
          cls <- checkCls ctx func_name func_typ'' rcls
          rest <- go rrest 
          pure $ cls : rest
  cls' <- go cls
  pure $ FuncDef func_name func_typ'' cls'

insertFunc :: Defs -> FuncDef -> Defs
insertFunc defs func = M.insert (funcName func) (DefFunc func) defs

checkFunc ::  Cxt -> RFuncDef -> IO FuncDef
checkFunc ctx rfun = do 
  m <- readIORef nextMeta
  prefun <- checkFunc1 ctx (rfun {funcClausesR = []}) -- this allowing recursion.
  fun <- checkFunc1 (ctx {defs = M.insert (funcNameR rfun) (DefFunc prefun) (defs ctx)}) rfun 
  -- TODO : Check Coverage.
  -- putStrLn $ showFunc fun
  pure fun

-- Check Data Definitions
----------------------------
insertData :: Defs -> DataDef -> Defs
insertData defs dat = M.insert (dataName dat) (DefData dat) defs

checkData :: SourcePos -> Defs -> RDataDef -> IO DataDef
checkData s defs rdat = do
    ix_ty <- E.check (emptyCxt s){defs = defs} (dataIxR rdat) VU >>= checkIx . nf defs []
    -- (snd -> ix_ty) <- checkTelescope  ()
    let defs' = insertData defs (DataDef (dataNameR rdat) ix_ty [])
    cons <- forM (dataConsR rdat) $ \(n, t) -> do
      t' <- nf defs' [] <$> (E.check (emptyCxt s){defs = defs'} t VU)
      checkCons defs' ix_ty n t'
    pure (DataDef (dataNameR rdat) ix_ty cons) 
  where 
    goPi :: Tm -> (Telescope, Tm)
    goPi (Pi x i t b) = ((x,i,t) : fst (goPi b), snd (goPi b))
    goPi b = ([], b)

    goApp :: Tm -> Maybe TSpine
    goApp (App a b i) = do 
      as <- goApp a 
      pure (as :> (b,i))
    goApp (Call n) 
      | n == dataNameR rdat = Just [] 
    goApp _ = Nothing

    go :: Tm -> Maybe (Telescope, TSpine)
    go tm = do 
      let (ts, r) = goPi tm 
      as <- goApp r 
      pure (ts, as)

    checkIx :: Tm -> IO Telescope
    checkIx tm = case goPi tm of 
      (ix, U) -> pure ix 
      _ -> throwIO $ DefError ((emptyCxt s){defs = defs}) $ DataMustInU (dataNameR rdat)
    
    checkCons :: Defs -> Telescope -> Name -> Tm -> IO (Name, Telescope, TSpine)
    checkCons defs ix_ty c ty = do 
      case go ty of 
        Nothing -> throwIO $ DefError ((emptyCxt s){defs = defs}) $ ConstructorMustReturnData c 
        Just (ts, ret_ix) -> pure (c, ts, ret_ix)

getConstructors :: DataDef -> [(Name, ConsDef)]
getConstructors dat = map go (dataCons dat) where 
  
  go (c, ts, ix) = (c, ConsDef c dat (go1 ts (go2 (Call (dataName dat)) ix)))

  go1 [] c = c 
  go1 ((x, i, t):xs) c = Pi x i t $ go1 xs c
  
  go2 c [] = c
  go2 c (as :> (a, i)) = App (go2 c as) a i 

insertCons :: Defs -> [(Name, ConsDef)] -> Defs
insertCons = foldl (\d (c, def) -> M.insert c (DefCons def) d) 

checkProg' :: Defs -> Program -> IO Defs 
checkProg' defs [] = pure defs
checkProg' defs ((sp, d):ds) = case d of 
  RDefFunc d -> do 
    f <- checkFunc ((emptyCxt sp){defs = defs}) d 
    checkProg' (insertFunc defs f) ds
  RDefData d -> do 
    d <- checkData sp defs d 
    checkProg' (insertCons (insertData defs d) (getConstructors d)) ds
  RDefMutual mb -> do
    let sigs = mutualSig mb
    let bodys = mutualBody mb
    defs' <- insertMutualSig defs sigs
    defs'' <- insertMutualBody defs' (map snd sigs) bodys
    checkProg' defs'' ds
  
insertMutualSig :: Defs -> [(SourcePos, Header)] -> IO Defs
insertMutualSig defs = \case 
  [] -> pure defs 
  (sp, h) : rest -> case h of 
    FunHeader name ty -> do 
      checkFunc1 ((emptyCxt sp){defs = defs}) (RFuncDef name ty []) >>= \ f -> 
        insertMutualSig (insertFunc defs f) rest
    DataHeader name ty -> do
      checkData sp defs (RDataDef name ty []) >>= \ d ->
        insertMutualSig (insertData defs d) rest

lookupHeader :: Cxt -> Name -> [Header] -> IO Header 
lookupHeader cxt n = \case 
  [] -> throwIO $ DefError cxt $ NameNotFoundOrMismatch n
  (h:hs) -> case h of 
    FunHeader name ty | name == n -> pure h
    DataHeader name ty | name == n -> pure h
    _ -> lookupHeader cxt n hs

insertMutualBody :: Defs -> [Header] -> [(SourcePos, Body)] -> IO Defs
insertMutualBody defs headers = \case
  [] -> pure defs 
  (sp, b) : rest -> case b of 
    FunBody name cls -> do 
      h <- lookupHeader ((emptyCxt sp){defs = defs}) name headers
      case h of 
        FunHeader _ ty -> do 
          f <- checkFunc1 ((emptyCxt sp){defs = defs}) (RFuncDef name ty cls)
          insertMutualBody (insertFunc defs f) headers rest
        _ -> throwIO $ DefError ((emptyCxt sp){defs = defs}) $ NameNotFoundOrMismatch name
    DataBody name cons -> do 
      h <- lookupHeader ((emptyCxt sp){defs = defs}) name headers
      case h of 
        DataHeader _ ty -> do 
          d <- checkData sp defs (RDataDef name ty cons)
          insertMutualBody (insertCons (insertData defs d) (getConstructors d)) headers rest
        _ -> throwIO $ DefError ((emptyCxt sp){defs = defs}) $ NameNotFoundOrMismatch name

checkProg :: HasCallStack => String -> Defs -> Program -> IO Defs 
checkProg src defs prog = checkProg' defs prog `catch` \ e -> do 
  displayError src e 
  exitSuccess
  