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
import Control.Monad (forM, when, unless, join, forM_)
import GHC.Stack (HasCallStack)
import Pretty (displayMetas)
import Data.IORef (readIORef)
import Metacontext (nextMeta)
import Debug.Trace (trace)
import GHC.IO (unsafePerformIO)

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
-- Here ctx is the current context, u and v are the two values we are trying to unify,
-- t is their type, and ctx' is the context after unification.
-- We need to update the portion of the context that comes after the unified variable.
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
  ((force' ctx -> u, i1):us, (force' ctx -> v, i2):vs, VPi x i3 t b) | i1 == i2 -> do
    uni_res <- unify ctx (updateVal ctx u) (updateVal ctx v) t
    case uni_res of 
      UnifOk ctx' -> 
        let u' = updateVal ctx' u in 
        unifySp ctx' us vs ((defs ctx, b) $$ u')
      e -> pure e
  -- ((force' ctx -> u, i1):us, (force' ctx -> v, i2):vs, VPi x i3 t b) -> do 
  --   -- print all the arguments
  --   putStrLn $ showVal ctx u ++ " " ++ show i1
  --   putStrLn $ showVal ctx v ++ " " ++ show i2
  --   putStrLn $ showVal ctx t ++ " " ++ show i3
  --   putStrLn x
  --   error "!!!!"
  _ -> throwIO $ DefError ctx $ PatArgMismatch

freshVal :: Defs -> [Val] -> [Val] -> Val -> Val 
freshVal def from to = eval def to . quote def from (Lvl (length from))

-- Note. This is a very bad function, it refresh the hole context.
-- But I can't figure out a better way now.
-- The Context in this project is not very well formed for most cases.
-- For example, we may have a context: `cxt, x : A, cxt'` where `A` may refer to variables in `cxt'`.
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

  -- Use the context above to update the parts of the context affected by it.
  -- Note that earlier parts of the context may also be affected, so we need to refresh the entire context here.
  -- The previous version only updated the later part of the context.
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

-- Pattern match against given type, returning the rest type (rhs type) and rhs Cxt.
-- isCons = True, if we are elaborating the patterns of a constructor.
-- Throws `Error`, throw `DefError _ $ WrongPattern _ _` for absurd patterns, `DefError _ $ UnsurePattern _ _` for IDK patterns.
-- TODO : Change the return type to `IO ([(Pattern, Icit)], Spine, Cxt, VTy)`
checkPat :: Bool -> Cxt -> RPatterns -> VTy -> IO ([(Pattern, Icit)], Cxt, VTy)
checkPat isCons ctx [] ty 
  | isCons = case force' ctx ty of -- If we are elaborating constructor patterns, we need to make sure all implicit patterns are filled.
      VPi x Impl a b -> do
        let ctx' = bind ctx ('_':x) a
        let b' = (defs ctx', b) $$ VVar (lvl ctx)
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

          -- trace ("At") $ pure ()
          -- trace (showVal ctx' a) $ pure ()
          -- trace (showVal ctx' c_ty') $ pure ()
          -- trace (showVal ctx' d_type) $ pure ()
          
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
    -- Coverage Check
    let defs' = insertFunc defs f
    checkFuncCover sp defs' (funcName f)
    checkProg' defs' ds
  RDefData d -> do 
    d <- checkData sp defs d 
    checkProg' (insertCons (insertData defs d) (getConstructors d)) ds
  RDefMutual mb -> do
    let sigs = mutualSig mb
    let bodys = mutualBody mb
    defs' <- insertMutualSig defs sigs
    defs'' <- insertMutualBody defs' (map snd sigs) bodys
    -- Coverage Check 
    forM_ sigs $ \ (_, h) -> case h of 
      FunHeader name _ -> checkFuncCover sp defs'' name
      _ -> pure ()
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
  throwIO e

-- Coverage Checking
-------------------------------

type ClauseLHS = [(Pattern, Icit)]

type MissingPattern = [Spine]

data CoverCheckingError = CoverMissPat MissingPattern | MeetIDKCons 
  deriving (Show)

data CoverRes 
  = CoverOk
  | CoverStuck Lvl -- Which variable is stuck
  | CoverFail [(Cxt, Spine)] -- Meet a dead end

checkFuncCover :: SourcePos -> Defs -> Name -> IO () 
checkFuncCover srcpos defs fname = do 
    case checkFuncCover' srcpos defs fname of 
      Left (CoverMissPat ps) -> do 
        putStrLn $ "Error: function " ++ fname ++ " is not exhaustive."
        putStrLn $ "Missing the following " ++ show (length ps) ++ " pattern(s):"
        forM_ ps $ \sp -> 
          putStrLn $ " " ++ printSp sp 
      Left MeetIDKCons -> putStrLn $ "Error: cannot check exhaustiveness for function " ++ fname ++ " due to unknown existance of some constructors."
      Right () -> pure ()
  where 
    printSp :: Spine -> String 
    printSp = \case 
      [] -> "" 
      rest :> (VCons c sp', i) -> printSp rest ++ " " ++ q i (consName c ++ printSp sp')
      rest :> (v, i) -> printSp rest ++ " " ++ q i "_"
      where 
        q Impl s = "{" ++ s ++ "}"
        q Expl s = "(" ++ s ++ ")"


checkFuncCover' :: SourcePos -> Defs -> Name -> Either CoverCheckingError ()
checkFuncCover' srcpos defs fname = do 
    case M.lookup fname defs of 
      Just (DefFunc f@(FuncDef _ fty (map clausePatterns -> ps))) -> do        
        checkCover ((emptyCxt srcpos) {defs = defs}) (eval defs [] fty) (arity f) ps
      _ -> error " impossible"

checkCover :: Cxt -> VTy -> Int -> [ClauseLHS] -> Either CoverCheckingError ()
checkCover ctx fty arity clss = case testManySpine (defs ctx) clss [initSp] of
    Nothing -> Left MeetIDKCons
    Just [] -> Right ()
    Just sp -> Left . CoverMissPat $ map snd sp
  where 
    genInitSpine :: Cxt -> VTy -> Int -> (Cxt, Spine)
    genInitSpine cxt ty 0 = (cxt, [])
    genInitSpine cxt (force' cxt -> VPi x i a b) arity = 
      let (cxt', sp) = genInitSpine (bind cxt ("_cov_chk_"++x) a) ((defs cxt, b) $$ VVar (lvl cxt)) (arity - 1)
      in (cxt', sp ++ [(VVar (lvl cxt), i)]) -- TODO: Spine is reversed, change to normal list one day. 
    genInitSpine _ _ _ = error "genInitSpine: impossible"

    initSp = genInitSpine ctx fty arity

-- Given a `x in ctx`, where `ctx |- x : D args`, where D is a data type,
-- returns all possible context for splitting `x`.
-- For example,  
-- if `ctx |- x : Nat`, then `splitCxt ctx x = Just [ctx [x |-> zero], ctx [x |-> suc (VVar y)]]` where `y : Nat` is a fresh variable. 
-- Return `Nothing`, if there is one or more IDK constructors. 
splitCxt :: Cxt -> Lvl -> Maybe [Cxt]
splitCxt cxt x = case force' cxt (E.findType cxt x) of
  x_ty@(VData d d_arg) -> might $ do 
    fmap join $ forM (dataCons d) $ \c@(c_name, c_tele, c_ix) -> do 
          -- split x to constructor c
          -- make a raw pattern
          let makePs :: Telescope -> RPatterns 
              makePs [] = []
              makePs ((x, i, _):xs) = (Right i, RPat ("_cov_chk_"++x) []) : makePs xs
          let p = RPat c_name (makePs c_tele)
          -- check the pattern against x's type
          cp <- (checkPat False cxt [(Right Expl, p)] (VPi "_" Expl x_ty (Closure (env cxt) U)) >>= pure . Just)
                                `catch` \case 
                                  DefError _ (UnsurePattern _ _) -> quitMight
                                  DefError _ (WrongPattern _ _) -> pure Nothing
                                  e -> error $ "impossible: " ++  show e
          case cp of 
            Nothing -> pure []
            Just ([(p', _)], cxt', _) -> do 
              let pv = p2v (defs cxt) (lvl cxt) p'
              let cxt'' = updateCxt cxt' x pv
              pure [cxt'']
            _ -> error "splitCxt: impossible"
  _ -> error "splitCxt: impossible"

-- Check a list of clause lhs against a spine
-- If the spine can be matched by the patterns, return ()
-- If stucked, split the stucked variable of the spine.
-- If fails, move to next clause lhs.
testSpine :: Defs -> [ClauseLHS] -> Cxt -> Spine -> CoverRes
testSpine defs clss cxt sp = go clss where -- cxt |- sp 
  go = \case 
    [] -> CoverFail [(cxt, sp)]
    (ps:rest) -> case match defs (env cxt) ps sp of 
      MatchSuc _ -> CoverOk
      MatchFailed -> go rest -- move to next clause
      MatchStuck (BVar x) -> CoverStuck x
      _ -> error "impossible"

genSpine :: Cxt -> Spine -> Lvl -> Maybe [(Cxt, Spine)]
genSpine cxt sp l = do -- Maybe
  splitted_cxts <- splitCxt cxt l
  pure $ do -- Maybe
    cxt' <- splitted_cxts  
    let sp' = updateSp cxt' sp
    pure (cxt', sp')

testManySpine :: Defs -> [ClauseLHS] -> [(Cxt, Spine)] -> Maybe [(Cxt, Spine)]
testManySpine defs clss = \case 
  [] -> Just []
  (cxt, sp):rest -> case testSpine defs clss cxt sp of 
    CoverOk -> testManySpine defs clss rest
    CoverStuck l -> do
      gen <- genSpine cxt sp l 
      left <- forM gen $ \ (cxt', sp') -> 
        testManySpine defs clss [(cxt', sp')]
      right <- testManySpine defs clss rest
      pure $ join left ++ right 
    CoverFail sp' -> do 
      right <- testManySpine defs clss rest
      pure $ sp' ++ right