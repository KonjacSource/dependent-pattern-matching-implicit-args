
module Evaluation (($$), quote, eval, nf, force, lvl2Ix, vApp, quoteCxt, evalCxt, fv, fvSp, force', p2v, updateVal) where

import Common
import Metacontext
import Syntax
import Value
import Cxt.Type
import Data.List (nub)
import Definition
import qualified Data.Map as M
import GHC.Stack (HasCallStack)
import Text.Printf (printf)


data MatchResult
  = MatchSuc Env   -- ^ 匹配成功
  | MatchStuck MatchBlocker
  -- ^ 匹配卡住了, 并返回卡住的相关信息, 这在Coverage Check的时候会用到
  | MatchFailed    -- ^ c != c'

data MatchBlocker = BVar Lvl | BFunc FuncDef | BFlex MetaVar

-- | 注意, 虽然在这个项目中模式匹配总是发生在顶层, 
-- 但是我们可能会扩展这个系统, 加入模块, 或是句内 match 语句.
match1 :: Defs -> Env -> Pattern -> Val -> MatchResult
match1 defs env pat val = case (pat, val) of
  (PatVar x, v) -> MatchSuc (v : env)
  (PatCon c ps, VCons c_def args)
    | c == consName c_def -> match defs env ps (reverse args)
    | otherwise -> MatchFailed
  (PatCon _ _, VU)          -> MatchFailed
  (PatCon _ _, VData _ _)   -> MatchFailed
  (PatCon _ _, VLam {})     -> MatchFailed
  (PatCon _ _, VPi {})      -> MatchFailed
  (PatCon _ _, VRigid x _)  -> MatchStuck (BVar x)
  (PatCon _ _, VFunc f _)   -> MatchStuck (BFunc f)
  (PatCon _ _, VHold f _)   -> MatchStuck (BFunc f)
  (PatCon _ _, VFlex m _ _) -> MatchStuck (BFlex m)

-- TODO : BUG> The reason is that Spine is a reversed list
match :: Defs -> Env -> [(Pattern, Icit)] -> Spine -> MatchResult
match defs env [] [] = MatchSuc env
match defs env pats@((p, i):ps) vals@(((a, i'):as)) 
  | i == i' = 
    case match1 defs env p a of
      MatchFailed -> MatchFailed
      MatchStuck l -> MatchStuck l
      MatchSuc env' -> match defs env' ps as
match _ _ ps vs = error $ "match: impossible\n when matching: " ++ show ps ++ " against " ++ show vs

infixl 8 $$
($$) :: HasCallStack => (Defs, Closure) -> Val -> Val
($$) (defs, Closure env t) ~u = eval defs (env :> u) t

vApp :: HasCallStack => Defs -> Env -> Val -> Val -> Icit -> Val
vApp defs env t ~u i = case force defs t of
  VLam _ _ t  -> (defs, t) $$ u
  VFlex  m sp env -> VFlex  m (sp :> (u, i)) env 
  VRigid x sp     -> VRigid x (sp :> (u, i))
  VFunc f sp
    | length sp + 1 < arity f -> evalFun defs env f (funcClauses f) (sp :> (u, i))
    | otherwise -> let (sp', rest) = splitAt (arity f) (sp :> (u,i)) in
        vAppSp defs env (evalFun defs env f (funcClauses f) sp') rest
  VHold f sp -> VHold f (sp :> (u,i))
  VCons c sp -> VCons c (sp :> (u,i))
  VData d sp -> VData d (sp :> (u,i))
  t           -> error "impossible"

-- | Make sure `(length sp) <= arity f`
evalFun :: HasCallStack => Defs -> Env -> FuncDef -> [Clause] -> Spine -> Val
evalFun defs env f [] sp = VHold f sp -- No matchable clause yet.
evalFun defs env f (c:cs) sp
  | length sp < arity f = VFunc f sp -- Wait
  | otherwise = -- `length sp == arity f`
      case match defs env (clausePatterns c) (reverse sp) of
        MatchFailed -> evalFun defs env f cs sp --Failed
        MatchStuck _ -> VHold f sp       -- Stucked
        MatchSuc env' -> eval defs env' (clauseRhs c) -- Succeeded

vAppSp :: Defs -> Env -> Val -> Spine -> Val
vAppSp defs env t = \case
  []           -> t
  sp :> (u, i) -> vApp defs env (vAppSp defs env t sp) u i

vMeta :: HasCallStack => Env -> MetaVar -> Val
vMeta env m = case lookupMeta m of
  Solved v -> v
  Unsolved -> VMeta m env

vAppBDs :: HasCallStack => Defs -> Env -> Val -> [BD] -> Val
vAppBDs defs env ~v bds = case (env, bds) of
  ([]       , []            ) -> v
  (env :> t , bds :> Bound  ) -> vApp defs env (vAppBDs defs env v bds) t Expl
  (env :> t , bds :> Defined) -> vAppBDs defs env v bds
  _                           -> error "impossible"

eval :: HasCallStack => Defs -> Env -> Tm -> Val
eval defs env = \case
  Var x              -> env !! unIx x
  App t u i          -> vApp defs env (eval defs env t) (eval defs env u) i
  Lam x i t          -> VLam x i (Closure env t)
  Pi x i a b         -> VPi x i (eval defs env a) (Closure env b)
  Let _ _ t u        -> eval defs (env :> eval defs env t) u
  U                  -> VU
  Meta m             -> vMeta env m 
  InsertedMeta m bds -> vAppBDs defs env (vMeta env m) bds
  Call f             -> case M.lookup f defs of
                        Just (DefFunc f) 
                          | arity f == 0 && not (null $ funcClauses f) -> eval defs env (clauseRhs (head (funcClauses f))) -- eval 0-arity function
                          | otherwise-> VFunc f [] 
                        Just (DefData d) -> VData d []
                        Just (DefCons c) -> VCons c []
                        Nothing -> error "eval: impossible"

evalCxt :: HasCallStack => Cxt -> Tm -> Val
evalCxt ctx = eval (defs ctx) (env ctx)

force :: Defs -> Val -> Val
force defs = \case
  VFlex m sp env | Solved t <- lookupMeta m -> force defs (vAppSp defs env t sp)
  t -> t

force' :: Cxt -> Val -> Val 
force' = force . defs

lvl2Ix :: Lvl -> Lvl -> Ix
lvl2Ix (Lvl l) (Lvl x) = Ix (l - x - 1)

quoteSp :: Defs -> Env -> Lvl -> Tm -> Spine -> Tm
quoteSp defs env l t = \case
  []           -> t
  sp :> (u, i) -> App (quoteSp defs env l t sp) (quote defs env l u) i

quote :: HasCallStack => Defs -> Env -> Lvl -> Val -> Tm
quote defs env l t = case force defs t of
  VFlex m sp _ -> quoteSp defs env l (Meta m) sp
  VRigid x sp  -> quoteSp defs env l (Var (lvl2Ix l x)) sp
  VLam x i t   -> Lam x i (quote defs (VVar l : env) (l + 1) ((defs, t) $$ VVar l))
  VPi x i a b  -> Pi x i (quote defs env l a) (quote defs (VVar l : env) (l + 1) ((defs, b) $$ VVar l))
  VU           -> U
  VCons c sp   -> quoteSp defs env l (Call (consName c)) sp
  VFunc f sp   -> quoteSp defs env l (Call (funcName f)) sp
  VHold f sp   -> quoteSp defs env l (Call (funcName f)) sp
  VData d sp   -> quoteSp defs env l (Call (dataName d)) sp

quoteCxt :: Cxt -> Val -> Tm 
quoteCxt cxt = quote (defs cxt) (env cxt) (lvl cxt)

nf :: HasCallStack => Defs -> Env -> Tm -> Tm
nf defs env t = quote defs env (Lvl (length env)) (eval defs env t)

fvSp :: Defs -> Lvl -> Spine -> [Lvl]
fvSp def dep = \case 
  [] -> []
  ((v, _):vs) -> fv def dep v ++ fvSp def dep vs

fv :: Defs -> Lvl -> Val -> [Lvl]
fv def dep = nub . \case
  VFlex _ sp _ -> fvSp def dep sp
  VRigid l sp -> l : fvSp def dep sp
  VLam x _ b -> filter (< dep) $ fv def (dep + 1) ((def, b) $$ (VVar dep))
  VPi x _ t b -> fv def dep t ++ filter (< dep) (fv def (dep + 1) ((def, b) $$ (VVar dep)))
  VCons _ sp -> fvSp def dep sp 
  VFunc _ sp -> fvSp def dep sp 
  VHold _ sp -> fvSp def dep sp 
  VData _ sp -> fvSp def dep sp 
  VU -> []


p2v :: Defs -> Lvl -> Pattern -> Val
p2v defs dep = fst . go1 dep where

  go1 :: Lvl -> Pattern -> (Val, Lvl)
  go1 l = \case 
    PatVar _ -> (VVar l, l+1)
    PatCon c ps -> case M.lookup c defs of 
      Just (DefCons c) -> 
        let (l', r) = go l ps in 
          (VCons c l', r)
      _ -> error "p2v: impossible"
      
  go :: Lvl -> [(Pattern, Icit)] -> (Spine, Lvl)
  go l [] = ([], l)
  go l ((p,i):ps) = 
    let (p', l') = go1 l p 
        (ps', l'') = go l' ps 
    in (ps' ++ [(p', i)], l'')


updateVal :: Cxt -> Val -> Val
updateVal ctx = evalCxt ctx . quote (defs ctx) (env ctx) (lvl ctx)


