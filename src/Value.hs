
module Value where

import Common
import Syntax
import Definition

type Env     = [Val]
type Spine   = [(Val, Icit)]
data Closure = Closure Env Tm deriving Show 
type VTy     = Val

data Val
  = VFlex MetaVar Spine Env -- Env of spine
  | VRigid Lvl Spine
  | VLam Name Icit {-# unpack #-} Closure
  | VPi Name Icit ~VTy {-# unpack #-} Closure
  | VU
  | VFunc FuncDef Spine
  | VHold FuncDef Spine
  | VData DataDef Spine 
  | VCons ConsDef Spine
  deriving Show 

pattern VVar :: Lvl -> Val
pattern VVar x = VRigid x []

pattern VMeta :: MetaVar -> Env -> Val
pattern VMeta m env = VFlex m [] env
