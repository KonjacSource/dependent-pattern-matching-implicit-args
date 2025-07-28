module Definition where

import Common
import Syntax
import qualified Presyntax as R

type Telescope = [(Name, Icit, Ty)]
type TSpine = [(Tm, Icit)]

data Def
  = DefFunc FuncDef
  | DefData DataDef
  | DefCons ConsDef 
  deriving Show 

data ConsDef = ConsDef
  { consName :: Name 
  , consData :: DataDef -- ^ Datatype which the constructor belongs to.
  , consType :: Ty -- ^ The type of the constructor.
  } 

data FuncDef = FuncDef
  { funcName :: Name
  , funcType :: Ty -- ^ Type of the function
  , funcClauses :: [Clause]
  } 

data DataDef = DataDef
  { dataName :: Name 
  , dataIx   :: Telescope
  , dataCons  :: [(Name, Telescope, TSpine)] 
  -- ^ List of (Name of constructor, Arguments list, The returning indexes), Note that the returning indexes is under the context of the arguments list. 
  } 

instance Show ConsDef where 
  show = consName


instance Show FuncDef where 
  show = funcName
  
instance Show DataDef where 
  show = dataName


lookupCons :: DataDef -> Name -> Maybe (Telescope, TSpine)
lookupCons (DataDef d _ cons) c = go cons where 
  go [] = Nothing
  go ((c', ts, ix):rest) 
    | c' == c = pure (ts, ix)
    | otherwise = go rest

getConsType :: DataDef -> Telescope -> TSpine -> Tm 
getConsType d [] ix = go (Call $ dataName d) ix where 
  go t [] = t
  go t (as :> (a, i)) = App (go t as) a i
getConsType d ((x, i, t):ts) ix = Pi x i t $ getConsType d ts ix 

dataType :: DataDef -> Ty 
dataType d = go (dataIx d) where 
  go [] = U 
  go ((x,i,t):ts) = Pi x i t (go ts)

data Clause = Clause
  { clausePatterns :: [(Pattern, Icit)]
  , clauseRhs :: Tm
  } deriving Show

data Pattern 
  = PatVar Name
  | PatCon Name [(Pattern, Icit)] 
  deriving Show

class Arity f where 
  arity :: f -> Int 

instance Arity Clause where 
  arity = length . clausePatterns

instance Arity FuncDef where 
  arity f = case funcClauses f of 
    [] -> 0
    (c:_) -> arity c

data RClause = RClause
  { clausePatternsR :: RPatterns
  , clauseRhsR :: R.Tm
  }

data RPattern = RPat Name RPatterns deriving Show
type RPatterns = [(Either Name Icit, RPattern)]

data RFuncDef = RFuncDef
  { funcNameR :: Name
  , funcTypeR :: R.Tm -- ^ Type of the function
  , funcClausesR :: [RClause]
  }  

type RTelescope = [(Name, Icit, R.Tm)]

data RDataDef = RDataDef
  { dataNameR :: Name
  , dataIxR :: R.Tm
  , dataConsR :: [(Name, R.Tm)]
  } deriving Show 

data RDef = RDefData RDataDef | RDefFunc RFuncDef

type Program = [(SourcePos, RDef)]

