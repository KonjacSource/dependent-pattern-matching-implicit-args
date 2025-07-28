module Cxt.Type where 

import Common
import Syntax
import Value
import qualified Data.Map as M
import Definition

-- Elaboration context
--------------------------------------------------------------------------------

data NameOrigin = Inserted | Source deriving Eq
type Types = [(String, NameOrigin, VTy)]

data Cxt = Cxt {           -- used for:
                           -----------------------------------
    env   :: Env           -- evaluation
  , lvl   :: Lvl           -- unification
  , types :: Types         -- raw name lookup, pretty printing
  , bds   :: [BD]          -- fresh meta creation
  , pos   :: SourcePos     -- error reporting
  , defs  :: Defs
  }

type Defs = M.Map Name Def
