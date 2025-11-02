{-# LANGUAGE ImpredicativeTypes #-}

module Debug where 
import Debug.Trace (trace)
import Cxt.Type

isDebug :: Bool
isDebug = True

class ShowUnderCxt a where 
  showUnderCxt :: Cxt -> a -> String

-- debug :: Cxt -> [forall a. ShowUnderCxt a => a] -> ()
-- debug cxt | isDebug = \case 
--   [] -> () 
--   (x:xs) -> trace (showUnderCxt cxt x) $ debug cxt xs
-- debug _ = \_ -> () 