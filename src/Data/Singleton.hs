module Data.Singleton where

import Data.Proxy

class Singleton (f :: k -> *) (i :: k)
  where
  single :: Proxy i -> f i

data SBool b
  where
  SF :: SBool 'False
  ST :: SBool 'True

instance Singleton SBool 'False
  where
  single _ = SF

instance Singleton SBool 'True
  where
  single _ = ST
