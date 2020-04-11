module Data.Sift where

import Data.Type.Equality

class Sift i f g
  where
  sift :: f x -> (x :~: i) + g x
