module Data.Sift where

import Data.Diagram
import Data.Type.Equality

class Sift i f g
  where
  sift :: f x -> (x :~: i) + g x

instance Sift 'False (Two a b) (Two c b)
  where
  sift (Fst _) = Left Refl
  sift (Snd x) = Right $ Snd x

instance Sift 'True (Two a b) (Two a c)
  where
  sift (Fst x) = Right $ Fst x
  sift (Snd _) = Left Refl
