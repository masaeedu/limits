module Data.Diagram where

data Two a b (i :: Bool)
  where
  Fst :: a -> Two a b 'False
  Snd :: b -> Two a b 'True

type Row k v = [(k, v)]

type family (r :: Row i k) :! (s :: i) = (c :: Maybe k)
  where
  '[]            :! _ = 'Nothing
  ('(s, v) ': _) :! s = 'Just v
  (_       ': r) :! s = r :! s

data RowSel (r :: [(k, *)]) (i :: k)
  where
  Choose :: r :! i ~ 'Just v => v -> RowSel r i
