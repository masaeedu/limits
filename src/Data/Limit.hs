{-# LANGUAGE LambdaCase, TypeFamilies, FunctionalDependencies, PartialTypeSignatures, EmptyCase, TypeFamilyDependencies #-}
module Data.Limit where

import Data.Proxy
import Data.Type.Equality
import Data.Singleton
import Data.Maybe
import Data.Profunctor
import Data.Sift
import Data.Diagram

import GHC.TypeLits (KnownSymbol, sameSymbol)

import Control.Applicative

-- {{{ Limits

type Cone p (s :: k -> *) (f :: k -> *) n
  = forall x. s x -> p n (f x)

class Limit p (s :: k -> *) (f :: k -> *) l | l -> f, f -> s
  where
  project :: Cone p s f l
  build   :: Cone p s f n -> p n l

inject :: Limit Op s f l => s i -> f i -> l
inject p = runOp $ project p

match :: (Limit Op s f l) => (forall i. s i -> f i -> n) -> l -> n
match c = runOp $ build (Op . c)

convert :: (Limit p c f l, Limit p c f l') => p l l'
convert = build project

-- }}}

-- {{{ Test out tuples and eithers

instance Limit (->) SBool (Two a b) (a, b)
  where
  project SF (a, _) = Fst a
  project ST (_, b) = Snd b
  build c n =
    ( case (c SF n) of Fst a -> a
    , case (c ST n) of Snd b -> b
    )

newtype Op b a = Op { runOp :: a -> b }

instance Limit Op SBool (Two a b) (a + b)
  where
  project SF = Op $ \(Fst a) -> Left a
  project ST = Op $ \(Snd b) -> Right b

  build c = Op $ \case
    { Left  a -> runOp (c SF) $ Fst a
    ; Right b -> runOp (c ST) $ Snd b
    }

-- }}}

-- {{{ Diagram functor for string-indexed products

unChoose :: r :! i ~ 'Just v => RowSel r i -> v
unChoose (Choose x) = x

-- }}}

-- {{{ Test RowSel diagram functor

test1 :: RowSel ['("foo", Int), '("bar", String)] "foo"
test1 = Choose 42

test2 :: RowSel ['("foo", Int), '("bar", String)] "bar"
test2 = Choose "hello"

-- }}}

-- {{{ Test manual records

data Foo = Foo { a :: Int, b :: String }

type FooRep =['("a", Int), '("b", String)]

data SSymbol s = (KnownSymbol s) => SSymbol (Proxy s)

ssym :: KnownSymbol s => SSymbol s
ssym = SSymbol $ Proxy

instance Limit (->) SSymbol (RowSel FooRep) Foo
  where
  project (SSymbol p) (Foo a b) = fromJust $ v1 <|> v2
    where
    v1 = (\Refl -> Choose a) <$> sameSymbol p (Proxy @"a")
    v2 = (\Refl -> Choose b) <$> sameSymbol p (Proxy @"b")
  build c n = Foo (unChoose $ c (ssym @"a") n) (unChoose $ c (ssym @"b") n)

test3 :: Int
test3 = unChoose $ project (SSymbol (Proxy @"a")) $ Foo 42 "hello"

data Foo' = Foo' { a' :: Int, b' :: String }

instance Limit (->) SSymbol (RowSel FooRep) Foo'
  where
  project (SSymbol p) (Foo' a b) = fromJust $ v1 <|> v2
    where
    v1 = (\Refl -> Choose a) <$> sameSymbol p (Proxy @"a")
    v2 = (\Refl -> Choose b) <$> sameSymbol p (Proxy @"b")
  build c n = Foo' (unChoose $ c (ssym @"a") n) (unChoose $ c (ssym @"b") n)

test4 :: Foo' -> Foo
test4 = convert

test5 :: Foo -> Foo'
test5 = convert

-- }}}

-- {{{ Test manual variants

data Bar = B1 Int | B2 String
type BarRep = ['("B1", Int), '("B2", String)]

instance Limit Op SSymbol (RowSel BarRep) Bar
  where
  project (SSymbol p) = Op $ case (fromJust $ v1 <|> v2) of
    { Left Refl -> B1 . unChoose
    ; Right Refl -> B2 . unChoose
    }
    where
    v1 = Left <$> sameSymbol p (Proxy @"B1")
    v2 = Right <$> sameSymbol p (Proxy @"B2")

  build c = Op $ \case
    { B1 a -> runOp (c $ ssym @"B1") $ Choose a
    ; B2 b -> runOp (c $ ssym @"B2") $ Choose b
    }

test6 :: String -> Bar
test6 = inject (ssym @"B2") . Choose

-- }}}

-- {{{ Lenses and products

type Lens s t a b = forall p. Strong p => p a b -> p s t

lens :: (s -> a) -> (s -> b -> t) -> Lens s t a b
lens v u = dimap (\s -> (v s, s)) (uncurry $ flip u) . first'

{-
some exposition to help write @at@

we receive:
- a @p@, which is @s@ in this scenario
- a @g i@, which is @b@ in this scenario and corresponds to a component of @q@

we can construct right off the bat:
- an @f i@, which is a component of @p@

we need to produce overall:
- a @q@, which is @t@ in this scenario

to accomplish this using @build@, we need to produce for any @s i'@:
- a @g i'@

now we have the @g i@, but that is only an acceptable output when @i ~ i'@.

when @i !~ i'@, we need to instead demonstrate that we can convert `f` to `g`
-}

at ::
  ( Limit (->) s f p
  , Limit (->) s g q
  , Sift i f g
  ) =>
  s i -> Lens p q (f i) (g i)
at (si :: s i) =
  lens
    (project si)
    (flip $ \gi ->
      build (\sx -> either (\Refl -> gi) id . sift @i . project sx)
    )

_1 :: Lens (a, x) (b, x) a b
_1 = at SF . dimap (\(Fst a) -> a) Fst

_2 :: Lens (x, a) (x, b) a b
_2 = at ST . dimap (\(Snd a) -> a) Snd

-- }}}

-- {{{ Generic instances

{-
data Nat = Z | S Nat

data SNat n
  where
  SZ :: SNat 'Z
  SS :: SNat n -> SNat ('S n)

instance Singleton SNat 'Z
  where
  single _ = SZ

instance Singleton SNat n => Singleton SNat ('S n)
  where
  single _ = SS $ single Proxy

type family (r :: [k]) !! (i :: Nat) = (c :: Maybe k)
  where
  '[]       !! n      = 'Nothing
  (x ': _)  !! 'Z     = 'Just x
  (_ ': xs) !! ('S n) = xs !! n

data IdxSel (r :: [k]) (i :: Nat)
  where
  Zilch :: IdxSel '[] i
  Nth :: (x ': xs) !! i ~ 'Just v => v -> IdxSel (x ': xs) i

unwrap :: r !! i ~ 'Just v => IdxSel r i -> v
unwrap (Nth a) = a

foo :: IdxSel xs n -> IdxSel (x ': xs) ('S n)
foo (Nth a) = Nth a

-- bar :: IdxSel (x ': xs) ('S n) -> IdxSel xs n
-- bar (Nth a) = Nth a

instance Limit (->) SNat (IdxSel ('[] :: [*])) (NP f '[])
  where
  project _ Nil = Zilch
  build _ _ = Nil

instance
  Limit (->) SNat (IdxSel xs) (NP f xs') =>
  Limit (->) SNat (IdxSel (f x ': xs)) (NP f (x ': xs'))
  where
  project SZ     (x :* _)  = Nth $ x
  project (SS n) (_ :* xs) = foo $ project n xs

  build c n = x n :* xs n
    where
    x = unwrap . c SZ
    xs = build (\case { SZ -> _; (SS n) -> _ })

test7 :: I Int
test7 = unwrap $ project (SS SZ) $ I "foo" :* I 42 :* Nil

instance Limit Op SNat (IdxSel ('[] :: [*])) (NS f '[])
  where
  project _ = Op $ \case {}
  build _ = Op $ \case {}
-}

-- }}}
