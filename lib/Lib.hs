{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Lib where

import Data.Kind (Constraint, Type)
import Data.Proxy (Proxy (..))

--------------------------------------------------------------------------------------

-- We'd like to demonstrate that the following record is the limit of a diagram out of a discrete category

data Foo = Foo
  { a :: String,
    b :: Int,
    c :: Bool
  }

--------------------------------------------------------------------------------------

-- We'll need a way to talk about the relationship between a promoted type and its unpromoted version

type family Sing :: k -> Type

data SomeSing k where
  SomeSing :: SingI a => Sing (a :: k) -> SomeSing k

class SingI a where
  sing :: Sing a

class SingKind k where
  type Demote k = (r :: Type) | r -> k
  fromSing :: Sing (a :: k) -> Demote k
  toSing :: Demote k -> SomeSing k

--------------------------------------------------------------------------------------

-- `Category` from Control.Category is insufficient for working with "pattern matchable" domains of objects
-- instead we need this class...

type CCategory :: (k -> Type) -> Hom k -> Constraint
class CCategory f p where
  cid :: f x -> x `p` x
  ccompose :: (f x, f y, f z) -> y `p` z -> x `p` y -> x `p` z

--------------------------------------------------------------------------------------

-- Regular instances of `Category` just correspond to `CCategory Proxy`

instance CCategory f (->) where
  cid _ = id
  ccompose _ = (.)

--------------------------------------------------------------------------------------

-- First let's witness the hom constructor of discrete categories

type Discrete :: k -> k -> Type
data Discrete a b where
  Refl :: Discrete a a

instance CCategory f Discrete where
  cid _ = Refl
  ccompose _ Refl Refl = Refl

--------------------------------------------------------------------------------------

-- We'll also need a more general notion of functor

type Hom k = k -> k -> Type

type GFunctor :: (i -> Type) -> Hom i -> (o -> Type) -> Hom o -> (i -> o) -> Constraint
class (CCategory obp p, CCategory obq q) => GFunctor obp p obq q f | f -> p q where
  gomap :: obp x -> obq (f x)
  gfmap :: (obp a, obp b) -> p a b -> q (f a) (f b)

--------------------------------------------------------------------------------------

-- We'll also need to work with "cones" of a functor, which are natural transformations between
-- the constant functor to some apex object and the given functor

type Cone ob p n f = forall x. ob x -> p n (f x)

--------------------------------------------------------------------------------------

-- And here finally is our representation of a limit

-- | A limit is a terminal cone, which means...
type Limit :: (i -> Type) -> Hom i -> (o -> Type) -> Hom o -> (i -> o) -> o -> Constraint
class GFunctor obp p obq q f => Limit obp p obq q f l where
  -- ... the limit is an object
  ob :: obq l

  -- | ... carrying a cone
  project :: Cone obp q l f

  -- | ... to which any other cone has a morphism
  build :: obq l -> Cone obp q n f -> q n l

--------------------------------------------------------------------------------------

-- Here are the objects of the category that indexes 'Foo''s diagram

data FooKey = A | B | C

--------------------------------------------------------------------------------------

-- And the requisite boilerplate for them ...

data SFooKey fk where
  SA :: SFooKey 'A
  SB :: SFooKey 'B
  SC :: SFooKey 'C

type instance Sing = SFooKey

instance SingKind FooKey where
  type Demote FooKey = FooKey
  fromSing = \case
    SA -> A
    SB -> B
    SC -> C
  toSing = \case
    A -> SomeSing SA
    B -> SomeSing SB
    C -> SomeSing SC

instance SingI 'A where
  sing = SA

instance SingI 'B where
  sing = SB

instance SingI 'C where
  sing = SC

--------------------------------------------------------------------------------------

-- Here is the diagram functor that sketches 'Foo' in 'Type'

type FooVal :: FooKey -> Type
data FooVal k where
  VA :: String -> FooVal 'A
  VB :: Int -> FooVal 'B
  VC :: Bool -> FooVal 'C

instance GFunctor SFooKey Discrete Proxy (->) FooVal where
  gomap _ = Proxy
  gfmap _ Refl = id

--------------------------------------------------------------------------------------

-- And here is the proof that 'Foo' is a limit of said diagram

instance Limit SFooKey Discrete Proxy (->) FooVal Foo where
  ob = Proxy

  project = \case
    SA -> VA . a
    SB -> VB . b
    SC -> VC . c

  build _ cone n =
    Foo
      { a = case cone SA n of VA a -> a,
        b = case cone SB n of VB b -> b,
        c = case cone SC n of VC c -> c
      }

--------------------------------------------------------------------------------------

message :: String
message = "Ready? Get set... GO!"
