{-# LANGUAGE NoImplicitParams, PackageImports #-}
module Prelude (module Prelude, module P) where

import "base" Prelude as P

type (+) = P.Either
type (×) = (,)
