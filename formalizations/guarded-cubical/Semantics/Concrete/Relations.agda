{-# OPTIONS --rewriting --guarded #-}
{-# OPTIONS --lossy-unification #-}
{-# OPTIONS --allow-unsolved-metas #-}
open import Common.Later

module Semantics.Concrete.Relations (k : Clock) where

open import Semantics.Concrete.Relations.Base k public
open import Semantics.Concrete.Relations.Constructions k public
