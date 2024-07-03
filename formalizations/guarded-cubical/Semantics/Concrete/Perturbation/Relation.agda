{- Extension of pertubrations from types to relations, and push-pull -}
{-# OPTIONS --rewriting --guarded #-}
{-# OPTIONS --lossy-unification #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import Common.Later
module Semantics.Concrete.Perturbation.Relation (k : Clock) where

open import Semantics.Concrete.Perturbation.Relation.Base k public
open import Semantics.Concrete.Perturbation.Relation.Constructions k public
