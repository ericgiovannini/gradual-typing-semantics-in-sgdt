{-# OPTIONS --rewriting --guarded #-}

{-# OPTIONS --lossy-unification #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}

open import Common.Later

module Semantics.Concrete.Types (k : Clock) where

open import Semantics.Concrete.Types.Base k public
open import Semantics.Concrete.Types.Constructions k public
