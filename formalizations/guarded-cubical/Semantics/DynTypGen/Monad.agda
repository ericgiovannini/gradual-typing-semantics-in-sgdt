{-# OPTIONS --rewriting --guarded #-}
{-# OPTIONS --lossy-unification #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import Common.Later

module Semantics.DynTypGen.Monad (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma
open import Cubical.Data.List
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Data.Empty as ⊥

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Adjoint
open import Cubical.Categories.Instances.Sets

open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Representable

open import Cubical.Categories.Adjoint.UniversalElements
open import Cubical.Categories.Profunctor.FunctorComprehension
open import Cubical.Categories.Profunctor.General
open import Cubical.Categories.Instances.Discrete

open import Semantics.Concrete.Predomain.SimpleErrorDomain k

{-

  The monad for dynamic type-tag generation is constructed as the composition
  of the following adjunctions:



            L₁                  L₂                 L₃                  
      _______________    _______________     _______________
     /               \  /               \   /               \    
     |               |  |               |   |               |
     |               V  |               V   |               V  
  [W, Set]       [|W|, Set]         [W^op, Set]       [W^op, ErrDom]
     ∧               |  ∧               |   ∧               |
     |               |  |               |   |               |
     \_______________/  \_______________/   \_______________/

            R₁                 R₂                  R₃
 


  "values"                                          "computations"


-}

private
  variable
    ℓC ℓC' : Level

module _ (C : Category ℓC ℓC') (isUnivalentC : isUnivalent C) (ℓS : Level) where

  open Category

  open isUnivalent

  private
    module C = Category C



  groupoidC : isGroupoid (C .ob)
  groupoidC = isGroupoid-ob isUnivalentC
   
  |C| = DiscreteCategory (C .ob , groupoidC)

  incl : Functor |C| C
  incl = DiscFunc (λ x → x)


  PshC : Category _ _
  PshC = PresheafCategory C (ℓ-max ℓC ℓC') -- doesn't mention ℓS

  FamC : Category _ _
  FamC = PresheafCategory |C| (ℓ-max ℓC ℓC') -- doesn't mention ℓS

  U : Functor PshC FamC
  U = precomposeF (SET _) (incl ^opF)


  -- Left adjoint to the forgetful functor U
  ΣC : Functor FamC PshC
  ΣC = FunctorComprehension {C = FamC} {D = PshC} {P = {!!}} {!!}
    where
      prof : Profunctor FamC PshC {!!} -- see file that defines adjoints
      prof .Functor.F-ob X  = {!!}
      prof .Functor.F-hom   = {!!}
      prof .Functor.F-id    = {!!}
      prof .Functor.F-seq   = {!!}


      ΣC₀ : FamC .ob → PshC .ob
      ΣC₀ X .Functor.F-ob c .fst = Σ[ c' ∈ C .ob ] (Σ[ f ∈ (C.Hom[ c , c' ]) ] (X ⟅ c' ⟆) .fst)
      ΣC₀ X .Functor.F-ob c .snd = {!!}
      ΣC₀ X .Functor.F-hom = {!!}
      ΣC₀ X .Functor.F-id = {!!}
      ΣC₀ X .Functor.F-seq = {!!}

      elts : UniversalElements {!!}
      elts = {!!}

