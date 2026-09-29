{-# OPTIONS --rewriting --guarded #-}
{-# OPTIONS --lossy-unification #-}
{-# OPTIONS --allow-unsolved-metas #-}

module Experiments.CBPVModel where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma

open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Constructions.Elements
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Properties
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Monoidal.Base
open import Cubical.Categories.Monoidal.Enriched
open import Cubical.Categories.Bifunctor.Redundant

open import Cubical.Categories.Limits.BinProduct
open import Cubical.Categories.Limits.BinProduct.More

open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Constructions.BinProduct

open MonoidalCategory
open MonoidalStr
open TensorStr
open Category

private
  variable
    ℓ ℓ' : Level


module _ (ℓ ℓ' : Level)
  (C : Category ℓ ℓ')
  (prods : BinProducts C)
  where

  open Functor
  open BinProduct

  private
    module C = Category C

  BinProductsFunctor : Functor (C ×C C) C
  BinProductsFunctor .F-ob (c₁ , c₂) =
    prods c₁ c₂ .binProdOb
  BinProductsFunctor .F-hom {c₁ , c₂} {c₁' , c₂'} (f₁ , f₂) =
    prods c₁' c₂' .univProp
      ((prods _ _ .binProdPr₁) C.⋆ f₁)
      ((prods _ _ .binProdPr₂) C.⋆ f₂)
      .fst .fst
  BinProductsFunctor .F-id = {!!}
  BinProductsFunctor .F-seq = {!!}

module _ (ℓ ℓ' : Level)
  (D : Category ℓ ℓ')
  (terminal : Terminal D)
  (prods : BinProducts D)
  where

  private
    module D = Category D

  open NatTrans

  BinProducts→MonoidalCat : MonoidalCategory ℓ ℓ'
  BinProducts→MonoidalCat .C = D
  BinProducts→MonoidalCat .monstr .tenstr .─⊗─ = BinProductsFunctor ℓ ℓ' D prods
  BinProducts→MonoidalCat .monstr .tenstr .unit = terminal .fst
  BinProducts→MonoidalCat .monstr .α = {!!}
  BinProducts→MonoidalCat .monstr .η = {!!}
  BinProducts→MonoidalCat .monstr .ρ = {!!}
  BinProducts→MonoidalCat .monstr .pentagon = {!!}
  BinProducts→MonoidalCat .monstr .triangle = {!!}


module _ {ℓC ℓC' ℓD ℓD' : Level}
  (C : Category ℓC ℓC')
  (D : Category ℓD ℓD')
  (M : MonoidalStr D) where

  MonCat→MonCatFunctor : MonoidalStr (FUNCTOR C D)
  MonCat→MonCatFunctor .tenstr .─⊗─ = {!!}
  MonCat→MonCatFunctor .tenstr .unit = {!!}
  MonCat→MonCatFunctor .α = {!!}
  MonCat→MonCatFunctor .η = {!!}
  MonCat→MonCatFunctor .ρ = {!!}
  MonCat→MonCatFunctor .pentagon = {!!}
  MonCat→MonCatFunctor .triangle = {!!}


module _ {ℓS : Level} (C : Category ℓ ℓ') (X Y : Presheaf C ℓS) where

  PshAsCartMonCat : MonoidalCategory (ℓ-max (ℓ-max ℓ ℓ') (ℓ-suc ℓS)) {!!}
  PshAsCartMonCat = BinProducts→MonoidalCat _ _ (PresheafCategory C ℓS) {!!} {!!}

record CBPVModel (ℓV ℓC : Level) : Type where

  field
    𝓥 : EnrichedCategory {!!} ℓV
    𝓒 : EnrichedCategory {!!} ℓC
