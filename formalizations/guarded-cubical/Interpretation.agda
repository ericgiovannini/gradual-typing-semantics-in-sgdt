{-# OPTIONS --cubical --rewriting --guarded #-}

-- Define the interpretation of the syntax

open import Later

module Interpretation (k : Clock)  where

  open import Cubical.Foundations.Prelude
  open import Cubical.Foundations.Function
  open import Cubical.Foundations.Transport
  open import Cubical.Data.Unit
  open import Cubical.Data.Nat hiding (_^_)
  open import Cubical.Data.Prod
  open import Cubical.Data.Empty
  open import Cubical.Relation.Binary.Poset

  open import ErrorDomains k
  open import GradualSTLC

  private
    variable
      l : Level
      A B : Set l
  private
    ▹_ : Set l → Set l
    ▹_ A = ▹_,_ k A 

  -- Denotational semantics

  ⟦_⟧ty : Ty -> Type
  ⟦ nat ⟧ty = ℕ
  ⟦ dyn ⟧ty =  Dyn
  ⟦ A => B ⟧ty =  ⟦ A ⟧ty -> L℧ ⟦ B ⟧ty

  ⟦_⟧ctx : Ctx -> Type
  ⟦ · ⟧ctx = Unit
  ⟦ Γ :: A ⟧ctx = ⟦ Γ ⟧ctx × ⟦ A ⟧ty

  -- Agda can infer that the context is not empty, so
  -- ⟦ Γ ⟧ctx must be a product
  -- Make A implicit
  look : {Γ : Ctx} -> (env : ⟦ Γ ⟧ctx) -> (A : Ty) -> (x : Γ ∋ A) -> ⟦ A ⟧ty
  look env A vz = proj₂ env
  look env A (vs {Γ} {S} {T} x) = look (proj₁ env) A x

  {-
  lookup : (Γ : Ctx) -> (A : Ty) -> (x : Γ ∋ A) -> ⟦ A ⟧ty
  lookup (Γ :: A) A vz =  proj₂ {!!}
  lookup Γ A (vs y) = {!!}
  -}

  ⟦_⟧lt : {A B : Ty} -> A ⊑ B -> EP ⟦ A ⟧ty ⟦ B ⟧ty
  ⟦ dyn ⟧lt = EP-id Dyn
  ⟦ A⊑A' => B⊑B' ⟧lt = EP-lift ⟦ A⊑A' ⟧lt ⟦ B⊑B' ⟧lt
  ⟦ nat ⟧lt = EP-id ℕ
  ⟦ inj-nat ⟧lt = EP-nat
  ⟦ inj-arrow (A-dyn => B-dyn) ⟧lt =
    EP-comp (EP-lift  ⟦ A-dyn ⟧lt  ⟦ B-dyn ⟧lt) EP-fun


  ⟦_⟧tm : {Γ : Ctx} {A : Ty} -> Tm Γ A -> (⟦ Γ ⟧ctx -> L℧ ⟦ A ⟧ty)
  ⟦ var x ⟧tm  = λ ⟦Γ⟧ -> ret (look ⟦Γ⟧ _ x)
  
  ⟦ lda M ⟧tm = λ ⟦Γ⟧ -> ret ( λ N -> ⟦ M ⟧tm (⟦Γ⟧ , N) )
  
  ⟦ app M1 M2 ⟧tm =
    -- λ Γ -> bind (⟦ M1 ⟧tm Γ) λ f -> bind (⟦ M2 ⟧tm Γ) f
    λ Γ -> bind (⟦ M1 ⟧tm Γ) (bind (⟦ M2 ⟧tm Γ))
    
  ⟦ err ⟧tm ⟦Γ⟧ = ℧

  ⟦ up {Γ = Γ2} {A = A} {B = B} A⊑B M ⟧tm =
    λ ⟦Γ⟧ -> mapL (EP.emb ⟦ A⊑B ⟧lt) (⟦ M ⟧tm ⟦Γ⟧)
  -- Equivalently:
  -- EP.emb (EP-L ⟦ A⊑B ⟧lt) (⟦ M ⟧tm ⟦Γ⟧)
    
  ⟦ dn {A = A} {B = B} A⊑B M ⟧tm =
    λ ⟦Γ⟧ -> bind (⟦ M ⟧tm ⟦Γ⟧) (EP.proj ⟦ A⊑B ⟧lt)


  mapL-emb : {A A' : Type} -> (epAA' : EP A A') (a : L℧ A) ->
    mapL (EP.emb epAA') a ≡ EP.emb (EP-L epAA') a
  mapL-emb epAA' a = refl


  --------------------------------------------------------------------------------

  
      
 
