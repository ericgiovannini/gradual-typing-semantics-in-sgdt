
{-# OPTIONS --cubical --rewriting --guarded #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}

open import Common.Later
open import Common.Common

module Semantics.ErrorDomains where -- (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Relation.Binary.Poset
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma


open import Semantics.Predomains
import Semantics.Lift as L℧
import Semantics.Monotone.MonFunCombinators
open import Semantics.StrongBisimulation
open import Semantics.PredomainInternalHom

open import Semantics.Monotone.Base



private
  variable
    ℓ : Level


_$_ : {A B : Predomain} -> ⟨ A ==> B ⟩ -> ⟨ A ⟩ -> ⟨ B ⟩
_$_ f = MonFun.f f

-- Error domains
record ErrorDomain' {ℓ : Level} (k : Clock) : Type (ℓ-suc ℓ) where
  field
    X : Predomain
  module X = PosetStr (X .snd)
  _≤_ = X._≤_
  field
    ℧ : X .fst
    ℧⊥ : ∀ x → ℧ ≤ x
    θ : MonFun (▸''_ k X) X

ErrorDomain : {ℓ : Level} -> Type (ℓ-suc ℓ)
ErrorDomain = Σ[ k ∈ Clock ] ErrorDomain' k


-- Isomorphic error domains (with potentially different clocks) have
-- * Isomorphic predomains
-- * The same error element and proof that it's the bottom element
-- * Potentially different θ functions (since they're indexed by potentially different clocks)

-- A family of error domains indexed by a clock k is

-- Morphism of error domains
record ErrorDomainFun {k k' : Clock} (A : ErrorDomain' {ℓ} k) (B : ErrorDomain' {ℓ} k') : Type where
  open ErrorDomain'
  θA = A .θ
  θB = B .θ
  field
    f :  MonFun (A .X) (B .X)
    f℧ : MonFun.f f (A .℧) ≡ (B .℧)
    fθ : (x~ : ▹ k , ⟨ A .X ⟩) -> (f $ (θA $ x~)) ≡ (θB $ λ t → f $ {!x~ t!})
    


-- Underlying predomain of an error domain
𝕌 : {k : Clock} -> ErrorDomain' {ℓ} k -> Predomain
𝕌 d = ErrorDomain'.X d


-- Later structure on error domains
module _ (k : Clock)  where
  -- open import Semantics.ErrorDomains k
  open ErrorDomain'
  open import Semantics.Monotone.MonFunCombinators
  Domain-▹ : ErrorDomain' {ℓ} k -> ErrorDomain' {ℓ} k
  Domain-▹ A =
    record {
      X  = (▸'' k) (𝕌 A) ;
      ℧ = λ t → ErrorDomain'.℧ A ;
      ℧⊥ = λ x t → ℧⊥ A (x t) ;
      θ = Map▹ k (ErrorDomain'.θ A) }



-- View the lift of a predomain as an error domain (under the provided clock)
𝕃℧ : Predomain → (k : Clock) -> ErrorDomain' {ℓ} k
𝕃℧ A k' = record {
  X = 𝕃 A ; ℧ = L℧.℧ ; ℧⊥ = ord-bot A ;
  θ = record { f = L℧.θ ; isMon = ord-θ-monotone A } }
  where
    open LiftPredomain k'


-- Error domain of monotone functions between a predomain A and an error domain B
arr : (k : Clock) -> Predomain -> ErrorDomain' {ℓ} k -> ErrorDomain' {ℓ} k
arr k A B =
  record {
    X = A ==> (𝕌 B) ;
    ℧ = const-err ;
    ℧⊥ = const-err-bot ;
    θ = θf }
    where
       open ErrorDomain'
       open import Semantics.Monotone.MonFunCombinators k
       const-err : ⟨ A ==> (𝕌 B) ⟩
       const-err = record {
         f = λ _ -> ErrorDomain'.℧ B ;
         isMon = λ _ -> reflexive (𝕌 B) (ErrorDomain'.℧ B) }

       const-err-bot : (f : ⟨ A ==> (𝕌 B) ⟩) -> rel (A ==> (𝕌 B)) const-err f
       const-err-bot f = λ x y x≤y → ErrorDomain'.℧⊥ B (MonFun.f f y)

       θf : MonFun ((▸'' k) (A ==> 𝕌 B)) (A ==> 𝕌 B)
       θf = mCompU {!!} Ap▹

       -- Goal: MonFun (▹ (A ==> 𝕌 B)) (A ==> 𝕌 B)
       -- We will factor this as
       --  (▹ (A ==> 𝕌 B))  ==>  (▹ A ==> ▹ (𝕌 B))  ==>  (A ==> 𝕌 B)
       -- The first function is Ap▹
       -- The second is θB ∘ App ∘ next


module ClockInv
  (A : (k : Clock) -> ErrorDomain' {ℓ} k) where

  open ErrorDomain'

  {-
  to' : {k k' : Clock} ->
    (▹ k' , ▹ k , (⟨ 𝕌 (A k) ⟩ -> ⟨ 𝕌 (A k') ⟩)) ->
                  (⟨ 𝕌 (A k) ⟩ -> ⟨ 𝕌 (A k') ⟩)
  to' {k} {k'} rec = fix (λ rec' x → A k' .θ $ λ t' → rec' t' x)
  -}


  to : {k k' : Clock} -> ⟨ 𝕌 (A k) ⟩ -> ⟨ 𝕌 (A k') ⟩
  


module ClockInvariant
  (A : (k : Clock) -> ErrorDomain' {ℓ} k) where

  open ErrorDomain'

  open import Cubical.Data.Empty

  absurd : {k : Clock} ->
    (▹ k , (⊥ -> ⟨ 𝕌 (A k) ⟩)) -> (⊥ -> ⟨ 𝕌 (A k) ⟩)
  absurd {k} IH fls = (A k .θ) $ λ t → IH t fls
  
  -- Given a family of ErrorDomains indexed by a clock, we can define a function
  -- between the underlying sets of any two members of the family.
  -- TODO this function doesn't do anything, it just keeps adding θ's
  to' : {k k' : Clock} ->
    (▹ k' , (⟨ 𝕌 (A k) ⟩ -> ⟨ 𝕌 (A k') ⟩)) ->
             ⟨ 𝕌 (A k) ⟩ -> ⟨ 𝕌 (A k') ⟩
  to' {k} {k'} rec x1 = (A k' .θ) $ λ t → rec t x1

  to : {k k' : Clock} -> ⟨ 𝕌 (A k) ⟩ -> ⟨ 𝕌 (A k') ⟩
  to = fix to'

  unfold-to : {k k' : Clock} -> to {k} {k'} ≡ to' (next to)
  unfold-to = fix-eq to'

  to'-refl : {k : Clock} ->
    (▹ k , (to' {k} {k} (next to) ≡ id)) ->
            to' {k} {k} (next to) ≡ id
  to'-refl IH = funExt (λ x → {!!})


  to'-mon : {k k' : Clock} ->
    ▹ k' , ({x y : ⟨ 𝕌 (A k) ⟩} -> (rel (𝕌 (A k)) x y) ->
               (rel (𝕌 (A k')) (to' (next to) x) (to' (next to) y))) ->
            {x y : ⟨ 𝕌 (A k) ⟩} -> (rel (𝕌 (A k)) x y) ->
               (rel (𝕌 (A k')) (to' (next to) x) (to' (next to) y))
  to'-mon {k} {k'} IH {x} {y} x≤y = MonFun.isMon (θ (A k')) λ t ->
    transport (sym (λ i → rel (𝕌 (A k')) (unfold-to i x) (unfold-to i y))) (IH t x≤y)

  to'-mon' : {k k' : Clock} -> {x y : ⟨ 𝕌 (A k) ⟩} -> (rel (𝕌 (A k)) x y) ->
    ▹ k' , (rel (𝕌 (A k')) (to' (next to) x) (to' (next to) y)) ->
           (rel (𝕌 (A k')) (to' (next to) x) (to' (next to) y))
  to'-mon' {k} {k'} {x} {y} x≤y IH = MonFun.isMon (θ (A k')) λ t ->
    transport (sym (λ i → rel (𝕌 (A k')) (unfold-to i x) (unfold-to i y))) (IH t)

{- NTS:
 (rel (𝕌 (A k')) (to' (next to) x) (to' (next to) y) ≡
 (rel (𝕌 (A k')) (to x)            (to y)
-}


  to-mon : {k k' : Clock} ->
     {x y : ⟨ 𝕌 (A k) ⟩} -> (rel (𝕌 (A k)) x y) ->
       (rel (𝕌 (A k')) (to x) (to y))
  to-mon {k} {k'} {x} {y} x≤y = transport
    (sym (λ i → rel (𝕌 (A k')) (unfold-to i x) (unfold-to i y)))
    (fix (to'-mon' x≤y))


  To : {k k' : Clock} -> ⟨ 𝕌 (A k) ==> 𝕌 (A k') ⟩
  To {k} {k'} = record { f = to ; isMon = to-mon }

{-
  to' : ∀ k' -> (▹ k , (ErrorDomain' {ℓ} k -> ErrorDomain' {ℓ} k')) -> (ErrorDomain' k -> ErrorDomain' {ℓ} k')
  to' k' rec A =
    record {
      X = A .X ;
      ℧ = A .℧ ;
      ℧⊥ = A .℧⊥ ;
      θ = record {
        f = λ a~ -> MonFun.f (A .θ) λ t -> let foo = rec t A in {!!} ;
        isMon = {!!} } }
-}


{-
bad : {k : Clock} -> {X : Type} ->  ▹ k , ▹ k , X -> ▹ k , X
bad x = λ t → x t t
-}

module _ (k k' : Clock) {A : Type} where
  -- open ErrorDomain
  open import Cubical.Foundations.Isomorphism 
  open import Semantics.Lift
  
  to' : (▹ k' , (L℧ k A -> L℧ k' A)) -> (L℧ k A -> L℧ k' A)
  to' _ (η x) = η x
  to' _ L℧.℧ = L℧.℧
  to' rec (L℧.θ l~) = L℧.θ λ t → rec t (L℧.θ l~)

  to : (L℧ k A -> L℧ k' A)
  to = fix to'

  inv' : (▹ k , (L℧ k' A -> L℧ k A)) -> (L℧ k' A -> L℧ k A)
  inv' _ (η x) = η x
  inv' _ L℧.℧ = L℧.℧
  inv' rec (L℧.θ l~) = L℧.θ (λ t → rec t (L℧.θ l~))

  inv : (L℧ k' A -> L℧ k A)
  inv = fix inv'

  unfold-to : fix (to') ≡ to' (next to)
  unfold-to = fix-eq to'

  unfold-inv : fix (inv') ≡ inv' (next inv)
  unfold-inv = fix-eq inv'


  L℧-Iso :  Iso (L℧ k A) (L℧ k' A)
  L℧-Iso = iso to inv sec retr
    where
      sec' : ▹ k' , (section (to' (next to)) (inv' (next inv))) -> (section (to' (next to)) (inv' (next inv)))
      sec' _ (η x) = refl
      sec' _ L℧.℧ = refl
      sec' IH (L℧.θ l~) = {!!}
        -- cong L℧.θ (later-ext (λ t → let foo = IH t (L℧.θ l~) in let foo' = inj-θ k' _ _ foo in {!t!}))
        -- λ i -> L℧.θ (λ t → IH t (L℧.θ l~) {!i!})
--  L℧.θ (λ t → next to t (L℧.θ (λ t₁ → next inv t₁ (L℧.θ l~))))
--      ≡ L℧.θ l~


      -- cong L℧.θ (later-ext (λ t → let foo = IH t (L℧.θ l~) in {!!}))

      sec : {!!}
      sec = {!!}

      retr' : retract to inv
      retr' = {!!}

      retr : {!!}
      retr = {!!}






{-
-- Predomain to lift Error Domain

𝕃℧ : Predomain → ErrorDomain
𝕃℧ X = record {
  X = 𝕃 X ; ℧ = ℧ ; ℧⊥ = ord-bot X ;
  θ = record { f = θ ; isMon = λ t -> {!!} } }
  where
    -- module X = PosetStr (X .snd)
    -- open Relation X
    open LiftPredomain
-}



-- Experiment with composing relations on error domains
{-

open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation

record MyRel {ℓ} (B1 B2 : ErrorDomain) : Type (ℓ-suc ℓ) where
  open ErrorDomain
  open MonFun
  private
    UB1 = ⟨ 𝕌 B1 ⟩
    UB2 = ⟨ 𝕌 B2 ⟩
    ℧B1 = B1 .℧
    θB1 = B1 .θ
    θB2 = B2 .θ
  field
    Rel : UB1 -> UB2 -> hProp ℓ
    Rel℧ : ∀ (b2 : UB2) -> ⟨ Rel ℧B1 b2 ⟩
    RelΘ : ∀ (b1~ : ▹_,_ k UB1) -> (b2~ : ▹_,_ k UB2) ->
      (▸ (λ t -> ⟨ Rel (b1~ t) (b2~ t) ⟩)) ->
      ⟨ Rel (θB1 .f b1~) (θB2 .f b2~) ⟩

_⊙_ : {ℓ : Level} {B1 B2 B3 : ErrorDomain}
  (S : MyRel {ℓ} B1 B2) (R : MyRel {ℓ} B2 B3) ->  MyRel {ℓ} B1 B3
_⊙_ {ℓ} {B1} {B2} {B3} S R = record {
  Rel = λ b1 b3 → (∃[ b2 ∈ UB2 ] ⟨ S .Rel b1 b2 ⟩ × ⟨ R .Rel b2 b3 ⟩) , {!!} ;
  Rel℧ = λ b3 -> ∣ (B2 .℧ , (S .Rel℧ (B2 .℧)) , R .Rel℧ b3) ∣₁ ;
  RelΘ = λ b1~ b2~ H → ∣ (θB2 .f {!!} , {!!}) ∣₁ }
  where
    open ErrorDomain
    open MonFun
    open MyRel
    UB1 = ⟨ 𝕌 B1 ⟩
    UB2 = ⟨ 𝕌 B2 ⟩
    UB3 = ⟨ 𝕌 B3 ⟩
    θB2 = B2 .θ
-}

