{-# OPTIONS --rewriting --guarded #-}

{-# OPTIONS --lossy-unification #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}

open import Common.Later

module Semantics.Concrete.DoublePoset.ErrorDomain (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Relation.Binary.Order.Poset.Base
open import Cubical.Relation.Binary.Base
open import Cubical.Reflection.Base
open import Cubical.Reflection.RecordEquiv
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Data.Sigma

open import Common.Common
open import Semantics.Concrete.DoublePoset.Base
open import Semantics.Concrete.DoublePoset.Morphism
open import Semantics.Concrete.DoublePoset.Constructions
  renaming (module Clocked to ClockedConstructions)
open import Semantics.Concrete.DoublePoset.DPMorRelation
open import Semantics.Concrete.DoublePoset.DblPosetCombinators
open import Semantics.Concrete.DoublePoset.PBSquare


private
  variable
    ℓ ℓ'  : Level
    ℓ≤ ℓ≈ : Level
    --
    ℓA  ℓ≤A  ℓ≈A     : Level
    ℓA' ℓ≤A' ℓ≈A'    : Level
    ℓAᵢ  ℓ≤Aᵢ  ℓ≈Aᵢ  : Level
    ℓAᵢ' ℓ≤Aᵢ' ℓ≈Aᵢ' : Level
    ℓAₒ  ℓ≤Aₒ  ℓ≈Aₒ  : Level
    ℓAₒ' ℓ≤Aₒ' ℓ≈Aₒ' : Level
    ℓc               : Level
    ℓcᵢ ℓcₒ          : Level
    --
    ℓB  ℓ≤B  ℓ≈B     : Level
    ℓB' ℓ≤B' ℓ≈B'    : Level
    ℓBᵢ  ℓ≤Bᵢ  ℓ≈Bᵢ  : Level
    ℓBᵢ' ℓ≤Bᵢ' ℓ≈Bᵢ' : Level
    ℓBₒ  ℓ≤Bₒ  ℓ≈Bₒ  : Level
    ℓBₒ' ℓ≤Bₒ' ℓ≈Bₒ' : Level
    ℓd               : Level
    ℓdᵢ ℓdₒ          : Level
    --
    ℓB₁  ℓ≤B₁  ℓ≈B₁  : Level
    ℓB₂  ℓ≤B₂  ℓ≈B₂  : Level
    ℓB₃  ℓ≤B₃  ℓ≈B₃  : Level
    ℓd' : Level


private
  ▹_ : Type ℓ -> Type ℓ
  ▹ A = ▹_,_ k A

module _ where

  open ClockedConstructions k

  record ErrorDomainStr {ℓ : Level} (ℓ≤ ℓ≈ : Level) (B : Type ℓ) :
    Type (ℓ-suc (ℓ-max (ℓ-max ℓ ℓ≤) ℓ≈)) where

    field
      is-predomain : PosetBisimStr ℓ≤ ℓ≈ B
      
    open PosetBisimStr is-predomain public
    Pre : PosetBisim ℓ ℓ≤ ℓ≈
    Pre = B , is-predomain
  
    field
      ℧ : B
      ℧⊥ : ∀ (x : B) → ℧ ≤ x
      θ : PBMor (PB▹ Pre) Pre


  ErrorDomain : ∀ ℓ ℓ≤ ℓ≈ → Type (ℓ-suc (ℓ-max (ℓ-max ℓ ℓ≤) ℓ≈))
  ErrorDomain ℓ ℓ≤ ℓ≈ = TypeWithStr ℓ (ErrorDomainStr ℓ≤ ℓ≈)

  ErrorDomain→Predomain : {ℓ ℓ≤ ℓ≈ : Level} → ErrorDomain ℓ ℓ≤ ℓ≈ → PosetBisim ℓ ℓ≤ ℓ≈
  ErrorDomain→Predomain B = ⟨ B ⟩ , (B .snd .is-predomain)
    where open ErrorDomainStr

  -- TODO iso with sigma type
  -- TODO Error domains form a Set







  -- Vertical morphisms of error domains. These are defined to be
  -- morphisms of the underlying predomains that respect the algebraic
  -- structure of the error domains.
  record ErrorDomMor
    (Bᵢ : ErrorDomain ℓBᵢ ℓ≤Bᵢ ℓ≈Bᵢ)
    (Bₒ : ErrorDomain ℓBₒ ℓ≤Bₒ ℓ≈Bₒ) :
    Type (ℓ-max (ℓ-max ℓBᵢ (ℓ-max ℓ≤Bᵢ ℓ≈Bᵢ)) (ℓ-max ℓBₒ (ℓ-max ℓ≤Bₒ ℓ≈Bₒ))) where
    
    module Bᵢ = ErrorDomainStr (Bᵢ .snd)
    module Bₒ = ErrorDomainStr (Bₒ .snd)
    field
      f  : PBMor (ErrorDomain→Predomain Bᵢ) (ErrorDomain→Predomain Bₒ)
      f℧ : PBMor.f f (Bᵢ.℧) ≡ (Bₒ.℧)
      fθ : (x~ : ▹ ⟨ Bᵢ ⟩) -> (f $ (Bᵢ.θ $ x~)) ≡ (Bₒ.θ $ (λ t → f $ x~ t))

  -- TODO iso with sigma type
  -- TODO vertical morphisms form a Set








  -- Identity and composition of vertical morphisms.
  


  -- Horizontal morphisms of error domains. These are defined to be
  -- relations of the underlying predomains that respect the algebraic
  -- structure.
  record ErrorDomRel
    (B  : ErrorDomain ℓB  ℓ≤B  ℓ≈B)
    (B' : ErrorDomain ℓB' ℓ≤B' ℓ≈B')
    (ℓd : Level) :
    Type (ℓ-max (ℓ-max (ℓ-max ℓB ℓ≤B) (ℓ-max ℓB' ℓ≤B')) (ℓ-suc ℓd)) where
    
    open PBMor
    module B  = ErrorDomainStr (B  .snd)
    module B' = ErrorDomainStr (B' .snd)
  
    field
      UR : PBRel (ErrorDomain→Predomain B) (ErrorDomain→Predomain B') ℓd
      R℧ : ∀ (b' : ⟨ B' ⟩) → UR .PBRel.R B.℧ b'
      Rθ : ∀ (b~ : ▹ ⟨ B ⟩) → (b'~ : ▹ ⟨ B' ⟩) ->
        (▸ (λ t → UR .PBRel.R (b~ t) (b'~ t))) →
        UR .PBRel.R (B.θ $ b~) (B'.θ $ b'~)

    _R_ : ⟨ B ⟩ → ⟨ B' ⟩ → Type ℓd
    _R_ = UR .PBRel.R

    -- open PBRel UR public

  syntax EDRel d b b' = b R[ d ] b'


  -- TODO iso with sigma type
  -- TODO horizontal morphisms form a Set








  -- Identity and composition of horizontal morphisms
  module HorizontalComp
    {B₁ : ErrorDomain ℓB₁ ℓ≤B₁ ℓ≈B₁}
    {B₂ : ErrorDomain ℓB₂ ℓ≤B₂ ℓ≈B₂}
    {B₃ : ErrorDomain ℓB₃ ℓ≤B₃ ℓ≈B₃}
    (d  : ErrorDomRel B₁ B₂ ℓd)
    (d' : ErrorDomRel B₂ B₃ ℓd') where

    open ErrorDomRel

    module B₁ = ErrorDomainStr (B₁ .snd)
    module B₂ = ErrorDomainStr (B₂ .snd)
    module B₃ = ErrorDomainStr (B₃ .snd)

    module d  = ErrorDomRel d
    module d' = ErrorDomRel d'

    lvl : Level
    lvl = ℓ-max ℓ1 ℓ2
     where
       ℓ1 = ℓ-max (ℓ-max ℓB₁ ℓB₂) ℓB₃
       ℓ2 = ℓ-max (ℓ-max ℓ≤B₁ ℓ≤B₃) (ℓ-max ℓd ℓd')


    -- Unerlying relation for the composition of d and d'.
    data HCRel :
      ⟨ B₁ ⟩ → ⟨ B₃ ⟩ → Type lvl where
      inj       : ∀ b₁ b₂ b₃ → b₁ d.R b₂ → b₂ d'.R b₃ → HCRel b₁ b₃
      up-closed : ∀ b₁ b₃ b₃' → HCRel b₁ b₃ → b₃ B₃.≤ b₃' → HCRel b₁ b₃'
      dn-closed : ∀ b₁' b₁ b₃ → b₁' B₁.≤ b₁ → HCRel b₁ b₃ → HCRel b₁' b₃
      pres℧     : ∀ b₃ → HCRel B₁.℧ b₃
      presθ     : ∀ (b₁~ : ▹ ⟨ B₁ ⟩) (b₃~ : ▹ ⟨ B₃ ⟩) →
        ▸ (λ t → HCRel (b₁~ t) (b₃~ t)) → HCRel (B₁.θ $ b₁~) (B₃.θ $ b₃~)
      is-prop   : ∀ b₁ b₃ → isProp (HCRel b₁ b₃)

    -- Now we give it the relation defined above the structure of an error domain relation.
    HorizComp : ErrorDomRel B₁ B₃ lvl
    HorizComp .UR .PBRel.R = HCRel
    HorizComp .UR .PBRel.is-prop-valued = is-prop
    HorizComp .UR .PBRel.is-antitone = dn-closed _ _ _
    HorizComp .UR .PBRel.is-monotone = up-closed _ _ _   
    HorizComp .R℧ = pres℧
    HorizComp .Rθ = presθ

    -- Universal property of the horizontal composition.



    



  module HorizontalCompBad
    {B₁ : ErrorDomain ℓB₁ ℓ≤B₁ ℓ≈B₁}
    {B₂ : ErrorDomain ℓB₂ ℓ≤B₂ ℓ≈B₂}
    {B₃ : ErrorDomain ℓB₃ ℓ≤B₃ ℓ≈B₃}
    (d  : ErrorDomRel B₁ B₂ ℓd)
    (d' : ErrorDomRel B₂ B₃ ℓd') where

    open ErrorDomRel

    module B₁ = ErrorDomainStr (B₁ .snd)
    module B₂ = ErrorDomainStr (B₂ .snd)
    module B₃ = ErrorDomainStr (B₃ .snd)

    module d  = ErrorDomRel d
    module d' = ErrorDomRel d'


    -- Unerlying relation for the composition of d and d'.
    data HCRel :
      ⟨ B₁ ⟩ → ⟨ B₃ ⟩ → Type (ℓ-max (ℓ-max (ℓ-max ℓB₁ ℓB₂) ℓB₃) (ℓ-max ℓd ℓd')) where
      inj   : ∀ b₁ b₂ b₃ → b₁ d.R b₂ → b₂ d'.R b₃ → HCRel b₁ b₃
      pres℧ : ∀ b₃ → HCRel B₁.℧ b₃
      presθ : ∀ (b₁~ : ▹ ⟨ B₁ ⟩) (b₃~ : ▹ ⟨ B₃ ⟩) →
        ▸ (λ t → HCRel (b₁~ t) (b₃~ t)) → HCRel (B₁.θ $ b₁~) (B₃.θ $ b₃~)
      is-prop : ∀ b₁ b₃ → isProp (HCRel b₁ b₃)

    -- Eliminator
    --
    -- Question: Does X need to be parameterized by the
    -- proof that b₁ and b₃ are related?  Since HCRel is Prop-valued,
    -- then for a given b₁ and b₃ there is at most one proof that they
    -- are related. But we still need to know that they are related,
    -- so X needs to take a proof as a parameter.
    module Elim 
      {X : ∀ b₁ b₃ → HCRel b₁ b₃ → Type ℓ}
      (inj* : ∀ b₁ b₂ b₃ → (R₁₂ : b₁ d.R b₂) → (R₂₃ : b₂ d'.R b₃) →
        X b₁ b₃ (inj b₁ b₂ b₃ R₁₂ R₂₃))
      (pres℧* : ∀ b₃ →
        X B₁.℧ b₃ (pres℧ b₃))
      (presθ* : ∀ (b₁~ : ▹ ⟨ B₁ ⟩) (b₃~ : ▹ ⟨ B₃ ⟩) → (H~ : ▸ (λ t → HCRel (b₁~ t) (b₃~ t))) →
        X (B₁.θ $ b₁~) (B₃.θ $ b₃~) (presθ b₁~ b₃~ H~))
      (is-prop* : ∀ b₁ b₃ R₁₃ → isProp (X b₁ b₃ R₁₃)) where
    
      ℧₁ = B₁.℧

      f : ∀ b₁ b₃ (R₁₃ : HCRel b₁ b₃) → X b₁ b₃ R₁₃
      f b₁ b₃ (inj .b₁ b₂ .b₃ R₁₂ R₂₃) = inj* b₁ b₂ b₃ R₁₂ R₂₃
      f .℧₁ b₃ (pres℧ .b₃) = pres℧* b₃
      f .(B₁.θ $ b₁~) .(B₃.θ $ b₃~) (presθ b₁~ b₃~ H~) = presθ* b₁~ b₃~ H~
      f b₁ b₃ (is-prop .b₁ .b₃ p q i) = {!!}
      

    test : ∀ b₁ b₃ → HCRel b₁ b₃ → ∃[ b₂ ∈ ⟨ B₂ ⟩ ] (b₁ d.R b₂) × (b₂ d'.R b₃)
    test b₁ b₃ (inj .b₁ b₂ .b₃ R₁₂ R₂₃) = ∣ b₂ , R₁₂ , R₂₃ ∣₁
    test ℧₁ b₃ (pres℧ .b₃) = ∣ B₂.℧ , {!!} , {!!}  ∣₁
    test .(B₁.θ $ b₁~) .(B₃.θ $ b₃~) (presθ b₁~ b₃~ H~) = {!!}
    test b₁ b₃ (is-prop .b₁ .b₃ p q i) = {!!}


    -- Now we give it the relation defined above the structure of an error domain relation.
    HorizComp : ErrorDomRel B₁ B₃ (ℓ-max (ℓ-max (ℓ-max ℓB₁ ℓB₂) ℓB₃) (ℓ-max ℓd ℓd'))
    HorizComp .UR .PBRel.R = HCRel
    HorizComp .UR .PBRel.is-prop-valued = is-prop
    HorizComp .UR .PBRel.is-antitone = {!!}
    HorizComp .UR .PBRel.is-monotone {x = b₁} {y = b₃} {y' = b₃'} (inj .b₁ b₂ .b₃ R₁₂ R₂₃) b₃≤b₃' = inj b₁ b₂ b₃' R₁₂ (d' .UR .PBRel.is-monotone R₂₃ b₃≤b₃')
    HorizComp .UR .PBRel.is-monotone {x = b₁} {y = b₃} {y' = b₃'} (pres℧ a) b₃≤b₃' = pres℧ b₃'
    HorizComp .UR .PBRel.is-monotone {x = b₁} {y = b₃} {y' = b₃'} (presθ b₁~ b₃~ H~) b₃≤b₃' = rec (is-prop _ _) (λ (b₂ , R₁₂ , R₂₃) → {!!}) (test b₁ b₃ (presθ b₁~ b₃~ H~)) -- inj (B₁.θ $ b₁~) {!!} b₃' {!!} {!!}
    HorizComp .UR .PBRel.is-monotone {x = b₁} {y = b₃} {y' = b₃'} (is-prop r s p q i) b₃≤b₃' = {!!}
    HorizComp .R℧ = pres℧
    HorizComp .Rθ = presθ




  ErrorDomSq :
    {Bᵢ  : ErrorDomain ℓBᵢ  ℓ≤Bᵢ  ℓ≈Bᵢ}
    {Bᵢ' : ErrorDomain ℓBᵢ' ℓ≤Bᵢ' ℓ≈Bᵢ'}
    {Bₒ  : ErrorDomain ℓBₒ  ℓ≤Bₒ  ℓ≈Bₒ} 
    {Bₒ' : ErrorDomain ℓBₒ' ℓ≤Bₒ' ℓ≈Bₒ'} →
    (dᵢ  : ErrorDomRel Bᵢ Bᵢ' ℓdᵢ) →
    (dₒ  : ErrorDomRel Bₒ Bₒ' ℓdₒ) →
    (ϕ   : ErrorDomMor Bᵢ  Bₒ) →
    (ϕ'  : ErrorDomMor Bᵢ' Bₒ') →
    Type (ℓ-max (ℓ-max ℓBᵢ ℓBᵢ') (ℓ-max ℓdᵢ ℓdₒ))
  ErrorDomSq dᵢ dₒ ϕ ϕ' =
    PBSq (dᵢ .ErrorDomRel.UR) (dₒ .ErrorDomRel.UR)
         (ϕ .ErrorDomMor.f)  (ϕ' .ErrorDomMor.f)

  -- Identity and composition of squares are given by identity and
  -- composition of the underlying predomain squares.





  -----------------------------
  -----------------------------
  -- Functors F, U, and ⟶
  -----------------------------
  -----------------------------


  -------------------
  -- The U functor.
  -------------------
  U-ob : ErrorDomain ℓ ℓ≤ ℓ≈ → PosetBisim ℓ ℓ≤ ℓ≈
  U-ob = ErrorDomain→Predomain


  U-mor :
    {Bᵢ : ErrorDomain ℓBᵢ ℓ≤Bᵢ ℓ≈Bᵢ}
    {Bₒ : ErrorDomain ℓBₒ ℓ≤Bₒ ℓ≈Bₒ} →
    ErrorDomMor Bᵢ Bₒ →
    PBMor (U-ob Bᵢ) (U-ob Bₒ)
  U-mor ϕ = ϕ .ErrorDomMor.f


  U-rel :
    {B  : ErrorDomain ℓB  ℓ≤B  ℓ≈B}
    {B' : ErrorDomain ℓB' ℓ≤B' ℓ≈B'} →
    ErrorDomRel B B' ℓd →
    PBRel (U-ob B) (U-ob B') ℓd
  U-rel d = d .ErrorDomRel.UR


  U-sq :
    {Bᵢ  : ErrorDomain ℓBᵢ  ℓ≤Bᵢ  ℓ≈Bᵢ}
    {Bᵢ' : ErrorDomain ℓBᵢ' ℓ≤Bᵢ' ℓ≈Bᵢ'}
    {Bₒ  : ErrorDomain ℓBₒ  ℓ≤Bₒ  ℓ≈Bₒ} 
    {Bₒ' : ErrorDomain ℓBₒ' ℓ≤Bₒ' ℓ≈Bₒ'} →
    (dᵢ  : ErrorDomRel Bᵢ Bᵢ' ℓdᵢ) →
    (dₒ  : ErrorDomRel Bₒ Bₒ' ℓdₒ) →
    (ϕ   : ErrorDomMor Bᵢ  Bₒ) →
    (ϕ'  : ErrorDomMor Bᵢ' Bₒ') →
    ErrorDomSq dᵢ dₒ ϕ ϕ' →
    PBSq (U-rel dᵢ) (U-rel dₒ) (U-mor ϕ) (U-mor ϕ')
  U-sq dᵢ dₒ f g sq = sq


  -- TODO lax functoriality of U with respect to relational composition




  -------------------
  -- The ⟶ functor.
  -------------------
  open ErrorDomMor
  
  module _ (A : PosetBisim ℓA ℓ≤A ℓ≈A) (B : ErrorDomain ℓB ℓ≤B ℓ≈B) where
    open ErrorDomainStr
    open PBMor

    private
      module B = ErrorDomainStr (B .snd)

    -- Given a predomain A and an error domain B, we can form the
    -- error domain of all predomain morphisms from A to B.
    Arr-ob :
      ErrorDomain
        (ℓ-max (ℓ-max (ℓ-max ℓA ℓ≤A) ℓ≈A) (ℓ-max (ℓ-max ℓB ℓ≤B) ℓ≈B))
        (ℓ-max ℓA ℓ≤B)
        (ℓ-max (ℓ-max ℓA ℓ≈A) ℓ≈B)
    Arr-ob .fst = PBMor A (U-ob B)
    Arr-ob .snd .is-predomain = (A ==> (U-ob B)) .snd
    Arr-ob .snd .℧ = Const (U-ob B) (B .snd .℧)
    Arr-ob .snd .℧⊥ f x = B .snd .℧⊥ (f $ x)
    Arr-ob .snd .θ .f g~ = aux
      -- This can likely be defined using combinators
      where
        aux : Arr-ob .fst
        aux .f x = B.θ $ (λ t → g~ t $ x)
        aux .isMon x1≤x2 = B.θ .isMon (λ t → (g~ t) .isMon x1≤x2)
        aux .pres≈ x1≈x2 = B.θ .pres≈ (λ t → (g~ t) .pres≈ x1≈x2)
    Arr-ob .snd .θ .isMon {g1~} {g2~} g1~≤g2~ x =
      B.θ .isMon (λ t → g1~≤g2~ t x)
    Arr-ob .snd .θ .pres≈ {g1~} {g2~} g1~≈g2~ x x' x≈x' =
      B.θ .pres≈ (λ t → g1~≈g2~ t x x' x≈x')
    

  _⟶ob_ : (A : PosetBisim ℓA ℓ≤A ℓ≈A) (B : ErrorDomain ℓB ℓ≤B ℓ≈B) →
    ErrorDomain
        (ℓ-max (ℓ-max (ℓ-max ℓA ℓ≤A) ℓ≈A) (ℓ-max (ℓ-max ℓB ℓ≤B) ℓ≈B))
        (ℓ-max ℓA ℓ≤B)
        (ℓ-max (ℓ-max ℓA ℓ≈A) ℓ≈B)
  A ⟶ob B = Arr-ob A B


  -- Action of ⟶ on vertical morphisms
  _⟶mor_ :
    {Aᵢ : PosetBisim  ℓAᵢ ℓ≤Aᵢ ℓ≈Aᵢ} {Aₒ : PosetBisim  ℓAₒ ℓ≤Aₒ ℓ≈Aₒ}
    {Bᵢ : ErrorDomain ℓBᵢ ℓ≤Bᵢ ℓ≈Bᵢ} {Bₒ : ErrorDomain ℓBₒ ℓ≤Bₒ ℓ≈Bₒ} →
    (f : PBMor Aₒ Aᵢ) (ϕ : ErrorDomMor Bᵢ Bₒ) → ErrorDomMor (Aᵢ ⟶ob Bᵢ) (Aₒ ⟶ob Bₒ)
  (f ⟶mor ϕ) .f = f ~-> (U-mor ϕ)
  (f ⟶mor ϕ) .f℧ = eqPBMor _ _ (funExt (λ _ → ϕ .f℧))
  (f ⟶mor ϕ) .fθ = {!!} 

  -- Functoriality (preservation of identity and composition)








  -- Action of ⟶ on horizontal morphisms
  module _ {A : PosetBisim ℓA ℓ≤A ℓ≈A}  {A' : PosetBisim ℓA' ℓ≤A' ℓ≈A'}
           {B : ErrorDomain ℓB ℓ≤B ℓ≈B} {B' : ErrorDomain ℓB' ℓ≤B' ℓ≈B'}
           (c : PBRel A A' ℓc) (d : ErrorDomRel B B' ℓd) where
           
    open ErrorDomainStr
    open ErrorDomRel
    private
      --module B  = ErrorDomainStr (B  .snd)
      --module B' = ErrorDomainStr (B' .snd)

      module c = PBRel c
      module d = ErrorDomRel d
    
    Arr-rel : ErrorDomRel (A ⟶ob B) (A' ⟶ob B') (ℓ-max (ℓ-max ℓA ℓA') (ℓ-max ℓc ℓd))
    Arr-rel .UR = c ==>pbmonrel (U-rel d)
    Arr-rel .R℧ f x y xRy = d.R℧ (PBMor.f f y)
    Arr-rel .Rθ = λ f~ g~ f~Rg~ x y xRy → d.Rθ _ _ (λ t → f~Rg~ t x y xRy)


  _⟶rel_ : {A : PosetBisim ℓA ℓ≤A ℓ≈A}  {A' : PosetBisim ℓA' ℓ≤A' ℓ≈A'}
            {B : ErrorDomain ℓB ℓ≤B ℓ≈B} {B' : ErrorDomain ℓB' ℓ≤B' ℓ≈B'}
            (c : PBRel A A' ℓc) (d : ErrorDomRel B B' ℓd) →
            ErrorDomRel (A ⟶ob B) (A' ⟶ob B') (ℓ-max (ℓ-max ℓA ℓA') (ℓ-max ℓc ℓd))
  c ⟶rel d = Arr-rel c d           


  -- Action of ⟶ on squares
  



