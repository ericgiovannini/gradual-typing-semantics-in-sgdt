{-# OPTIONS --rewriting --guarded #-}

{-# OPTIONS --lossy-unification #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}

open import Common.Later

module Semantics.Concrete.DoublePoset.ErrorDomain (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

open import Cubical.Relation.Binary.Order.Poset.Base
open import Cubical.Relation.Binary.Base
open import Cubical.Reflection.Base
open import Cubical.Reflection.RecordEquiv
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Data.Sigma

open import Cubical.Reflection.Base
open import Cubical.Reflection.RecordEquiv

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
    ℓB₁   ℓ≤B₁   ℓ≈B₁   : Level
    ℓB₁'  ℓ≤B₁'  ℓ≈B₁'  : Level
    ℓB₂   ℓ≤B₂   ℓ≈B₂   : Level
    ℓB₂'  ℓ≤B₂'  ℓ≈B₂'  : Level
    ℓB₃   ℓ≤B₃   ℓ≈B₃   : Level
    ℓB₃'  ℓ≤B₃'  ℓ≈B₃'  : Level
    ℓd₁ ℓd₂ ℓd₃ ℓd' : Level

    ℓA₁   ℓ≤A₁   ℓ≈A₁   : Level
    ℓA₂   ℓ≤A₂   ℓ≈A₂   : Level
    ℓA₃   ℓ≤A₃   ℓ≈A₃   : Level
    ℓc' : Level

    ℓBᵢ₁  ℓ≤Bᵢ₁  ℓ≈Bᵢ₁  : Level
    ℓBₒ₁  ℓ≤Bₒ₁  ℓ≈Bₒ₁  : Level
    ℓBᵢ₂  ℓ≤Bᵢ₂  ℓ≈Bᵢ₂  : Level
    ℓBₒ₂  ℓ≤Bₒ₂  ℓ≈Bₒ₂  : Level
    ℓBᵢ₃  ℓ≤Bᵢ₃  ℓ≈Bᵢ₃  : Level
    ℓBₒ₃  ℓ≤Bₒ₃  ℓ≈Bₒ₃  : Level
    ℓdᵢ₁ ℓdₒ₁ ℓdᵢ₂ ℓdₒ₂ : Level


private
  ▹_ : Type ℓ -> Type ℓ
  ▹ A = ▹_,_ k A


-----------------
-- Error domains
-----------------

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

    module θ = PBMor θ


  ErrorDomain : ∀ ℓ ℓ≤ ℓ≈ → Type (ℓ-suc (ℓ-max (ℓ-max ℓ ℓ≤) ℓ≈))
  ErrorDomain ℓ ℓ≤ ℓ≈ = TypeWithStr ℓ (ErrorDomainStr ℓ≤ ℓ≈)

  ErrorDomain→Predomain : {ℓ ℓ≤ ℓ≈ : Level} → ErrorDomain ℓ ℓ≤ ℓ≈ → PosetBisim ℓ ℓ≤ ℓ≈
  ErrorDomain→Predomain B = ⟨ B ⟩ , (B .snd .is-predomain)
    where open ErrorDomainStr

  -- TODO iso with sigma type
  -- TODO Error domains form a Set
  







  mkErrorDomain :
    (A : PosetBisim ℓA ℓ≤A ℓ≈A) →
    (℧ : ⟨ A ⟩) →
    (℧⊥ : (∀ (x : ⟨ A ⟩) → (A .snd .PosetBisimStr._≤_) ℧ x)) →
    (θ : PBMor (PB▹ A) A) → ErrorDomain ℓA ℓ≤A ℓ≈A
  mkErrorDomain A _ _ _ .fst = ⟨ A ⟩
  mkErrorDomain A _ _ _ .snd .ErrorDomainStr.is-predomain = A .snd
  mkErrorDomain A ℧ _ _ .snd .ErrorDomainStr.℧ = ℧
  mkErrorDomain A _ ℧⊥ _ .snd .ErrorDomainStr.℧⊥ = ℧⊥
  mkErrorDomain A _ _ θ .snd .ErrorDomainStr.θ = θ

  ---------------------------------------
  -- Vertical morphisms of error domains
  ---------------------------------------

  -- A vertical morphism of error domaisn is defined to be
  -- a morphism of the underlying predomains that respects the algebraic
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

    open PBMor f public renaming (f to fun)

    --fun : _
    --fun = f .PBMor.f

  -- TODO iso with sigma type
  -- TODO vertical morphisms form a Set






  -- Equality of error domain morphisms
  module _
    {Bᵢ : ErrorDomain ℓBᵢ ℓ≤Bᵢ ℓ≈Bᵢ}
    {Bₒ : ErrorDomain ℓBₒ ℓ≤Bₒ ℓ≈Bₒ}
    (ϕ ϕ'  : ErrorDomMor Bᵢ Bₒ) where

    private
      module ϕ  = ErrorDomMor ϕ
      module ϕ' = ErrorDomMor ϕ'

    eqErrorDomMor :
      ϕ.fun ≡ ϕ'.fun → ϕ ≡ ϕ'
    eqErrorDomMor = {!!} -- TODO





  -- Identity and composition of vertical morphisms.
  IdE : {B : ErrorDomain ℓB ℓ≤B ℓ≈B} → ErrorDomMor B B
  IdE .ErrorDomMor.f = Id
  IdE .ErrorDomMor.f℧ = refl
  IdE .ErrorDomMor.fθ x~ = refl


  module CompErrorDomMor
    {B₁ : ErrorDomain ℓB₁ ℓ≤B₁ ℓ≈B₁}
    {B₂ : ErrorDomain ℓB₂ ℓ≤B₂ ℓ≈B₂}
    {B₃ : ErrorDomain ℓB₃ ℓ≤B₃ ℓ≈B₃}
    (ϕ  : ErrorDomMor B₁ B₂)
    (ϕ' : ErrorDomMor B₂ B₃) where

      module ϕ  = ErrorDomMor ϕ
      module ϕ' = ErrorDomMor ϕ'
      open ErrorDomMor
    
      CompE : ErrorDomMor B₁ B₃
      CompE .f = Comp ϕ.f ϕ'.f
      CompE .f℧ = (λ i → ϕ'.f $ (ϕ.f℧ i)) ∙ ϕ'.f℧
      CompE .fθ x~ = (λ i → ϕ'.f $ ϕ.fθ x~ i) ∙ (ϕ'.fθ (λ t → ϕ.f $ (x~ t)))
  

  _∘ed_ :
    {B₁ : ErrorDomain ℓB₁ ℓ≤B₁ ℓ≈B₁}
    {B₂ : ErrorDomain ℓB₂ ℓ≤B₂ ℓ≈B₂}
    {B₃ : ErrorDomain ℓB₃ ℓ≤B₃ ℓ≈B₃}
    (ϕ' : ErrorDomMor B₂ B₃)
    (ϕ  : ErrorDomMor B₁ B₂) →
    ErrorDomMor B₁ B₃
  ϕ' ∘ed ϕ = CompErrorDomMor.CompE ϕ ϕ'


  -- Identity and associativity laws for composition

  -- CompED-IdL







  ------------------------------------------
  -- Horizontal morphisms of error domains
  ------------------------------------------
  
  -- A horizontal morphism of error domains is defined to be a
  -- relation of the underlying predomains that respects the algebraic
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

    -- _R_ : ⟨ B ⟩ → ⟨ B' ⟩ → Type ℓd
    -- _R_ = UR .PBRel.R

    -- rel : ⟨ B ⟩ → ⟨ B' ⟩ → Type ℓd
    -- rel = UR .PBRel.R

    open PBRel UR public
    -- (can use fields from PBRel as well as the _rel_ shorthand)

  syntax rel d b b' = b R[ d ] b'


  -- Iso with sigma type
  unquoteDecl EDRelIsoΣ = declareRecordIsoΣ EDRelIsoΣ (quote ErrorDomRel)
  

  -- Horizontal morphisms of error domains form a Set
  EDRelIsSet :
    {B  : ErrorDomain ℓB  ℓ≤B  ℓ≈B}
    {B' : ErrorDomain ℓB' ℓ≤B' ℓ≈B'} →
    isSet (ErrorDomRel B B' ℓd)
  EDRelIsSet {B = B} {B' = B'} =
    isSetRetract
      (Iso.fun EDRelIsoΣ) (Iso.inv EDRelIsoΣ) (Iso.leftInv EDRelIsoΣ)
      (isSetΣ
          (isSetPBRel {A = ErrorDomain→Predomain B} {A' = ErrorDomain→Predomain B'})
          (λ R → isSet×
            (isProp→isSet (isPropΠ (λ _ → R .PBRel.is-prop-valued _ _)))
            (isProp→isSet (isPropΠ3 (λ _ _ _ → R .PBRel.is-prop-valued _ _ )))))


  -- Equality of horizontal morphisms

  -- TODO
  





  -- Identity and composition of horizontal morphisms
  
  idEDRel : (B : ErrorDomain ℓB ℓ≤B ℓ≈B) -> ErrorDomRel B B ℓ≤B
  idEDRel B .ErrorDomRel.UR = idPRel (ErrorDomain→Predomain B)
  idEDRel B .ErrorDomRel.R℧ x =
    -- This is just the fact that ℧ is the bottom element
    B .snd .ErrorDomainStr.℧⊥ x
  idEDRel B .ErrorDomRel.Rθ x1~ x2~ =
    -- This is just the monotonicity of θ
    B .snd .ErrorDomainStr.θ .PBMor.isMon


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
      inj       : ∀ b₁ b₂ b₃ → b₁ d.rel b₂ → b₂ d'.rel b₃ → HCRel b₁ b₃
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

{-
    -- TODO universal property of the horizontal composition
    module _ {ℓR : Level} (S : ErrorDomRel B₁ B₃ ℓR) where

      module S = ErrorDomRel S

      -- To eliminate from a proof of b₁ (d ⊙ d') b₃ into another
      -- error domain relation S from B₁ to B₃, it suffices to assume
      -- the existence of a b₂ ∈ B₂ such that b₁ d b₂ and b₂ d' b₃,
      -- and show under that assumption that b₁ S b₃.
      --
      -- In other words, the client gets to assume that there is some
      -- intermediate b₂ such that b₁ d b₂ and b₂ d' b₃.  If under
      -- this assumption, the client proves b₁ S b₃, then b₁ (d ⊙ d')
      -- b₃ implies that b₁ S b₃.
      ElimHorizComp :
        (∀ b₁ b₃ → Σ[ b₂ ∈ ⟨ B₂ ⟩ ] (b₁ d.rel b₂ × b₂ d'.rel b₃) → S.EDRel b₁ b₃) →
        ∀ b₁ b₃ → HCRel b₁ b₃ → S.EDRel b₁ b₃
      ElimHorizComp H b₁ b₃ (inj .b₁ b₂ .b₃ R₁₂ R₂₃) = H b₁ b₃ (b₂ , R₁₂ , R₂₃)
      ElimHorizComp H b₁ b₃' (up-closed .b₁ b₃ .b₃' b₁Rb₃ b₃≤b₃') = {!!}
      ElimHorizComp H b₁' b₃ (dn-closed .b₁' b₁ .b₃ b₁'≤b₁ b₁Rb₃) = {!!}
      ElimHorizComp H .(B₁.℧) b₃ (pres℧ .b₃) = S.R℧ b₃
      ElimHorizComp H .(B₁.θ $ b₁~) .(B₃.θ $ b₃~) (presθ b₁~ b₃~ H~) =
        S.Rθ b₁~ b₃~ (λ t → ElimHorizComp H (b₁~ t) (b₃~ t) (H~ t))
      ElimHorizComp H b₁ b₃ (is-prop .b₁ .b₃ p q i) =
        S.is-prop-valued b₁ b₃ (ElimHorizComp H b₁ b₃ p) (ElimHorizComp H b₁ b₃ q) i
-}



  _⊙ed_ :
    {B₁ : ErrorDomain ℓB₁ ℓ≤B₁ ℓ≈B₁}
    {B₂ : ErrorDomain ℓB₂ ℓ≤B₂ ℓ≈B₂}
    {B₃ : ErrorDomain ℓB₃ ℓ≤B₃ ℓ≈B₃}
    (d  : ErrorDomRel B₁ B₂ ℓd)
    (d' : ErrorDomRel B₂ B₃ ℓd') →
    ErrorDomRel B₁ B₃ (HorizontalComp.lvl d d')
  d ⊙ed d' = HorizontalComp.HorizComp d d'

{-
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
-}


  -- Identity and associativity laws for horizontal composition
  --
  -- TODO






  ------------------------  
  -- Error domain squares
  ------------------------

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
         (ϕ .ErrorDomMor.f) (ϕ' .ErrorDomMor.f)


  isPropErrorDomSq :
    {Bᵢ  : ErrorDomain ℓBᵢ  ℓ≤Bᵢ  ℓ≈Bᵢ}
    {Bᵢ' : ErrorDomain ℓBᵢ' ℓ≤Bᵢ' ℓ≈Bᵢ'}
    {Bₒ  : ErrorDomain ℓBₒ  ℓ≤Bₒ  ℓ≈Bₒ} 
    {Bₒ' : ErrorDomain ℓBₒ' ℓ≤Bₒ' ℓ≈Bₒ'} →
    (dᵢ  : ErrorDomRel Bᵢ Bᵢ' ℓdᵢ) →
    (dₒ  : ErrorDomRel Bₒ Bₒ' ℓdₒ) →
    (ϕ   : ErrorDomMor Bᵢ  Bₒ) →
    (ϕ'  : ErrorDomMor Bᵢ' Bₒ') →
    isProp (ErrorDomSq dᵢ dₒ ϕ ϕ')
  isPropErrorDomSq dᵢ dₒ ϕ ϕ' =
    isPropPBSq (dᵢ .ErrorDomRel.UR) (dₒ .ErrorDomRel.UR)
               (ϕ .ErrorDomMor.f) (ϕ' .ErrorDomMor.f)


  module HorizCompUMP
    {Bᵢ₁ : ErrorDomain ℓBᵢ₁ ℓ≤Bᵢ₁ ℓ≈Bᵢ₁}
    {Bᵢ₂ : ErrorDomain ℓBᵢ₂ ℓ≤Bᵢ₂ ℓ≈Bᵢ₂}
    {Bᵢ₃ : ErrorDomain ℓBᵢ₃ ℓ≤Bᵢ₃ ℓ≈Bᵢ₃}
    {Bₒ₁ : ErrorDomain ℓBₒ₁ ℓ≤Bₒ₁ ℓ≈Bₒ₁}
    {Bₒ₂ : ErrorDomain ℓBₒ₂ ℓ≤Bₒ₂ ℓ≈Bₒ₂}
    {Bₒ₃ : ErrorDomain ℓBₒ₃ ℓ≤Bₒ₃ ℓ≈Bₒ₃}
    (d  : ErrorDomRel Bᵢ₁ Bᵢ₂ ℓd)
    (d' : ErrorDomRel Bᵢ₂ Bᵢ₃ ℓd')
    (ϕ₁  : ErrorDomMor Bᵢ₁ Bₒ₁)
    (ϕ₂  : ErrorDomMor Bᵢ₂ Bₒ₂)
    (ϕ₃  : ErrorDomMor Bᵢ₃ Bₒ₃)
    {ℓS : Level} (S : ErrorDomRel Bₒ₁ Bₒ₃ ℓS)
    where

    open ErrorDomRel
    open HorizontalComp d d' -- brings modules d and d' in scope

    module ϕ₁ = ErrorDomMor ϕ₁
    module ϕ₂ = ErrorDomMor ϕ₂
    module ϕ₃ = ErrorDomMor ϕ₃

    module S = ErrorDomRel S

    -- To construct a square whose top edge is (d ⊙ed d') and whose
    -- bottom edge is a relation S between Bₒ₁ and Bₒ₃, it suffices to
    -- construct a square whose top edge is the *normal* composition
    -- of the underlying predomain relations of d and d' and whose
    -- bottom edge is the underlying predomain relation of S.
    --
    -- In other words, the client gets to assume that there exists
    -- (truncated) some intermediate b₂ such that b₁ d b₂ and b₂ d'
    -- b₃.  If under this assumption, the client proves (ϕ₁ b₁) S (ϕ₃
    -- b₃), then we can conclude that b₁ (d ⊙ed d') b₃ implies that
    -- (ϕ₁ b₁) S (ϕ₃ b₃).
    ElimHorizComp :
      (PBSq (d.UR ⊙ d'.UR) S.UR ϕ₁.f ϕ₃.f) →
       ErrorDomSq (d ⊙ed d') S ϕ₁ ϕ₃
      -- (b₁ d.rel b₂ × b₂ d'.rel b₃) → S.EDRel (ϕ₁.fun b₁) (ϕ₃.fun b₃)) →
      -- ∀ b₁ b₃ → HCRel b₁ b₃ → S.EDRel (ϕ₁.fun b₁) (ϕ₃.fun b₃)
    ElimHorizComp α b₁ b₃ (inj .b₁ b₂ .b₃ R₁₂ R₂₃) =
      α b₁ b₃ ∣ b₂ , R₁₂ , R₂₃ ∣₁
    ElimHorizComp α b₁ b₃' (up-closed .b₁ b₃ .b₃' b₁Rb₃ b₃≤b₃') =
      S.is-monotone (ElimHorizComp α b₁ b₃ b₁Rb₃) (ϕ₃.isMon b₃≤b₃')
    ElimHorizComp α b₁' b₃ (dn-closed .b₁' b₁ .b₃ b₁'≤b₁ b₁Rb₃) =
      S.is-antitone (ϕ₁.isMon b₁'≤b₁) (ElimHorizComp α b₁ b₃ b₁Rb₃)
    ElimHorizComp α .(B₁.℧) b₃ (pres℧ .b₃) =
      transport (sym (cong₂ S._rel_ ϕ₁.f℧ refl)) (S.R℧ (ϕ₃.fun b₃))
    ElimHorizComp α .(B₁.θ $ b₁~) .(B₃.θ $ b₃~) (presθ b₁~ b₃~ H~) =
      transport
        (sym (cong₂ S._rel_ (ϕ₁.fθ b₁~) (ϕ₃.fθ b₃~)))
        (S.Rθ
          (λ t → ϕ₁.fun (b₁~ t))
          (λ t → ϕ₃.fun (b₃~ t))
          (λ t → ElimHorizComp α (b₁~ t) (b₃~ t) (H~ t)))
      -- S.Rθ b₁~ b₃~ (λ t → ElimHorizComp H (b₁~ t) (b₃~ t) (H~ t))
    ElimHorizComp H b₁ b₃ (is-prop .b₁ .b₃ p q i) =
      S.is-prop-valued
        (ϕ₁.fun b₁) (ϕ₃.fun b₃)
        (ElimHorizComp H b₁ b₃ p) (ElimHorizComp H b₁ b₃ q) i
     


    

  -- Identity and composition of squares

  -- "Horizontal" identity squares.

  ED-IdSqH :
    {Bᵢ : ErrorDomain ℓBᵢ ℓ≤Bᵢ ℓ≈Bᵢ}
    {Bₒ : ErrorDomain ℓBₒ ℓ≤Bₒ ℓ≈Bₒ} →
    (ϕ : ErrorDomMor Bᵢ Bₒ) →
    ErrorDomSq (idEDRel Bᵢ) (idEDRel Bₒ) ϕ ϕ
  ED-IdSqH ϕ = Predom-IdSqH (ϕ .ErrorDomMor.f)

  -- "Vertical" identity squares.

  ED-IdSqV :
    {B : ErrorDomain ℓB ℓ≤B ℓ≈B}
    {B' : ErrorDomain ℓB' ℓ≤B' ℓ≈B'}
    (d : ErrorDomRel B B' ℓc) →
    ErrorDomSq d d IdE IdE
  ED-IdSqV c x y xRy = xRy


  ED-CompSqV :
    {B₁  : ErrorDomain ℓB₁  ℓ≤B₁  ℓ≈B₁ }
    {B₁' : ErrorDomain ℓB₁' ℓ≤B₁' ℓ≈B₁'}
    {B₂  : ErrorDomain ℓB₂  ℓ≤B₂  ℓ≈B₂ }
    {B₂' : ErrorDomain ℓB₂' ℓ≤B₂' ℓ≈B₂'}
    {B₃  : ErrorDomain ℓB₃  ℓ≤B₃  ℓ≈B₃ }
    {B₃' : ErrorDomain ℓB₃' ℓ≤B₃' ℓ≈B₃'}
    {d₁  : ErrorDomRel B₁ B₁' ℓd₁}
    {d₂  : ErrorDomRel B₂ B₂' ℓd₂}
    {d₃  : ErrorDomRel B₃ B₃' ℓd₃}
    {ϕ₁  : ErrorDomMor B₁  B₂ }
    {ϕ₁' : ErrorDomMor B₁' B₂'}
    {ϕ₂  : ErrorDomMor B₂  B₃ }
    {ϕ₂' : ErrorDomMor B₂' B₃'} →
    ErrorDomSq d₁ d₂ ϕ₁ ϕ₁' →
    ErrorDomSq d₂ d₃ ϕ₂ ϕ₂' →
    ErrorDomSq d₁ d₃ (ϕ₂ ∘ed ϕ₁) (ϕ₂' ∘ed ϕ₁')
  ED-CompSqV {d₁ = d₁} {d₂ = d₂} {d₃ = d₃}
             {ϕ₁ = ϕ₁} {ϕ₁' = ϕ₁'} {ϕ₂ = ϕ₂} {ϕ₂' = ϕ₂'} α₁ α₂ =
    CompSqV {c₁ = d₁ .ErrorDomRel.UR} {c₂ = d₂ .ErrorDomRel.UR}
            {c₃ = d₃ .ErrorDomRel.UR} {f₁ = ϕ₁ .ErrorDomMor.f}
            {g₁ = ϕ₁' .ErrorDomMor.f} {f₂ = ϕ₂ .ErrorDomMor.f}
            {g₂ = ϕ₂' .ErrorDomMor.f} α₁ α₂


  ED-CompSqH :
    {Bᵢ₁ : ErrorDomain ℓBᵢ₁ ℓ≤Bᵢ₁ ℓ≈Bᵢ₁}
    {Bᵢ₂ : ErrorDomain ℓBᵢ₂ ℓ≤Bᵢ₂ ℓ≈Bᵢ₂}
    {Bᵢ₃ : ErrorDomain ℓBᵢ₃ ℓ≤Bᵢ₃ ℓ≈Bᵢ₃}
    {Bₒ₁ : ErrorDomain ℓBₒ₁ ℓ≤Bₒ₁ ℓ≈Bₒ₁}
    {Bₒ₂ : ErrorDomain ℓBₒ₂ ℓ≤Bₒ₂ ℓ≈Bₒ₂}
    {Bₒ₃ : ErrorDomain ℓBₒ₃ ℓ≤Bₒ₃ ℓ≈Bₒ₃}
    {dᵢ₁ : ErrorDomRel Bᵢ₁ Bᵢ₂ ℓdᵢ₁}
    {dᵢ₂ : ErrorDomRel Bᵢ₂ Bᵢ₃ ℓdᵢ₂}
    {dₒ₁ : ErrorDomRel Bₒ₁ Bₒ₂ ℓdₒ₁}
    {dₒ₂ : ErrorDomRel Bₒ₂ Bₒ₃ ℓdₒ₂}
    {ϕ₁  : ErrorDomMor Bᵢ₁ Bₒ₁}
    {ϕ₂  : ErrorDomMor Bᵢ₂ Bₒ₂}
    {ϕ₃  : ErrorDomMor Bᵢ₃ Bₒ₃} →
    ErrorDomSq dᵢ₁ dₒ₁ ϕ₁ ϕ₂ →
    ErrorDomSq dᵢ₂ dₒ₂ ϕ₂ ϕ₃ →
    ErrorDomSq (dᵢ₁ ⊙ed dᵢ₂) (dₒ₁ ⊙ed dₒ₂) ϕ₁ ϕ₃
  ED-CompSqH
    {dᵢ₁ = dᵢ₁} {dᵢ₂ = dᵢ₂} {dₒ₁ = dₒ₁} {dₒ₂ = dₒ₂}
    {ϕ₁ = ϕ₁} {ϕ₂ = ϕ₂} {ϕ₃ = ϕ₃} α β = HorizCompUMP.ElimHorizComp dᵢ₁ dᵢ₂ ϕ₁ ϕ₂ ϕ₃ (dₒ₁ ⊙ed dₒ₂) {!!}
    -- HorizontalComp.ElimHorizComp dᵢ₁ dᵢ₂ {!(dₒ₁ ⊙ed dₒ₂)!} {!!} x z xRz





  -----------------------------
  -----------------------------
  -- Functors F, U, and ⟶
  -----------------------------
  -----------------------------


  -------------------
  -- The F functor.
  -------------------





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

   -- Defining the action of ⟶ on objects
   
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
    
    -- These next three can likely be defined using combinators
    Arr-ob .snd .θ .f g~ = aux
      where
        aux : Arr-ob .fst
        aux .f x = B.θ $ (λ t → g~ t $ x)
        aux .isMon x1≤x2 = B.θ .isMon (λ t → (g~ t) .isMon x1≤x2)
        aux .pres≈ x1≈x2 = B.θ .pres≈ (λ t → (g~ t) .pres≈ x1≈x2)
    Arr-ob .snd .θ .isMon {g1~} {g2~} g1~≤g2~ x =
      B.θ .isMon (λ t → g1~≤g2~ t x)
    Arr-ob .snd .θ .pres≈ {g1~} {g2~} g1~≈g2~ x x' x≈x' =
      B.θ .pres≈ (λ t → g1~≈g2~ t x x' x≈x')
    

  -- The action of ⟶ on objects
  
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
  (f ⟶mor ϕ) .fθ g~ = eqPBMor _ _ (funExt (λ _ → ϕ .fθ _)) 

  -- Functoriality (preservation of identity and composition)
 

  arrowPresIdVert : {A : PosetBisim  ℓA ℓ≤A ℓ≈A}  {B : ErrorDomain ℓB ℓ≤B ℓ≈B} →
    (Id {X = A}) ⟶mor (IdE {B = B}) ≡ IdE
  arrowPresIdVert = eqErrorDomMor _ _ (funExt (λ g → eqPBMor _ _ refl)) -- g is a predomain morphism A → UB


  -- presIdL : {A : PosetBisim ℓA ℓ≤A ℓ≈A} {Bᵢ : ErrorDomain ℓBᵢ ℓ≤Bᵢ ℓ≈Bᵢ} {Bₒ : ErrorDomain ℓBₒ ℓ≤Bₒ ℓ≈Bₒ} →
  --   (ϕ : ErrorDomMor Bᵢ Bₒ) →
  --   (Id {X = A}) ⟶mor ϕ ≡ {!!}

  module PresCompositionVertical
    {A₁ : PosetBisim ℓA₁ ℓ≤A₁ ℓ≈A₁}  {A₂ : PosetBisim ℓA₂ ℓ≤A₂ ℓ≈A₂}  {A₃ : PosetBisim ℓA₃ ℓ≤A₃ ℓ≈A₃}
    {B₁ : ErrorDomain ℓB₁ ℓ≤B₁ ℓ≈B₁} {B₂ : ErrorDomain ℓB₂ ℓ≤B₂ ℓ≈B₂} {B₃ : ErrorDomain ℓB₃ ℓ≤B₃ ℓ≈B₃}
    (f₁ : PBMor A₂ A₁) (f₂ : PBMor A₃ A₂)
    (ϕ₁ : ErrorDomMor B₁ B₂) (ϕ₂ : ErrorDomMor B₂ B₃) where

    arrowPresCompVert : (f₁ ∘p f₂) ⟶mor (ϕ₂ ∘ed ϕ₁) ≡ ((f₂ ⟶mor ϕ₂) ∘ed (f₁ ⟶mor ϕ₁))
    arrowPresCompVert = eqErrorDomMor _ _ (funExt (λ g → eqPBMor _ _ refl)) -- g is a predomain morphism A₁ → UB₁



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


  -- Lax functoriality of ⟶ on relations, i.e., relationship between
  -- (c ⊙ c') ⟶ (d ⊙ d') and (c ⟶ d) ⊙ (c' ⟶ d')
  --
  -- TODO









  -- Action of ⟶ on squares
  module _
    {Aᵢ  : PosetBisim ℓAᵢ  ℓ≤Aᵢ  ℓ≈Aᵢ}
    {Aᵢ' : PosetBisim ℓAᵢ' ℓ≤Aᵢ' ℓ≈Aᵢ'}
    {Aₒ  : PosetBisim ℓAₒ  ℓ≤Aₒ  ℓ≈Aₒ} 
    {Aₒ' : PosetBisim ℓAₒ' ℓ≤Aₒ' ℓ≈Aₒ'}
    {Bᵢ  : ErrorDomain ℓBᵢ  ℓ≤Bᵢ  ℓ≈Bᵢ}
    {Bᵢ' : ErrorDomain ℓBᵢ' ℓ≤Bᵢ' ℓ≈Bᵢ'}
    {Bₒ  : ErrorDomain ℓBₒ  ℓ≤Bₒ  ℓ≈Bₒ} 
    {Bₒ' : ErrorDomain ℓBₒ' ℓ≤Bₒ' ℓ≈Bₒ'}
    {cᵢ  : PBRel Aᵢ Aᵢ' ℓcᵢ}
    {cₒ  : PBRel Aₒ Aₒ' ℓcₒ}
    {f   : PBMor Aₒ  Aᵢ}   -- Notice the flip in direction!
    {g   : PBMor Aₒ' Aᵢ'}  -- Notice the flip in direction!
    {dᵢ  : ErrorDomRel Bᵢ Bᵢ' ℓdᵢ}
    {dₒ  : ErrorDomRel Bₒ Bₒ' ℓdₒ}
    {ϕ   : ErrorDomMor Bᵢ  Bₒ} 
    {ϕ'  : ErrorDomMor Bᵢ' Bₒ'} where

    _⟶sq_ : PBSq cₒ cᵢ f g → ErrorDomSq dᵢ dₒ ϕ ϕ' →
      ErrorDomSq (cᵢ ⟶rel dᵢ) (cₒ ⟶rel dₒ) (f ⟶mor ϕ) (g ⟶mor ϕ')
    α ⟶sq β = {!!}
    --   PBSq (cᵢ₁ ==>pbmonrel cᵢ₂) (cₒ₁ ==>pbmonrel cₒ₂) (f₁ ~-> f₂) (g₁ ~-> g₂)
    -- α ==>psq β = λ q q' γ → λ x y xRy → β _ _ (γ _ _ (α _ _ xRy))

