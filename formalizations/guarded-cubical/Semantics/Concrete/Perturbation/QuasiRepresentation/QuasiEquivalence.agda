{-# OPTIONS --rewriting --guarded #-}
{-# OPTIONS --lossy-unification #-}

open import Common.Later
module Semantics.Concrete.Perturbation.QuasiRepresentation.QuasiEquivalence (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure

open import Cubical.Algebra.Monoid.Base

open import Common.Common

open import Cubical.Data.Sigma

open import Semantics.Concrete.Predomain.Morphism
open import Semantics.Concrete.Predomain.Relation as PRel
open import Semantics.Concrete.Predomain.Square
open import Semantics.Concrete.Predomain.ErrorDomain k

open import Semantics.Concrete.Types k as Types
open import Semantics.Concrete.Perturbation.QuasiRepresentation k

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level
    ℓ≤ ℓ≈ ℓM : Level
    ℓA ℓA' ℓ≤A ℓ≤A' ℓ≈A ℓ≈A' ℓMA ℓMA' : Level
    ℓB ℓB' ℓ≤B ℓ≤B' ℓ≈B ℓ≈B' ℓMB ℓMB' : Level
    ℓc ℓc' ℓc'' ℓd ℓd' ℓd'' : Level
  
    ℓA₁   ℓ≤A₁   ℓ≈A₁   : Level
    ℓA₁'  ℓ≤A₁'  ℓ≈A₁'  : Level
    ℓA₂   ℓ≤A₂   ℓ≈A₂   : Level
    ℓA₂'  ℓ≤A₂'  ℓ≈A₂'  : Level
    ℓA₃   ℓ≤A₃   ℓ≈A₃   : Level
    ℓA₃'  ℓ≤A₃'  ℓ≈A₃'  : Level

    ℓB₁   ℓ≤B₁   ℓ≈B₁   : Level
    ℓB₁'  ℓ≤B₁'  ℓ≈B₁'  : Level
    ℓB₂   ℓ≤B₂   ℓ≈B₂   : Level
    ℓB₂'  ℓ≤B₂'  ℓ≈B₂'  : Level
    ℓB₃   ℓ≤B₃   ℓ≈B₃   : Level
    ℓB₃'  ℓ≤B₃'  ℓ≈B₃'  : Level
   
    ℓc₁ ℓc₂ ℓc₃  : Level    

    ℓMA₁ ℓMA₂ ℓMA₃ : Level
    ℓMB₁ ℓMB₂ ℓMB₃ : Level
    ℓMA₁' ℓMA₂' : Level


-- Quasi-order equivalence of value relations
-----------------------------------------------

module _
  (A : ValType ℓA ℓ≤A ℓ≈A ℓMA) (A' : ValType ℓA' ℓ≤A' ℓ≈A' ℓMA')
  (c  : PRel (ValType→Predomain A) (ValType→Predomain A') ℓc)
  (c' : PRel (ValType→Predomain A) (ValType→Predomain A') ℓc')

  where

  private
    MA  = PtbV A
    MA' = PtbV A'

    iA : _ → _
    iA = fst ∘ interpV A .fst

    iA' : _ → _
    iA' = fst ∘ interpV A' .fst
  

  record QuasiOrderEquivV :
      Type (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓA ℓA') (ℓ-max ℓ≤A ℓ≤A'))
        (ℓ-max (ℓ-max ℓ≈A ℓ≈A') (ℓ-max ℓMA ℓMA'))) (ℓ-max ℓc ℓc')) where
      
    field
      δ₁  : ⟨ MA ⟩
      δ₁' : ⟨ MA' ⟩
      sq-c-c' : PSq c c' (iA δ₁) (iA' δ₁') 

      δ₂  : ⟨ MA ⟩
      δ₂' : ⟨ MA' ⟩
      sq-c'-c : PSq c' c (iA δ₂) (iA' δ₂')


-- Quasi-order equivalence of computation relations
----------------------------------------------------

module _
  (B : CompType ℓB ℓ≤B ℓ≈B ℓMB) (B' : CompType ℓB' ℓ≤B' ℓ≈B' ℓMB')
  (d  : ErrorDomRel (CompType→ErrorDomain B) (CompType→ErrorDomain B') ℓd)
  (d' : ErrorDomRel (CompType→ErrorDomain B) (CompType→ErrorDomain B') ℓd')

  where

  private
    MB  = PtbC B
    MB' = PtbC B'

    iB : _ → _
    iB = fst ∘ interpC B .fst

    iB' : _ → _
    iB' = fst ∘ interpC B' .fst
  

  record QuasiOrderEquivC :
      Type (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓB ℓB') (ℓ-max ℓ≤B ℓ≤B'))
        (ℓ-max (ℓ-max ℓ≈B ℓ≈B') (ℓ-max ℓMB ℓMB'))) (ℓ-max ℓd ℓd')) where
      
    field
      δ₁  : ⟨ MB ⟩
      δ₁' : ⟨ MB' ⟩
      sq-d-d' : ErrorDomSq d d' (iB δ₁) (iB' δ₁') 

      δ₂  : ⟨ MB ⟩
      δ₂' : ⟨ MB' ⟩
      sq-d'-d : ErrorDomSq d' d (iB δ₂) (iB' δ₂')


----------------------------------------------------------------------
----------------------------------------------------------------------


-- Lemma: If two error domain relations d and d' between B and B' are
-- quasi-left-representable by the same embedding morphism e, then d
-- is quasi-order-equivalent to d'.

-- The construction of the two squares is symmetric, so the lemma
-- below constructs a square between d and d' given that they have the
-- same embeddings.  Then we instantiate the lemma to construct the
-- squares in both directions.

module _
  {B : CompType ℓB ℓ≤B ℓ≈B ℓMB} {B' : CompType ℓB' ℓ≤B' ℓ≈B' ℓMB'}
  (d  : ErrorDomRel (CompType→ErrorDomain B) (CompType→ErrorDomain B') ℓd)
  (d' : ErrorDomRel (CompType→ErrorDomain B) (CompType→ErrorDomain B') ℓd')
  (ρd  : LeftRepC B B' d)
  (ρd' : LeftRepC B B' d')
  (eq : embC _ _ _ ρd ≡ embC _ _ _ ρd') where

  open QuasiOrderEquivC

  private
    MB  = PtbC B
    MB' = PtbC B'

    iB : _ → _
    iB = fst ∘ interpC B .fst

    iB' : _ → _
    iB' = fst ∘ interpC B' .fst

    rB = idEDRel (CompType→ErrorDomain B)
    rB' = idEDRel (CompType→ErrorDomain B')

    δld' = δleC _ _ _ ρd'
    δrd  = δreC _ _ _ ρd

    δld  = δleC _ _ _ ρd
    δrd' = δreC _ _ _ ρd'

    ed' = embC _ _ _ ρd'
    ed  = embC _ _ _ ρd


  -- The first square is formed by horizontally composing the
  -- following squares, and using the fact that composing with the
  -- homogeneous relations is the identity.

  --           ⊑B                    d
  --       B o----* B           B o----* B'
  --       |        |           |        |
  -- d'.δl | d'.UpR | e      e  | d.UpL  | d.δr
  --       v        v           v        v
  --       B o----* B'          B' o---* B'
  --           d'                   ⊑B'

  
  quasi-order-rel-C : Σ[ δ-left ∈ ⟨ MB ⟩ ] Σ[ δ-right ∈ ⟨ MB' ⟩ ]
    (ErrorDomSq d d' (iB δ-left) (iB' δ-right))
  quasi-order-rel-C .fst = δld'
  quasi-order-rel-C .snd .fst = δrd
  quasi-order-rel-C .snd .snd  = composed123
  
  -- Agda accepts this without requiring us to transport along the
  -- fact that (IdE ∘ed (iB δld') ∘ed IdE) is equal to (iB δld') and
  -- likewise for the other side.
    where
      α1 : ErrorDomSq d (rB ⊙ed d) IdE IdE
      α1 = sq-d-idB⊙d d

      α2 : ErrorDomSq (rB ⊙ed d) (d' ⊙ed rB') (iB δld') (iB' δrd)
      α2 = _∘esqh_ {ϕ₁ = (iB δld')} {ϕ₂ = ed'} {ϕ₃ = (iB' δrd)}            
             (UpRC _ _ _ ρd')
             (transport
               (λ i → ErrorDomSq d (rB') (eq i) (iB' δrd))
               (UpLC _ _ _ ρd))

      α3 : ErrorDomSq (d' ⊙ed rB') d' IdE IdE
      α3 = sq-d⊙idB'-d d'

      composed12 : ErrorDomSq d (d' ⊙ed rB') ((iB δld') ∘ed IdE) ((iB' δrd) ∘ed IdE)
      composed12 = ED-CompSqV
        {d₁ = d} {d₂ = (rB ⊙ed d)} {d₃ = (d' ⊙ed rB')}
        {ϕ₁ = IdE} {ϕ₁' = IdE} {ϕ₂ = (iB δld')} {ϕ₂' = (iB' δrd)}
        α1 α2

      composed123 : ErrorDomSq d d' (IdE ∘ed (iB δld') ∘ed IdE) (IdE ∘ed (iB' δrd) ∘ed IdE)
      composed123 = ED-CompSqV
        {d₁ = d} {d₂ = (d' ⊙ed rB')} {d₃ = d'}
        {ϕ₁ = (iB δld')} {ϕ₁' = (iB' δrd)} {ϕ₂ = IdE} {ϕ₂' = IdE}
        composed12 α3


  -- The second square is formed symmetrically:

  --          ⊑B                    d'
  --      B o----* B           B o----* B'
  --      |        |           |        |
  -- d.δl | d.UpR  | e      e  | d'.UpL | d'.δr
  --      v        v           v        v
  --      B o----* B'          B' o---* B'
  --          d                    ⊑B'



module _
  {B : CompType ℓB ℓ≤B ℓ≈B ℓMB} {B' : CompType ℓB' ℓ≤B' ℓ≈B' ℓMB'}
  (d  : ErrorDomRel (CompType→ErrorDomain B) (CompType→ErrorDomain B') ℓd)
  (d' : ErrorDomRel (CompType→ErrorDomain B) (CompType→ErrorDomain B') ℓd')
  (ρd  : LeftRepC B B' d)
  (ρd' : LeftRepC B B' d')
  (eq : embC _ _ _ ρd ≡ embC _ _ _ ρd') where

  open QuasiOrderEquivC

  d≈⊑≈d' : _
  d≈⊑≈d' = quasi-order-rel-C _ _ ρd ρd' eq

  d'≈⊑≈d : _
  d'≈⊑≈d = quasi-order-rel-C _ _ ρd' ρd (sym eq)

  eqEmb→quasiEquivC : QuasiOrderEquivC B B' d d'
  eqEmb→quasiEquivC .δ₁      = d≈⊑≈d' .fst
  eqEmb→quasiEquivC .δ₁'     = d≈⊑≈d' .snd .fst
  eqEmb→quasiEquivC .sq-d-d' = d≈⊑≈d' .snd .snd
  
  eqEmb→quasiEquivC .δ₂      = d'≈⊑≈d .fst
  eqEmb→quasiEquivC .δ₂'     = d'≈⊑≈d .snd .fst
  eqEmb→quasiEquivC .sq-d'-d = d'≈⊑≈d .snd .snd


----------------------------------------------------------------------
----------------------------------------------------------------------


-- Lemma: If two predomain relations c and c' between A and A' are
-- quasi-right-representable by the same projection morphism p, then c
-- is quasi-order-equivalent to c'.

-- As above, the construction of the two squares is symmetric.


module _
  {A : ValType ℓA ℓ≤A ℓ≈A ℓMA} {A' : ValType ℓA' ℓ≤A' ℓ≈A' ℓMA'}
  (c  : PRel (ValType→Predomain A) (ValType→Predomain A') ℓc)
  (c' : PRel (ValType→Predomain A) (ValType→Predomain A') ℓc')
  (ρc  : RightRepV A A' c)
  (ρc' : RightRepV A A' c')
  (eq : projV _ _ _ ρc ≡ projV _ _ _ ρc') where

  open QuasiOrderEquivV

  private
    MA  = PtbV A
    MA' = PtbV A'

    iA : _ → _
    iA = fst ∘ interpV A .fst

    iA' : _ → _
    iA' = fst ∘ interpV A' .fst

    rA = idPRel (ValType→Predomain A)
    rA' = idPRel (ValType→Predomain A')

    δlc  = δlpV _ _ _ ρc
    δrc' = δrpV _ _ _ ρc'

    pc' = projV _ _ _ ρc'
    pc  = projV _ _ _ ρc

  -- The square is formed by horizontally composing the
  -- following squares, and using the fact that composing with the
  -- homogeneous relations is the identity.

  --            c                    ⊑A'
  --       A o----* A'          A' o---* A'
  --       |        |           |        |
  --  c.δl | c.DnR  | p      p' | c'.DnL | c'.δr
  --       v        v           v        v
  --       A o----* A           A o----* A'
  --           ⊑A                   c'

  quasi-order-rel-V : Σ[ δ-left ∈ ⟨ MA ⟩ ] Σ[ δ-right ∈ ⟨ MA' ⟩ ]
    (PSq c c' (iA δ-left) (iA' δ-right))
  quasi-order-rel-V .fst = δlc
  quasi-order-rel-V .snd .fst = δrc'
  quasi-order-rel-V .snd .snd  = composed123
    where
      α1 : PSq c (c ⊙ rA') Id Id
      α1 = sq-c-c⊙A' c

      α2 : PSq (c ⊙ rA') (rA ⊙ c') (iA δlc) (iA' δrc')
      α2 = CompSqH {f = iA _} {g = projV _ _ _ _} {h = iA' _}
        (DnRV _ _ _ ρc)
        (subst (λ z → PSq rA' c' z (iA' δrc')) (sym eq) (DnLV _ _ _ ρc'))

      α3 : PSq (rA ⊙ c') c' Id Id
      α3 = sq-idA⊙c-c c'

      composed12 : PSq c (rA ⊙ c') ((iA δlc) ∘p Id) ((iA' δrc') ∘p Id)
      composed12 = CompSqV
        {c₁ = c} {c₂ = (c ⊙ rA')} {c₃ = (rA ⊙ c')}
        {f₁ = Id} {g₁ = Id} {f₂ = (iA δlc)} {g₂ = (iA' δrc')}
        α1 α2

      composed123 : PSq c c' (Id ∘p (iA δlc) ∘p Id) (Id ∘p (iA' δrc') ∘p Id)
      composed123 = CompSqV
        {c₁ = c} {c₂ = (rA ⊙ c')} {c₃ = c'}
        {f₁ = (iA δlc)} {g₁ = (iA' δrc')} {f₂ = Id} {g₂ = Id}
        composed12 α3 



module _
  {A : ValType ℓA ℓ≤A ℓ≈A ℓMA} {A' : ValType ℓA' ℓ≤A' ℓ≈A' ℓMA'}
  (c  : PRel (ValType→Predomain A) (ValType→Predomain A') ℓc)
  (c' : PRel (ValType→Predomain A) (ValType→Predomain A') ℓc')
  (ρc  : RightRepV A A' c)
  (ρc' : RightRepV A A' c')
  (eq : projV _ _ _ ρc ≡ projV _ _ _ ρc') where

  open QuasiOrderEquivV

  c≈⊑≈c' : _
  c≈⊑≈c' = quasi-order-rel-V _ _ ρc ρc' eq

  c'≈⊑≈c : _
  c'≈⊑≈c = quasi-order-rel-V _ _ ρc' ρc (sym eq)

  eqEmb→quasiEquivV : QuasiOrderEquivV A A' c c'
  eqEmb→quasiEquivV .δ₁      = c≈⊑≈c' .fst
  eqEmb→quasiEquivV .δ₁'     = c≈⊑≈c' .snd .fst
  eqEmb→quasiEquivV .sq-c-c' = c≈⊑≈c' .snd .snd
  
  eqEmb→quasiEquivV .δ₂      = c'≈⊑≈c .fst
  eqEmb→quasiEquivV .δ₂'     = c'≈⊑≈c .snd .fst
  eqEmb→quasiEquivV .sq-c'-c = c'≈⊑≈c .snd .snd


----------------------------------------------------------------------
----------------------------------------------------------------------

-- Quasi-order-equivalence is reflexive, symmetric and transitive.
-- Reflexivity uses the identity perturbations, symmetry swaps the two
-- squares, and transitivity multiplies the perturbations and composes
-- the squares vertically.

module _ {A : ValType ℓA ℓ≤A ℓ≈A ℓMA} {A' : ValType ℓA' ℓ≤A' ℓ≈A' ℓMA'} where
  open QuasiOrderEquivV
  open IsMonoidHom
  private
    module MA  = MonoidStr (PtbV A .snd)
    module MA' = MonoidStr (PtbV A' .snd)
    iA : _ → _
    iA = fst ∘ interpV A .fst
    iA' : _ → _
    iA' = fst ∘ interpV A' .fst
    module iA  = IsMonoidHom (interpV A .snd)
    module iA' = IsMonoidHom (interpV A' .snd)

    𝔸  = ValType→Predomain A
    𝔸' = ValType→Predomain A'

  quasiEquivV-refl : (c : PRel 𝔸 𝔸' ℓc) → QuasiOrderEquivV A A' c c
  quasiEquivV-refl c .δ₁  = MA.ε
  quasiEquivV-refl c .δ₁' = MA'.ε
  quasiEquivV-refl c .sq-c-c' =
    subst2 (λ f g → PSq c c f g)
      (sym (cong fst iA.presε)) (sym (cong fst iA'.presε)) (Predom-IdSqV c)
  quasiEquivV-refl c .δ₂  = MA.ε
  quasiEquivV-refl c .δ₂' = MA'.ε
  quasiEquivV-refl c .sq-c'-c =
    subst2 (λ f g → PSq c c f g)
      (sym (cong fst iA.presε)) (sym (cong fst iA'.presε)) (Predom-IdSqV c)

  quasiEquivV-sym : {c : PRel 𝔸 𝔸' ℓc} {c' : PRel 𝔸 𝔸' ℓc'} →
    QuasiOrderEquivV A A' c c' → QuasiOrderEquivV A A' c' c
  quasiEquivV-sym e .δ₁  = e .δ₂
  quasiEquivV-sym e .δ₁' = e .δ₂'
  quasiEquivV-sym e .sq-c-c' = e .sq-c'-c
  quasiEquivV-sym e .δ₂  = e .δ₁
  quasiEquivV-sym e .δ₂' = e .δ₁'
  quasiEquivV-sym e .sq-c'-c = e .sq-c-c'

  quasiEquivV-trans : {c : PRel 𝔸 𝔸' ℓc} {c' : PRel 𝔸 𝔸' ℓc'} {c'' : PRel 𝔸 𝔸' ℓc''} →
    QuasiOrderEquivV A A' c c' → QuasiOrderEquivV A A' c' c'' → QuasiOrderEquivV A A' c c''
  quasiEquivV-trans {c = c} {c' = c'} {c'' = c''} e₁ e₂ .δ₁  = e₂ .δ₁ MA.· e₁ .δ₁
  quasiEquivV-trans {c = c} {c' = c'} {c'' = c''} e₁ e₂ .δ₁' = e₂ .δ₁' MA'.· e₁ .δ₁'
  quasiEquivV-trans {c = c} {c' = c'} {c'' = c''} e₁ e₂ .sq-c-c' =
    subst2 (λ f g → PSq c c'' f g)
      (sym (cong fst (iA.pres· (e₂ .δ₁) (e₁ .δ₁))))
      (sym (cong fst (iA'.pres· (e₂ .δ₁') (e₁ .δ₁'))))
      (CompSqV {c₁ = c} {c₂ = c'} {c₃ = c''}
        {f₁ = iA (e₁ .δ₁)} {g₁ = iA' (e₁ .δ₁')} {f₂ = iA (e₂ .δ₁)} {g₂ = iA' (e₂ .δ₁')}
        (e₁ .sq-c-c') (e₂ .sq-c-c'))
  quasiEquivV-trans {c = c} {c' = c'} {c'' = c''} e₁ e₂ .δ₂  = e₁ .δ₂ MA.· e₂ .δ₂
  quasiEquivV-trans {c = c} {c' = c'} {c'' = c''} e₁ e₂ .δ₂' = e₁ .δ₂' MA'.· e₂ .δ₂'
  quasiEquivV-trans {c = c} {c' = c'} {c'' = c''} e₁ e₂ .sq-c'-c =
    subst2 (λ f g → PSq c'' c f g)
      (sym (cong fst (iA.pres· (e₁ .δ₂) (e₂ .δ₂))))
      (sym (cong fst (iA'.pres· (e₁ .δ₂') (e₂ .δ₂'))))
      (CompSqV {c₁ = c''} {c₂ = c'} {c₃ = c}
        {f₁ = iA (e₂ .δ₂)} {g₁ = iA' (e₂ .δ₂')} {f₂ = iA (e₁ .δ₂)} {g₂ = iA' (e₁ .δ₂')}
        (e₂ .sq-c'-c) (e₁ .sq-c'-c))


module _ {B : CompType ℓB ℓ≤B ℓ≈B ℓMB} {B' : CompType ℓB' ℓ≤B' ℓ≈B' ℓMB'} where
  open QuasiOrderEquivC
  open IsMonoidHom
  private
    module MB  = MonoidStr (PtbC B .snd)
    module MB' = MonoidStr (PtbC B' .snd)
    iB : _ → _
    iB = fst ∘ interpC B .fst
    iB' : _ → _
    iB' = fst ∘ interpC B' .fst
    module iB  = IsMonoidHom (interpC B .snd)
    module iB' = IsMonoidHom (interpC B' .snd)

    𝔹  = CompType→ErrorDomain B
    𝔹' = CompType→ErrorDomain B'

  quasiEquivC-refl : (d : ErrorDomRel 𝔹 𝔹' ℓd) → QuasiOrderEquivC B B' d d
  quasiEquivC-refl d .δ₁  = MB.ε
  quasiEquivC-refl d .δ₁' = MB'.ε
  quasiEquivC-refl d .sq-d-d' =
    subst2 (λ ϕ ϕ' → ErrorDomSq d d ϕ ϕ')
      (sym (cong fst iB.presε)) (sym (cong fst iB'.presε)) (ED-IdSqV d)
  quasiEquivC-refl d .δ₂  = MB.ε
  quasiEquivC-refl d .δ₂' = MB'.ε
  quasiEquivC-refl d .sq-d'-d =
    subst2 (λ ϕ ϕ' → ErrorDomSq d d ϕ ϕ')
      (sym (cong fst iB.presε)) (sym (cong fst iB'.presε)) (ED-IdSqV d)

  quasiEquivC-sym : {d : ErrorDomRel 𝔹 𝔹' ℓd} {d' : ErrorDomRel 𝔹 𝔹' ℓd'} →
    QuasiOrderEquivC B B' d d' → QuasiOrderEquivC B B' d' d
  quasiEquivC-sym e .δ₁  = e .δ₂
  quasiEquivC-sym e .δ₁' = e .δ₂'
  quasiEquivC-sym e .sq-d-d' = e .sq-d'-d
  quasiEquivC-sym e .δ₂  = e .δ₁
  quasiEquivC-sym e .δ₂' = e .δ₁'
  quasiEquivC-sym e .sq-d'-d = e .sq-d-d'

  quasiEquivC-trans : {d : ErrorDomRel 𝔹 𝔹' ℓd} {d' : ErrorDomRel 𝔹 𝔹' ℓd'} {d'' : ErrorDomRel 𝔹 𝔹' ℓd''} →
    QuasiOrderEquivC B B' d d' → QuasiOrderEquivC B B' d' d'' → QuasiOrderEquivC B B' d d''
  quasiEquivC-trans {d = d} {d' = d'} {d'' = d''} e₁ e₂ .δ₁  = e₂ .δ₁ MB.· e₁ .δ₁
  quasiEquivC-trans {d = d} {d' = d'} {d'' = d''} e₁ e₂ .δ₁' = e₂ .δ₁' MB'.· e₁ .δ₁'
  quasiEquivC-trans {d = d} {d' = d'} {d'' = d''} e₁ e₂ .sq-d-d' =
    subst2 (λ ϕ ϕ' → ErrorDomSq d d'' ϕ ϕ')
      (sym (cong fst (iB.pres· (e₂ .δ₁) (e₁ .δ₁))))
      (sym (cong fst (iB'.pres· (e₂ .δ₁') (e₁ .δ₁'))))
      (ED-CompSqV {d₁ = d} {d₂ = d'} {d₃ = d''}
        {ϕ₁ = iB (e₁ .δ₁)} {ϕ₁' = iB' (e₁ .δ₁')} {ϕ₂ = iB (e₂ .δ₁)} {ϕ₂' = iB' (e₂ .δ₁')}
        (e₁ .sq-d-d') (e₂ .sq-d-d'))
  quasiEquivC-trans {d = d} {d' = d'} {d'' = d''} e₁ e₂ .δ₂  = e₁ .δ₂ MB.· e₂ .δ₂
  quasiEquivC-trans {d = d} {d' = d'} {d'' = d''} e₁ e₂ .δ₂' = e₁ .δ₂' MB'.· e₂ .δ₂'
  quasiEquivC-trans {d = d} {d' = d'} {d'' = d''} e₁ e₂ .sq-d'-d =
    subst2 (λ ϕ ϕ' → ErrorDomSq d'' d ϕ ϕ')
      (sym (cong fst (iB.pres· (e₁ .δ₂) (e₂ .δ₂))))
      (sym (cong fst (iB'.pres· (e₁ .δ₂') (e₂ .δ₂'))))
      (ED-CompSqV {d₁ = d''} {d₂ = d'} {d₃ = d}
        {ϕ₁ = iB (e₂ .δ₂)} {ϕ₁' = iB' (e₂ .δ₂')} {ϕ₂ = iB (e₁ .δ₂)} {ϕ₂' = iB' (e₁ .δ₂')}
        (e₂ .sq-d'-d) (e₁ .sq-d'-d))


----------------------------------------------------------------------
----------------------------------------------------------------------

-- Lemma: If two error domain relations d and d' between B and B' are
-- quasi-right-representable by the same projection morphism p, then d
-- is quasi-order-equivalent to d'. (Dual to the lemma above about
-- predomain relations with the same projection.)

module _
  {B : CompType ℓB ℓ≤B ℓ≈B ℓMB} {B' : CompType ℓB' ℓ≤B' ℓ≈B' ℓMB'}
  (d  : ErrorDomRel (CompType→ErrorDomain B) (CompType→ErrorDomain B') ℓd)
  (d' : ErrorDomRel (CompType→ErrorDomain B) (CompType→ErrorDomain B') ℓd')
  (ρd  : RightRepC B B' d)
  (ρd' : RightRepC B B' d')
  (eq : projC _ _ _ ρd ≡ projC _ _ _ ρd') where

  private
    MB  = PtbC B
    MB' = PtbC B'
    iB : _ → _
    iB = fst ∘ interpC B .fst
    iB' : _ → _
    iB' = fst ∘ interpC B' .fst
    rB = idEDRel (CompType→ErrorDomain B)
    rB' = idEDRel (CompType→ErrorDomain B')

    δld  = δlpC _ _ _ ρd
    δrd' = δrpC _ _ _ ρd'

  -- The square is formed by horizontally composing the following
  -- squares, and using the fact that composing with the homogeneous
  -- relations is the identity.
  --
  --            d                    ⊑B'
  --       B o----* B'          B' o---* B'
  --       |        |           |        |
  --  d.δl | d.DnR  | p      p' | d'.DnL | d'.δr
  --       v        v           v        v
  --       B o----* B           B o----* B'
  --           ⊑B                   d'
  quasi-order-rel-C-proj : Σ[ δ-left ∈ ⟨ MB ⟩ ] Σ[ δ-right ∈ ⟨ MB' ⟩ ]
    (ErrorDomSq d d' (iB δ-left) (iB' δ-right))
  quasi-order-rel-C-proj .fst = δld
  quasi-order-rel-C-proj .snd .fst = δrd'
  quasi-order-rel-C-proj .snd .snd = composed123
    where
      α1 : ErrorDomSq d (d ⊙ed rB') IdE IdE
      α1 = sq-d-d⊙idB' d

      α2 : ErrorDomSq (d ⊙ed rB') (rB ⊙ed d') (iB δld) (iB' δrd')
      α2 = _∘esqh_ {ϕ₁ = iB δld} {ϕ₂ = projC _ _ _ ρd} {ϕ₃ = iB' δrd'}
        (DnRC _ _ _ ρd)
        (transport (λ i → ErrorDomSq rB' d' (eq (~ i)) (iB' δrd')) (DnLC _ _ _ ρd'))

      α3 : ErrorDomSq (rB ⊙ed d') d' IdE IdE
      α3 = sq-idB⊙d-d d'

      composed12 : ErrorDomSq d (rB ⊙ed d') ((iB δld) ∘ed IdE) ((iB' δrd') ∘ed IdE)
      composed12 = ED-CompSqV
        {d₁ = d} {d₂ = d ⊙ed rB'} {d₃ = rB ⊙ed d'}
        {ϕ₁ = IdE} {ϕ₁' = IdE} {ϕ₂ = iB δld} {ϕ₂' = iB' δrd'}
        α1 α2

      composed123 : ErrorDomSq d d' (IdE ∘ed (iB δld) ∘ed IdE) (IdE ∘ed (iB' δrd') ∘ed IdE)
      composed123 = ED-CompSqV
        {d₁ = d} {d₂ = rB ⊙ed d'} {d₃ = d'}
        {ϕ₁ = iB δld} {ϕ₁' = iB' δrd'} {ϕ₂ = IdE} {ϕ₂' = IdE}
        composed12 α3

module _
  {B : CompType ℓB ℓ≤B ℓ≈B ℓMB} {B' : CompType ℓB' ℓ≤B' ℓ≈B' ℓMB'}
  (d  : ErrorDomRel (CompType→ErrorDomain B) (CompType→ErrorDomain B') ℓd)
  (d' : ErrorDomRel (CompType→ErrorDomain B) (CompType→ErrorDomain B') ℓd')
  (ρd  : RightRepC B B' d)
  (ρd' : RightRepC B B' d')
  (eq : projC _ _ _ ρd ≡ projC _ _ _ ρd') where

  open QuasiOrderEquivC

  eqProj→quasiEquivC : QuasiOrderEquivC B B' d d'
  eqProj→quasiEquivC .δ₁      = quasi-order-rel-C-proj _ _ ρd ρd' eq .fst
  eqProj→quasiEquivC .δ₁'     = quasi-order-rel-C-proj _ _ ρd ρd' eq .snd .fst
  eqProj→quasiEquivC .sq-d-d' = quasi-order-rel-C-proj _ _ ρd ρd' eq .snd .snd
  eqProj→quasiEquivC .δ₂      = quasi-order-rel-C-proj _ _ ρd' ρd (sym eq) .fst
  eqProj→quasiEquivC .δ₂'     = quasi-order-rel-C-proj _ _ ρd' ρd (sym eq) .snd .fst
  eqProj→quasiEquivC .sq-d'-d = quasi-order-rel-C-proj _ _ ρd' ρd (sym eq) .snd .snd


----------------------------------------------------------------------
----------------------------------------------------------------------

-- Lemma: If two predomain relations c and c' between A and A' are
-- quasi-left-representable by the same embedding morphism e, then c
-- is quasi-order-equivalent to c'. (The remaining case of the lemma;
-- dual to the lemma about error domain relations with the same
-- embedding.)

module _
  {A : ValType ℓA ℓ≤A ℓ≈A ℓMA} {A' : ValType ℓA' ℓ≤A' ℓ≈A' ℓMA'}
  (c  : PRel (ValType→Predomain A) (ValType→Predomain A') ℓc)
  (c' : PRel (ValType→Predomain A) (ValType→Predomain A') ℓc')
  (ρc  : LeftRepV A A' c)
  (ρc' : LeftRepV A A' c')
  (eq : embV _ _ _ ρc ≡ embV _ _ _ ρc') where

  private
    MA  = PtbV A
    MA' = PtbV A'
    iA : _ → _
    iA = fst ∘ interpV A .fst
    iA' : _ → _
    iA' = fst ∘ interpV A' .fst
    rA  = idPRel (ValType→Predomain A)
    rA' = idPRel (ValType→Predomain A')

    δlc' = δleV _ _ _ ρc'
    δrc  = δreV _ _ _ ρc

  --           ⊑A                    c
  --       A o----* A           A o----* A'
  --       |        |           |        |
  -- c'.δl | c'.UpR | e      e  | c.UpL  | c.δr
  --       v        v           v        v
  --       A o----* A'          A' o---* A'
  --           c'                   ⊑A'
  quasi-order-rel-V-emb : Σ[ δ-left ∈ ⟨ MA ⟩ ] Σ[ δ-right ∈ ⟨ MA' ⟩ ]
    (PSq c c' (iA δ-left) (iA' δ-right))
  quasi-order-rel-V-emb .fst = δlc'
  quasi-order-rel-V-emb .snd .fst = δrc
  quasi-order-rel-V-emb .snd .snd = composed123
    where
      α1 : PSq c (rA ⊙ c) Id Id
      α1 = sq-c-idA⊙c c

      α2 : PSq (rA ⊙ c) (c' ⊙ rA') (iA δlc') (iA' δrc)
      α2 = CompSqH {f = iA δlc'} {g = embV _ _ _ ρc'} {h = iA' δrc}
        (UpRV _ _ _ ρc')
        (transport (λ i → PSq c rA' (eq i) (iA' δrc)) (UpLV _ _ _ ρc))

      α3 : PSq (c' ⊙ rA') c' Id Id
      α3 = sq-c⊙A'-c c'

      composed12 : PSq c (c' ⊙ rA') ((iA δlc') ∘p Id) ((iA' δrc) ∘p Id)
      composed12 = CompSqV
        {c₁ = c} {c₂ = rA ⊙ c} {c₃ = c' ⊙ rA'}
        {f₁ = Id} {g₁ = Id} {f₂ = iA δlc'} {g₂ = iA' δrc}
        α1 α2

      composed123 : PSq c c' (Id ∘p (iA δlc') ∘p Id) (Id ∘p (iA' δrc) ∘p Id)
      composed123 = CompSqV
        {c₁ = c} {c₂ = c' ⊙ rA'} {c₃ = c'}
        {f₁ = iA δlc'} {g₁ = iA' δrc} {f₂ = Id} {g₂ = Id}
        composed12 α3

module _
  {A : ValType ℓA ℓ≤A ℓ≈A ℓMA} {A' : ValType ℓA' ℓ≤A' ℓ≈A' ℓMA'}
  (c  : PRel (ValType→Predomain A) (ValType→Predomain A') ℓc)
  (c' : PRel (ValType→Predomain A) (ValType→Predomain A') ℓc')
  (ρc  : LeftRepV A A' c)
  (ρc' : LeftRepV A A' c')
  (eq : embV _ _ _ ρc ≡ embV _ _ _ ρc') where

  open QuasiOrderEquivV

  eqEmbV→quasiEquivV : QuasiOrderEquivV A A' c c'
  eqEmbV→quasiEquivV .δ₁      = quasi-order-rel-V-emb _ _ ρc ρc' eq .fst
  eqEmbV→quasiEquivV .δ₁'     = quasi-order-rel-V-emb _ _ ρc ρc' eq .snd .fst
  eqEmbV→quasiEquivV .sq-c-c' = quasi-order-rel-V-emb _ _ ρc ρc' eq .snd .snd
  eqEmbV→quasiEquivV .δ₂      = quasi-order-rel-V-emb _ _ ρc' ρc (sym eq) .fst
  eqEmbV→quasiEquivV .δ₂'     = quasi-order-rel-V-emb _ _ ρc' ρc (sym eq) .snd .fst
  eqEmbV→quasiEquivV .sq-c'-c = quasi-order-rel-V-emb _ _ ρc' ρc (sym eq) .snd .snd
