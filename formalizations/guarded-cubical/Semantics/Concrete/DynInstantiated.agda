{-# OPTIONS --rewriting --guarded #-}
{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --lossy-unification #-}

open import Common.Later

module Semantics.Concrete.DynInstantiated (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels

open import Cubical.Functions.Embedding
open import Cubical.Relation.Nullary
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Monoid.More
open import Cubical.Algebra.Monoid.FreeMonoid as Free
open import Cubical.Algebra.Monoid.FreeProduct as FP
open import Cubical.Algebra.Monoid.FreeProduct.Indexed as Indexed
open import Cubical.Algebra.Monoid.Instances.Trivial as Trivial


open import Cubical.Data.Nat hiding (_·_)
open import Cubical.Data.Bool as Bool
open import Cubical.Data.Sum as Sum
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Unit renaming (Unit to ⊤ ; Unit* to ⊤*)
open import Cubical.Data.Sigma as Prod


open import Common.Common
open import Semantics.Concrete.DoublePoset.Base
open import Semantics.Concrete.DoublePoset.Morphism hiding (_$_)
open import Semantics.Concrete.DoublePoset.Constructions renaming (ℕ to NatP)
open import Semantics.Concrete.DoublePoset.ErrorDomain k
open import Semantics.Concrete.DoublePoset.FreeErrorDomain k
open import Semantics.Concrete.DoublePoset.DblPosetCombinators hiding (S)
open import Semantics.Concrete.Perturbation.Semantic k

open import Semantics.Concrete.ParameterizedDyn k as ParamDyn

open import Semantics.Concrete.Types k as Types hiding (Unit ; _×_ ; ℕ)
open import Semantics.Concrete.Perturbation.Relation.Constructions k
open import Semantics.Concrete.Relations k as Rel

private
  variable
    ℓ ℓ' : Level
    ℓA ℓ≤A ℓ≈A : Level
    ℓ≤ ℓ≈ : Level

  ▹_ : {ℓ : Level} → Type ℓ → Type ℓ
  ▹_ A = ▹_,_ k A


open LiftPredomain
open Clocked k

module _
  {M : Monoid ℓ} {N : Monoid ℓ'}
  (ϕ ψ : MonoidHom (M ^op) N)
  where

  op-ind : ϕ ^opHom ≡ ψ ^opHom → ϕ ≡ ψ
  op-ind H = eqMonoidHom ϕ ψ (cong fst H)


-- inl-lemma-neq : ∀ {X : Type ℓ} {Y : Type ℓ'} (x x' : X) →
--   ¬ (x ≡ x') → ¬ (inl {B = Y} x ≡ inl x')
-- inl-lemma-neq x x' x≢x' H-eq = x≢x' (isEmbedding→Inj isEmbedding-inl x x' H-eq)

-- inr-lemma-neq : ∀ {X : Type ℓ} {Y : Type ℓ'} (y y' : Y) →
--   ¬ (y ≡ y') → ¬ (inr {A = X} y ≡ inr y')
-- inr-lemma-neq y y' y≢y' H-eq = y≢y' (isEmbedding→Inj isEmbedding-inr y y' H-eq)


-- ⊎disc : DiscreteTy ℓ → DiscreteTy ℓ' → DiscreteTy (ℓ-max ℓ ℓ')
-- ⊎disc X Y .fst = ⟨ X ⟩ Sum.⊎ ⟨ Y ⟩
-- ⊎disc X Y .snd (inl x) (inl x') =
--   decRec
--     (λ eq → yes (cong inl eq))
--     (λ neq → no (inl-lemma-neq x x' neq))
--     (X .snd x x')
-- ⊎disc X Y .snd (inl x) (inr y) = no (inl≠inr x y)
-- ⊎disc X Y .snd (inr x) (inl y) = no (λ H → inl≠inr y x (sym H))
-- ⊎disc X Y .snd (inr y) (inr y') =
--   decRec
--     (λ eq → yes (cong inr eq))
--     (λ neq → no (inr-lemma-neq y y' neq))
--     (Y .snd y y')


UnitDisc : DiscreteTy ℓ-zero
UnitDisc .fst = Unit
UnitDisc .snd x y = yes refl

BotDisc : DiscreteTy ℓ-zero
BotDisc .fst = ⊥
BotDisc .snd = {!!}

BoolDisc : DiscreteTy ℓ-zero
BoolDisc .fst = Bool
BoolDisc .snd false false = yes refl
BoolDisc .snd false true = no false≢true
BoolDisc .snd true false = no true≢false
BoolDisc .snd true true = yes refl

NatDisc : DiscreteTy ℓ-zero
NatDisc .fst = ℕ
NatDisc .snd = discreteℕ
{-
NatDisc .snd = lem
  where
    lem : ∀ n m → Dec (n ≡ m)
    lem zero zero = yes refl
    lem zero (suc m) = no znots
    lem (suc n) zero = no snotz
    lem (suc n) (suc m) = decRec
      (λ n≡m → yes (cong suc n≡m))
      (λ neq → {!!})
      (lem n m)
-}

open F-ob

module _ {ℓ : Level} where

  -- Shapes and positions for the *unguarded* cases of Dyn:
  S : DiscreteTy ℓ-zero
  S = (ℕ Sum.⊎ Unit , discrete⊎ (NatDisc .snd) (UnitDisc .snd))

  P : ⟨ S ⟩ → DiscreteTy ℓ-zero
  P = Sum.rec (λ _ → BotDisc) (λ _ → BoolDisc)


  -- The functor corresponding to the *guarded* case:
  C : ▹ PosetBisim ℓ ℓ ℓ → PosetBisim ℓ ℓ ℓ
  -- C D~ = PB▸ (λ t → (D~ t) ==> 𝕃 (D~ t))
  C D~ = PB▸ (λ t → U-ob ((D~ t) ⟶ob (F-ob (D~ t))))

  -- open DynStep1 S P C
  
  -- Dyn as a predomain
  Dyn-Pre : PosetBisim ℓ ℓ ℓ
  Dyn-Pre = DP S P C

  -- C (next Dyn) as a predomain
  C-nextD : PosetBisim ℓ ℓ ℓ
  C-nextD = C (next Dyn-Pre)
  
  _ : C-nextD ≡ (PB▹ (U-ob (Dyn-Pre ⟶ob (F-ob Dyn-Pre))))
  _ = refl

  -- Presentation of the monoid of perturbations for C (next D):
  S'gen : Type ℓ-zero
  S'gen = Bool

  S'co : Type ℓ-zero
  S'co = Unit

  S'op : Type ℓ-zero
  S'op = Unit

  U-D→FD : PosetBisim ℓ ℓ ℓ
  U-D→FD = (U-ob (Dyn-Pre ⟶ob (F-ob Dyn-Pre)))

  -- Defining the semantic perturbations for C (next D):
  i-gen : S'gen → ⟨ Endo C-nextD ⟩
  -- U case
  i-gen false = Endo▹ {A = U-D→FD}
    (δB-as-PrePtb (Dyn-Pre ⟶ob F-ob Dyn-Pre))

  -- F case
  i-gen true = Endo▹ {A = U-D→FD}
    (U-PrePtb (PrePtbId ⟶PrePtb (δ*FA-as-PrePtb Dyn-Pre)))

  i-co : S'co → MonoidHom (Endo Dyn-Pre) (Endo C-nextD)
  i-co tt =
    (PrePtb▹ {A = U-D→FD})
      ∘hom (CEndo-B→Endo-UB {B = Dyn-Pre ⟶ob F-ob Dyn-Pre})
      ∘hom (⟶B-PrePtb {A = Dyn-Pre} {B = F-ob Dyn-Pre})
      ∘hom Endo-A→CEndo-FA

  i-op : S'op → MonoidHom (Endo Dyn-Pre ^op) (Endo C-nextD)
  i-op tt =
    (PrePtb▹ {A = U-D→FD})
      ∘hom (CEndo-B→Endo-UB {B = Dyn-Pre ⟶ob F-ob Dyn-Pre})
      ∘hom (A⟶-PrePtb {A = Dyn-Pre} {B = F-ob Dyn-Pre})

  -- Note: If we define DynV mutually with C-nextD-V, then we
  -- may be able to leverage that to make defining i-gen, i-co,
  -- and i-op more "compositional".
  -- This will make the termination checker complain.
  
 
  -- Defining Dyn as a ValType
  -- module Defs = DynStep2 S'gen S'co S'op i-gen i-co i-op
  module Defs = Definitions S P C S'gen S'co S'op i-gen i-co i-op

  DynV : ValType ℓ ℓ ℓ ℓ-zero
  DynV = Defs.DynV

  DynV' : ValType ℓ ℓ ℓ ℓ-zero
  DynV' = Defs.DynV'

  -- There are two a priori different definitions of Sigma and two definitions of C(next D):
  --
  -- 1. The "internal" definitions that are defined as part of the
  --    parameterized Dyn module.
  --
  -- 2. The "external" versions that we define in this module using combinators
  --    on value types, e.g.
  
  --     SigmaV : ValType ℓ ℓ ℓ ℓ-zero
  --     SigmaV = ΣV S (λ s → ΠV (P s) λ _ → DynV)

  -- In the case of Sigma, these two definitions are exactly the same, but
  -- it takes Agda some time to verify this.

  -- In the case of C (next D), these are not definitionally the same,
  -- but we can show that they are isomorphic as value types.

  SigmaV-internal : ValType ℓ ℓ ℓ ℓ-zero
  SigmaV-internal = Defs.SigmaV

  SigmaV : ValType ℓ ℓ ℓ ℓ-zero
  SigmaV = ΣV S (λ s → ΠV (P s) λ _ → DynV')

  -- The "internal" definition of C (next D)
  C-nextD-internal : ValType ℓ ℓ ℓ ℓ-zero
  C-nextD-internal = Defs.XV

  -- Defining ▹ (U (Dyn ⟶ F Dyn)) as a ValType
  C-nextD-V : ValType ℓ ℓ ℓ ℓ-zero
  C-nextD-V = V▹ (Types.U (DynV Types.⟶ (Types.F DynV)))

  _ : ValType→Predomain C-nextD-V ≡ (PB▹ (U-ob (Dyn-Pre ⟶ob (F-ob Dyn-Pre))))
  _ = refl

  -- _ : ValType→Predomain C-nextD-internal ≡ C (next Dyn-Pre)
  -- _ = refl

  isoArr : StrongIsoV C-nextD-internal C-nextD-V
  isoArr = mkStrongIsoV isoP isoM eq
    where
      -- This causes a slowdown...
      isoP : PredomIso (ValType→Predomain C-nextD-internal) (ValType→Predomain C-nextD-V)
      -- isoP = {!!}
      
      isoP .PredomIso.fun = Id
      isoP .PredomIso.inv = Id
      isoP .PredomIso.invRight x = refl
      isoP .PredomIso.invLeft x = refl

      to : MonoidHom (PtbV C-nextD-internal) (PtbV C-nextD-V)
      to =
        -- From internal monoid to external monoid
          (FP.rec
            (Indexed.rec S'gen _ (PtbV C-nextD-V)
              -- Cases for U and F:
              λ { false → Free.rec ⊤ ⊥ ⊥ (PtbV C-nextD-V) (λ _ → FP.⟦ Free.FM-1-gen ⟧₁) ⊥.rec ⊥.rec
                ; true  → Free.rec ⊤ ⊥ ⊥ (PtbV C-nextD-V) (λ _ → FP.⟦ FP.⟦ FP.⟦ Free.FM-1-gen ⟧₁ ⟧₂ ⟧₂) ⊥.rec ⊥.rec})
            (FP.rec
               -- Covariant case
               (Indexed.rec S'co _ (PtbV C-nextD-V) (λ sco → (FP.i₂ ∘hom FP.i₂ ∘hom FP.i₂)))

               -- Contravariant case
               (Indexed.rec S'op _ (PtbV C-nextD-V) (λ sop → (FP.i₂ ∘hom FP.i₁)))))

      from : MonoidHom (PtbV C-nextD-V) (PtbV C-nextD-internal)
      from =
        -- From external monoid to internal monoid
          (FP.rec
            -- U case
            (Free.FM-1-rec (PtbV C-nextD-internal) FP.⟦ Indexed.σ S'gen _ false .fst (Free.gen ⊤ ⊥ ⊥ tt) ⟧₁) 
            (FP.rec
              -- Contravariant case
              (inj-op _ _ C S'gen S'co S'op ∘hom Indexed.σ S'op _ tt)
              (FP.rec
                -- F case
                (Free.FM-1-rec (PtbV C-nextD-internal) FP.⟦ Indexed.σ S'gen _ true .fst (Free.gen ⊤ ⊥ ⊥ tt) ⟧₁)

                -- Covariant case
                (inj-co _ _ C S'gen S'co S'op ∘hom Indexed.σ S'co _ tt))))
      

      opaque
        unfolding ⊕ᵢ Indexed.rec Indexed.elim Indexed.σ
        isoM : MonoidIso (PtbV C-nextD-internal) (PtbV C-nextD-V)
        isoM = mkMonoidIso to from
         
          (FP.ind (FM-1-ind _ _ refl) (FP.ind (eqMonoidHom _ _ refl)
              (FP.ind (FM-1-ind _ _ refl) (eqMonoidHom _ _ refl))))

          (FP.ind (Indexed.ind S'gen _ (λ {false → Free.cases-ind ⊤ ⊥ ⊥ (λ _ → refl) ⊥.elim ⊥.elim
                                         ; true  → Free.cases-ind ⊤ ⊥ ⊥ (λ _ → refl) ⊥.elim ⊥.elim}))
            (FP.ind (Indexed.ind S'co _ (λ s-co → eqMonoidHom _ _ refl))
            (Indexed.ind S'op _ (λ s-op → eqMonoidHom _ _ refl))))

        eq : interpV C-nextD-V ∘hom (isoM .MonoidIso.fun)
           ≡ (PredomIso→EndoHom isoP) ∘hom interpV C-nextD-internal
        eq = FP.ind (Indexed.ind S'gen _
          λ {false → Free.cases-ind ⊤ ⊥ ⊥ (λ _ → PrePtb≡ _ _ (funExt (λ x → refl))) ⊥.elim ⊥.elim
           ; true  → Free.cases-ind ⊤ ⊥ ⊥ (λ _ → PrePtb≡ _ _ (funExt (λ x → refl))) ⊥.elim ⊥.elim})

            (FP.ind
              (Indexed.ind S'co _ (λ s-co → eqMonoidHom _ _ (funExt (λ p → PrePtb≡ _ _ refl))))
                 
              (Indexed.ind S'op _ (λ s-op → eqMonoidHom _ _ (funExt (λ p → PrePtb≡ _ _ refl)))))


  -------------------------------------------------------------------------------

  -- Now we establish the more familiar relations:
  --
  --            ℕ         --|-- Dyn
  --
  --        Dyn × Dyn     --|-- Dyn
  --
  --     U (Dyn ⟶ F Dyn) --|-- Dyn
  

  SigmaNatPi⊥Dyn : ValType ℓ ℓ ℓ ℓ-zero
  SigmaNatPi⊥Dyn = (ΣV NatDisc (λ n → ΠV BotDisc (λ _ → DynV')))

  -- SigmaBoolPiUnitDyn : ValType ℓ ℓ ℓ ℓ-zero
  -- SigmaBoolPiUnitDyn = (ΣV BoolDisc λ b → ΠV UnitDisc (λ _ → DynV))

  SigmaUnitPiBoolDyn : ValType ℓ ℓ ℓ ℓ-zero
  SigmaUnitPiBoolDyn = ΣV UnitDisc (λ _ → ΠV BoolDisc (λ _ → DynV'))

  NatSet : hSet ℓ-zero
  NatSet = (ℕ , isSetℕ)

  BoolSet : hSet ℓ-zero
  BoolSet = (Bool , Discrete→isSet (BoolDisc .snd))

  UnitSet : hSet ℓ-zero
  UnitSet = (Unit , isSetUnit)
  -- We cannot use the usual isSetBool, because that is not defined using
  -- discreteness of Bool and hence we will run into a definitional mismatch
  -- since the passage from Σ-ValType to Σ-Predomain uses discreteness.

  isoSum-Sigma : StrongIsoV (SigmaNatPi⊥Dyn Types.⊎ SigmaUnitPiBoolDyn) SigmaV
  isoSum-Sigma = isoΣΠ⊎ΣΠ-ΣΠ NatDisc UnitDisc BotDisc BoolDisc DynV'
  -- mkStrongIsoV isoP isoM eq

{-
      isoP' : PredomIso
        (ΣP NatSet  (λ n →  ΠP ⊥    (λ _ → ValType→Predomain DynV)) ⊎p
         ΣP UnitSet (λ tt → ΠP Bool (λ _ → ValType→Predomain DynV)))                         

        (ΣP ((ℕ Sum.⊎ Unit) , {!!})
          (λ s → ΠP (Sum.rec (λ n → ⊥) (λ tt → Bool) s) λ _ → ValType→Predomain DynV))

      isoP' = PredomIso-Inv
        let foo : PredomIso
                    (ΣP (ℕ Sum.⊎ Unit , {!!})
                      (λ s → ΠP (Sum.rec (λ _ → ⊥) (λ tt₁ → Bool) s)
                        (Sum.elim {C = λ s' → Sum.rec _ _ s' → PosetBisim _ _ _}
                          (λ _ _ → ValType→Predomain DynV) (λ _ _ → ValType→Predomain DynV) s)))
                    {!!}
            foo = Predom-Iso-ΣΠ-⊎ NatSet UnitSet (λ _ → ⊥) (λ tt → Bool)
                  (λ _ _ → ValType→Predomain DynV) (λ _ _ → ValType→Predomain DynV)
        in {!foo!}


      isoP : PredomIso
        (ValType→Predomain (SigmaNatPi⊥Dyn Types.⊎ SigmaUnitPiBoolDyn))
        (ValType→Predomain SigmaV)
      isoP .PredomIso.fun = ⊎p-rec
        (Σ-mor' NatSet (ℕ Sum.⊎ ⊤ , Discrete→isSet (S .snd)) inl
          (λ n → ΠP ⊥ (λ _ → ValType→Predomain DynV'))
          (λ z → ΠP ⟨ P z ⟩ λ _ → ValType→Predomain DynV')
          (λ n → Id))
        (Σ-mor' UnitSet (ℕ Sum.⊎ ⊤ , Discrete→isSet (S .snd)) inr _ _ (λ tt → Id))
      isoP .PredomIso.inv = Σ-elim (Sum.elim (λ n → σ1 ∘p Σ-intro n) (λ tt → σ2 ∘p Σ-intro tt))
      isoP .PredomIso.invRight (inl _ , _) = refl
      isoP .PredomIso.invRight (inr _ , _) = refl
      isoP .PredomIso.invLeft (inl _) = refl
      isoP .PredomIso.invLeft (inr _) = refl

      to : MonoidHom (PtbV (SigmaNatPi⊥Dyn Types.⊎ SigmaUnitPiBoolDyn)) (PtbV SigmaV)
      to = FP.rec
        (Indexed.rec _ _ _ (λ n → Indexed.rec _ _ _
          (λ bot → Indexed.σ _ _ (inl n) ∘hom Indexed.σ _ _ bot)))
        (Indexed.rec _ _ _ (λ tt → Indexed.rec _ _ _ (λ b →
               (Indexed.σ _ _ (inr tt))
          ∘hom (Indexed.σ _ _ b))))

      from : MonoidHom (PtbV SigmaV) (PtbV (SigmaNatPi⊥Dyn Types.⊎ SigmaUnitPiBoolDyn))
      from = Indexed.rec _ _ _
        λ { (inl n) → Indexed.rec _ _ _ (λ bot → i₁
               ∘hom Indexed.σ _ _ n
               ∘hom Indexed.σ _ _ bot)
          ; (inr _) → Indexed.rec _ _ _
            (λ b → i₂
              ∘hom (Indexed.σ ⊤ (λ _ → ⊕ᵢ Bool (λ _ → PtbV DynV)) tt)
              ∘hom (Indexed.σ Bool (λ _ → PtbV DynV) b))}

      opaque
        unfolding Indexed.elim Indexed.rec
        isoM : MonoidIso (PtbV (SigmaNatPi⊥Dyn Types.⊎ SigmaUnitPiBoolDyn)) (PtbV SigmaV)
        isoM = mkMonoidIso to from inv₁ inv₂
          where
            inv₁ : to ∘hom from ≡ idMon (PtbV SigmaV)
            inv₁ = Indexed.ind _ _
              (λ { (inl n)  → Indexed.ind _ _ (λ bot → eqMonoidHom _ _ refl)
                 ; (inr tt) → Indexed.ind _ _ (λ b →   eqMonoidHom _ _ refl)})
                 
            inv₂ : from ∘hom to ≡ idMon (PtbV _)
            inv₂ = FP.ind
              (Indexed.ind _ _ (λ n →  Indexed.ind _ _ λ bot → eqMonoidHom _ _ refl))
              (Indexed.ind _ _ (λ tt → Indexed.ind _ _ λ b   → eqMonoidHom _ _ refl))

        eq : interpV SigmaV ∘hom isoM .MonoidIso.fun ≡
             PredomIso→EndoHom isoP ∘hom interpV (SigmaNatPi⊥Dyn Types.⊎ SigmaUnitPiBoolDyn)
        eq = FP.ind
        
          (Indexed.ind _ _ (λ n → Indexed.ind _ _ (λ bot →
            eqMonoidHom _ _ (funExt (λ pD → PrePtb≡ _ _
              (funExt (λ { (inl m , ds) → {!!}
                         ; (inr tt , ds) → refl})))))))
              
          (Indexed.ind _ _ λ tt → Indexed.ind _ _ (λ b →
            eqMonoidHom _ _ (funExt (λ pD → PrePtb≡ _ _
              (funExt (λ { (inl n , ds) → refl
                         ; (inr tt , ds) → {!!}}))))))
-}                             
 

  rel1 : ValRel Types.ℕ SigmaV ℓ
  rel1 = Rel.⊙V (ValTyIso→ValRel iso1) (Rel.⊙V Rel.⊎-inl (ValTyIso→ValRel isoSum-Sigma))
    where
      iso1 : StrongIsoV Types.ℕ SigmaNatPi⊥Dyn
      iso1 = mkStrongIsoV isoP isoM eq'
        where
          isoP : PredomIso NatP (ValType→Predomain SigmaNatPi⊥Dyn)
          isoP = compPredomIso (PredomIso-Inv (isoSigmaUnit NatSet))
            (ΣP-cong-iso-snd NatSet (λ _ → UnitPB) _ (λ n → PredomIso-Inv isoPiBot))

          opaque
            unfolding Indexed.rec Indexed.elim
            isoM : MonoidIso (PtbV Types.ℕ) (PtbV SigmaNatPi⊥Dyn)
            isoM = mkMonoidIso
              Trivial.rec
              Trivial.corec
              (Indexed.ind _ _ λ n → Indexed.ind _ _ λ bot → eqMonoidHom _ _ (funExt (λ pD → ⊥.rec bot)))
              (eqMonoidHom _ _ refl)           

            eq' : (interpV SigmaNatPi⊥Dyn) ∘hom (isoM .MonoidIso.fun)
                ≡ (PredomIso→EndoHom isoP) ∘hom interpV Types.ℕ
            eq' = Trivial.ind _ _  -- any two homomorphisms out of the trivial monoid are equal


  rel2 : ValRel (DynV' Types.× DynV') SigmaV ℓ
  rel2 = Rel.⊙V (ValTyIso→ValRel iso1)
                (Rel.⊙V Rel.⊎-inr (ValTyIso→ValRel isoSum-Sigma))
    where
      test-iso : ∀ {X : Type ℓ} {Y : Type ℓ'}
        → Iso ((Lift {j = ℓ'} X) Prod.× (Lift {j = ℓ} Y))
              (Σ[ tt ∈ Unit ] ((b : Bool) → if b then Lift {j = ℓ'} X else Lift {j = ℓ} Y))
              
      test-iso {X = X} {Y = Y} .Iso.fun (x , y) = tt ,
        Bool.elim {A = λ b → if b then Lift X else Lift Y} x y
        
      test-iso .Iso.inv (tt , f) = ((f true) , (f false))
      
      test-iso .Iso.rightInv (tt , f) = ≡-× refl
        (funExt (Bool.elim {A = λ b → Bool.elim (f true) (f false) b ≡ f b} refl refl))
        
      test-iso .Iso.leftInv (x , y) = refl
      
      iso1 : StrongIsoV (DynV' Types.× DynV') SigmaUnitPiBoolDyn
      iso1 = mkStrongIsoV isoP isoM eq
        where
          isoP : PredomIso _ _
          isoP .PredomIso.fun = Σ-intro tt ∘p Π-intro λ b → if b then π1 else π2
          isoP .PredomIso.inv = ×-intro (Σ-elim (λ tt → Π-elim true)) (Σ-elim (λ tt → Π-elim false))
          isoP .PredomIso.invRight (tt , ds) = ≡-× refl (funExt (λ { false → refl ; true → refl}))
          isoP .PredomIso.invLeft (d , d') = refl

          opaque
            unfolding Indexed.rec Indexed.elim
            isoM : MonoidIso (PtbV (DynV' Types.× DynV')) (PtbV SigmaUnitPiBoolDyn)
            isoM = mkMonoidIso
              (FP.rec (Indexed.σ _ _ tt ∘hom Indexed.σ _ _ true) (Indexed.σ _ _ tt ∘hom Indexed.σ _ _ false))
              (Indexed.rec _ _ _ (λ tt → Indexed.rec _ _ _ (λ b → if b then i₁ else i₂)))
              (Indexed.ind _ _ (λ tt → Indexed.ind _ _ (λ { false → eqMonoidHom _ _ refl ; true → eqMonoidHom _ _ refl})))
              (FP.ind (eqMonoidHom _ _ refl) (eqMonoidHom _ _ refl))

            eq : (interpV SigmaUnitPiBoolDyn ∘hom isoM .MonoidIso.fun
               ≡ PredomIso→EndoHom isoP ∘hom interpV (DynV' Types.× DynV'))
            eq = FP.ind
                  (eqMonoidHom _ _ (funExt (λ pD → PrePtb≡ _ _ (funExt (λ { (tt , ds) →
                    ΣPathP (refl , (funExt (λ { false → refl ; true → refl})))})))))
                  (eqMonoidHom _ _ (funExt (λ pD → PrePtb≡ _ _ (funExt (λ { (tt , ds) →
                    ΣPathP (refl , funExt (λ { false → refl ; true → refl})) })))))
            
       

  injSigma : ValRel SigmaV-internal DynV ℓ
  injSigma = Defs.inj-SigmaV

  injArr' : ValRel C-nextD-internal DynV ℓ
  injArr' = Defs.inj-XV

  
  
