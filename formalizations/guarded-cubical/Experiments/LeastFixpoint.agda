{-# OPTIONS --rewriting --guarded #-}

{-# OPTIONS --allow-unsolved-metas #-}

{-# OPTIONS --lossy-unification #-}

open import Common.Later

module Semantics.Concrete.LeastFixpoint (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Transport.More
open import Cubical.Foundations.Function
open import Cubical.Foundations.Path
open import Cubical.Foundations.GroupoidLaws

open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Nullary

open import Cubical.Data.Nat hiding (_·_)
open import Cubical.Data.Bool
open import Cubical.Data.Sum as Sum
open import Cubical.Data.W.Indexed
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Unit renaming (Unit to ⊤ ; Unit* to ⊤*)
open import Cubical.Data.Sigma

open import Cubical.Algebra.Monoid.Base
open import Cubical.Algebra.Monoid.More
open import Cubical.Algebra.Monoid.Instances.CartesianProduct as Cart hiding (_×_)
open import Cubical.Algebra.Monoid.Instances.Trivial as Trivial
open import Cubical.Algebra.Monoid.FreeProduct as FP
open import Cubical.Algebra.Monoid.FreeMonoid as Free
open import Cubical.Algebra.Monoid.FreeProduct.Indexed as Indexed
open import Cubical.Algebra.Monoid.Displayed
open import Cubical.Algebra.Monoid.Displayed.Instances.Sigma
open import Cubical.Algebra.Monoid.Displayed.Instances.Reindex

open import Common.Common
open import Semantics.Concrete.GuardedLiftError k
open import Semantics.Concrete.DoublePoset.Base
open import Semantics.Concrete.DoublePoset.Convenience
open import Semantics.Concrete.DoublePoset.Constructions renaming (ℕ to NatP)
open import Semantics.Concrete.DoublePoset.DblPosetCombinators hiding (U)
open import Semantics.Concrete.DoublePoset.Morphism hiding (_$_)
open import Semantics.Concrete.DoublePoset.DPMorRelation
open import Semantics.Concrete.DoublePoset.PBSquare
open import Semantics.Concrete.DoublePoset.FreeErrorDomain k

open import Semantics.Concrete.Predomains.PrePerturbations k
open import Semantics.Concrete.Types k as Ty hiding (Unit ; _×_)
open import Semantics.Concrete.Perturbation.Relation.Alt k
open import Semantics.Concrete.Perturbation.QuasiRepresentation k
open import Semantics.Concrete.Relations k

private
  variable
    ℓ ℓ' ℓS : Level
    ℓA ℓ≤A ℓ≈A : Level
    ℓ≤ ℓ≈ : Level

  ▹_ : {ℓ : Level} → Type ℓ → Type ℓ
  ▹_ A = ▹_,_ k A

open BinaryRelation


module _ {ℓ : Level}
  (S : DiscreteTy ℓS) (P : ⟨ S ⟩ → DiscreteTy ℓ-zero)
  where

  |P| = fst ∘ P

  |S| = ⟨ S ⟩
  dec-eq-S = S .snd

  dec-eq-P : ∀ s → _
  dec-eq-P s = P s .snd

  isSetS : isSet |S|
  isSetS = Discrete→isSet (S .snd)

  S-set : hSet ℓS
  S-set = (|S| , isSetS)


{-
  data Mu : Type ℓS

  MuPredomStr : PosetBisimStr ℓS ℓS Mu
  
  ⊑mu : Mu → Mu → Type {!!}
  ≈mu : Mu → Mu → Type {!!}

  data Mu where
    node : ⟨ ΣP S-set (λ s → ΠP (|P| s) (λ _ → Mu , MuPredomStr)) ⟩ → Mu

  MuPredomStr = predomRetractStr Mu (Σ[ s ∈ |S| ] ((p : |P| s) → Mu))
    (λ { (node sigma) → sigma})
    (λ s → node s) {!!} {!!}
-}


{-
  -- The underlying type
  data Mu : Type ℓS

  f : PosetBisimStr ℓS ℓS Mu

  data Mu where
    -- node : ∀ s → (|P| s → Mu) → Mu
    node : ⟨ ΣP S-set (λ s → ΠP (|P| s) (λ _ → Mu , f)) ⟩ → Mu

  f = predomRetractStr Mu (Σ[ s ∈ |S| ] ((p : |P| s) → Mu))
    (λ { (node sigma) → sigma})
    (λ s → node s)
    {!!}
    (ΣP S-set (λ s → ΠP (|P| s) λ _ → Mu , f) .snd)


  -- MuP : PosetBisim ℓS ℓS ℓS
  -- MuP .fst = Mu
  -- MuP .snd = (predomRetractStr Mu (Σ[ s ∈ |S| ] ((p : |P| s) → Mu)) (λ { (node s xs) → s , xs}) (λ { (s , xs) → node s xs}) {!!} (ΣP S-set (λ s → ΠP (|P| s) λ _ → MuP) .snd))
-}



  data Mu : Type ℓS

  test : (Mu → Mu → Type ℓS) → (Mu → Mu → Type ℓS)
  test ord = {!!}

  data Mu where
    node : (Σ[ s ∈ |S| ] ((|P| s) → Mu)) → Mu

  Sigma : Type ℓS
  Sigma = (Σ[ s ∈ |S| ] ((|P| s) → Mu))

  Pi : ∀ s → Type ℓS
  Pi s = (|P| s → Mu)
  

  _⊑mu_ : Mu → Mu → Type ℓS
  ordSigma : Sigma → Sigma → Type ℓS
  ordPi : ∀ s → (|P| s → Mu) → (|P| s → Mu) → Type ℓS

  node (s , xs) ⊑mu node (s' , ys) = ordSigma (s , xs) (s' , ys) -- SigmaPredomain .snd .PosetBisimStr._≤_ (s , xs) (s' , ys)
  
  ordSigma (s , xs) (s' , ys) = Σ[ eq ∈ (s ≡ s') ] ordPi s' (subst (λ v → |P| v → Mu) eq xs) ys
  ordPi s xs ys = ∀ (p : |P| s) → xs p ⊑mu ys p

  ord-refl : isRefl _⊑mu_
  ord-pi-refl : ∀ s → isRefl (ordPi s)

  ord-refl (node (s , xs)) = Σ-ord-refl S-set Pi (λ s → ordPi s) ord-pi-refl (s , xs)

  ord-pi-refl s = Π-ord-refl (|P| s) (λ _ → Mu) (λ p → _⊑mu_) (λ p → (λ a → ord-refl a))

  _≈mu_ : Mu → Mu → Type {!!}
  
  MuPredomStr : PosetBisimStr ℓS ℓS Mu
  MuPredomStr = posetbisimstr {!!} _⊑mu_ {!!} {!!} {!!}



{-


  -- The underlying type
  data Mu : Type ℓS where
    node : ∀ s → (|P| s → Mu) → Mu

  -- The ordering
  data _⊑mu_ : Mu → Mu → Type ℓS where
    ⊑node : ∀ s s' ds es →
      (eq : s ≡ s') →
      (∀ (p : |P| s) (p' : |P| s') (path : PathP (λ i → |P| (eq i)) p p') → (ds p ⊑mu es p')) →
      node s ds ⊑mu node s' es

  -- Bisimilarity
  data _≈mu_ : Mu → Mu → Type ℓS where
    ⊑node : ∀ s s' ds es →
      (eq : s ≡ s') →
      (∀ (p : |P| s) (p' : |P| s') (path : PathP (λ i → |P| (eq i)) p p') → (ds p ≈mu es p')) →
      node s ds ≈mu node s' es
  -------------------------------------
  -- Defining the predomain structure:
  -------------------------------------
  MuPredom : PosetBisim ℓS ℓS ℓS
  MuPredom .fst = Mu
  MuPredom .snd = posetbisimstr {!!}
    _⊑mu_ (isorderingrelation {!!} {!!} {!!} {!!})
    _≈mu_ (isbisim {!!} {!!} {!!})

  ΣΠPredom : PosetBisim ℓS ℓS ℓS
  ΣΠPredom = ΣP S-set (λ s → ΠP (|P| s) (λ _ → MuPredom))

  ΠPredom : ∀ s → PosetBisim ℓS ℓS ℓS
  ΠPredom s = ΠP (|P| s) λ _ → MuPredom

  Σ→Mu : PBMor ΣΠPredom MuPredom
  Σ→Mu .PBMor.f (s , xs) = node s xs
  Σ→Mu .PBMor.isMon {x = (s , xs)} {y = (s' , ys)} (eq , xs⊑ys) = ⊑node s s' xs ys eq {!!}
  Σ→Mu .PBMor.pres≈ = {!!}

  Mu→Σ : PBMor MuPredom ΣΠPredom
  Mu→Σ .PBMor.f (node s xs) = s , xs
  Mu→Σ .PBMor.isMon = {!!}
  Mu→Σ .PBMor.pres≈ = {!!}


  -- Perturbations + interpretation as endomorphisms
  PtbMu : Monoid ℓS
  PtbMu = FM ⊥ (Σ[ s ∈ |S| ] |P| s) ⊥

  PtbΣΠ : Monoid ℓS
  PtbΣΠ = (⊕ᵢ |S| λ s → ⊕ᵢ (|P| s) λ _ → PtbMu)

  PtbΠ : ∀ s → Monoid ℓS
  PtbΠ s = ⊕ᵢ (|P| s) (λ _ → PtbMu)

  PtbMu→PtbΣΠ : MonoidHom PtbMu PtbΣΠ
  PtbMu→PtbΣΠ = Free.rec ⊥ (Σ-syntax |S| |P|) ⊥ _ ⊥.rec (λ {(s , p) → idMon _}) ⊥.rec

  iΣ : MonoidHom PtbΣΠ (Endo ΣΠPredom)
  iΣ = Indexed.rec ⟨ S ⟩ (λ s → PtbΠ s) (Endo ΣΠPredom)
    (λ s → (Σ-PrePtb S-set dec-eq-S s) ∘hom (iΠ s))
    where
      iΠ : ∀ s →  MonoidHom (PtbΠ s) (Endo (ΠPredom s))
      iΠ s = Indexed.rec (|P| s) (λ _ → PtbMu) (Endo (ΠPredom s))
        (λ p → Π-PrePtb (|P| s) (dec-eq-P s) p ∘hom {!!})

  -- PtbMu ---> PtbΣΠ ---> Endo ΣΠ ---> Endo MuPredom

  iMu : MonoidHom PtbMu (Endo MuPredom)
  iMu = {!!}
    where
      interp : ⟨ MuPredom ⟩ → ⟨ MuPredom ⟩
      interp = {!!}


  MuV : ValType ℓS ℓS ℓS ℓS
  MuV = mkValType MuPredom PtbMu iMu


-}
