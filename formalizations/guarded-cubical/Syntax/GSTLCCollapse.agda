{-# OPTIONS --cubical --rewriting --guarded #-}

open import Common.Later

module Syntax.GSTLCCollapse (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat hiding (_·_)
open import Cubical.Relation.Nullary
open import Cubical.Data.Sum
open import Cubical.Foundations.Isomorphism

import Syntax.DeBruijnCommon
open import Syntax.GSTLC k


private
 variable
    ℓ : Level

private
  ▹_ : Set ℓ → Set ℓ
  ▹_ A = ▹_,_ k A


IntTm = Tm Int
ExtTm = Tm Ext


⌊_⌋ : ∀ {Γ} {A} -> IntTm {Empty} Γ A -> ExtTm {Empty} Γ A
⌊ var x ⌋ = var x
⌊ lda M ⌋ = lda ⌊ M ⌋
⌊ app M N ⌋ = app ⌊ M ⌋ ⌊ N ⌋
⌊ err ⌋ = err
⌊ up c M ⌋ = up c ⌊ M ⌋
⌊ dn c M ⌋ = dn c ⌊ M ⌋
⌊ zro ⌋ = zro
⌊ suc M ⌋ = suc ⌊ M ⌋
⌊ θ M~ ⌋ = ⌊ M~ ◇ ⌋


embed : ∀ {Γ} {A} -> ExtTm {Empty} Γ A -> IntTm {Empty} Γ A
embed (var x) = var x
embed (lda M) = lda (embed M)
embed (app M N) = app (embed M) (embed N)
embed err = err
embed (up c M) = up c (embed M)
embed (dn c M) = dn c (embed M)
embed zro = zro
embed (suc M) = suc (embed M)



-- Every extensional term has an intensional program computing it
collapse-embed : ∀ {Γ} {A} -> retract embed (⌊_⌋ {Γ} {A})
collapse-embed (var x) = refl
collapse-embed (lda M) = cong lda (collapse-embed M)
collapse-embed (app M N) = cong₂ app (collapse-embed M) (collapse-embed N)
collapse-embed err = refl
collapse-embed (up c M) = cong (up c) (collapse-embed M)
collapse-embed (dn c M) = cong (dn c) (collapse-embed M)
collapse-embed zro = refl
collapse-embed (suc M) = cong suc (collapse-embed M)



