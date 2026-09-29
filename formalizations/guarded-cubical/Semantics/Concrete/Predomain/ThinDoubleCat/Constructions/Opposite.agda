{-# OPTIONS --rewriting --guarded #-}
{-# OPTIONS --lossy-unification #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import Common.Later

module Semantics.Concrete.Predomain.ThinDoubleCat.Constructions.Opposite (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Semantics.Concrete.Predomain.ThinDoubleCat.Base k
open import Semantics.Concrete.Predomain.ThinDoubleCat.Functor.Base k

private
  variable
    ℓ : Level
    ℓob ℓv ℓh ℓsq ℓ≈ : Level
    ℓobC ℓvC ℓhC ℓsqC ℓ≈C : Level
    ℓobD ℓvD ℓhD ℓsqD ℓ≈D : Level

module _ (C : ThinDoubleCat ℓob ℓv ℓh ℓsq ℓ≈) where

  private
    module C = ThinDoubleCat C

open ThinDoubleCat

-- Flips the direction of the vertical morphisms and the squares
_^op : (C : ThinDoubleCat ℓob ℓv ℓh ℓsq ℓ≈) → ThinDoubleCat ℓob ℓv ℓh ℓsq ℓ≈
(C ^op) .ob = C .ob
(C ^op) .vhom[_,_] x y = C [ y , x ]v
(C ^op) .hhom[_,_] x y = C [ x , y ]h
(C ^op) .sq cᵢ cₒ f g = C [ cₒ , cᵢ , f , g ]sq
(C ^op) .idV = C .idV
(C ^op) ._⋆V_ f g = g ⋆⟨ C ⟩v f
(C ^op) .idLV = C .idRV
(C ^op) .idRV = C .idLV
(C ^op) .assocV f g h = sym (C .assocV h g f)
(C ^op) .idH = C .idH
(C ^op) ._⋆H_ = C ._⋆H_
(C ^op) .idLH = C .idLH
(C ^op) .idRH = C .idRH
(C ^op) .assocH = C .assocH
(C ^op) .idSqV = C .idSqV
(C ^op) .idSqH = C .idSqH
(C ^op) ._⋆SqV_ sq sq' = C ._⋆SqV_ sq' sq
(C ^op) ._⋆SqH_ = C ._⋆SqH_
(C ^op) .isSetVMor = C .isSetVMor
(C ^op) .isSetHMor = C .isSetHMor
(C ^op) .isPropSq cᵢ cₒ f g x y = {!!}
(C ^op) ._≈vhom_ = C ._≈vhom_
(C ^op) .isBisim≈ = C .isBisim≈
(C ^op) .comp≈ = {!!}


module _
  (C : ThinDoubleCat ℓobC ℓvC ℓhC ℓsqC ℓ≈C)
  (D : ThinDoubleCat ℓobD ℓvD ℓhD ℓsqD ℓ≈D)  
  where

  open FunctorBase
  open FunctorWithLaxity

  private
    module C = ThinDoubleCat C
    module D = ThinDoubleCat D

  module _ {l : Laxity} (F : FunctorWithLaxity l C D) where

    private module F = FunctorWithLaxity F

    opBase : FunctorBase (C ^op) (D ^op)
    opBase .F-ob = F.F-ob
    opBase .F-homV = F.F-homV
    opBase .F-idV = F.F-idV
    opBase .F-seqV f g = F.F-seqV g f
    opBase .F-homH = F.F-homH
    opBase .F-idH = F.F-idH
    -- opBase .F-seqH r s = {!F.F-seqH ? ?!}
    opBase .F-sq = F.F-sq
    opBase .F-bisim = F.F-bisim


  opStrict : FunctorWithLaxity strict C D
    → FunctorWithLaxity strict (C ^op) (D ^op)
  opStrict F .base = opBase F
  opStrict F .F-seqH r s = lift (lower (F.F-seqH r s))
    where module F = FunctorWithLaxity F

 
  _^opF : {l : Laxity}
    → FunctorWithLaxity l C D
    → FunctorWithLaxity (l ^opL) (C ^op) (D ^op)
  _^opF F .base = opBase F
  _^opF {strict} F .F-seqH r s = lift (lower (F .F-seqH r s))
  _^opF {lax} F .F-seqH r s    = lift (lower (F .F-seqH r s))
  _^opF {oplax} F .F-seqH r s  = lift (lower (F .F-seqH r s))
  



-- (C ^op) ._≈vhom_ {xᵢ = xᵢ} {xₒ = xₒ} f g = C ._≈vhom_ {xᵢ = xₒ} {xₒ = xᵢ} f g
