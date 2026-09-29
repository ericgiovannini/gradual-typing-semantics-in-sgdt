{-# OPTIONS --rewriting --guarded #-}
{-# OPTIONS --lossy-unification #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import Common.Later

module Semantics.Concrete.Predomain.ThinDoubleCat.Constructions.Product (k : Clock) where


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma
open import Cubical.Foundations.HLevels

open import Semantics.Concrete.Predomain.ThinDoubleCat.Base k
open import Semantics.Concrete.Predomain.ThinDoubleCat.Functor.Base k
open import Semantics.Concrete.Predomain.ThinDoubleCat.Functor.Identity k
open import Semantics.Concrete.Predomain.ThinDoubleCat.Constructions.Opposite k

private
  variable
    ℓ : Level
    ℓob ℓv ℓh ℓsq ℓ≈ : Level
    ℓob' ℓv' ℓh' ℓsq' ℓ≈' : Level
    ℓobC ℓvC ℓhC ℓsqC ℓ≈C : Level
    ℓobD ℓvD ℓhD ℓsqD ℓ≈D : Level
    ℓobE ℓvE ℓhE ℓsqE ℓ≈E : Level


module _
  (C : ThinDoubleCat ℓobC ℓvC ℓhC ℓsqC ℓ≈C)
  (D : ThinDoubleCat ℓobD ℓvD ℓhD ℓsqD ℓ≈D) where

  open ThinDoubleCat

  private
    module C = ThinDoubleCat C
    module D = ThinDoubleCat D

  infixl 10 _×C_ -- is this a good level?

  _×C_ : ThinDoubleCat (ℓ-max ℓobC ℓobD) (ℓ-max ℓvC ℓvD) (ℓ-max ℓhC ℓhD) (ℓ-max ℓsqC ℓsqD) (ℓ-max ℓ≈C ℓ≈D)
  _×C_ .ob = C.ob × D.ob
  _×C_ .vhom[_,_] (c , d) (c' , d') = C [ c , c' ]v × (D [ d , d' ]v)
  _×C_ .hhom[_,_] (c , d) (c' , d') = C [ c , c' ]h × D [ d , d' ]h
  _×C_ .sq {cᵢ , dᵢ} {cᵢ' , dᵢ'} {cₒ , dₒ} {cₒ' , dₒ'}
    (rᵢ , sᵢ) (rₒ , sₒ) (f , g) (f' , g') =
      (C [ rᵢ , rₒ , f , f' ]sq)
    × (D [ sᵢ , sₒ , g , g' ]sq)
  _×C_ .idV = C.idV , D.idV
  _×C_ ._⋆V_ (f , g) (f' , g') = (f C.⋆V f') , (g D.⋆V g')
  _×C_ .idLV (f , g) = ≡-× (C.idLV f) (D.idLV g)
  _×C_ .idRV (f , g) = ≡-× (C.idRV f) (D.idRV g)
  _×C_ .assocV (f , g) (f' , g') (f'' , g'') =
    ≡-× (C.assocV f f' f'') (D.assocV g g' g'')
  _×C_ .idH = C.idH , D.idH
  _×C_ ._⋆H_ (r , s) (r' , s') = (r C.⋆H r') , (s D.⋆H s')
  _×C_ .idLH (r , s) = ≡-× (C.idLH r) (D.idLH s)
  _×C_ .idRH (r , s) = ≡-× (C.idRH r) (D.idRH s)
  _×C_ .assocH (r , s) (r' , s') (r'' , s'') =
    ≡-× (C.assocH r r' r'') (D.assocH s s' s'')
  _×C_ .idSqV (r , s) = (C.idSqV r , D.idSqV s)
  _×C_ .idSqH (f , g) = (C.idSqH f , D.idSqH g)
  _×C_ ._⋆SqV_ (sq1 , sq2) (sq1' , sq2') =
    (C._⋆SqV_ sq1 sq1' , D._⋆SqV_ sq2 sq2')
  _×C_ ._⋆SqH_ (sq1 , sq2) (sq1' , sq2') =
    (C._⋆SqH_ sq1 sq1' , D._⋆SqH_ sq2 sq2')
  _×C_ .isSetVMor = isSet× C.isSetVMor D.isSetVMor
  _×C_ .isSetHMor = isSet× C.isSetHMor D.isSetHMor
  _×C_ .isPropSq (rᵢ , sᵢ) (rₒ , sₒ) (f , g) (f' , g') = {!!}
  _×C_ ._≈vhom_ (f , g) (f' , g') = (f C.≈vhom f') × (g D.≈vhom g')
  _×C_ .isBisim≈ = {!!}
  _×C_ .comp≈ = {!!}


module _
  {C : ThinDoubleCat ℓobC ℓvC ℓhC ℓsqC ℓ≈C}
  {D : ThinDoubleCat ℓobD ℓvD ℓhD ℓsqD ℓ≈D}
  where

  private
    module C = ThinDoubleCat C
    module D = ThinDoubleCat D

  open FunctorBase
  open FunctorWithLaxity

  ×opBase : FunctorBase ((C ×C D) ^op) ((C ^op) ×C (D ^op))
  ×opBase .F-ob (c , d) = c , d
  ×opBase .F-homV (f , g) = f , g
  ×opBase .F-idV = refl
  ×opBase .F-seqV f g = refl
  ×opBase .F-homH (r , s) = r , s
  ×opBase .F-idH = refl
  ×opBase .F-sq (square , square') = square , square'
  ×opBase .F-bisim f g f≈g = f≈g

  -- ×op = IdF ((C ×C D) ^op)
  ×op : {l : Laxity}
    → FunctorWithLaxity l ((C ×C D) ^op) ((C ^op) ×C (D ^op))
  ×op .base = ×opBase
  ×op {strict} .F-seqH r r' = {!!}
  ×op {lax} .F-seqH r r' = {!!}
  ×op {oplax} .F-seqH r r' = {!!}



module _
  {C : ThinDoubleCat ℓobC ℓvC ℓhC ℓsqC ℓ≈C}
  {D : ThinDoubleCat ℓobD ℓvD ℓhD ℓsqD ℓ≈D}
  where

  open FunctorBase
  open FunctorWithLaxity

  private
    module C = ThinDoubleCat C
    module D = ThinDoubleCat D

  Pr₁Base : FunctorBase (C ×C D) C
  Pr₁Base .F-ob (c , d) = c
  Pr₁Base .F-homV (f , g) = f
  Pr₁Base .F-idV = refl
  Pr₁Base .F-seqV f g = refl
  Pr₁Base .F-homH (r , s) = r
  Pr₁Base .F-idH = refl
  Pr₁Base .F-sq (square , square') = square
  Pr₁Base .F-bisim f g f≈g = f≈g .fst

  Pr₂Base : FunctorBase (C ×C D) D
  Pr₂Base .F-ob (c , d) = d
  Pr₂Base .F-homV (f , g) = g
  Pr₂Base .F-idV = refl
  Pr₂Base .F-seqV f g = refl
  Pr₂Base .F-homH (r , s) = s
  Pr₂Base .F-idH = refl
  Pr₂Base .F-sq (square , square') = square'
  Pr₂Base .F-bisim f g f≈g = f≈g .snd


  Pr₁ : {l : Laxity} → FunctorWithLaxity l (C ×C D) C
  Pr₁ .base = Pr₁Base
  Pr₁ {strict} .F-seqH r s = lift refl
  Pr₁ {lax} .F-seqH r s = lift (C.idSqV _)
  Pr₁ {oplax} .F-seqH r s = lift (C.idSqV _)

  Pr₂ : {l : Laxity} → FunctorWithLaxity l (C ×C D) D
  Pr₂ .base = Pr₂Base
  Pr₂ {strict} .F-seqH r s = lift refl
  Pr₂ {lax} .F-seqH r s = lift (D.idSqV _)
  Pr₂ {oplax} .F-seqH r s = lift (D.idSqV _)




module _
  {C : ThinDoubleCat ℓobC ℓvC ℓhC ℓsqC ℓ≈C}
  {D : ThinDoubleCat ℓobD ℓvD ℓhD ℓsqD ℓ≈D}
  {E : ThinDoubleCat ℓobE ℓvE ℓhE ℓsqE ℓ≈E}
  where

  private
    module C = ThinDoubleCat C
    module D = ThinDoubleCat D
    module E = ThinDoubleCat E

  module _ {l : Laxity}
    (F : FunctorWithLaxity l C D) (G : FunctorWithLaxity l C E) where
    
    -- open FunctorWithLaxity

    private
      module F = FunctorWithLaxity F
      module G = FunctorWithLaxity G

    PairBase : FunctorBase C (D ×C E)
    PairBase .FunctorBase.F-ob x = F ⟅ x ⟆ , G ⟅ x ⟆
    PairBase .FunctorBase.F-homV f = F ⟪ f ⟫v , G ⟪ f ⟫v
    PairBase .FunctorBase.F-idV = ≡-× F.F-idV G.F-idV
    PairBase .FunctorBase.F-seqV f g = ≡-× (F.F-seqV f g) (G.F-seqV f g)
    PairBase .FunctorBase.F-homH r = F ⟪ r ⟫h , G ⟪ r ⟫h
    PairBase .FunctorBase.F-idH = ≡-× F.F-idH G.F-idH
    PairBase .FunctorBase.F-sq square = (F.F-sq square) , (G.F-sq square)
    PairBase .FunctorBase.F-bisim f g f≈g = (F.F-bisim f g f≈g) , (G.F-bisim f g f≈g)



  open FunctorWithLaxity

  _,F_ : {l : Laxity}
       → FunctorWithLaxity l C D
       → FunctorWithLaxity l C E
       → FunctorWithLaxity l C (D ×C E)
  _,F_ F G .base = PairBase F G
  
  _,F_ {strict} F G .F-seqH r s =
    lift (≡-× (lower (F .F-seqH r s)) (lower (G .F-seqH r s)))
    
  _,F_ {lax} F G .F-seqH r s =
    lift ((lower (F .F-seqH r s)) , (lower (G .F-seqH r s)))
    where
      module F = FunctorWithLaxity F
      module G = FunctorWithLaxity G
      
  _,F_ {oplax} F G .F-seqH r s =
    lift ((lower (F .F-seqH r s)) , (lower (G .F-seqH r s)))

-- (F .F-seqH r s) , (G .F-seqH r s)
   

