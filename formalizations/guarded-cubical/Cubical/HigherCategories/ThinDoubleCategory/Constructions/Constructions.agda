
-- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}


module Cubical.HigherCategories.ThinDoubleCategory.Constructions.Constructions where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma


open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Limits.BinProduct
open import Cubical.Categories.Displayed.Limits.Terminal
open import Cubical.Categories.Displayed.Preorder

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Limits.Terminal renaming (Terminal to 1Terminal)
open import Cubical.Categories.Limits.BinProduct renaming
  (BinProduct to 1BinProduct ; BinProducts to 1BinProducts)
open import Cubical.Categories.Limits.BinProduct.More

open import Cubical.HigherCategories.ThinDoubleCategory.ThinDoubleCat

open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Functors.Constant
open import Cubical.Categories.Instances.Sets
open import Cubical.Foundations.HLevels
open import Cubical.Categories.Functor.Base
open import Cubical.Foundations.Equiv

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level

open ThinDoubleCat

open Category
open Functor
open UniversalElement


--
-- Product of Hsets
--
_×hs_ : hSet ℓ -> hSet ℓ' -> hSet (ℓ-max ℓ ℓ')
(A , isSetA) ×hs (B , isSetB) = A × B , isSet× isSetA isSetB

--
-- Product of presheaves
--
_×Psh_ : {C D : Category ℓ ℓ'} {ℓS : Level} -> Presheaf C ℓS -> Presheaf D ℓS ->
  Presheaf (C ×C D) ℓS
(P ×Psh Q) .F-ob (c , d) =
  (P .F-ob c) ×hs (Q .F-ob d)
(P ×Psh Q) .F-hom {(c , d)} {(c' , d')} (f , g) (x , y) =
  (P .F-hom f x) , (Q .F-hom g y)
(P ×Psh Q) .F-id {c , d} =
  funExt λ {(x , y) -> ≡-× (funExt⁻ (P .F-id) x) (funExt⁻ (Q .F-id) y)}
(P ×Psh Q) .F-seq {c , d} {c' , d'} {c'' , d''} (f , g) (f' , g') =
  funExt (λ { (x , y) -> ≡-× (funExt⁻ (P .F-seq f f') x) (funExt⁻ (Q .F-seq g g') y) })

--
-- Universal element of the product of presheaves
--
_×UE_ : {C D : Category ℓ ℓ'} {ℓS : Level} {P : Presheaf C ℓS} {Q : Presheaf D ℓS} ->
  UniversalElement C P -> UniversalElement D Q ->
  UniversalElement (C ×C D) (_×Psh_ {C = C} {D = D} P Q)
(ηP ×UE ηQ) .vertex = (ηP .vertex) , (ηQ .vertex)
(ηP ×UE ηQ) .element = ηP .element , ηQ .element 
(ηP ×UE ηQ) .universal (c , d) .equiv-proof (x , y) .fst .fst =
  ((ηP .universal c .equiv-proof x .fst .fst) ,
   (ηQ .universal d .equiv-proof y .fst .fst))
(ηP ×UE ηQ) .universal (c , d) .equiv-proof (x , y) .fst .snd =
  ≡-× (ηP .universal c .equiv-proof x .fst .snd)
      (ηQ .universal d .equiv-proof y .fst .snd)
(ηP ×UE ηQ) .universal (c , d) .equiv-proof (x , y) .snd ((f , g) , t) =
  -- could use Σ≡Prop
  ΣPathP ((≡-× (cong fst (ηP .universal c .equiv-proof x .snd (f , cong fst t)))
               (cong fst (ηQ .universal d .equiv-proof y .snd (g , cong snd t)))) ,

           λ i → ≡-× (ηP .universal c .equiv-proof x .snd (f , cong fst t) i .snd)
                     (ηQ .universal d .equiv-proof y .snd (g , cong snd t) i .snd))
         -- λ i j → (ηP .universal c .equiv-proof x .snd (f , cong fst t) i .snd j) ,
         --          ηQ .universal d .equiv-proof y .snd (g , cong snd t) i .snd j)


---
-- Constant presheaf over C ×C D equals the product of
-- constant presheaves over C and D
---
Const-product : ∀ {C D : Category ℓ ℓ'} {x : hSet ℓ''} ->
  (Constant (C ×C D) (SET ℓ'') (x ×hs x)) ≡
  (_×Psh_ {C = C ^op} {D = D ^op} (Constant C (SET ℓ'') x) (Constant D (SET ℓ'') x))
Const-product = Functor≡
  (λ {(c , d) -> refl })
  λ f -> refl



-- Define terminal objects on a thin double category C
-- in terms of displayed terminal objects on the
-- displayed category of squares (Squares C)
module _ (C : ThinDoubleCat ℓ ℓ' ℓ'' ℓ''') where

  open Category (VCat C)

  module Terminal  where

    -- User provices a terminal object in VCat, and we construct a terminal object
    -- in the displayed preorder of squares of C.

    -- UniversalElement (C ×C D)
    

    Term : (t : 1Terminal (VCat C)) ->
      Type (ℓ-max (ℓ-max (ℓ-max ℓ'' ℓ''') (ℓ-max ℓ ℓ)) (ℓ-max ℓ' ℓ'))
    Term t = Terminalᴰ (Preorderᴰ→Catᴰ (Squares C))
      (transport {!!} (terminalToUniversalElement t ×UE terminalToUniversalElement t))


      -- "manual" way
      -- (Preorderᴰ→Catᴰ (Squares C)) (terminalToUniversalElement
      --   ((fst t , fst t) ,
      --     (λ { (c , c') →
      --       ((t .snd c .fst) , (t .snd c' .fst)) ,
      --       λ { (f , f') → ≡-× (t .snd c .snd f) (t .snd c' .snd f')}})))

    Terminal : Type (ℓ-max (ℓ-max (ℓ-max ℓ ℓ') ℓ'') ℓ''')
    Terminal = Σ[ t ∈ 1Terminal (VCat C) ] Term t


  module Prod where

    {-
    Prod : (p : 1BinProducts (VCat C)) ->
      Type {!!}
    Prod p = BinProductᴰ (Preorderᴰ→Catᴰ (Squares C)) {!!} {!!}
    -}





  
