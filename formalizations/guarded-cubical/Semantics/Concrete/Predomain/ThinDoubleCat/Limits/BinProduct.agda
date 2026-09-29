{-# OPTIONS --rewriting --guarded #-}
{-# OPTIONS --lossy-unification #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import Common.Later

module Semantics.Concrete.Predomain.ThinDoubleCat.Limits.BinProduct (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma

open import Semantics.Concrete.Predomain.ThinDoubleCat.Base k

private
  variable
    ℓ ℓ' : Level
    ℓob ℓv ℓh ℓsq ℓ≈ : Level


module _ (C : ThinDoubleCat ℓob ℓv ℓh ℓsq ℓ≈) where

  private open module C = ThinDoubleCat C

  module _ {x y x×y : ob}
           (π₁ : vhom[ x×y , x ])
           (π₂ : vhom[ x×y , y ]) where

    isBinProductV : Type (ℓ-max ℓob ℓv)
    isBinProductV = ∀ {z : ob} (f₁ : vhom[ z , x ]) (f₂ : vhom[ z , y ])
      → ∃![ f ∈ vhom[ z , x×y ] ] (f ⋆V π₁ ≡ f₁) × (f ⋆V π₂ ≡ f₂)

    -- TODO: what about preservation of bisimilarity? I.e., if f₁ ≈ g₁ and f₂ ≈ g₂, then
    -- (f₁ , f₂) ≈ (g₁ , g₂)


  record BinProductV (x y : ob) : Type (ℓ-max ℓob ℓv) where
    field
      binProdOb  : ob
      binProdPr₁ : vhom[ binProdOb , x ]
      binProdPr₂ : vhom[ binProdOb , y ]
      univProp   : isBinProductV binProdPr₁ binProdPr₂

    π₁ = binProdPr₁
    π₂ = binProdPr₂

    binProdArrow : {z : ob} → vhom[ z , x ] → vhom[ z , y ] → vhom[ z , binProdOb ]
    binProdArrow f g = univProp f g .fst .fst

    binProdArrowUnique : {z : ob} {f : vhom[ z , x ]} {g : vhom[ z , y ]} {h : vhom[ z , binProdOb ]}
      → h ⋆V binProdPr₁ ≡ f → h ⋆V binProdPr₂ ≡ g → binProdArrow f g ≡ h
    binProdArrowUnique {f = f} {g = g} {h = h} p q i = univProp f g .snd (h , p , q) i .fst

    -- Beta rules for products:
    binProdArrowPr₁ : {z : ob} {f : vhom[ z , x ]} {g : vhom[ z , y ]}
      → binProdArrow f g ⋆V binProdPr₁ ≡ f
    binProdArrowPr₁ {f = f} {g = g} = univProp f g .fst .snd .fst

    binProdArrowPr₂ : {z : ob} {f : vhom[ z , x ]} {g : vhom[ z , y ]}
      → binProdArrow f g ⋆V binProdPr₂ ≡ g
    binProdArrowPr₂ {f = f} {g = g} = univProp f g .fst .snd .snd


  module _
    {x₁ y₁ x₂ y₂ : ob}
    (prod₁ : BinProductV x₁ y₁)
    (prod₂ : BinProductV x₂ y₂)
    where

    open BinProductV

    private
      module prod₁ = BinProductV prod₁
      module prod₂ = BinProductV prod₂
      x₁×y₁ = prod₁.binProdOb
      x₂×y₂ = prod₂.binProdOb

    module _
      {r : hhom[ x₁ , x₂ ]} {s : hhom[ y₁ , y₂ ]}
      {r×s : hhom[ x₁×y₁ , x₂×y₂ ]}
      (π₁-sq : sq r×s r prod₁.π₁ prod₂.π₁)
      (π₂-sq : sq r×s s prod₁.π₂ prod₂.π₂)
      where

      isBinProductH : Type (ℓ-max (ℓ-max (ℓ-max ℓob ℓv) ℓh) ℓsq)
      isBinProductH = ∀ {z₁ z₂ : ob} {q : hhom[ z₁ , z₂ ]}
        → (f₁ : vhom[ z₁ , x₁ ]) (g₁ : vhom[ z₁ , y₁ ])
        → (f₂ : vhom[ z₂ , x₂ ]) (g₂ : vhom[ z₂ , y₂ ])
        → (sqr : sq q r f₁ f₂) (sqs : sq q s g₁ g₂)
        → sq q r×s (prod₁.binProdArrow f₁ g₁) (prod₂.binProdArrow f₂ g₂)
        -- → ∃![ f ∈ vhom[ z , x×y ] ] (f ⋆V π₁ ≡ f₁) × (f ⋆V π₂ ≡ f₂)


    --          q                   q
    --    z₁ ---|--- z₂       z₁ ---|--- z₂
    --    |          |        |          |
    -- f₁ |    sqr   | f₂  g₁ |    sqs   | g₂   
    --    v          v        v          v
    --    x₁ ---|--- x₂       y₁ ---|--- y₂
    --          r                   s
    --
    --                    q         
    --           z₁ ------|------ z₂   
    --           |                |    
    -- (f₁ , g₁) |    sqr × sqs   | (f₂ , g₂) 
    --           v                v    
    --         x₁×y₁ -----|----- x₂×y₂  
    --                  r × s        


    record BinProductH (r : hhom[ x₁ , x₂ ]) (s : hhom[ y₁ , y₂ ])
      : Type (ℓ-max (ℓ-max (ℓ-max ℓob ℓv) ℓh) ℓsq) where

      field
        binProdHomH : hhom[ x₁×y₁ , x₂×y₂ ]
        binProdPr₁H : sq binProdHomH r prod₁.π₁ prod₂.π₁
        binProdPr₂H : sq binProdHomH s prod₁.π₂ prod₂.π₂
        univPropH : isBinProductH binProdPr₁H binProdPr₂H


  -----------------------------------------------------------------------


  BinProductsV : Type (ℓ-max ℓob ℓv)
  BinProductsV = (x y : ob) → BinProductV x y


  module BinProdsV (prod : BinProductsV) where
  
    -- open module AllProductsV (x y : ob)
    --   = BinProductV (prod x y) public using (binProdOb; univProp)

    -- _×ob_ : (x y : ob) → ob
    -- x ×ob y = binProdOb x y

    private open module AllProductsVImpl {x y : ob} = BinProductV (prod x y) hiding (binProdOb; univProp)

    module _ (x y : ob) where
      open BinProductV (prod x y) public using (univProp) renaming (binProdOb to _×ob_)

    _×v_ : {x x' y y' : ob}
      → vhom[ x , x' ]
      → vhom[ y , y' ]
      → vhom[ x ×ob y , x' ×ob y' ]
    _×v_ f g = binProdArrow (π₁ ⋆V f) (π₂ ⋆V g)


  -----------------------------------------------------------------------


  BinProductsH : Type (ℓ-max (ℓ-max (ℓ-max ℓob ℓv) ℓh) ℓsq)
  BinProductsH =
    {x₁ y₁ x₂ y₂ : ob}
    → (prod₁ : BinProductV x₁ y₁)
    → (prod₂ : BinProductV x₂ y₂)
    → (r : hhom[ x₁ , x₂ ]) (s : hhom[ y₁ , y₂ ])
    → BinProductH prod₁ prod₂ r s

  BinProductsH' : BinProductsV → Type (ℓ-max (ℓ-max (ℓ-max ℓob ℓv) ℓh) ℓsq)
  BinProductsH' prod = {x₁ y₁ x₂ y₂ : ob}
    → (r : hhom[ x₁ , x₂ ]) (s : hhom[ y₁ , y₂ ])
    → BinProductH (prod x₁ y₁) (prod x₂ y₂) r s


  module BinProdsH (prodV : BinProductsV) (prodH : BinProductsH' prodV) where
  
    open module AllProductsH {x₁ y₁ x₂ y₂ : ob} (r : hhom[ x₁ , x₂ ]) (s : hhom[ y₁ , y₂ ])
      = BinProductH (prodH r s) public using (binProdHomH)


-----------------------------------------------------------------------


  -- Record combining vertical and horizontal products
  record BinProducts : Type (ℓ-max (ℓ-max ℓob ℓv) (ℓ-max ℓh ℓsq)) where
    field
      bpV : BinProductsV
      bpH : BinProductsH' bpV

    open module AllProductsV (x y : ob)
      = BinProductV (bpV x y) public using (binProdOb; univProp)
      
    open module AllProductsH {x₁ y₁ x₂ y₂ : ob} (r : hhom[ x₁ , x₂ ]) (s : hhom[ y₁ , y₂ ])
      = BinProductH (bpH r s) public using (binProdHomH)

    _×ob_ : (x y : ob) → ob
    x ×ob y = binProdOb x y

    _×h_ : {x₁ y₁ x₂ y₂ : ob} (r : hhom[ x₁ , x₂ ]) (s : hhom[ y₁ , y₂ ])
      → hhom[ x₁ ×ob y₁ , x₂ ×ob y₂ ]
    r ×h s = binProdHomH r s



  -- record BinProductFor (x y : ob) : Type {!!} where
  --   field
  --     x×y : ob
  --     π₁ : C [ x×y , x ]v
  --     π₂ : C [ x×y , y ]v

  --     univ : {z : ob} → (f : C [ z , x ]v) (g : C [ z , y ]v)
  --       → ∃![ h ∈ C [ z , x×y ]v ]
  --         ( ((h ⋆V π₁) ≡ f) × ((h ⋆V π₂) ≡ g) )
