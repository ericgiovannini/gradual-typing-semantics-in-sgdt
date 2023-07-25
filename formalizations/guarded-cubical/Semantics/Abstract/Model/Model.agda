 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}

{-# OPTIONS --lossy-unification #-}


module Semantics.Abstract.Model.Model where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Algebra.Monoid
open import Cubical.Data.List

open import Cubical.Categories.Category.Base

open import Cubical.HigherCategories.ThinDoubleCategory.ThinDoubleCat
open import Cubical.HigherCategories.ThinDoubleCategory.Constructions.Terminal
open import Cubical.HigherCategories.ThinDoubleCategory.Constructions.BinProduct


private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level


-- An abstract model of the logic consists of
-- a thin double category C, such that
-- 
-- For each object S ∈ C₀ we have a (commutative) monoid Ptb_S with
-- an injective homomorphism ptb_S : Ptb_S -> VerticalEndo(S)
--
-- ...such that the following squares have at most one filler by
-- ptb_X and ptb_Y respectively:

--        c                   d
--   X o----* Y           X o----* Y
--            |           |        
--            | δY    δX  |        
--            v           v        
--   X o----* Y           X o----* Y
--       c                    d



-- The objects should be thought of as types with a relation.
-- The horizontal morphisms of C should be thought of as relations.
-- The vertical morphisms of C should be thought of as monotone functions.



isLeftInvertible : {ℓA ℓB : Level} {A : Type ℓA} {B : Type ℓB} ->
  (f : A -> B) -> Type (ℓ-max ℓA ℓB)
isLeftInvertible {A = A} {B = B} f =
 Σ[ g ∈ (B -> A) ] (∀ a -> g (f a) ≡ a)


InjectiveMonoidHom : {ℓm ℓn : Level} ->
  (M : Monoid ℓm) (N : Monoid ℓn) -> Type (ℓ-max ℓm ℓn)
InjectiveMonoidHom M N =
  Σ[ f ∈ MonoidHom M N ] isLeftInvertible (fst f)

-- Monoid of vertical endomorphisms of a given object of the given double category
VEndo : {ℓ ℓ' : Level} ->
  (C : ThinDoubleCat ℓ ℓ' ℓ'' ℓ''') -> (X : C .ThinDoubleCat.ob) -> Monoid ℓ'
VEndo C X = makeMonoid
    {M = HomV[ X , X ]} idV _⋆V_ (MorphismsForObj.isSetHom Vert)
    (λ p q r -> sym (⋆Assoc p q r)) (λ p -> ⋆IdR p) (λ p -> ⋆IdL p)
      where
        open ThinDoubleCat C
        open MorphismsForObj Vert



record Model (ℓ ℓ' ℓ'' ℓ''' : Level) :
  Type (ℓ-suc (ℓ-max (ℓ-max ℓ ℓ') (ℓ-max ℓ'' ℓ'''))) where

  -- A thin double category with additional structure
  field
    cat : ThinDoubleCat ℓ ℓ' ℓ'' ℓ'''
    term : Terminal cat
    prod : BinProducts cat
    -- exponentials : Exponentials cat binProd
    -- binCoprod : BinCoproducts cat
    -- monad : StrongExtensionSystem binProd

  -- module C = ThinDoubleCat C
  open ThinDoubleCat cat public

  open TerminalNotation cat term public
  open BinProdNotation cat prod public

  -- Perturbations
  field
    Ptb : (X : ob) -> Monoid ℓ'
    ptb : (X : ob) -> InjectiveMonoidHom (Ptb X) (VEndo cat X)

  ptb-f : {X : cat .ThinDoubleCat.ob} -> ⟨ (Ptb X) ⟩ -> ⟨ VEndo cat X ⟩
  ptb-f {X} = fst (fst (ptb X))

  -- Natural numbers, dynamic type, and error
  field

    nat : ob
    nat-fp : CatIso VCat {!!} nat
    -- match-nat

    dyn : ob
    -- inj : cat      [ nat + (dyn ⇀ dyn) , dyn ]
    -- prj : ClLinear [ dyn , nat + (dyn ⇀ dyn) ]


    err : ∀ {a} → HomV[ {!!} , {!!} ]

    -- If the abstract model had a notion of later, we could
    -- actually define dyn abstractly as an object `dyn` with an
    -- isomorphism between `dyn` and `nat + later (dyn ⇀ dyn)`
    -- We could also define the relation on dyn abstractly
    -- by defining the relations on sum types, function spaces,
    -- and later.



{-
 field
    -- a weak model of the natural numbers, but good enough for our syntax
    nat : cat .ob
    nat-fp : CatIso cat (𝟙 + nat) nat

    -- now the dyn stuff
    -- a model of dyn/casts
    dyn : cat .ob

    -- at this point we will model injection and projection as
    -- arbitrary morphisms
    inj : cat      [ nat + (dyn ⇀ dyn) , dyn ]
    prj : ClLinear [ dyn , nat + (dyn ⇀ dyn) ]

    -- and the error of course!
    -- err : 1 ⇀ A
    -- naturality says err ≡ T f ∘ err
    -- not sure if that's exactly right...
    err : ∀ {a} → cat [ 𝟙 , T a ]
  ℧ : ∀ {Γ a} → cat [ Γ , T a ]
  ℧ = err ∘⟨ cat ⟩ !t

  field
    ℧-homo : ∀ {Γ a b} → (f : Linear Γ [ a , b ])
           -- define this explicitly as a profunctor?
           -- f ∘⟨ Linear Γ ⟩ (F ℧) ≡ F ℧
           → bindP f ∘⟨ cat ⟩ ((cat .id ,p ℧)) ≡ ℧

-}


  -- field
  --   sq-filler-left-prop : ∀ {X Y} ->
  --     (c : HomH[ X , Y ]) (δY : HomV[ Y , Y ]) ->
  --     isProp (Σ[ pX ∈ ⟨ Ptb X ⟩ ] 2Cell c c (ptb-f pX) δY)

  --   sq-filler-right-prop : ∀ {X Y} ->
  --     (d : HomH[ X , Y ]) (δX : HomV[ X , X ]) ->
  --     isProp (Σ[ pY ∈ ⟨ Ptb Y ⟩ ] 2Cell d d δX (ptb-f pY))


