module Syntax.Perturbation where


-- The intensional syntax, which is quotiented by βη equivalence and
-- order equivalence but where casts take observable steps.

open import Cubical.Foundations.Prelude renaming (comp to compose)


open import Syntax.Types

open TyPrec
open CtxPrec

private
 variable
   Δ Γ Θ Z Δ' Γ' Θ' Z' : Ctx
   R S T U R' S' T' U' : Ty
   B B' C C' D D' : Γ ⊑ctx Γ'
   b b' c c' d d' : S ⊑ S'

data Pertᴱ : Ty -> Type
data Pertᴾ : Ty -> Type

data Pertᴱ where
  id : Pertᴱ S
  _⇀_ : ∀ {S T} -> Pertᴾ S -> Pertᴱ T -> Pertᴱ (S ⇀ T)
  PertD : Pertᴱ nat -> Pertᴱ (dyn ⇀ dyn) -> Pertᴱ dyn

data Pertᴾ where
  δPert : Pertᴾ S -> Pertᴾ S
  id : Pertᴾ S
  _⇀_ : ∀ {S T} -> Pertᴱ S -> Pertᴾ T -> Pertᴾ (S ⇀ T)
  PertD : Pertᴾ nat -> Pertᴾ (dyn ⇀ dyn) -> Pertᴾ dyn

-- Pushing and pulling perturbations across type precision

PushP : (c : S ⊑ T) -> Pertᴾ S -> Pertᴾ T
PushE : (c : S ⊑ T) -> Pertᴱ S -> Pertᴱ T

PushP c (δPert p) = δPert (PushP c p)
PushP c id = id
PushP (ci ⇀ co) (δi ⇀ δo) = PushE ci δi ⇀ PushP co δo
PushP (inj-arr c) (δi ⇀ δo) = PertD id (PushP c (δi ⇀ δo))
PushP dyn (PertD δn δf) = PertD δn δf

PushE c id = id
PushE (ci ⇀ co) (δi ⇀ δo) = PushP ci δi ⇀ PushE co δo
PushE (inj-arr c) (δi ⇀ δo) = PertD id (PushE c (δi ⇀ δo))
PushE dyn (PertD δn δf) = PertD δn δf


PullE : (c : S ⊑ T) -> Pertᴱ T -> Pertᴱ S
PullP : (c : S ⊑ T) -> Pertᴾ T -> Pertᴾ S

PullE c id = id
PullE (ci ⇀ co) (δi ⇀ δo) = PullP ci δi ⇀ PullE co δo
PullE dyn (PertD δn δf) = PertD δn δf
PullE inj-nat (PertD δn δf) = δn
PullE (inj-arr c) (PertD δn δf) = PullE c δf

PullP c (δPert p) = δPert (PullP c p)
PullP c id = id
PullP (ci ⇀ co) (δi ⇀ δo) = PullE ci δi ⇀ PullP co δo
PullP dyn (PertD δn δf) = PertD δn δf
PullP inj-nat (PertD δn δf) = δn
PullP (inj-arr c) (PertD δn δf) = PullP c δf



-- Perturbations from type precision derivations

-- Left (e and p)
δl-e-pert : S ⊑ T -> Pertᴱ S
δl-p-pert : S ⊑ T -> Pertᴾ S

δl-e-pert nat = id
δl-e-pert dyn = id
δl-e-pert (ci ⇀ co) = (δl-p-pert ci) ⇀ (δl-e-pert co)
δl-e-pert inj-nat = id
δl-e-pert (inj-arr c) = δl-e-pert c

δl-p-pert nat = id
δl-p-pert dyn = id
δl-p-pert (ci ⇀ co) = (δl-e-pert ci) ⇀ (δl-p-pert co)
δl-p-pert inj-nat = id
δl-p-pert (inj-arr c) = δPert (δl-p-pert c)

-- Right (e and p)
δr-e-pert : S ⊑ T -> Pertᴱ T
δr-p-pert : S ⊑ T -> Pertᴾ T

δr-e-pert nat = id
δr-e-pert dyn = id
δr-e-pert (ci ⇀ co) = (δr-p-pert ci) ⇀ (δr-e-pert co)
δr-e-pert inj-nat = id
δr-e-pert (inj-arr c) = PertD id (δr-e-pert c) -- correct?

δr-p-pert nat = id
δr-p-pert dyn = id
δr-p-pert (ci ⇀ co) = (δr-e-pert ci) ⇀ (δr-p-pert co)
δr-p-pert inj-nat = id -- correct?
δr-p-pert (inj-arr c) =  PertD id (δPert (δr-p-pert c))  -- wrong: δPert (PertD id (δr-p-pert c)) 
