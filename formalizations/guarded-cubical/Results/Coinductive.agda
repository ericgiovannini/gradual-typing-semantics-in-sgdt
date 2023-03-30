{-# OPTIONS --cubical --rewriting --guarded #-}
{-# OPTIONS --guardedness #-}


open import Common.Later

module Results.Coinductive where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sum
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Data.Sigma
open import Cubical.Data.Nat renaming (ℕ to Nat) hiding (_·_ ; _^_)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Data.Empty

open import Semantics.Predomains
open import Semantics.StrongBisimulation
open import Semantics.Lift

open import Results.IntensionalAdequacy


private
  variable
    l : Level
    X : Type l


{-
-- If there was an answer produced at each step, we could parameterize by another type A,
-- and make running have type A -> State Res
mutual
  data State (Res : Type) : Type where
    done : Res -> State Res
    running : Machine Res -> State Res

  record Machine (B : Type) : Type where
    coinductive
    field
      view : State B

open Machine

Ω : {B : Type} -> Machine B
-- Ω .view = running (Ω .view)
view Ω = running Ω


isom : {X : Type} -> Iso (L℧F X) (Machine (X ⊎ ⊤))
isom {X} = iso {!!} {!!} {!!} {!!}
   where
     f : (L℧F X) -> (Machine (X ⊎ ⊤))
     view (f l) with (l k0)
     ... | η x = done (inl x)
     ... | ℧   = done (inr tt)
     ... | θ lx~ = running (f l)

     inv : Machine (X ⊎ ⊤) -> L℧F X
     inv m with (view m)
     ... | done (inl x) = ηF x
     ... | done (inr tt) = ℧F
     ... | running m' = λ k -> θ λ t → inv m'' {!!}
      where
       m'' : Machine (X ⊎ ⊤)
       view m'' = {!!}
-}


{-
    inv : Machine (X ⊎ ⊤) -> L℧F X
    inv m with (view m)
    ... | done (inl x) = λ k -> η x
    ... | done (inr x) = λ k -> ℧
    ... | running = λ k -> θ λ t → {!!}
      
-}





{-
-- A until B == B + A × (A until B)
record Machine (B : Type) : Type where
  coinductive
  field
    -- view : State B
    view : B ⊎ (Unit × Machine B)

open Machine

Ω : {B : Type} -> Machine B
Ω .view = inr (tt , Ω)
-- equivalently:
--view Ω = inr (tt , Ω)
-- But this doesn't work:
-- Ω = record { view = inr (tt , Ω) } -- fails termination checking



module _ {X : Type} (H-irrel : clock-irrel X) where

  ∀-to-machine' : (L℧F X) -> Machine (X ⊎ ⊤)
  view (∀-to-machine' l) with (Iso.fun (L℧F-iso H-irrel) l)
  ... | inl (inl x) = inl (inl x)
  ... | inl (inr _) = inl (inr tt)
  ... | inr l' = inr (tt , (∀-to-machine' l'))


-}

record Machine (Res : Type) : Type

data State (Res : Type) : Type where
  result : Res -> State Res
  error : State Res
  running : Machine Res -> State Res

record Machine Res where
  coinductive
  field view : State Res

open Machine public


module _ {X : Type} (H-irrel : clock-irrel X) where

   ∀-to-machine : (L℧F X) -> Machine X
   view (∀-to-machine l) with (Iso.fun (L℧F-iso H-irrel) l)
   ... | inl (inl x) = result x
   ... | inl (inr _) = error
   ... | inr l' = running (∀-to-machine l')


   -- We can't use normal recursion, because the argument is coinductive and so may be infinite.
   {-
   machine-to-∀ : Machine X -> L℧F X   
   machine-to-∀ m with (view m)
   ... | result x = ηF x
   ... | error = ℧F
   ... | running m' = λ k -> θ λ t → machine-to-∀ m' k
   -}


   {-
   machine-to-∀' : (k : Clock) -> (Machine X) -> L℧ k X
   machine-to-∀' k m = fix f
     where
       f : ▹ k , L℧ k X -> L℧ k X
       f lx~ with (view m)
       ... | result x = η x
       ... | error = ℧
       ... | running m' = θ (λ t → lx~ t)
   -}


   machine-to-∀'' : (k : Clock) -> ▹ k , (Machine X -> L℧ k X) -> (Machine X -> L℧ k X)
   machine-to-∀'' k rec m with (view m)
   ... | result x = η x
   ... | error = ℧
   ... | running m' = θ (λ t → rec t m')

   -- Instead, we can define it by a guarded fixpoint.
   machine-to-∀' : (k : Clock) -> (Machine X) -> L℧ k X
   machine-to-∀' k = fix (machine-to-∀'' k)
      
   machine-to-∀ : Machine X -> L℧F X
   machine-to-∀ m k = fix (machine-to-∀'' k) m

   retr : retract ∀-to-machine machine-to-∀
   retr l with (Iso.fun (L℧F-iso H-irrel) l)
   ... | inl (inl x) = clock-ext (λ k → {!!})
   ... | inl (inr _) = {!!}
   ... | inr x = {!!}


  -- Showing these are inverses requires a notion of equality for Machines,
  -- which is the bisimilarity relation defined below.



-- Bisimilarity relation on Machines.
module Bisim (X : Predomain) (H-irrel : clock-irrel ⟨ X ⟩) where


  -- Mutually define coinductive bisimilarity of machines
  -- along with the relation on states of a machine.
 

  record _≋_ (m m' : Machine ⟨ X ⟩) : Type

  _≋''_ : State ⟨ X ⟩ -> State ⟨ X ⟩ -> Type
  result x ≋'' result x' = rel X x x'
  error ≋'' error = ⊤
  running m ≋'' running m' = m ≋ m' -- using the coinductive bisimilarity on machines
  _ ≋'' _ = ⊥


  data _≋'_ (s s' : State ⟨ X ⟩) : Type

  record _≋_ m m' where
    coinductive
    field prove : view m ≋' view m'

  data _≋'_ s s' where
    con : s ≋'' s' -> s ≋' s'


  open _≋_ public


  

  
    
  



{-
∀-to-machine : (L℧F X) -> (Machine (X ⊎ ⊤))
view (∀-to-machine l) with (l k0)
... | η x   = inl (inl x)  -- done (inl x) }
... | ℧     = inl (inr tt) -- done (inr tt) }
... | θ lx~ = inr (tt , (∀-to-machine l)) -- running }

{-# TERMINATING #-}
machine-to-∀ : Machine (X ⊎ ⊤) -> L℧F X
machine-to-∀ m with (view m)
... | inl (inl x) = λ k -> η x
... | inl (inr tt) = λ k -> ℧
... | inr (tt , m') = λ k -> θ λ t → machine-to-∀ m' k

isom : {X : Type} -> Iso (L℧F X) (Machine (X ⊎ ⊤))
isom {X} = iso ∀-to-machine machine-to-∀ sec retr
  where
    sec : section ∀-to-machine machine-to-∀
    sec m with (view m)
    ... | inl (inl x) = {!!}
    ... | inl (inr tt) = {!!}
    ... | inr (_ , m') = {!!}

    retr : retract ∀-to-machine machine-to-∀
    retr l with (l k0) in eq
    ... | η x = clock-ext {!!}
    ... | ℧ = clock-ext {!!}
    ... | θ l~ = {!!}
   
-}
