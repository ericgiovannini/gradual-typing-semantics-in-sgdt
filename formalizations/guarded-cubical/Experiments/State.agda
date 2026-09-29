{-# OPTIONS --rewriting --guarded #-}
{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --lossy-unification #-}

open import Common.Later

module Experiments.State (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma

open import Semantics.Concrete.GuardedLiftError k


private
  variable
    ℓ ℓ' : Level

private
  ▹_ : Type ℓ → Type ℓ
  ▹_ A = ▹_,_ k A



module _ (S : Type ℓ) where

  data Free (A : Type ℓ') : Type (ℓ-max ℓ ℓ') where
    ret : A → Free A
    err : Free A
    θ   : ▹ (Free A) → Free A
    get : (S → ▹ Free A) → Free A
    put : (S × (▹ Free A)) → Free A


  StateDelay : Type ℓ' → Type (ℓ-max ℓ ℓ')
  StateDelay A = (S → L℧ (S × A))

  Theta : {A : Type ℓ'} → ▹ (StateDelay A) → StateDelay A
  Theta x~ s = θ (λ t → x~ t s)

  -- Showing that StateDelay A implements the operations Get and Put
  Get : {A : Type ℓ'} → (S → StateDelay A) → StateDelay A
  Get f s = f s s

  Get' : {A : Type ℓ'} → (S → ▹ StateDelay A) → StateDelay A
  Get' f s = θ (λ t → f s t s)

  Put : {A : Type ℓ'} → (S × StateDelay A) → StateDelay A
  Put (s , d) s' = d s

  Put' : {A : Type ℓ'} → (S × ▹ StateDelay A) → StateDelay A
  Put' (s , d~) s' = θ (λ t → d~ t s)
  

  Free→L℧ : (A : Type ℓ') → Free A → StateDelay A
  Free→L℧ A = fix aux
    where
      aux : ▹ (Free A → StateDelay A) → (Free A → StateDelay A)
      aux rec (ret x) s = η (s , x)
      aux rec err _ = ℧
      aux rec (θ x~) s = θ (λ t → rec t (x~ t) s)
      
      aux rec (get f) = Get (g ∘ f)
        -- Get' ((λ x~ → rec ⊛ x~) ∘ f) 
        where
          g : ▹ (Free A) → StateDelay A
          g x~ = Theta (rec ⊛ x~)
          
      aux rec (put (s , x~)) = Put (s , Theta (rec ⊛ x~))
