module Syntax.IntensionalTerms.Results where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Data.List

open import Syntax.Types
open import Syntax.IntensionalTerms
open import Syntax.IntensionalTerms.Induction
import Syntax.Nbe as Nbe
-- open import Syntax.Normalization

open import Cubical.HITs.PropositionalTruncation

private
  variable
   Δ Γ Θ Z Δ' Γ' Θ' Z' : Ctx
   R S T U R' S' T' U' : Ty

   γ γ' γ'' : Subst Δ Γ
   δ δ' δ'' : Subst Θ Δ
   θ θ' θ'' : Subst Z Θ

   V V' V'' : Val Γ S
   M M' M'' N N' : Comp Γ S
   E E' E'' F F' : EvCtx Γ S T
   ℓ ℓ' ℓ'' ℓ''' ℓ'''' : Level


{-
test-1 : E [ γ ∘s δ ]e ≡ E [ γ ]e [ δ ]e
test-1 = {!!}

test-2 : (F ∘E E) [ M ]∙ ≡ F [ E [ M ]∙ ]∙
test-2 = proof-by-normalization {!!}
-}

up-comp : (c : R ⊑ S) (d : S ⊑ T) ->
  emb (c ∘⊑ d) ≡ ((emb d [ !s ,s var ]v) ∘V emb c)
dn-comp : (c : R ⊑ S) (d : S ⊑ T) ->
  proj (c ∘⊑ d) ≡ (proj c ∘E proj d)

up-comp nat nat =
  var
    ≡⟨ sym varβ ⟩
  (var [ ids ,s var ]v)
    ≡⟨ (λ i -> (varβ {δ = !s} {V = var}) (~ i) [ ids ,s var ]v) ⟩
  (var [ !s ,s var ]v [ ids ,s var ]v) ∎
up-comp nat inj-nat = {!!}
  where
    lem : injectN ≡ ((injectN [ {!!} ]v) ∘V var)
    lem = {!!}
up-comp dyn dyn = {!!}
up-comp (ci ⇀ co) (ei ⇀ eo) =
  lda (((proj (trans-⊑ ci ei) [ !s ]e) [ ret' var ]∙) >>
      ((app [ drop2nd ]c) >>
      ((vToE (emb (trans-⊑ co eo)) [ !s ]e) [ ret' var ]∙)))
      
  ≡⟨ (λ i -> lda (((dn-comp ci ei i [ !s ]e) [ ret' var ]∙) >>
      ((app [ drop2nd ]c) >>
      ((vToE (up-comp co eo i) [ !s ]e) [ ret' var ]∙)))) ⟩
  
  lda ((((proj ci ∘E proj ei) [ !s ]e) [ ret' var ]∙) >>
      ((app [ drop2nd ]c) >>
      ((vToE ((emb eo [ !s ,s var ]v) ∘V emb co ) [ !s ]e) [ ret' var ]∙)))

  ≡⟨ congS lda ( {!!}) ⟩
  
  lda (((((proj ci [ !s ]e) ∘E (proj ei [ !s ]e))) [ ret' var ]∙) >>
      ((app [ drop2nd ]c) >>
      ((vToE ((emb eo [ !s ,s var ]v) ∘V emb co ) [ !s ]e) [ ret' var ]∙)))

  ≡⟨ congS lda ( {!!}) ⟩

{-
  lda (((((proj ei [ !s ]e))) [ ret' var ]∙) >>
      (((proj ci [ !s ]e) [ ret' var ]∙) >> 
      ((app [ {!!} ]c) >>
      (((vToE (emb co ) [ !s ]e) [ ret' var ]∙) >>
      ((vToE (emb eo) [ !s ]e) [ ret' var ]∙)))))

  ≡⟨ cong lda {!!} ⟩
-}

  lda (M1 [ (!s ∘s wk ,s (lda M2 [ wk ]v)) ,s var ]c)
      
  ≡⟨ congS lda (cong₂ _[_]c refl (cong₂ _,s_ (sym ,s-nat) refl)) ⟩
  
  lda (M1 [ ((!s ,s lda M2) ∘s wk) ,s var ]c)
      
  ≡⟨ sym (lda-nat _ _) ⟩
  
  ((lda M1) [ !s ,s lda M2 ]v)
          
  ≡⟨ cong₂ _[_]v refl (sym lem) ⟩
  
  ((lda M1) [ (!s ,s var) ∘s (ids ,s lda M2) ]v)
          
  ≡⟨ substAssoc ⟩
  
  ((lda M1) [ !s ,s var ]v) ∘V lda M2 ∎
  where
   -- bind-nat : (bind M) [ γ ]e ≡ bind (M [ γ ∘s wk ,s var ]c)

    M1 = ((proj ei [ !s ]e) [ ret' var ]∙) >>
           ((app [ drop2nd ]c) >> ((vToE (emb eo) [ !s ]e) [ ret' var ]∙))
    M2 = ((proj ci [ !s ]e) [ ret' var ]∙) >>
           ((app [ drop2nd ]c) >> ((vToE (emb co) [ !s ]e) [ ret' var ]∙))
           
    P = lda (M1 [ (!s ∘s wk ,s (lda M2 [ wk ]v)) ,s var ]c)

    eq : P ≡ lda (((proj ei [ !s ]e) [ ret' var ]∙) >>
                 (((app [ drop2nd ]c) >> ((vToE (emb eo) [ !s ]e) [ ret' var ]∙))
                 [ (!s ∘s wk ,s (lda M2 [ wk ]v) ,s var) ∘s wk ,s var ]c))
    eq = congS lda
      (substPlugDist
       ∙ (cong₂ _[_]∙ bind-nat (substPlugDist
                                  ∙ cong₂ _[_]∙
                                        (sym substAssoc ∙ cong₂ _[_]e refl []η)
                                        (ret'-nat ∙ congS ret' varβ))))


    lem : ∀ {V : Val Γ S} -> (!s ,s var) ∘s (ids ,s V) ≡ (!s ,s V)
    lem = ,s-nat ∙ (cong₂ _,s_ []η varβ)
    -- ,s-nat : (γ ,s V) ∘s δ ≡ ((γ ∘s δ) ,s (V [ δ ]v))
    -- varβ : var [ δ ,s V ]v ≡ V


up-comp (ci ⇀ co) (inj-arr (ei ⇀ eo)) = {!!}
up-comp inj-nat dyn = {!!}
up-comp (inj-arr c) dyn = {!!}



dn-comp nat nat = sym ∘IdL
dn-comp nat inj-nat = sym ∘IdL
dn-comp dyn dyn = sym ∘IdL
dn-comp (ci ⇀ co) (ei ⇀ eo) = {!!}
dn-comp (ci ⇀ co) (inj-arr (ei ⇀ eo)) = {!!}
dn-comp inj-nat dyn = sym ∘IdR
dn-comp (inj-arr c) dyn = sym ∘IdR



