{-# OPTIONS --rewriting --guarded #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}

module Semantics.GlobalWeakBisimilarity where


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport -- pathToIso
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.Nat hiding (_^_ ; _+_)
import Cubical.Data.Nat as Nat
open import Cubical.Data.Nat.Order hiding (eq)
open import Cubical.Data.Sum
open import Cubical.Data.Unit renaming (Unit to ⊤ ; Unit* to ⊤*)
open import Cubical.Data.Empty as ⊥

open import Cubical.HITs.PropositionalTruncation renaming (map to PTmap)

open import Cubical.Functions.FunExtEquiv
open import Cubical.Functions.Embedding


open import Common.Common
open import Common.Later
open import Common.ClockProperties

open import Semantics.Concrete.WeakBisimilarity
open import Semantics.Concrete.GuardedLift
open import Semantics.BigStepFunction
open import Semantics.GlobalLift


private
  variable
    ℓ ℓ' ℓR : Level


module Adequacy (X : Type ℓ) (R : X → X → Type ℓR)
         (isSetX : isSet X)
         (X-clk-irrel : clock-irrel X)
         (R-prop-valued : ∀ x y → isProp (R x y))
         (R-clk-irrel : ∀ x y → clock-irrel (R x y)) where


  -- Some convenience definitions and syntax.
  ≈S : (k : Clock) → L k X → L k X → Type (ℓ-max ℓ ℓR)
  ≈S k = _≈_ -- _≈_ k X R
    where open BisimSum k X R

  syntax ≈S k x y = x ≈[ k ] y

  δL = δ


  _↓ : {k : Clock} → L k X → Type ℓ
  _↓  {k = k} l = Σ[ n ∈ ℕ ] Σ[ x ∈ X ] (l ≡ ((δ k) ^ n) (η x))

  pattern in1 x = inl x
  pattern in2 x = inr (inl x)
  pattern in3 x = inr (inr (inl x))
  pattern in4 x = inr (inr (inr x))


  _+_ : {ℓ ℓ' : Level} → Type ℓ → Type ℓ' → Type (ℓ-max ℓ ℓ')
  _+_ = _⊎_
  infixr 20 _+_

  

  -- Definition of global weak bisimilarity.
  _≈g_ : L^gl X → L^gl X → Type (ℓ-max ℓ ℓR)
  l1 ≈g l2 = ∀ (k : Clock) → l1 k ≈[ k ] l2 k


  -- The four cases of the sum type for *clocked* weak bisimilarity.
  module ClockedCases {k : Clock} (l1 l2 : L k X) where
  
    ret-ret : Type (ℓ-max ℓ ℓR)
    ret-ret =
      Σ[ x ∈ X ] Σ[ y ∈ X ] (l1 ≡ η x) × (l2 ≡ η y) × (R x y)

    ret-theta : Type (ℓ-max ℓ ℓR)
    ret-theta  =
      Σ[ x ∈ X ] (l1 ≡ η x) ×
        ∥ (Σ[ n ∈ ℕ ] Σ[ y ∈ X ] (l2 ≡ ((δL k) ^ n) (η y)) × R x y) ∥₁

    theta-ret : Type (ℓ-max ℓ ℓR)
    theta-ret =
      Σ[ y ∈ X ] (l2 ≡ η y) ×
        ∥ (Σ[ n ∈ ℕ ] Σ[ x ∈ X ] (l1 ≡ ((δL k) ^ n) (η x)) × R x y) ∥₁
    -- ret-theta l2 l1

    theta-theta : Type (ℓ-max ℓ ℓR)
    theta-theta =
      Σ[ l1~ ∈ ▹ k , L k X ] Σ[ l2~ ∈ ▹ k , L k X ]
        (l1 ≡ θ l1~) × (l2 ≡ θ l2~) × (▸ (λ t → l1~ t ≈[ k ] l2~ t))


  -- The four cases of the sum type for *global* weak bisimilarity.
  module GlobalCases (lg1 : L^gl X) (lg2 : L^gl X) where
  
    ret-ret-g : Type (ℓ-max ℓ ℓR)
    ret-ret-g = Σ[ x ∈ X ] Σ[ y ∈ X ]
          (lg1 ≡ ηL^gl x) × (lg2 ≡ ηL^gl y) × R x y

    ret-theta-g : Type (ℓ-max ℓ ℓR)
    ret-theta-g = Σ[ x ∈ X ] (lg1 ≡ ηL^gl x) × ( Σ[ n ∈ ℕ ] Σ[ y ∈ X ]
          (lg2 ≡ (δL^gl ^ n) (ηL^gl y)) × R x y )

    theta-ret-g : Type (ℓ-max ℓ ℓR)
    theta-ret-g = Σ[ y ∈ X ] (lg2 ≡ ηL^gl y) × ( Σ[ n ∈ ℕ ] Σ[ x ∈ X ]
           (lg1 ≡ (δL^gl ^ n) (ηL^gl x)) × R x y )

    theta-theta-g : Type (ℓ-max ℓ ℓR)
    theta-theta-g = Σ[ lg1' ∈ L^gl X ] Σ[ lg2' ∈ L^gl X ]
          (lg1 ≡ δL^gl lg1') × (lg2 ≡ δL^gl lg2') × (lg1' ≈g lg2')
  

  -- The "unfolding" of the definition of global weak bisimilarity.
  ≈g-unfolded : L^gl X → L^gl X → Type (ℓ-max ℓ ℓR)
  ≈g-unfolded lg1 lg2 = ret-ret-g + ret-theta-g + theta-ret-g + theta-theta-g
    where open GlobalCases lg1 lg2


  -- The goal of this module is to prove a lemma stating that the cases
  -- of *global* bisimilarity involving iterated delays are Props, and
  -- hence we can remove the propositional truncation in those cases.
  module Prop where
    open GlobalCases

    δL^gl-inj-cor : ∀ n m (x y : X) ->
      (δL^gl ^ n) (ηL^gl x) ≡ (δL^gl ^ m) (ηL^gl y) ->
      (n ≡ m) × (x ≡ y)
    δL^gl-inj-cor zero zero x y eq = refl , ηL^gl-inj x y eq k0 -- is that ok?
    δL^gl-inj-cor zero (suc m) x y eq = ⊥.rec (ηL^gl≠δL^gl _ _ eq)
    δL^gl-inj-cor (suc n) zero x y eq = ⊥.rec (ηL^gl≠δL^gl _ _ (sym eq))
    δL^gl-inj-cor (suc n) (suc m) x y eq = (cong suc (IH .fst)) , (IH .snd)
      where IH = δL^gl-inj-cor n m x y (δL^gl-inj _ _ eq)
     

    is-prop-x : ∀ (x y : X) (lg : L^gl X) →
      isProp (Σ[ n ∈ ℕ ] Σ[ x ∈ X ] (lg ≡ (δL^gl ^ n) (ηL^gl x)) × R x y)
    is-prop-x x y lg (n1 , x1 , eq1 , rel1)  (n2 , x2 , eq2 , rel2) =
      ΣPathP (n1≡n2 , ΣPathP (x1≡x2 , ΣPathPProp {B = λ i _ → R (x1≡x2 i) y}
        (λ _ → R-prop-valued x2 y)
        (isProp→PathP (λ i → isSetL^gl isSetX lg _) eq1 eq2)))
      -- (λ i j → isSetL^gl isSetX lg ((δL^gl ^ (n1≡n2 i)) (ηL^gl (x1≡x2 i))) ({!eq1 i!}) {!!} i j)
      where
        eq : _
        eq = sym eq1 ∙ eq2
        
        n1≡n2 : n1 ≡ n2
        n1≡n2 = δL^gl-inj-cor n1 n2 x1 x2 eq .fst

        x1≡x2 : x1 ≡ x2
        x1≡x2 = δL^gl-inj-cor n1 n2 x1 x2 eq .snd

    is-prop-y : ∀ (x y : X) (lg : L^gl X) →
      isProp (Σ[ n ∈ ℕ ] Σ[ y ∈ X ] (lg ≡ (δL^gl ^ n) (ηL^gl y)) × R x y)
    is-prop-y x y lg (n1 , y1 , eq1 , rel1)  (n2 , y2 , eq2 , rel2) =
      ΣPathP (n1≡n2 , ΣPathP (y1≡y2 , ΣPathPProp {B = λ i _ → R x (y1≡y2 i)}
        (λ _ → R-prop-valued x y2)
        (isProp→PathP (λ _ → isSetL^gl isSetX lg _) eq1 eq2)))
      where
        eq : _
        eq = sym eq1 ∙ eq2
        
        n1≡n2 : n1 ≡ n2
        n1≡n2 = δL^gl-inj-cor n1 n2 y1 y2 eq .fst

        y1≡y2 : y1 ≡ y2
        y1≡y2 = δL^gl-inj-cor n1 n2 y1 y2 eq .snd
        
    

  ------------------------------------------------------------------------------
  
  -- Lemmas used in the construction of the global bisimilarity isomorphism:
  open GlobalCases
  open ClockedCases
  
  lem1 : ∀ lg1 lg2 →
    Iso (∀ (k : Clock) → ret-ret (lg1 k) (lg2 k)) (ret-ret-g lg1 lg2)
  lem1 lg1 lg2 =
    _ Iso⟨ Iso-∀clock-Σ X-clk-irrel ⟩
    _ Iso⟨ Σ-cong-iso-snd (λ x → Iso-∀clock-Σ X-clk-irrel) ⟩
    _ Iso⟨ Σ-cong-iso-snd (λ x → Σ-cong-iso-snd (λ y → compIso Iso-∀clock-× (prodIso idIso Iso-∀clock-×))) ⟩
    _ Iso⟨ Σ-cong-iso-snd (λ x → Σ-cong-iso-snd (λ y → prodIso funExtIso (prodIso funExtIso (Iso-∀kA-A (R-clk-irrel x y))))) ⟩
    ret-ret-g lg1 lg2 ∎Iso

  lem1' : ∀ lg1 lg2 →
    (∀ (k : Clock) → ret-ret (lg1 k) (lg2 k)) → (ret-ret-g lg1 lg2)
  lem1' lg1 lg2 f =
    (f k0 .fst) ,
    (f k0 .snd .fst) ,
    funExt (λ k → f k .snd .snd .fst ∙ congS η (X-clk-irrel (λ k' → f k' .fst) k k0)) ,
    -- (funExt (λ k → transport {!!} (f k0 .snd .snd .fst))) ,
    funExt (λ k → f k .snd .snd .snd .fst ∙ congS η (X-clk-irrel (λ k' → f k' .snd .fst) k k0)) ,
    f k0 .snd .snd .snd .snd
    

  propTruncIso : ∀ {ℓ ℓ' : Level} → {A : Type ℓ} {B : Type ℓ'} →
    Iso A B → Iso ∥ A ∥₁ ∥ B ∥₁
  propTruncIso isom =
    isProp→Iso isPropPropTrunc isPropPropTrunc (PTmap (Iso.fun isom)) (PTmap (Iso.inv isom))

  δ^gl-iterated-η^gl : (n : ℕ) (x : X) → (δL^gl ^ n) (ηL^gl x) ≡ (λ k → (δL k ^ n) (η x))
  δ^gl-iterated-η^gl zero x = refl
  δ^gl-iterated-η^gl (suc n) x = cong δL^gl (δ^gl-iterated-η^gl n x)
 

  lem2 : ∀ lg1 lg2 →
    Iso (∀ (k : Clock) → ret-theta (lg1 k) (lg2 k)) (ret-theta-g lg1 lg2)
  lem2 lg1 lg2 =
    _
      Iso⟨ Iso-∀clock-Σ X-clk-irrel ⟩
    _
      Iso⟨ Σ-cong-iso-snd (λ x → Iso-∀clock-×) ⟩
    _
      Iso⟨ Σ-cong-iso-snd (λ x → prodIso idIso ∀k-propTrunc) ⟩
    _
      Iso⟨ Σ-cong-iso-snd (λ x → prodIso funExtIso (propTruncIso
        (compIso (Iso-∀clock-Σ nat-clock-irrel)
          (compIso (Σ-cong-iso-snd (λ n → Iso-∀clock-Σ X-clk-irrel))
            (compIso (Σ-cong-iso-snd (λ n → Σ-cong-iso-snd (λ y → Iso-∀clock-×)))
              (compIso (Σ-cong-iso-snd (λ n → Σ-cong-iso-snd (λ y → prodIso funExtIso (Iso-∀kA-A (R-clk-irrel x y)))))
                (Σ-cong-iso-snd (λ n → Σ-cong-iso-snd (λ y → prodIso (Eq-Iso (sym (cong (λ p → _ ≡ p) (δ^gl-iterated-η^gl n y)))) idIso))))))))) ⟩
    _
      Iso⟨ Σ-cong-iso-snd (λ x → prodIso idIso (Eq-Iso (propTruncIdempotent (Prop.is-prop-y x x lg2)))) ⟩
    ret-theta-g lg1 lg2
      ∎Iso

  lem3 : ∀ lg1 lg2 →
    Iso (∀ (k : Clock) → theta-ret (lg1 k) (lg2 k)) (theta-ret-g lg1 lg2)
  lem3 lg1 lg2 =
    ((k : Clock) → theta-ret (lg1 k) (lg2 k))
      Iso⟨ Iso-∀clock-Σ X-clk-irrel ⟩
    _
      Iso⟨ Σ-cong-iso-snd (λ y → Iso-∀clock-×) ⟩
    _
      Iso⟨ Σ-cong-iso-snd (λ y → prodIso idIso ∀k-propTrunc) ⟩
    _
      Iso⟨ Σ-cong-iso-snd (λ y → prodIso funExtIso (propTruncIso
        (compIso (Iso-∀clock-Σ nat-clock-irrel)
          (compIso (Σ-cong-iso-snd (λ n → Iso-∀clock-Σ X-clk-irrel))
            (compIso (Σ-cong-iso-snd (λ n → Σ-cong-iso-snd (λ x → Iso-∀clock-×)))
              (compIso (Σ-cong-iso-snd (λ n → Σ-cong-iso-snd (λ x → prodIso funExtIso (Iso-∀kA-A (R-clk-irrel x y)))))
                (Σ-cong-iso-snd (λ n → Σ-cong-iso-snd (λ x → prodIso (Eq-Iso (sym (cong (λ p → _ ≡ p) (δ^gl-iterated-η^gl n x)))) idIso))))))))) ⟩
    _
      Iso⟨ Σ-cong-iso-snd (λ y → prodIso idIso (Eq-Iso (propTruncIdempotent (Prop.is-prop-x y y lg1)))) ⟩
    _
      ∎Iso


  -- Note:
  -- force-iso: Iso (∀ k → (▹ k , A k)) (∀ k → A k)
  -- We use Σ-cong-iso-fst' (defined in Common.agda) becasuse this
  -- definition uses Iso.inv rather than Iso.fun, and in this case
  -- we want to use the Iso.inv of force-iso (which involves next).
  lem4 : ∀ lg1 lg2 →
    Iso (∀ (k : Clock) → theta-theta (lg1 k) (lg2 k)) (theta-theta-g lg1 lg2)
  lem4 lg1 lg2 =
    _ Iso⟨ Σ-Π-Iso ⟩
    _ Iso⟨ Σ-cong-iso-snd (λ l~g1 → Σ-Π-Iso) ⟩
    M Iso⟨ compIso (Σ-cong-iso-fst' force-iso) (Σ-cong-iso-snd (λ f → Σ-cong-iso-fst' force-iso)) ⟩
    N Iso⟨ Σ-cong-iso-snd (λ _ → Σ-cong-iso-snd (λ _ → compIso Iso-∀clock-× (prodIso idIso Iso-∀clock-×))) ⟩
    P Iso⟨ Σ-cong-iso-snd (λ _ → Σ-cong-iso-snd (λ _ → prodIso funExtIso (prodIso funExtIso force-iso))) ⟩
    theta-theta-g lg1 lg2 ∎Iso
      where
        M = Σ[ f ∈ ((k : Clock) → ▹ k , L k X) ]
            Σ[ g ∈ ((k : Clock) → ▹ k , L k X) ]
              ((k : Clock) →
               (lg1 k ≡ θ (f k)) ×
               (lg2 k ≡ θ (g k)) × (▸ (λ t → ≈S k (f k t) (g k t))))

        N = Σ[ f ∈ ((k : Clock) → L k X) ]
            Σ[ g ∈ ((k : Clock) → L k X) ]
              ((k : Clock) →
               (lg1 k ≡ θ (next (f k))) ×
               (lg2 k ≡ θ (next (g k))) × (▹ k , ≈S k (f k) (g k)))

        P = Σ[ f ∈ ((k : Clock) → L k X) ]
            Σ[ g ∈ ((k : Clock) → L k X) ]
              (((k : Clock) → (lg1 k ≡ θ (next (f k)))) ×
               ((k : Clock) → (lg2 k ≡ θ (next (g k)))) ×
               ((k : Clock) → (▹ k , ≈S k (f k) (g k))))


  -- The unfolding isomorphism satisfied by global bisimilarity.
  -- The construction of this iso uses the above lemmas.
  ≈g-iso : (lg1 lg2 : L^gl X) →
    Iso (lg1 ≈g lg2) (≈g-unfolded lg1 lg2)
  ≈g-iso lg1 lg2 =
  
    ((k : Clock) → lg1 k ≈[ k ] lg2 k)
    
      Iso⟨ pathToIso (λ i → ∀ k → BisimSum.unfold-≈ k X R i (lg1 k) (lg2 k) )⟩

    (∀ k → ((ret-ret     (lg1 k) (lg2 k))
          + (ret-theta   (lg1 k) (lg2 k))
          + (theta-ret   (lg1 k) (lg2 k))
          + (theta-theta (lg1 k) (lg2 k))))

      -- distribute the clock quantifier
      Iso⟨ compIso Iso-Π-⊎-clk
            (⊎Iso idIso (compIso Iso-Π-⊎-clk
              (⊎Iso idIso Iso-Π-⊎-clk))) ⟩ 
      
      (∀ k → ret-ret     (lg1 k) (lg2 k))
    + (∀ k → ret-theta   (lg1 k) (lg2 k))
    + (∀ k → theta-ret   (lg1 k) (lg2 k))
    + (∀ k → theta-theta (lg1 k) (lg2 k))

      -- apply the four lemmas
      Iso⟨ ⊎Iso (lem1 lg1 lg2) (⊎Iso (lem2 lg1 lg2) (⊎Iso (lem3 lg1 lg2) (lem4 lg1 lg2))) ⟩ 
      
    ≈g-unfolded lg1 lg2 ∎Iso


  -- The unfolding function, given by the above isomorphism.
  unfold-≈g : {lg1 lg2 : L^gl X} →
    (lg1 ≈g lg2) → (≈g-unfolded lg1 lg2)
  unfold-≈g {lg1 = lg1} {lg2 = lg2} = Iso.fun (≈g-iso lg1 lg2)



  -- Adequacy proofs
 
  open BigStepLemmas X-clk-irrel
  open PartialFunctions
  open BigStep X X-clk-irrel

  -- The big-step term semantics.
  -- ⟦_⟧ : L^gl X → Fun
  -- ⟦ lg ⟧ = toFun X-clk-irrel lg


  -- (Step-indexed) weak bisimilarity for the Fun type.
  bisimFun : Fun → Fun → ℕ → Type (ℓ-max ℓ ℓR)
  syntax bisimFun f g n = n ⊨ f ≈ g

  one-terminates-at-n : _ → _ → _ → _
  one-terminates-at-n n f g =
     -- (Σ[ x ∈ X ] Σ[ y ∈ X ] (f ↓fun[ 0 ] x) × (g ↓fun[ 0 ] y) × R x y)
     (Σ[ x ∈ X ] Σ[ y ∈ X ] Σ[ m ∈ ℕ ] (f ↓fun[ n ] x) × (g ↓fun[ m ] y) × R x y)
   + (Σ[ x ∈ X ] Σ[ y ∈ X ] Σ[ m ∈ ℕ ] (f ↓fun[ m ] x) × (g ↓fun[ n ] y) × R x y)

  zero  ⊨ f ≈ g = one-terminates-at-n zero f g + (f ↑fun[ 0 ] × g ↑fun[ 0 ])
  suc n ⊨ f ≈ g = one-terminates-at-n zero f g + (f ↑fun[ 0 ] × g ↑fun[ 0 ] × (n ⊨ (f ∘ suc) ≈ (g ∘ suc)))

  -- n ⊨ f ≈ g = one-terminates-at-n zero f g + ((n ≡ zero) + (n ≡ suc n' × n' ⊨ f ≈ g))


  ↓-unique-downward : (f : Fun {ℓ = ℓ} {X = X}) → ↓-unique f → ↓-unique (f ∘ suc)
  ↓-unique-downward f Hf m n x y fs↓x fs↓y = cong predℕ (Hf (suc m) (suc n) x y fs↓x fs↓y .fst) , Hf (suc m) (suc n) x y fs↓x fs↓y .snd

  -- A more intuitive definition, but harder to establish.
  _≈fun[_]_ : Fun → ℕ → Fun → Type (ℓ-max ℓ ℓR)
  f ≈fun[ n ] g = ∀ (m : ℕ) → (m ≤ n)  →
    (∀ (x : X) → f m ≡ inl x → Σ[ j ∈ ℕ ] Σ[ y ∈ X ] (g j ≡ inl y) × R x y) ×
    (∀ (y : X) → g m ≡ inl y → Σ[ j ∈ ℕ ] Σ[ x ∈ X ] (f j ≡ inl x) × R x y)


  -- The first definition implies the second, provided that the
  -- functions satisfy the (strong) uniqueness property.
  adequacy-pt2 : (f g : Fun) (Hf : ↓-unique f) (Hg : ↓-unique g) →
    (n : ℕ) → n ⊨ f ≈ g → f ≈fun[ n ] g

  -- case n = 0, f terminates in 0 steps, and g terminates in m steps
  adequacy-pt2 f g Hf Hg zero (inl (inl (x , y , m , f↓x , g↓y , xRy))) l l≤zero = aux
    where
      aux : _ × _
      aux .fst x' f↓x' = m , y , g↓y , transport (cong₂ R x≡x' refl) xRy
        where
          x≡x' : x ≡ x'
          x≡x' = isEmbedding→Inj isEmbedding-inl x x'
            (sym f↓x ∙ (subst (f ↓fun[_] x') (≤0→≡0 l≤zero) f↓x'))  -- (subst (λ j → f ↓fun[ j ] x') l≡zero f↓x')

      aux .snd y' g↓y' = 0 , x , f↓x , transport (cong₂ R refl y≡y') xRy
        where
          y≡y' : y ≡ y'
          y≡y' = Hg m l y y' g↓y g↓y' .snd

  -- case n = 0, f terminates in m steps, and g terminates in 0 steps
  adequacy-pt2 f g Hf Hg zero (inl (inr (x , y , m , f↓x , g↓y , xRy))) l l≤zero = aux
    where
      aux : _ × _
      aux .fst x' f↓x' = 0 , y , g↓y , transport (cong₂ R x≡x' refl) xRy
        where
          x≡x' : x ≡ x'
          x≡x' = Hf m l x x' f↓x f↓x' .snd --≤0→≡0 l≤zero
      aux .snd y' g↓y' = m , x , f↓x , transport (cong₂ R refl y≡y') xRy
        where
          y≡y' : y ≡ y'
          y≡y' = isEmbedding→Inj isEmbedding-inl y y' (sym g↓y ∙ subst (g ↓fun[_] y') (≤0→≡0 l≤zero) g↓y')

  -- case n = 0, f and g appear to diverge at 0 steps
  adequacy-pt2 f g Hf Hg zero (inr (f↑ , g↑)) l l≤zero = aux
    where
      aux : _ × _
      aux .fst x' f↓x' =
        ⊥.rec (coherence f 0 x' (subst (f ↓fun[_] x') (≤0→≡0 l≤zero) f↓x') f↑)

      aux .snd y' g↓y' =
        ⊥.rec (coherence g 0 y' (subst (g ↓fun[_] y') (≤0→≡0 l≤zero) g↓y') g↑)

  -- case n = suc n, f terminates in 0 steps, and g terminates in m steps
  adequacy-pt2 f g Hf Hg (suc n) (inl (inl (x , y , m , f↓x , g↓y , xRy))) l l≤sucn = aux
    where
      aux : _ × ((y' : X) →
                 g l ≡ in1 y' →
                 Σ-syntax ℕ (λ j → Σ-syntax X (λ x₁ → (f j ≡ in1 x₁) × R x₁ y')))
      aux .fst x' f↓x' = m , y , g↓y , transport (cong₂ R x≡x' refl) xRy
        where
          x≡x' : x ≡ x'
          x≡x' = Hf zero l x x' f↓x f↓x' .snd
      aux .snd y' g↓y' = zero , x , f↓x , transport (cong₂ R refl y≡y') xRy
        where
          y≡y' : y ≡ y'
          y≡y' = Hg m l y y' g↓y g↓y' .snd

  -- case n = suc n, f terminates in m steps, and g terminates in 0 steps
  adequacy-pt2 f g Hf Hg (suc n) (inl (inr (x , y , m , f↓x , g↓y , xRy))) l l≤sucn = aux
    where
      aux : _ × _
      aux .fst x' f↓x' = zero , y , g↓y , transport (cong₂ R x≡x' refl) xRy
        where
          x≡x' : x ≡ x'
          x≡x' = Hf m l x x' f↓x f↓x' .snd
      aux .snd y' g↓y' = m , x , f↓x , transport (cong₂ R refl y≡y') xRy
        where
          y≡y' : y ≡ y'
          y≡y' = Hg zero l y y' g↓y g↓y' .snd

  -- case n = suc n, f and g appear to diverge at 0 steps
  adequacy-pt2 f g Hf Hg (suc n) (inr (f↑ , g↑ , bisim-f-g-n)) zero l≤suc-n = aux
    where
      aux : _ × _
      aux .fst x f↓x = ⊥.rec (coherence f zero x f↓x f↑)
      aux .snd y g↓y = ⊥.rec (coherence g zero y g↓y g↑)
  adequacy-pt2 f g Hf Hg (suc n) (inr (f↑ , g↑ , bisim-f-g-n)) (suc l) sucl≤suc-n = aux
    where
      ≤-suc-n : ∀ m n → m ≤ suc n → (m ≤ n) ⊎ (m ≡ suc n)
      ≤-suc-n zero zero H = in1 ≤-refl
      ≤-suc-n (suc m) zero H = inr (cong suc (≤0→≡0 (pred-≤-pred H)))
      ≤-suc-n zero (suc n) H = in1 zero-≤
      ≤-suc-n (suc m) (suc n) H with ≤-split H
      ... | inl less = in1 (pred-≤-pred less)
      ... | inr eq = inr eq

      aux : _ × _

      -- If l ≤ n, then the result follows by the IH (i.e. the theorem at n).
      aux .fst x' f↓x' = suc m , y , eq , Rx'y

      -- adequacy-pt2 f g Hf Hg n bisim-f-g-n l l≤n
        where
          IH : _
          IH = adequacy-pt2 (f ∘ suc) (g ∘ suc) (↓-unique-downward f Hf) (↓-unique-downward g Hg) n bisim-f-g-n l (pred-≤-pred sucl≤suc-n)

          m : ℕ
          m = IH .fst x' f↓x' .fst

          y : X
          y = IH .fst x' f↓x' .snd .fst

          eq : g (suc m) ≡ inl y
          eq = IH .fst x' f↓x' .snd .snd .fst

          Rx'y : R x' y
          Rx'y = IH .fst x' f↓x' .snd .snd .snd

      aux .snd y' g↓y' = suc m , x , eq , Rxy'
        where
          IH : _
          IH = adequacy-pt2 (f ∘ suc) (g ∘ suc) (↓-unique-downward f Hf) (↓-unique-downward g Hg) n bisim-f-g-n l (pred-≤-pred sucl≤suc-n)

          m : ℕ
          m = IH .snd y' g↓y' .fst

          x : X
          x = IH .snd y' g↓y' .snd .fst

          eq : f (suc m) ≡ inl x
          eq = IH .snd y' g↓y' .snd .snd .fst

          Rxy' : R x y'
          Rxy' = IH .snd y' g↓y' .snd .snd .snd


  -- Global bisimilarity implies the first definition.
  adequacy-pt1 : (lg1 lg2 : L^gl X) →
    (lg1 ≈g lg2) → (n : ℕ) → (n ⊨ ⟦ lg1 ⟧ ≈ ⟦ lg2 ⟧)
  adequacy-pt1 lg1 lg2 bisim zero with unfold-≈g bisim
  ... | in1 (x , y , eq1 , eq2 , xRy) =
    inl (inl (x , y , 0 , bigStep-η-zero lg1 x eq1 , bigStep-η-zero lg2 y eq2 , xRy))

  ... | in2 (x , eq1 , m , y , eq2 , xRy) = 
    inl (inl (x , y , m , bigStep-η-zero lg1 x eq1 , bigStep-δ^n∘η lg2 y m eq2 , xRy)) 

  ... | in3 (y , eq2 , m , x , eq1 , xRy) = 
    in1 (inr (x , y , m , bigStep-δ^n∘η lg1 x m eq1 , bigStep-η-zero lg2 y eq2 , xRy))

  ... | in4 (lg1' , lg2' , eq1 , eq2 , bisim') =
    inr
      ((λ m m≤zero → (λ i → toFun X-clk-irrel lg1 (≤0→≡0 m≤zero i)) ∙ (bigStep-δ-zero lg1 lg1' eq1)) ,
       (λ m m≤zero → (λ i → toFun X-clk-irrel lg2 (≤0→≡0 m≤zero i)) ∙ (bigStep-δ-zero lg2 lg2' eq2)))

  adequacy-pt1 lg1 lg2 bisim (suc n) with unfold-≈g bisim
  ... | in1 (x , y , eq1 , eq2 , xRy) =
    inl (inl (x , y , 0 , bigStep-η-zero lg1 x eq1 , bigStep-η-zero lg2 y eq2 , xRy))

  ... | in2 (x , eq1 , m , y , eq2 , xRy) = 
    inl (inl (x , y , m , bigStep-η-zero lg1 x eq1 , bigStep-δ^n∘η lg2 y m eq2 , xRy)) 

  ... | in3 (y , eq2 , m , x , eq1 , xRy) = 
    in1 (inr (x , y , m , bigStep-δ^n∘η lg1 x m eq1 , bigStep-η-zero lg2 y eq2 , xRy))
  ... | in4 (lg1' , lg2' , eq1 , eq2 , bisim') = inr pf
    where
      pf : _ × _
      pf .fst      m m≤zero = (λ i → toFun X-clk-irrel lg1 (≤0→≡0 m≤zero i)) ∙ (bigStep-δ-zero lg1 lg1' eq1)
      pf .snd .fst m m≤zero = (λ i → toFun X-clk-irrel lg2 (≤0→≡0 m≤zero i)) ∙ (bigStep-δ-zero lg2 lg2' eq2)
      pf .snd .snd = let IH = adequacy-pt1 lg1' lg2' bisim' n in
        transport (sym (λ i → n ⊨ aux1 i ≈ aux2 i)) IH
        where
          aux1 :  ⟦ lg1 ⟧ ∘ suc ≡ ⟦ lg1' ⟧
          aux1 = funExt (λ n → bigStep-δ-suc lg1 lg1' n eq1)

          aux2 :  ⟦ lg2 ⟧ ∘ suc ≡ ⟦ lg2' ⟧
          aux2 = funExt (λ n → bigStep-δ-suc lg2 lg2' n eq2)

        -- Know: lg1 = δ^gl (lg1'), so ⟦ lg1 ⟧ ∘ suc ≡ ⟦ lg1' ⟧
        --       lg2 = δ^gl (lg2'), so ⟦ lg2 ⟧ ∘ suc ≡ ⟦ lg2' ⟧
        --       IH : n ⊨ ⟦ lg1' ⟧ ≈ ⟦ lg2' ⟧
        --       Goal : n ⊨ (⟦ lg1 ⟧ ∘ suc) ≈ (⟦ lg2 ⟧ ∘ suc)









{-

Doesn't pass the termination checker:

   -- Later operator on step-indexed relations.
   ▷ : {ℓ : Level} → (ℕ → Type ℓ) → (ℕ → Type ℓ)
   ▷ R zero = ⊤*
   ▷ R (suc n) = R n

 n ⊨ f ≈ g =
       (Σ[ x ∈ X ] Σ[ y ∈ X ] (f ↓fun[ 0 ] x) × (g ↓fun[ 0 ] y) × R x y)
     + (Σ[ x ∈ X ] Σ[ y ∈ X ] Σ[ m ∈ ℕ ] (f ↓fun[ 0 ] x) × (g ↓fun[ m ] y) × R x y)
     + (Σ[ x ∈ X ] Σ[ y ∈ X ] Σ[ m ∈ ℕ ] (f ↓fun[ m ] x) × (g ↓fun[ 0 ] y) × R x y)
     + ▷ (bisimFun f g) n

-}
