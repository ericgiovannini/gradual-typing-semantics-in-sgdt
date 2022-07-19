-- | The below is an attempt to describe the semantics of gradually
-- | typed languages in a HOAS style.
--
-- | Warning: this might not make any sense without directed type
-- | theory!

open import ErrorDomains
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Product

op : Preorder → Preorder
op X = record
         { X = X.X
         ; _⊑_ = λ x y → y X.⊑ x
         ; refl = X.refl
         ; trans = λ p1 p2 → X.trans p2 p1
         }
  where module X = Preorder X

opF : ∀ {X Y} → (X ⇨ Y) → op X ⇨ op Y
opF {X}{Y} f = record { f = f.f ; mon = _⇨_.mon f }
  where module X = Preorder X
        module Y = Preorder Y
        module f = _⇨_ f

record FiberPts {X : Preorder}{Y : Preorder} (f : X ⇨ Y) (y : Preorder.X Y) : Set where
  field
    pt : Preorder.X X
    over : _⇨_.f f pt ≡ y

Fiber : {X : Preorder}{Y : Preorder} (f : X ⇨ Y) (y : Preorder.X Y) → Preorder
Fiber {X}{Y} f y = record { X = FiberPts f y
                   ; _⊑_ = λ x x' → FiberPts.pt x ⊑x FiberPts.pt x'
                   ; refl = λ x → X.refl (FiberPts.pt x)
                   ; trans = λ p1 p2 → X.trans p1 p2 }
 where module X = Preorder X
       _⊑x_ = X._⊑_
       module Y = Preorder Y

record fibration {X : Preorder} {Y : Preorder} (f : X ⇨ Y) : Set where
  module X = Preorder X
  module Y = Preorder Y
  _⊑x_ = X._⊑_
  _⊑y_ = Y._⊑_
  module f = _⇨_ f
  field
    -- A < B -> tm B -> tm A (downcast)
    pull : ∀ (x : X.X) {y : Y.X} → (y ⊑y app f x) → X.X

    -- the downcast is a lower bound
    -- dncast (A < B) N <= N
    pullLB : ∀ {x : X.X} {y : Y.X} → (c : y ⊑y app f x) → pull x c ⊑x x

    -- the downcast is the *greatest* lower bound over a type at least as low
    -- Given N : B
    -- and M' : A' where A' <= A <= B
    -- and M' <= N over A' <= A <= B
    -- then M' <= dncast (A <= B) N over A' <= A
    pullGLB : ∀ {x : X.X} {y : Y.X} {x' : X.X} → (c : y ⊑y app f x) → (app f x' ⊑y y) → (x' ⊑x x) → x' ⊑x pull x c

opfibration : ∀ {X Y} (f : X ⇨ Y) → Set
opfibration f = fibration (opF f)

record GLTC : Set₁ where
  field
    type : Preorder
  module type = Preorder type
  _⊑ty_ = type._⊑_

  field
    term : Preorder
    type-of : term ⇨ type

    dncasts : fibration   type-of
    upcasts : opfibration type-of

    -- need that the dncast of an upcast is the identity(!)
    -- projection : {!!}

  module term = Preorder term
  module type-of = _⇨_ type-of
  _⊑tm_ = term._⊑_

  -- dynamic type
  field
    dyn : type.X
    dynT : ∀ A → A ⊑ty dyn

  of-ty : type.X → Preorder
  of-ty A = Fiber type-of A

  -- errors
  field
    err : ∀ A → Preorder.X (of-ty A)
    -- err⊥ : ∀ M →
    -- can we define err to be the least element of type dyn which then is then
    -- err <= up (M) so dn(err) <= dn(up(M))
    

  -- function types
  field
    arr : type ⇨ type ⇒ type
  arr' : type.X → type.X → type.X
  arr' A B = app (app arr A) B
  field
    lam : ∀ {A B} → (of-ty A ⇒ of-ty B) ⇔ of-ty (arr' A B)
    

  -- can we *prove* that application preserves error, i.e., that (err{A -> B} N = err{B})?
  -- doubtful... seems like we need to add it in as an axiom, i.e., that the above is an iso of *pointed* preorders

  -- boolean types
  field
    bool : type.X
     -- this doesn't satisfy the UMP because
     -- there are terms that are not strict in their input (x |- x) 
    if : ∀ {A} → product (of-ty A) (of-ty A) ◃ (of-ty bool ⇒ of-ty A)
    
    
--     -- terms are more interesting because they are "clocked"
--     term : type → K → Set
--     _||_⊨_⊑₁_ : ∀ {A B : type} → (A ⊑₀ B) → (k : K) → term A k → term B k → ℙ
--     -- reflexivity is "approximation-wise"
--     refl₁   : ∀ {A}{M : ∀ k → term A k} → (k : K) → refl₀ || k ⊨ (M k) ⊑₁ (M k)
--     -- transitivity is only "in the limit"
--     trans₁  : ∀ {A B C}{M : ∀ k → term A k}{N : ∀ k → term B k}{P : ∀ k → term C k}
--             {AB : A ⊑₀ B}{BC : B ⊑₀ C}
--             → (∀ k → AB || k ⊨ (M k) ⊑₁ (N k))
--             → (∀ k → BC || k ⊨ (N k) ⊑₁ (P k))
--             → ∀ k → trans₀ AB BC || k ⊨ (M k) ⊑₁ (P k)

--     -- the above defines a kind of "guarded functor" ty : term -> type

--     -- upcasts/downcasts ask that that functor be an/a opfibration/fibration
--     up : ∀ {A B} → A ⊑₀ B → ∀ k → term A k → term B k
    
  
--     dn : ∀ {A B} → A ⊑₀ B → ∀ k → term B k → term A k

-- postulate
--   ▸₁ : Set₁ → Set₁
--   fix : (▸₁ 𝕌 → 𝕌) → 𝕌
--   θ𝕌 : ▸₁ 𝕌 →  𝕌

-- infixl 30 _+_
-- data _+_ (A B : Set) : Set where
--   inl_ : A → A + B
--   inr_ : B → A + B

-- record One : Set where
--   constructor ⟨⟩

-- Two : Set
-- Two = One + One

-- L℧ : Set → Set
-- L℧ X = fix (λ L℧X → One + X + θ𝕌 L℧X)

-- dyn℧ : Set
-- dyn℧ = fix λ dyn℧ → L℧ ((Two + (θ𝕌 dyn℧ → θ𝕌 dyn℧)))

record GTLC-CBV : Set₁ where
  field
    type : Preorder
    valu : Preorder
    comp : Preorder
    ty-ofv : valu ⇨ type
    ty-ofc : comp ⇨ type

  module type = Preorder type

  val-of-ty : type.X → Preorder
  val-of-ty A = Fiber ty-ofv A
  comp-of-ty : type.X → Preorder
  comp-of-ty A = Fiber ty-ofc A

  field
    -- not quite right, need the rhs to be some kind of strict morphisms.
    -- should probably have a third sort of ev ctxts from A to B
    lett : ∀ {A B} → (val-of-ty A ⇒ comp-of-ty B) ⇔ (comp-of-ty A ⇒ comp-of-ty B)
    
    upcasts : opfibration ty-ofv
    dncasts :   fibration ty-ofc -- problem this doesn't imply that downcasts are linear, maybe we add this as a separate prop?
    -- something for projection property

    -- dynamic type
    dyn : type.X
    dyn⊤ : ∀ A → type ⊨ A ⊑ dyn

    -- errors...

    -- functions
    arr : type ⇨ type ⇒ type
  arr' : type.X → type.X → type.X
  arr' A B = app (app arr A) B
  field
    lam : ∀ {A B} → (val-of-ty A ⇒ comp-of-ty B) ⇔ val-of-ty (arr' A B)

    -- bools
    bool : type.X
    if :  ∀ {A} → product (comp-of-ty A) (comp-of-ty A) ⇔ (val-of-ty bool ⇒ comp-of-ty A)
