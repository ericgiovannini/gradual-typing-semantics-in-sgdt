module ErrorDomains where

𝕍 : Set₂
𝕍 = Set₁

𝕌 : 𝕍
𝕌 = Set

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Product

record Preorder : 𝕍 where
  field
    X   : 𝕌
    _⊑_ : X → X → 𝕌
    refl : ∀ (x : X) → x ⊑ x
    trans : ∀ {x y z : X} → x ⊑ y → y ⊑ z → x ⊑ z

infixr 20 _⇨_
infixr 20 _⇒_

record _⇨_ (X : Preorder) (Y : Preorder) : 𝕌 where
  module X = Preorder X
  module Y = Preorder Y
  field
    f   : X.X → Y.X
    mon : ∀ {x y} → X._⊑_ x y → Y._⊑_ (f x) (f y)

app : ∀ {X Y} → (X ⇨ Y) → Preorder.X X → Preorder.X Y
app = _⇨_.f

_$_ = app

_⇒_ : Preorder → Preorder → Preorder
X ⇒ Y = record { X = X ⇨ Y
               ; _⊑_ = λ f g → (x : X.X) → _⇨_.f f x ⊑y _⇨_.f g x
               ; refl = λ x x₁ → _⇨_.mon x (X.refl x₁)
               ; trans = λ p1 p2 x → Y.trans (p1 x) (p2 x) }
  where
    module X = Preorder X
    module Y = Preorder Y
    _⊑y_ = Y._⊑_

_⊨_⊑_ : (X : Preorder) → Preorder.X X → Preorder.X X → Set
X ⊨ x ⊑ x' = Preorder._⊑_ X x x'

record _⊨_≣_ (X : Preorder) (x y : Preorder.X X) : Set where
  module X = Preorder X
  _⊑_ = X._⊑_
  field
    to  : x ⊑ y
    fro : y ⊑ x

record _⇔_ (X : Preorder) (Y : Preorder) : Set where
  field
    to  : X ⇨ Y
    fro : Y ⇨ X
    eqX : ∀ x → X ⊨ app fro (app to x) ≣ x
    eqY : ∀ y → Y ⊨ app to (app fro y) ≣ y

record _◃_ (X Y : Preorder) : Set where
  _⊑y_ = Preorder._⊑_ Y
  field
    emb  : X ⇨ Y
    prj  : Y ⇨ X
    projection : ∀ y → Y ⊨ app emb (app prj y) ⊑ y
    retraction : ∀ x → X ⊨ x ≣ app prj (app emb x)

product : Preorder → Preorder → Preorder
product X Y = record { X = X.X × Y.X
                     ; _⊑_ = λ p1 p2 → (proj₁ p1 ⊑x proj₁ p2) × (proj₂ p1 ⊑y proj₂ p2)
                     ; refl = λ x → (X.refl (proj₁ x)) , (Y.refl (proj₂ x))
                     ; trans = λ leq1 leq2 → (X.trans (proj₁ leq1) (proj₁ leq2)) , Y.trans (proj₂ leq1) (proj₂ leq2)
                     }
  where module X = Preorder X
        _⊑x_ = X._⊑_
        module Y = Preorder Y
        _⊑y_ = Y._⊑_

data TransClosure {X : 𝕌}(_R_ : X → X → 𝕌) : X → X → 𝕌 where
  one  : ∀ {x y} → x R y → TransClosure _R_ x y
  more : ∀ {x y z} → x R y → TransClosure _R_ y z → TransClosure _R_ x z

transClosureAppend : ∀ {X}{_R_ : X → _}{x y z} → TransClosure _R_ x y → TransClosure _R_ y z → TransClosure _R_ x z
transClosureAppend (one x) pyz      = more x pyz
transClosureAppend (more x pxy) pyz = more x (transClosureAppend pxy pyz)

record ReflGraph : 𝕍 where
  field
    X : 𝕌
    _⊑_ : X → X → 𝕌
    refl : ∀ x → x ⊑ x

_^+ : ReflGraph → Preorder
G ^+ = record
  { X = G.X
  ; _⊑_ = TransClosure G._⊑_
  ; refl = λ x → one (G.refl x)
  ; trans = transClosureAppend
  }
  where module G = ReflGraph G

-- Let's get some clocks going
postulate
  K : 𝕌
  ▸^  : K → 𝕌 → 𝕌
  ▸^' : K → 𝕍 → 𝕍
  next^ : ∀ {A}{k} → A → ▸^ k A
  gfix^ : ∀ {k : K}{X : 𝕌} → (▸^ k X → X) → X
  gfix^-unfold : ∀ {k}{X} (f : ▸^ k X → X) → gfix^ f ≡ f (next^ (gfix^ f))

  next^' : ∀ {A}{k} → A → ▸^' k A
  gfix^' : ∀ {k : K}{X : 𝕍} → (▸^' k X → X) → X
  gfix^'-unfold : ∀ {k}{X} (f : ▸^' k X → X) → gfix^' f ≡ f (next^' (gfix^' f))

