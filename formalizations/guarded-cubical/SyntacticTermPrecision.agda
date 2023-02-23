{-# OPTIONS --cubical --rewriting --guarded #-}

 -- to allow opening this module in other files while there are still holes
{-# OPTIONS --allow-unsolved-metas #-}

open import Later

module SyntacticTermPrecision (k : Clock) where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Relation.Nullary

open import ErrorDomains k
open import GradualSTLC

---- Syntactic term precision relation ----

-- Make this a sigma type
data CtxTyPrec : Set where
  · : CtxTyPrec
  _::_ : {A B : Ty} -> CtxTyPrec -> A ⊑ B -> CtxTyPrec


infixr 5 _::_

Ctx-ref : Ctx -> CtxTyPrec
Ctx-ref · = ·
Ctx-ref (Γ :: x) = Ctx-ref Γ :: ⊑ref x


lhs-ty : {A B : Ty} -> A ⊑ B -> Ty
lhs-ty {A} d = A

rhs-ty : {A B : Ty} -> A ⊑ B -> Ty
rhs-ty {_} {B} d = B

lhs : CtxTyPrec -> Ctx
lhs · = ·
lhs (ctx :: d) = (lhs ctx) :: lhs-ty d

rhs : CtxTyPrec -> Ctx
rhs · = ·
rhs (ctx :: d) = (rhs ctx) :: rhs-ty d


lem-lhs : (A : Ty) -> A ≡ lhs-ty (⊑ref A)
lem-lhs A = refl

lem-rhs : (A : Ty) -> A ≡ rhs-ty (⊑ref A)
lem-rhs A = refl


ctx-refl-lhs : (Γ : Ctx) -> Γ ≡ lhs (Ctx-ref Γ)
ctx-refl-lhs · = refl
ctx-refl-lhs (Γ :: x) = λ i -> ctx-refl-lhs Γ i :: lem-lhs x i

ctx-refl-rhs : (Γ : Ctx) -> Γ ≡ rhs (Ctx-ref Γ)
ctx-refl-rhs · = refl
ctx-refl-rhs (Γ :: x) = λ i -> ctx-refl-rhs Γ i :: lem-rhs x i

iso-L : {Γ : Ctx} {A : Ty} -> Tm Γ A -> Tm (lhs (Ctx-ref Γ)) A
iso-L {Γ} {A} M = transport (λ i → Tm (ctx-refl-lhs Γ i) A) M

iso-R : {Γ : Ctx} {A : Ty} -> Tm Γ A -> Tm (rhs (Ctx-ref Γ)) A
iso-R {Γ} {A} M = transport (λ i -> Tm (ctx-refl-rhs Γ i) A) M


TmL : {A B : Ty} -> CtxTyPrec -> A ⊑ B -> Set
TmL ctx d = {!!}


-- "Contains" relation stating that a context Γ contains a type T

data _∋'_ : {A B : Ty} -> CtxTyPrec -> A ⊑ B -> Set where

infix 4 _∋'_

contains-lhs : {A B : Ty} ->
  (Γ : CtxTyPrec) (d : A ⊑ B) -> (Γ ∋' d) -> (lhs Γ ∋ A)
contains-lhs = {!!}

contains-rhs : {A B : Ty} ->
  (Γ : CtxTyPrec) (d : A ⊑ B) -> (Γ ∋' d) -> (rhs Γ ∋ B)
contains-rhs = {!!}




-- d is fixed here so it should be a parameter, not an index
-- (hence why it doesn't appear after M and N)
data ltdyn-tm :
  {A B : Ty} ->
  (Γ : CtxTyPrec) ->
  (d : A ⊑ B) ->
  (M : Tm (lhs Γ) A) ->
  (N : Tm (rhs Γ) B) -> Set where

  -- err
  err : {A B : Ty} -> (Γ : CtxTyPrec) -> (d : A ⊑ B) -> (N : Tm (rhs Γ) B) -> ltdyn-tm Γ d err N

  ---- *Congruence rules* ----

  -- variables
  -- var : {!{A B : Ty} -> (Γ : CtxTyPrec) -> (d : A ⊑ B) -> (Γ ∋' d) -> ?!}
  var : (A B : Ty) ->
        (Γ : CtxTyPrec) ->
        (d : A ⊑ B) ->
        (x : Γ ∋' d) ->
        ltdyn-tm Γ d (var (contains-lhs Γ d x)) (var (contains-rhs Γ d x))

  -- natural numbers
  zro : (Γ : CtxTyPrec) -> ltdyn-tm Γ nat zro zro
  suc : (Γ : CtxTyPrec) (M : Tm (lhs Γ) nat) (M' : Tm (rhs Γ) nat) ->
        ltdyn-tm Γ nat M M' ->
        ltdyn-tm Γ nat (suc M) (suc M')

  -- lambdas
  lda : (Γ : CtxTyPrec) (A A' B B' : Ty)
        (c : A ⊑ A') (d : B ⊑ B')
        (M1 : Tm ((lhs Γ) :: A) B) (M2 : Tm ((rhs Γ) :: A') B') ->
        ltdyn-tm (Γ :: c) d M1 M2 ->
        ltdyn-tm Γ (c => d) (lda M1) (lda M2)

  -- application
  app : (Γ : CtxTyPrec) (Ain Bin Aout Bout : Ty)
        (din : Ain ⊑ Bin) (dout : Aout ⊑ Bout)
        (M1 : Tm (lhs Γ) (Ain => Aout)) (N1 : Tm (lhs Γ) Ain)
        (M2 : Tm (rhs Γ) (Bin => Bout)) (N2 : Tm (rhs Γ) Bin) ->
        ltdyn-tm Γ (din => dout) M1 M2 ->
        ltdyn-tm Γ din N1 N2 ->
        ltdyn-tm Γ dout (app M1 N1) (app M2 N2)
    

  ---- *Cast rules* ----
  
  upR : (Γ : Ctx) (A B : Ty)
        (c : A ⊑ B)
        --(M : Tm (lhs Γ) A)
        (N : Tm Γ A) ->
     --   ltdyn-tm Γ (⊑ref A) N N ->
     ltdyn-tm (Ctx-ref Γ) c (iso-L N) (up c (iso-R N))
     --   ltdyn-tm (Ctx-ref Γ) c N (up c N)

  upL : (Γ : CtxTyPrec) (A B : Ty)
        (c : A ⊑ B)
        (M : Tm (lhs Γ) A)
        (N : Tm (rhs Γ) B) ->
        ltdyn-tm Γ c M N ->
        ltdyn-tm Γ (⊑ref B) (up c M) N
  
  dnL : (Γ : Ctx) (A B : Ty)
        (c : A ⊑ B)
        (M : Tm Γ B) ->
       --  (N : Tm (rhs Γ) B) ->
       --  ltdyn-tm Γ (⊑ref B) M N ->
       ltdyn-tm (Ctx-ref Γ) c (dn c (iso-L M)) (iso-R M)
        -- ltdyn-tm Γ c (dn c M) M

  dnR : (Γ : CtxTyPrec) (A B : Ty)
        (c : A ⊑ B)
        (M : Tm (lhs Γ) A)
        (N : Tm (rhs Γ) B) ->
        ltdyn-tm Γ c M N ->
        ltdyn-tm Γ (⊑ref A) M (dn c N)


-- Notation that matches the written syntax, with d appearing at the end
_|-_⊑tm_#_ : {A B : Ty} -> (Γ : CtxTyPrec) -> (Tm (lhs Γ) A) -> (Tm (rhs Γ) B) -> A ⊑ B -> Set
Γ |- M ⊑tm N # d = ltdyn-tm Γ d M N
