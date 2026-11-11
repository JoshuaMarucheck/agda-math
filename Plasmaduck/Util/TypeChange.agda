open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; inspect; cong; Reveal_·_is_; [_]; refl; sym; trans)
open import Relation.Binary using (Rel; IsEquivalence)
open import Function using (_∋_; _∘_; id; Bijective; Injective; Surjective)
open import Data.Product using (Σ; _,_)

open import Plasmaduck.Relation.OrderHelpers using (WeakTri; cmp₁; cmp₂; cmp₃; _Extends_)
open import Plasmaduck.Relation.OperatorDefs using (SameRel)


module Plasmaduck.Util.TypeChange where
variable
    ℓ ℓ₁ ℓ₂ a b c : Level
    A B C : Set ℓ

-- For when you need to tell the type checker that yes, these two types really are equal!
change-type : (A ≡ B) → (x : A) → B
change-type refl x = x

-- ≡-recompute : (x y : A) → .(x ≡ y) → x ≡ y
-- ≡-recompute x y x=y = {!   !}

-- change-type' : .(A ≡ B) → (x : A) → B
-- change-type' A=B = {!   !}

change-type-proof-irrelevance : (pf₁ pf₂ : A ≡ B) {x : A} → change-type pf₁ x ≡ change-type pf₂ x
change-type-proof-irrelevance refl refl = refl

change-type-trans : (pf₁ : A ≡ B) (pf₂ : B ≡ C) {x : A} → change-type pf₂ (change-type pf₁ x) ≡ change-type (trans pf₁ pf₂) x
change-type-trans refl refl = refl

change-type-trans' : (pf₁ : A ≡ B) (pf₂ : B ≡ C) (pf₃ : A ≡ C) {x : A} → change-type pf₂ (change-type pf₁ x) ≡ change-type pf₃ x
change-type-trans' refl refl refl = refl

-- Note the following use of change-type-trans'
change-type-flatten : (pf₁ : A ≡ B) (pf₂ : B ≡ A) {x : A} → change-type pf₂ (change-type pf₁ x) ≡ x
change-type-flatten pf₁ pf₂ = change-type-trans' pf₁ pf₂ refl

change-type-elim : (pf : A ≡ A) {x : A} → change-type pf x ≡ x
change-type-elim refl = refl

change-type-swap-to-left : {pf₁ : A ≡ B} (pf₂ : B ≡ A) {x : A} {y : B} → x ≡ change-type pf₂ y → change-type pf₁ x ≡ y
change-type-swap-to-left {pf₁ = refl} refl refl = refl

change-type-flat-cong :
    {A : Set a} {i j : A} (i=j : i ≡ j) {B : Set b} {x : B} →
    change-type (cong (λ _ → B) i=j) x ≡ x
change-type-flat-cong refl = refl

change-type-arrow-input :
    {A₁ A₂ : Set a} (pf : A₁ ≡ A₂) (B : (i : A₁) → Set c) →
    ((i : A₁) → B i) ≡ ((j : A₂) → B (change-type (sym pf) j))
change-type-arrow-input refl B = refl

-- Changes the working type of f and i so that they pass through A₂ instead of A₁.
change-type-bridge :
    {A₁ A₂ : Set a} (pf : A₁ ≡ A₂) (B : (i : A₁) → Set c) → (f : (i : A₁) → B i) →
    (i : A₁) →
    f i ≡ change-type (cong B (change-type-flatten pf (sym pf))) ((change-type (change-type-arrow-input pf B) f) (change-type pf i))
change-type-bridge refl B f i = refl

change-type-swap-to-right : {pf₂ : B ≡ A} (pf₁ : A ≡ B) {x : A} {y : B} → change-type pf₁ x ≡ y → x ≡ change-type pf₂ y
change-type-swap-to-right {pf₂ = refl} refl refl = refl

-- Note (cong B i≡j) is the easy proof to construct here, but it could be any proof.
-- We do need to know i ≡ j though.
change-type-input-dependence-irrelevance :
    {A : Set a} (B : A → Set b) {C : Set c} → (f : {k : A} → B k → C) →
    {i j : A} → (i≡j : i ≡ j) →
    (x : B i) →
    f (change-type (cong B i≡j) x) ≡ f x
change-type-input-dependence-irrelevance B f refl x = refl

change-type-input-dependence-irrelevance' :
    {A : Set a} (B : A → Set b) {C : Set c} → (f : {k : A} → B k → C) →
    {i j : A} → (i≡j : i ≡ j) → (Bi≡Bj : B i ≡ B j) →
    (x : B i) →
    f (change-type Bi≡Bj x) ≡ f x
change-type-input-dependence-irrelevance' B f refl refl x = refl

cong₂-dependent :
    {A : Set a} (B : A → Set b) {C : Set c} (f : (i : A) → B i → C) →
    {i j : A} → (i≡j : i ≡ j) →
    {p : B i} {q : B j} → change-type (cong B i≡j) p ≡ q →
    f i p ≡ f j q
cong₂-dependent B C refl refl = refl

change-type-dependence-commute :
    {A : Set a} (B : (i : A) → Set c) → (f : (i : A) → B i) →
    {i j : A} → (i≡j : i ≡ j) →
    change-type (cong B i≡j) (f i) ≡ f j
change-type-dependence-commute B f refl = refl

change-type-output-dependence-commute :
    {A : Set a} (B : A → Set b) (C : (i : A) → B i → Set c) → (f : {i : A} → (q : B i) → C i q) →
    {i j : A} → (i≡j : i ≡ j) →
    (x : B i) →
    f (change-type (cong B i≡j) x) ≡ change-type (cong₂-dependent B C i≡j {p = x} {q = change-type (cong B i≡j) x} refl) (f x)
change-type-output-dependence-commute B C f refl x = refl

change-type-relation-dependence-irrelevance :
    {A : Set a} (B : A → Set b)
    (rel : {i : A} → Rel (B i) c) →
    {i j : A} (i≡j : i ≡ j) →
    (x y : B i) → rel x y → rel {i = j} (change-type (cong B i≡j) x) (change-type (cong B i≡j) y)
change-type-relation-dependence-irrelevance B rel refl x y x~y = x~y

change-type-relation-dependence-irrelevance' :
    {A : Set a} (B : A → Set b)
    (rel : {i : A} → Rel (B i) c) →
    {i j : A} (i≡j : i ≡ j) → (Bi≡Bj : B i ≡ B j) →
    (x y : B i) → rel x y → rel {i = j} (change-type Bi≡Bj x) (change-type Bi≡Bj y)
change-type-relation-dependence-irrelevance' B rel refl refl x y x~y = x~y

change-type-injective : (pf : A ≡ B) (_≈₁_ : Rel A ℓ₁) (_≈₂_ : Rel B ℓ₂) → _≈₁_ Extends (λ x y → change-type pf x ≈₂ change-type pf y) → Injective _≈₁_ _≈₂_ (change-type pf)
change-type-injective refl _ _ 1-extends-2 x≈₂y = 1-extends-2  x≈₂y

change-type-surjective : (pf : A ≡ B) (_≈₁_ : Rel A ℓ₁) (_≈₂_ : Rel B ℓ₂) → (λ x y → change-type pf x ≈₂ change-type pf y) Extends _≈₁_ → Surjective _≈₁_ _≈₂_ (change-type pf)
change-type-surjective refl _ _ 2-extends-1 z = z , 2-extends-1

change-type-bijective : (pf : A ≡ B) (_≈₁_ : Rel A ℓ₁) (_≈₂_ : Rel B ℓ₂) → SameRel A _≈₁_ (λ x y → change-type pf x ≈₂ change-type pf y) → Bijective _≈₁_ _≈₂_ (change-type pf)
change-type-bijective refl _ _ (2-extends-1 , 1-extends-2) = 1-extends-2 , λ z → z , 2-extends-1

change-type-bijective' : (pf : A ≡ B) → Bijective _≡_ _≡_ (change-type pf)
change-type-bijective' refl = id , λ z → z , id
