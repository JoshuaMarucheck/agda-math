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

change-type-proof-irrelevance : (pf₁ pf₂ : A ≡ B) {x : A} → change-type pf₁ x ≡ change-type pf₂ x
change-type-proof-irrelevance refl refl = refl

change-type-trans : (pf₁ : A ≡ B) (pf₂ : B ≡ C) {x : A} → change-type pf₂ (change-type pf₁ x) ≡ change-type (trans pf₁ pf₂) x
change-type-trans refl refl = refl

change-type-trans' : (pf₁ : A ≡ B) (pf₂ : B ≡ C) (pf₃ : A ≡ C) {x : A} → change-type pf₂ (change-type pf₁ x) ≡ change-type pf₃ x
change-type-trans' refl refl refl = refl

change-type-swap : (pf : A ≡ B) {x : A} {y : B} → x ≡ change-type (sym pf) y → change-type pf x ≡ y
change-type-swap refl refl = refl

change-type-input-dependence-irrelevance :
    {A : Set a} (B : A → Set b) {C : Set c} → (f : {k : A} → B k → C) →
    {i j : A} → (i≡j : i ≡ j) →
    (x : B i) →
    f (change-type (cong B i≡j) x) ≡ f x
change-type-input-dependence-irrelevance B f refl x = refl

cong₂-dependent :
    {A : Set a} (B : A → Set b) {C : Set c} (f : (i : A) → B i → C) →
    {i j : A} → (i≡j : i ≡ j) →
    {p : B i} {q : B j} → change-type (cong B i≡j) p ≡ q →
    f i p ≡ f j q
cong₂-dependent B C refl refl = refl

change-type-output-dependence-commute :
    {A : Set a} (B : A → Set b) (C : (i : A) → B i → Set c) → (f : {i : A} → (q : B i) → C i q) →
    {i j : A} → (i≡j : i ≡ j) →
    (x : B i) →
    f (change-type (cong B i≡j) x) ≡ change-type (cong₂-dependent B C i≡j {p = x} {q = change-type (cong B i≡j) x} refl) (f x)
change-type-output-dependence-commute B C f refl x = refl

change-type-injective : (pf : A ≡ B) (_≈₁_ : Rel A ℓ₁) (_≈₂_ : Rel B ℓ₂) → _≈₁_ Extends (λ x y → change-type pf x ≈₂ change-type pf y) → Injective _≈₁_ _≈₂_ (change-type pf)
change-type-injective refl _ _ 1-extends-2 x≈₂y = 1-extends-2  x≈₂y

change-type-surjective : (pf : A ≡ B) (_≈₁_ : Rel A ℓ₁) (_≈₂_ : Rel B ℓ₂) → (λ x y → change-type pf x ≈₂ change-type pf y) Extends _≈₁_ → Surjective _≈₁_ _≈₂_ (change-type pf)
change-type-surjective refl _ _ 2-extends-1 z = z , 2-extends-1

change-type-bijective : (pf : A ≡ B) (_≈₁_ : Rel A ℓ₁) (_≈₂_ : Rel B ℓ₂) → SameRel A _≈₁_ (λ x y → change-type pf x ≈₂ change-type pf y) → Bijective _≈₁_ _≈₂_ (change-type pf)
change-type-bijective refl _ _ (2-extends-1 , 1-extends-2) = 1-extends-2 , λ z → z , 2-extends-1

change-type-bijective' : (pf : A ≡ B) → Bijective _≡_ _≡_ (change-type pf)
change-type-bijective' refl = id , λ z → z , id
