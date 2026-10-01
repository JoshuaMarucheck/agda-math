open import Level using (Level)
open import Relation.Unary using (_⊆′_; _≐′_) renaming (Pred to Pred')
open import Relation.Binary using (Reflexive; Symmetric; Antisymmetric; Transitive; IsEquivalence; IsPreorder; IsPartialOrder; _⇒_)
open import Function using (flip; _∘_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)

open import Plasmaduck.Function using (_⇔_)



module Plasmaduck.Relation.Unary {α : Level} (A : Set α) where

variable
    β γ ε : Level


Pred = Pred' A
_⊆_ = _⊆′_ {A = A}
_≐_ = _≐′_ {A = A}

⊆-refl : Reflexive (_⊆_ {β})
⊆-refl = λ x₁ z → z

⊆-reflexive : (_≐_ {β} {γ}) ⇒ _⊆_
⊆-reflexive = proj₁

⊆-antisym : Antisymmetric (_≐_ {β}) _⊆_
⊆-antisym = _,_

⊆-trans : ∀ {x} {y} {z} → _⊆_ {β} {γ} x y → _⊆_ {γ} {ε} y z → x ⊆ z
⊆-trans x⊆y y⊆z i i∈x = y⊆z i (x⊆y i i∈x)

≐-refl : Reflexive (_≐_ {β})
≐-refl = ⊆-refl , ⊆-refl

≐-sym : ∀ {x} {y} → _≐_ {β} {γ} x y → y ≐ x
≐-sym (x⊆y , y⊆x) = y⊆x , x⊆y

≐-trans : ∀ {x} {y} {z} → _≐_ {β} {γ} x y → _≐_ {γ} {ε} y z → x ≐ z
≐-trans (x⊆y , y⊆x) (y⊆z , z⊆y) = ⊆-trans x⊆y y⊆z , ⊆-trans z⊆y y⊆x

≐-isEquivalence : IsEquivalence (_≐_ {β})
≐-isEquivalence = record {
    refl = ≐-refl;
    sym = ≐-sym;
    trans = ≐-trans
    }

⊆-isPreorder : IsPreorder (_≐_ {β}) _⊆_
⊆-isPreorder = record {
    isEquivalence = ≐-isEquivalence;
    reflexive = ⊆-reflexive;
    trans = ⊆-trans
    }

⊆-isPartialOrder : IsPartialOrder (_≐_ {β}) _⊆_
⊆-isPartialOrder = record {
    isPreorder = ⊆-isPreorder;
    antisym = ⊆-antisym
    }
