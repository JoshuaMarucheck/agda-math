open import Level using (Level; _⊔_)
open import Relation.Unary using (_⊆′_; _≐′_) renaming (Pred to Pred')
open import Relation.Binary using (Rel; Reflexive; Symmetric; Antisymmetric; Transitive; IsEquivalence; IsPreorder; IsPartialOrder; _⇒_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)



module Plasmaduck.Relation.GeneralizedSubset {α β γ : Level} {A : Set α} {B : Set β} (_∈_ : A → B → Set γ)  where

_⊆_ : Rel B (α ⊔ γ)
_⊆_ X Y = ∀ i → i ∈ X → i ∈ Y

_≐_ : Rel B (α ⊔ γ)
_≐_ X Y = X ⊆ Y × Y ⊆ X

⊆-refl : Reflexive _⊆_
⊆-refl = λ x₁ z → z

⊆-reflexive : _≐_ ⇒ _⊆_
⊆-reflexive = proj₁

⊆-antisym : Antisymmetric _≐_ _⊆_
⊆-antisym = _,_

⊆-trans : ∀ {x y z} → x ⊆ y → y ⊆ z → x ⊆ z
⊆-trans x⊆y y⊆z i i∈x = y⊆z i (x⊆y i i∈x)

≐-refl : Reflexive _≐_
≐-refl = ⊆-refl , ⊆-refl

≐-sym : ∀ {x} {y} → x ≐ y → y ≐ x
≐-sym (x⊆y , y⊆x) = y⊆x , x⊆y

≐-trans : ∀ {x} {y} {z} → x ≐ y → y ≐ z → x ≐ z
≐-trans (x⊆y , y⊆x) (y⊆z , z⊆y) = ⊆-trans x⊆y y⊆z , ⊆-trans z⊆y y⊆x

≐-isEquivalence : IsEquivalence _≐_
≐-isEquivalence = record {
    refl = ≐-refl;
    sym = ≐-sym;
    trans = ≐-trans
    }

⊆-isPreorder : IsPreorder _≐_ _⊆_
⊆-isPreorder = record {
    isEquivalence = ≐-isEquivalence;
    reflexive = ⊆-reflexive;
    trans = ⊆-trans
    }

⊆-isPartialOrder : IsPartialOrder _≐_ _⊆_
⊆-isPartialOrder = record {
    isPreorder = ⊆-isPreorder;
    antisym = ⊆-antisym
    }
