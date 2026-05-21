open import Level using (Level; _⊔_) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary using (Rel; IsEquivalence)


module Plasmaduck.Function where

_≈_ : {α β : Level} {A : Set α} {B : Set β} → (f g : A → B) → Set (α ⊔ β)
_≈_ f g = ∀ x → f x ≡ g x
infix 1 _≈_

≈-isEquivalence : {α β : Level} {A : Set α} {B : Set β} → IsEquivalence (_≈_ {A = A} {B = B})
≈-isEquivalence = record {
    refl = λ x → refl;
    sym = λ f≈g x → sym (f≈g x);
    trans = λ f≈g g≈h x → trans (f≈g x) (g≈h x)
    }

_⇔_ : {α β : Level} (A : Set α) (B : Set β) → Set (α ⊔ β)
A ⇔ B = (A → B) × (B → A)

⇔-isEquivalence : {ℓ : Level} → IsEquivalence (_⇔_ {α = ℓ} {β = ℓ})
⇔-isEquivalence = record {
    refl = λ {x} → (λ z → z) , (λ z → z);
    sym = λ {x} {y} z → z .proj₂ , z .proj₁;
    trans = λ {i} {j} {k} z z₁ →
        (λ z₂ → z₁ .proj₁ (z .proj₁ z₂)) , (λ z₂ → z .proj₂ (z₁ .proj₂ z₂))
    }
