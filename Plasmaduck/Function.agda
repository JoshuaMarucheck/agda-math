open import Level using (Level; _⊔_) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary using (Rel; IsEquivalence)


module Plasmaduck.Function where

variable
    α β γ : Level
    A : Set α
    B : Set β
    C : Set γ

_≈_ : {α β : Level} {A : Set α} {B : A → Set β} → (f g : (x : A) → B x) → Set (α ⊔ β)
_≈_ f g = ∀ x → f x ≡ g x
infix 1 _≈_

≈-isEquivalence : {α β : Level} {A : Set α} {B : A → Set β} → IsEquivalence (_≈_ {A = A} {B = B})
≈-isEquivalence = record {
    refl = λ x → refl;
    sym = λ f≈g x → sym (f≈g x);
    trans = λ f≈g g≈h x → trans (f≈g x) (g≈h x)
    }

{-
    Suppose you're defining a type. Supposing f and g have all the same outputs, you want to show that the two following types are equal:
        ∀ x → P (f x)
        ∀ x → P (g x)
    You can't just invoke cong, since that requires x to be instantiated.

    P depends only on its input of type B.

    f g : A → B
    P : B → C

    tbh, this should be the same as saying that P ∘ f and P ∘ g are the same function, no?
    That is, P ∘ f ≈ P ∘ g
-}
-- dependent-equality : (f g : A → B) → f ≈ g → (P : B → Set γ) → (∀ (x : A) → P (f x)) ≡ (∀ (x : A) → P (g x))
-- dependent-equality f g f≈g P = {!   !}

_⇔_ : {α β : Level} (A : Set α) (B : Set β) → Set (α ⊔ β)
A ⇔ B = (A → B) × (B → A)

⇔-isEquivalence : {ℓ : Level} → IsEquivalence (_⇔_ {α = ℓ} {β = ℓ})
⇔-isEquivalence = record {
    refl = λ {x} → (λ z → z) , (λ z → z);
    sym = λ {x} {y} z → z .proj₂ , z .proj₁;
    trans = λ {i} {j} {k} z z₁ →
        (λ z₂ → z₁ .proj₁ (z .proj₁ z₂)) , (λ z₂ → z .proj₂ (z₁ .proj₂ z₂))
    }
