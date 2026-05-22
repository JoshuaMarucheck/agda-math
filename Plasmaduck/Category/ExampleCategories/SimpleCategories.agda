open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; Reveal_·_is_) renaming (refl to ≡-refl)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open import Relation.Binary using (Setoid)
open import Function using (flip)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)

open import Plasmaduck.SetoidExperiment.SetoidMachinery using (discrete-setoid; indiscrete-setoid)
open import Plasmaduck.Category.Category using (Category)
open import Plasmaduck.Function using (≈-isEquivalence)



module Plasmaduck.Category.ExampleCategories.SimpleCategories where

variable
    a b c α β γ ℓ₁ ℓ₂ ℓ₃ : Level

𝟘 : Category lzero lzero lzero
𝟘 = record {
    rawCategory = record {
        Object = ⊥;
        Morphism' = λ ();
        id = λ ();
        compose = λ {}
        };
    isCategory = record {
        assoc = λ {};
        id-is-left-id = λ {};
        id-is-right-id = λ {}
        }
    }

𝟙 : Category lzero lzero lzero
𝟙 = record {
    rawCategory = record {
        Object = ⊤;
        Morphism' = λ _ _ → discrete-setoid ⊤;
        id = λ _ → tt;
        compose = record {
            func = λ _ _ → tt;
            respects = λ _ _ → ≡-refl
            }
        };
    isCategory = record {
        assoc = λ _ _ _ → ≡-refl;
        id-is-left-id = ≡-refl;
        id-is-right-id = ≡-refl
        }
    }

𝐒𝐞𝐭 : (ℓ : Level) → Category (lsuc ℓ) ℓ ℓ
𝐒𝐞𝐭 ℓ = record {
    rawCategory = record {
        Object = Set ℓ;
        Morphism' = λ A B → record {
            Carrier = A → B;
            _≈_ = Plasmaduck.Function._≈_;
            isEquivalence = Plasmaduck.Function.≈-isEquivalence
            };
        id = λ A → Function.id;
        compose = record {
            func = λ g f → Function._∘_ g f;
            respects = λ {g₁} {g₂} {f₁} {f₂} g₁≈g₂ f₁≈f₂ x →
                g₁ (f₁ x)   ≡⟨ cong g₁ (f₁≈f₂ x) ⟩
                g₁ (f₂ x)   ≡⟨ g₁≈g₂ (f₂ x) ⟩
                g₂ (f₂ x)   ∎
            }
        };
    isCategory = record {
        assoc = λ _ _ _ _ → ≡-refl;
        id-is-left-id = λ _ → ≡-refl;
        id-is-right-id = λ _ → ≡-refl
        }
    }
    where open ≡-Reasoning

-- Also see make-net from Net.agda.
setoid-category : Setoid a b → Category a b lzero
setoid-category setoid = record {
    rawCategory = record {
        Object = setoid .Setoid.Carrier;
        Morphism' = λ A B → indiscrete-setoid (A ~ B);
        id = λ x → Setoid.refl setoid {x = x};
        compose = record { func = flip (Setoid.trans setoid) }
        };
    isCategory = record {}
    }
    where open Setoid setoid using () renaming (_≈_ to _~_)

discrete-category : Set a → Category a a lzero
discrete-category A = setoid-category (discrete-setoid A)
