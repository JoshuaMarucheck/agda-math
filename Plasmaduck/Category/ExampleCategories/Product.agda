open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; Reveal_·_is_) renaming (refl to ≡-refl)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open import Relation.Binary using (Setoid)
open import Function using (flip)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (_,_) renaming (_×_ to _×-set_)

open import Plasmaduck.SetoidExperiment.SetoidMachinery using (discrete-setoid; indiscrete-setoid; ×-setoid; SetoidFunctionSetoid; SetoidFunction) renaming (_∘'_ to _∘-setoid_)
open import Plasmaduck.Category.Category using (Category; Functor)
open import Plasmaduck.Function using (≈-isEquivalence)



module Plasmaduck.Category.ExampleCategories.Product where

variable
    a b c α β γ ℓ₁ ℓ₂ ℓ₃ l₁ l₂ l₃ : Level


_×_ : Category a b c → Category α β γ → Category (a ⊔ α) (b ⊔ β) (c ⊔ γ)
_×_ 𝔸 𝔹 = record {
    rawCategory = record {
        Object = Category.Object 𝔸 ×-set Category.Object 𝔹;
        Morphism' = λ (X₁ , Y₁) (X₂ , Y₂) → ×-setoid (Category.Morphism' 𝔸 X₁ X₂) (Category.Morphism' 𝔹 Y₁ Y₂);
        id = λ (X , Y) → Category.id 𝔸 X , Category.id 𝔹 Y;
        compose = record {
            func = λ (f₁ , g₁) (f₂ , g₂) → Category._∘_ 𝔸 f₁ f₂ , Category._∘_ 𝔹 g₁ g₂;
            respects = λ (f₁ , g₁) (f₂ , g₂) → Category.∘-respects 𝔸 f₁ f₂ , Category.∘-respects 𝔹 g₁ g₂
            }
        };
    isCategory = record {
        assoc = λ (f₁ , g₁) (f₂ , g₂) (f₃ , g₃) → Category.assoc 𝔸 f₁ f₂ f₃ , Category.assoc 𝔹 g₁ g₂ g₃;
        id-is-left-id = Category.id-is-left-id 𝔸 , Category.id-is-left-id 𝔹;
        id-is-right-id = Category.id-is-right-id 𝔸 , Category.id-is-right-id 𝔹
        }
    }
infix 30 _×_

×-functor : 
    {𝔸 : Category a b c} {𝔹 : Category α β γ} {ℂ : Category ℓ₁ ℓ₂ ℓ₃} {𝔻 : Category l₁ l₂ l₃} →
    Functor 𝔸 ℂ →
    Functor 𝔹 𝔻 →
    Functor (𝔸 × 𝔹) (ℂ × 𝔻)
×-functor F G = record {
    rawFunctor = record {
        mapₒ = λ (X , Y) → Functor.mapₒ F X , Functor.mapₒ G Y;
        mapₘ-func = record {
            func = λ (f , g) → Functor.mapₘ F f , Functor.mapₘ G g;
            respects = λ (f₁~f₂ , g₁~g₂) → Functor.mapₘ-respects F f₁~f₂ , Functor.mapₘ-respects G g₁~g₂
            }
        };
    isFunctor = record {
        consistent-on-id = Functor.consistent-on-id F , Functor.consistent-on-id G;
        consistent-on-∘ = λ (f₂ , g₂) (f₁ , g₁) → Functor.consistent-on-∘ F f₂ f₁ , Functor.consistent-on-∘ G g₂ g₁
        }
    }

restrict-bifunctor-left :
    {𝔸 : Category a b c} {𝔹 : Category α β γ} {ℂ : Category ℓ₁ ℓ₂ ℓ₃} →
    Functor (𝔸 × 𝔹) ℂ →
    Category.Object 𝔹 →
    Functor 𝔸 ℂ
restrict-bifunctor-left {𝔸 = 𝔸} {𝔹} {ℂ} F Y = record {
    rawFunctor = record {
        mapₒ = λ X → Functor.mapₒ F (X , Y);
        mapₘ-func = record {
            func = λ f → Functor.mapₘ F (f , Category.id 𝔹 Y);
            respects = λ f~g → Functor.mapₘ-respects F (f~g , Category.~-refl 𝔹)
            }
        };
    isFunctor = record {
        consistent-on-id = Functor.consistent-on-id F;
        consistent-on-∘ = λ g f → begin
            Functor.mapₘ F (g ∘₁ f , Category.id 𝔹 Y)                                       ≈⟨ Functor.mapₘ-respects F (Category.~-refl 𝔸 , Category.~-sym 𝔹 (Category.id-is-left-id 𝔹)) ⟩
            Functor.mapₘ F (g ∘₁ f , Category.id 𝔹 Y ∘₂ Category.id 𝔹 Y)                    ≈⟨ Functor.consistent-on-∘ F (g , Category.id 𝔹 Y) (f , Category.id 𝔹 Y) ⟩
            Functor.mapₘ F (g , Category.id 𝔹 Y) ∘ Functor.mapₘ F (f , Category.id 𝔹 Y)     ∎
        }
    }
    where
        open Category 𝔸 using () renaming (_∘_ to _∘₁_)
        open Category 𝔹 using () renaming (_∘_ to _∘₂_)
        open Category ℂ using (_∘_)

        module _ {X Y : Category.Object ℂ} where
            open import Relation.Binary.Reasoning.Setoid (Category.Morphism' ℂ X Y) public

restrict-bifunctor-right :
    {𝔸 : Category a b c} {𝔹 : Category α β γ} {ℂ : Category ℓ₁ ℓ₂ ℓ₃} →
    Functor (𝔸 × 𝔹) ℂ →
    Category.Object 𝔸 →
    Functor 𝔹 ℂ
restrict-bifunctor-right {𝔸 = 𝔸} {𝔹} {ℂ} F X = record {
    rawFunctor = record {
        mapₒ = λ Y → Functor.mapₒ F (X , Y);
        mapₘ-func = record {
            func = λ f → Functor.mapₘ F (Category.id 𝔸 X , f);
            respects = λ f~g → Functor.mapₘ-respects F (Category.~-refl 𝔸 , f~g)
            }
        };
    isFunctor = record {
        consistent-on-id = Functor.consistent-on-id F;
        consistent-on-∘ = λ g f → begin
            Functor.mapₘ F (Category.id 𝔸 X , g ∘₂ f)                                       ≈⟨ Functor.mapₘ-respects F (Category.~-sym 𝔸 (Category.id-is-left-id 𝔸) , Category.~-refl 𝔹) ⟩
            Functor.mapₘ F (Category.id 𝔸 X ∘₁ Category.id 𝔸 X , g ∘₂ f)                    ≈⟨ Functor.consistent-on-∘ F (Category.id 𝔸 X , g) (Category.id 𝔸 X , f) ⟩
            Functor.mapₘ F (Category.id 𝔸 X , g) ∘ Functor.mapₘ F (Category.id 𝔸 X , f)     ∎
        }
    }
    where
        open Category 𝔸 using () renaming (_∘_ to _∘₁_)
        open Category 𝔹 using () renaming (_∘_ to _∘₂_)
        open Category ℂ using (_∘_)

        module _ {X Y : Category.Object ℂ} where
            open import Relation.Binary.Reasoning.Setoid (Category.Morphism' ℂ X Y) public
