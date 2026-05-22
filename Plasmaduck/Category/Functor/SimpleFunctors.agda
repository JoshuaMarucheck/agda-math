open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc; zero to lzero)
import Function

open import Plasmaduck.Category.Category using (Category; Functor)
open import Plasmaduck.Category.ExampleCategories.SimpleCategories using (𝟙)



module Plasmaduck.Category.Functor.SimpleFunctors where

variable
    a b c α β γ ℓ₁ ℓ₂ ℓ₃ : Level

module ObjectPicker (ℂ : Category a b c) where
    open Category ℂ using (Object; id; ~-refl; ~-sym; ~-trans)

    object-picker : Object → Functor 𝟙 ℂ
    object-picker X = record {
        rawFunctor = record {
            mapₒ = λ _ → X;
            mapₘ-func = record {
                func = λ _ → id X;
                respects = λ _ → ~-refl
                }
            };
        isFunctor = record {
            consistent-on-id = ~-refl;
            consistent-on-∘ = λ g f → ~-sym (Category.id-is-left-id ℂ)
            }
        }

id-functor : (ℂ : Category a b c) → Functor ℂ ℂ
id-functor ℂ = record {
    rawFunctor = record {
        mapₒ = Function.id;
        mapₘ-func = record {
            func = Function.id;
            respects = Function.id
            }
        };
    isFunctor = record {
        consistent-on-id = Category.~-refl ℂ;
        consistent-on-∘ = λ g f → Category.~-refl ℂ
        }
    }

constant-functor : (ℂ : Category a b c) → ℂ .Category.Object → Functor ℂ ℂ
constant-functor ℂ X = record {
    rawFunctor = record {
        mapₒ = λ _ → X;
        mapₘ-func = record {
            func = λ _ → Category.id ℂ X;
            respects = λ z → Category.~-refl ℂ
            }
        };
    isFunctor = record {
        consistent-on-id = Category.~-refl ℂ;
        consistent-on-∘ = λ g f → Category.~-sym ℂ (Category.id-is-left-id ℂ)
        }
    }