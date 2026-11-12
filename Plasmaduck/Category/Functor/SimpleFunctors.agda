open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc; zero to lzero)
import Function
open import Data.Product using (_×_; _,_)
open import Relation.Binary using (Setoid; IsEquivalence)

open import Plasmaduck.Category.Category using (RawCategory; Category; RawFunctor; Functor; ContravariantFunctor; opposite-category)
open import Plasmaduck.Category.ExampleCategories.SimpleCategories using (𝟙; 𝐒𝐞𝐭𝐨𝐢𝐝)

open import Plasmaduck.SetoidExperiment.SetoidMachinery using (SetoidFunction₂)



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

id-raw-functor : (ℂ : RawCategory a b c) → RawFunctor ℂ ℂ
id-raw-functor ℂ = record {
    mapₒ = Function.id;
    mapₘ-func = record {
        func = Function.id;
        respects = Function.id
        }
    }

id-raw-functor' : (ℂ : Category a b c) → RawFunctor (ℂ .Category.rawCategory) (ℂ .Category.rawCategory)
id-raw-functor' ℂ = id-raw-functor (ℂ .Category.rawCategory)

id-functor : (ℂ : Category a b c) → Functor ℂ ℂ
id-functor ℂ = record {
    rawFunctor = id-raw-functor' ℂ;
    isFunctor = record {
        consistent-on-id = Category.~-refl ℂ;
        consistent-on-∘ = λ g f → Category.~-refl ℂ
        }
    }

constant-functor : (𝔸 : Category a b c) (𝔹 : Category α β γ) → 𝔹 .Category.Object → Functor 𝔸 𝔹
constant-functor 𝔸 𝔹 X = record {
    rawFunctor = record {
        mapₒ = λ _ → X;
        mapₘ-func = record {
            func = λ _ → Category.id 𝔹 X;
            respects = λ z → Category.~-refl 𝔹
            }
        };
    isFunctor = record {
        consistent-on-id = Category.~-refl 𝔹;
        consistent-on-∘ = λ g f → Category.~-sym 𝔹 (Category.id-is-left-id 𝔹)
        }
    }
