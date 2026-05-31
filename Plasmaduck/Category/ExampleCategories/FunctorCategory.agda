open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Relation.Binary.PropositionalEquality using (_≡_) renaming (refl to ≡-refl)
open import Relation.Binary using (Setoid; Rel; IsEquivalence)
open import Function using (Congruent)
open import Data.Product using (_×_; _,_)
open import Data.Bool using (Bool; true; false)

open import Plasmaduck.SetoidExperiment.SetoidMachinery using (SetoidFunction₂)
open import Plasmaduck.Category.Category using (Category; Functor; opposite-category; opposite-functor; IsSidedInverse)
open import Plasmaduck.Category.ExampleCategories.SimpleCategories using (discrete-category)
open import Plasmaduck.Category.Functor.SimpleFunctors using (id-functor; constant-functor)
open import Plasmaduck.Category.Functor.NaturalTransformation using (NaturalTransformation; NaturalTransformationSetoid) renaming (_≈_ to _≈-NaturalTransformation_; ≈-eq to ≈-NaturalTransformation-eq; id to id-NaturalTransformation; compose-func to NaturalTransformation-compose-func; ∘-assoc to ∘-NaturalTransformation-assoc; ∘-left-id to ∘-NaturalTransformation-left-id; ∘-right-id to ∘-NaturalTransformation-right-id)
open import Plasmaduck.Category.Functor.Properties using (FunctorSetoid; Functor-compose-func)
open import Plasmaduck.Function.Properties using (ExplicitlyCongruent; Congruent₂)
open import Plasmaduck.Util.Case using (case_of_)



module Plasmaduck.Category.ExampleCategories.FunctorCategory where

variable
    a b c α β γ ℓ₁ ℓ₂ ℓ₃ : Level

open Functor using (mapₒ; mapₘ)

-- Functors from 𝔸 to 𝔹
FunctorCategory : (𝔸 : Category a b c) (𝔹 : Category α β γ) → Category (a ⊔ b ⊔ c ⊔ α ⊔ β ⊔ γ) (a ⊔ b ⊔ β ⊔ γ) (a ⊔ γ)
FunctorCategory 𝔸 𝔹 = record {
    rawCategory = record {
        Object = Functor 𝔸 𝔹;
        Morphism' = NaturalTransformationSetoid;
        id = id-NaturalTransformation;
        compose = NaturalTransformation-compose-func
        };
    isCategory = record {
        assoc = λ {w} {x} {y} {z} h g f X → Category.~-sym 𝔹 (∘-NaturalTransformation-assoc h g f X);
        id-is-left-id = λ {x} {y} {f} X → ∘-NaturalTransformation-left-id f X;
        id-is-right-id = λ {x} {y} {f} X → ∘-NaturalTransformation-right-id f X
        }
    }

_^_ : Category a b c → Category α β γ → Category _ _ _
_^_ = Function.flip FunctorCategory
infixr 45 _^_

-- Diagonal functor
Δ : (𝔸 : Category a b c) (𝔹 : Category α β γ) → Functor 𝔹 (𝔹 ^ 𝔸)
Δ 𝔸 𝔹 = record {
    rawFunctor = record {
        mapₒ = λ X → constant-functor 𝔸 𝔹 X;
        mapₘ-func = record {
            func = λ f → record {
                η = λ X → f;
                commutes = λ _ → Category.~-trans 𝔹 (Category.id-is-right-id 𝔹) (Category.~-sym 𝔹 (Category.id-is-left-id 𝔹))
                };
            respects = λ z X → z
            }
        };
    isFunctor = record {
        consistent-on-id = λ _ → Category.~-refl 𝔹;
        consistent-on-∘ = λ g f X → Category.~-refl 𝔹
        }
    }

-------------------------------
--- Some Example Categories ---
-------------------------------

product-category : (ℂ : Category a b c) → Category (a ⊔ b ⊔ c) (b ⊔ c) c
product-category ℂ = FunctorCategory (discrete-category Bool) ℂ

