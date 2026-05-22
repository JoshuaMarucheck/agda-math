open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Relation.Binary.PropositionalEquality using (_≡_) renaming (refl to ≡-refl)
open import Relation.Binary using (Setoid; Rel; IsEquivalence)
open import Function using (Congruent)
open import Data.Product using (_×_; _,_)

open import Plasmaduck.Category.Category using (Category; Functor)
open import Plasmaduck.Util.Case using (case_of_)
open import Plasmaduck.Category.Functor.SimpleFunctors using (id-functor)
open import Plasmaduck.Category.Functor.Properties using (FunctorSetoid; Functor-compose-func)



module Plasmaduck.Category.ExampleCategories.Cat where

variable
    a b c α β γ ℓ₁ ℓ₂ ℓ₃ : Level

𝐂𝐚𝐭 : (α β γ : Level) → Category (lsuc α ⊔ lsuc β ⊔ lsuc γ) (α ⊔ β ⊔ γ) (α ⊔ β ⊔ γ)
𝐂𝐚𝐭 α β γ = record {
    rawCategory = record {
        Object = Category α β γ;
        Morphism' = FunctorSetoid;
        id = id-functor;
        compose = Functor-compose-func
        };
    isCategory = record {
        assoc = λ {𝔸} {𝔹} {ℂ} {𝔻} H G F → (λ _ → ≡-refl) , (λ {X} {Y} f → Category.~-refl 𝔻);
        id-is-left-id = λ {𝔸} {𝔹} {F} → (λ _ → ≡-refl) , (λ {X} {Y} f → Category.~-refl 𝔹);
        id-is-right-id = λ {𝔸} {𝔹} {F} → (λ _ → ≡-refl) , (λ {X} {Y} f → Category.~-refl 𝔹)
        }
    }
