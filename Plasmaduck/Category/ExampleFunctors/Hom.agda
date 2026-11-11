open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc; zero to lzero)
import Function
open import Data.Product using (_×_; _,_)
open import Relation.Binary using (Setoid; IsEquivalence)

open import Plasmaduck.Category.Category using (RawCategory; Category; RawFunctor; Functor; ContravariantFunctor; opposite-category)
open import Plasmaduck.Category.ExampleCategories.SimpleCategories using (𝟙; 𝐒𝐞𝐭𝐨𝐢𝐝) 
open import Plasmaduck.Category.ExampleCategories.Product using (restrict-bifunctor-left; restrict-bifunctor-right) renaming (_×_ to _×-category_)

open import Plasmaduck.SetoidExperiment.SetoidMachinery using (SetoidFunction₂)



module Plasmaduck.Category.ExampleFunctors.Hom where

variable
    a b c α β γ ℓ₁ ℓ₂ ℓ₃ : Level


-- Since I'm using morphism setoids,
-- this functor needs to go to the category of setoids,
-- rather than to the category of sets
Hom : (ℂ : Category a b c) → Functor (opposite-category ℂ ×-category ℂ) (𝐒𝐞𝐭𝐨𝐢𝐝 b c)
Hom ℂ = record {
    rawFunctor = record {
        mapₒ = λ (X , Y) → Category.Morphism' ℂ X Y;
        mapₘ-func = λ {X} {Y} → record {
            func = λ (f₁ , f₂) → record {
                func = λ g → f₂ ∘ g ∘ f₁;
                respects = λ {f} {g} f~g → ∘-respects ~-refl (∘-respects f~g ~-refl)
                };
            respects = λ {(f₁ , f₂)} {(g₁ , g₂)} (f₁≈g₁ , f₂≈g₂) h₁≈h₂ → ∘-respects f₂≈g₂ (∘-respects h₁≈h₂ f₁≈g₁)
            }
        };
    isFunctor = record {
        consistent-on-id = λ {(X , Y)} {f} {g} → ~-trans (~-trans (Category.id-is-left-id ℂ) (Category.id-is-right-id ℂ));
        consistent-on-∘ = consistent-on-∘-pf
        }
    }
    where
        open Category ℂ using (_∘_; _~_; assoc; ∘-respects; ~-refl; ~-sym; ~-trans)
        module _ {X Y : Category.Object ℂ} where
            open import Relation.Binary.Reasoning.Setoid (Category.Morphism' ℂ X Y) public
        consistent-on-∘-pf :
            {X@(X₁ , X₂) Y@(Y₁ , Y₂) Z@(Z₁ , Z₂) : Category.Object (opposite-category ℂ ×-category ℂ)}
            ((g₁ , g₂) : Category.Morphism (opposite-category ℂ ×-category ℂ) Y Z)
            ((f₁ , f₂) : Category.Morphism (opposite-category ℂ ×-category ℂ) X Y) →
            {h₁ h₂ : Category.Morphism ℂ X₁ X₂} →
            h₁ ~ h₂ →
            (g₂ ∘ f₂) ∘ (h₁ ∘ (f₁ ∘ g₁)) ~ g₂ ∘ ((f₂ ∘ (h₂ ∘ f₁)) ∘ g₁)
        consistent-on-∘-pf (g₁ , g₂) (f₁ , f₂) {h₁} {h₂} h₁~h₂ = begin
            (g₂ ∘ f₂) ∘ (h₁ ∘ (f₁ ∘ g₁))    ≈⟨ assoc g₂ f₂ (h₁ ∘ f₁ ∘ g₁) ⟩
            g₂ ∘ (f₂ ∘ (h₁ ∘ (f₁ ∘ g₁)))    ≈⟨ ∘-respects ~-refl (∘-respects ~-refl (~-sym (assoc h₁ f₁ g₁))) ⟩
            g₂ ∘ (f₂ ∘ ((h₁ ∘ f₁) ∘ g₁))    ≈⟨ ∘-respects ~-refl (~-sym (assoc f₂ (h₁ ∘ f₁) g₁)) ⟩
            g₂ ∘ ((f₂ ∘ (h₁ ∘ f₁)) ∘ g₁)    ≈⟨ ∘-respects ~-refl (∘-respects (∘-respects ~-refl (∘-respects h₁~h₂ ~-refl)) ~-refl) ⟩
            g₂ ∘ ((f₂ ∘ (h₂ ∘ f₁)) ∘ g₁)    ∎

-- Hom_ℂ (X , -)
Hom₁ : (ℂ : Category a b c) → Category.Object ℂ → Functor ℂ (𝐒𝐞𝐭𝐨𝐢𝐝 b c)
Hom₁ ℂ X = restrict-bifunctor-right (Hom ℂ) X

-- Hom_ℂ (- , Y)
Hom₂ : (ℂ : Category a b c) → Category.Object ℂ → ContravariantFunctor ℂ (𝐒𝐞𝐭𝐨𝐢𝐝 b c)
Hom₂ ℂ Y = restrict-bifunctor-left (Hom ℂ) Y
