open import Level using (Level; _⊔_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary using (Rel; IsEquivalence; Decidable)
open import Relation.Binary.Bundles using (Setoid)

module Plasmaduck.Relation.Defs {a ℓ : Level} (A-setoid : Setoid a ℓ) where

variable
    ℓ₂ : Level

open Setoid using (Carrier)

private
    A = A-setoid .Carrier
    _≈_ = A-setoid .Setoid._≈_

-- Congruent wrt the ambient equality relation, which is necessary for some of the proofs
CongruentRel : Rel A ℓ₂ → Set (a ⊔ ℓ ⊔ ℓ₂)
CongruentRel _~_ = ∀ {x₁ x₂ y₁ y₂ : A} → (x₁ ≈ x₂) → (y₁ ≈ y₂) → (x₁ ~ y₁) → (x₂ ~ y₂)

CongruentProperty : (A → Set ℓ₂) → Set (a ⊔ ℓ ⊔ ℓ₂)
CongruentProperty P = ∀ {x y : A} → x ≈ y → P x → P y

rel-property : {_~_ : Rel A ℓ₂} → CongruentRel _~_ → (x : A) → CongruentProperty (x ~_)
rel-property ~-cong _ = ~-cong (A-setoid .Setoid.isEquivalence .IsEquivalence.refl)
