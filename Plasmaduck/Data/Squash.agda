open import Level using (Level)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary using (Irrelevant)



module Plasmaduck.Data.Squash where

variable
    ℓ : Level

data Squash (A : Set ℓ) : Set ℓ where
    squash : .A → Squash A

squash-irrelevant : ∀ {A : Set ℓ} → Irrelevant (Squash A)
squash-irrelevant (squash p₁) (squash p₂) = refl
