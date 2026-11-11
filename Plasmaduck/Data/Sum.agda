open import Level using (Level)
open import Data.Empty using (⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)



module Plasmaduck.Data.Sum where

variable
    α β : Level
    A : Set α
    B : Set β

⊎-force₁ : A ⊎ B → ¬ B → A
⊎-force₁ (inj₁ a) ¬B = a
⊎-force₁ (inj₂ b) ¬B = ⊥-elim (¬B b)

⊎-force₂ : A ⊎ B → ¬ A → B
⊎-force₂ (inj₁ a) ¬A = ⊥-elim (¬A a)
⊎-force₂ (inj₂ b) ¬A = b
