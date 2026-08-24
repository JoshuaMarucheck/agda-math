open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≢_)
import Relation.Binary as Binary
open import Relation.Nullary as Nullary using (¬_)
open import Data.Empty using (⊥; ⊥-elim)



module Plasmaduck.Data.Empty where

variable
    α : Level
    A : Set α

⊥-irr-elim : .⊥ → A
⊥-irr-elim ()

⊥-recompute : Nullary.Recomputable ⊥
⊥-recompute ()

¬-recompute : Nullary.Recomputable (¬ A)
¬-recompute ¬A x = ⊥-recompute (¬A x)

≢-recompute : Binary.Recomputable (_≢_ {A = A})
≢-recompute = ¬-recompute
