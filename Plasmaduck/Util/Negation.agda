open import Level using (Level; _⊔_; Lift; lift; Setω) renaming (suc to lsuc; zero to lzero)
open import Relation.Nullary.Negation using (¬_)


module Plasmaduck.Util.Negation where

variable
    a : Level
    A : Set a

¬¬-lift : A → ¬ ¬ A
¬¬-lift x ¬x = ¬x x
