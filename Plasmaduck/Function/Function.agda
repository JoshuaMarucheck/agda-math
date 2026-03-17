open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc; zero to lzero)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)


module Plasmaduck.Function.Function where

variable
    a b : Level

_↔_ : Set a → Set b → Set (a ⊔ b)
A ↔ B = (A → B) × (B → A)