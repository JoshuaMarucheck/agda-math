open import Level using (Level)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)



module Plasmaduck.Data.PropositionalEquality where

variable
    a : Level
    A : Set a

≡-proof-unique : {x y : A} → {p₁ p₂ : x ≡ y} → p₁ ≡ p₂
≡-proof-unique {x = x} {.x} {refl} {refl} = refl
