open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc; zero to lzero)
open import Relation.Nullary using (Dec; yes; no)


module Plasmaduck.Property.Defs where

open import Plasmaduck.Relation.Defs using (CongruentProperty) public

variable
    a ℓ ℓ₁ : Level

module _
    {A : Set a}
    (P : A → Set ℓ₁)
    where

    DecidableProperty : Set (a ⊔ ℓ₁)
    DecidableProperty = ∀ x → Dec (P x)
