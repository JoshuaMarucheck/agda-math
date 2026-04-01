open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc; zero to lzero)
open import Relation.Nullary using (Dec; yes; no)
open import Data.Product using (Σ)


module Plasmaduck.Property.Defs where

open import Plasmaduck.Relation.Defs using (CongruentProperty) public

variable
    a ℓ₁ ℓ₂ : Level

module _
    {A : Set a}
    (P : A → Set ℓ₁)
    where

    DecidableProperty : Set (a ⊔ ℓ₁)
    DecidableProperty = ∀ x → Dec (P x)

    any-type : Set (a ⊔ ℓ₁)
    any-type = Σ A λ x → P x

    all-type : Set (a ⊔ ℓ₁)
    all-type = ∀ x → P x

_Extends_ :
    {A : Set a}
    (P : A → Set ℓ₁)
    (Q : A → Set ℓ₂)
    → Set (a ⊔ ℓ₁ ⊔ ℓ₂)
P Extends Q = ∀ {x} → Q x → P x
