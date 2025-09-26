open import Level using (Level; _⊔_) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_)


module Plasmaduck.Function where

_≈_ : {α β : Level} {A : Set α} {B : Set β} → (f g : A → B) → Set (α ⊔ β)
_≈_ f g = ∀ x → f x ≡ g x
infix 1 _≈_