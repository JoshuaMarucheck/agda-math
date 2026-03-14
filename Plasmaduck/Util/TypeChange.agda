open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; inspect; cong; Reveal_·_is_; [_]; refl; sym; trans)


module Plasmaduck.Util.TypeChange where
variable
    ℓ : Level

-- For when you need to tell the type checker that yes, these two types really are equal!
change-type : {A B : Set ℓ} → (A ≡ B) → (x : A) → B
change-type refl x = x
