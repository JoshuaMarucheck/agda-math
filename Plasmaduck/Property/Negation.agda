open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc; zero to lzero)

open import Function using (_∘_; id)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary using (IsEquivalence)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Nullary using (Dec; yes; no)

open import Plasmaduck.Property.Defs using (DecidableProperty; CongruentProperty)
open import Plasmaduck.Util.Negation using (¬¬-lift)



module Plasmaduck.Property.Negation where

variable
    a ℓ ℓ₁ : Level


module _
    (setoid : Setoid a ℓ)
    (P : setoid .Setoid.Carrier → Set ℓ₁)
    where

    open IsEquivalence (setoid .Setoid.isEquivalence) using (refl; sym; trans)

    negate-property : setoid .Setoid.Carrier → Set ℓ₁
    negate-property = ¬_ ∘ P

    negation-dec : DecidableProperty P → DecidableProperty negate-property
    negation-dec dec x with dec x
    ... | yes pf = no (¬¬-lift pf)
    ... | no pf = yes pf

    negation-cong : CongruentProperty setoid P → CongruentProperty setoid negate-property
    negation-cong cong x≈y ¬P[x] P[y] = ¬P[x] (cong (sym x≈y) P[y])
