open import Level using (Level; _⊔_)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary using (Decidable)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)

open import Plasmaduck.SetoidExperiment.SetoidMachinery using (property-subset-setoid)



module Plasmaduck.Relation.Decidable where

variable
    c ℓ ℓ₁ : Level

module _ (A-setoid : Setoid c ℓ) where
    private
        A = A-setoid .Setoid.Carrier
        _~_ = A-setoid .Setoid._≈_

    decidable-push : Decidable _~_ → {P : A → Set ℓ₁} → Decidable ((property-subset-setoid A-setoid P) .Setoid._≈_)
    decidable-push _~?_ = λ x y → x .proj₁ ~? y .proj₁
