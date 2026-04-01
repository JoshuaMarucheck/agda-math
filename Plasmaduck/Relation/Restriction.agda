open import Level using (Level; _⊔_)
open import Relation.Binary using (Rel; IsEquivalence; Decidable)
open import Relation.Binary.Bundles using (Setoid)
open import Data.Product using (Σ; _,_; proj₁; proj₂)

open import Plasmaduck.Property.Defs using (DecidableProperty; CongruentProperty)
open import Plasmaduck.Relation.Defs using (CongruentRel)
open import Plasmaduck.SetoidExperiment.SetoidMachinery using (property-subset-setoid)



module Plasmaduck.Relation.Restriction where

variable
    ℓ₁ ℓ₂ : Level

open Setoid using (Carrier)


module _
    {a ℓ : Level} (A-setoid : Setoid a ℓ)
    where

    private
        A = A-setoid .Carrier

    restrict-relation : (P : A → Set ℓ₁) → (_~_ : Rel A ℓ₂) → Rel (property-subset-setoid A-setoid P .Carrier) ℓ₂
    restrict-relation _ _~_ (x , _) (y , _) = x ~ y

module _
    {a ℓ : Level} (A-setoid : Setoid a ℓ)
    where

    private
        A = A-setoid .Carrier

    restrict-relation-cong :
        (P : A → Set ℓ₁) →
        {_~_ : Rel A ℓ₂} → CongruentRel A-setoid  _~_ →
        CongruentRel (property-subset-setoid A-setoid P) (restrict-relation A-setoid P _~_)
    restrict-relation-cong _ {_~_} ~-cong = ~-cong

    restrict-relation-dec :
        (P : A → Set ℓ₁) →
        {_~_ : Rel A ℓ₂} → Decidable  _~_ →
        Decidable (restrict-relation A-setoid P _~_)
    restrict-relation-dec _ {_~_} ~-dec x y = ~-dec (x .proj₁) (y .proj₁)
