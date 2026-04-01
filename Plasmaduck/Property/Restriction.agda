open import Level using (Level; _⊔_)
open import Function using (_∘_; id; Congruent; Bijection; Injective; Surjective)
open import Relation.Binary using (Rel; IsEquivalence; Decidable)
open import Relation.Binary.Bundles using (Setoid)
open import Data.Product using (Σ; _,_; proj₁; proj₂)

open import Plasmaduck.Property.Defs using (DecidableProperty; CongruentProperty; _Extends_)
open import Plasmaduck.Relation.Defs using (CongruentRel)
open import Plasmaduck.SetoidExperiment.SetoidMachinery using (property-subset-setoid)


module Plasmaduck.Property.Restriction where

variable
    ℓ₁ ℓ₂ : Level

open Setoid using (Carrier; _≈_)


module _
    {a ℓ : Level} (A-setoid : Setoid a ℓ)
    where

    private
        A = A-setoid .Carrier

    restrict-property : (P : A → Set ℓ₁) (Q : A → Set ℓ₂) → property-subset-setoid A-setoid P .Carrier → Set ℓ₂
    restrict-property _ Q = Q ∘ proj₁

module _
    {a ℓ : Level} (A-setoid : Setoid a ℓ)
    where

    private
        A = A-setoid .Carrier

    -- tbh this one doesn't work terribly well, for reasons I don't understand.
    -- Just use Q-cong directly.
    -- When this is used, it can't find the proof term for something in property-subset-setoid A-setoid P
    --   where the proof term doesn't matter and immediately vanishes,
    --   and would have been picked up temporarily from another source it can't find automatically.
    restrict-property-cong :
        (P : A → Set ℓ₁) →
        {Q : A → Set ℓ₂} → CongruentProperty A-setoid Q →
        CongruentProperty (property-subset-setoid A-setoid P) (restrict-property A-setoid P Q)
    restrict-property-cong _ {Q} Q-cong = Q-cong

    restrict-property-dec :
        (P : A → Set ℓ₁) →
        {Q : A → Set ℓ₂} → DecidableProperty Q →
        DecidableProperty (restrict-property A-setoid P Q)
    restrict-property-dec _ {Q} P-dec = P-dec ∘ proj₁

    restrict-lift :
        (P : A → Set ℓ₁) →
        (Q : A → Set ℓ₂) →
        {x : A} → {P[x] : P x} → restrict-property A-setoid P Q (x , P[x]) →
        Q x
    restrict-lift P Q {x} Qr[x] = Qr[x]

    restrict-collapse :
        (P : A → Set ℓ₁) →
        (Q : A → Set ℓ₂) →
        P Extends Q →
        Bijection (property-subset-setoid (property-subset-setoid A-setoid P) (restrict-property A-setoid P Q)) (property-subset-setoid A-setoid Q)
    restrict-collapse P Q Q→P = record {
        to = to;
        cong = λ {x} {y} x≈y → x≈y;
        bijective = (λ {x} {y} x≈y → x≈y) , to-surjective
        }
        where
            B-setoid = property-subset-setoid (property-subset-setoid A-setoid P) (restrict-property A-setoid P Q)
            C-setoid = property-subset-setoid A-setoid Q

            B = B-setoid .Carrier
            C = C-setoid .Carrier

            to : B → C
            to ((x , P[x]) , Q[x]) = (x , Q[x])

            to-surjective : Surjective (B-setoid ._≈_) (C-setoid ._≈_) to
            to-surjective = λ y →
                ((y .proj₁ , Q→P (y .proj₂)) , y .proj₂) ,
                (λ {z} z₁ → z₁)
