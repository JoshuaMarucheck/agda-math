open import Level using (Level; _⊔_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary using (Rel; IsEquivalence; Decidable; _Respects₂_)
open import Relation.Binary.Bundles using (Setoid)
open import Data.Product using (_,_)

module Plasmaduck.Relation.Defs {a ℓ : Level} (A-setoid : Setoid a ℓ) where

variable
    ℓ₂ : Level

open Setoid using (Carrier)
open IsEquivalence (A-setoid .Setoid.isEquivalence) using (refl; sym; trans)

private
    A = A-setoid .Carrier
    _≈_ = A-setoid .Setoid._≈_

-- Congruent wrt the ambient equality relation, which is necessary for some of the proofs
CongruentRel : Rel A ℓ₂ → Set (a ⊔ ℓ ⊔ ℓ₂)
CongruentRel _~_ = ∀ {x₁ x₂ y₁ y₂ : A} → (x₁ ≈ x₂) → (y₁ ≈ y₂) → (x₁ ~ y₁) → (x₂ ~ y₂)

CongruentProperty : (A → Set ℓ₂) → Set (a ⊔ ℓ ⊔ ℓ₂)
CongruentProperty P = ∀ {x y : A} → x ≈ y → P x → P y

rel-property : {_~_ : Rel A ℓ₂} → CongruentRel _~_ → (x : A) → CongruentProperty (x ~_)
rel-property ~-cong _ = ~-cong refl

-- Oops, it turns out CongruentProperty is (essentially) the same as _Respects₂_
respects→cong-rel : {_~_ : Rel A ℓ₂} → _~_ Respects₂ _≈_ → CongruentRel _~_
respects→cong-rel (~-resp-≈₁ , ~-resp-≈₂) x₁≈x₂ y₁≈y₂ x₁~y₁ = ~-resp-≈₂ x₁≈x₂ (~-resp-≈₁ y₁≈y₂ x₁~y₁)

cong-rel→respects : {_~_ : Rel A ℓ₂} → CongruentRel _~_ → _~_ Respects₂ _≈_
cong-rel→respects ~-cong =
    (λ y₁≈y₂ → ~-cong refl y₁≈y₂) ,
    (λ x₁≈x₂ → ~-cong x₁≈x₂ refl)
