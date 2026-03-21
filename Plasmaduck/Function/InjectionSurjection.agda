open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc; zero to lzero)

open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Function using (Bijective; Injective; Surjective; Congruent; Bijection; _∘_; id)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary using (IsEquivalence)

open import Plasmaduck.SetoidExperiment.SetoidMachinery using (⊎-setoid; ⊎-rel; rel₁; rel₂; ×-setoid; ×-rel; discrete-setoid; from-discrete-cong)


module Plasmaduck.Function.InjectionSurjection
    {a b ℓ₁ ℓ₂ : Level}
    (A-setoid : Setoid a ℓ₁) (B-setoid : Setoid b ℓ₂)
    (f : A-setoid .Setoid.Carrier → B-setoid .Setoid.Carrier)
    (f-cong : Congruent (A-setoid .Setoid._≈_) (B-setoid .Setoid._≈_) f)
    where

open Setoid using (Carrier; isEquivalence)
A = A-setoid .Carrier
B = B-setoid .Carrier

_~_ = A-setoid .Setoid._≈_
_≈_ = B-setoid .Setoid._≈_

~-refl = A-setoid .isEquivalence .IsEquivalence.refl
~-sym = A-setoid .isEquivalence .IsEquivalence.sym
~-trans = A-setoid .isEquivalence .IsEquivalence.trans

≈-refl = B-setoid .isEquivalence .IsEquivalence.refl
≈-sym = B-setoid .isEquivalence .IsEquivalence.sym
≈-trans = B-setoid .isEquivalence .IsEquivalence.trans


LeftInverse : (g : B → A) → Set (a ⊔ ℓ₁)
LeftInverse g = ∀ {x : A} → g (f x) ~ x

RightInverse : (g : B → A) → Set (b ⊔ ℓ₂)
RightInverse g = ∀ {y : B} → f (g y) ≈ y

BothInverse : (g : B → A) → Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂)
BothInverse g = LeftInverse g × RightInverse g

-- Technically this is too strong; g only needs to be congruent when its domain is restricted to the range of f.
HasLeftInverse : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂)
HasLeftInverse = Σ (B → A) λ g → Congruent _≈_ _~_ g × LeftInverse g

left-inv→injective : HasLeftInverse → Injective _~_ _≈_ f
left-inv→injective (g , g-cong , gfx~x) fx≈fy = ~-trans (~-trans (~-sym gfx~x) (g-cong fx≈fy)) gfx~x


-- Likewise, I suspect this one is too strong too
HasRightInverse : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂)
HasRightInverse = Σ (B → A) λ g → Congruent _≈_ _~_ g × RightInverse g

right-inv→surjective : HasRightInverse → Surjective _~_ _≈_ f
right-inv→surjective (g , g-cong , fgy~y) y = g y , λ {z} z~gy → ≈-trans (f-cong z~gy) fgy~y


-- This, however, is just right
HasBothInverse : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂)
HasBothInverse = Σ (B → A) λ g → Congruent _≈_ _~_ g × BothInverse g

both-inv→bijective : HasBothInverse → Bijective _~_ _≈_ f
both-inv→bijective (g , g-cong , left-inv , right-inv) = left-inv→injective  (g , g-cong , left-inv) , right-inv→surjective (g , g-cong , right-inv)

bijective→both-inv : Bijective _~_ _≈_ f → HasBothInverse
bijective→both-inv (injective , surjective) = g , g-cong , (λ {x} →  gfx~x) , (λ {y} → fgy≈y)
    where
        g : B → A
        g = proj₁ ∘ surjective

        gfx~x : ∀ {x : A} → g (f x) ~ x
        gfx~x {x} = injective (surjective (f x) .proj₂ ~-refl)

        fgy≈y : ∀ {y : B} → f (g y) ≈ y
        fgy≈y {y} = surjective y .proj₂ ~-refl

        g-cong : Congruent _≈_ _~_ g
        g-cong {x} {y} x≈y = injective (begin
            f (g x)   ≈⟨ fgy≈y ⟩
            x           ≈⟨ x≈y ⟩
            y           ≈⟨ ≈-sym (fgy≈y) ⟩
            f (g y)   ∎)
            where open import Relation.Binary.Reasoning.Setoid B-setoid
