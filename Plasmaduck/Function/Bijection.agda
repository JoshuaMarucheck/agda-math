open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc; zero to lzero)

open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Function using (Bijective; Injective; Surjective; Congruent; Bijection; _∘_)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary using (IsEquivalence)

open import Plasmaduck.SetoidExperiment.SetoidMachinery using (⊎-setoid; rel₁; rel₂; ×-setoid)

module Plasmaduck.Function.Bijection where

variable
    a b c d e ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level

open Setoid using (Carrier; _≈_)
open Bijection using (to; cong; bijective)


module InverseFunction {s₁ : Setoid c ℓ₁} {s₂ : Setoid d ℓ₂} (bij : Bijection s₁ s₂) where
    private
        f = bij .Bijection.to
        f-cong = bij .Bijection.cong
        f-surj = bij .Bijection.bijective .proj₂
        f-inj = bij .Bijection.bijective .proj₁

        _≈₁_ = s₁ ._≈_
        _≈₂_ = s₂ ._≈_

    inv : s₂ .Carrier → s₁ .Carrier
    inv y = f-surj y .proj₁

    is-right-inv : (x : s₂ .Carrier) → (bij .to (inv x)) ≈₂ x
    is-right-inv x = f-surj x .proj₂ (s₁ .Setoid.refl)

    is-left-inv : (x : s₁ .Carrier) →  (inv (bij .to x)) ≈₁ x
    is-left-inv i = f-inj (f-surj (f i) .proj₂ (s₁ .Setoid.refl))

    open IsEquivalence

    inv-congruent : Congruent _≈₂_ _≈₁_ inv
    inv-congruent {x} {y} x≈₂y = f-inj (begin
        f (inv x)   ≈⟨ is-right-inv x ⟩
        x           ≈⟨ x≈₂y ⟩
        y           ≈⟨ s₂ .Setoid.sym (is-right-inv y) ⟩
        f (inv y)   ∎)
        where open import Relation.Binary.Reasoning.Setoid s₂

    inv-injective : Injective _≈₂_ _≈₁_ inv
    inv-injective {x} {y} inv-x≈₁inv-y = begin
        x           ≈⟨ s₂ .Setoid.sym (is-right-inv x) ⟩
        f (inv x)   ≈⟨ f-cong inv-x≈₁inv-y ⟩
        f (inv y)   ≈⟨ is-right-inv y ⟩
        y           ∎
        where open import Relation.Binary.Reasoning.Setoid s₂

    inv-surjective : Surjective _≈₂_ _≈₁_ inv
    inv-surjective i = f i , λ {z} z≈₂f-i → begin
        inv z       ≈⟨ inv-congruent z≈₂f-i ⟩
        inv (f i)   ≈⟨ is-left-inv i ⟩
        i           ∎
        where open import Relation.Binary.Reasoning.Setoid s₁



invert-bijection : {s₁ : Setoid c ℓ₁} {s₂ : Setoid d ℓ₂} → Bijection s₁ s₂ → Bijection s₂ s₁
invert-bijection {s₁ = s₁} {s₂} bij = record {
    to = inv;
    cong = inv-congruent;
    bijective = inv-injective , inv-surjective
    }
    where open InverseFunction bij

∘-bijection : {s₁ : Setoid c ℓ₁} {s₂ : Setoid d ℓ₂} {s₃ : Setoid e ℓ₃} → Bijection s₁ s₂ → Bijection s₂ s₃ → Bijection s₁ s₃
∘-bijection {s₁ = s₁} {s₂} {s₃} bij₁ bij₂ = record {
    to = f;
    cong = f-cong;
    bijective = bij₁ .bijective .proj₁ ∘ bij₂ .bijective .proj₁ , surjective
    }
    where
        f = bij₂ .to ∘ bij₁ .to

        f-cong : Congruent (s₁ ._≈_) (s₃ ._≈_) f
        f-cong = bij₂ .cong ∘ bij₁ .cong

        surj₁ = bij₁ .bijective .proj₂
        surj₂ = bij₂ .bijective .proj₂

        surjective : Surjective (s₁ ._≈_) (s₃ ._≈_) f
        surjective z with surj₂ z
        ...             | (y , f₂y≈₃z) with surj₁ y
        ...                               | (x , f₁x≈₂y) = x , λ {w} w≈₁x → begin
            f w         ≈⟨ f-cong w≈₁x ⟩
            f x         ≈⟨ bij₂ .cong (f₁x≈₂y (s₁ .Setoid.refl)) ⟩
            bij₂ .to y  ≈⟨ f₂y≈₃z (s₂ .Setoid.refl) ⟩
            z           ∎
            where open import Relation.Binary.Reasoning.Setoid s₃


⊎-bijection :
    {s₁ : Setoid a ℓ₁} {s₂ : Setoid b ℓ₂} {s₃ : Setoid c ℓ₃} {s₄ : Setoid d ℓ₄} →
    Bijection s₁ s₂ → Bijection s₃ s₄ → Bijection (⊎-setoid s₁ s₃) (⊎-setoid s₂ s₄)
⊎-bijection {s₁ = s₁} {s₂} {s₃} {s₄} bij₁₂ bij₃₄ = record {
    to = f;
    cong = f-cong;
    bijective = f-injective , f-surjective
    }
    where
        f : (⊎-setoid s₁ s₃) .Carrier → (⊎-setoid s₂ s₄) .Carrier
        f (inj₁ x) = inj₁ (bij₁₂ .to x)
        f (inj₂ x) = inj₂ (bij₃₄ .to x)

        f-cong : Congruent ((⊎-setoid s₁ s₃) ._≈_) ((⊎-setoid s₂ s₄) ._≈_) f
        f-cong {inj₁ x} {inj₁ y} (rel₁ x≈₁y) = rel₁ (bij₁₂ .cong x≈₁y)
        f-cong {inj₂ x} {inj₂ y} (rel₂ x≈₃y) = rel₂ (bij₃₄ .cong x≈₃y)

        f-injective : Injective ((⊎-setoid s₁ s₃) ._≈_) ((⊎-setoid s₂ s₄) ._≈_) f
        f-injective {inj₁ x} {inj₁ y} (rel₁ fx≈₂fy) = rel₁ (bij₁₂ .bijective .proj₁ fx≈₂fy)
        f-injective {inj₂ x} {inj₂ y} (rel₂ fx≈₄fy) = rel₂ (bij₃₄ .bijective .proj₁ fx≈₄fy)

        f-surjective : Surjective ((⊎-setoid s₁ s₃) ._≈_) ((⊎-setoid s₂ s₄) ._≈_) f
        f-surjective (inj₁ x) = inj₁ (inv x) , λ { {inj₁ z} (rel₁ z≈₁invx) → rel₁ (begin
            bij₁₂ .to z         ≈⟨ bij₁₂ .cong z≈₁invx ⟩
            bij₁₂ .to (inv x)   ≈⟨ is-right-inv x ⟩
            x                   ∎)}
            where
                open InverseFunction bij₁₂
                open import Relation.Binary.Reasoning.Setoid s₂
        f-surjective (inj₂ x) = inj₂ (inv x) , λ { {inj₂ z} (rel₂ z≈₃invx) → rel₂ (begin
            bij₃₄ .to z         ≈⟨ bij₃₄ .cong z≈₃invx ⟩
            bij₃₄ .to (inv x)   ≈⟨ is-right-inv x ⟩
            x                   ∎)}
            where
                open InverseFunction bij₃₄
                open import Relation.Binary.Reasoning.Setoid s₄

×-bijection :
    {s₁ : Setoid a ℓ₁} {s₂ : Setoid b ℓ₂} {s₃ : Setoid c ℓ₃} {s₄ : Setoid d ℓ₄} →
    Bijection s₁ s₂ → Bijection s₃ s₄ → Bijection (×-setoid s₁ s₃) (×-setoid s₂ s₄)
×-bijection {s₁ = s₁} {s₂} {s₃} {s₄} bij₁₂ bij₃₄ = record {
    to = f;
    cong = f-cong;
    bijective = f-injective , f-surjective
    }
    where
        f : (×-setoid s₁ s₃) .Carrier → (×-setoid s₂ s₄) .Carrier
        f (x₁ , x₂) = bij₁₂ .to x₁ , bij₃₄ .to x₂

        f-cong : Congruent ((×-setoid s₁ s₃) ._≈_) ((×-setoid s₂ s₄) ._≈_) f
        f-cong (x₁ , x₂) = bij₁₂ .cong x₁ , bij₃₄ .cong x₂

        f-injective : Injective ((×-setoid s₁ s₃) ._≈_) ((×-setoid s₂ s₄) ._≈_) f
        f-injective (x₁ , x₂) =
            bij₁₂ .bijective .proj₁ x₁ ,
            bij₃₄ .bijective .proj₁ x₂

        f-surjective : Surjective ((×-setoid s₁ s₃) ._≈_) ((×-setoid s₂ s₄) ._≈_) f
        f-surjective (x₁ , x₂) =
            (bij₁₂ .bijective .proj₂ x₁ .proj₁ ,
             bij₃₄ .bijective .proj₂ x₂ .proj₁)
            ,
            (λ {z} z~x →
               bij₁₂ .bijective .proj₂ x₁ .proj₂ (z~x .proj₁) ,
               bij₃₄ .bijective .proj₂ x₂ .proj₂ (z~x .proj₂))
