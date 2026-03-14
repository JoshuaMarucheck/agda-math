open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc; zero to lzero)

open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Function using (Bijective; Injective; Surjective; Congruent; Bijection)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary using (IsEquivalence)



module Plasmaduck.Function.Bijection where

variable
    a b c d ℓ₁ ℓ₂ ℓ₃ : Level

open Setoid using (Carrier; _≈_)


invert-bijection : {s₁ : Setoid c ℓ₁} {s₂ : Setoid d ℓ₂} → Bijection s₁ s₂ → Bijection s₂ s₁
invert-bijection {s₁ = s₁} {s₂} bij = record {
    to = inv;
    cong = inv-congruent;
    bijective = inv-injective , inv-surjective
    }
    where

        f = bij .Bijection.to
        f-cong = bij .Bijection.cong
        f-surj = bij .Bijection.bijective .proj₂
        f-inj = bij .Bijection.bijective .proj₁

        _≈₁_ = s₁ ._≈_
        _≈₂_ = s₂ ._≈_

        inv : s₂ .Carrier → s₁ .Carrier
        inv y = f-surj y .proj₁

        is-right-inv : (x : s₂ .Carrier) → f (inv x) ≈₂ x
        is-right-inv x = f-surj x .proj₂ (s₁ .Setoid.refl)

        is-left-inv : (x : s₁ .Carrier) → inv (f x) ≈₁ x
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
