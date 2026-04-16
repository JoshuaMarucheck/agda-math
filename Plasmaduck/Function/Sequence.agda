open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≢_; _≡_; inspect; cong; Reveal_·_is_; [_]) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Data.Nat using (ℕ; suc; zero; _+_; _∸_; _<_; _≤_; z≤n; s≤s; s≤s⁻¹)
open import Data.Nat.Properties using (m∸n+n≡m; _≟_; ≤-total; ≤-trans)
open import Function using (_∘_; _on_; flip; id; Injective; Surjective; Bijection; Congruent)
open import Relation.Binary using (TotalOrder; DecTotalOrder; IsTotalOrder; IsStrictTotalOrder; Reflexive; Irreflexive; Symmetric; Asymmetric; Transitive; Trans; Rel; IsEquivalence; _Respects₂_; _Respectsˡ_; _Respectsʳ_; Decidable; IsStrictPartialOrder; Trichotomous; Tri; tri<; tri≈; tri>; IsDecStrictPartialOrder)
open import Relation.Binary.Bundles using (Setoid)

open import Plasmaduck.SetoidExperiment.SetoidMachinery using (SetoidFunction; discrete-setoid; property-subset-setoid)



module Plasmaduck.Function.Sequence where

variable
    a b c d ℓ ℓ₁ ℓ₂ ℓ₃ : Level

open Setoid using (Carrier; _≈_)
open SetoidFunction using (func; respects)

module Repeat
    {A-setoid : Setoid a ℓ₁}
    (f-func : SetoidFunction A-setoid A-setoid)
    where

    private
        A = A-setoid .Carrier
        _~_ = A-setoid ._≈_
        f = f-func .func
        f-respects = f-func .respects

        open IsEquivalence (A-setoid .Setoid.isEquivalence) using (reflexive; refl; sym; trans)

    repeat : A → ℕ → A
    repeat x zero = x
    repeat x (suc n) = repeat (f x) n

    repeat-f : (x : A) → (n : ℕ) → f (repeat x n) ≡ repeat (f x) n
    repeat-f x zero = ≡-refl
    repeat-f x (suc n) = repeat-f (f x) n

    repeat-cong-in-x : (n : ℕ) → Congruent _~_ _~_ (λ x → repeat x n)
    repeat-cong-in-x zero x~y = x~y
    repeat-cong-in-x (suc n) {x} {y} x~y = begin
        repeat x (suc n)    ≈⟨ sym (reflexive (repeat-f x n)) ⟩
        f (repeat x n)      ≈⟨ f-respects (repeat-cong-in-x n x~y) ⟩
        f (repeat y n)      ≈⟨ reflexive (repeat-f y n) ⟩
        repeat y (suc n)    ∎
        where open import Relation.Binary.Reasoning.Setoid A-setoid


    -- This form is bad for computation since it's not tail-recursive
    -- However, this saves a lot of headaches for proving things since it keeps all the function calls on the outside of the repeat
    repeat' : A → ℕ → A
    repeat' x zero = x
    repeat' x (suc n) = f (repeat' x n)

    repeat-pf-swap : (x : A) (n : ℕ) → repeat x n ≡ repeat' x n
    repeat-pf-swap x zero = ≡-refl
    repeat-pf-swap x (suc n) = ≡-trans (≡-sym (repeat-f x n)) (cong f (repeat-pf-swap x n))

    repeat'-f : (x : A) → (n : ℕ) → f (repeat' x n) ≡ repeat' (f x) n
    repeat'-f x n =
        f (repeat' x n)     ≡⟨ cong f (≡-sym (repeat-pf-swap x n)) ⟩
        f (repeat x n)      ≡⟨ repeat-f x n ⟩
        repeat (f x) n      ≡⟨ repeat-pf-swap (f x) n ⟩
        repeat' (f x) n     ∎
        where open ≡-Reasoning

    repeat'-cong-in-x : (n : ℕ) → Congruent _~_ _~_ (λ x → repeat' x n)
    repeat'-cong-in-x n {x} {y} x~y = begin
        repeat' x n     ≈⟨ reflexive (≡-sym (repeat-pf-swap x n)) ⟩
        repeat x n      ≈⟨ repeat-cong-in-x n x~y ⟩
        repeat y n      ≈⟨ reflexive (repeat-pf-swap y n) ⟩
        repeat' y n     ∎
        where open import Relation.Binary.Reasoning.Setoid A-setoid

open Repeat public
