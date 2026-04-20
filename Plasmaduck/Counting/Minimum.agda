open import Level using (Level; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_; inspect; cong; Reveal_·_is_; [_]) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Function using (_∘_; id)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary using (Rel; IsEquivalence; Decidable; _Respects₂_)
open import Relation.Binary.Bundles using (Setoid)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; s≤s; s≤s⁻¹)
open import Data.Nat.Properties using (≤-trans)

open import Plasmaduck.SetoidExperiment.SetoidMachinery using (property-subset-setoid; discrete-setoid)
open import Plasmaduck.Counting.Counting using (any; fin-nat-bijection)
open import Plasmaduck.Data.Nat using (n≤n; n≤sn)
open import Plasmaduck.Property.Defs using (DecidableProperty; CongruentProperty)
open import Plasmaduck.Relation.Defs using (from-discrete-cong-property)



module Plasmaduck.Counting.Minimum {ℓ : Level} (P : ℕ → Set ℓ) where

HasValue : Set ℓ
HasValue = Σ ℕ P

-- Defined like this to match the shape of property-subset-setoid (discrete-setoid ℕ) (_< n)
ValueBelow : ℕ → Set ℓ
ValueBelow n = Σ (Σ ℕ (_< n)) (P ∘ proj₁)

IsMinimum : ℕ → Set ℓ
IsMinimum m = P m × ¬ ValueBelow m

Minimum : Set ℓ
Minimum = Σ ℕ IsMinimum


IsMinimum-cong : CongruentProperty (discrete-setoid ℕ) IsMinimum
IsMinimum-cong = from-discrete-cong-property ℕ IsMinimum

P-cong : CongruentProperty (discrete-setoid ℕ) P
P-cong = from-discrete-cong-property ℕ P

value-below-cong : CongruentProperty (discrete-setoid ℕ) ValueBelow
value-below-cong = from-discrete-cong-property ℕ ValueBelow

value-below-suc : (n : ℕ) → ValueBelow n → ValueBelow (suc n)
value-below-suc n ((m , m<n) , value-at-m) = ((m , ≤-trans m<n n≤sn) , value-at-m)


module FindMinimum (P-dec : DecidableProperty P) where
    value-below-dec : DecidableProperty ValueBelow
    value-below-dec n = any {A-setoid = property-subset-setoid (discrete-setoid ℕ) (_< n)} (n , fin-nat-bijection n) (P ∘ proj₁) (λ { ≡-refl → id }) (P-dec ∘ proj₁)

    find-minimum : HasValue → Minimum
    find-minimum (m , P[m]) = find-minimum' (suc m) (suc m) n≤n ((m , n≤n) , P[m])
        where
        -- Defined this way to take advantage of the fact that any searches from below.
        -- This means that this function should only have to recurse twice for any input.
        -- ... I should really figure out how to properly do strong induction.
        find-minimum' : (m n : ℕ) → .(m ≤ n) → ValueBelow m → Minimum
        find-minimum' zero _ m≤n ((_ , ()) , _)
        find-minimum' m@(suc m') (suc n') m≤n ((o , o<m) , P[o]) with value-below-dec o
        ... | yes value-below-o = find-minimum' o n' (s≤s⁻¹ (≤-trans o<m m≤n)) value-below-o
        ... | no nothing-below-o = o , P[o] , nothing-below-o

    is-minimum-dec : DecidableProperty IsMinimum
    is-minimum-dec n with P-dec n | value-below-dec n
    ... | yes P[n] | no nothing-below-n = yes (P[n] , nothing-below-n)
    ... | no ¬P[n] | _ = no (¬P[n] ∘ proj₁)
    ... | _ | yes item-below-n = no λ nothing-below-n → nothing-below-n .proj₂ item-below-n
