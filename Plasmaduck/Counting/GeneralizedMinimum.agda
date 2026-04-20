open import Level using (Level; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_; inspect; cong; Reveal_·_is_; [_]) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Function using (_∘_; id)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary using (Rel; IsEquivalence; Decidable; _Respects₂_)
open import Relation.Binary.Bundles using (Setoid)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; s≤s; s≤s⁻¹)
open import Data.Nat.Properties using (≤-trans)
open import Data.Empty using (⊥; ⊥-elim)

open import Plasmaduck.SetoidExperiment.SetoidMachinery using (property-subset-setoid; discrete-setoid)
open import Plasmaduck.Counting.Counting using (any; all; fin-nat-bijection)
open import Plasmaduck.Data.Nat using (n≤n; n≤sn; ≤→<≡; s≡s⁻¹)
open import Plasmaduck.Property.Defs using (DecidableProperty; CongruentProperty)
open import Plasmaduck.Relation.Defs using (from-discrete-cong-property)
open import Plasmaduck.Util.Case using (case_of_)
open import Plasmaduck.Util.TypeChange using (change-type)


-- For when you want to avoid double negation nonsense since P is already negated.
-- This way, you don't need decidability of P for as much.
module Plasmaduck.Counting.GeneralizedMinimum {ℓ₁ ℓ₂ : Level} (P : ℕ → Set ℓ₁) (Q : ℕ → Set ℓ₂) where

HasValue : Set ℓ₁
HasValue = Σ ℕ P

NotHasValue : Set ℓ₂
NotHasValue = Σ ℕ Q

-- Defined like this to match the shape of property-subset-setoid (discrete-setoid ℕ) (_< n)
ValueBelow : ℕ → Set ℓ₁
ValueBelow n = Σ (Σ ℕ (_< n)) (P ∘ proj₁)

NoValueBelow : ℕ → Set ℓ₂
NoValueBelow n = ∀ (m : Σ ℕ (_< n)) → (Q ∘ proj₁) m

-- Technically, this is not known to be a minimum unless P and Q are contradictory
IsMinimum : ℕ → Set (ℓ₁ ⊔ ℓ₂)
IsMinimum m = P m × NoValueBelow m

Minimum : Set (ℓ₁ ⊔ ℓ₂)
Minimum = Σ ℕ IsMinimum

IsNotMinimum : ℕ → Set (ℓ₁ ⊔ ℓ₂)
IsNotMinimum m = Q m ⊎ ValueBelow m


IsMinimum-cong : CongruentProperty (discrete-setoid ℕ) IsMinimum
IsMinimum-cong = from-discrete-cong-property ℕ IsMinimum

IsNotMinimum-cong : CongruentProperty (discrete-setoid ℕ) IsNotMinimum
IsNotMinimum-cong = from-discrete-cong-property ℕ IsNotMinimum

P-cong : CongruentProperty (discrete-setoid ℕ) P
P-cong = from-discrete-cong-property ℕ P

value-below-cong : CongruentProperty (discrete-setoid ℕ) ValueBelow
value-below-cong = from-discrete-cong-property ℕ ValueBelow

no-value-below-cong : CongruentProperty (discrete-setoid ℕ) NoValueBelow
no-value-below-cong = from-discrete-cong-property ℕ NoValueBelow

value-below-suc : (n : ℕ) → ValueBelow n → ValueBelow (suc n)
value-below-suc n ((m , m<n) , value-at-m) = ((m , ≤-trans m<n n≤sn) , value-at-m)

no-value-below-pred : (n : ℕ) → NoValueBelow (suc n) → NoValueBelow n
no-value-below-pred n nothing-below-sn (m , m<n) = nothing-below-sn (m , ≤-trans m<n n≤sn)


module FindMinimum (PQ-dec : ∀ m → P m ⊎ Q m) where
    value-below-dec : ∀ n → ValueBelow n ⊎ NoValueBelow n
    value-below-dec n with any {A-setoid = property-subset-setoid (discrete-setoid ℕ) (_< n)} (n , fin-nat-bijection n) (PQ-dec-is-first ∘ proj₁) (λ { ≡-refl → id }) (PQ-dec-is-first-dec ∘ proj₁)
        where
            PQ-dec-is-first : ℕ → Set (ℓ₁ ⊔ ℓ₂)
            PQ-dec-is-first m = Σ (P m) λ P[m] → PQ-dec m ≡ inj₁ P[m]

            PQ-dec-is-first-dec : DecidableProperty PQ-dec-is-first
            PQ-dec-is-first-dec m with PQ-dec m
            ... | inj₁ P[m] = yes (P[m] , ≡-refl)
            ... | inj₂ Q[m] = no λ ()

    ... | yes ((m , m<n) , P[m] , PQ-dec-m≡inj₁-P[m]) = inj₁ ((m , m<n) , P[m])
    ... | no pf = inj₂ everything-is-Q
        where
            everything-is-Q : (m : Σ ℕ (_< n)) → Q (proj₁ m)
            everything-is-Q (m , m<n) with PQ-dec m | inspect PQ-dec m
            ... | inj₁ P[m] | [ PQ-dec-m≡inj₁-P[m] ] = ⊥-elim (pf ((m , m<n) , P[m] , PQ-dec-m≡inj₁-P[m]))
            ... | inj₂ Q[m] | _ = Q[m]

    find-minimum : HasValue → Minimum
    find-minimum (m , P[m]) = find-minimum' (suc m) (suc m) n≤n ((m , n≤n) , P[m])
        where
        -- Defined this way to take advantage of the fact that any searches from below.
        -- This means that this function should only have to recurse twice for any input.
        -- ... I should really figure out how to properly do strong induction.
        find-minimum' : (m n : ℕ) → .(m ≤ n) → ValueBelow m → Minimum
        find-minimum' zero _ m≤n ((_ , ()) , _)
        find-minimum' m@(suc m') (suc n') m≤n ((o , o<m) , P[o]) with value-below-dec o
        ... | inj₁ value-below-o = find-minimum' o n' (s≤s⁻¹ (≤-trans o<m m≤n)) value-below-o
        ... | inj₂ nothing-below-o = o , P[o] , nothing-below-o

    is-minimum-dec : ∀ n → IsMinimum n ⊎ IsNotMinimum n
    is-minimum-dec n with PQ-dec n | value-below-dec n
    ... | inj₁ P[n] | inj₂ nothing-below-n = inj₁ (P[n] , nothing-below-n)
    ... | inj₂ Q[n] | _ = inj₂ (inj₁ Q[n])
    ... | _ | inj₁ item-below-n = inj₂ (inj₂ item-below-n)

    not-is-minimum→is-not-minimum : ∀ {n} → ¬ (IsMinimum n) → IsNotMinimum n
    not-is-minimum→is-not-minimum {n} n-not-is-minimum with is-minimum-dec n
    ... | inj₁ n-min = ⊥-elim (n-not-is-minimum n-min)
    ... | inj₂ n-not-min = n-not-min


module IsMinimum (not-both-PQ : ∀ {m} → P m → Q m → ⊥) where
    minimum-is-minimum : ∀ {m n} → m < n → IsMinimum n → P m → ⊥
    minimum-is-minimum {m = m} m<n n-is-minimum P[m] = not-both-PQ P[m] (n-is-minimum .proj₂ (m , m<n))

    minimum-contradict : ∀ {n} → IsMinimum n → IsNotMinimum n → ⊥
    minimum-contradict (P[n] , Q[<n]) (inj₁ Q[n]) = not-both-PQ P[n] Q[n]
    minimum-contradict (P[n] , Q[<n]) (inj₂ ((m , m<n) , P[m])) = not-both-PQ P[m] (Q[<n] (m , m<n))

    value-below-pred : (n : ℕ) → Q n → ValueBelow (suc n) → ValueBelow n
    value-below-pred n Q[n] ((m , m<sn) , P[m]) with ≤→<≡ m<sn
    ... | inj₁ (s≤s m<n) = (m , m<n) , P[m]
    ... | inj₂ sm=sn = ⊥-elim (not-both-PQ (change-type (cong P (s≡s⁻¹ sm=sn)) P[m]) Q[n])

    no-value-below-suc : (n : ℕ) → Q n → NoValueBelow n → NoValueBelow (suc n)
    no-value-below-suc n Q[n] nothing-below-n (m , m<sn) with ≤→<≡ m<sn
    ... | inj₁ (s≤s m<n) = nothing-below-n (m , m<n)
    ... | inj₂ sm=sn = change-type (cong Q (≡-sym (s≡s⁻¹ sm=sn))) Q[n]


open FindMinimum public
open IsMinimum public
