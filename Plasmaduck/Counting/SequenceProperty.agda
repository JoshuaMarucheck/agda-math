open import Level using (Level; _⊔_) renaming (suc to lsuc; zero to lzero)
open import Relation.Nullary.Negation using (¬_)
open import Data.Nat using (ℕ; suc; zero; _+_; _∸_; _<_; _≤_; z≤n; s≤s; s≤s⁻¹)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; curry; uncurry)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.Bundles using (Setoid)

open import Plasmaduck.SetoidExperiment.SetoidMachinery using (SetoidFunction)
open import Plasmaduck.Property.Defs using (DecidableProperty; CongruentProperty)


module Plasmaduck.Counting.SequenceProperty
    {a b c ℓ : Level} (A-setoid : Setoid a ℓ)
    (P : A-setoid .Setoid.Carrier → ℕ → Set b)
    (Q : A-setoid .Setoid.Carrier → ℕ → Set c)
    where

-- As with GeneralizedMinimum, P and Q are supposed to stand in as approximately opposites.
-- Many of the definition names assume P and Q are contradictory.
--
-- You can do various things below with only P ⊎ Q and P → Q → ⊥, and I hope to lay out minimal assumption sets for each theorem.
-- The extensions defined here are centered around minimum as defined in Plasmaduck.Counting.GeneralizedMinimum.
-- Thus, minimum means some P x n where Q x m holds for all m < n.

open Setoid using (Carrier; _≈_)
open SetoidFunction using (func; respects)

private
    A = A-setoid .Carrier
    _~_ = A-setoid ._≈_


module Types (x : A) where
    EverQ : Set c
    EverQ = Σ ℕ (Q x)

    AlwaysP : Set b
    AlwaysP = ∀ (n : ℕ) → P x n

    open import Plasmaduck.Counting.GeneralizedMinimum (Q x) (P x) using () renaming (ValueBelow to QBefore; Minimum to EverMinimumQ; IsMinimum to MinimumQAt; IsNotMinimum to NotMinimumQAt) public

    NeverMinimumQ : Set (b ⊔ c)
    NeverMinimumQ = ∀ n → NotMinimumQAt n


module BasicExtensions {x : A} where
    open Types x using (EverQ; EverMinimumQ)

    open import Plasmaduck.Counting.GeneralizedMinimum (Q x) (P x) using (module FindMinimum; module IsMinimum) public

    ever-minimum→ever-q : EverMinimumQ → EverQ
    ever-minimum→ever-q (m , q-at-m , _) = m , q-at-m


module ContradictExtensions (contradict-q-p : {y : A} {n : ℕ} → Q y n → P y n → ⊥) {x : A} where
    open Types x using (AlwaysP; EverQ; EverMinimumQ; NeverMinimumQ)
    open BasicExtensions {x} using (ever-minimum→ever-q)

    contradict-minimum : NeverMinimumQ → EverMinimumQ → ⊥
    contradict-minimum never-minimum (n , (q-at-n , p-below-n)) with never-minimum n
    ... | inj₁ p-at-n = contradict-q-p q-at-n p-at-n
    ... | inj₂ ((m , m<n) , q-at-m) = contradict-q-p q-at-m (p-below-n (m , m<n))

    contradict-always-ever : AlwaysP → EverQ → ⊥
    contradict-always-ever always-p (m , q-at-m) = contradict-q-p q-at-m (always-p m)

    contradict-always-minimum : AlwaysP → EverMinimumQ → ⊥
    contradict-always-minimum always-p minimum = contradict-always-ever always-p (ever-minimum→ever-q minimum)


module DecidableExtensions
    (contradict-q-p : {y : A} {n : ℕ} → Q y n → P y n → ⊥)
    (PQ-dec : (x : A) (n : ℕ) → Q x n ⊎ P x n)
    {x : A}
    where

    open Types x using (AlwaysP; EverQ; EverMinimumQ; NeverMinimumQ)
    open BasicExtensions {x} using (module FindMinimum)
    open ContradictExtensions contradict-q-p {x}

    open FindMinimum (PQ-dec x) using (not-is-minimum→is-not-minimum) renaming (find-minimum to ever-q→ever-minimum; value-below-dec to q-before-dec) public

    not-ever-minimum-is-never-minimum : (¬ EverMinimumQ) → NeverMinimumQ
    not-ever-minimum-is-never-minimum not-ever-minimum m = not-is-minimum→is-not-minimum {n = m} (λ minimum-at-m → not-ever-minimum (m , minimum-at-m))

    not-ever-q-is-always-p : (¬ EverQ) → AlwaysP
    not-ever-q-is-always-p not-ever-q n with PQ-dec x n
    ... | inj₁ q-at-n = ⊥-elim (not-ever-q (n , q-at-n))
    ... | inj₂ p-at-n = p-at-n

    never-minimum→always-p : NeverMinimumQ → AlwaysP
    never-minimum→always-p never-minimum n with never-minimum n
    ... | inj₁ p-at-n = p-at-n
    ... | inj₂ ((m , m<n) , q-at-m) = ⊥-elim (contradict-minimum never-minimum (ever-q→ever-minimum (m , q-at-m)))

    contradict-minimum-q : NeverMinimumQ → EverQ → ⊥
    contradict-minimum-q never-minimum ever-q = contradict-always-ever (never-minimum→always-p never-minimum) ever-q


module Extensions where
    open Types public
    open BasicExtensions public
    open ContradictExtensions public
    open DecidableExtensions public


open Types

-----------------------------------
--- Forward and Backward things ---
-----------------------------------


module _ (f-func : SetoidFunction A-setoid A-setoid) where

    private
        f = f-func .func
        f-respects = f-func .respects

        P-forward-type = (x : A) (n : ℕ) → P x (suc n) → P (f x) n
        P-backward-type = (x : A) (n : ℕ) → P (f x) n → P x (suc n)
        Q-forward-type = (x : A) (n : ℕ) → Q x (suc n) → Q (f x) n
        Q-backward-type = (x : A) (n : ℕ) → Q (f x) n → Q x (suc n)

    module PForward (forward : P-forward-type) (x : A) where
        always-p-pass-forward : AlwaysP x → AlwaysP (f x)
        always-p-pass-forward x-always-p n = forward x n (x-always-p (suc n))

    module PBackward (backward : P-backward-type) (x : A) (p-x-at-zero : P x 0) where
        always-p-pass-backward : AlwaysP (f x) → AlwaysP x
        always-p-pass-backward fx-always-p zero = p-x-at-zero
        always-p-pass-backward fx-always-p (suc n) = backward x n (fx-always-p n)

    module QForward
        (contradict-q-p : {x : A} {n : ℕ} → Q x n → P x n → ⊥)
        (Q-forward : Q-forward-type)
        (x : A)
        (p-x-at-zero : P x 0)
        where
        ever-q-pass-forward : EverQ x → EverQ (f x)
        ever-q-pass-forward (zero , q-x-at-zero) = ⊥-elim (contradict-q-p q-x-at-zero p-x-at-zero)
        ever-q-pass-forward (suc m , q-x-at-sm) = m , Q-forward x m q-x-at-sm

    module QBackward (Q-backward : Q-backward-type) (x : A) where
        ever-q-pass-backward : EverQ (f x) → EverQ x
        ever-q-pass-backward (m , q-fx-at-m) = suc m , Q-backward x m q-fx-at-m

    module PQBackward
        (P-backward : P-backward-type)
        (Q-backward : Q-backward-type)
        where

        open PBackward P-backward public
        open QBackward Q-backward public

        module _ (x : A) where
            ever-minimum-pass-backward : (P x 0 ⊎ Q x 0) → EverMinimumQ (f x) → EverMinimumQ x
            ever-minimum-pass-backward (inj₂ qx) _ = zero , qx , λ ()
            ever-minimum-pass-backward (inj₁ px) (m , q-fx-at-m , p-fx-below-m) =
                suc m ,
                Q-backward x m q-fx-at-m ,
                λ {
                    (zero , n<m) → px;
                    (suc n' , n<m) → P-backward x n' (p-fx-below-m (n' , s≤s⁻¹ n<m))
                }

        module _ (x : A) (p-x-at-zero : P x 0) where
            never-minimum-pass-backward : NeverMinimumQ (f x) → NeverMinimumQ x
            never-minimum-pass-backward fx-never-minimum zero = inj₁ p-x-at-zero
            never-minimum-pass-backward fx-never-minimum (suc n') with fx-never-minimum n'
            ... | inj₁ p-fx-at-n' = inj₁ (P-backward x n' p-fx-at-n')
            ... | inj₂ ((m , m<sn) , q-fx-at-m) = inj₂ ((suc m , s≤s m<sn) , Q-backward x m q-fx-at-m)

    module PQForward
        (contradict-q-p : {x : A} {n : ℕ} → Q x n → P x n → ⊥)
        (P-forward : P-forward-type)
        (Q-forward : Q-forward-type)
        where

        open PForward P-forward public
        open QForward contradict-q-p Q-forward public

        module _ (x : A) (p-x-at-zero : P x 0) where
            ever-minimum-pass-forward : EverMinimumQ x → EverMinimumQ (f x)
            ever-minimum-pass-forward (zero , q-x-at-zero , _) = ⊥-elim (contradict-q-p q-x-at-zero p-x-at-zero)
            ever-minimum-pass-forward (suc m , q-x-at-sm , p-x-≤-m) =
                m ,
                Q-forward x m q-x-at-sm ,
                (λ (n , n<m) → P-forward x n (p-x-≤-m (suc n , s≤s n<m)))

        module _ (x : A) where
            never-minimum-pass-forward : NeverMinimumQ x → NeverMinimumQ (f x)
            never-minimum-pass-forward x-never-minimum n with x-never-minimum (suc n)
            ... | inj₁ p-x-at-sn = inj₁ (P-forward x n p-x-at-sn)
            ... | inj₂ ((suc m' , s≤s m'<n) , q-x-at-m) = inj₂ ((m' , m'<n) , Q-forward x m' q-x-at-m)
            ... | inj₂ ((zero , z<n) , q-x-at-zero) with x-never-minimum zero
            ...     | inj₁ p-x-at-zero = ⊥-elim (contradict-q-p q-x-at-zero p-x-at-zero)
            ...     | inj₂ ((_ , ()) , _)

    module PQForwardBackward
        (contradict-q-p : {x : A} {n : ℕ} → Q x n → P x n → ⊥)
        (P-forward : P-forward-type)
        (P-backward : P-backward-type)
        (Q-forward : Q-forward-type)
        (Q-backward : Q-backward-type)
        where

        open PQBackward P-backward Q-backward public
        open PQForward contradict-q-p P-forward Q-forward public


    module StronglyDecidablePQ
        (PQ-dec : (x : A) (n : ℕ) → P x n ⊎ Q x n)
        (contradict-q-p : {x : A} {n : ℕ} → Q x n → P x n → ⊥)
        (P-forward : P-forward-type)
        (P-backward : P-backward-type)
        where

        module _ (x : A) (n : ℕ) where
            Q-forward : Q x (suc n) → Q (f x) n
            Q-forward q-x-at-sn with PQ-dec (f x) n
            ... | inj₁ fx-works-at-n = ⊥-elim (contradict-q-p q-x-at-sn (P-backward x n fx-works-at-n))
            ... | inj₂ q-fx-at-n = q-fx-at-n

            Q-backward : Q (f x) n → Q x (suc n)
            Q-backward q-fx-at-n with PQ-dec x (suc n)
            ... | inj₁ x-works-at-sn = ⊥-elim (contradict-q-p q-fx-at-n (P-forward x n x-works-at-sn))
            ... | inj₂ q-x-at-sn = q-x-at-sn

        open PQForwardBackward contradict-q-p P-forward P-backward Q-forward Q-backward public

    -- If Q = ¬ P
    module ContradictForwardBackward
        (contradict-q-p : {x : A} {n : ℕ} → Q x n → P x n → ⊥)
        (P-forward : P-forward-type)
        (P-backward : P-backward-type)
        where

        module _ (x : A) (n : ℕ) where
            contradict-forward : Q x (suc n) → ¬ P (f x) n
            contradict-forward q-x-at-sn fx-works-at-n = contradict-q-p q-x-at-sn (P-backward x n fx-works-at-n)

            contradict-backward : Q (f x) n → ¬ P x (suc n)
            contradict-backward q-fx-at-n x-works-at-sn = contradict-q-p q-fx-at-n (P-forward x n x-works-at-sn)



-------------------------
--- Congruence things ---
-------------------------

module AlwaysPCong
    (P-cong-in-x : (n : ℕ) → CongruentProperty A-setoid (λ x → P x n))
    where

    always-p-cong : CongruentProperty A-setoid AlwaysP
    always-p-cong x~y x-always-p n = P-cong-in-x n x~y (x-always-p n)

-- If Q x n = ¬ P x n, then consider using negation-cong from Plasmaduck.Property.Negation
module Cong
    (P-cong-in-x : (n : ℕ) → CongruentProperty A-setoid (λ x → P x n))
    (Q-cong-in-x : (n : ℕ) → CongruentProperty A-setoid (λ x → Q x n))
    where

    open AlwaysPCong P-cong-in-x public

    open import Plasmaduck.Counting.GeneralizedMinimum using () renaming (value-below-cong to q-before-cong; IsMinimum-cong to MinimumQAt-cong)

    ever-q-cong : CongruentProperty A-setoid EverQ
    ever-q-cong x~y (m , q-x-at-m) = m , Q-cong-in-x m x~y q-x-at-m

    q-before-cong-in-x : (n : ℕ) → CongruentProperty A-setoid (λ q → QBefore q n)
    q-before-cong-in-x n x~y ((m , m<n) , q-x-at-m) = (m , m<n) , Q-cong-in-x m x~y q-x-at-m

    ever-minimum-cong : CongruentProperty A-setoid EverMinimumQ
    ever-minimum-cong x~y (m , q-x-at-m , p-x-below-m) = m , Q-cong-in-x m x~y q-x-at-m , λ (n , n<m) → P-cong-in-x n x~y (p-x-below-m (n , n<m))
