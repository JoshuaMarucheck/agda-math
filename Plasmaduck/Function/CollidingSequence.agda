open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≢_; _≡_; inspect; cong; Reveal_·_is_; [_]) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Data.Nat using (ℕ; suc; zero; _+_; _∸_; _<_; _≤_; z≤n; s≤s; s≤s⁻¹)
open import Data.Nat.Properties using (m∸n+n≡m; _≟_; ≤-total; ≤-trans; <-cmp)
open import Data.Vec using (Vec; _∷_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; curry; uncurry)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Function using (_∘_; flip; id; Injective; Surjective; Bijection; Congruent)
open import Relation.Binary using (TotalOrder; DecTotalOrder; IsTotalOrder; IsStrictTotalOrder; Reflexive; Irreflexive; Symmetric; Asymmetric; Transitive; Trans; Rel; IsEquivalence; _Respects₂_; _Respectsˡ_; _Respectsʳ_; Decidable; IsStrictPartialOrder; Trichotomous; Tri; tri<; tri≈; tri>; IsDecStrictPartialOrder)
open import Relation.Binary.Bundles using (Setoid)

open import Plasmaduck.Function.InjectionSurjection using (RightInverse; HasRightInverse; right-inv→surjective; HasRightInverse-conjunct; weak-right-inv→surjective)
open import Plasmaduck.SetoidExperiment.SetoidMachinery using (SetoidFunction; property-subset-setoid; discrete-setoid; _∘'_; _which-is-cong_)
open import Plasmaduck.Function.Sequence using (module Repeat)
open import Plasmaduck.Function using (_⇔_)
open import Plasmaduck.Property.Defs using (DecidableProperty; CongruentProperty)
open import Plasmaduck.Property.Negation using (negation-cong)
open import Plasmaduck.Relation.Decidable using (decidable-push)
open import Plasmaduck.Counting.Counting using (any)
open import Plasmaduck.Number.Nat using (n≤sn; n≤n; ≤→<≡)
open import Plasmaduck.Util.Negation using (¬¬-lift; invert-product)
open import Plasmaduck.Util.Case using (case_of_)
open import Plasmaduck.Util.TypeChange using (change-type)



module Plasmaduck.Function.CollidingSequence where


variable
    a b c d ℓ ℓ₁ ℓ₂ ℓ₃ : Level

open Setoid using (Carrier; _≈_)
open SetoidFunction using (func; respects)

private
    apply : {B : Set b} {C : Set c} → (B → C) → B → C
    apply = id


module _
    (A-setoid : Setoid a ℓ)
    (f-func : SetoidFunction A-setoid A-setoid)
    where
    private
        A = A-setoid .Carrier
        _~_ = A-setoid ._≈_
        f = f-func .func
        f-respects = f-func .respects

    module ContradictingSequenceProperties
        (UnbrokenAt : A → ℕ → Set b)
        (BreaksAt : A → ℕ → Set c)
        (contradict-broken-unbroken : {x : A} {n : ℕ} → BreaksAt x n → UnbrokenAt x n → ⊥)
        (unbroken-pass-forward : (x : A) (m : ℕ) → UnbrokenAt x (suc m) → UnbrokenAt (f x) m)
        (unbroken-pass-back : (x : A) (m : ℕ) → UnbrokenAt (f x) m → UnbrokenAt x (suc m))
        (breaks-at-pass-forward : (x : A) (m : ℕ) → BreaksAt x (suc m) → BreaksAt (f x) m)
        (breaks-at-pass-backward : (x : A) (m : ℕ) → BreaksAt (f x) m → BreaksAt x (suc m))
        (unbroken-at-cong-in-x : (n : ℕ) → CongruentProperty A-setoid (λ x → UnbrokenAt x n))
        (breaks-at-cong-in-x : (n : ℕ) → CongruentProperty A-setoid (λ x → BreaksAt x n))
        where
        -- Does not open DecidableExtensions; please do that yourself

        open import Plasmaduck.Counting.SequenceProperty A-setoid UnbrokenAt BreaksAt using (module PQForwardBackward; module Extensions; module ContradictExtensions; module DecidableExtensions) renaming (module Cong to SequenceCong)
        open Extensions using () renaming (
            EverQ to EverBreaks;
            AlwaysP to NeverBreaks;
            QBefore to BreaksBefore;
            EverMinimumQ to EverTerminates;
            MinimumQAt to TerminatesAt;
            NotMinimumQAt to NotTerminatesAt;
            NeverMinimumQ to NeverTerminates;

            ever-minimum→ever-q to ever-terminates→ever-breaks
            ) public

        open ContradictExtensions contradict-broken-unbroken using () renaming (
            contradict-minimum to contradict-terminates;
            contradict-always-ever to contradict-breaks;
            contradict-always-minimum to contradict-breaks-terminates
            ) public

        open PQForwardBackward f-func contradict-broken-unbroken unbroken-pass-forward unbroken-pass-back breaks-at-pass-forward breaks-at-pass-backward using () renaming (
            always-p-pass-forward to never-breaks-pass-forward;
            always-p-pass-backward to never-breaks-pass-backward;
            ever-q-pass-forward to ever-breaks-pass-forward;
            ever-q-pass-backward to ever-breaks-pass-backward;
            ever-minimum-pass-forward to ever-terminates-pass-forward;
            ever-minimum-pass-backward to ever-terminates-pass-backward;
            never-minimum-pass-forward to never-terminates-pass-forward;
            never-minimum-pass-backward to never-terminates-pass-backward
            ) public

        open SequenceCong unbroken-at-cong-in-x breaks-at-cong-in-x using () renaming (
            always-p-cong to never-breaks-cong;
            ever-q-cong to ever-breaks-cong;
            q-before-cong-in-x to breaks-before-cong-in-x;
            ever-minimum-cong to ever-terminates-cong
            ) public

module SequenceBreak
    (A-setoid : Setoid a ℓ)
    (f-func : SetoidFunction A-setoid A-setoid)
    (g-func : SetoidFunction A-setoid A-setoid)
    where
    -- The intent is that if g is a right inverse of f, then f is a surjection and we can do cool things with that.
    -- f is the function which we're looking at the looping of though.

    private
        A = A-setoid .Carrier
        _~_ = A-setoid ._≈_
        f = f-func .func
        f-respects = f-func .respects

        g = g-func .func
        g-respects = g-func .respects

        open IsEquivalence (A-setoid .Setoid.isEquivalence) using (reflexive; refl; sym; trans)
        open Repeat f-func using (repeat'; repeat'-f; repeat'-cong-in-x)

    module _ (x : A-setoid .Carrier) where
        -- x is the starting point

        -- Like, unbroken on the first step
        Unbroken : Set ℓ
        Unbroken = g (f x) ~ x

        UnbrokenAt : ℕ → Set ℓ
        UnbrokenAt n = g (repeat' x (suc n)) ~ repeat' x n

        BreaksAt : ℕ → Set ℓ
        BreaksAt n = ¬ UnbrokenAt n

    open import Plasmaduck.Counting.SequenceProperty A-setoid UnbrokenAt BreaksAt using (module DecidableExtensions; module ContradictForwardBackward)
    module _ (_~?_ : Decidable _~_) where

        breaks-at-dec : (x : A) → ∀ m → BreaksAt x m ⊎ UnbrokenAt x m
        breaks-at-dec x n with g (repeat' x (suc n)) ~? repeat' x n
        ... | yes pf = inj₂ pf
        ... | no pf = inj₁ pf

        open DecidableExtensions apply breaks-at-dec using () renaming (
            not-is-minimum→is-not-minimum to ¬terminates-at→not-terminates-at;
            ever-q→ever-minimum to ever-breaks→ever-terminates;
            q-before-dec to breaks-before-dec;
            not-ever-minimum-is-never-minimum to not-ever-terminates-is-never-terminates;
            not-ever-q-is-always-p to not-ever-breaks-is-never-breaks;
            never-minimum→always-p to never-terminates→never-breaks;
            contradict-minimum-q to contradict-terminates-breaks
            ) public

    unbroken-pass-forward : (x : A) (m : ℕ) → UnbrokenAt x (suc m) → UnbrokenAt (f x) m
    unbroken-pass-forward x m x-unbroken-at-sm =  (begin
        (g ∘ f) (repeat' (f x) m)   ≈⟨ (g-respects ∘ f-respects) (sym (reflexive (repeat'-f x m))) ⟩
        (g ∘ f ∘ f) (repeat' x m)   ≈⟨ x-unbroken-at-sm ⟩
        f (repeat' x m)             ≈⟨ reflexive (repeat'-f x m) ⟩
        repeat' (f x) m             ∎
        ) where open import Relation.Binary.Reasoning.Setoid A-setoid

    unbroken-pass-back : (x : A) (m : ℕ) → UnbrokenAt (f x) m → UnbrokenAt x (suc m)
    unbroken-pass-back x m fx-unbroken-at-m = (begin
        (g ∘ f ∘ f) (repeat' x m)   ≈⟨ (g-respects ∘ f-respects) (reflexive (repeat'-f x m)) ⟩
        (g ∘ f) (repeat' (f x) m)   ≈⟨ fx-unbroken-at-m ⟩
        repeat' (f x) m             ≈⟨ sym (reflexive (repeat'-f x m)) ⟩
        repeat' x (suc m)           ∎
        ) where open import Relation.Binary.Reasoning.Setoid A-setoid

    -- Congruence over A-setoid given fixed n
    unbroken-at-cong-in-x : (n : ℕ) → CongruentProperty A-setoid (λ x → UnbrokenAt x n)
    unbroken-at-cong-in-x n {x} {y} x~y x-unbroken-at-n = (begin
        g (repeat' y (suc n))    ≈⟨ g-respects (repeat'-cong-in-x (suc n) (sym x~y)) ⟩
        g (repeat' x (suc n))    ≈⟨ x-unbroken-at-n ⟩
        repeat' x n              ≈⟨ repeat'-cong-in-x n x~y ⟩
        repeat' y n              ∎
        ) where open import Relation.Binary.Reasoning.Setoid A-setoid

    breaks-at-cong-in-x : (n : ℕ) → CongruentProperty A-setoid (λ x → BreaksAt x n)
    breaks-at-cong-in-x n = negation-cong A-setoid (λ x → UnbrokenAt x n) (unbroken-at-cong-in-x n)

    -- Since BreaksAt is negated UnbrokenAt
    open ContradictForwardBackward f-func apply unbroken-pass-forward unbroken-pass-back using () renaming (
        contradict-forward to breaks-at-pass-forward;
        contradict-backward to breaks-at-pass-backward
        ) public
    open ContradictingSequenceProperties A-setoid f-func UnbrokenAt BreaksAt apply unbroken-pass-forward unbroken-pass-back breaks-at-pass-forward breaks-at-pass-backward unbroken-at-cong-in-x breaks-at-cong-in-x public

module Stability
    {A-setoid : Setoid a ℓ₁} {B-setoid : Setoid b ℓ₂} {C-setoid : Setoid c ℓ₃}
    (f-func : SetoidFunction A-setoid B-setoid)
    (f-right-inv : HasRightInverse A-setoid B-setoid f-func)
    (g-func : SetoidFunction B-setoid C-setoid)
    (g-right-inv : HasRightInverse B-setoid C-setoid g-func)
    where
    private
        A = A-setoid .Carrier
        B = B-setoid .Carrier
        C = C-setoid .Carrier

        _~₁_ = A-setoid ._≈_
        _~₂_ = B-setoid ._≈_
        _~₃_ = C-setoid ._≈_

        f : A → B
        f-inv : B → A

        g : B → C
        g-inv : C → B

        f-respects : Congruent _~₁_ _~₂_ f
        g-respects : Congruent _~₂_ _~₃_ g
        f-inv-respects : Congruent _~₂_ _~₁_ f-inv
        g-inv-respects : Congruent _~₃_ _~₂_ g-inv

        f = f-func .func
        f-respects = f-func .respects

        f-inv-func = f-right-inv .proj₁
        f-inv = f-inv-func .func
        f-inv-respects = f-inv-func .respects

        g = g-func .func
        g-respects = g-func .respects

        g-inv-func = g-right-inv .proj₁
        g-inv = g-inv-func .func
        g-inv-respects = g-inv-func .respects

        f-f-inv-x~x : ∀ {x} → f (f-inv x) ~₂ x
        f-f-inv-x~x = f-right-inv .proj₂

        g-g-inv-x~x : ∀ {x} → g (g-inv x) ~₃ x
        g-g-inv-x~x = g-right-inv .proj₂

        g∘f-right-inv : HasRightInverse A-setoid C-setoid (g-func ∘' f-func)
        g∘f-right-inv = HasRightInverse-conjunct g-func f-func g-right-inv f-right-inv

        open IsEquivalence (B-setoid .Setoid.isEquivalence) using () renaming (refl to refl₂; sym to sym₂; trans to trans₂)

    second-step-stable :
        {x : A} →
        (f-inv ∘ g-inv ∘ g ∘ f) x ~₁ x →
        (g-inv ∘ g ∘ f) x ~₂ f x
    second-step-stable {x} f'g'gfx~x = begin
        (g-inv ∘ g ∘ f) x               ≈⟨ sym₂ f-f-inv-x~x ⟩
        (f ∘ f-inv ∘ g-inv ∘ g ∘ f) x   ≈⟨ f-respects f'g'gfx~x ⟩
        f x                             ∎
        where open import Relation.Binary.Reasoning.Setoid B-setoid

    first-step-stable :
        {x : A} →
        (f-inv ∘ g-inv ∘ g ∘ f) x ~₁ x →
        (f-inv ∘ f) x ~₁ x
    first-step-stable {x} f'g'gfx~x = begin
        (f-inv ∘ f) x               ≈⟨ f-inv-respects (sym₂ (second-step-stable f'g'gfx~x)) ⟩
        (f-inv ∘ g-inv ∘ g ∘ f) x   ≈⟨ f'g'gfx~x ⟩
        x                           ∎
        where open import Relation.Binary.Reasoning.Setoid A-setoid

module BijectionBuilding
    {A-setoid : Setoid a ℓ₁} {B-setoid : Setoid b ℓ₂}
    (f-func : SetoidFunction A-setoid B-setoid)
    (f-right-inv : HasRightInverse A-setoid B-setoid f-func)
    (g-func : SetoidFunction B-setoid A-setoid)
    (g-right-inv : HasRightInverse B-setoid A-setoid g-func)
    where
    -- f and g are essentially surjections, given right-inv→surjective.
    -- The condition HasRightInverse is a bit stronger than plain surjection though, since it requires the inverse be congruent.

    private
        A = A-setoid .Carrier
        B = B-setoid .Carrier

        _~₁_ = A-setoid ._≈_
        _~₂_ = B-setoid ._≈_

        f : A → B
        f-inv : B → A

        g : B → A
        g-inv : A → B

        f-respects : Congruent _~₁_ _~₂_ f
        g-respects : Congruent _~₂_ _~₁_ g
        f-inv-respects : Congruent _~₂_ _~₁_ f-inv
        g-inv-respects : Congruent _~₁_ _~₂_ g-inv

        f = f-func .func
        f-respects = f-func .respects

        f-inv-func = f-right-inv .proj₁
        f-inv = f-inv-func .func
        f-inv-respects = f-inv-func .respects

        g = g-func .func
        g-respects = g-func .respects

        g-inv-func = g-right-inv .proj₁
        g-inv = g-inv-func .func
        g-inv-respects = g-inv-func .respects

        f-f-inv-x~x : ∀ {x} → f (f-inv x) ~₂ x
        f-f-inv-x~x = f-right-inv .proj₂

        g-g-inv-x~x : ∀ {x} → g (g-inv x) ~₁ x
        g-g-inv-x~x = g-right-inv .proj₂

        g∘f-right-inv : HasRightInverse A-setoid A-setoid (g-func ∘' f-func)
        g∘f-right-inv = HasRightInverse-conjunct g-func f-func g-right-inv f-right-inv

        open IsEquivalence (A-setoid .Setoid.isEquivalence) using () renaming (reflexive to reflexive₁; refl to refl₁; sym to sym₁; trans to trans₁)
        open IsEquivalence (B-setoid .Setoid.isEquivalence) using () renaming (reflexive to reflexive₂; refl to refl₂; sym to sym₂; trans to trans₂)
    open Repeat (f-func ∘' g-func) using () renaming (repeat to repeat-fg; repeat-pf-swap to repeat-pf-swap-fg; repeat' to repeat'-fg; repeat'-f to repeat'-fg-swap; repeat'-cong-in-x to repeat'-fg-cong-in-x)
    open Repeat (g-func ∘' f-func) using () renaming (repeat to repeat-gf; repeat-pf-swap to repeat-pf-swap-gf; repeat' to repeat'-gf; repeat'-f to repeat'-gf-swap; repeat'-cong-in-x to repeat'-gf-cong-in-x)
    open SequenceBreak A-setoid (g-func ∘' f-func) (f-inv-func ∘' g-inv-func) using (Unbroken; UnbrokenAt; BreaksBefore; EverBreaks; NeverBreaks; EverTerminates; ever-terminates-cong; not-ever-terminates-is-never-terminates; never-terminates→never-breaks; ever-breaks→ever-terminates; contradict-breaks-terminates; never-breaks-cong; unbroken-pass-forward; unbroken-pass-back; breaks-at-pass-forward; breaks-at-pass-backward; ever-terminates-pass-backward; ever-terminates-pass-forward; never-breaks-pass-forward; never-breaks-pass-backward; unbroken-at-cong-in-x)
    open SequenceBreak using () renaming (BreaksAt to BreaksAt'; EverBreaks to EverBreaks'; EverTerminates to EverTerminates'; breaks-at-dec to breaks-at-dec'; Unbroken to Unbroken'; ever-terminates→ever-breaks to ever-terminates→ever-breaks'; ever-breaks→ever-terminates to ever-breaks→ever-terminates')

    -- open Stability g-func g-right-inv f-func f-right-inv using () renaming (first-step-stable to fg-stable→g-left-inv; second-step-stable to fg-stable→f-weak-left-inv)

    -- Then the idea is that if EverBreaks (equivalently, EverTerminates) is decidable for all inputs,
    -- then we can just make a bijection.


    repeat'-invert-f : (x : A) (n : ℕ) → repeat'-fg (f x) n ~₂ f (repeat'-gf x n)
    repeat'-invert-f x zero = refl₂
    repeat'-invert-f x (suc n) = (f-respects ∘ g-respects) (repeat'-invert-f x n)

    repeat'-invert-g : (y : B) (n : ℕ) → repeat'-gf (g y) n ~₁ g (repeat'-fg y n)
    repeat'-invert-g y zero = refl₁
    repeat'-invert-g y (suc n) = (g-respects ∘ f-respects) (repeat'-invert-g y n)


    -- Some properties for telling which function it breaks on
    module _ (x : A) where
        open Stability f-func f-right-inv g-func g-right-inv using (first-step-stable; second-step-stable)

        UnbrokenF : Set ℓ₁
        UnbrokenF = (f-inv ∘ f) x ~₁ x

        UnbrokenAtF : ℕ → Set ℓ₁
        UnbrokenAtF n = (f-inv ∘ f) (repeat'-gf x n) ~₁ repeat'-gf x n

        BreaksAtF : ℕ → Set ℓ₁
        BreaksAtF n = ¬ UnbrokenAtF n

        open import Plasmaduck.Counting.GeneralizedMinimum BreaksAtF UnbrokenAtF using () renaming (NoValueBelow to UnbrokenBeforeF) public


        UnbrokenG : Set ℓ₂
        UnbrokenG = (g-inv ∘ g ∘ f) x ~₂ f x

        UnbrokenAtG : ℕ → Set ℓ₂
        UnbrokenAtG n = (g-inv ∘ g ∘ f) (repeat'-gf x n) ~₂ f (repeat'-gf x n)

        BreaksAtG : ℕ → Set ℓ₂
        BreaksAtG n = ¬ UnbrokenAtG n

        open import Plasmaduck.Counting.GeneralizedMinimum BreaksAtG UnbrokenAtG using () renaming (NoValueBelow to UnbrokenBeforeG) public


        -- and the equivalence:
        unbroken-step₁ : Unbroken x → UnbrokenF
        unbroken-step₁ = first-step-stable

        unbroken-step₂ : Unbroken x → UnbrokenG
        unbroken-step₂ = second-step-stable

        merge-unbroken : UnbrokenF → UnbrokenG → Unbroken x
        merge-unbroken f'fx~x g'gfx~fx = trans₁ (f-inv-respects g'gfx~fx) f'fx~x

        unbroken-at-step₁ : (n : ℕ) → UnbrokenAt x n → UnbrokenAtF n
        unbroken-at-step₁ _ = first-step-stable

        unbroken-at-step₂ : (n : ℕ) → UnbrokenAt x n → UnbrokenAtG n
        unbroken-at-step₂ _ = second-step-stable

        merge-unbroken-at : (n : ℕ) → UnbrokenAtF n → UnbrokenAtG n → UnbrokenAt x n
        merge-unbroken-at _ f'fx~x g'gfx~fx = trans₁ (f-inv-respects g'gfx~fx) f'fx~x


    module _ (x : A) (n : ℕ) where

        unbroken-at-f-pass-forward : UnbrokenAtF x (suc n) → UnbrokenAtF ((g ∘ f) x) n
        unbroken-at-f-pass-forward x-unbroken-at-sn = begin
            (f-inv ∘ f) (repeat'-gf ((g ∘ f) x) n)  ≈⟨ (f-inv-respects ∘ f-respects) (reflexive₁ (≡-sym (repeat'-gf-swap x n))) ⟩
            (f-inv ∘ f ∘ g ∘ f) (repeat'-gf x n)    ≈⟨ refl₁ ⟩
            (f-inv ∘ f) (repeat'-gf x (suc n))      ≈⟨ x-unbroken-at-sn ⟩
            repeat'-gf x (suc n)                    ≈⟨ refl₁ ⟩
            (g ∘ f) (repeat'-gf x n)                ≈⟨ reflexive₁ (repeat'-gf-swap x n) ⟩
            repeat'-gf ((g ∘ f) x) n                ∎
            where open import Relation.Binary.Reasoning.Setoid A-setoid

        unbroken-at-f-pass-backward : UnbrokenAtF ((g ∘ f) x) n → UnbrokenAtF x (suc n)
        unbroken-at-f-pass-backward gfx-unbroken-at-n = begin
            (f-inv ∘ f) (repeat'-gf x (suc n))      ≈⟨ refl₁ ⟩
            (f-inv ∘ f ∘ g ∘ f) (repeat'-gf x n)    ≈⟨ (f-inv-respects ∘ f-respects) (reflexive₁ (repeat'-gf-swap x n)) ⟩
            (f-inv ∘ f) (repeat'-gf ((g ∘ f) x) n)  ≈⟨ gfx-unbroken-at-n ⟩
            repeat'-gf ((g ∘ f) x) n                ≈⟨ reflexive₁ (≡-sym (repeat'-gf-swap x n)) ⟩
            (g ∘ f) (repeat'-gf x n)                ≈⟨ refl₁ ⟩
            repeat'-gf x (suc n)                    ∎
            where open import Relation.Binary.Reasoning.Setoid A-setoid

        unbroken-at-g-pass-forward : UnbrokenAtG x (suc n) → UnbrokenAtG ((g ∘ f) x) n
        unbroken-at-g-pass-forward x-unbroken-at-sn = begin
            (g-inv ∘ g ∘ f) (repeat'-gf ((g ∘ f) x) n)  ≈⟨ (g-inv-respects ∘ g-respects ∘ f-respects) (reflexive₁ (≡-sym (repeat'-gf-swap x n))) ⟩
            (g-inv ∘ g ∘ f ∘ g ∘ f) (repeat'-gf x n)    ≈⟨ refl₂ ⟩
            (g-inv ∘ g ∘ f) (repeat'-gf x (suc n))      ≈⟨ x-unbroken-at-sn ⟩
            f (repeat'-gf x (suc n))                    ≈⟨ refl₂ ⟩
            (f ∘ g ∘ f) (repeat'-gf x n)                ≈⟨ f-respects (reflexive₁ (repeat'-gf-swap x n)) ⟩
            f (repeat'-gf ((g ∘ f) x) n)                ∎
            where open import Relation.Binary.Reasoning.Setoid B-setoid

        unbroken-at-g-pass-back : UnbrokenAtG ((g ∘ f) x) n → UnbrokenAtG x (suc n)
        unbroken-at-g-pass-back gfx-unbroken-at-n = begin
            (g-inv ∘ g ∘ f) (repeat'-gf x (suc n))      ≈⟨ refl₂ ⟩
            (g-inv ∘ g ∘ f ∘ g ∘ f) (repeat'-gf x n)    ≈⟨ (g-inv-respects ∘ g-respects ∘ f-respects) (reflexive₁ (repeat'-gf-swap x n)) ⟩
            (g-inv ∘ g ∘ f) (repeat'-gf ((g ∘ f) x) n)  ≈⟨ gfx-unbroken-at-n ⟩
            f (repeat'-gf ((g ∘ f) x) n)                ≈⟨ f-respects (reflexive₁ (≡-sym (repeat'-gf-swap x n))) ⟩
            (f ∘ g ∘ f) (repeat'-gf x n)                ≈⟨ refl₂ ⟩
            f (repeat'-gf x (suc n))                    ∎
            where open import Relation.Binary.Reasoning.Setoid B-setoid

    module _ where
        open import Plasmaduck.Counting.SequenceProperty A-setoid UnbrokenAtF BreaksAtF using (module ContradictForwardBackward)
        open ContradictForwardBackward (g-func ∘' f-func) apply unbroken-at-f-pass-forward unbroken-at-f-pass-backward using () renaming (
            contradict-forward to breaks-at-f-pass-forward;
            contradict-backward to breaks-at-f-pass-backward
            ) public

    module _ where
        open import Plasmaduck.Counting.SequenceProperty A-setoid UnbrokenAtG BreaksAtG using (module ContradictForwardBackward)
        open ContradictForwardBackward (g-func ∘' f-func) apply unbroken-at-g-pass-forward unbroken-at-g-pass-back using () renaming (
            contradict-forward to breaks-at-g-pass-forward;
            contradict-backward to breaks-at-g-pass-backward
            ) public

    unbroken-at-f-cong-in-x : (n : ℕ) → CongruentProperty A-setoid (λ x → UnbrokenAtF x n)
    unbroken-at-f-cong-in-x n {x} {y} x~y x-unbroken-on-f-at-n = begin
        (f-inv ∘ f) (repeat'-gf y n)    ≈⟨ (f-inv-respects ∘ f-respects) (repeat'-gf-cong-in-x n (sym₁ x~y)) ⟩
        (f-inv ∘ f) (repeat'-gf x n)   ≈⟨ x-unbroken-on-f-at-n ⟩
        repeat'-gf x n                  ≈⟨ repeat'-gf-cong-in-x n x~y ⟩
        repeat'-gf y n                  ∎
        where open import Relation.Binary.Reasoning.Setoid A-setoid

    breaks-at-f-cong-in-x : (n : ℕ) → CongruentProperty A-setoid (λ x → BreaksAtF x n)
    breaks-at-f-cong-in-x n = negation-cong A-setoid (λ x → UnbrokenAtF x n) (unbroken-at-f-cong-in-x n)

    unbroken-at-g-cong-in-x : (n : ℕ) → CongruentProperty A-setoid (λ x → UnbrokenAtG x n)
    unbroken-at-g-cong-in-x n {x} {y} x~y x-unbroken-on-g-at-n = begin
        (g-inv ∘ g ∘ f) (repeat'-gf y n)    ≈⟨ (g-inv-respects ∘ g-respects ∘ f-respects) (repeat'-gf-cong-in-x n (sym₁ x~y)) ⟩
        (g-inv ∘ g ∘ f) (repeat'-gf x n)   ≈⟨ x-unbroken-on-g-at-n ⟩
        f (repeat'-gf x n)                  ≈⟨ f-respects (repeat'-gf-cong-in-x n x~y) ⟩
        f (repeat'-gf y n)                  ∎
        where open import Relation.Binary.Reasoning.Setoid B-setoid

    breaks-at-g-cong-in-x : (n : ℕ) → CongruentProperty A-setoid (λ x → BreaksAtG x n)
    breaks-at-g-cong-in-x n = negation-cong A-setoid (λ x → UnbrokenAtG x n) (unbroken-at-g-cong-in-x n)

    open ContradictingSequenceProperties A-setoid (g-func ∘' f-func) UnbrokenAt BreaksAtF (λ {x} {n} f-broken unbroken → f-broken (unbroken-at-step₁ x n unbroken)) unbroken-pass-forward unbroken-pass-back breaks-at-f-pass-forward breaks-at-f-pass-backward unbroken-at-cong-in-x breaks-at-f-cong-in-x using () renaming (
        EverBreaks to EverBreaksOnF;
        BreaksBefore to BreaksBeforeF;
        EverTerminates to EverTerminatesOnF;
        TerminatesAt to TerminatesAtF;
        ever-terminates-pass-forward to ever-terminates-f-pass-forward;
        ever-terminates-pass-backward to ever-terminates-f-pass-backward;
        ever-terminates-cong to ever-terminates-on-f-cong
        ) public


    module _ where
        -- We need to do some type shifting for g

        module MessyGTypes where
            SpecialBreaksAtG : A → ℕ → Set (ℓ₁ ⊔ ℓ₂)
            SpecialBreaksAtG x n = BreaksAtG x n × UnbrokenAtF x n

            module _ (x : A) (n : ℕ) where
                forward : SpecialBreaksAtG x (suc n) → SpecialBreaksAtG ((g ∘ f) x) n
                forward (x-breaks-on-g-at-sn , x-unbroken-on-f-at-sn) = breaks-at-g-pass-forward x n x-breaks-on-g-at-sn , unbroken-at-f-pass-forward x n x-unbroken-on-f-at-sn

                backward : SpecialBreaksAtG ((g ∘ f) x) n → SpecialBreaksAtG x (suc n)
                backward (fx-breaks-on-g-at-n , fx-unbroken-on-f-at-n) = breaks-at-g-pass-backward x n fx-breaks-on-g-at-n , unbroken-at-f-pass-backward x n fx-unbroken-on-f-at-n

            special-breaks-at-g-cong-in-x : (n : ℕ) → CongruentProperty A-setoid (λ x → SpecialBreaksAtG x n)
            special-breaks-at-g-cong-in-x n x~y (x-breaks-on-g , x-unbroken-on-f) = breaks-at-g-cong-in-x n x~y x-breaks-on-g , unbroken-at-f-cong-in-x n x~y x-unbroken-on-f

            open ContradictingSequenceProperties A-setoid (g-func ∘' f-func) UnbrokenAt SpecialBreaksAtG ((λ {x} {n} (g-broken , _) unbroken → g-broken (unbroken-at-step₂ x n unbroken))) unbroken-pass-forward unbroken-pass-back forward backward unbroken-at-cong-in-x special-breaks-at-g-cong-in-x using () renaming (EverBreaks to EverBreaksOnF;
                EverTerminates to SpecialEverTerminatesOnG;
                TerminatesAt to SpecialTerminatesAtG;
                ever-terminates-pass-forward to special-ever-terminates-g-pass-forward;
                ever-terminates-pass-backward to special-ever-terminates-g-pass-backward;
                ever-terminates-cong to special-ever-terminates-g-cong
                )

            -- The reason for the suc is that, since f and g alternate, g comes after an extra f, and we need that extra f to be unbroken.
            -- g f g f g f x
            --   ^ unbroken, despite having the same index as the broken g
            -- ^ broken here
            TerminatesAtG : A → ℕ → Set (ℓ₁ ⊔ ℓ₂)
            TerminatesAtG x n = BreaksAtG x n × UnbrokenBeforeF x (suc n) × UnbrokenBeforeG x n

            EverTerminatesOnG : A → Set (ℓ₁ ⊔ ℓ₂)
            EverTerminatesOnG x = Σ ℕ (TerminatesAtG x)

            module _ {x : A} {n : ℕ} where
                special→normal : SpecialTerminatesAtG x n → TerminatesAtG x n
                special→normal ((x-breaks-on-g-at-n , x-unbroken-on-f-at-n) , x-unbroken-below-n) = x-breaks-on-g-at-n , (λ (m , m<sn) → case ≤→<≡ (s≤s⁻¹ m<sn) of λ { (inj₁ m<n) → unbroken-at-step₁ x m (x-unbroken-below-n (m , m<n)); (inj₂ m=n) → change-type (cong (UnbrokenAtF x) (≡-sym m=n)) x-unbroken-on-f-at-n}) , (λ (m , m<n) → unbroken-at-step₂ x m (x-unbroken-below-n (m , m<n)))

                normal→special : TerminatesAtG x n → SpecialTerminatesAtG x n
                normal→special (x-breaks-on-g-at-n , x-unbroken-on-f-below-sn , x-unbroken-on-g-below-n) = (x-breaks-on-g-at-n , x-unbroken-on-f-below-sn (n , n≤n)) , λ (m , m<n) → merge-unbroken-at x m (x-unbroken-on-f-below-sn (m , ≤-trans m<n n≤sn)) (x-unbroken-on-g-below-n (m , m<n))

            module _ {x : A} where
                ever-special→normal : SpecialEverTerminatesOnG x → EverTerminatesOnG x
                ever-special→normal (n , special-terminates-at-n) = n , special→normal special-terminates-at-n

                ever-normal→special : EverTerminatesOnG x → SpecialEverTerminatesOnG x
                ever-normal→special (n , terminates-at-n) = n , normal→special terminates-at-n

            module _ (x : A) (p-x-at-zero : UnbrokenAt x 0) where
                ever-terminates-g-pass-forward : EverTerminatesOnG x → EverTerminatesOnG ((g ∘ f) x)
                ever-terminates-g-pass-forward = ever-special→normal ∘ (special-ever-terminates-g-pass-forward x p-x-at-zero) ∘ ever-normal→special

            ever-terminates-on-g-cong : CongruentProperty A-setoid EverTerminatesOnG
            ever-terminates-on-g-cong x~y = ever-special→normal ∘ special-ever-terminates-g-cong x~y ∘ ever-normal→special
        open MessyGTypes using (
            TerminatesAtG;
            EverTerminatesOnG;
            ever-terminates-g-pass-forward;
            ever-terminates-on-g-cong
            ) public

        open ContradictingSequenceProperties A-setoid (g-func ∘' f-func) UnbrokenAt BreaksAtG (λ {x} {n} g-broken unbroken → g-broken (unbroken-at-step₂ x n unbroken)) unbroken-pass-forward unbroken-pass-back breaks-at-g-pass-forward breaks-at-g-pass-backward unbroken-at-cong-in-x breaks-at-g-cong-in-x using () renaming (
            EverBreaks to EverBreaksOnG;
            BreaksBefore to BreaksBeforeG
            ) public


    module _ (x : A) where
        f-terminates→breaks : EverTerminatesOnF x → EverBreaksOnF x
        f-terminates→breaks (m , breaks-at-m , _) = m , breaks-at-m

        g-terminates→breaks : EverTerminatesOnG x → EverBreaksOnG x
        g-terminates→breaks (m , breaks-at-m , _) = m , breaks-at-m

        breaks-before-f : (n : ℕ) → BreaksBeforeF x n → BreaksBefore x n
        breaks-before-f n ((m , m<n) , breaks-on-f-at-m) = (m , m<n) , breaks-on-f-at-m ∘ (unbroken-at-step₁ x m)

        breaks-before-g : (n : ℕ) → BreaksBeforeG x n → BreaksBefore x n
        breaks-before-g n ((m , m<n) , breaks-on-g-at-m) = (m , m<n) , breaks-on-g-at-m ∘ (unbroken-at-step₂ x m)
        -- the inverse is breaks-before-split. It depends on decidability of _~₁_ (or _~₂_, admittedly), so it's defined below.

        ever-breaks-f : EverBreaksOnF x → EverBreaks x
        ever-breaks-f (m , x-breaks-on-f-at-m) = m , x-breaks-on-f-at-m ∘ (unbroken-at-step₁ x m)

        ever-breaks-g : EverBreaksOnG x → EverBreaks x
        ever-breaks-g (m , x-breaks-on-g-at-m) = m , x-breaks-on-g-at-m ∘ (unbroken-at-step₂ x m)

    not-terminate-on-both-f-g : (x : A) → EverTerminatesOnF x → EverTerminatesOnG x → ⊥
    not-terminate-on-both-f-g x
        (m , breaks-on-f-at-m , unbroken-below-m)
        (n , breaks-on-g-at-n , unbroken-on-f-below-sn , unbroken-on-g-below-n) with <-cmp m n
    ... | tri< m<n _ _ = breaks-on-f-at-m (unbroken-on-f-below-sn (m , ≤-trans m<n n≤sn))
    ... | tri≈ _ m=n _ = breaks-on-f-at-m (change-type (cong (UnbrokenAtF x) (≡-sym m=n)) (unbroken-on-f-below-sn (n , n≤n)))
    ... | tri> _ _ m>n = breaks-on-g-at-n (unbroken-at-step₂ x n (unbroken-below-m (n , m>n)))

    module _ (_~₁?_ : Decidable _~₁_) where
        open Stability f-func f-right-inv g-func g-right-inv using () renaming (first-step-stable to gf-stable→f-left-inv; second-step-stable to gf-stable→g-weak-left-inv)

        translate-unbroken :
            (x : A) →
            Unbroken' A-setoid (g-func ∘' f-func) (f-inv-func ∘' g-inv-func) x →
            Unbroken' A-setoid (g-func ∘' f-func) (f-inv-func ∘' g-inv-func) (g (f x)) →
            Unbroken' B-setoid (f-func ∘' g-func) (g-inv-func ∘' f-inv-func) (f x)
        translate-unbroken x gf-stable-on-x gf-stable-on-gfx = begin
            (g-inv ∘ f-inv ∘ f ∘ g ∘ f) x   ≈⟨ g-inv-respects (gf-stable→f-left-inv gf-stable-on-gfx) ⟩
            (g-inv ∘ g ∘ f) x               ≈⟨ gf-stable→g-weak-left-inv gf-stable-on-x ⟩
            f x                             ∎
            where open import Relation.Binary.Reasoning.Setoid B-setoid

        breaks-at-translator :
            (x : A) →
            (m : ℕ) →
            BreaksAt' B-setoid (f-func ∘' g-func) (g-inv-func ∘' f-inv-func) (f x) m →
            BreaksAt' A-setoid (g-func ∘' f-func) (f-inv-func ∘' g-inv-func) x m ⊎
            BreaksAt' A-setoid (g-func ∘' f-func) (f-inv-func ∘' g-inv-func) x (suc m)
        breaks-at-translator x m fg^m[fx]≉f'g'gf[fg^m[fx]] with breaks-at-dec' A-setoid (g-func ∘' f-func) (f-inv-func ∘' g-inv-func) _~₁?_ x m | breaks-at-dec' A-setoid (g-func ∘' f-func) (f-inv-func ∘' g-inv-func) _~₁?_ x (suc m)
        ... | inj₁ breaks-at-x | _ = inj₁ breaks-at-x
        ... | _ | inj₁ breaks-at-gfx = inj₂ breaks-at-gfx
        ... | inj₂ unbroken-at-gf^m[x] | inj₂ unbroken-at-gf^[m+1][x] = ⊥-elim (fg^m[fx]≉f'g'gf[fg^m[fx]] (begin
            (g-inv ∘ f-inv) (repeat'-fg (f x) (suc m))   ≈⟨ refl₂ ⟩
            (g-inv ∘ f-inv ∘ f ∘ g) (repeat'-fg (f x) m) ≈⟨ (g-inv-respects ∘ f-inv-respects ∘ f-respects ∘ g-respects) (repeat'-invert-f x m) ⟩
            (g-inv ∘ f-inv ∘ f ∘ g ∘ f) (repeat'-gf x m) ≈⟨ translate-unbroken (repeat'-gf x m) unbroken-at-gf^m[x] unbroken-at-gf^[m+1][x] ⟩
            f (repeat'-gf x m)                           ≈⟨ sym₂ (repeat'-invert-f x m) ⟩
            (repeat'-fg (f x) m)                         ∎
            ))
            where open import Relation.Binary.Reasoning.Setoid B-setoid

        ever-breaks-equivalence :
            (x : A) →
            EverBreaks' B-setoid (f-func ∘' g-func) (g-inv-func ∘' f-inv-func) (f x) →
            EverBreaks' A-setoid (g-func ∘' f-func) (f-inv-func ∘' g-inv-func) x
        ever-breaks-equivalence x (m , fx-breaks-at-m) with breaks-at-translator x m fx-breaks-at-m
        ... | inj₁ breaks-at-x = m , breaks-at-x
        ... | inj₂ breaks-at-gfx = suc m , breaks-at-gfx

        ever-terminates-equivalence :
            (x : A) →
            EverTerminates' B-setoid (f-func ∘' g-func) (g-inv-func ∘' f-inv-func) (f x) →
            EverTerminates' A-setoid (g-func ∘' f-func) (f-inv-func ∘' g-inv-func) x
        ever-terminates-equivalence x fx-terminates-in-B =
            ever-breaks→ever-terminates' A-setoid (g-func ∘' f-func) (f-inv-func ∘' g-inv-func) _~₁?_ (
                ever-breaks-equivalence x (
                    ever-terminates→ever-breaks' B-setoid (f-func ∘' g-func) (g-inv-func ∘' f-inv-func) fx-terminates-in-B
                )
            )


    module _ (_~₁?_ : Decidable _~₁_) (_~₂?_ : Decidable _~₂_) where
        module _ (x : A) where
            unbroken-at-f-dec : DecidableProperty (UnbrokenAtF x)
            unbroken-at-f-dec n = (f-inv ∘ f) (repeat'-gf x n) ~₁? repeat'-gf x n

            unbroken-at-g-dec : DecidableProperty (UnbrokenAtG x)
            unbroken-at-g-dec n = (g-inv ∘ g ∘ f) (repeat'-gf x n) ~₂? f (repeat'-gf x n)

            -- Only needs _₁?_ ⊎ _~₂?_, admittedly
            breaks-before-split : (n : ℕ) → BreaksBefore x n → BreaksBeforeF x n ⊎ BreaksBeforeG x n
            breaks-before-split n ((m , m<n) , breaks-at-m) with invert-product (unbroken-at-f-dec m) (λ q → breaks-at-m (uncurry (merge-unbroken-at x m) q))
            ... | inj₁ f-breaks-at-m = inj₁ ((m , m<n) , f-breaks-at-m)
            ... | inj₂ g-breaks-at-m = inj₂ ((m , m<n) , g-breaks-at-m)

            termination-split :
                EverTerminates x →
                EverTerminatesOnF x ⊎ EverTerminatesOnG x
            termination-split (n , x-breaks-at-n , unbroken-below-n) with unbroken-at-f-dec n | unbroken-at-g-dec n
            ... | no broken-on-f | _ = inj₁ (n , broken-on-f , (λ (m , m<n) → unbroken-below-n (m , m<n)))
            ... | yes unbroken-on-f | no broken-on-g = inj₂ (n , broken-on-g ,
                    (λ (m , m<sn) → case ≤→<≡ (s≤s⁻¹ m<sn) of λ {
                        (inj₁ m<n) → unbroken-at-step₁ x m (unbroken-below-n (m , m<n));
                        (inj₂ m=n) → change-type (cong (λ q → (f-inv ∘ f) (repeat'-gf x q) ~₁ repeat'-gf x q) (≡-sym m=n)) unbroken-on-f
                    }) ,
                    (λ (m , m<n) → unbroken-at-step₂ x m (unbroken-below-n (m , m<n)))
                )
            ... | yes unbroken-on-f | yes unbroken-on-g = ⊥-elim (x-breaks-at-n (trans₁ (f-inv-respects unbroken-on-g) unbroken-on-f))

            termination-merge-f : EverTerminatesOnF x → EverTerminates x
            termination-merge-f = ever-breaks→ever-terminates _~₁?_ ∘ (ever-breaks-f x) ∘ (f-terminates→breaks x)

            termination-merge-g : EverTerminatesOnG x → EverTerminates x
            termination-merge-g = ever-breaks→ever-terminates _~₁?_ ∘ (ever-breaks-g x) ∘ (g-terminates→breaks x)

        build-bijection : DecidableProperty EverTerminates → Bijection A-setoid B-setoid
        build-bijection ever-terminates-dec = record {
            to = to;
            cong = to-cong;
            bijective = to-inj , to-surj
            }
            where
                not-ever-terminates→never-breaks : {x : A} → ¬ (EverTerminates x) → NeverBreaks x
                not-ever-terminates→never-breaks {x = x} pf = never-terminates→never-breaks _~₁?_ (not-ever-terminates-is-never-terminates _~₁?_ pf)

                termination-dec : ∀ x → EverTerminates x ⊎ NeverBreaks x
                termination-dec x with ever-terminates-dec x
                ... | yes x-terminates = inj₁ x-terminates
                ... | no not-x-terminates = inj₂ (not-ever-terminates→never-breaks not-x-terminates)

                termination-contradict : ∀ {x y} → x ~₁ y → NeverBreaks x → EverTerminates y → ⊥
                termination-contradict {y = y} x~y x-never-breaks y-ever-terminates = contradict-breaks-terminates (never-breaks-cong x~y x-never-breaks) y-ever-terminates

                termination-on-both-f-g-contradict : ∀ {x y} → x ~₁ y → EverTerminatesOnF x → EverTerminatesOnG y → ⊥
                termination-on-both-f-g-contradict {y = y} x~y x-terminates-on-f y-terminates-on-g = not-terminate-on-both-f-g y (ever-terminates-on-f-cong x~y x-terminates-on-f) y-terminates-on-g


                to-helper : (x : A) → EverTerminatesOnF x ⊎ EverTerminatesOnG x → B
                to-helper x (inj₁ _) = g-inv x
                to-helper x (inj₂ _) = f x

                to : A → B
                to x with termination-dec x
                ... | (inj₂ _) = f x -- arbitrary between f and g-inv
                ... | (inj₁ pf) = to-helper x (termination-split x pf)

                to-cong : Congruent _~₁_ _~₂_ to
                to-cong {x = x} {y} x~y with termination-dec x | termination-dec y
                ... | inj₂ x-never-breaks | inj₂ y-never-breaks = f-respects x~y
                ... | inj₂ x-never-breaks | inj₁ y-terminates = ⊥-elim (termination-contradict x~y x-never-breaks y-terminates)
                ... | inj₁ x-terminates   | inj₂ y-never-breaks = ⊥-elim (termination-contradict (sym₁ x~y) y-never-breaks x-terminates)
                ... | inj₁ x-terminates   | inj₁ y-terminates with termination-split x x-terminates | termination-split y y-terminates
                ...    | inj₁ x-terminates-on-f | inj₁ y-terminates-on-f = g-inv-respects x~y
                ...    | inj₁ x-terminates-on-f | inj₂ y-terminates-on-g = ⊥-elim (termination-on-both-f-g-contradict x~y x-terminates-on-f y-terminates-on-g)
                ...    | inj₂ x-terminates-on-g | inj₁ y-terminates-on-f = ⊥-elim (termination-on-both-f-g-contradict (sym₁ x~y) y-terminates-on-f x-terminates-on-g)
                ...    | inj₂ x-terminates-on-g | inj₂ y-terminates-on-g = f-respects x~y


                -------------------
                --- Injectivity ---
                -------------------

                {-
                    How do we know to is injective?
                    Suppose x and y map to the same thing.
                    Obviously, f is congruent and g-inv is congruent, so if to resorts to the same function then it's congruent.

                    So suppose to resorts to f for x and g-inv for y.
                    That means:
                    - y terminates on F
                    - x either terminates on G or does not terminate.

                    So we have

                    x ----f--->
                                to x/y
                    y <---g----

                    So y = g(f(x)). If these f and g are unbroken, then x and y have the same termination properties.
                    (This is an obvious contradiction, assuming we can prove f and g are unbroken.)

                    Obviously, the termination properties of y don't matter.
                    If x does not terminate, then f and g are unbroken.
                    If x terminates on g, first check.
                    - If n > 0, then x and y flow into one another. That is, this f and g are unbroken.
                    - If n = 0, then this g is broken. That is, (g-inv ∘ g) (f x) ≠ f x
                    But this means g-inv y ≠ f x, which is exactly to y ≠ to x, contradicting to y = to x.
                -}

                {-
                    to x ~₂ to y
                    reduces to
                    f x ~₂ to-helper y (termination-split y y-terminates)
                    in the context of NeverBreaks x and EverTerminates y
                -}
                contradict-breaks-terminates-via-to : (x y : A) → NeverBreaks x → (y-terminates : EverTerminates y) → f x ~₂ to-helper y (termination-split y y-terminates) → ⊥
                contradict-breaks-terminates-via-to x y x-never-breaks y-terminates to-x~to-y with termination-split y y-terminates
                ... | inj₁ y-terminates-on-f = termination-contradict {x = (g ∘ f) x} {y = y} (trans₁ (g-respects to-x~to-y) g-g-inv-x~x) (never-breaks-pass-forward x x-never-breaks) y-terminates
                ... | inj₂ y-terminates-on-g@(zero , _ , y-unbroken-f-≤-0 , _) = ⊥-elim (termination-contradict {x = x} {y = y} (begin
                    x               ≈⟨ sym₁ (unbroken-step₁ x (x-never-breaks 0)) ⟩
                    (f-inv ∘ f) x   ≈⟨ f-inv-respects to-x~to-y ⟩
                    (f-inv ∘ f) y   ≈⟨ y-unbroken-f-≤-0 (0 , s≤s z≤n) ⟩
                    y               ∎
                    ) x-never-breaks y-terminates) -- Technically, this proof involves a proof that x = y. However, I like to show the stronger result.
                    where open import Relation.Binary.Reasoning.Setoid A-setoid
                ... | inj₂ y-terminates-on-g@(suc m , _ , y-unbroken-f-≤-sm , y-unbroken-g-<-sm) = termination-contradict {x = (g ∘ f) x} {y = (g ∘ f) y} (g-respects to-x~to-y) (never-breaks-pass-forward x x-never-breaks) (ever-terminates-pass-forward y (merge-unbroken y (y-unbroken-f-≤-sm (0 , s≤s z≤n)) (y-unbroken-g-<-sm (0 , s≤s z≤n))) y-terminates)

                {-
                    Again, to x ~₂ to y reduces to g-inv x ~₂ f y in this context.
                -}
                contradict-f-g-terminates-via-to : (x y : A) → EverTerminatesOnF x → EverTerminatesOnG y → g-inv x ~₂ f y → ⊥
                contradict-f-g-terminates-via-to x y x-terminates-on-f (zero , y-breaks-on-g-at-0 , _) to-x~to-y = y-breaks-on-g-at-0 (begin
                    (g-inv ∘ g ∘ f) y       ≈⟨ (g-inv-respects ∘ g-respects) (sym₂ to-x~to-y) ⟩
                    (g-inv ∘ g ∘ g-inv) x   ≈⟨ g-inv-respects g-g-inv-x~x ⟩
                    g-inv x                 ≈⟨ to-x~to-y ⟩
                    f y                     ∎
                    ) where open import Relation.Binary.Reasoning.Setoid B-setoid
                contradict-f-g-terminates-via-to x y x-terminates-on-f y-terminates-on-g@(suc m , _ , y-unbroken-on-f-≤-sm , y-unbroken-on-g-<-sm) to-x~to-y = termination-on-both-f-g-contradict {x = x} {y = (g ∘ f) y} (begin
                        x               ≈⟨ sym₁ g-g-inv-x~x ⟩
                        (g ∘ g-inv) x   ≈⟨ g-respects to-x~to-y ⟩
                        (g ∘ f) y       ∎
                    ) x-terminates-on-f (ever-terminates-g-pass-forward y (begin
                        (f-inv ∘ g-inv ∘ g ∘ f) y       ≈⟨ (f-inv-respects ∘ g-inv-respects ∘ g-respects) (sym₂ to-x~to-y) ⟩
                        (f-inv ∘ g-inv ∘ g ∘ g-inv) x   ≈⟨ (f-inv-respects ∘ g-inv-respects) g-g-inv-x~x ⟩
                        (f-inv ∘ g-inv) x               ≈⟨ f-inv-respects to-x~to-y ⟩
                        (f-inv ∘ f) y                   ≈⟨ y-unbroken-on-f-≤-sm (0 , s≤s z≤n) ⟩
                        y                               ∎
                    ) y-terminates-on-g)
                    where open import Relation.Binary.Reasoning.Setoid A-setoid

                to-inj : Injective _~₁_ _~₂_ to
                to-inj {x} {y} to-x~to-y with termination-dec x | termination-dec y
                to-inj {x} {y} to-x~to-y | inj₂ x-never-breaks | inj₂ y-never-breaks = begin
                    x               ≈⟨ sym₁ (unbroken-step₁ x (x-never-breaks 0)) ⟩
                    (f-inv ∘ f) x   ≈⟨ f-inv-respects to-x~to-y ⟩
                    (f-inv ∘ f) y   ≈⟨ unbroken-step₁ y (y-never-breaks 0) ⟩
                    y               ∎
                    where open import Relation.Binary.Reasoning.Setoid A-setoid
                to-inj {x} {y} to-x~to-y | inj₂ x-never-breaks | inj₁ y-terminates = ⊥-elim (contradict-breaks-terminates-via-to x y x-never-breaks y-terminates to-x~to-y)
                to-inj {x} {y} to-x~to-y | inj₁ x-terminates   | inj₂ y-never-breaks = ⊥-elim (contradict-breaks-terminates-via-to y x y-never-breaks x-terminates (sym₂ to-x~to-y))
                to-inj {x} {y} to-x~to-y | inj₁ x-terminates   | inj₁ y-terminates with termination-split x x-terminates | termination-split y y-terminates
                ... | inj₁ x-terminates-on-f | inj₁ y-terminates-on-f = begin
                    x               ≈⟨ sym₁ g-g-inv-x~x ⟩
                    (g ∘ g-inv) x   ≈⟨ g-respects to-x~to-y ⟩
                    (g ∘ g-inv) y   ≈⟨ g-g-inv-x~x ⟩
                    y               ∎
                    where open import Relation.Binary.Reasoning.Setoid A-setoid
                ... | inj₁ x-terminates-on-f | inj₂ y-terminates-on-g = ⊥-elim (contradict-f-g-terminates-via-to x y x-terminates-on-f y-terminates-on-g to-x~to-y)
                ... | inj₂ x-terminates-on-g | inj₁ y-terminates-on-f = ⊥-elim (contradict-f-g-terminates-via-to y x y-terminates-on-f x-terminates-on-g (sym₂ to-x~to-y))
                ... | inj₂ (_ , _ , x-unbroken-f-≤ , _) | inj₂ (_ , _ , y-unbroken-f-≤ , _) = begin
                    x               ≈⟨ sym₁ (x-unbroken-f-≤ (0 , s≤s z≤n)) ⟩
                    (f-inv ∘ f) x   ≈⟨ f-inv-respects to-x~to-y ⟩
                    (f-inv ∘ f) y   ≈⟨ y-unbroken-f-≤ (0 , s≤s z≤n) ⟩
                    y               ∎
                    where open import Relation.Binary.Reasoning.Setoid A-setoid


                --------------------
                --- Surjectivity ---
                --------------------

                {-
                    What is the proof that to is surjective?

                    We split A and B into chains.

                    z is part of some chain. Note f (f-inv z) maps to z, so if (f-inv z) has the properties that cause it to be mapped by to via f, then z has an input associated with it.

                    So suppose f-inv z fails at one of the checks.
                    This means both:
                      termination-dec (f-inv z) -> inj₁ (f-inv z) terminates
                      termination-split (f-inv z) _ _ terminates -> terminates-on-f

                    That is, f-inv z terminates on f.
                    Which, along with unbroken before it info,
                    means ¬ (f-inv ∘ f) (repeat'-gf x n) ~₁ repeat'-gf x n
                    for some minimal n.

                    If this is a future x (if n > 0), then (g z) is part of the same chain, so obviously (g z) maps via g-inv through an unbroken piece of chain to z.
                    If n = 0, then ¬ (f-inv ∘ f) (f-inv z) ~₁ f-inv z
                    which means ¬ f-inv z ~₁ f-inv z
                    which is a blatant contradiction.
                -}

                to-inv-tracer : (x : A) → EverTerminatesOnF x ⊎ EverTerminatesOnG x → A
                to-inv-tracer x (inj₁ terminates-on-f) = g (f x)
                to-inv-tracer x (inj₂ terminates-on-g) = x

                to-inv : B → A
                to-inv y with termination-dec (f-inv y)
                ... | inj₂ _ = f-inv y
                ... | inj₁ pf = to-inv-tracer (f-inv y) (termination-split (f-inv y) pf)

                {-
                    I do this forcing stuff instead of abstracting because to and to-inv abstract over some of the same things,
                    and I was having trouble getting only one of them to abstract at a time.
                -}
                never-breaks-forces-to : {x : A} → NeverBreaks x → to x ≡ f x
                never-breaks-forces-to {x = x} x-never-breaks with termination-dec x
                ... | inj₂ x-never-breaks = ≡-refl
                ... | inj₁ x-terminates = ⊥-elim (termination-contradict refl₁ x-never-breaks x-terminates)

                to-helper-proof-cong : {x : A} → {pf₁ pf₂ : EverTerminates x} → to-helper x (termination-split x pf₁) ≡ to-helper x (termination-split x pf₂)
                to-helper-proof-cong {x = x} {pf₁} {pf₂} with termination-split x pf₁ | termination-split x pf₂
                ... | inj₁ _ | inj₁ _ = ≡-refl
                ... | inj₁ terminates-on-f | inj₂ terminates-on-g = ⊥-elim (not-terminate-on-both-f-g x terminates-on-f terminates-on-g)
                ... | inj₂ terminates-on-g | inj₁ terminates-on-f = ⊥-elim (not-terminate-on-both-f-g x terminates-on-f terminates-on-g)
                ... | inj₂ _ | inj₂ _ = ≡-refl

                terminates-forces-to : {x : A} → (pf : EverTerminates x) → to x ≡ to-helper x (termination-split x pf)
                terminates-forces-to {x = x} x-terminates with termination-dec x
                ... | inj₂ x-never-breaks = ⊥-elim (termination-contradict refl₁ x-never-breaks x-terminates)
                ... | inj₁ x-terminates = to-helper-proof-cong

                terminates-on-f-forces-to : {x : A} → EverTerminatesOnF x → to x ≡ g-inv x
                terminates-on-f-forces-to {x = x} x-terminates-on-f with termination-split x (termination-merge-f x x-terminates-on-f) | inspect (termination-split x) (termination-merge-f x x-terminates-on-f)
                ... | inj₁ x-terminates-on-f' | [ inspect-pf ] =
                    to x                                                                            ≡⟨ terminates-forces-to (termination-merge-f x x-terminates-on-f) ⟩
                    to-helper x (termination-split x (termination-merge-f x x-terminates-on-f))    ≡⟨ cong (to-helper x) inspect-pf ⟩
                    to-helper x (inj₁ x-terminates-on-f')                                          ≡⟨⟩
                    g-inv x                                                                         ∎
                    where open ≡-Reasoning
                ... | inj₂ x-terminates-on-g | _ = ⊥-elim (not-terminate-on-both-f-g x x-terminates-on-f x-terminates-on-g)

                terminates-on-g-forces-to : {x : A} → EverTerminatesOnG x → to x ≡ f x
                terminates-on-g-forces-to {x = x} x-terminates-on-g with termination-split x (termination-merge-g x x-terminates-on-g) | inspect (termination-split x) (termination-merge-g x x-terminates-on-g)
                ... | inj₂ x-terminates-on-g' | [ inspect-pf ] =
                    to x                                                                            ≡⟨ terminates-forces-to (termination-merge-g x x-terminates-on-g) ⟩
                    to-helper x (termination-split x (termination-merge-g x x-terminates-on-g))    ≡⟨ cong (to-helper x) inspect-pf ⟩
                    to-helper x (inj₂ x-terminates-on-g')                                          ≡⟨⟩
                    f x                                                                         ∎
                    where open ≡-Reasoning
                ... | inj₁ x-terminates-on-f | _ = ⊥-elim (not-terminate-on-both-f-g x x-terminates-on-f x-terminates-on-g)

                never-breaks-forces-to-inv : {y : B} → NeverBreaks (f-inv y) → to-inv y ≡ f-inv y
                never-breaks-forces-to-inv {y = y} f-inv-y-never-breaks with termination-dec (f-inv y)
                ... | inj₂ f-inv-y-never-breaks = ≡-refl
                ... | inj₁ f-inv-y-terminates = ⊥-elim (termination-contradict refl₁ f-inv-y-never-breaks f-inv-y-terminates)

                to-inv-tracer-proof-cong : {x : A} → {pf₁ pf₂ : EverTerminates x} → to-inv-tracer x (termination-split x pf₁) ≡ to-inv-tracer x (termination-split x pf₂)
                to-inv-tracer-proof-cong {x = x} {pf₁} {pf₂} with termination-split x pf₁ | termination-split x pf₂
                ... | inj₁ _ | inj₁ _ = ≡-refl
                ... | inj₁ terminates-on-f | inj₂ terminates-on-g = ⊥-elim (not-terminate-on-both-f-g x terminates-on-f terminates-on-g)
                ... | inj₂ terminates-on-g | inj₁ terminates-on-f = ⊥-elim (not-terminate-on-both-f-g x terminates-on-f terminates-on-g)
                ... | inj₂ _ | inj₂ _ = ≡-refl

                terminates-forces-to-inv : {y : B} → (pf : EverTerminates (f-inv y)) → to-inv y ≡ to-inv-tracer (f-inv y) (termination-split (f-inv y) pf)
                terminates-forces-to-inv {y = y} f-inv-y-terminates with termination-dec (f-inv y)
                ... | inj₂ f-inv-y-never-breaks = ⊥-elim (termination-contradict refl₁ f-inv-y-never-breaks f-inv-y-terminates)
                ... | inj₁ f-inv-y-terminates = to-inv-tracer-proof-cong

                terminates-on-f-forces-to-inv : {y : B} → EverTerminatesOnF (f-inv y) → to-inv y ~₁ g y
                terminates-on-f-forces-to-inv {y = y} f-inv-y-terminates-on-f with termination-split (f-inv y) (termination-merge-f (f-inv y) f-inv-y-terminates-on-f) | inspect (termination-split (f-inv y)) (termination-merge-f (f-inv y) f-inv-y-terminates-on-f)
                ... | inj₁ f-inv-y-terminates-on-f' | [ inspect-pf ] = begin
                    to-inv y            ≈⟨ reflexive₁ thing ⟩
                    (g ∘ f ∘ f-inv) y   ≈⟨ g-respects f-f-inv-x~x ⟩
                    g y                 ∎
                    where
                        thing : to-inv y ≡ (g ∘ f ∘ f-inv) y
                        thing =
                            to-inv y                                                                                                        ≡⟨ terminates-forces-to-inv (termination-merge-f (f-inv y) f-inv-y-terminates-on-f) ⟩
                            to-inv-tracer (f-inv y) (termination-split (f-inv y) (termination-merge-f (f-inv y) f-inv-y-terminates-on-f))   ≡⟨ cong (to-inv-tracer (f-inv y)) inspect-pf ⟩
                            to-inv-tracer (f-inv y) (inj₁ f-inv-y-terminates-on-f')                                                         ≡⟨⟩
                            (g ∘ f ∘ f-inv) y                                                                                               ∎
                            where open ≡-Reasoning
                        open import Relation.Binary.Reasoning.Setoid A-setoid
                ... | inj₂ f-inv-y-terminates-on-g | _ = ⊥-elim (not-terminate-on-both-f-g (f-inv y) f-inv-y-terminates-on-f f-inv-y-terminates-on-g)

                terminates-on-g-forces-to-inv : {y : B} → EverTerminatesOnG (f-inv y) → to-inv y ≡ f-inv y
                terminates-on-g-forces-to-inv {y = y} f-inv-y-terminates-on-g with termination-split (f-inv y) (termination-merge-g (f-inv y) f-inv-y-terminates-on-g) | inspect (termination-split (f-inv y)) (termination-merge-g (f-inv y) f-inv-y-terminates-on-g)
                ... | inj₂ f-inv-y-terminates-on-g' | [ inspect-pf ] =
                    to-inv y                                                                                                        ≡⟨ terminates-forces-to-inv (termination-merge-g (f-inv y) f-inv-y-terminates-on-g) ⟩
                    to-inv-tracer (f-inv y) (termination-split (f-inv y) (termination-merge-g (f-inv y) f-inv-y-terminates-on-g))   ≡⟨ cong (to-inv-tracer (f-inv y)) inspect-pf ⟩
                    to-inv-tracer (f-inv y) (inj₂ f-inv-y-terminates-on-g')                                                         ≡⟨⟩
                    f-inv y                                                                                                         ∎
                    where open ≡-Reasoning
                ... | inj₁ f-inv-y-terminates-on-f | _ = ⊥-elim (not-terminate-on-both-f-g (f-inv y) f-inv-y-terminates-on-f f-inv-y-terminates-on-g)


                module _ {y : B} where
                    ba-term-f : EverTerminatesOnF (f-inv y) → to (g y) ~₂ y
                    ba-term-f y-terminates-on-f@(zero , f-inv-y-breaks-on-f-at-0 , _) = ⊥-elim (f-inv-y-breaks-on-f-at-0 (begin
                        (f-inv ∘ f ∘ f-inv) y   ≈⟨ f-inv-respects f-f-inv-x~x ⟩
                        f-inv y                 ∎
                        )) where open import Relation.Binary.Reasoning.Setoid A-setoid
                    ba-term-f y-terminates-on-f@(suc m , _ , unbroken-<-sm) = begin
                        (to ∘ g) y                  ≈⟨ (to-cong ∘ g-respects) (sym₂ f-f-inv-x~x) ⟩
                        (to ∘ g ∘ f ∘ f-inv) y      ≈⟨ reflexive₂ (terminates-on-f-forces-to (ever-terminates-f-pass-forward (f-inv y) (unbroken-<-sm (0 , s≤s z≤n)) y-terminates-on-f)) ⟩
                        (g-inv ∘ g ∘ f ∘ f-inv) y   ≈⟨ unbroken-step₂ (f-inv y) (unbroken-<-sm (0 , s≤s z≤n)) ⟩
                        (f ∘ f-inv) y               ≈⟨ f-f-inv-x~x ⟩
                        y                           ∎
                        where open import Relation.Binary.Reasoning.Setoid B-setoid

                    ba-term-g : EverTerminatesOnG (f-inv y) → to (f-inv y) ~₂ y
                    ba-term-g y-terminates-on-g = trans₂ (reflexive₂ (terminates-on-g-forces-to y-terminates-on-g)) f-f-inv-x~x

                    ba-never-breaks : NeverBreaks (f-inv y) → to (f-inv y) ~₂ y
                    ba-never-breaks y-never-breaks = trans₂ (reflexive₂ (never-breaks-forces-to y-never-breaks)) f-f-inv-x~x

                    ba : to (to-inv y) ~₂ y
                    ba = case termination-dec (f-inv y) of λ {
                        (inj₁ f-inv-y-terminates) → case termination-split (f-inv y) f-inv-y-terminates of λ {
                            (inj₁ f-inv-y-terminates-on-f) → begin
                                (to ∘ to-inv) y ≈⟨ to-cong (terminates-on-f-forces-to-inv f-inv-y-terminates-on-f) ⟩
                                (to ∘ g) y      ≈⟨ ba-term-f f-inv-y-terminates-on-f ⟩
                                y               ∎;
                            (inj₂ f-inv-y-terminates-on-g) → begin
                                (to ∘ to-inv) y ≈⟨ to-cong (reflexive₁ (terminates-on-g-forces-to-inv f-inv-y-terminates-on-g)) ⟩
                                (to ∘ f-inv) y  ≈⟨ ba-term-g f-inv-y-terminates-on-g ⟩
                                y               ∎
                            };
                        (inj₂ f-inv-y-never-breaks) → begin
                            (to ∘ to-inv) y ≈⟨ to-cong (reflexive₁ (never-breaks-forces-to-inv f-inv-y-never-breaks)) ⟩
                            (to ∘ f-inv) y  ≈⟨ ba-never-breaks f-inv-y-never-breaks ⟩
                            y               ∎
                        }
                        where open import Relation.Binary.Reasoning.Setoid B-setoid

                to-surj : Surjective _~₁_ _~₂_ to
                to-surj = weak-right-inv→surjective A-setoid B-setoid (to which-is-cong to-cong) (to-inv , ba)

open BijectionBuilding using (build-bijection) public
