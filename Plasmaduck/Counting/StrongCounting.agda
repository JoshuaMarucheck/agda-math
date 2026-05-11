open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; inspect; cong; Reveal_·_is_; [_]) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open import Function using (_∘_; flip; Bijective; Injective; Surjective; Bijection; Injection; Surjection; Congruent)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary using (Rel; Decidable; IsEquivalence; tri<; tri≈; tri>)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; _+_; _*_; _/_; _≤_; _≥_; _<_; z≤n; s≤s; s≤s⁻¹) renaming (zero to zero-ℕ; suc to suc-ℕ)
open import Data.Nat.Properties using (≤-reflexive; <-trans; ≤-trans; ≤-<-trans; <-cmp; _<?_)
open import Data.Fin using (Fin; zero; suc; _↑ˡ_; _↑ʳ_; splitAt; join; combine; toℕ; fromℕ<)
open import Data.Fin.Properties using (join-splitAt; splitAt-↑ˡ; splitAt-↑ʳ; combine-injective; combine-surjective; toℕ-fromℕ<; fromℕ<-toℕ; fromℕ<-cong; toℕ<n)

open import Plasmaduck.SetoidExperiment.SetoidMachinery using (discrete-setoid; from-discrete-cong; ⊎-setoid; ×-setoid; maybe-setoid; rel₁; rel₂; property-subset-setoid; SetoidFunction; _which-is-cong_; equality→setoid)
open import Plasmaduck.Function.Bijection using (invert-bijection; _∘-bijection_; ⊎-bijection; ×-bijection; ⊎-discrete-distributivity; ⊎-property-split-bijection; ×-discrete-distributivity; module InverseFunction)
open import Plasmaduck.Function.InjectionSurjection using (bijection→surjection)
open import Plasmaduck.Function.Properties using (Idempotent)
open import Plasmaduck.Relation.Defs using (CongruentRel; CongruentProperty; rel-property)
open import Plasmaduck.Property.Defs using (DecidableProperty)
open import Plasmaduck.Data.Nat using (n<sn; n≤sn; ≤→<≡; s≡s⁻¹; n≤n)
open import Plasmaduck.Util.Case using (case_of_)
open import Plasmaduck.Util.Negation using (¬¬-lift)
open import Plasmaduck.Counting.Counting using (fin-setoid; HasSize; fin-⊎-bijection; IsFinite)
open import Plasmaduck.Counting.Pigeonhole using (pigeonhole-principle-fin)
open import Plasmaduck.Counting.Minimum using (module Minimum; module TransformMinimumTypes)


{-
    This module is for counting results that rely on the pigeonhole principle, but that aren't the pigeonhole principle.
-}

module Plasmaduck.Counting.StrongCounting where

variable
    a ℓ ℓ₁ ℓ₂ : Level

open Setoid using (Carrier)


module _
    {m n : ℕ} (m-n-surjection : Surjection (fin-setoid m) (fin-setoid n))
    where

    private
        to = m-n-surjection .Surjection.to
        inv = proj₁ ∘ m-n-surjection .Surjection.surjective

        open ≡-Reasoning

    surj→¬m<n : ¬ m < n
    surj→¬m<n m<n with pigeonhole-principle-fin m<n inv
    ... | i , j , i≢j , inv-i≡inv-j = i≢j (
        i           ≡⟨ ≡-sym (m-n-surjection .Surjection.surjective i .proj₂ ≡-refl) ⟩
        to (inv i)  ≡⟨ cong to inv-i≡inv-j ⟩
        to (inv j)  ≡⟨ m-n-surjection .Surjection.surjective j .proj₂ ≡-refl ⟩
        j           ∎
        )

bijection-maintains-size : {m n : ℕ} (m-n-bijection : Bijection (fin-setoid m) (fin-setoid n)) → m ≡ n
bijection-maintains-size {m = m} {n} m-n-bijection with <-cmp m n
... | tri< m<n _ _ = ⊥-elim (surj→¬m<n (bijection→surjection m-n-bijection) m<n)
... | tri≈ _ m≡n _ = m≡n
... | tri> _ _ m>n = ⊥-elim (surj→¬m<n (bijection→surjection (invert-bijection m-n-bijection)) m>n)


⊎-property-split-size-theorem :
    {A-setoid : Setoid a ℓ} → (P : A-setoid .Carrier → Set ℓ₁) →
    (P-cong : CongruentProperty A-setoid P)
    (P-dec : DecidableProperty P)
    {m n o : ℕ} →
    HasSize A-setoid m →
    HasSize (property-subset-setoid A-setoid P) n →
    HasSize (property-subset-setoid A-setoid (¬_ ∘ P)) o →
    m ≡ n + o
⊎-property-split-size-theorem {A-setoid = A-setoid} P P-cong P-dec {m} {n} {o} A-size-m A-with-P-size-n A-without-P-size-o = bijection-maintains-size final-bijection
    where
        split-bijection : Bijection A-setoid (⊎-setoid (property-subset-setoid A-setoid P) (property-subset-setoid A-setoid (¬_ ∘ P)))
        split-bijection = ⊎-property-split-bijection A-setoid P P-cong P-dec

        fin-bijection : Bijection (fin-setoid m) (⊎-setoid (fin-setoid n) (fin-setoid o))
        fin-bijection = ⊎-bijection (invert-bijection A-with-P-size-n) (invert-bijection A-without-P-size-o) ∘-bijection split-bijection ∘-bijection A-size-m

        final-bijection : Bijection (fin-setoid m) (fin-setoid (n + o))
        final-bijection = invert-bijection (fin-⊎-bijection n o) ∘-bijection invert-bijection (⊎-discrete-distributivity (Fin n) (Fin o)) ∘-bijection fin-bijection

module _
    (A-setoid : Setoid a ℓ)
    {_~-coarse_ : Rel (A-setoid .Carrier) ℓ₂} (~-eq : IsEquivalence _~-coarse_) (~-cong : CongruentRel A-setoid _~-coarse_) (_~-coarse?_ : Decidable _~-coarse_)
    {n' : ℕ} (size-n : HasSize A-setoid (suc-ℕ n'))
    {m' : ℕ} (each-item-size-m : ∀ (x : A-setoid .Carrier) → HasSize (property-subset-setoid A-setoid (x ~-coarse_)) (suc-ℕ m'))
    where
    private
        n = suc-ℕ n'
        m = suc-ℕ m'

        A = A-setoid .Carrier
        _~-fine_ = A-setoid .Setoid._≈_

        B-setoid : Setoid a ℓ₂
        B-setoid = equality→setoid ~-eq

        to = size-n .Bijection.to

        open IsEquivalence (A-setoid .Setoid.isEquivalence) renaming (refl to f-refl; sym to f-sym; trans to f-trans)
        open IsEquivalence ~-eq using () renaming (refl to c-refl; sym to c-sym; trans to c-trans)
        open InverseFunction size-n using (inv)

        fine→coarse : {x y : A} → x ~-fine y → x ~-coarse y
        fine→coarse x~y = ~-cong f-refl x~y c-refl



    module _ (x : A) where
        related-to-x-index : ℕ → Set ℓ₂
        related-to-x-index i = Σ (i < n) λ i<n → to (fromℕ< i<n) ~-coarse x

        related-to-x-dec : DecidableProperty related-to-x-index
        related-to-x-dec i with i <? n
        ... | no ¬i<n = no (¬i<n ∘ proj₁)
        ... | yes i<n with to (fromℕ< i<n) ~-coarse? x
        ...     | no ¬fi~x = no (¬fi~x ∘ proj₂)
        ...     | yes fi~x = yes (i<n , fi~x)

        reflexive-related : {y : A} → x ~-coarse y → related-to-x-index (toℕ (inv y))
        reflexive-related {y = y} x~y = toℕ<n (inv y) , (begin
            to (fromℕ< {m = toℕ (inv y)} _)   ≈⟨ IsEquivalence.reflexive ~-eq (cong to (fromℕ<-toℕ (inv y) (toℕ<n (inv y)))) ⟩
            to (inv y)                        ≈⟨ fine→coarse (size-n .Bijection.bijective .proj₂ y .proj₂ ≡-refl) ⟩
            y                                                   ≈⟨ c-sym x~y ⟩
            x                                                   ∎
            ) where open import Relation.Binary.Reasoning.Setoid B-setoid

        exists : Σ ℕ related-to-x-index
        exists = toℕ (inv x) , reflexive-related c-refl

        open Minimum related-to-x-index using (module FindMinimum; IsMinimum; minimum-has-value) public
        open FindMinimum related-to-x-dec using (find-minimum; to-minimum-value; to-minimum-value-idempotent; is-minimum-dec) public

        canonize : A
        canonize = to (fromℕ< {m = i} i<n)
            where
                i : ℕ
                i = to-minimum-value exists .proj₁

                i<n : i < n
                i<n = to-minimum-value exists .proj₂ .proj₁

        canonize-related : canonize ~-coarse x
        canonize-related = to-minimum-value exists .proj₂ .proj₂


    coarsely-related-preserves-indices : {x y : A} → x ~-coarse y → {i : ℕ} → related-to-x-index x i → related-to-x-index y i
    coarsely-related-preserves-indices {x = x} {y} x~y (i<n , i~x) = i<n , c-trans i~x x~y

    module _ {x y : A} (x~y : x ~-coarse y) where
        open TransformMinimumTypes
            (related-to-x-index x)
            (related-to-x-index y)
            (coarsely-related-preserves-indices x~y)
            (coarsely-related-preserves-indices (c-sym x~y))
            using () renaming (unique-minimum' to unique-minimum) public

    canonize-makes-fine : {x y : A} → x ~-coarse y → canonize x ~-fine canonize y
    canonize-makes-fine {x = x} {y} x~y = begin
        canonize x                                                                                          ≈⟨ f-refl ⟩
        to (fromℕ< {m = find-minimum x (exists x) .proj₁} (to-minimum-value x (exists x) .proj₂ .proj₁))    ≈⟨ size-n .Bijection.cong (fromℕ<-cong (find-minimum x (exists x) .proj₁) (find-minimum y (exists y) .proj₁) same-minimum (to-minimum-value x (exists x) .proj₂ .proj₁) (to-minimum-value y (exists y) .proj₂ .proj₁)) ⟩
        to (fromℕ< {m = find-minimum y (exists y) .proj₁} (to-minimum-value y (exists y) .proj₂ .proj₁))    ≈⟨ f-refl ⟩
        canonize y                                                                                          ∎
        where
            open import Relation.Binary.Reasoning.Setoid A-setoid

            x-finds-minimum : IsMinimum x (find-minimum x (exists x) .proj₁)
            x-finds-minimum = find-minimum x (exists x) .proj₂

            y-finds-minimum : IsMinimum y (find-minimum y (exists y) .proj₁)
            y-finds-minimum = find-minimum y (exists y) .proj₂

            same-minimum : find-minimum x (exists x) .proj₁ ≡ find-minimum y (exists y) .proj₁
            same-minimum = unique-minimum x~y x-finds-minimum y-finds-minimum

    canonize-cong : Congruent _~-fine_ _~-fine_ canonize
    canonize-cong x~y = canonize-makes-fine (fine→coarse x~y)

    idempotent : Idempotent A-setoid canonize
    idempotent x = canonize-makes-fine (canonize-related x)

    open import Plasmaduck.SetoidExperiment.CanonicalElement A-setoid (canonize which-is-cong canonize-cong) idempotent using (on-bijection)


    -- canonize-preserves-relatedness : (x : A) (i : ℕ) → related-to-x-index x i → related-to-x-index (canonize x) i
    -- canonize-preserves-relatedness x i (i<n , i~x) = i<n , c-trans i~x (c-sym (canonize-related x))

    -- canonize-induces-relatedness : (x : A) (i : ℕ) → related-to-x-index (canonize x) i → related-to-x-index x i
    -- canonize-induces-relatedness x i (i<n , i~canon-x) = i<n , c-trans i~canon-x (canonize-related x)

    {-
        Alternatively:
        We already have the ×-size-theorem where the size of Fin m × Fin n is m * n.
        Maybe we can biject Fin n with Fin m × Fin (n / m)
        and then the idea is that we can biject that with a weird product set of like, a canonical element and an element corresponding to it
            and that bijection is possible because we can biject the canonical elements with Fin (n / m) (how?) and then biject their random associated junk with Fin m
            and then since everything in A has exactly one canonical element, *that* trivially bijects with A.

        so in particular, if there are n canonical elements, and each one is associated with m items, then the original set has size n * m.
        Then all we have to do is flip that around: Note that the set of canonical elements is finite (squeeze via pigeonhole), and each has m associated items, so if the new finite set has size n, then A must have size m * n.
        and thus size A / m = number of canonical elements.
        which as we've shown in CanonicalElement.agda is bijective with the setoid of equality classes.
    -}
    -- lumping-bijection : HasSize (equality→setoid ~-eq) (n / m)
    -- lumping-bijection = record {
    --     to = {!   !};
    --     cong = {!   !};
    --     bijective = {!   !}
    --     }
    --         {-
    --             How do we know this? It's a counting argument, but what is the argument?

    --             There are n items. Each item is equal to m items (including itself).

    --             I mean, I think ideally equality would be decidable.
    --             Then for each item, we can figure out what indices are equal to it, and then pick the minimum index.
    --             This will be our canonical representative for the equality group.
    --         -}


