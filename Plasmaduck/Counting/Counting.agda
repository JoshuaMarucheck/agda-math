open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; inspect; cong; Reveal_·_is_; [_]) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open import Function using (_∘_; flip; Bijective; Injective; Surjective; Bijection; Injection; Surjection; Congruent)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary using (Rel; Decidable; IsEquivalence)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; _+_; _*_; _∸_; _≤_; _≥_; _<_; z≤n; s≤s; s≤s⁻¹) renaming (zero to zero-ℕ; suc to suc-ℕ)
open import Data.Nat.Properties using (≤-reflexive; <-trans; ≤-trans; ≤-<-trans; _<?_; m+[n∸m]≡n)
open import Data.Fin using (Fin; zero; suc; _↑ˡ_; _↑ʳ_; splitAt; join; combine; toℕ; fromℕ<)
open import Data.Fin.Properties using (join-splitAt; splitAt-↑ˡ; splitAt-↑ʳ; toℕ-↑ˡ; combine-injective; combine-surjective; toℕ-fromℕ<; fromℕ<-toℕ; fromℕ<-cong; toℕ<n)

open import Plasmaduck.SetoidExperiment.SetoidMachinery using (discrete-setoid; from-discrete-cong; ⊎-setoid; ×-setoid; maybe-setoid; rel₁; rel₂; property-subset-setoid)
open import Plasmaduck.Function.Bijection using (invert-bijection; _∘-bijection_; ⊎-bijection; ×-bijection; ⊎-discrete-distributivity; ×-discrete-distributivity)
open import Plasmaduck.Function.InjectionSurjection using (bijection→surjection; _∘-surjection_)
open import Plasmaduck.Relation.Defs using (CongruentRel; CongruentProperty; rel-property)
open import Plasmaduck.Property.Defs using (DecidableProperty; any-type; all-type)
open import Plasmaduck.Number.Nat using (n<sn; n≤sn; ≤→<≡; s≡s⁻¹; n≤n)
open import Plasmaduck.Util.Case using (case_of_)
open import Plasmaduck.Util.Negation using (¬¬-lift)
open import Plasmaduck.Util.TypeChange using (change-type; change-type-input-dependence-irrelevance)
open import Plasmaduck.Function.Surjectionish using (Surjectionish; _∘-surjectionish_)



module Plasmaduck.Counting.Counting where

variable
    a b c d ℓ ℓ₁ ℓ₂ : Level

fin-setoid : (n : ℕ) → Setoid lzero lzero
fin-setoid n = discrete-setoid (Fin n)

HasSize : (setoid : Setoid c ℓ) (n : ℕ) → Set (c ⊔ ℓ)
HasSize setoid n = Bijection (fin-setoid n) setoid

open Setoid using (Carrier; _≈_)

AtLeastSize : (setoid : Setoid c ℓ) (n : ℕ) → Set (c ⊔ ℓ)
AtLeastSize setoid n = Injection (fin-setoid n) setoid

-- Defined like this since if the target set is empty, no surjection exists since no functions exist. oops.
-- Of course, such a definition means the target set is decidable.
AtMostSize : (setoid : Setoid c ℓ) (n : ℕ) → Set (c ⊔ ℓ)
AtMostSize setoid n = Surjectionish (fin-setoid n) setoid

-- Or maybe this definition would be easier to use
-- Certainly, it's easier to restrict.
-- But this version is not enumerable, not necessarily.
-- Classic example: A datatype with one constructor, taking a proof of Axiom of Choice.
--   The setoid over that set with all equal then injects into Fin 1,
--   but it has no concrete size, so does not biject with Fin anything.
AtMostSize' : (setoid : Setoid c ℓ) (n : ℕ) → Set (c ⊔ ℓ)
AtMostSize' setoid n = Injection setoid (fin-setoid n)

IsWeaklyFinite : (setoid : Setoid c ℓ) → Set (c ⊔ ℓ)
IsWeaklyFinite setoid = Σ ℕ λ n → AtMostSize setoid n

IsWeaklyFinite' : (setoid : Setoid c ℓ) → Set (c ⊔ ℓ)
IsWeaklyFinite' setoid = Σ ℕ λ n → AtMostSize' setoid n

IsFinite : (setoid : Setoid c ℓ) → Set (c ⊔ ℓ)
IsFinite setoid = Σ ℕ λ n → HasSize setoid n


-- This property makes me question my definition of AtMostSize.
-- Ideally, we could have a property setoid with some undecidable property (like the axiom of choice or double-negation inversion or something).
-- Then the setoid would have one element in universes where it is true, and zero elements in universes where it is false.
--   (Both universes are extensions of base Agda, so of course we cannot prove one or the other.)
-- I'd still like to be able to say that such a setoid has at most one element in it, since in all universes it has at most one element.
at-most-size-implies-decidable : {setoid : Setoid c ℓ} {n : ℕ} → AtMostSize setoid n → Dec (setoid .Carrier)
at-most-size-implies-decidable (inj₂ ¬S) = no ¬S
at-most-size-implies-decidable {n = zero-ℕ} (inj₁ surj) = no λ x → case surj .Surjection.surjective x of λ { (() , _) }
at-most-size-implies-decidable {n = suc-ℕ _} (inj₁ surj) = yes (surj .Surjection.to zero)


module _
    {A-setoid : Setoid a ℓ}
    {n : ℕ}
    (A-bounded : Surjection (fin-setoid n) A-setoid)
    (P : A-setoid .Carrier → Set ℓ₂)
    (P-cong : CongruentProperty A-setoid P)
    (dec-P : DecidableProperty P)
    where

    private
        A = A-setoid .Carrier
        _~_ = A-setoid .Setoid._≈_

        open IsEquivalence (A-setoid .Setoid.isEquivalence) using (refl; reflexive; sym; trans)

        to : Fin n → A
        to = A-bounded .Surjection.to

        inv : A → Fin n
        inv = proj₁ ∘ A-bounded .Surjection.surjective

    any-via-surjection : Dec (any-type P)
    any-via-surjection = sol
        where
            hunt : (j : ℕ) .(j≤n : j ≤ n) → Dec (Σ (Fin n) λ i → toℕ i < j × P (to i))
            hunt zero-ℕ _ = no λ { (_ , () , _) }
            hunt j@(suc-ℕ j') j'<n           with dec-P (to (fromℕ< {m = j'} j'<n))
            ...                             | yes P[j] =  yes (fromℕ< {m = j'} j'<n , ≤-reflexive (toℕ-fromℕ< (s≤s j'<n)) , P[j])
            hunt (suc-ℕ zero-ℕ) z<n         | no ¬P[j] = no λ { (zero , s≤s z≤n , P[j]) → ¬P[j] P[j] }
            hunt j@(suc-ℕ j'@(suc-ℕ _)) j'<n | no ¬P[j] with hunt j' (<-trans n<sn j'<n)
            ...                                     | yes (k , k≤j' , P[k]) = yes (k , ≤-trans k≤j' n≤sn , P[k])
            ...                                     | no pf = no λ { (k , k≤j , P[k]) → case ≤→<≡ k≤j of λ {
                (inj₁ k<j) → pf (k , s≤s⁻¹ k<j , P[k]);
                (inj₂ k≡j) → ¬P[j] (P-cong (reflexive (cong to (≡-trans (≡-sym (fromℕ<-toℕ k (≤-<-trans (s≤s⁻¹ k≤j) j'<n))) (fromℕ<-cong (toℕ k) j' (s≡s⁻¹ k≡j) (≤-<-trans (s≤s⁻¹ k≤j) j'<n) j'<n)))) P[k])
                } }

            pre-sol : Dec (Σ (Fin n) λ i → P (to i))
            pre-sol with hunt n n≤n
            ... | yes (i , _ , P[i]) = yes (i , P[i])
            ... | no pf = no λ { (i , P[i]) → pf (i , toℕ<n i , P[i]) }

            sol : Dec (Σ A λ x → P x)
            sol with pre-sol
            ... | yes (i , P[i]) = yes (to i , P[i])
            ... | no pf = no λ { (y , P[y]) → pf (inv y , P-cong (sym (A-bounded .Surjection.surjective y .proj₂ ≡-refl)) P[y]) }

any' :
    {A-setoid : Setoid a ℓ}
    {n : ℕ} (A-bounded : AtMostSize A-setoid n) →
    (P : A-setoid .Carrier → Set ℓ₂) →
    (P-cong : CongruentProperty A-setoid P) →
    (dec-P : DecidableProperty P) →
    Dec (any-type P)
any' (inj₁ surj) P P-cong dec-P = any-via-surjection surj P P-cong dec-P
any' (inj₂ ¬A) P P-cong dec-P = no (¬A ∘ proj₁)

any :
    {A-setoid : Setoid a ℓ}
    (A-finite : IsFinite A-setoid) →
    (P : A-setoid .Carrier → Set ℓ₂) →
    (P-cong : CongruentProperty A-setoid P) →
    (dec-P : DecidableProperty P) →
    Dec (any-type P)
any A-finite P P-cong dec-P = any-via-surjection (bijection→surjection (A-finite .proj₂)) P P-cong dec-P

module _
    {A-setoid : Setoid a ℓ}
    (A-finite : IsFinite A-setoid)
    (P : A-setoid .Carrier → Set ℓ₂)
    (P-cong : CongruentProperty A-setoid P)
    (dec-P : DecidableProperty P)
    where

    private
        A = A-setoid .Carrier
        _~_ = A-setoid .Setoid._≈_
        n = A-finite .proj₁

        open IsEquivalence (A-setoid .Setoid.isEquivalence) using (refl; sym; trans)

        -- negation of P
        Q : A → Set ℓ₂
        Q = ¬_ ∘ P

        Q-cong : CongruentProperty A-setoid Q
        Q-cong x≈y ¬P[x] P[y] = ¬P[x] (P-cong (sym x≈y) P[y])

        dec-Q : DecidableProperty Q
        dec-Q x with dec-P x
        ... | yes P[x] = no (¬¬-lift P[x])
        ... | no ¬P[x] = yes ¬P[x]

    all : Dec (all-type P)
    all with any A-finite Q Q-cong dec-Q
    ... | yes (x , ¬P[x]) = no λ all-proof → ¬P[x] (all-proof x)
    ... | no ¬¬P-proof = yes λ x → case dec-P x of λ {
        (yes P[x]) → P[x];
        (no ¬P[x]) → ⊥-elim (¬¬P-proof (x , ¬P[x]))
        }

module _
    {A-setoid : Setoid a ℓ}
    (A-finite : IsFinite A-setoid)
    {_#_ : Rel (A-setoid .Carrier) ℓ₂}
    (#-cong : CongruentRel A-setoid _#_)
    where

    private
        A = A-setoid .Carrier

    any-related-to : (x : A) → Set (a ⊔ ℓ₂)
    any-related-to x = Σ A (x #_)

    all-related-to : (x : A) → Set (a ⊔ ℓ₂)
    all-related-to x = ∀ y → x # y

    module _
        (_#?_ : Decidable _#_)
        where

        any-related-to-dec : DecidableProperty any-related-to
        any-related-to-dec x = any A-finite (x #_) (rel-property A-setoid #-cong x) (x #?_)

        all-related-to-dec : DecidableProperty all-related-to
        all-related-to-dec x = all A-finite (x #_) (rel-property A-setoid #-cong x) (x #?_)

module _
    {A-setoid : Setoid a ℓ}
    (A-finite : IsFinite A-setoid)
    {_#_ : Rel (A-setoid .Carrier) ℓ₂}
    (#-cong : CongruentRel A-setoid _#_)
    where

    private
        A = A-setoid .Carrier
        _~_ = A-setoid .Setoid._≈_
        n = A-finite .proj₁

    any-related-to' : (x : A) → Set (a ⊔ ℓ₂)
    any-related-to' x = Σ A λ y → y # x

    all-related-to' : (x : A) → Set (a ⊔ ℓ₂)
    all-related-to' x = ∀ y → y # x

    any-related : Set (a ⊔ ℓ₂)
    any-related = Σ A λ x → Σ A λ y → x # y

    all-related : Set (a ⊔ ℓ₂)
    all-related = ∀ (x y : A) → x # y

    module _
        (_#?_ : Decidable _#_)
        where
        private
            open IsEquivalence (A-setoid .Setoid.isEquivalence) using (refl; sym; trans)

            _#'_ : Rel A ℓ₂
            _#'_ = flip _#_

            #'-cong : CongruentRel A-setoid _#'_
            #'-cong = flip #-cong

            _#'?_ : Decidable _#'_
            _#'?_ = flip _#?_

        any-related-to'-dec : DecidableProperty any-related-to'
        any-related-to'-dec x = any-related-to-dec A-finite #'-cong _#'?_ x

        all-related-to'-dec : DecidableProperty all-related-to'
        all-related-to'-dec x = all-related-to-dec A-finite #'-cong _#'?_ x

        any-related-dec : Dec any-related
        any-related-dec = any A-finite (any-related-to A-finite #-cong) (λ x≈y (z , x#z) → z , #-cong x≈y refl x#z) (any-related-to-dec A-finite #-cong _#?_)

        all-related-dec : Dec all-related
        all-related-dec = all A-finite (all-related-to A-finite #-cong) (λ x≈y all-x-proof → λ z → #-cong x≈y refl (all-x-proof z)) (all-related-to-dec A-finite #-cong _#?_)



≤-bound : {m n : ℕ} → (m ≤ n) → AtMostSize (fin-setoid m) n
≤-bound {zero-ℕ} {_} m≤n = inj₂ λ ()
≤-bound {m@(suc-ℕ m')} {n@(suc-ℕ n')} m≤n = inj₁ record {
    to = to;
    cong = from-discrete-cong (fin-setoid m) to;
    surjective = to-surj
    }
    where
        open ≡-Reasoning

        to : Fin n → Fin m
        to x with toℕ x <? m
        ... | yes x<m = fromℕ< {m = toℕ x} x<m
        ... | no ¬x<m = zero

        inv : Fin m → Fin n
        inv y = change-type (cong Fin (m+[n∸m]≡n m≤n)) (y ↑ˡ (n ∸ m))

        inv-y≈y : ∀ (y : Fin m) → toℕ (inv y) ≡ toℕ y
        inv-y≈y y =
            toℕ (change-type (cong Fin (m+[n∸m]≡n m≤n)) (y ↑ˡ (n ∸ m)))     ≡⟨ change-type-input-dependence-irrelevance Fin toℕ (m+[n∸m]≡n m≤n) (y ↑ˡ (n ∸ m)) ⟩
            toℕ (y ↑ˡ (n ∸ m))                                              ≡⟨ toℕ-↑ˡ y (n ∸ m) ⟩
            toℕ y                                                           ∎

        is-right-inv : ∀ (y : Fin m) → to (inv y) ≡ y
        is-right-inv y with toℕ (inv y) <? m
        ... | yes y<m =
            fromℕ< {m = toℕ (inv y)} y<m  ≡⟨ fromℕ<-cong (toℕ (inv y)) (toℕ y) (inv-y≈y y) y<m (toℕ<n y) ⟩
            fromℕ< {m = toℕ y} (toℕ<n y)  ≡⟨ fromℕ<-toℕ y (toℕ<n y) ⟩
            y                             ∎
        ... | no ¬y<m = ⊥-elim (¬y<m (change-type (cong (_< m) (≡-sym (inv-y≈y y))) (toℕ<n y)))

        to-surj : Surjective _≡_ _≡_ to
        to-surj y = inv y , λ { ≡-refl → is-right-inv y }

raise-at-most : (s : Setoid c ℓ) → {m n : ℕ} → AtMostSize s m → m ≤ n → AtMostSize s n
raise-at-most s {m} {n} s-size-m m≤n = s-size-m ∘-surjectionish (≤-bound m≤n)

has-size→at-most : (s : Setoid c ℓ) → {n : ℕ} → HasSize s n → AtMostSize s n
has-size→at-most s {n = n} s-size-n = inj₁ (bijection→surjection s-size-n)

has-size→at-most-raise : (s : Setoid c ℓ) → {m n : ℕ} → HasSize s m → m ≤ n → AtMostSize s n
has-size→at-most-raise s s-size-m m≤n = raise-at-most s (has-size→at-most s s-size-m) m≤n

finite-is-weakly-finite : (s : Setoid c ℓ) → IsFinite s → IsWeaklyFinite s
finite-is-weakly-finite s (n , n-bij-s) = n , inj₁ (bijection→surjection n-bij-s)

infixr 9 _∘-at-most-size_
_∘-at-most-size_ : {A-setoid : Setoid a ℓ₁} {B-setoid : Setoid b ℓ₂} {n : ℕ} → Surjectionish A-setoid B-setoid → AtMostSize A-setoid n → AtMostSize B-setoid n
_∘-at-most-size_ = _∘-surjectionish_

subset-of-finite-is-upper-bounded :
    {s : Setoid c ℓ} →
    {P : s .Carrier → Set ℓ₁} → CongruentProperty s P → DecidableProperty P →
    {n : ℕ} → HasSize s n →
    AtMostSize (property-subset-setoid s P) n
subset-of-finite-is-upper-bounded {s = s} {P} P-cong dec-P {zero-ℕ} s-size-n = inj₂ λ (x , _) → case invert-bijection s-size-n .Bijection.to x of λ ()
subset-of-finite-is-upper-bounded {s = s} {P} P-cong dec-P {n@(suc-ℕ n')} s-size-n with any-P
    where
        s-finite : IsFinite s
        s-finite = n , s-size-n

        any-P : Dec (any-type P)
        any-P = any s-finite P P-cong dec-P

... | no pf = inj₂ pf
... | yes (x , P[x]) =
    inj₁ record {
    to = to;
    cong = to-cong;
    surjective = to-surjective
    }
    where
        old-to = s-size-n .Bijection.to
        A-setoid = property-subset-setoid s P
        A = A-setoid .Carrier
        _~_ = A-setoid .Setoid._≈_

        -- So it turns out that _~_ reduces to equivalence in setoid s.
        -- This wouldn't normally matter, but _~_ has to keep track of all of the
        -- proofs of inclusion that don't matter but are part of the elements of A-setoid.
        -- It then complains about hidden variables.
        -- Thus, using equality in s directly is easier to reason about.
        open IsEquivalence (s .Setoid.isEquivalence) renaming (reflexive to ~-reflexive; refl to ~-refl; sym to ~-sym; trans to ~-trans)
        open import Relation.Binary.Reasoning.Setoid A-setoid

        to : Fin n → A
        to i with dec-P (old-to i)
        ... | yes P[to-i] = old-to i , P[to-i]
        ... | no ¬P[to-i] = x , P[x]

        to-cong : Congruent _≡_ _~_ to
        to-cong {x = i} {y = .i} ≡-refl with dec-P (old-to i)
        ... | yes P[to-i] = ~-refl
        ... | no ¬P[to-i] = ~-refl

        to-surjective : Surjective _≡_ _~_ to
        to-surjective (y , P[y]) with s-size-n .Bijection.bijective .proj₂ y
        ... | (i , refl→to-i~y) with dec-P (old-to i) | inspect (proj₁ ∘ to) i
        ...     | no ¬P[to-i] | _ = ⊥-elim (¬P[to-i] (P-cong (~-sym (refl→to-i~y ≡-refl)) P[y]))
        ...     | yes P[to-i] | [ proj₁-to-i≡old-to-i ]
            = i , λ { {.i} ≡-refl → begin
                to i                    ≈⟨ ~-reflexive proj₁-to-i≡old-to-i ⟩
                (old-to i , P[to-i])    ≈⟨ refl→to-i~y ≡-refl ⟩
                (y , P[y])              ∎
                }

module _ (A-setoid : Setoid a ℓ) where
    private
        A = A-setoid .Carrier
        _~_ = A-setoid ._≈_
        open IsEquivalence (A-setoid .Setoid.isEquivalence) using (refl; sym; trans)

    one-equal-item : (x : A) → HasSize (property-subset-setoid A-setoid (x ~_)) 1
    one-equal-item x = record {
        to = to;
        cong = from-discrete-cong B-setoid to;
        bijective = (λ { {zero} {zero} _ → ≡-refl }) , λ (z , x~z) → zero , λ { ≡-refl → x~z }
        }
        where
            B-setoid = property-subset-setoid A-setoid (x ~_)
            B = B-setoid .Carrier
            to : Fin 1 → B
            to _ = (x , refl)

fin-⊎-bijection : (m n : ℕ) → Bijection (discrete-setoid (Fin (m + n))) (discrete-setoid (Fin m ⊎ Fin n))
fin-⊎-bijection m n = record {
    to = splitAt m {n};
    cong = from-discrete-cong (discrete-setoid (Fin m ⊎ Fin n)) (splitAt m);
    bijective = record {
        fst = λ {i} {j} to-i≈to-j →
            i                       ≡⟨ ≡-sym (join-splitAt m n i) ⟩
            join m n (splitAt m i)  ≡⟨ cong (join m n) to-i≈to-j ⟩
            join m n (splitAt m j)  ≡⟨ join-splitAt m n j ⟩
            j                       ∎;
        snd = surjective
        }
    }
    where
        open ≡-Reasoning

        surjective : Surjective (_≡_ {A = Fin (m + n)}) (_≡_ {A = Fin m ⊎ Fin n}) (splitAt m)
        surjective (inj₁ x) = x ↑ˡ n , λ {z} z≡x↑n →
            splitAt m z         ≡⟨ cong (splitAt m) z≡x↑n ⟩
            splitAt m (x ↑ˡ n)  ≡⟨ splitAt-↑ˡ m x n ⟩
            inj₁ x              ∎
        surjective (inj₂ y) = m ↑ʳ y , λ {z} z≡m↑y →
            splitAt m z         ≡⟨ cong (splitAt m) z≡m↑y ⟩
            splitAt m (m ↑ʳ y)  ≡⟨ splitAt-↑ʳ m n y ⟩
            inj₂ y              ∎

⊎-size-theorem :
    {s₁ : Setoid c ℓ₁} {m : ℕ} → (HasSize s₁ m) →
    {s₂ : Setoid d ℓ₂} {n : ℕ} → (HasSize s₂ n) →
    HasSize (⊎-setoid s₁ s₂) (m + n)
⊎-size-theorem {m = m} fin-m↔s₁ {n = n} fin-n↔s₂ =
    (⊎-bijection fin-m↔s₁ fin-n↔s₂)
        ∘-bijection
    (⊎-discrete-distributivity (Fin m) (Fin n))
        ∘-bijection
    (fin-⊎-bijection m n)


fin-×-bijection' : (m n : ℕ) → Bijection (discrete-setoid (Fin m × Fin n)) (discrete-setoid (Fin (m * n)))
fin-×-bijection' m n = record {
    to = f ;
    cong = from-discrete-cong (discrete-setoid (Fin (m * n))) f;
    bijective = injective , surjective
    }
    where
        f : Fin m × Fin n → Fin (m * n)
        f (x , y) = combine x y

        injective : Injective _≡_ _≡_ f
        injective {x₁ , y₁} {x₂ , y₂} c₁≡c₂ with combine-injective x₁ y₁ x₂ y₂ c₁≡c₂
        ...                                    | ≡-refl , ≡-refl = ≡-refl

        surjective : Surjective _≡_ _≡_ f
        surjective i with combine-surjective {m = m} {n = n} i
        ...             | j , k , combine-jk≡i = (j , k) , λ { {z} ≡-refl → combine-jk≡i}

fin-×-bijection : (m n : ℕ) → Bijection (discrete-setoid (Fin (m * n))) (discrete-setoid (Fin m × Fin n))
fin-×-bijection m n = invert-bijection (fin-×-bijection' m n)

×-size-theorem :
    {s₁ : Setoid c ℓ₁} {m : ℕ} → (HasSize s₁ m) →
    {s₂ : Setoid d ℓ₂} {n : ℕ} → (HasSize s₂ n) →
    HasSize (×-setoid s₁ s₂) (m * n)
×-size-theorem {m = m} fin-m↔s₁ {n = n} fin-n↔s₂ =
    (×-bijection fin-m↔s₁ fin-n↔s₂)
        ∘-bijection
    (×-discrete-distributivity (Fin m) (Fin n))
        ∘-bijection
    (fin-×-bijection m n)


maybe-bijection-lemma : (m : ℕ) → Bijection (discrete-setoid (Maybe (Fin m))) (discrete-setoid (Fin (suc-ℕ m)))
maybe-bijection-lemma m = record {
    to = f;
    cong = from-discrete-cong (discrete-setoid (Fin (suc-ℕ m))) f;
    bijective = injective , surjective
    }
    where
        f : Maybe (Fin m) → Fin (suc-ℕ m)
        f nothing = zero
        f (just x) = suc x

        injective : Injective _≡_ _≡_ f
        injective {nothing} {nothing} _ = ≡-refl
        injective {just x} {just y} ≡-refl = ≡-refl

        surjective : Surjective _≡_ _≡_ f
        surjective zero = nothing , λ { ≡-refl → ≡-refl }
        surjective (suc x) = just x , λ { ≡-refl → ≡-refl }

-- maybe-size-theorem :
--     {s : Setoid c ℓ₁} {m : ℕ} → (HasSize s m) →
--     HasSize (maybe-setoid s) (suc-ℕ m)
-- maybe-size-theorem fin-m↔s = {!   !}

record InfiniteSize (setoid : Setoid c ℓ) : Set (c ⊔ ℓ) where
    field
        infinite : Injection (discrete-setoid ℕ) setoid
