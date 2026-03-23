open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; inspect; cong; Reveal_·_is_; [_]) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open import Function using (_∘_; flip; Bijective; Injective; Surjective; Bijection; Injection; Surjection)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary using (Rel; Decidable; IsEquivalence)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; _+_; _*_; _≤_; _≥_; _<_; z≤n; s≤s; s≤s⁻¹) renaming (zero to zero-ℕ; suc to suc-ℕ)
open import Data.Nat.Properties using (≤-reflexive; <-trans; ≤-trans; ≤-<-trans)
open import Data.Fin using (Fin; zero; suc; _↑ˡ_; _↑ʳ_; splitAt; join; combine; toℕ; fromℕ<)
open import Data.Fin.Properties using (join-splitAt; splitAt-↑ˡ; splitAt-↑ʳ; combine-injective; combine-surjective; toℕ-fromℕ<; fromℕ<-toℕ; fromℕ<-cong; toℕ<n)

open import Plasmaduck.SetoidExperiment.SetoidMachinery using (discrete-setoid; from-discrete-cong; ⊎-setoid; ×-setoid; maybe-setoid; rel₁; rel₂)
open import Plasmaduck.Function.Bijection using (invert-bijection; _∘-bijection_; ⊎-bijection; ×-bijection; ⊎-discrete-distributivity; ×-discrete-distributivity)
open import Plasmaduck.Relation.Defs using (CongruentRel; CongruentProperty; rel-property)
open import Plasmaduck.Number.Nat using (n<sn; n≤sn; ≤→<≡; s≡s⁻¹; n≤n)
open import Plasmaduck.Util.Case using (case_of_)
open import Plasmaduck.Util.Negation using (¬¬-lift)



module Plasmaduck.Counting.Counting where

variable
    a c d ℓ ℓ₁ ℓ₂ : Level

fin-setoid : (n : ℕ) → Setoid lzero lzero
fin-setoid n = discrete-setoid (Fin n)

HasSize : (setoid : Setoid c ℓ) (n : ℕ) → Set (c ⊔ ℓ)
HasSize setoid n = Bijection (fin-setoid n) setoid

open Setoid using (Carrier; _≈_)

AtLeastSize : (setoid : Setoid c ℓ) (n : ℕ) → Set (c ⊔ ℓ)
AtLeastSize setoid n = Injection (fin-setoid n) setoid

AtMostSize : (setoid : Setoid c ℓ) (n : ℕ) → Set (c ⊔ ℓ)
AtMostSize setoid n = Surjection (fin-setoid n) setoid

IsWeaklyFinite : (setoid : Setoid c ℓ) → Set (c ⊔ ℓ)
IsWeaklyFinite setoid = Σ ℕ λ n → AtMostSize setoid n

IsFinite : (setoid : Setoid c ℓ) → Set (c ⊔ ℓ)
IsFinite setoid = Σ ℕ λ n → HasSize setoid n


module _
    {A-setoid : Setoid a ℓ}
    (A-finite : IsFinite A-setoid)
    (P : A-setoid .Carrier → Set ℓ₂)
    (P-cong : CongruentProperty A-setoid P)
    (dec-P : ∀ x → Dec (P x))
    where

    private
        A = A-setoid .Carrier
        _~_ = A-setoid .Setoid._≈_
        n = A-finite .proj₁

        open IsEquivalence (A-setoid .Setoid.isEquivalence) using (refl; reflexive; sym; trans)

        A-size-n : Bijection (fin-setoid n) A-setoid
        A-size-n = A-finite .proj₂

        to : Fin n → A
        to = A-size-n .Bijection.to

        inv : A → Fin n
        inv = proj₁ ∘ A-size-n .Bijection.bijective .proj₂

    any-type : Set (a ⊔ ℓ₂)
    any-type = Σ A λ x → P x

    any : Dec any-type
    any = sol
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
            ... | no pf = no λ { (y , P[y]) → pf (inv y , P-cong (sym (A-finite .proj₂ .Bijection.bijective .proj₂ y .proj₂ ≡-refl)) P[y]) }

module _
    {A-setoid : Setoid a ℓ}
    (A-finite : IsFinite A-setoid)
    (P : A-setoid .Carrier → Set ℓ₂)
    (P-cong : CongruentProperty A-setoid P)
    (dec-P : ∀ x → Dec (P x))
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

        dec-Q : ∀ x → Dec (Q x)
        dec-Q x with dec-P x
        ... | yes P[x] = no (¬¬-lift P[x])
        ... | no ¬P[x] = yes ¬P[x]

    all-type : Set (a ⊔ ℓ₂)
    all-type = ∀ x → P x

    all : Dec all-type
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

        any-related-to-dec : (x : A) → Dec (any-related-to x)
        any-related-to-dec x = any A-finite (x #_) (rel-property A-setoid #-cong x) (x #?_)

        all-related-to-dec : (x : A) → Dec (all-related-to x)
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

        any-related-to'-dec : (x : A) → Dec (any-related-to' x)
        any-related-to'-dec x = any-related-to-dec A-finite #'-cong _#'?_ x

        all-related-to'-dec : (x : A) → Dec (all-related-to' x)
        all-related-to'-dec x = all-related-to-dec A-finite #'-cong _#'?_ x

        any-related-dec : Dec any-related
        any-related-dec = any A-finite (any-related-to A-finite #-cong) (λ x≈y (z , x#z) → z , #-cong x≈y refl x#z) (any-related-to-dec A-finite #-cong _#?_)

        all-related-dec : Dec all-related
        all-related-dec = all A-finite (all-related-to A-finite #-cong) (λ x≈y all-x-proof → λ z → #-cong x≈y refl (all-x-proof z)) (all-related-to-dec A-finite #-cong _#?_)



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
