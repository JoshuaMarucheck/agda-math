open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; inspect; cong; Reveal_·_is_; [_]) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open import Function using (Bijective; Injective; Surjective; Bijection; Injection; Surjection)
open import Relation.Binary.Bundles using (Setoid)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (ℕ; _+_; _*_; _≤_; _≥_; _<_) renaming (zero to zero-ℕ; suc to suc-ℕ)
open import Data.Fin using (Fin; zero; suc; _↑ˡ_; _↑ʳ_; splitAt; join; combine)
open import Data.Fin.Properties using (join-splitAt; splitAt-↑ˡ; splitAt-↑ʳ; combine-injective; combine-surjective)

open import Plasmaduck.SetoidExperiment.SetoidMachinery using (discrete-setoid; from-discrete-cong; ⊎-setoid; ×-setoid; maybe-setoid; rel₁; rel₂)
open import Plasmaduck.Function.Bijection using (invert-bijection; _∘-bijection_; ⊎-bijection; ×-bijection; ⊎-discrete-distributivity; ×-discrete-distributivity)



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
