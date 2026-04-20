open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; inspect; cong; Reveal_·_is_; [_]; refl; sym; trans)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open import Data.Nat using (ℕ; _+_; _∸_; _≤_; _≥_; _<_; s≤s⁻¹) renaming (zero to zero-ℕ; suc to suc-ℕ)
open import Data.Nat.Properties using (+-comm; <-≤-trans; ≤-<-trans; ≤-trans; ∸-monoˡ-<; ≤-reflexive; m+n∸m≡n; +-mono-≤)
open import Data.Fin using (Fin; zero; suc; _↑ˡ_; _↑ʳ_; splitAt; fromℕ<; join; toℕ) renaming (_<_ to _<-fin_)
open import Data.Fin.Properties using (splitAt⁻¹-↑ʳ; toℕ<n; fromℕ<-toℕ; splitAt-↑ˡ; splitAt-↑ʳ; join-splitAt; toℕ-↑ˡ; toℕ-↑ʳ)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary using (Decidable)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Function using (_∘_)

open import Plasmaduck.Util.Case using (case_of_)
open import Plasmaduck.Util.TypeChange using (change-type)


module Plasmaduck.Data.Fin where

suc-inj : {n : ℕ} → {x y : Fin n} → suc x ≡ suc y → x ≡ y
suc-inj {n} {x} {y} refl = refl

fin-≡-dec : {n : ℕ} → Decidable (_≡_ {A = Fin n})
fin-≡-dec {zero-ℕ} ()
fin-≡-dec {suc-ℕ n} zero zero = yes refl
fin-≡-dec {suc-ℕ n} zero (suc _) = no λ ()
fin-≡-dec {suc-ℕ n} (suc _) zero = no λ ()
fin-≡-dec {suc-ℕ n} (suc p) (suc q) = case (fin-≡-dec p q) of λ {
    (yes p≡q) → yes (cong suc p≡q);
    (no p≢q) → no λ sp≡sq → p≢q (suc-inj sp≡sq)
    }

_∸-fin_ : (n : ℕ) → (m : Fin n) → ℕ
zero-ℕ ∸-fin ()
(suc-ℕ n) ∸-fin zero = suc-ℕ n
(suc-ℕ n) ∸-fin (suc m) = n ∸-fin m

-- Left addition
_↑ˡ-inverted_ : {m : ℕ} → Fin m → (n : ℕ) → Fin (n + m)
_↑ˡ-inverted_ {m = m} i n = change-type (cong Fin (+-comm m n)) (i ↑ˡ n)

splitAt-≥ : {m n : ℕ} → (i : Fin (m + n)) → (m≤i : m ≤ toℕ i) → splitAt m i ≡ inj₂ (fromℕ< {m = (toℕ i) ∸ m} (<-≤-trans (∸-monoˡ-< {m = toℕ i} {n = m} {o = m + n} (toℕ<n i) m≤i) (≤-reflexive (m+n∸m≡n m n))))
splitAt-≥ {m = zero-ℕ} {n} zero m≤i = refl
splitAt-≥ {m = suc-ℕ m'} {n} zero ()
splitAt-≥ {m = zero-ℕ} {n = suc-ℕ n'} (suc i') m≤i = cong (inj₂ ∘ suc) (sym (fromℕ<-toℕ i' (toℕ<n i')))
splitAt-≥ {m = suc-ℕ m'} {n} (suc i') m≤i = cong (Data.Sum.map₁ suc) (splitAt-≥ i' (s≤s⁻¹ m≤i))

fromℕ<-cong₂ : (m n o p : ℕ) → m ≡ n → (o≡p : o ≡ p) → .(m<o : m < o) → .(n<p : n < p) → change-type (cong Fin o≡p) (fromℕ< {m = m} {n = o} m<o) ≡ fromℕ< {m = n} {n = p} n<p
fromℕ<-cong₂ m n o p refl refl m<o n<p = refl

join₁-toℕ : (m n : ℕ) → (i : Fin m) → toℕ (join m n (inj₁ i)) ≡ toℕ i
join₁-toℕ m n i =
    toℕ (join m n (inj₁ i))             ≡⟨ cong (λ q → toℕ (join m n q)) (sym (splitAt-↑ˡ m i n)) ⟩
    toℕ (join m n (splitAt m (i ↑ˡ n))) ≡⟨ cong toℕ (join-splitAt m n (i ↑ˡ n)) ⟩
    toℕ (i ↑ˡ n)                        ≡⟨ toℕ-↑ˡ i n ⟩
    toℕ i                               ∎
    where
        open ≡-Reasoning

join₂-toℕ : (m n : ℕ) → (i : Fin n) → toℕ (join m n (inj₂ i)) ≡ m + toℕ i
join₂-toℕ m n i =
    toℕ (join m n (inj₂ i))             ≡⟨ cong (λ q → toℕ (join m n q)) (sym (splitAt-↑ʳ m n i)) ⟩
    toℕ (join m n (splitAt m (m ↑ʳ i))) ≡⟨ cong toℕ (join-splitAt m n (m ↑ʳ i)) ⟩
    toℕ (m ↑ʳ i)                        ≡⟨ toℕ-↑ʳ m i ⟩
    m + toℕ i                           ∎
    where
        open ≡-Reasoning

join₁-< : (m n : ℕ) → (i : Fin m) → toℕ (join m n (inj₁ i)) < m
join₁-< m n i = ≤-<-trans (≤-reflexive (toℕ-↑ˡ i n)) (toℕ<n i)

join₂-≥ : (m n : ℕ) → (i : Fin n) → toℕ (join m n (inj₂ i)) ≥ m
join₂-≥ m n i = ≤-trans (≤-trans (≤-reflexive (+-comm 0 m)) (+-mono-≤ {m} {m} {0} {toℕ i} (≤-reflexive refl) _≤_.z≤n)) (≤-reflexive (sym (join₂-toℕ m n i)))
