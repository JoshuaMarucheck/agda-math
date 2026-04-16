open import Level using (Level)
open import Relation.Binary.PropositionalEquality using (_≢_; _≡_; inspect; cong; Reveal_·_is_; [_]) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open import Relation.Binary using (tri<; tri≈; tri>)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Data.Nat using (ℕ; _+_; _*_; _≤_; _≥_; _<_; _∸_; <-cmp; _<?_; s≤s; z≤n; s≤s⁻¹; zero; suc; pred)
open import Data.Nat.Properties using (<-irrefl; <-≤-trans; ≤-trans; ≤-reflexive; +-comm; +-suc; _≟_; m∸n+n≡m)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)

open import Plasmaduck.Util.TypeChange using (change-type)


module Plasmaduck.Number.Nat where


variable
    m n o : ℕ
    ℓ : Level

n≤n : n ≤ n
n≤n {n = zero} = z≤n
n≤n {n = suc n'} = s≤s n≤n

n<sn : n < suc n
n<sn = n≤n

n≤sn : n ≤ suc n
n≤sn {n = zero} = z≤n
n≤sn {n = suc n'} = s≤s n≤sn

<→≤ : m < n → m ≤ n
<→≤ (s≤s m-1<n-1) = ≤-trans m-1<n-1 n≤sn

≤→<≡ : m ≤ n → m < n ⊎ m ≡ n
≤→<≡ {m = m} {n = n} m≤n with <-cmp m n
... | tri< m<n _ _ = inj₁ m<n
... | tri≈ _ m≡n _ = inj₂ m≡n
... | tri> _ _ m>n = ⊥-elim (<-irrefl ≡-refl (<-≤-trans m>n m≤n))

<≡→≤ : m < n ⊎ m ≡ n → m ≤ n
<≡→≤ (inj₁ m<n) = <→≤ m<n
<≡→≤ (inj₂ m≡n) = ≤-reflexive m≡n

s≡s⁻¹ : suc m ≡ suc n → m ≡ n
s≡s⁻¹ ≡-refl = ≡-refl

m∸n∸o≡m∸[n+o] : (m n o : ℕ) → m ∸ n ∸ o ≡ m ∸ (n + o)
m∸n∸o≡m∸[n+o] _ zero _ = ≡-refl
m∸n∸o≡m∸[n+o] zero (suc n') zero = ≡-refl
m∸n∸o≡m∸[n+o] zero (suc n') (suc o') = ≡-refl
m∸n∸o≡m∸[n+o] (suc m') (suc n') zero = cong (λ x → m' ∸ x) (+-comm 0 n')
m∸n∸o≡m∸[n+o] (suc m') (suc n') (suc o') = m∸n∸o≡m∸[n+o] m' n' (suc o')

m∸sn∸o≡m∸n∸so : (m n o : ℕ) → m ∸ suc n ∸ o ≡ m ∸ n ∸ suc o
m∸sn∸o≡m∸n∸so m n o =
    m ∸ suc n ∸ o   ≡⟨ m∸n∸o≡m∸[n+o] m (suc n) o ⟩
    m ∸ (suc n + o) ≡⟨ ≡-sym (cong (λ x → m ∸ x) (+-suc n o)) ⟩
    m ∸ (n + suc o) ≡⟨ ≡-sym (m∸n∸o≡m∸[n+o] m n (suc o)) ⟩
    m ∸ n ∸ suc o   ∎
    where open ≡-Reasoning

m∸n∸o≡m∸o∸n : (m n o : ℕ) → m ∸ n ∸ o ≡ m ∸ o ∸ n
m∸n∸o≡m∸o∸n m n o =
    m ∸ n ∸ o   ≡⟨ m∸n∸o≡m∸[n+o] m n o ⟩
    m ∸ (n + o) ≡⟨ cong (λ a → m ∸ a) (+-comm n o) ⟩
    m ∸ (o + n) ≡⟨ ≡-sym (m∸n∸o≡m∸[n+o] m o n) ⟩
    m ∸ o ∸ n   ∎
    where open ≡-Reasoning

sm∸n≡so→m∸n≡o : (m n : ℕ) → {o : ℕ} → suc m ∸ n ≡ suc o → m ∸ n ≡ o
sm∸n≡so→m∸n≡o m n {o} sm-n=so =
    m ∸ n                   ≡⟨⟩
    (suc m ∸ suc zero) ∸ n  ≡⟨ m∸n∸o≡m∸o∸n (suc m) (suc zero) n ⟩
    (suc m ∸ n) ∸ suc zero  ≡⟨ cong (λ x → x ∸ suc zero) sm-n=so ⟩
    (suc o) ∸ suc zero      ≡⟨⟩
    o ∎
    where open ≡-Reasoning

∸-suc : (m n : ℕ) → m ≥ n → suc (m ∸ n) ≡ (suc m ∸ n)
∸-suc _ zero m≥n = ≡-refl
∸-suc zero (suc n') ()
∸-suc (suc m') (suc n') m≥n = ∸-suc m' n' (s≤s⁻¹ m≥n)

m≢0→m≡sn : m ≢ 0 → Σ ℕ λ n → m ≡ suc n
m≢0→m≡sn {m = zero} z≢z = ⊥-elim (z≢z ≡-refl)
m≢0→m≡sn {m = suc m'} _ = m' , ≡-refl

m≡spm : m ≢ 0 → m ≡ suc (pred m)
m≡spm {m = m} m≢0 with m ≟ 0
... | yes m≡0 = ⊥-elim (m≢0 m≡0)
... | no m≢0 with m≢0→m≡sn m≢0
m≡spm {m = m} m≢0 | _ | m' , m≡sm' =
    m                   ≡⟨ m≡sm' ⟩
    suc m'              ≡⟨⟩
    suc (suc m' ∸ 1)    ≡⟨ cong (λ x → suc (x ∸ 1)) (≡-sym m≡sm') ⟩
    suc (m ∸ 1)         ∎
    where open ≡-Reasoning

module _
    (P : ℕ → Set ℓ)
    where

    inductive-step-type : Set ℓ
    inductive-step-type = ∀ n → P n → P (suc n)

    module _
        (IH : inductive-step-type)
        where

        induction : P 0 → ∀ n → P n
        induction P[0] zero = P[0]
        induction P[0] (suc n) = IH n (induction P[0] n)

        +-induction : ∀ m n → P m → P (n + m)
        +-induction m zero P[m] = P[m]
        +-induction m (suc n) P[m] = IH (n + m) (+-induction m n P[m])

        ≤-induction : ∀ {m n : ℕ} → m ≤ n → P m → P n
        ≤-induction {m = m} {n} m≤n P[m] = change-type (cong P (m∸n+n≡m m≤n)) (+-induction m (n ∸ m) P[m])
