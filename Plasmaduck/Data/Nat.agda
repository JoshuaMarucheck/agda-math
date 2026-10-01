open import Level using (Level)
open import Relation.Binary.PropositionalEquality using (_≢_; _≡_; inspect; cong; cong₂; subst; Reveal_·_is_; [_]) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open import Relation.Binary using (tri<; tri≈; tri>; Recomputable; Setoid)
open import Relation.Nullary.Decidable using (Dec; yes; no; recompute)
open import Relation.Nullary.Negation using (¬_)
import Relation.Nullary as Nullary
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; _+_; _*_; _≤_; _≥_; _<_; _>_; _∸_; <-cmp; _<?_; _≤?_; s≤s; z≤n; s≤s⁻¹; zero; suc; pred; NonZero; ≢-nonZero; NonTrivial; _⊔_; _⊓_)
open import Data.Nat.Properties using (<-irrefl; <-≤-trans; ≤-<-trans; ≤-trans; <-trans; ≤-reflexive; <⇒≤; +-mono-≤; +-comm; +-suc; +-∸-assoc; *-comm; *-assoc; *-identity; *-zero; *-distrib-∸; _≟_; m∸n+n≡m; m+n∸n≡m; n∸n≡0; m*n≢0⇒m≢0; m≤m*n; m≤n*m; m<m*n; m≤n⇒m⊔n≡n; m≥n⇒m⊔n≡m; ⊔-comm)
open import Data.Nat.DivMod using (_/_; _%_; m≡m%n+[m/n]*n; m/n≡1+[m∸n]/n; m<n⇒m/n≡0; m<n⇒m%n≡m; m%n<n; +-distrib-/-∣ˡ; m*n/n≡m; m/n*n≡m; m*n/m*o≡n/o; m%[n*o]/o≡m/o%n; m∣n⇒o%n%m≡o%m; m%n≡m∸m/n*n; m*n%n≡0; *-/-assoc; /-congˡ; /-congʳ; %-congˡ; %-congʳ)
open import Data.Nat.Divisibility using (divides; _∣_; n/m≡quotient)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; uncurry)
open import Data.Empty using (⊥; ⊥-elim)
open import Algebra.Definitions {A = ℕ} _≡_ using (_DistributesOver_; _DistributesOverʳ_; _DistributesOverˡ_)
open import Function using (Bijection; _∋_)

open import Plasmaduck.SetoidExperiment.SetoidMachinery using (discrete-setoid; SetoidFunction₂)
open import Plasmaduck.Util.TypeChange using (change-type)
open import Plasmaduck.Util.Case using (case_of_)
open import Plasmaduck.Data.Empty using (≢-recompute; ⊥-irr-elim)
open import Plasmaduck.Data.Product using (Σ≡; ×≡)
open import Plasmaduck.Data.Squash using (Squash; squash)
open import Plasmaduck.Data.FakeFin using (FakeFin; realize; falsify)
open import Plasmaduck.Relation.Equivalence using (irrelevant-cong)



module Plasmaduck.Data.Nat where


variable
    m n o p : ℕ
    c ℓ ℓ₁ : Level

*-nonZero : ∀ m n .{{_ : NonZero m}} .{{_ : NonZero n}} → NonZero (m * n)
*-nonZero (suc m) (suc n) = record { nonZero = tt }

¬NonZero⇒is-zero : ¬ NonZero n → n ≡ 0
¬NonZero⇒is-zero {n = n} ¬nonZero with n ≟ 0
... | yes n=0 = n=0
... | no n≠0 = ⊥-elim (¬nonZero (≢-nonZero n≠0))

≤-recompute : Recomputable _≤_
≤-recompute {x} {y} = recompute (x ≤? y)

-- Look at how cheap this is!
NonZero-recompute : Nullary.Recomputable (NonZero n)
NonZero-recompute {zero} ()
NonZero-recompute {suc n} _ = record { nonZero = tt }

NonTrivial-recompute : Nullary.Recomputable (NonTrivial n)
NonTrivial-recompute {zero} ()
NonTrivial-recompute {suc zero} ()
NonTrivial-recompute {suc (suc n)} _ = record { nonTrivial = tt }

m≤1⇒m*n≤n : ∀ m n → .(m ≤ 1) → m * n ≤ n
m≤1⇒m*n≤n zero n m≤1 = z≤n
m≤1⇒m*n≤n (suc zero) n m≤1 = ≤-reflexive (+-comm n zero)
m≤1⇒m*n≤n (suc (suc m)) n m≤1 = ⊥-irr-elim (case s≤s⁻¹ m≤1 of λ ())

NonTrivial-divisor : ∀ m n .{{_ : NonTrivial m}} → .(m < m * n) → NonTrivial n
NonTrivial-divisor m zero m<m*n = ⊥-irr-elim (case <-≤-trans m<m*n (≤-reflexive (*-zero .proj₂ m)) of λ ())
NonTrivial-divisor m (suc zero) m<m*n = ⊥-irr-elim (<-irrefl {m} ≡-refl (<-≤-trans m<m*n (≤-reflexive (*-identity .proj₂ m))))
NonTrivial-divisor m (suc (suc n)) m<m*n = record { nonTrivial = tt }

nonTrivial⇒pred-nonZero : ∀ n .{{_ : NonTrivial n}} → NonZero (pred n)
nonTrivial⇒pred-nonZero (suc (suc _)) = record { nonZero = tt }

≤-cmp : (m n : ℕ) → m ≤ n ⊎ m > n
≤-cmp m n with <-cmp m n
... | tri< m<n _ _ = inj₁ (<⇒≤ m<n)
... | tri≈ _ m=n _ = inj₁ (≤-reflexive m=n)
... | tri> _ _ m>n = inj₂ m>n

⊔≥₁ : ∀ m n → m ⊔ n ≥ m
⊔≥₁ m n with ≤-cmp m n
... | inj₁ m≤n = ≤-trans m≤n (≤-reflexive (≡-sym (m≤n⇒m⊔n≡n m≤n)))
... | inj₂ m>n = ≤-reflexive (≡-sym (m≥n⇒m⊔n≡m (<⇒≤ m>n)))

⊔≥₂ : ∀ m n → m ⊔ n ≥ n
⊔≥₂ m n = ≤-trans (⊔≥₁ n m) (≤-reflexive (⊔-comm n m))

max : ℕ → ℕ → ℕ
max m n with m ≤? n
... | yes _ = n
... | no _ = m

n≤n : n ≤ n
n≤n {n = zero} = z≤n
n≤n {n = suc n'} = s≤s n≤n

n<sn : n < suc n
n<sn = n≤n

n≤sn : n ≤ suc n
n≤sn {n = zero} = z≤n
n≤sn {n = suc n'} = s≤s n≤sn

m>0⇒m=sn : .(m > 0) → Σ ℕ λ n → m ≡ suc n
m>0⇒m=sn {m = suc m} m>0 = m , ≡-refl

m<n*m : ∀ m n .{{_ : NonZero m}} → 1 < n → m < n * m
m<n*m m n 1<n = <-≤-trans (m<m*n m n 1<n) (≤-reflexive (*-comm m n))

m≢0⇒m=sn : .(m ≢ 0) → Σ ℕ λ n → m ≡ suc n
m≢0⇒m=sn {m = zero} m≠0 = ⊥-elim ((≢-recompute m≠0) ≡-refl)
m≢0⇒m=sn {m = suc m} _ = m , ≡-refl

sn≠0 : ∀ n → suc n ≢ 0
sn≠0 n ()

m<n⇒m≢n : .(m > 0) → m ≢ 0
m<n⇒m≢n {0} 0>0 ≡-refl = case (≤-recompute 0>0) of λ ()

m≤n⇒m≤pn : m ≤ n → pred m ≤ n
m≤n⇒m≤pn {m = zero} {n = n} m≤n = z≤n
m≤n⇒m≤pn {m = m@(suc m')} {n = n} m≤n = ≤-trans n≤sn m≤n

m<o∧n<p⇒s[m+o]<n+p : m < o → n < p → suc (m + n) < o + p
m<o∧n<p⇒s[m+o]<n+p {m = m} {n = n} m<o n<p = ≤-trans (≤-reflexive (cong suc (≡-sym (+-suc m n)))) (+-mono-≤ m<o n<p)

<→≤ : m < n → m ≤ n
<→≤ (s≤s m-1<n-1) = ≤-trans m-1<n-1 n≤sn

≤≥⇒≡ : .(m ≤ n) → m ≥ n → m ≡ n
≤≥⇒≡ {m} {n} m≤n m≥n with <-cmp m n
... | tri< m<n _ _ = ⊥-elim (<-irrefl ≡-refl (<-≤-trans m<n (≤-recompute m≥n)))
... | tri≈ _ m≡n _ = m≡n
... | tri> _ _ m>n = ⊥-elim (<-irrefl ≡-refl (<-≤-trans m>n (≤-recompute m≤n)))

≤→<≡ : .(m ≤ n) → m < n ⊎ m ≡ n
≤→<≡ {m = m} {n = n} m≤n with <-cmp m n
... | tri< m<n _ _ = inj₁ m<n
... | tri≈ _ m≡n _ = inj₂ m≡n
... | tri> _ _ m>n = ⊥-elim (<-irrefl ≡-refl (<-≤-trans m>n (≤-recompute m≤n)))

<≡→≤ : m < n ⊎ m ≡ n → m ≤ n
<≡→≤ (inj₁ m<n) = <→≤ m<n
<≡→≤ (inj₂ m≡n) = ≤-reflexive m≡n

max≥fst : max m n ≥ m
max≥fst {m} {n} with m ≤? n
... | yes m≤n = m≤n
... | no _ = n≤n

max≥snd : max m n ≥ n
max≥snd {m} {n} with m ≤? n
... | yes _ = n≤n
... | no ¬m≤n with <-cmp m n
...     | tri< m<n _ _ = ⊥-elim (¬m≤n (<→≤ m<n))
...     | tri≈ _ m≡n _ = ≤-reflexive (≡-sym m≡n)
...     | tri> _ _ m>n = ≤-trans n≤sn m>n

s≡s⁻¹ : suc m ≡ suc n → m ≡ n
s≡s⁻¹ ≡-refl = ≡-refl

+-∸-telescope : (m n o : ℕ) → m ≥ n → n ≥ o → (m ∸ n) + (n ∸ o) ≡ m ∸ o
+-∸-telescope m n o m≥n n≥o =
    (m ∸ n) + (n ∸ o)   ≡⟨ ≡-sym (+-∸-assoc (m ∸ n) {n} {o} n≥o) ⟩
    (m ∸ n + n) ∸ o     ≡⟨ cong (_∸ o) (m∸n+n≡m {m} {n} m≥n) ⟩
    m ∸ o               ∎
    where open ≡-Reasoning

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

∸-suc : (m n : ℕ) → .(m ≥ n) → suc (m ∸ n) ≡ (suc m ∸ n)
∸-suc _ zero m≥n = ≡-refl
∸-suc zero (suc n') ()
∸-suc (suc m') (suc n') m≥n = ∸-suc m' n' (s≤s⁻¹ m≥n)

m≢0→m≡sn : .(m ≢ 0) → Σ ℕ λ n → m ≡ suc n
m≢0→m≡sn {m = zero} z≢z = ⊥-elim ((≢-recompute z≢z) ≡-refl)
m≢0→m≡sn {m = suc m'} _ = m' , ≡-refl

m≡spm : .(m ≢ 0) → m ≡ suc (pred m)
m≡spm {m = m} m≢0 with m≢0→m≡sn m≢0
m≡spm {m = m} m≢0 | m' , m≡sm' =
    m                   ≡⟨ m≡sm' ⟩
    suc m'              ≡⟨⟩
    suc (suc m' ∸ 1)    ≡⟨ cong (λ x → suc (x ∸ 1)) (≡-sym m≡sm') ⟩
    suc (m ∸ 1)         ∎
    where open ≡-Reasoning

n=spn : {{NonZero n}} → n ≡ suc (pred n)
n=spn {suc n} = ≡-refl

[m+n]/n=1+m/n : .{{_ : NonZero n}} → (m + n) / n ≡ 1 + m / n
[m+n]/n=1+m/n {n = n} {m = m} =
    (m + n) / n             ≡⟨ m/n≡1+[m∸n]/n {m + n} {n} (+-mono-≤ {0} {m} {n} {n} z≤n n≤n) ⟩
    1 + (m + n ∸ n) / n     ≡⟨ cong (λ q → 1 + q / n) (m+n∸n≡m m n) ⟩
    1 + m / n               ∎
    where open ≡-Reasoning

[m*n+i]/n=i : {m n i : ℕ} → .{{_ : NonZero n}} → i < n → (m * n + i) / n ≡ m
[m*n+i]/n=i {m} {n@(suc n')} {i} i<n =
    (m * n + i) / n     ≡⟨ +-distrib-/-∣ˡ {m * n} i {n} (divides m ≡-refl) ⟩
    m * n / n + i / n   ≡⟨ cong (_+ i / n) (m*n/n≡m m n) ⟩
    m + i / n           ≡⟨ cong (m +_) ((m<n⇒m/n≡0 {i} {n} i<n)) ⟩
    m + zero            ≡⟨ +-comm m zero ⟩
    m                   ∎
    where open ≡-Reasoning

m=n*o⇒m/n=o : ∀ m n o .{{_ : NonZero n}} → m ≡ n * o → m / n ≡ o
m=n*o⇒m/n=o m n o m=n*o = n/m≡quotient {n} {m} (divides o (≡-trans m=n*o (*-comm n o)))

quotient-nonZero : {m n : ℕ} → {{NonZero m}} → {{_ : NonZero n}} → n ∣ m → NonZero (m / n)
quotient-nonZero {m} {n} {{m-nonZero}} {{n-nonZero}} (divides q m=q*n) = change-type (cong NonZero q=m/n) q-nonZero
    where
        q=m/n : q ≡ m / n
        q=m/n = ≡-trans (≡-sym (m*n/n≡m q n)) (/-congˡ (≡-sym m=q*n))

        instance
            q*n-nonZero : NonZero (q * n)
            q*n-nonZero = change-type (cong NonZero m=q*n) m-nonZero

        q-nonZero : NonZero q
        q-nonZero = m*n≢0⇒m≢0 q {n}

/-distribʳ-% : (m n o : ℕ) → .{{_ : NonZero n}} .{{_ : NonZero o}} →
    (o∣n : o ∣ n) →
    m % n / o ≡ ((m / o) % (n / o)) {{quotient-nonZero o∣n}}
/-distribʳ-% m n o {{n-nonZero}} (divides q n=q*o) =
    m % n / o           ≡⟨ /-congˡ (%-congʳ n=q*o) ⟩
    m % (q * o) / o     ≡⟨ m%[n*o]/o≡m/o%n m q o ⟩
    (m / o) % q         ≡⟨ %-congʳ {q} {n / o} {m / o} q=n/o ⟩
    (m / o) % (n / o)   ∎
    where
        open ≡-Reasoning

        q=n/o : q ≡ n / o
        q=n/o = ≡-trans (≡-sym (m*n/n≡m q o)) (/-congˡ (≡-sym n=q*o))

        instance
            q*o-nonZero : NonZero (q * o)
            q*o-nonZero = NonZero-recompute (change-type (cong NonZero n=q*o) n-nonZero)

            q-nonZero : NonZero q
            q-nonZero = m*n≢0⇒m≢0 q {o}

            q*o/o-nonZero : NonZero (q * o / o)
            q*o/o-nonZero = change-type (cong NonZero (≡-sym (m*n/n≡m q o))) q-nonZero

            n/o-nonZero : NonZero (n / o)
            n/o-nonZero = change-type (cong NonZero q=n/o) q-nonZero

m∣n⇒m≤n : ∀ m n .{{_ : NonZero m}} .{{_ : NonZero n}} → m ∣ n → m ≤ n
m∣n⇒m≤n m n {{_}} {{n-nonZero}} (divides k n=k*m) = ≤-trans (m≤n*m m k) (≤-reflexive (≡-sym n=k*m))
    where
        instance
            k-nonZero : NonZero k
            k-nonZero = m*n≢0⇒m≢0 k {m} {{change-type (cong NonZero n=k*m) n-nonZero}}

m%n%o=m%n : (m n o : ℕ) → .{{_ : NonZero n}} → .{{_ : NonZero o}} →
    n ≤ o →
    m % n % o ≡ m % n
m%n%o=m%n m n o n≤o = m<n⇒m%n≡m {o} {m % n} (<-≤-trans (m%n<n m n) n≤o)

*-distribˡ-% : ∀ m n o .{{_ : NonZero o}} .{{_ : NonZero (m * o)}} → m * (n % o) ≡ (m * n) % (m * o)
*-distribˡ-% m n o =
    m * (n % o)                             ≡⟨ cong (m *_) (m%n≡m∸m/n*n n o) ⟩
    m * (n ∸ n / o * o)                     ≡⟨ *-distrib-∸ .proj₁ m n (n / o * o) ⟩
    m * n ∸ m * (n / o * o)                 ≡⟨ cong (m * n ∸_) (*-comm m (n / o * o)) ⟩
    m * n ∸ (n / o * o) * m                 ≡⟨ cong (m * n ∸_) (*-assoc (n / o) o m) ⟩
    m * n ∸ (n / o) * (o * m)               ≡⟨ cong (λ q → m * n ∸ (n / o) * q) (*-comm o m) ⟩
    m * n ∸ (n / o) * (m * o)               ≡⟨ cong (λ q → m * n ∸ q * (m * o)) (≡-sym (m*n/m*o≡n/o m n o)) ⟩
    m * n ∸ (m * n) / (m * o) * (m * o)     ≡⟨ ≡-sym (m%n≡m∸m/n*n (m * n) (m * o)) ⟩
    (m * n) % (m * o)                       ∎
    where open ≡-Reasoning

*-distribʳ-% : ∀ m n o .{{_ : NonZero o}} .{{_ : NonZero (o * m)}} → (n % o) * m ≡ (n * m) % (o * m)
*-distribʳ-% m n o {{_}} {{o*m-nonZero}} =
    (n % o) * m         ≡⟨ *-comm (n % o) m ⟩
    m * (n % o)         ≡⟨ *-distribˡ-% m n o ⟩
    (m * n) % (m * o)   ≡⟨ cong (_% (m * o)) (*-comm m n) ⟩
    (n * m) % (m * o)   ≡⟨ %-congʳ {o = n * m} (*-comm m o) ⟩
    (n * m) % (o * m)   ∎
    where
        open ≡-Reasoning
        instance
            m*o-nonZero : NonZero (m * o)
            m*o-nonZero = NonZero-recompute (subst NonZero (*-comm o m) o*m-nonZero)

{-
    Intuition:
    Consider a digit in a multi-base numeral

    Lower sig ---> Higher sig
    Base:   3   5   8   7   13
    Num:    1   2   3   4   5

    So this would be the number 1 + 2 * (3) + 3 * (5 * 3) + 4 * (8 * 5 * 3) + 5 * (7 * 8 * 5 * 3)

    Consider the goal of extracting a digit from this number. In particular, suppose we want the third digit (so the 3).

    One way to do it is:
    divide by the lower base (3 * 5)
    giving us the number
    Base:   8   7   13
    Num:    3   4   5
    and the modulo by the digit base 8, giving us 3

    but alternatively, we could crop off the higher digits first, moduloing by (3 * 5 * 8 * 7), giving us the number
    Base:   3   5   8   7
    Num:    1   2   3   4
    and then divide by (3 * 5)
    Base:   8   7
    Num:    3   4
    and then modulo again to get 3.

    note the smaller modulo and divide both divide the big initial modulo. I think that is key to how this works.
-}
[[m%n]/o]%p=[m/o]%p : {m n o p : ℕ} → {{_ : NonZero n}} {{_ : NonZero o}} {{_ : NonZero p}} →
    o * p ∣ n →
    ((m % n) / o) % p ≡ (m / o) % p
[[m%n]/o]%p=[m/o]%p {m} {n} {o} {p} o*p∣n@(divides q n=q*[o*p]) =
    m % n / o % p           ≡⟨ %-congˡ (/-distribʳ-% m n o o∣n) ⟩
    (m / o) % (n / o) % p   ≡⟨ m∣n⇒o%n%m≡o%m p (n / o) (m / o) p∣n/o ⟩
    m / o % p               ∎
    where
        open ≡-Reasoning

        n=q*p*o : n ≡ q * p * o
        n=q*p*o =
            n               ≡⟨ n=q*[o*p] ⟩
            q * (o * p)     ≡⟨ cong (q *_) (*-comm o p) ⟩
            q * (p * o)     ≡⟨ ≡-sym (*-assoc q p o) ⟩
            (q * p) * o     ∎

        o∣n : o ∣ n
        o∣n = divides (q * p) n=q*p*o

        p∣n/o : p ∣ n / o
        p∣n/o = divides q (
            n / o           ≡⟨ /-congˡ n=q*p*o ⟩
            q * p * o / o   ≡⟨ m*n/n≡m (q * p) o ⟩
            q * p           ∎)
        instance
            n/o-nonZero : NonZero (n / o)
            n/o-nonZero = quotient-nonZero o∣n

m+m*n=m*sn : (m n : ℕ) → m + m * n ≡ m * suc n
m+m*n=m*sn m n =
    m + m * n   ≡⟨ cong (m +_) (*-comm m n) ⟩
    m + n * m   ≡⟨⟩
    suc n * m   ≡⟨ *-comm (suc n) m ⟩
    m * suc n   ∎
    where open ≡-Reasoning

m*n*o=m*o*n : (m n o : ℕ) → m * n * o ≡ m * o * n
m*n*o=m*o*n m n o =
    (m * n) * o ≡⟨ *-assoc m n o ⟩
    m * (n * o) ≡⟨ cong (m *_) (*-comm n o) ⟩
    m * (o * n) ≡⟨ ≡-sym (*-assoc m o n) ⟩
    (m * o) * n ∎
    where open ≡-Reasoning

m≠0∧n≠0⇒m*n≠0 : ∀ m n → .{{NonZero m}} → .{{NonZero n}} → NonZero (m * n)
m≠0∧n≠0⇒m*n≠0 (suc m) (suc n) = record { nonZero = tt }

m∣n⇒n%m≡0 : ∀ n m .{{_ : NonZero m}} → m ∣ n → n % m ≡ 0
m∣n⇒n%m≡0 n m (divides k n=k*m) =
    n % m       ≡⟨ cong (_% m) n=k*m ⟩
    k * m % m   ≡⟨ m*n%n≡0 k m ⟩
    0           ∎
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


≤-proofs-equal : {pf₁ pf₂ : m ≤ n} → pf₁ ≡ pf₂
≤-proofs-equal {pf₁ = z≤n} {z≤n} = ≡-refl
≤-proofs-equal {pf₁ = s≤s pf₁} {s≤s pf₂} = cong s≤s ≤-proofs-equal
