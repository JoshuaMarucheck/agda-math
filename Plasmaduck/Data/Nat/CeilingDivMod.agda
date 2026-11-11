open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; cong; cong₂; subst; inspect; [_]) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (proj₁; proj₂)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _*_; _/_; _%_; _≟_; NonZero; ≢-nonZero; >-nonZero; ≢-nonZero⁻¹; >-nonZero⁻¹; NonTrivial; n>1⇒nonTrivial; nonTrivial⇒nonZero; nonTrivial⇒n>1; nonTrivial⇒≢1; _≤_; _<_; _≥_; _>_; z≤n; s≤s; s≤s⁻¹)
open import Data.Nat.Properties using (+-suc; +-assoc; +-comm; *-identity; *-comm; *-distrib-∸; *-mono-≤; ≤-reflexive; ≤-refl; ≤-trans; ≤-<-trans; <-≤-trans; module ≤-Reasoning; <⇒≤; m∸n≤m; m≤m+n; m≤n+m; m≤n*m; m<m*n; +-mono-≤; ∸-mono; n∸n≡0)
open import Data.Nat.DivMod using (m≡m%n+[m/n]*n; m%n≡m∸m/n*n; m/n*n≡m; m/n≡1+[m∸n]/n; m%n<n; [m+kn]%n≡m%n; m≥n⇒m/n>0; m<n⇒m%n≡m; n/n≡1; /-mono-≤)
open import Data.Nat.Divisibility using (_∣_; divides; n/m≡quotient; m%n≡0⇒n∣m)

open import Plasmaduck.Data.Nat using (m∸[n∸o]=m+o∸n; +-∸-assoc; m<n⇒m/n≡0; ≤-cmp; n≤sn; n<sn; m+n+o=m+o+n; [m+n]/n=1+m/n; sn≠0; +-∸-comm; [m+kn]/n≡k+m/n; [kn+m]/n≡k+m/n)



{-
    Ceiling division of Nats
-}
module Plasmaduck.Data.Nat.CeilingDivMod where

infixl 7 _/ᶜ_ _%ᶜ_

_/ᶜ_ : (dividend divisor : ℕ) .{{_ : NonZero divisor}} → ℕ
m /ᶜ n@(suc n') = (m + n') / n

-- modulus to go with ceiling division
-- hmm, except this needs to be negative
_%ᶜ_ : (dividend divisor : ℕ) .{{_ : NonZero divisor}} → ℕ
m %ᶜ n@(suc n') with m % n
... | zero = zero
... | i@(suc _) = n ∸ i

m%ᶜn<n : ∀ m n .{{_ : NonZero n}} → m %ᶜ n < n
m%ᶜn<n m n@(suc n') with m % n
... | zero = s≤s z≤n
... | i@(suc i') = s≤s (m∸n≤m n' i')

n∣m⇒m/ᶜn=m/n : ∀ m n .{{_ : NonZero n}} → n ∣ m → m /ᶜ n ≡ m / n
n∣m⇒m/ᶜn=m/n m n@(suc n') m∣n@(divides k m=k*n) =
    (m + n') / n        ≡⟨ cong (λ q → (q + n') / n) m=k*n ⟩
    (k * n + n') / n    ≡⟨ [kn+m]/n≡k+m/n k n n' ⟩
    k + n' / n          ≡⟨ cong (k +_) (m<n⇒m/n≡0 {n'} {n} n<sn) ⟩
    k + 0               ≡⟨ +-comm k 0 ⟩
    k                   ≡⟨ ≡-sym (n/m≡quotient m∣n) ⟩
    m / n               ∎
    where open ≡-Reasoning

m%n=0⇒m/ᶜn=m/n : ∀ m n .{{_ : NonZero n}} → m % n ≡ 0 → m /ᶜ n ≡ m / n
m%n=0⇒m/ᶜn=m/n m n m%n=0 = n∣m⇒m/ᶜn=m/n m n (m%n≡0⇒n∣m m n m%n=0)

m%n≠0⇒m/ᶜn=s[m/n] : ∀ m n .{{_ : NonZero n}} → m % n ≢ 0 → m /ᶜ n ≡ suc (m / n)
m%n≠0⇒m/ᶜn=s[m/n] m n@(suc n') m%n≠0 with m % n | inspect (_% n) m
... | zero | _ = ⊥-elim (m%n≠0 ≡-refl)
... | i@(suc i') | [ m%n=i ] =
    (m + n') / n                    ≡⟨ cong (λ q → (q + n') / n) (m≡m%n+[m/n]*n m n) ⟩
    (m % n + m / n * n + n') / n    ≡⟨ cong (_/ n) (m+n+o=m+o+n (m % n) (m / n * n) n') ⟩
    (m % n + n' + m / n * n) / n    ≡⟨ [m+kn]/n≡k+m/n (m % n + n') (m / n) n ⟩
    m / n + (m % n + n') / n        ≡⟨ cong (m / n +_) (cong (λ q → (q + n') / n) m%n=i) ⟩
    m / n + (i + n') / n            ≡⟨ cong (m / n +_) (cong (_/ n) (≡-sym (+-suc i' n'))) ⟩
    m / n + (i' + n) / n            ≡⟨ cong (m / n +_) ([m+n]/n=1+m/n i' n) ⟩
    m / n + (1 + i' / n)            ≡⟨ cong (m / n +_) (cong suc (m<n⇒m/n≡0 {i'} {n} (<⇒≤ (≤-<-trans (≤-reflexive (≡-sym m%n=i)) (m%n<n m n))))) ⟩
    m / n + (1 + 0)                 ≡⟨⟩
    m / n + 1                       ≡⟨ +-comm (m / n) 1 ⟩
    suc (m / n)                     ∎
    where open ≡-Reasoning

m/n≤m/ᶜn : ∀ m n .{{_ : NonZero n}} → m / n ≤ m /ᶜ n
m/n≤m/ᶜn m n with m % n ≟ 0
... | no m%n≠0 = ≤-trans (n≤sn {m / n}) (≤-reflexive (≡-sym (m%n≠0⇒m/ᶜn=s[m/n] m n m%n≠0)))
... | yes m%n=0 = ≤-reflexive (≡-sym (m%n=0⇒m/ᶜn=m/n m n m%n=0))

m%n≠0⇒m/ᶜn-nonZero : ∀ m n .{{_ : NonZero n}} → m % n ≢ 0 → NonZero (m /ᶜ n)
m%n≠0⇒m/ᶜn-nonZero m n m%n≢0 = ≢-nonZero (subst (_≢ 0) (≡-sym (m%n≠0⇒m/ᶜn=s[m/n] m n m%n≢0)) (sn≠0 (m / n)))

/ᶜ-nonZero : ∀ m n .{{_ : NonZero m}} .{{_ : NonZero n}} → NonZero (m /ᶜ n)
/ᶜ-nonZero m n {{m-nonZero}} with ≤-cmp n m
... | inj₁ n≤m = >-nonZero (<-≤-trans (m≥n⇒m/n>0 n≤m) (m/n≤m/ᶜn m n))
... | inj₂ n>m = m%n≠0⇒m/ᶜn-nonZero m n (≢-nonZero⁻¹  (m % n) {{subst NonZero (≡-sym (m<n⇒m%n≡m {n} {m} n>m)) m-nonZero}})

m≤n⇒m/ᶜn=1 : ∀ m n .{{_ : NonZero m}} .{{_ : NonZero n}} → .(m ≤ n) → m /ᶜ n ≡ 1
m≤n⇒m/ᶜn=1 m@(suc m') n@(suc n') m≤n =
    m /ᶜ n          ≡⟨⟩
    (m + n') / n    ≡⟨ cong (_/ n) (≡-sym (+-suc m' n')) ⟩
    (m' + n) / n    ≡⟨ [m+n]/n=1+m/n m' n ⟩
    1 + m' / n      ≡⟨ cong suc (m<n⇒m/n≡0 {m'} {n} m≤n) ⟩
    1 + 0           ≡⟨⟩
    1               ∎
    where open ≡-Reasoning

m>n⇒m/ᶜn>1 : ∀ m n .{{_ : NonZero n}} → (m > n) → m /ᶜ n > 1
m>n⇒m/ᶜn>1 m@(suc m') n@(suc n') m>n = begin
    suc 1           ≡⟨ cong suc (≡-sym (n/n≡1 n)) ⟩
    1 + n / n       ≤⟨ +-mono-≤ {1} {1} {n / n} {m' / n} ≤-refl (/-mono-≤ {n} {n} {n} {m'} (s≤s⁻¹ m>n) ≤-refl) ⟩
    1 + m' / n      ≡⟨ ≡-sym ([m+n]/n=1+m/n m' n) ⟩
    (m' + n) / n    ≡⟨ cong (_/ n) (+-suc m' n') ⟩
    (m + n') / n    ≡⟨⟩
    m /ᶜ n          ∎
    where open ≤-Reasoning

m=m/ᶜn*n∸m%ᶜn : ∀ m n .{{_ : NonZero n}} → m ≡ m /ᶜ n * n ∸ m %ᶜ n
m=m/ᶜn*n∸m%ᶜn m n@(suc n') with m % n | inspect (_% n) m
... | 0 | [ m%n=0 ] =
    m                   ≡⟨ ≡-sym (m/n*n≡m {m} {n} (m%n≡0⇒n∣m m n m%n=0)) ⟩
    m / n * n           ≡⟨ cong (_* n) (≡-sym (m%n=0⇒m/ᶜn=m/n m n m%n=0)) ⟩
    (m + n') / n * n    ≡⟨⟩
    m /ᶜ n * n          ≡⟨⟩
    m /ᶜ n * n ∸ 0      ∎
    where open ≡-Reasoning
... | i@(suc i') | [ m%n=i ] =
    m                               ≡⟨ m≡m%n+[m/n]*n m n ⟩
    m % n + m / n * n               ≡⟨⟩
    m % n + (0 + m / n * n)         ≡⟨ cong (m % n +_) (cong (_+ m / n * n) (≡-sym (n∸n≡0 n))) ⟩
    m % n + (n ∸ n + m / n * n)     ≡⟨ cong (m % n +_) (≡-sym (+-∸-comm {n} (m / n * n) {n} ≤-refl)) ⟩
    m % n + (suc (m / n) * n ∸ n)   ≡⟨ cong (m % n +_) (cong (λ q → q * n ∸ n) (≡-sym (m%n≠0⇒m/ᶜn=s[m/n] m n (subst (_≢ 0) (≡-sym m%n=i) (sn≠0 i'))))) ⟩
    m % n + (m /ᶜ n * n ∸ n)        ≡⟨ cong₂ _+_ m%n=i ≡-refl ⟩
    i + (m /ᶜ n * n ∸ n)            ≡⟨ ≡-sym (+-∸-assoc i {m /ᶜ n * n} {n} (m≤n*m n (m /ᶜ n) {{m%n≠0⇒m/ᶜn-nonZero m n (subst (_≢ 0) (≡-sym m%n=i) (sn≠0 i'))}})) ⟩
    i + m /ᶜ n * n ∸ n              ≡⟨ cong (_∸ n) (+-comm i (m /ᶜ n * n)) ⟩
    m /ᶜ n * n + i ∸ n              ≡⟨ ≡-sym (m∸[n∸o]=m+o∸n (m /ᶜ n * n) n i (<⇒≤ (subst (_< n) m%n=i (m%n<n m n)))) ⟩
    m /ᶜ n * n ∸ (n ∸ i)            ∎
    where open ≡-Reasoning

m≤m/ᶜn*n : ∀ m n .{{_ : NonZero n}} → m ≤ m /ᶜ n * n
m≤m/ᶜn*n m n = ≤-trans (≤-reflexive (m=m/ᶜn*n∸m%ᶜn m n)) (m∸n≤m (m /ᶜ n * n) (m %ᶜ n))


{-
    * * * - - - -
    * * * * * * *
    * * * * * * *
    |----n=7----|

    m : number of stars
    m /ᶜ n = 3 (height)
    m %ᶜ n = 4 (number of dashes)

    then m /ᶜ n < m because the left column is always full, and there is always a star in the bottom right corner.

    so in particular, one row is full, and the other rows are at least 1.

    Careful of the edge case!:

    * *

    m = 2
    n = 2
    m /ᶜ n = 1
    m %ᶜ n = 0
-}
m/ᶜn<m : ∀ m n .{{_ : NonTrivial m}} .{{_ : NonTrivial n}} .{{_ : NonZero n}} → m /ᶜ n < m
m/ᶜn<m m n@(suc n') with ≤-cmp m n
... | inj₁ m≤n = begin
    suc (m /ᶜ n)    ≡⟨ cong suc (m≤n⇒m/ᶜn=1 m n m≤n) ⟩
    suc (suc zero)  ≤⟨ nonTrivial⇒n>1 m ⟩
    m               ∎
    where
        open ≤-Reasoning
        instance
            n-nonZero : NonZero n
            n-nonZero = nonTrivial⇒nonZero n

            m-nonZero : NonZero m
            m-nonZero = nonTrivial⇒nonZero m

            m/ᶜn-nonZero : NonZero (m /ᶜ n)
            m/ᶜn-nonZero = /ᶜ-nonZero m n
... | inj₂ m>n = begin
    suc (m /ᶜ n)                        ≡⟨ +-comm 1 (m /ᶜ n) ⟩
    m /ᶜ n + 1                          ≤⟨ +-mono-≤ ≤-refl (s≤s⁻¹ (nonTrivial⇒n>1 n)) ⟩
    m /ᶜ n + n'                         ≡⟨ cong (m /ᶜ n +_) n'-thing ⟩
    m /ᶜ n + (2 * n' ∸ n')              ≤⟨ +-mono-≤ {m /ᶜ n} ≤-refl (∸-mono {_} {_} {n'} (*-mono-≤ {2} {m /ᶜ n} {n'} (m>n⇒m/ᶜn>1 m n m>n) ≤-refl) ≤-refl) ⟩ --
    m /ᶜ n + (m /ᶜ n * n' ∸ n')         ≡⟨ ≡-sym (+-∸-assoc (m /ᶜ n) {m /ᶜ n * n'} {n'} (m≤n*m n' (m /ᶜ n))) ⟩
    (m /ᶜ n + m /ᶜ n * n') ∸ n'         ≤⟨ ∸-mono {m /ᶜ n + m /ᶜ n * n'} {_} {n'} {m %ᶜ n} ≤-refl (s≤s⁻¹ (m%ᶜn<n m n)) ⟩
    (m /ᶜ n + m /ᶜ n * n') ∸ m %ᶜ n     ≡⟨ cong (_∸ m %ᶜ n) distrib-thing ⟩
    m /ᶜ n * n ∸ m %ᶜ n                 ≡⟨ ≡-sym (m=m/ᶜn*n∸m%ᶜn m n) ⟩
    m                                   ∎
    where
        instance
            n-nonZero : NonZero n
            n-nonZero = nonTrivial⇒nonZero n

            m-nonZero : NonZero m
            m-nonZero = nonTrivial⇒nonZero m

            m/ᶜn-nonZero : NonZero (m /ᶜ n)
            m/ᶜn-nonZero = /ᶜ-nonZero m n

        n'-thing : n' ≡ n' + (n' + zero) ∸ n'
        n'-thing =
            n'                      ≡⟨ +-comm zero n' ⟩
            n' + zero               ≡⟨ cong (n' +_) (≡-sym (n∸n≡0 n')) ⟩
            n' + (n' ∸ n')          ≡⟨ ≡-sym (+-∸-assoc n' {n'} {n'} ≤-refl) ⟩
            n' + n' ∸ n'            ≡⟨ cong (λ q → n' + q ∸ n') (+-comm zero n') ⟩
            n' + (n' + zero) ∸ n'   ∎
            where open ≡-Reasoning

        distrib-thing : m /ᶜ n + m /ᶜ n * n' ≡ m /ᶜ n * n
        distrib-thing =
            m /ᶜ n + m /ᶜ n * n'      ≡⟨ cong (m /ᶜ n +_) (*-comm (m /ᶜ n) n') ⟩
            m /ᶜ n + n' * (m /ᶜ n)    ≡⟨⟩
            n * (m /ᶜ n)              ≡⟨ *-comm n (m /ᶜ n) ⟩
            m /ᶜ n * n                ∎
            where open ≡-Reasoning
        open ≤-Reasoning
