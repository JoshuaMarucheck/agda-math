open import Relation.Binary.PropositionalEquality using (_≡_; cong; cong₂; subst) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open import Relation.Binary using (Decidable; Reflexive; Transitive; IsPartialOrder; IsPreorder; Antisymmetric)
open import Relation.Nullary using (Dec; yes; no)
open import Data.Product using (proj₂)
open import Data.Nat using (zero; suc; _+_; _∸_; _*_; _/_; _%_; NonZero; ≢-nonZero; ≢-nonZero⁻¹; _≟_; _≤_)
open import Data.Nat.Properties using (+-identity; *-assoc; *-identity; *-zero; *-distrib-+; *-distrib-∸; m+n∸n≡m; ≤-reflexive; ≤-trans; ≤-antisym; m≤n*m; m*n≡0⇒m≡0)
open import Data.Nat.Divisibility using (_∣_; divides; m%n≡0⇒n∣m; n∣m⇒m%n≡0)
open import Data.Nat.DivMod using (m≡m%n+[m/n]*n)

open import Plasmaduck.Data.PropositionalEquality using (≡-isEquivalence)
open import Plasmaduck.Data.Nat using (sn≠0)


module Plasmaduck.Data.Nat.Divisibility where

∣-dec : Decidable _∣_
∣-dec m n with m ≟ 0 | n ≟ 0
... | _ | yes ≡-refl = yes (divides 0 ≡-refl)
... | yes ≡-refl | no n≠0 = no λ (divides m n=m*0) → n≠0 (
    n       ≡⟨ n=m*0 ⟩
    m * 0   ≡⟨ *-zero .proj₂ m ⟩
    0       ∎)
    where open ≡-Reasoning
... | no m≠0 | no n≠0 with (_%_ n m {{≢-nonZero m≠0}}) ≟ 0
... | yes n%m=0 = yes (m%n≡0⇒n∣m n m {{≢-nonZero m≠0}} n%m=0)
... | no n%m≠0 = no λ m∣n → n%m≠0 (n∣m⇒m%n≡0 n m {{≢-nonZero m≠0}} m∣n)

∣-reflexive : _≡_ Relation.Binary.⇒ _∣_
∣-reflexive {x} x=y = divides 1 (≡-trans (≡-sym x=y) (≡-sym (+-identity .proj₂ x)))

∣-refl : Reflexive _∣_
∣-refl = divides 1 (≡-sym (+-identity .proj₂ _))

∣-trans : Transitive _∣_
∣-trans {i} {j} {k} (divides m j=m*i) (divides n k=n*j) = divides (n * m) (
    k           ≡⟨ k=n*j ⟩
    n * j       ≡⟨ cong (n *_) j=m*i ⟩
    n * (m * i) ≡⟨ ≡-sym (*-assoc n m i) ⟩
    n * m * i   ∎)
    where open ≡-Reasoning

∣-max : ∀ i → i ∣ 0
∣-max i = divides 0 ≡-refl

∣-max' : ∀ {i} → 0 ∣ i → i ≡ 0
∣-max' (divides q i=q*0) = ≡-trans i=q*0 (*-zero .proj₂ q)

0-divisor : ∀ {n} → {{_ : NonZero n}} → ((divides p _) : n ∣ 0) → p ≡ 0
0-divisor {n} (divides p 0=p*gcd) = m*n≡0⇒m≡0 p n (≡-sym 0=p*gcd)

∣-antisym : Antisymmetric _≡_ _∣_
∣-antisym {zero} {n} 0∣n _ = ≡-sym (∣-max' 0∣n)
∣-antisym {m} {zero} _ 0∣m = ∣-max' 0∣m
∣-antisym {m@(suc m')} {n@(suc n')} (divides o n=o*m) (divides p m=p*n) = ≤-antisym (≤-trans (m≤n*m m o) (≤-reflexive (≡-sym n=o*m))) (≤-trans (m≤n*m n p) (≤-reflexive (≡-sym m=p*n)))
    where
        instance
            o-nonZero : NonZero o
            o-nonZero = ≢-nonZero λ o=0 → sn≠0 n' (≡-trans n=o*m (≡-trans (cong (_* m) o=0) ≡-refl))

            p-nonZero : NonZero p
            p-nonZero = ≢-nonZero λ p=0 → sn≠0 m' (≡-trans m=p*n (≡-trans (cong (_* n) p=0) ≡-refl))

∣-isPreorder : IsPreorder _≡_ _∣_
∣-isPreorder = record {
    isEquivalence = ≡-isEquivalence;
    reflexive = ∣-reflexive;
    trans = ∣-trans
    }

∣-isPartialOrder : IsPartialOrder _≡_ _∣_
∣-isPartialOrder = record {
    isPreorder = ∣-isPreorder;
    antisym = ∣-antisym
    }

∣-min : ∀ i → 1 ∣ i
∣-min i = divides i (≡-sym (*-identity .proj₂ i))

∣-combine-% : ∀ m n o .{{_ : NonZero m}} → o ∣ n % m → o ∣ m → o ∣ n
∣-combine-% m n o o∣n%m@(divides p n%m=p*o) o∣m@(divides q m=q*o) = divides (p + n / m * q) (
    n                           ≡⟨ m≡m%n+[m/n]*n n m ⟩
    n % m + n / m * m           ≡⟨ cong₂ _+_ n%m=p*o (cong (n / m *_) m=q*o) ⟩
    p * o + n / m * (q * o)     ≡⟨ cong (p * o +_) (≡-sym (*-assoc (n / m) q o)) ⟩
    p * o + (n / m * q) * o     ≡⟨ ≡-sym (*-distrib-+ .proj₂ o p (n / m * q)) ⟩
    (p + n / m * q) * o         ∎)
    where open ≡-Reasoning

∣-mod-% : ∀ m n o .{{_ : NonZero o}} → m ∣ n → m ∣ o → m ∣ n % o
∣-mod-% m n o m∣n@(divides p n=p*m) m∣o@(divides q o=q*m) = divides (p ∸ n / o * q) (
    n % o                           ≡⟨ ≡-sym (m+n∸n≡m (n % o) (n / o * o)) ⟩
    n % o + n / o * o ∸ n / o * o   ≡⟨ cong (_∸ n / o * o) (≡-sym (m≡m%n+[m/n]*n n o)) ⟩
    n ∸ n / o * o                   ≡⟨ cong₂ _∸_ n=p*m (cong (n / o *_) o=q*m) ⟩
    p * m ∸ n / o * (q * m)         ≡⟨ cong (p * m ∸_) (≡-sym (*-assoc (n / o) q m)) ⟩
    p * m ∸ (n / o * q) * m         ≡⟨ ≡-sym (*-distrib-∸ .proj₂ m p (n / o * q)) ⟩
    (p ∸ n / o * q) * m             ∎)
    where open ≡-Reasoning

∣⇒≤ : ∀ {m} {n} .{{_ : NonZero n}} → m ∣ n → m ≤ n
∣⇒≤ {m} {n} (divides k n=k*m) = subst (m ≤_) (≡-sym n=k*m) (m≤n*m m k)
    where
        instance
            k-nonZero : NonZero k
            k-nonZero = ≢-nonZero λ k=0 → ≢-nonZero⁻¹ n (
                n       ≡⟨ n=k*m ⟩
                k * m   ≡⟨ cong (_* m) k=0 ⟩
                0 * m   ≡⟨⟩
                0       ∎)
                where open ≡-Reasoning


