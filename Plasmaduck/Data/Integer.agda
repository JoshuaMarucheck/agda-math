open import Level using (Level) renaming (zero to lzero; suc to lsuc)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; cong₂; inspect; [_]) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open import Relation.Nullary using (Dec; yes; no)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _×_; proj₁; proj₂)
open import Data.Nat as ℕ using (ℕ)
open import Data.Nat.Properties as NatProperties using ()
open import Data.Nat.DivMod using (m≡m%n+[m/n]*n; m%n≡m∸m/n*n; m*n/n≡m; m/n*n≡m; m≥n⇒m/n>0; m%n<n; 0/n≡0) renaming (/-mono-≤ to /-ℕ-mono-≤)
open import Data.Nat.Divisibility using (divides-refl; m%n≡0⇒n∣m) renaming (divides to dividesℕ)
open import Data.Sign.Base as Sign using (Sign)
import Data.Sign.Properties as SignProperties
open import Data.Integer using (ℤ; 0ℤ; 1ℤ; -1ℤ; +_; -_; +0; -[1+_]; +[1+_]; _+_; _-_; _*_; _/_; _/ℕ_; _%ℕ_; Positive; NonNegative; Negative; NonZero; ≢-nonZero; ∣_∣; sign; _◃_; _≟_)
open import Data.Integer.Properties using (i≡j⇒i-j≡0; ◃-inverse; +-assoc; +-comm; +-identity; +-inverse; *-assoc; *-comm; *-identity; *-distrib-+; abs-*; abs-◃; -1*i≡-i; +◃n≡+n; -◃n≡-n; ◃-distrib-*)
open import Data.Integer.DivMod using (a≡a%ℕn+[a/ℕn]*n; a≡a%n+[a/n]*n; div-pos-is-/ℕ; div-neg-is-neg-/ℕ)
open import Data.Integer.Divisibility using () renaming (_∣_ to _∣'_)

open import Plasmaduck.Data.Nat using (m∣n⇒m≤n)


module Plasmaduck.Data.Integer where

variable
    ℓ : Level

inject-sign : Sign → ℤ
inject-sign s = s ◃ 1

sign-inject-sign : ∀ s → sign (inject-sign s) ≡ s
sign-inject-sign Sign.- = ≡-refl
sign-inject-sign Sign.+ = ≡-refl

*-inject-sign : ∀ s t → inject-sign (s Sign.* t) ≡ inject-sign s * inject-sign t
*-inject-sign Sign.- Sign.- = ≡-refl
*-inject-sign Sign.- Sign.+ = ≡-refl
*-inject-sign Sign.+ Sign.- = ≡-refl
*-inject-sign Sign.+ Sign.+ = ≡-refl

-[s◃n]=-s◃n : ∀ s n → - (s ◃ n) ≡ Sign.opposite s ◃ n
-[s◃n]=-s◃n s ℕ.zero = ≡-refl
-[s◃n]=-s◃n Sign.- (ℕ.suc n) = ≡-refl
-[s◃n]=-s◃n Sign.+ (ℕ.suc n) = ≡-refl

sign[-i]=opposite[sign[i]] : ∀ i .{{_ : NonZero i}} → sign (- i) ≡ Sign.opposite (sign i)
sign[-i]=opposite[sign[i]] (+[1+ _ ]) = ≡-refl
sign[-i]=opposite[sign[i]] (-[1+ _ ]) = ≡-refl

abs-neg : ∀ i → ∣ - i ∣ ≡ ∣ i ∣
abs-neg (+[1+ n ]) = ≡-refl
abs-neg +0 = ≡-refl
abs-neg (-[1+ n ]) = ≡-refl

-i*-j=i*j : ∀ i j → - i * - j ≡ i * j
-i*-j=i*j i j =
    - i * - j               ≡⟨ cong (_* - j) (≡-sym (-1*i≡-i i)) ⟩
    -1ℤ * i * - j           ≡⟨ cong (-1ℤ * i *_) (≡-sym (-1*i≡-i j)) ⟩
    (-1ℤ * i) * (-1ℤ * j)   ≡⟨ ≡-sym (*-assoc (-1ℤ * i) -1ℤ j) ⟩
    ((-1ℤ * i) * -1ℤ) * j   ≡⟨ cong (_* j) (*-comm (-1ℤ * i) -1ℤ) ⟩
    (-1ℤ * (-1ℤ * i)) * j   ≡⟨ cong (_* j) (≡-sym (*-assoc -1ℤ -1ℤ i)) ⟩
    (-1ℤ * -1ℤ) * i * j     ≡⟨ cong (λ q → q * i * j) (-1*i≡-i -1ℤ) ⟩
    1ℤ * i * j              ≡⟨ cong (_* j) (*-identity .proj₁ i) ⟩
    i * j                   ∎
    where open ≡-Reasoning

-[i*j]=-i*j : ∀ i j → - (i * j) ≡ - i * j
-[i*j]=-i*j i j with i ≟ 0ℤ
... | yes ≡-refl = ≡-refl
... | no i≠0 =
    - (i * j)                                               ≡⟨⟩
    - (sign i Sign.* sign j ◃ ∣ i ∣ ℕ.* ∣ j ∣)              ≡⟨ -[s◃n]=-s◃n (sign i Sign.* sign j) (∣ i ∣ ℕ.* ∣ j ∣) ⟩
    Sign.opposite (sign i Sign.* sign j) ◃ ∣ i ∣ ℕ.* ∣ j ∣  ≡⟨⟩
    Sign.- Sign.* (sign i Sign.* sign j) ◃ ∣ i ∣ ℕ.* ∣ j ∣  ≡⟨ cong (_◃ ∣ i ∣ ℕ.* ∣ j ∣) (≡-sym (SignProperties.*-assoc Sign.- (sign i) (sign j))) ⟩
    (Sign.- Sign.* sign i) Sign.* sign j ◃ ∣ i ∣ ℕ.* ∣ j ∣  ≡⟨ cong (λ q → q Sign.* sign j ◃ ∣ i ∣ ℕ.* ∣ j ∣) (≡-sym (sign[-i]=opposite[sign[i]] i)) ⟩
    sign (- i) Sign.* sign j ◃ ∣ i ∣ ℕ.* ∣ j ∣              ≡⟨ cong (λ q → sign (- i) Sign.* sign j ◃ q ℕ.* ∣ j ∣) (≡-sym (abs-neg i)) ⟩
    sign (- i) Sign.* sign j ◃ ∣ - i ∣ ℕ.* ∣ j ∣            ≡⟨⟩
    - i * j                                                 ∎
    where
        open ≡-Reasoning
        instance
            i-nonZero : NonZero i
            i-nonZero = ≢-nonZero i≠0

-[i*j]=i*-j : ∀ i j → - (i * j) ≡ i * - j
-[i*j]=i*-j i j =
    - (i * j)   ≡⟨ cong -_ (*-comm i j) ⟩
    - (j * i)   ≡⟨ -[i*j]=-i*j j i ⟩
    - j * i     ≡⟨ *-comm (- j) i ⟩
    i * - j     ∎
    where open ≡-Reasoning

◃→* : ∀ s n → inject-sign s * + n ≡ s ◃ n
◃→* Sign.- ℕ.zero = ≡-refl
◃→* Sign.- (ℕ.suc n) = -1*i≡-i (+ ℕ.suc n)
◃→* Sign.+ n =
    inject-sign Sign.+ * + n    ≡⟨ *-identity .proj₁ (+ n) ⟩
    + n                         ≡⟨ ≡-sym (+◃n≡+n n) ⟩
    Sign.+ ◃ n                  ∎
    where open ≡-Reasoning

div-sign-is-signed-/ℕ₁ : ∀ n d .{{_ : NonZero d}} →
    n / d ≡ (inject-sign (sign d)) * (n /ℕ ∣ d ∣)
div-sign-is-signed-/ℕ₁ n (+ d) =
    n / + d                                     ≡⟨ div-pos-is-/ℕ n d ⟩
    n /ℕ ∣ + d ∣                                ≡⟨ ≡-sym (*-identity .proj₁ (n /ℕ d)) ⟩
    1ℤ * (n /ℕ ∣ + d ∣)                         ≡⟨⟩
    inject-sign (sign (+ d)) * (n /ℕ ∣ + d ∣)   ∎
    where open ≡-Reasoning
div-sign-is-signed-/ℕ₁ n (-[1+ d ]) =
    n / -[1+ d ]                                        ≡⟨ div-neg-is-neg-/ℕ n (ℕ.suc d) ⟩
    - (n /ℕ ∣ -[1+ d ] ∣)                               ≡⟨ ≡-sym (-1*i≡-i _) ⟩
    -1ℤ * (n /ℕ ∣ -[1+ d ] ∣)                           ≡⟨⟩
    inject-sign (sign -[1+ d ]) * (n /ℕ ∣ -[1+ d ] ∣)   ∎
    where open ≡-Reasoning

+-pos : ∀ {m} → .{{ℕ.NonZero m}} → Positive (+ m)
+-pos {ℕ.suc m} = record { pos = tt }

i-i=0 : ∀ i → i - i ≡ 0ℤ
i-i=0 i = i≡j⇒i-j≡0 {i} ≡-refl

minus-neg-sign : ∀ m .{{_ : ℕ.NonZero m}} → sign (- (+ m)) ≡ Sign.-
minus-neg-sign (ℕ.suc m) = ≡-refl

/ℕ-sign : ∀ i m .{{_ : ℕ.NonZero m}} → sign (i /ℕ m) ≡ sign i
/ℕ-sign (+ i) (ℕ.suc m) = ≡-refl
/ℕ-sign (-[1+ i' ]) m@(ℕ.suc m') with ℕ.suc i' ℕ.% m | inspect (ℕ._% m) (ℕ.suc i')
... | ℕ.suc r | _ = ≡-refl
... | ℕ.zero | [ i%m=0 ] with i ℕ./ m | m≥n⇒m/n>0 (m∣n⇒m≤n m i (m%n≡0⇒n∣m i m i%m=0))
    where i = ℕ.suc i'
...     | ℕ.suc [i/m]' | _ = ≡-refl

P-abs : (P : ℤ → Set ℓ) → ∀ i → P i → P (- i) → P (+ ∣ i ∣)
P-abs P (+ i) P[i] P[-i] = P[i]
P-abs P (-[1+ i' ]) P[i] P[-i] = P[-i]

0/i=0 : ∀ i .{{_ : NonZero i}} → 0ℤ / i ≡ 0ℤ
0/i=0 (+ (ℕ.suc i)) = ≡-refl
0/i=0 (-[1+ i' ]) = ≡-refl

i+j-j=i : ∀ i j → i + j - j ≡ i
i+j-j=i i j =
    (i + j) - j     ≡⟨ +-assoc i j (- j) ⟩
    i + (j - j)     ≡⟨ cong (λ q → i + q) (+-inverse .proj₂ j) ⟩
    i + 0ℤ          ≡⟨ +-identity .proj₂ i ⟩
    i               ∎
    where open ≡-Reasoning

i-j+j=i : ∀ i j → i - j + j ≡ i
i-j+j=i i j =
    i - j + j       ≡⟨ +-assoc i (- j) j ⟩
    i + (- j + j)   ≡⟨ cong (λ q → i + q) (+-inverse .proj₁ j) ⟩
    i + 0ℤ          ≡⟨ +-identity .proj₂ i ⟩
    i               ∎
    where open ≡-Reasoning

i*j*k=i*k*j : ∀ i j k → i * j * k ≡ i * k * j
i*j*k=i*k*j i j k =
    i * j * k       ≡⟨ *-assoc i j k ⟩
    i * (j * k)     ≡⟨ cong (i *_) (*-comm j k) ⟩
    i * (k * j)     ≡⟨ ≡-sym (*-assoc i k j) ⟩
    i * k * j       ∎
    where open ≡-Reasoning

foil : ∀ i j k l → (i + j) * (k + l) ≡ i * k + i * l + j * k + j * l
foil i j k l =
    (i + j) * (k + l)                   ≡⟨ *-distrib-+ .proj₂ (k + l) i j ⟩
    i * (k + l) + j * (k + l)           ≡⟨ cong₂ _+_ (*-distrib-+ .proj₁ i k l) (*-distrib-+ .proj₁ j k l) ⟩
    (i * k + i * l) + (j * k + j * l)   ≡⟨ ≡-sym (+-assoc (i * k + i * l) (j * k) (j * l)) ⟩
    i * k + i * l + j * k + j * l       ∎
    where open ≡-Reasoning
