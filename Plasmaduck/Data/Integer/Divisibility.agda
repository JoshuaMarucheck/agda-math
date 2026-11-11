open import Relation.Nullary using (Dec; yes; no; recompute)
open import Relation.Binary using (Decidable; Reflexive; Transitive; Recomputable)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; inspect; [_]) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open import Function using (_∘_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (proj₁; proj₂)
open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Data.Nat.Properties as NatProperties using ()
open import Data.Nat.DivMod using (m%n<n)
open import Data.Nat.Divisibility using (m%n≡0⇒n∣m) renaming (divides to dividesℕ)
open import Data.Sign.Base as Sign using (Sign)
import Data.Sign.Properties as SignProperties
open import Data.Integer using (ℤ; 0ℤ; 1ℤ; +_; -_; -[1+_]; _+_; _-_; _*_; _/_; _%_; _/ℕ_; _%ℕ_; _≟_; NonZero; ≢-nonZero; ∣_∣; sign; _◃_)
open import Data.Integer.Properties using (◃-inverse; +-identity; *-assoc; *-comm; *-identity; *-zero; *-cancelʳ-≡; abs-*; neg-distribˡ-*; ◃-distrib-*)
open import Data.Integer.Divisibility using () renaming (_∣_ to _∣'_)

open import Plasmaduck.Data.Nat using (m∣n⇒n%m≡0; sn≠0)
open import Plasmaduck.Data.Integer using (-i*-j=i*j; P-abs)
open import Plasmaduck.Data.Integer.DivMod using (i/j*j=i-i%j)



module Plasmaduck.Data.Integer.Divisibility where

-- For the purposes of actually using this, I much prefer this definition to the one in the standard library.
record _∣_ (i j : ℤ) : Set where
    constructor divides
    field
        quotient : ℤ
        equality : j ≡ quotient * i
infix 4 _∣_

∣-refl : Reflexive _∣_
∣-refl = divides 1ℤ (≡-sym (*-identity .proj₁ _))

∣-trans : Transitive _∣_
∣-trans {i} {j} {k} (divides p j=p*i) (divides q k=q*j) = divides (q * p) (
    k               ≡⟨ k=q*j ⟩
    q * j           ≡⟨ cong (q *_) j=p*i ⟩
    q * (p * i)     ≡⟨ ≡-sym (*-assoc q p i) ⟩
    (q * p) * i     ∎)
    where open ≡-Reasoning

∣-max : ∀ i → i ∣ 0ℤ
∣-max i = divides 0ℤ (*-zero .proj₁ i)

∣-min : ∀ i → 1ℤ ∣ i
∣-min i = divides i (≡-sym (*-identity .proj₂ i))

0∣i⇒i=0 : ∀ {i} → 0ℤ ∣ i → i ≡ 0ℤ
0∣i⇒i=0 {i} (divides k i=k*0) = ≡-trans i=k*0 (*-zero .proj₂ k)

∣⇒∣' : ∀ {i j} → i ∣ j → i ∣' j
∣⇒∣' {i} {j} (divides q j=q*i) = dividesℕ ∣ q ∣ (
    ∣ j ∣               ≡⟨ cong ∣_∣ j=q*i ⟩
    ∣ q * i ∣           ≡⟨ abs-* q i ⟩
    ∣ q ∣ ℕ.* ∣ i ∣     ∎)
    where open ≡-Reasoning

∣'⇒∣ : ∀ {i j} → i ∣' j → i ∣ j
∣'⇒∣ {i} {j} (dividesℕ q j=q*i) = divides (sign j Sign.* sign i ◃ q) (
    j                                                   ≡⟨ ≡-sym (◃-inverse j) ⟩
    sign j ◃ ∣ j ∣                                      ≡⟨ cong (_◃ ∣ j ∣) (≡-sym (SignProperties.*-identity .proj₂ (sign j))) ⟩
    sign j Sign.* Sign.+ ◃ ∣ j ∣                        ≡⟨ cong (λ s → sign j Sign.* s ◃ ∣ j ∣) (≡-sym (SignProperties.*-inverse .proj₁ (sign i))) ⟩
    sign j Sign.* (sign i Sign.* sign i) ◃ ∣ j ∣        ≡⟨ cong (_◃ ∣ j ∣) (≡-sym (SignProperties.*-assoc (sign j) (sign i) (sign i))) ⟩
    (sign j Sign.* sign i) Sign.* sign i ◃ ∣ j ∣        ≡⟨ cong (sign j Sign.* sign i Sign.* sign i ◃_) j=q*i ⟩
    (sign j Sign.* sign i) Sign.* sign i ◃ q ℕ.* ∣ i ∣  ≡⟨ ◃-distrib-* (sign j Sign.* sign i) (sign i) q ∣ i ∣ ⟩
    (sign j Sign.* sign i ◃ q) * (sign i ◃ ∣ i ∣)       ≡⟨ cong  ((sign j Sign.* sign i ◃ q) *_) (◃-inverse i) ⟩
    (sign j Sign.* sign i ◃ q) * i                      ∎)
    where open ≡-Reasoning

i∣j⇒-i∣j : ∀ {i j} → i ∣ j → (- i) ∣ j
i∣j⇒-i∣j {i} {j} (divides k j=k*i) = divides (- k) (≡-trans j=k*i (≡-sym (-i*-j=i*j k i)))

i∣j⇒i∣-j : ∀ {i j} → i ∣ j → i ∣ (- j)
i∣j⇒i∣-j {i} {j} (divides k j=k*i) = divides (- k) (≡-trans (cong -_ j=k*i) (neg-distribˡ-* k i))

i∣j⇒abs-i∣j : ∀ {i j} → i ∣ j → (+ ∣ i ∣) ∣ j
i∣j⇒abs-i∣j {i} {j} i∣j = P-abs (λ q → q ∣ j) i i∣j (i∣j⇒-i∣j i∣j)

i∣j⇒i∣abs-j : ∀ {i j} → i ∣ j → i ∣ (+ ∣ j ∣)
i∣j⇒i∣abs-j {i} {j} i∣j = P-abs (λ q → i ∣ q) j i∣j (i∣j⇒i∣-j i∣j)

abs-i∣j⇒i∣j : ∀ i {j} → (+ ∣ i ∣) ∣ j → i ∣ j
abs-i∣j⇒i∣j (+ i) abs-i∣j = abs-i∣j
abs-i∣j⇒i∣j (-[1+ i' ]) abs-i∣j = i∣j⇒-i∣j abs-i∣j

i∣abs-j⇒i∣j : ∀ {i} j → i ∣ (+ ∣ j ∣) → i ∣ j
i∣abs-j⇒i∣j {i} (+ j) i∣abs-j = i∣abs-j
i∣abs-j⇒i∣j {i} (-[1+ j' ]) i∣abs-j = i∣j⇒i∣-j i∣abs-j

i∣j*i : ∀ i j → i ∣ j * i
i∣j*i i j = divides j ≡-refl

i∣i*j : ∀ i j → i ∣ i * j
i∣i*j i j = divides j (*-comm i j)


-----------------------------
--- Divisibility by a Nat ---
-----------------------------
{- Three possible representations of divisibility here:
    - + m ∣ i (equivalently as above, + m ∣' i)
    - i %ℕ m ≡ 0        (note this is equivalent to i % + m ≡ 0)
    - ∣ i ∣ ℕ.% m ≡ 0   (note this is equivalent to + ∣ i ∣ % + m ≡ 0)
-}

i%ℕm=0⇒∣i∣%m=0 : ∀ i m .{{_ : ℕ.NonZero m}} → i %ℕ m ≡ 0 → ∣ i ∣ ℕ.% m ≡ 0
i%ℕm=0⇒∣i∣%m=0 (+ i) m i%ℕm=0 = i%ℕm=0
i%ℕm=0⇒∣i∣%m=0 (-[1+ i' ]) m i%ℕm=0 with ℕ.suc i' ℕ.% m | inspect (ℕ._% m) (ℕ.suc i')
... | ℕ.zero | [ i%m=0 ] = i%ℕm=0
... | r@(ℕ.suc r') | [ i%m=r ] = ⊥-elim (NatProperties.<-irrefl (≡-sym m∸i%m=0) m∸i%m>0)
    where
        i = ℕ.suc i'
        m∸i%m>0 : m ℕ.∸ (i ℕ.% m) ℕ.> 0
        m∸i%m>0 = NatProperties.m<n⇒0<n∸m {i ℕ.% m} {m} (m%n<n i m)

        m∸i%m=0 : m ℕ.∸ i ℕ.% m ≡ 0
        m∸i%m=0 =
            m ℕ.∸ i ℕ.% m   ≡⟨ cong (m ℕ.∸_) i%m=r ⟩
            m ℕ.∸ r         ≡⟨ i%ℕm=0 ⟩
            0               ∎
            where open ≡-Reasoning

∣i∣%m=0⇒m∣'i : ∀ i m .{{_ : ℕ.NonZero m}} → ∣ i ∣ ℕ.% m ≡ 0 → (+ m) ∣' i
∣i∣%m=0⇒m∣'i i m ∣i∣%m=0 = m%n≡0⇒n∣m ∣ i ∣ m ∣i∣%m=0

∣i∣%m=0⇒m∣i : ∀ i m .{{_ : ℕ.NonZero m}} → ∣ i ∣ ℕ.% m ≡ 0 → (+ m) ∣ i
∣i∣%m=0⇒m∣i i m ∣i∣%m=0 = ∣'⇒∣ (∣i∣%m=0⇒m∣'i i m ∣i∣%m=0)

m∣i⇒i%ℕm=0 : ∀ {i m} .{{_ : ℕ.NonZero m}} → (+ m) ∣ i → i %ℕ m ≡ 0
m∣i⇒i%ℕm=0 {+ i} {m} m∣i = m∣n⇒n%m≡0 {i} {m} (∣⇒∣' m∣i)
m∣i⇒i%ℕm=0 {(-[1+ i' ])} {m} m∣i with ℕ.suc i' ℕ.% m | inspect (ℕ._% m) (ℕ.suc i')
... | ℕ.zero | _ = ≡-refl
... | r@(ℕ.suc r') | [ i%m=r ] = ⊥-elim (sn≠0 r' (
    r                   ≡⟨ ≡-sym i%m=r ⟩
    (ℕ.suc i') ℕ.% m    ≡⟨ m∣n⇒n%m≡0 {ℕ.suc i'} {m} (∣⇒∣' m∣i) ⟩
    0                   ∎))
    where open ≡-Reasoning

-- reverse arrows --
∣i∣%m=0⇒i%ℕm=0 : ∀ i m .{{_ : ℕ.NonZero m}} → ∣ i ∣ ℕ.% m ≡ 0 → i %ℕ m ≡ 0
∣i∣%m=0⇒i%ℕm=0 i m = m∣i⇒i%ℕm=0 {i} {m} ∘ ∣i∣%m=0⇒m∣i i m

m∣i⇒∣i∣%m=0 : ∀ {i m} .{{_ : ℕ.NonZero m}} → (+ m) ∣ i → ∣ i ∣ ℕ.% m ≡ 0
m∣i⇒∣i∣%m=0 {i} {m} = i%ℕm=0⇒∣i∣%m=0 i m ∘ m∣i⇒i%ℕm=0 {i} {m}

i%ℕm=0⇒m∣i : ∀ i m .{{_ : ℕ.NonZero m}} → i %ℕ m ≡ 0 → (+ m) ∣ i
i%ℕm=0⇒m∣i i m = ∣i∣%m=0⇒m∣i i m ∘ i%ℕm=0⇒∣i∣%m=0 i m


----------------------------------
--- Divisibility by an Integer ---
----------------------------------

i∣j⇒j%i=0 : ∀ {i j} .{{_ : NonZero i}} → i ∣ j → j % i ≡ 0
i∣j⇒j%i=0 {i} {j} i∣j = m∣i⇒i%ℕm=0 {j} {∣ i ∣} (i∣j⇒abs-i∣j i∣j)

j%i=0⇒i∣j : ∀ i j .{{_ : NonZero i}} → j % i ≡ 0 → i ∣ j
j%i=0⇒i∣j i j j%i=0 = abs-i∣j⇒i∣j i (i%ℕm=0⇒m∣i j ∣ i ∣ j%i=0)

i/j*j=i : ∀ {i j} .{{_ : NonZero j}} → j ∣ i → i / j * j ≡ i
i/j*j=i {i} {j} j∣i =
    i / j * j       ≡⟨ i/j*j=i-i%j i j ⟩
    i - + (i % j)   ≡⟨ cong (λ q → i - + q) (i∣j⇒j%i=0 j∣i) ⟩
    i - 0ℤ          ≡⟨ +-identity .proj₂ i ⟩
    i               ∎
    where open ≡-Reasoning

i*[j/i]=j : ∀ {i j} .{{_ : NonZero i}} → i ∣ j → i * (j / i) ≡ j
i*[j/i]=j {i} {j} i∣j =
    i * (j / i)     ≡⟨ *-comm i (j / i) ⟩
    j / i * i       ≡⟨ i/j*j=i i∣j ⟩
    j               ∎
    where open ≡-Reasoning

i*j/j=i : ∀ i j .{{_ : NonZero j}} → i * j / j ≡ i
i*j/j=i i j = *-cancelʳ-≡ (i * j / j) i j (i/j*j=i {i * j} {j} (i∣j*i j i))

i*j/i=j : ∀ i j .{{_ : NonZero i}} → i * j / i ≡ j
i*j/i=j i j = ≡-trans (cong (_/ i) (*-comm i j)) (i*j/j=i j i)

i=j*k⇒i/j=k : ∀ i j k → .{{_ : NonZero j}} → i ≡ j * k → i / j ≡ k
i=j*k⇒i/j=k i j k i=j*k =
    i / j       ≡⟨ cong (_/ j) i=j*k ⟩
    j * k / j   ≡⟨ i*j/i=j j k ⟩
    k           ∎
    where open ≡-Reasoning

i∣j⇒j/i=quotient : ∀ (i j : ℤ) → .{{_ : NonZero i}} → ((divides quotient _) : i ∣ j) → j / i ≡ quotient
i∣j⇒j/i=quotient i j (divides k j=k*i) =
    j / i       ≡⟨ cong (_/ i) j=k*i ⟩
    k * i / i   ≡⟨ i*j/j=i k i ⟩
    k           ∎
    where open ≡-Reasoning

∣-dec : Decidable _∣_
∣-dec i j with i ≟ 0ℤ | j ≟ 0ℤ
... | yes _ |  yes ≡-refl = yes (divides 0ℤ (≡-sym (*-zero .proj₁ i)))
... | yes ≡-refl | no j≠0 = no λ 0∣j → j≠0 (0∣i⇒i=0 0∣j)
... | no i≠0 | _ with (_%_ j i {{≢-nonZero i≠0}}) ℕ.≟ 0
...     | yes j%i=0 = yes (j%i=0⇒i∣j i j j%i=0)
    where instance i-nonZero = ≢-nonZero i≠0
...     | no j%i≠0 = no (j%i≠0 ∘ i∣j⇒j%i=0)
    where instance i-nonZero = ≢-nonZero i≠0

∣-recompute : Recomputable _∣_
∣-recompute {i} {j} = recompute (∣-dec i j)
