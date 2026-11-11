open import Relation.Binary.PropositionalEquality using (_≢_; ≢-sym; _≡_; inspect; cong; cong₂; subst; Reveal_·_is_; [_]) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _*_; _/_; _%_; _≤_; _≥_; _<_; _>_; s≤s; z≤n; s≤s⁻¹; NonZero)
open import Data.Nat.Properties using (m+n∸n≡m; n∸n≡0; m∸n≤m; +-suc; +-comm; m≤n+m; ≤-refl; module ≤-Reasoning)
open import Agda.Builtin.Nat using ()
  renaming (div-helper to divₕ; mod-helper to modₕ)

open import Relation.Unary as U using (Pred)
open import Relation.Binary.Core
  using (_⇒_; _Preserves_⟶_; _Preserves₂_⟶_⟶_)
open import Relation.Binary.Bundles
open import Relation.Binary.Definitions
open import Relation.Binary.Consequences
  using (mono₂⇒monoˡ; mono₂⇒monoʳ; flip-Connex; wlog)
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Structures

open import Algebra.Definitions {A = ℕ} _≡_
  hiding (LeftCancellative; RightCancellative; Cancellative)
open import Algebra.Definitions
  using (LeftCancellative; RightCancellative; Cancellative)
open import Algebra.Structures {A = ℕ} _≡_



{-
    Goal: for all of those proof things in Nat that take an m ≤ n as an argument,
    usually that argument can be made irrelevant by inducting on the nat instead.
-}
module Plasmaduck.Data.Nat.IrrelevantLe where

private
    variable
        m n o p : ℕ

∸-suc : (m n : ℕ) → .(m ≥ n) → suc (m ∸ n) ≡ (suc m ∸ n)
∸-suc _ zero m≥n = ≡-refl
∸-suc zero (suc n') ()
∸-suc (suc m') (suc n') m≥n = ∸-suc m' n' (s≤s⁻¹ m≥n)

≤-antisym : .(m ≤ n) → .(n ≤ m) → m ≡ n
≤-antisym {zero} {zero} _ _       = refl
≤-antisym {suc m} {suc n} m≤n n≤m = cong suc (≤-antisym (s≤s⁻¹ m≤n) (s≤s⁻¹ n≤m))

-- I mean, it's not like it's any less efficient than what they have in the standard library...
≤-trans : .(m ≤ n) → .(n ≤ o) → m ≤ o
≤-trans {zero} {n} {o} _       _        = z≤n
≤-trans {suc m} {suc n} {suc o} m≤n n≤o = s≤s (≤-trans (s≤s⁻¹ m≤n) (s≤s⁻¹ n≤o))

<-≤-trans : .(m < n) → .(n ≤ o) → m < o
<-≤-trans m<n n≤o = ≤-trans m<n n≤o

≤-<-trans : .(m ≤ n) → .(n < o) → m < o
≤-<-trans {zero} {n} {suc o} m≤n n<o = s≤s z≤n
≤-<-trans {suc m} {suc n} {suc o} m≤n n<o = s≤s (≤-<-trans (s≤s⁻¹ m≤n) (s≤s⁻¹ n<o))

∸-mono : .(m ≤ n) → .(o ≥ p) → m ∸ o ≤ n ∸ p
∸-mono {m} {n} {o} {zero} m≤n _ = ≤-trans (m∸n≤m m o) m≤n
∸-mono {zero} {n} {zero} {suc p} _ _ = z≤n
∸-mono {zero} {n} {suc o} {suc p} _ _ = z≤n
∸-mono {suc m} {suc n} {suc o} {suc p} sm≤sn so≥sp = ∸-mono {m} {n} {o} {p} (s≤s⁻¹ sm≤sn) (s≤s⁻¹ so≥sp)

+-∸-comm : ∀ {m} n {o} → .(o ≤ m) → (m + n) ∸ o ≡ (m ∸ o) + n
+-∸-comm {zero} n {zero} _ = ≡-refl
+-∸-comm {suc m} n {zero} _ = ≡-refl
+-∸-comm {suc m} n {suc o} o≤m = +-∸-comm {m} n {o} (s≤s⁻¹ o≤m)

m∸n+n≡m : ∀ {m n} → .(n ≤ m) → (m ∸ n) + n ≡ m
m∸n+n≡m {m} {n} n≤m =
    (m ∸ n) + n ≡⟨ ≡-sym (+-∸-comm n n≤m) ⟩
    (m + n) ∸ n ≡⟨ m+n∸n≡m m n ⟩
    m           ∎
    where open ≡-Reasoning

m≤n⇒m∸n≡0 : ∀ {m n} → .(m ≤ n) → m ∸ n ≡ 0
m≤n⇒m∸n≡0 {zero} {zero} _ = ≡-refl
m≤n⇒m∸n≡0 {zero} {suc n} _ = ≡-refl
m≤n⇒m∸n≡0 {suc m} {suc n} m≤n = m≤n⇒m∸n≡0 {m} {n} (s≤s⁻¹ m≤n)

m<n⇒0<n∸m : .(m < n) → 0 < n ∸ m
m<n⇒0<n∸m {zero}  {suc n} _         = s≤s z≤n
m<n⇒0<n∸m {suc m} {suc n} m<n = m<n⇒0<n∸m (s≤s⁻¹ m<n)

+-∸-assoc : ∀ m {n o} → .(o ≤ n) → (m + n) ∸ o ≡ m + (n ∸ o)
+-∸-assoc m {n} {zero} o≤n = ≡-refl
+-∸-assoc m {suc n} {suc o} o≤n =
  (m + suc n) ∸ suc o  ≡⟨ cong (_∸ suc o) (+-suc m n) ⟩
  suc (m + n) ∸ suc o  ≡⟨⟩
  (m + n) ∸ o          ≡⟨ +-∸-assoc m (s≤s⁻¹ o≤n) ⟩
  m + (n ∸ o)          ∎
  where open ≡-Reasoning

divₕ-finish : ∀ {acc} d n j → .(j ≥ n) → divₕ acc d n j ≡ acc
divₕ-finish d zero    j       j≥n = ≡-refl
divₕ-finish d (suc n) (suc j) j≥n = divₕ-finish d n j (s≤s⁻¹ j≥n)

-- m<n⇒m%n≡m : .{{_ : NonZero n}} → .(m < n) → m % n ≡ m
-- m<n⇒m%n≡m {n = suc _} m<n = {! m≤n⇒m%n≡m  !} -- m≤n⇒m%n≡m (<⇒≤pred m<n)

m<n⇒m/n≡0 : ∀ {m n} .{{_ : NonZero n}} → .(m < n) → m / n ≡ 0
m<n⇒m/n≡0 {m} {suc n-1} m<n = divₕ-finish n-1 m n-1 (s≤s⁻¹ m<n)

-- m<n*o⇒m/o<n : ∀ {m n o} .{{_ : NonZero o}} → m < n * o → m / o < n
-- m<n*o⇒m/o<n {m} {suc n} {o} m<o = begin
--   {!   !} ≤⟨ {!   !} ⟩
--   {!   !} ∎
--   where open ≤-Reasoning

m+[n∸m]≡n : ∀ {m n} → .(m ≤ n) → m + (n ∸ m) ≡ n
m+[n∸m]≡n {zero} {zero} m≤n = ≡-refl
m+[n∸m]≡n {zero} {suc n} m≤n = ≡-refl
m+[n∸m]≡n {suc m} {suc n} m≤n = cong suc (m+[n∸m]≡n (s≤s⁻¹ m≤n))

m∸[m∸n]≡n : ∀ {m n} → .(n ≤ m) → m ∸ (m ∸ n) ≡ n
m∸[m∸n]≡n {zero} {zero} m≤n = ≡-refl
m∸[m∸n]≡n {suc m} {zero} m≤n = n∸n≡0 m
m∸[m∸n]≡n {suc m} {suc n} m≤n = ≡-trans (≡-sym (∸-suc m (m ∸ n) (m∸n≤m m n))) (cong suc (m∸[m∸n]≡n {m} {n} (s≤s⁻¹ m≤n)))

+-mono-≤ : ∀ {m n o p} → .(m ≤ n) → .(o ≤ p) → m + o ≤ n + p
+-mono-≤ {zero} {n} m≤n o≤p = ≤-trans o≤p (m≤n+m _ n)
+-mono-≤ {suc m} {suc n} m≤n o≤p = s≤s (+-mono-≤ (s≤s⁻¹ m≤n) o≤p)

*-mono-≤ : ∀ {m n o p} → .(m ≤ n) → .(o ≤ p) → m * o ≤ n * p
*-mono-≤ {zero} _ _ = z≤n
*-mono-≤ {suc m} {suc n} m≤n u≤v = +-mono-≤ u≤v (*-mono-≤ (s≤s⁻¹ m≤n) u≤v)

*-monoˡ-≤ : ∀ n {x} {y} → .(x ≤ y) → x * n ≤ y * n
*-monoˡ-≤ n {x} {y} x≤y = *-mono-≤ {x} {y} {n} {n} x≤y ≤-refl

*-monoʳ-≤ : ∀ n {x} {y} → .(x ≤ y) → n * x ≤ n * y
*-monoʳ-≤ n {x} {y} x≤y = *-mono-≤ {n} {n} {x} {y} ≤-refl x≤y

-- /-mono-≤ : .{{_ : NonZero o}} .{{_ : NonZero p}} →
--            m ≤ n → o ≥ p → m / o ≤ n / p
-- /-mono-≤ m≤n (s≤s o≥p) = divₕ-mono-≤ 0 m≤n o≥p

-- /-monoˡ-≤ : ∀ o .{{_ : NonZero o}} → m ≤ n → m / o ≤ n / o
-- /-monoˡ-≤ o m≤n = /-mono-≤ m≤n (≤-refl {o})

-- /-monoʳ-≤ : ∀ m {n o} .{{_ : NonZero n}} .{{_ : NonZero o}} →
--             n ≥ o → m / n ≤ m / o
-- /-monoʳ-≤ m n≥o = /-mono-≤ ≤-refl n≥o

-- /-cancelʳ-≡ : ∀ {m n o} .{{_ : NonZero o}} →
--               o ∣ m → o ∣ n → m / o ≡ n / o → m ≡ n
-- /-cancelʳ-≡ {m} {n} {o} o∣m o∣n m/o≡n/o = begin-equality
--   m           ≡⟨ m*[n/m]≡n {o} {m} o∣m ⟨
--   o * (m / o) ≡⟨ cong (o *_) m/o≡n/o ⟩
--   o * (n / o) ≡⟨ m*[n/m]≡n {o} {n} o∣n ⟩
--   n           ∎

-- m<n⇒m/n≡0 : ∀ {m n} .{{_ : NonZero n}} → m < n → m / n ≡ 0
-- m<n⇒m/n≡0 {m} {suc n-1} (s≤s m≤n) = divₕ-finish n-1 m n-1 m≤n

-- m≥n⇒m/n>0 : ∀ {m n} .{{_ : NonZero n}} → m ≥ n → m / n > 0
-- m≥n⇒m/n>0 {m@(suc _)} {n@(suc _)} m≥n = begin
--   1     ≡⟨ n/n≡1 m ⟨
--   m / m ≤⟨ /-monoʳ-≤ m m≥n ⟩
--   m / n ∎

-- m≤n⇒m≤1+n : m ≤ n → m ≤ 1 + n

-- n≤0⇒n≡0 : n ≤ 0 → n ≡ 0


-- <⇒≤ : _<_ ⇒ _≤_
-- <⇒≤ z<s               = z≤n
-- <⇒≤ (s<s m<n@(s≤s _)) = s≤s (<⇒≤ m<n)

-- <⇒≢ : _<_ ⇒ _≢_
-- <⇒≢ m<n refl = 1+n≰n m<n

-- >⇒≢ : _>_ ⇒ _≢_
-- >⇒≢ = ≢-sym ∘ <⇒≢

-- ≤⇒≯ : _≤_ ⇒ _≯_

-- <⇒≱ : _<_ ⇒ _≱_

-- <⇒≯ : _<_ ⇒ _≯_

-- ≰⇒≮ : _≰_ ⇒ _≮_

-- ≰⇒> : _≰_ ⇒ _>_

-- ≮⇒≥ : _≮_ ⇒ _≥_

-- ≤∧≢⇒< : ∀ {m n} → m ≤ n → m ≢ n → m < n

-- ≤∧≮⇒≡ : ∀ {m n} → m ≤ n → m ≮ n → m ≡ n

-- ≤-<-connex : Connex _≤_ _<_
-- ≤-<-connex m n with m ≤? n
-- ... | yes m≤n = inj₁ m≤n
-- ... | no ¬m≤n = inj₂ (≰⇒> ¬m≤n)

-- ≥->-connex : Connex _≥_ _>_
-- ≥->-connex = flip ≤-<-connex

-- <-≤-connex : Connex _<_ _≤_
-- <-≤-connex = flip-Connex ≤-<-connex

-- >-≥-connex : Connex _>_ _≥_
-- >-≥-connex = flip-Connex ≥->-connex



-- n<1⇒n≡0 : n < 1 → n ≡ 0

-- n>0⇒n≢0 : n > 0 → n ≢ 0
