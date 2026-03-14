open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; inspect; cong; Reveal_·_is_; [_]; refl; sym; trans)
open import Data.Nat using (ℕ; _+_; _≤_; _≥_) renaming (zero to zero-ℕ; suc to suc-ℕ)
open import Data.Nat.Properties using (+-comm)
open import Data.Fin using (Fin; zero; suc; _↑ˡ_) renaming (_<_ to _<-fin_)
open import Relation.Binary using (Decidable)
open import Relation.Nullary.Decidable using (Dec; yes; no)

open import Plasmaduck.Util.Case using (case_of_)
open import Plasmaduck.Util.TypeChange using (change-type)


module Plasmaduck.Number.Fin where

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
