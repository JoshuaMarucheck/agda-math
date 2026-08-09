open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; cong; refl; sym; trans; inspect; [_])
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open import Relation.Binary using (Setoid; Rel; IsEquivalence)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Function using (_∘_; id; Bijection; Injective; Surjective)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (ℕ; _≤_; _<_) renaming (zero to zeroℕ; suc to sucℕ)
open import Data.Fin using (Fin; _≟_; _≤?_; _<?_; toℕ; fromℕ<) renaming (zero to zero-fin; suc to suc-fin; _<_ to _<-fin_; _≤_ to _≤-fin_)
open import Data.Fin.Properties using (toℕ<n; fromℕ<-toℕ; toℕ-fromℕ<)

open import Plasmaduck.Data.Product using (Σ≡)
open import Plasmaduck.Data.Squash using (Squash; squash; squash-irrelevant)



-- This pattern keeps appearing, so let's just formalize it
module Plasmaduck.Data.FakeFin where

variable
    m n : ℕ
    i j k : Fin n

FakeFin : ℕ → Set
FakeFin n = Σ ℕ λ m → Squash (m < n)

realize : FakeFin n → Fin n
realize {n} (m , squash m<n) = fromℕ< m<n

falsify : Fin n → FakeFin n
falsify {n} i = toℕ i , squash (toℕ<n i)


realize-falsify : (realize ∘ falsify) i ≡ i
realize-falsify {i = i} = fromℕ<-toℕ i (toℕ<n i)

falsify-realize : ∀ {x : FakeFin n} → (falsify ∘ realize) x ≡ x
falsify-realize {x = m , squash m<n} = Σ≡ (toℕ-fromℕ< m<n) (squash-irrelevant _ _)
