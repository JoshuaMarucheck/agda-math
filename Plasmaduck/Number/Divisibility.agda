open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; inspect; cong; Reveal_·_is_; [_]; refl; sym; trans)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open import Relation.Binary using (Rel)
open import Data.Nat using (ℕ; _+_; _∸_; _*_; _≤_; _≥_; _<_; s≤s⁻¹) renaming (zero to zero-ℕ; suc to suc-ℕ)
open import Data.Nat.Properties using (+-comm; <-≤-trans; ≤-<-trans; ≤-trans; ∸-monoˡ-<; ≤-reflexive; m+n∸m≡n; +-mono-≤)
open import Data.Fin using (Fin; zero; suc; _↑ˡ_; _↑ʳ_; splitAt; fromℕ<; join; toℕ) renaming (_<_ to _<-fin_)
open import Data.Fin.Properties using (splitAt⁻¹-↑ʳ; toℕ<n; fromℕ<-toℕ; splitAt-↑ˡ; splitAt-↑ʳ; join-splitAt; toℕ-↑ˡ; toℕ-↑ʳ)
open import Data.Product using (Σ)


module Plasmaduck.Number.Divisibility where

variable
    α β γ : Level

-- Note this is \|
_∣_ : Rel ℕ lzero
m ∣ n = Σ ℕ λ o → m * o ≡ n
