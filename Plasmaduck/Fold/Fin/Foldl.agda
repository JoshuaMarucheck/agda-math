open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; inspect; cong; Reveal_·_is_; [_]; refl; sym; trans)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Nat using (ℕ; _+_; _∸_; _≤_; _≥_; _<_; z≤n; s≤s; s≤s⁻¹) renaming (zero to zero-ℕ; suc to suc-ℕ)
open import Data.Nat.Properties using (≰⇒≥; ≤-refl; +-comm; <-≤-trans; ≤-<-trans; ≤-trans; ∸-monoˡ-<; ≤-reflexive; m+n∸m≡n; +-mono-<-≤; +-mono-≤-<; +-mono-≤)
open import Data.Fin using (Fin; zero; suc; _↑ˡ_; _↑ʳ_; splitAt; fromℕ<; join; toℕ) renaming (_<_ to _<-fin_; _≤_ to _≤-fin_)
open import Data.Fin.Properties using (_≤?_; splitAt⁻¹-↑ʳ; toℕ<n; fromℕ<-toℕ; splitAt-↑ˡ; splitAt-↑ʳ; join-splitAt; toℕ-↑ˡ; toℕ-↑ʳ)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary using (Decidable)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Function using (_∘_)

open import Plasmaduck.Util.Case using (case_of_)
open import Plasmaduck.Util.TypeChange using (change-type)
open import Plasmaduck.Data.Product using (Σ≡)
open import Plasmaduck.Data.Nat using (≤-recompute)
open import Plasmaduck.Fold.BoundedNat.Foldl using () renaming (fold to fold-ℕ; fold-carrying-theorem to fold-ℕ-carrying-theorem; fold-all-theorem to fold-ℕ-all-theorem)
open import Plasmaduck.Relation.Equivalence using (irrelevant-cong)
open import Plasmaduck.Data.PropositionalEquality using (≡-proof-unique)



module Plasmaduck.Fold.Fin.Foldl where

variable
    ℓ ℓ₁ : Level

---------------
--- Folding ---
---------------
-- A bit like induction, but up to a finite bound
-- The type changes made this more efficient to implement in Nat, so I'm porting the proofs over from there.
-- Admittedly, I'm using fromℕ< in my combine function, which makes folding over Fin n quadratic in n...


fold :
    {A : Set ℓ}
    (n : ℕ)
    (combine : A → Fin n → A) →
    A → A
fold n combine start = fold-ℕ n (λ x i i<n → combine x (fromℕ< i<n)) start

-- If a property is preserved by combining and exists at the start, then it exists after folding.
fold-carrying-theorem :
    {A : Set ℓ}
    (n : ℕ)
    (combine : A → Fin n → A) →
    (start : A)
    (P : A → Set ℓ₁) →
    (∀ (x : A) (i : Fin n) → P x → P (combine x i)) →
    (P start) →
    P (fold n combine start)
fold-carrying-theorem n combine start P P-carries P[start] = fold-ℕ-carrying-theorem n (λ x i i<n → combine x (fromℕ< i<n)) start P (λ x i i<n → P-carries x (fromℕ< i<n)) P[start]

-- If a property at each index is imposed and preserved by combining, then it exists on all indices after folding.
fold-all-theorem :
    {A : Set ℓ}
    (n : ℕ)
    (combine : A → Fin n → A) →
    (start : A)
    (P : A → Fin n → Set ℓ₁) →
    (∀ (x : A) (i : Fin n) → P (combine x i) i) →
    (∀ (x : A) (i j : Fin n) → P x j → P (combine x i) j) →
    ∀ (k : Fin n) → P (fold n combine start) k
fold-all-theorem n combine start P combine-imposes-P combine-preserves-P k =
    change-type (cong (λ q → P (fold n combine start) q) (fromℕ<-toℕ k (toℕ<n k)))
        (fold-ℕ-all-theorem n (λ x i i<n → combine x (fromℕ< i<n)) start (λ x i i<n → P x (fromℕ< i<n)) (λ x i i<n → combine-imposes-P x (fromℕ< _)) (λ x i i<n j j<n → combine-preserves-P x (fromℕ< _) (fromℕ< _)) (toℕ k) (toℕ<n k))
