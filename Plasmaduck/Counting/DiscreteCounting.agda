open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; inspect; cong; Reveal_·_is_; [_]) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open import Function using (_∘_; flip; Bijective; Injective; Surjective; Bijection; Injection; Surjection; Congruent)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary using (Rel; Decidable; IsEquivalence)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; _+_; _*_; _∸_; _≤_; _≥_; _<_; z≤n; s≤s; s≤s⁻¹) renaming (zero to zero-ℕ; suc to suc-ℕ)
open import Data.Nat.Properties using (≤-reflexive; <-trans; ≤-trans; ≤-<-trans; _<?_; m+[n∸m]≡n)
open import Data.Fin using (Fin; zero; suc; _↑ˡ_; _↑ʳ_; splitAt; join; combine; toℕ; fromℕ<)
open import Data.Fin.Properties using (join-splitAt; splitAt-↑ˡ; splitAt-↑ʳ; toℕ-↑ˡ; combine-injective; combine-surjective; toℕ-fromℕ<; fromℕ<-toℕ; fromℕ<-cong; toℕ<n)

open import Plasmaduck.SetoidExperiment.SetoidMachinery using (discrete-setoid; from-discrete-cong; ⊎-setoid; ×-setoid; maybe-setoid; rel₁; rel₂; property-subset-setoid)
open import Plasmaduck.Function.Bijection using (invert-bijection; _∘-bijection_; ⊎-bijection; ×-bijection; ⊎-discrete-distributivity; ×-discrete-distributivity)
open import Plasmaduck.Function.InjectionSurjection using (bijection→surjection; _∘-surjection_)
open import Plasmaduck.Relation.Defs using (CongruentRel; CongruentProperty; rel-property)
open import Plasmaduck.Property.Defs using (DecidableProperty; any-type; all-type)
open import Plasmaduck.Data.Nat using (n<sn; n≤sn; ≤→<≡; s≡s⁻¹; n≤n)
open import Plasmaduck.Util.Case using (case_of_)
open import Plasmaduck.Util.Negation using (¬¬-lift)
open import Plasmaduck.Util.TypeChange using (change-type; change-type-input-dependence-irrelevance)
open import Plasmaduck.Function.Surjectionish using (Surjectionish; _∘-surjectionish_)
open import Plasmaduck.Counting.Counting using (fin-setoid) renaming (HasSize to SetoidHasSize)


-- Copying some definitions over from Plasmaduck/Counting/Counting.agda, but assuming all setoids are discrete setoids.
module Plasmaduck.Counting.DiscreteCounting where


variable
    a b c d ℓ ℓ₁ ℓ₂ : Level

HasSize : (A : Set a) (n : ℕ) → Set a
HasSize A n = Bijection (fin-setoid n) (discrete-setoid A)

open Setoid using (Carrier; _≈_)

AtLeastSize : (A : Set a) (n : ℕ) → Set a
AtLeastSize A n = Injection (fin-setoid n) (discrete-setoid A)

-- Defined like this since if the target set is empty, no surjection exists since no functions exist. oops.
-- Of course, such a definition means the target set is decidable.
AtMostSize : (A : Set a) (n : ℕ) → Set a
AtMostSize A n = Surjectionish (fin-setoid n) (discrete-setoid A)

IsWeaklyFinite : (A : Set a) → Set a
IsWeaklyFinite A = Σ ℕ λ n → AtMostSize A n

IsFinite : (A : Set a) → Set a
IsFinite A = Σ ℕ λ n → HasSize A n


SubsetHasSize : {A : Set a} → (A → Set ℓ₂) → ℕ → Set (a ⊔ ℓ₂)
SubsetHasSize {A = A} P n = SetoidHasSize (property-subset-setoid (discrete-setoid A) P) n
