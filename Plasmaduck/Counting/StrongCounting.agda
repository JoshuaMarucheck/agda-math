open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; inspect; cong; Reveal_·_is_; [_]) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open import Function using (_∘_; flip; Bijective; Injective; Surjective; Bijection; Injection; Surjection; Congruent)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary using (Rel; Decidable; IsEquivalence; tri<; tri≈; tri>)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; _+_; _*_; _≤_; _≥_; _<_; z≤n; s≤s; s≤s⁻¹) renaming (zero to zero-ℕ; suc to suc-ℕ)
open import Data.Nat.Properties using (≤-reflexive; <-trans; ≤-trans; ≤-<-trans; <-cmp)
open import Data.Fin using (Fin; zero; suc; _↑ˡ_; _↑ʳ_; splitAt; join; combine; toℕ; fromℕ<)
open import Data.Fin.Properties using (join-splitAt; splitAt-↑ˡ; splitAt-↑ʳ; combine-injective; combine-surjective; toℕ-fromℕ<; fromℕ<-toℕ; fromℕ<-cong; toℕ<n)

open import Plasmaduck.SetoidExperiment.SetoidMachinery using (discrete-setoid; from-discrete-cong; ⊎-setoid; ×-setoid; maybe-setoid; rel₁; rel₂; property-subset-setoid; SetoidFunction; _which-is-cong_)
open import Plasmaduck.Function.Bijection using (invert-bijection; _∘-bijection_; ⊎-bijection; ×-bijection; ⊎-discrete-distributivity; ⊎-property-split-bijection; ×-discrete-distributivity)
open import Plasmaduck.Function.InjectionSurjection using (bijection→surjection)
open import Plasmaduck.Relation.Defs using (CongruentRel; CongruentProperty; rel-property)
open import Plasmaduck.Property.Defs using (DecidableProperty)
open import Plasmaduck.Data.Nat using (n<sn; n≤sn; ≤→<≡; s≡s⁻¹; n≤n)
open import Plasmaduck.Util.Case using (case_of_)
open import Plasmaduck.Util.Negation using (¬¬-lift)
open import Plasmaduck.Counting.Counting using (fin-setoid; HasSize; fin-⊎-bijection; IsFinite)
open import Plasmaduck.Counting.Pigeonhole using (pigeonhole-principle-fin)


{-
    This module is for counting results that rely on the pigeonhole principle, but that aren't the pigeonhole principle.
-}

module Plasmaduck.Counting.StrongCounting where

variable
    a ℓ ℓ₁ : Level


module _
    {m n : ℕ} (m-n-surjection : Surjection (fin-setoid m) (fin-setoid n))
    where

    private
        to = m-n-surjection .Surjection.to
        inv = proj₁ ∘ m-n-surjection .Surjection.surjective

        open ≡-Reasoning

    surj→¬m<n : ¬ m < n
    surj→¬m<n m<n with pigeonhole-principle-fin m<n inv
    ... | i , j , i≢j , inv-i≡inv-j = i≢j (
        i           ≡⟨ ≡-sym (m-n-surjection .Surjection.surjective i .proj₂ ≡-refl) ⟩
        to (inv i)  ≡⟨ cong to inv-i≡inv-j ⟩
        to (inv j)  ≡⟨ m-n-surjection .Surjection.surjective j .proj₂ ≡-refl ⟩
        j           ∎
        )

bijection-maintains-size : {m n : ℕ} (m-n-bijection : Bijection (fin-setoid m) (fin-setoid n)) → m ≡ n
bijection-maintains-size {m = m} {n} m-n-bijection with <-cmp m n
... | tri< m<n _ _ = ⊥-elim (surj→¬m<n (bijection→surjection m-n-bijection) m<n)
... | tri≈ _ m≡n _ = m≡n
... | tri> _ _ m>n = ⊥-elim (surj→¬m<n (bijection→surjection (invert-bijection m-n-bijection)) m>n)


⊎-property-split-size-theorem :
    {A-setoid : Setoid a ℓ} → (P : A-setoid .Setoid.Carrier → Set ℓ₁) →
    (P-cong : CongruentProperty A-setoid P)
    (P-dec : DecidableProperty P)
    {m n o : ℕ} →
    HasSize A-setoid m →
    HasSize (property-subset-setoid A-setoid P) n →
    HasSize (property-subset-setoid A-setoid (¬_ ∘ P)) o →
    m ≡ n + o
⊎-property-split-size-theorem {A-setoid = A-setoid} P P-cong P-dec {m} {n} {o} A-size-m A-with-P-size-n A-without-P-size-o = bijection-maintains-size final-bijection
    where
        split-bijection : Bijection A-setoid (⊎-setoid (property-subset-setoid A-setoid P) (property-subset-setoid A-setoid (¬_ ∘ P)))
        split-bijection = ⊎-property-split-bijection A-setoid P P-cong P-dec

        fin-bijection : Bijection (fin-setoid m) (⊎-setoid (fin-setoid n) (fin-setoid o))
        fin-bijection = ⊎-bijection (invert-bijection A-with-P-size-n) (invert-bijection A-without-P-size-o) ∘-bijection split-bijection ∘-bijection A-size-m

        final-bijection : Bijection (fin-setoid m) (fin-setoid (n + o))
        final-bijection = invert-bijection (fin-⊎-bijection n o) ∘-bijection invert-bijection (⊎-discrete-distributivity (Fin n) (Fin o)) ∘-bijection fin-bijection
