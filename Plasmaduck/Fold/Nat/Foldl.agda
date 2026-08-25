open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; _≗_; cong; cong-app; inspect; [_]; ≢-sym) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open import Relation.Binary using (Setoid; Rel; IsEquivalence; IsDecTotalOrder; tri<; tri≈; tri>)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Function using (_∘_; _∋_; ∣_⟩-_; id; Bijective; Bijection; Injective; Surjective)
open import Data.Bool using (true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (ℕ; zero; suc; pred; _≟_; _≤_; _<_; _>_; z≤n; s≤s; s≤s⁻¹; _∸_; _+_; NonZero; >-nonZero)
open import Data.Nat.Properties using (module ≤-Reasoning; <-cmp; suc-pred; ≤-reflexive; ≤-refl; ≤-trans; ≤-<-trans; <-≤-trans; <-trans; ≰⇒≥; <⇒≱; ≮⇒≥; <⇒≤; ≰⇒>; ≤-antisym; <-irrefl; +-mono-≤; +-mono-<; +-mono-≤-<; ∸-mono; +-suc; +-comm; +-assoc; n>0⇒n≢0; n∸n≡0; ≤∧≢⇒<; m≤n+m; m∸n≤m; m≤m+n; m+n≤o⇒m≤o; m+n≤o⇒n≤o; m<n⇒0<n∸m; m+n∸n≡m; m+[n∸m]≡n; +-∸-assoc; ∸-monoʳ-<; m∸[m∸n]≡n; m∸n+n≡m)

open import Plasmaduck.SetoidExperiment.SetoidMachinery using (discrete-setoid)
open import Plasmaduck.Relation.Equivalence using (irrelevant-cong; irrelevant-cong₂)
open import Plasmaduck.Data.Nat using (n≤sn; n<sn; ≤→<≡; s≡s⁻¹)
open import Plasmaduck.Util.TypeChange using (change-type)



module Plasmaduck.Fold.Nat.Foldl where

variable
    c ℓ ℓ₁ : Level



-- Folds over all values less than i
foldl :
    {A : Set ℓ} →
    (combine : A → ℕ → A) →
    A → ℕ → A
foldl combine start zero = start
foldl combine start i@(suc i') = foldl combine (combine start i') i'


module _ (A-setoid : Setoid c ℓ) where
    open Setoid A-setoid using (_≈_) renaming (
        Carrier to A;
        refl to ≈-refl;
        sym to ≈-sym;
        trans to ≈-trans
        )

    foldl-substitute :
        (combine combine' : A → ℕ → A) →
        (∀ {x y : A} → x ≈ y → (i : ℕ) → combine x i ≈ combine' y i) →
        (start start' : A) →
        (start ≈ start') → 
        (i : ℕ) →
        foldl combine start i ≈ foldl combine' start' i
    foldl-substitute combine combine' c≈c' start start' s≈s' zero = s≈s'
    foldl-substitute combine combine' c≈c' start start' s≈s' (suc i) = foldl-substitute combine combine' c≈c' (combine start i) (combine' start' i) (c≈c' s≈s' i) i

foldl-combine-substitute :
    {A : Set ℓ} →
    (combine₁ combine₂ : A → ℕ → A) →
    (∀ (x : A) (i : ℕ) → combine₁ x i ≡ combine₂ x i) →
    (start : A) → (i : ℕ) →
    foldl combine₁ start i ≡ foldl combine₂ start i
foldl-combine-substitute {A = A} combine₁ combine₂ c₁≈c₂ start i = foldl-substitute (discrete-setoid A) combine₁ combine₂ (λ { {x} {.x} ≡-refl j → c₁≈c₂ x j }) start start ≡-refl i

-- If a property is preserved by combining and exists at the start, then it exists after folding.
foldl-carrying-lemma :
    {A : Set ℓ}
    (combine : A → ℕ → A) →
    (start : A)
    (i : ℕ)
    (P : A → Set ℓ₁) →
    (∀ (x : A) (i : ℕ) → P x → P (combine x i)) →
    (P start) →
    P (foldl combine start i)
foldl-carrying-lemma combine start zero P P-carries P[start] = P[start]
foldl-carrying-lemma combine start i@(suc i') P P-carries P[start] = foldl-carrying-lemma combine (combine start i') i' P P-carries (P-carries start i' P[start])

-- If a property at each index is imposed and preserved by combining, then it exists on all indices after folding.
foldl-all-lemma :
    {A : Set ℓ}
    (combine : A → ℕ → A) →
    (start : A)
    (P : A → (i : ℕ) → Set ℓ₁) →
    (∀ (x : A) (i : ℕ) → P (combine x i) i) →
    (∀ (x : A) (i : ℕ) (j : ℕ) → P x j → P (combine x i) j) →
    (i : ℕ) →
    ∀ (j : ℕ) → .(j < i) → P (foldl combine start i) j
foldl-all-lemma combine start P combine-imposes-P combine-preserves-P zero j ()
foldl-all-lemma combine start P combine-imposes-P combine-preserves-P i@(suc i') j j<i with ≤→<≡ j<i
... | inj₁ (s≤s j'<i') = foldl-all-lemma combine (combine start i') P combine-imposes-P combine-preserves-P i' j j'<i'
... | inj₂ sj=si = foldl-carrying-lemma combine (combine start i') i' (λ x → P x j) (λ x i₁ → combine-preserves-P x i₁ j) (change-type (cong (λ q → P (combine start i') q) (≡-sym (s≡s⁻¹ sj=si))) (combine-imposes-P start i'))

foldl-pop-first-lemma :
    {A : Set ℓ}
    (combine : A → ℕ → A) →
    (start : A)
    (i : ℕ) →
    foldl combine start (suc i) ≡ combine (foldl (λ acc j → combine acc (suc j)) start i) zero
foldl-pop-first-lemma combine start zero = ≡-refl
foldl-pop-first-lemma combine start (suc i) = foldl-pop-first-lemma combine (combine start (suc i)) i

-- Proof tool; slow, since it uses continuations
-- foldr' :
--     {A : Set ℓ} →
--     (combine : A → ℕ → A) →
--     A → ℕ → A
-- foldr' combine start zero = start
-- foldr' combine start i@(suc i') = combine (foldr' combine start i') i
