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
open import Data.List using (List; foldl; _∷_; []; _∷ʳ_; length; lookup; drop; _++_; reverse; tabulate; map; concat)
open import Data.List.Properties using (drop-drop; reverse-++; ++-identity; foldl-map; foldl-∷ʳ; foldl-cong; map-++; concat-map; map-∘; reverse-map; map-cong; reverse-involutive)
open import Data.List.Relation.Unary.All using (All)

open import Plasmaduck.Relation.Equivalence using (irrelevant-cong; irrelevant-cong₂)
open import Plasmaduck.Data.Nat using (n≤sn; n<sn; ≤→<≡)
open import Plasmaduck.Util.TypeChange using (change-type)



module Plasmaduck.Fold.BoundedNat.Foldl where

variable
    ℓ ℓ₁ : Level


---------------
--- Folding ---
---------------
-- A bit like induction, but up to a finite bound

module _ where
    module Foldl' where
        foldl' :
            {A : Set ℓ} →
            (n : ℕ) →
            (combine : A → (i : ℕ) → .(i < n) → A) →
            A → (i : ℕ) → .(i < n) → A
        foldl' n combine start zero i<n = combine start zero i<n
        foldl' n combine start i@(suc i') i<n = foldl' n combine (combine start i i<n) i' (≤-trans n≤sn i<n)

        foldl'-combine-substitute :
            {A : Set ℓ} →
            (n : ℕ) →
            (combine₁ : A → (i : ℕ) → .(i < n) → A) →
            (combine₂ : A → (i : ℕ) → .(i < n) → A) →
            (∀ (x : A) (i : ℕ) .(i<n : i < n) → combine₁ x i i<n ≡ combine₂ x i i<n) →
            (start : A) → (i : ℕ) → .(i<n : i < n) →
            foldl' n combine₁ start i i<n ≡ foldl' n combine₂ start i i<n
        foldl'-combine-substitute n combine₁ combine₂ c₁≈c₂ start zero i<n = c₁≈c₂ start zero _
        foldl'-combine-substitute n combine₁ combine₂ c₁≈c₂ start (suc i) si<n =
            foldl' n combine₁ start (suc i) si<n                                    ≡⟨⟩
            foldl' n combine₁ (combine₁ start (suc i) si<n) i (≤-trans n≤sn si<n)   ≡⟨ foldl'-combine-substitute n combine₁ combine₂ c₁≈c₂ (combine₁ start (suc i) si<n) i (≤-trans n≤sn si<n) ⟩
            foldl' n combine₂ (combine₁ start (suc i) si<n) i (≤-trans n≤sn si<n)   ≡⟨ cong (λ q → foldl' n combine₂ q i (≤-trans n≤sn si<n)) (c₁≈c₂ start (suc i) si<n) ⟩
            foldl' n combine₂ (combine₂ start (suc i) si<n) i (≤-trans n≤sn si<n)   ≡⟨⟩
            foldl' n combine₂ start (suc i) si<n                                    ∎
            where open ≡-Reasoning

        foldl'-carrying-lemma :
            {A : Set ℓ}
            (n : ℕ)
            (combine : A → (i : ℕ) → .(i < n) → A) →
            (start : A)
            (i : ℕ)
            .(i<n : i < n)
            (P : A → Set ℓ₁) →
            (∀ (x : A) (i : ℕ) .(i<n : i < n) → P x → P (combine x i i<n)) →
            (P start) →
            P (foldl' n combine start i i<n)
        foldl'-carrying-lemma n combine start zero i<n P P-carries P[start] = P-carries start zero i<n P[start]
        foldl'-carrying-lemma n combine start i@(suc i') i<n P P-carries P[start] = foldl'-carrying-lemma n combine (combine start i i<n) i' (≤-trans n≤sn i<n) P P-carries (P-carries start (suc i') i<n P[start])

        foldl'-all-lemma :
            {A : Set ℓ}
            (n : ℕ)
            (combine : A → (i : ℕ) → .(i < n) → A) →
            (start : A)
            (P : A → (i : ℕ) → .(i < n) → Set ℓ₁) →
            (∀ (x : A) (i : ℕ) .(i<n : i < n) → P (combine x i i<n) i i<n) →
            (∀ (x : A) (i : ℕ) .(i<n : i < n) (j : ℕ) .(j<n : j < n) → P x j j<n → P (combine x i i<n) j j<n) →
            (i : ℕ) → .(i<n : i < n) →
            ∀ (j : ℕ) .(j≤i : j ≤ i) → P (foldl' n combine start i i<n) j (≤-<-trans j≤i i<n)
        foldl'-all-lemma zero combine start P combine-imposes-P combine-preserves-P zero () j j≤i
        foldl'-all-lemma zero combine start P combine-imposes-P combine-preserves-P i@(suc i') () j j≤i
        foldl'-all-lemma n@(suc n') combine start P combine-imposes-P combine-preserves-P zero _ zero _ = (combine-imposes-P start zero (s≤s z≤n))
        foldl'-all-lemma n@(suc n') combine start P combine-imposes-P combine-preserves-P zero _ j@(suc j') ()
        foldl'-all-lemma n@(suc n') combine start P combine-imposes-P combine-preserves-P i@(suc i') i<n j j≤i with ≤→<≡ j≤i
        ... | inj₂ j≡i =
                (foldl'-carrying-lemma n combine (combine start i i<n) i' (≤-trans n≤sn i<n)
                    (λ x → P x j (≤-<-trans j≤i i<n))
                    (λ x i₁ i<n₁ → combine-preserves-P x i₁ i<n₁ j (≤-<-trans j≤i i<n))
                    (change-type (irrelevant-cong (λ q → q < n) (λ p q → P (combine start i i<n) p q) (≡-sym j≡i))
                        (combine-imposes-P start i i<n)
                    )
                )
        ... | inj₁ (s≤s j'<i') =
                (foldl'-all-lemma n combine (combine start i i<n) P combine-imposes-P combine-preserves-P i' (≤-trans n≤sn i<n) j j'<i')

        foldl'-clip-lemma :
            {A : Set ℓ}
            (n : ℕ)
            (combine : A → (i : ℕ) → .(i < n) → A) →
            (start : A)
            (i : ℕ)
            .(i<n : i < n) →
            foldl' n combine start i i<n ≡ foldl' (suc i) (λ acc j j<si → combine acc j (<-≤-trans j<si i<n)) start i n<sn
        foldl'-clip-lemma (suc n) combine start zero _ = ≡-refl
        foldl'-clip-lemma (suc n) combine start (suc i) si<sn =
            foldl' (suc n) combine start (suc i) _                                                                              ≡⟨⟩
            foldl' (suc n) combine (combine start (suc i) si<sn) i (≤-<-trans n≤sn si<sn)                                       ≡⟨ foldl'-clip-lemma (suc n) combine (combine start (suc i) si<sn) i (≤-<-trans n≤sn si<sn) ⟩
            foldl' (suc i) (λ acc j .j<si → combine acc j (<-trans j<si si<sn)) (combine start (suc i) si<sn) i n<sn            ≡⟨ ≡-sym (foldl'-clip-lemma (suc (suc i)) (λ acc j .j<ssi → combine acc j (<-≤-trans j<ssi si<sn)) (combine start (suc i) si<sn) i n≤sn) ⟩
            foldl' (suc (suc i)) (λ acc j .j<ssi → combine acc j (<-≤-trans j<ssi si<sn)) (combine start (suc i) si<sn) i n≤sn  ≡⟨⟩
            foldl' (suc (suc i)) (λ acc j .j<ssi → combine acc j _) start (suc i) n<sn                                          ∎
            where open ≡-Reasoning

        foldl'-pop-first :
            {A : Set ℓ}
            (n : ℕ)
            (combine : A → (i : ℕ) → .(i < suc n) → A) →
            (start : A)
            (i : ℕ)
            .(si<sn : suc i < suc n) →
            foldl' (suc n) combine start (suc i) si<sn ≡ combine (foldl' n (λ acc j j<n → combine acc (suc j) (s≤s j<n)) start i (s≤s⁻¹ si<sn)) zero (s≤s z≤n)
        foldl'-pop-first n combine start zero si<sn = ≡-refl
        foldl'-pop-first n combine start (suc i) si<sn = foldl'-pop-first n combine (combine start (suc (suc i)) si<sn) i (≤-trans n≤sn si<sn)

        -- Proof tool; slow, since it uses continuations
        -- foldr' :
        --     {A : Set ℓ} →
        --     (n : ℕ) →
        --     (combine : A → (i : ℕ) → .(i < n) → A) →
        --     A → (i : ℕ) → .(i < n) → A
        -- foldr' n combine start zero i<n = combine start zero i<n
        -- foldr' n combine start i@(suc i') i<n = combine (foldr' n combine start i' (≤-trans n≤sn i<n)) i i<n
    open Foldl'

    -- Folds over all values less than n
    fold :
        {A : Set ℓ}
        (n : ℕ)
        (combine : A → (i : ℕ) → .(i < n) → A) →
        A → A
    fold zero combine start = start
    fold n@(suc n') combine start = foldl' n combine start n' n<sn

    -- If a property is preserved by combining and exists at the start, then it exists after folding.
    fold-carrying-theorem :
        {A : Set ℓ}
        (n : ℕ)
        (combine : A → (i : ℕ) → .(i < n) → A) →
        (start : A)
        (P : A → Set ℓ₁) →
        (∀ (x : A) (i : ℕ) .(i<n : i < n) → P x → P (combine x i i<n)) →
        (P start) →
        P (fold n combine start)
    fold-carrying-theorem zero combine start P P-carries P[start] = P[start]
    fold-carrying-theorem n@(suc n') combine start P P-carries P[start] = foldl'-carrying-lemma n combine start n' n<sn P P-carries P[start]

    -- If a property at each index is imposed and preserved by combining, then it exists on all indices after folding.
    fold-all-theorem :
        {A : Set ℓ}
        (n : ℕ)
        (combine : A → (i : ℕ) → .(i < n) → A) →
        (start : A)
        (P : A → (i : ℕ) → .(i < n) → Set ℓ₁) →
        (∀ (x : A) (i : ℕ) .(i<n : i < n) → P (combine x i i<n) i i<n) →
        (∀ (x : A) (i : ℕ) .(i<n : i < n) (j : ℕ) .(j<n : j < n) → P x j j<n → P (combine x i i<n) j j<n) →
        ∀ (i : ℕ) .(i<n : i < n) → P (fold n combine start) i i<n
    fold-all-theorem n@(suc n') combine start P combine-imposes-P combine-preserves-P i i<n =
        foldl'-all-lemma n combine start P combine-imposes-P combine-preserves-P n' n<sn i (s≤s⁻¹ i<n)

    fold-consume-last-lemma :
        {A : Set ℓ}
        (n : ℕ)
        (combine : A → (i : ℕ) → .(i < suc n) → A) →
        (start : A) →
        fold (suc n) combine start ≡ fold n (λ acc i i<n → combine acc i (≤-trans i<n n≤sn)) (combine start n n<sn)
    fold-consume-last-lemma zero combine start = ≡-refl
    fold-consume-last-lemma (suc n) combine start =
        foldl'-clip-lemma (suc (suc n)) combine (combine start (suc n) n<sn) n (≤-trans n≤sn n<sn)

    fold-pop-first-lemma :
        {A : Set ℓ}
        (n : ℕ)
        (combine : A → (i : ℕ) → .(i < suc n) → A) →
        (start : A) →
        fold (suc n) combine start ≡ combine (fold n (λ acc i i<n → combine acc (suc i) (s≤s i<n)) start) zero (s≤s z≤n)
    fold-pop-first-lemma zero combine start = ≡-refl
    fold-pop-first-lemma (suc n) combine start = foldl'-pop-first (suc n) combine start n n<sn
