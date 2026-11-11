open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≢_; _≡_; _≗_; inspect; cong; cong₂; Reveal_·_is_; [_]; ≢-sym) renaming (subst to ≡-subst; refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open import Relation.Binary using (Setoid; Rel; IsEquivalence; IsDecTotalOrder; tri<; tri≈; tri>)
import Relation.Unary as Unary
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Function using (_∘_; _∋_; Bijective; Bijection; Injective; Surjective)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc; _≟_; _≤_; _<_; _>_; _<?_; z≤n; s≤s; s≤s⁻¹; _∸_; _+_; _*_; NonZero; >-nonZero)
open import Data.Nat.DivMod using (_%_; _/_; [m+kn]%n≡m%n; m<n⇒m%n≡m)
open import Data.Nat.Properties using (module ≤-Reasoning; <-cmp; suc-pred; ≤-reflexive; ≤-refl; ≤-trans; ≤-<-trans; <-≤-trans; <-trans; ≰⇒≥; <⇒≱; ≮⇒≥; <⇒≤; <⇒≢; ≤∧≢⇒<; ≤-antisym; <-irrefl; +-mono-≤; +-mono-<; ∸-mono; +-suc; +-comm; +-assoc; m≤n+m; m∸n≤m; m≤m+n; m+n≤o⇒m≤o; m+n≤o⇒n≤o; m+n∸n≡m; m+[n∸m]≡n; +-∸-assoc; ∸-monoʳ-<; m∸[m∸n]≡n; ∸-cancelʳ-<)
open import Data.List using (List; []; _∷_; _∷ʳ_; length)
open import Data.List.Relation.Unary.All as All using (All)

open import Plasmaduck.SetoidExperiment.SetoidMachinery using (discrete-setoid; from-discrete-cong; SetoidFunction₂; _which-is-cong₂_; _←₂_; SetoidFunction; _which-is-cong_; _←_; property-subset-setoid)
open import Plasmaduck.Function.Properties using (module SingleOperator; assoc-middle; exchange-middle)
open import Plasmaduck.Util.Case using (case_of_)
open import Plasmaduck.Data.FakeFin using (FakeFin; realize; falsify; realize-bijection; falsify-bijection; falsify-realize; realize-falsify)
open import Plasmaduck.Data.Squash using (Squash; squash; squash-irrelevant)
open import Plasmaduck.Data.Empty using (⊥-irr-elim)
open import Plasmaduck.Data.Nat using (≤-recompute; n≤n; n≤sn; n<sn; ∸-cancelˡ-<; ≤→<≡; ∸-suc; m∸n+n≡m; m∸n∸o≡m∸[n+o]; s≡s⁻¹; [m*n+i]/n=i)
open import Plasmaduck.Fold.Nat.Foldl using (foldl; foldl-pop-first-lemma; foldl-carrying-lemma; foldl-local-carrying-lemma; foldl-all-lemma)
open import Plasmaduck.Data.List using (drop-lookup; All-concat; liat; unsnoc; liat∷ʳunsnoc; All-liat; All-get-unsnoc; length-liat)
open import Plasmaduck.Data.Product using (Σ≡; ×≡; proj₁≡; uncurry; curry)
open import Plasmaduck.Util.TypeChange using (change-type-input-dependence-irrelevance)
open import Plasmaduck.Relation.Equivalence using (irrelevant-cong; irrelevant-cong₂)
open import Plasmaduck.Function.Bijection using (_∘-bijective_; id-bijective; bijective-is-functional; _∘-bijection_; module InverseFunction)
open import Plasmaduck.Function.Properties using (DistributiveFunction; Associative; Commutative; LeftIdentity; Identity; Congruent₂)

open import Plasmaduck.SetoidExperiment.SetoidMachinery using (SetoidFunction₂; _which-is-cong₂_; SetoidFunction; _which-is-cong_; maybe-setoid; maybe-rel-just; maybe-rel-nothing)
open import Plasmaduck.Counting.Permutation.FlipPermutation using (decompose-permutation; is-permutation-decomposition; decompose-permutation-valid)
open import Plasmaduck.Counting.Permutation.FlipList using (flip; FlipList; IsValidFlipList; flip-swap-using-list; flip-swap-using-list-pop-last)
open import Plasmaduck.Counting.Permutation.Defs using (IsNFuncLower; IsNFuncUpper; IsNFunc; IsNFuncPermutation; swp; swp-helper)
open import Plasmaduck.Counting.Permutation.Swap using (swp-no-match⇒id)



{-
    combining finite sets using commutative associative binary operators.
-}
module Plasmaduck.Fold.Nat.Merge where

variable
    ℓ ℓ₁ b c α β : Level


{-
    Fold, as in Nat/Foldl.agda, but for binary operators.
        That is, when combine can be split into two functions _∙_ and generate
        such that combine acc i = generate i ∙ acc
    This makes proofs about associativity and commutativity more apparent.
    Since fold goes from high indices to low indices, the accumulator adds elements on the left.
    That means the resulting expression is right-associative.
-}
private
    make-combine :
        {A : Set ℓ}
        (_∙_ : A → A → A) →
        (generate : ℕ → A) →
        (start : A) →
        (i : ℕ) → A
    make-combine _∙_ generate acc i = generate i ∙ acc

-- Merges over all values less than i
merge :
    {A : Set ℓ}
    (_∙_ : A → A → A) →
    (start : A) → -- should probably be identity for _∙_
    (generate : ℕ → A) →
    (i : ℕ) →
    A
merge _∙_ start generate i = foldl (make-combine _∙_ generate) start i

merge-pop-first :
    {A : Set ℓ}
    (_∙_ : A → A → A)
    (start : A)
    (generate : ℕ → A) →
    (i : ℕ) →
    merge _∙_ start generate (suc i) ≡ generate zero ∙ merge _∙_ start (generate ∘ suc) i
merge-pop-first _∙_ start generate i = foldl-pop-first-lemma (make-combine _∙_ generate) start i

module MergeSubstitute
    (A-setoid : Setoid c ℓ)
    where
    open Setoid A-setoid using (_≈_; refl; sym; trans; reflexive) renaming (Carrier to A)

    merge-substitute :
        (_∙_ : A → A → A)
        (_∙'_ : A → A → A) →
        (∀ {x₁ x₂ y₁ y₂ : A} → (x₁ ≈ x₂) → y₁ ≈ y₂ → x₁ ∙ y₁ ≈ x₂ ∙' y₂) →
        (start : A)
        (start' : A) →
        (start ≈ start') →
        (generate : ℕ → A) →
        (generate' : ℕ → A) →
        (∀ i → generate i ≈ generate' i) →
        (i : ℕ) →
        merge _∙_ start generate i ≈
        merge _∙'_ start' generate' i
    merge-substitute _∙_ _∙'_ ∙-sim start start' start-sim generate generate' generate-sim zero = start-sim
    merge-substitute _∙_ _∙'_ ∙-sim start start' start-sim generate generate' generate-sim i@(suc zero) = ∙-sim (generate-sim zero) start-sim
    merge-substitute _∙_ _∙'_ ∙-sim start start' start-sim generate generate' generate-sim i@(suc i'@(suc i'')) =
        merge-substitute _∙_ _∙'_ ∙-sim  (generate i' ∙ start) (generate' i' ∙' start') (∙-sim (generate-sim i') start-sim) generate generate' generate-sim i'

    merge-substitute-op :
        (_∙_ : A → A → A)
        (_∙'_ : A → A → A) →
        (∀ {x₁ x₂ y₁ y₂ : A} → (x₁ ≈ x₂) → y₁ ≈ y₂ → x₁ ∙ y₁ ≈ x₂ ∙' y₂) →
        (start : A)
        (generate : ℕ → A) →
        (i : ℕ) →
        merge _∙_ start generate i ≈
        merge _∙'_ start generate i
    merge-substitute-op _∙_ _∙'_ ∙-sim start generate i = merge-substitute _∙_ _∙'_ ∙-sim start start refl generate generate (λ _ → refl) i

    merge-substitute-start :
        (_∙_ : A → A → A)
        (∙-cong : Congruent₂ _≈_ _≈_ _≈_ _∙_)
        (start : A)
        (start' : A) →
        (start ≈ start') →
        (generate : ℕ → A) →
        (i : ℕ) →
        merge _∙_ start generate i ≈
        merge _∙_ start' generate i
    merge-substitute-start _∙_ ∙-cong start start' start-sim generate i = merge-substitute _∙_ _∙_ ∙-cong start start' start-sim generate generate (λ _ → refl) i

    merge-substitute-generate :
        (_∙_ : A → A → A)
        (∙-cong : Congruent₂ _≈_ _≈_ _≈_ _∙_)
        (start : A)
        (generate : ℕ → A) →
        (generate' : ℕ → A) →
        (∀ i → generate i ≈ generate' i) →
        (i : ℕ) →
        merge _∙_ start generate i ≈
        merge _∙_ start generate' i
    merge-substitute-generate _∙_ ∙-cong start = merge-substitute _∙_ _∙_ ∙-cong start start refl

    merge-local-substitute-generate :
        (_∙_ : A → A → A)
        (∙-cong : Congruent₂ _≈_ _≈_ _≈_ _∙_)
        (start : A)
        (generate : ℕ → A) →
        (generate' : ℕ → A) →
        (n : ℕ) →
        (∀ i → i < n → generate i ≈ generate' i) →
        (merge _∙_ start generate n) ≈
        (merge _∙_ start generate' n)
    merge-local-substitute-generate _∙_ ∙-cong start generate generate' zero gen= = refl
    merge-local-substitute-generate _∙_ ∙-cong start generate generate' n@(suc n') gen= = begin
        merge _∙_ start generate (suc n') ≈⟨ refl ⟩
        merge _∙_ (make-combine _∙_ generate start n') generate n'      ≈⟨ merge-local-substitute-generate _∙_ ∙-cong (make-combine _∙_ generate start n') generate generate' n' (λ i i<n' → gen= i (≤-trans i<n' n≤sn)) ⟩
        merge _∙_ (make-combine _∙_ generate start n') generate' n'     ≈⟨ merge-substitute _∙_ _∙_ ∙-cong (make-combine _∙_ generate start n') (make-combine _∙_ generate' start n') (∙-cong (gen= n' n<sn) refl) generate' generate' (λ i → refl) n' ⟩
        merge _∙_ (make-combine _∙_ generate' start n') generate' n'    ≈⟨ refl ⟩
        merge _∙_ start generate' (suc n')                              ∎
        where open import Relation.Binary.Reasoning.Setoid A-setoid hiding (start)

-- If a property is preserved by combining and exists at the start, then it exists after merging.
merge-local-carrying-lemma :
    {A : Set ℓ}
    (P : A → Set ℓ₁)
    (_∙_ : A → A → A) →
    (∀ (x y : A) → P x → P y → P (x ∙ y)) →
    (start : A)
    (generate : ℕ → A) →
    (i : ℕ) →
    (P start) →
    (∀ j → .(j < i) → P (generate j)) →
    P (merge _∙_ start generate i)
merge-local-carrying-lemma P _∙_ ∙-preserves-P start generate i P[start] P[generate] = foldl-local-carrying-lemma (make-combine _∙_ generate) start i P (λ x j j<i P[x] → ∙-preserves-P (generate j) x (P[generate] j j<i) P[x]) P[start]

-- If a property is preserved by combining and exists at the start, then it exists after merging.
merge-carrying-lemma :
    {A : Set ℓ}
    (P : A → Set ℓ₁)
    (_∙_ : A → A → A) →
    (∀ (x y : A) → P x → P y → P (x ∙ y)) →
    (start : A)
    (generate : ℕ → A) →
    (i : ℕ) →
    (P start) →
    (∀ j → P (generate j)) →
    P (merge _∙_ start generate i)
merge-carrying-lemma P _∙_ ∙-preserves-P start generate i P[start] P[generate] = foldl-carrying-lemma (make-combine _∙_ generate) start i P (λ x j P[x] → ∙-preserves-P (generate j) x (P[generate] j) P[x]) P[start]

-- If a property at each index is imposed and preserved by combining, then it exists on all indices after merging.
-- merge-all-lemma :
--     {A : Set ℓ}
--     (P : A → A → Set ℓ₁)
--     (P-refl : ∀ x → P x x) →
--     (_∙_ : A → A → A) →
--     (∀ (x y : A) → P x y → P (y ∙ x) y) →
--     (start : A) →
--     P start start →
--     (generate : ℕ → A) →
--     (i : ℕ) →
--     ∀ (j : ℕ) → .(j < i) → P (merge _∙_ start generate i) (generate j)
-- merge-all-lemma P P-refl _∙_ P-carries start P[start,start] generate i j j<i = foldl-all-lemma (make-combine _∙_ generate) start (λ x j → P x (generate j)) (λ x k → {! P-carries start (generate k)  !}) {!   !} i j j<i

module MergeOnSetoid
    (A-setoid : Setoid c ℓ)
    (∙-op : SetoidFunction₂ A-setoid A-setoid A-setoid)
    where

    open MergeSubstitute A-setoid
    open Setoid A-setoid using (_≈_; refl; sym; trans; reflexive) renaming (Carrier to A)
    open SetoidFunction₂ ∙-op using () renaming (respects to ∙-cong)
    private
        _∙_ = ∙-op .SetoidFunction₂.func
        infixl 20 _∙_

    merge-pop-startᵣ :
        Associative A-setoid _∙_ →
        (startₗ : A)
        (startᵣ : A)
        (generate : ℕ → A) →
        (i : ℕ) →
        merge _∙_ (startₗ ∙ startᵣ) generate i ≈
        merge _∙_ startₗ generate i ∙ startᵣ
    merge-pop-startᵣ ∙-assoc startₗ startᵣ generate zero = refl
    merge-pop-startᵣ ∙-assoc startₗ startᵣ generate i@(suc i') = begin
        merge _∙_ (startₗ ∙ startᵣ) generate (suc i')               ≈⟨ refl ⟩
        merge _∙_ (generate i' ∙ (startₗ ∙ startᵣ)) generate i'     ≈⟨ merge-substitute-start _∙_ ∙-cong _ _ ∙-assoc generate i' ⟩
        merge _∙_ ((generate i' ∙ startₗ) ∙ startᵣ) generate i'     ≈⟨ merge-pop-startᵣ ∙-assoc (generate i' ∙ startₗ) startᵣ generate i' ⟩
        merge _∙_ (generate i' ∙ startₗ) generate i' ∙ startᵣ       ≈⟨ refl ⟩
        merge _∙_ startₗ generate i ∙ startᵣ                        ∎
        where open import Relation.Binary.Reasoning.Setoid A-setoid hiding (start)

    merge-pop-start :
        Associative A-setoid _∙_ →
        (id : A) →
        Identity A-setoid _∙_ id →
        (start : A)
        (generate : ℕ → A) →
        (i : ℕ) →
        merge _∙_ start generate i ≈
        merge _∙_ id generate i ∙ start
    merge-pop-start ∙-assoc id ∙-id start generate zero = sym (∙-id .proj₁)
    merge-pop-start ∙-assoc id ∙-id start generate i@(suc i') = begin
        merge _∙_ start generate i                          ≈⟨ refl ⟩
        merge _∙_ (generate i' ∙ start) generate i'         ≈⟨ merge-pop-startᵣ ∙-assoc (generate i') start generate i' ⟩
        merge _∙_ (generate i') generate i' ∙ start         ≈⟨ ∙-cong (merge-substitute-start _∙_ ∙-cong (generate i') (generate i' ∙ id) (sym (∙-id .proj₂)) generate i') refl ⟩
        merge _∙_ (generate i' ∙ id) generate i' ∙ start    ≈⟨ refl ⟩
        merge _∙_ id generate i ∙ start                     ∎
        where open import Relation.Binary.Reasoning.Setoid A-setoid hiding (start)


    -- If f distributes over combine, then it distributes through merge
    merge-distribute-theorem :
        (f : A → A) →
        DistributiveFunction A-setoid f _∙_ →
        (start : A)
        (generate : ℕ → A)
        (n : ℕ) →
        f (merge _∙_ start generate n) ≈ merge _∙_ (f start) (f ∘ generate) n
    merge-distribute-theorem f f-∙-distributes start generate zero = refl
    merge-distribute-theorem f f-∙-distributes start generate n@(suc n') = begin
        f (merge _∙_ start generate n)                                      ≈⟨ reflexive (cong f (merge-pop-first _∙_ start generate n')) ⟩
        f (generate zero ∙ merge _∙_ start (generate ∘ suc) n')             ≈⟨ f-∙-distributes ⟩
        f (generate zero) ∙ f (merge _∙_ start (generate ∘ suc) n')         ≈⟨ ∙-cong refl (merge-distribute-theorem f f-∙-distributes start (generate ∘ suc) n') ⟩
        f (generate zero) ∙ merge _∙_ (f start) (f ∘ generate ∘ suc) n'     ≈⟨ reflexive (≡-sym (merge-pop-first _∙_ (f start) (f ∘ generate) n')) ⟩
        merge _∙_ (f start) (f ∘ generate) n                                ∎
        where open import Relation.Binary.Reasoning.Setoid A-setoid hiding (start)

    merge-zipper-lemma :
        Associative A-setoid _∙_ →
        Commutative A-setoid _∙_ →
        {id : A} →
        Identity A-setoid _∙_ id →
        (generate₁ generate₂ : ℕ → A)
        (n : ℕ) →
        merge _∙_ id generate₁ n ∙ merge _∙_ id generate₂ n ≈ merge _∙_ id (λ i → generate₁ i ∙ generate₂ i) n
    merge-zipper-lemma ∙-assoc ∙-comm {id} ∙-id generate₁ generate₂ zero = ∙-id .proj₁
    merge-zipper-lemma ∙-assoc ∙-comm {id} ∙-id generate₁ generate₂ n@(suc n') = begin
        merge _∙_ id generate₁ n ∙ merge _∙_ id generate₂ n     ≈⟨ reflexive (cong₂ _∙_ (merge-pop-first _∙_ id generate₁ n') (merge-pop-first _∙_ id generate₂ n')) ⟩
        _∙_
            (generate₁ zero ∙ merge _∙_ id (generate₁ ∘ suc) n')
            (generate₂ zero ∙ merge _∙_ id (generate₂ ∘ suc) n')  ≈⟨ exchange-middle A-setoid _∙_ ∙-assoc ∙-comm ∙-cong ⟩
        _∙_
            (generate₁ zero ∙ generate₂ zero)
            (merge _∙_ id (generate₁ ∘ suc) n' ∙ merge _∙_ id (generate₂ ∘ suc) n')  ≈⟨ ∙-cong refl (merge-zipper-lemma ∙-assoc ∙-comm ∙-id (generate₁ ∘ suc) (generate₂ ∘ suc) n') ⟩
        _∙_
            (generate₁ zero ∙ generate₂ zero)
            (merge _∙_ id (λ i → generate₁ (suc i) ∙ generate₂ (suc i)) n')  ≈⟨ reflexive (≡-sym (merge-pop-first _∙_ id (λ i → generate₁ i ∙ generate₂ i) n')) ⟩
        merge _∙_ id (λ i → generate₁ i ∙ generate₂ i) n        ∎
        where open import Relation.Binary.Reasoning.Setoid A-setoid hiding (start)

    merge-pop-last' :
        Associative A-setoid _∙_ →
        {id : A} →
        Identity A-setoid _∙_ id →
        (start : A)
        (generate : ℕ → A) →
        (n : ℕ) →
        merge _∙_ start generate (suc n) ≈ merge _∙_ id generate n ∙ generate n ∙ start
    merge-pop-last' ∙-assoc {id} ∙-id start generate zero = trans (sym (∙-id .proj₁)) ∙-assoc
    merge-pop-last' ∙-assoc {id} ∙-id start generate n@(suc n') = begin
        merge _∙_ start generate (suc n)                                            ≈⟨ reflexive (merge-pop-first _∙_ start generate n) ⟩
        generate zero ∙ merge _∙_ start (generate ∘ suc) n                          ≈⟨ ∙-cong refl (merge-pop-last' ∙-assoc ∙-id start (generate ∘ suc) n') ⟩
        generate zero ∙ ((merge _∙_ id (generate ∘ suc) n' ∙ generate n) ∙ start)   ≈⟨ ∙-assoc ⟩
        (generate zero ∙ (merge _∙_ id (generate ∘ suc) n' ∙ generate n)) ∙ start   ≈⟨ ∙-cong ∙-assoc refl ⟩
        (generate zero ∙ merge _∙_ id (generate ∘ suc) n') ∙ generate n ∙ start     ≈⟨ ∙-cong (∙-cong (reflexive (≡-sym (merge-pop-first _∙_ id generate n'))) refl) refl ⟩
        merge _∙_ id generate n ∙ generate n ∙ start                                ∎
        where open import Relation.Binary.Reasoning.Setoid A-setoid hiding (start)

    merge-pop-last :
        Associative A-setoid _∙_ →
        {id : A} →
        Identity A-setoid _∙_ id →
        (generate : ℕ → A) →
        (n : ℕ) →
        merge _∙_ id generate (suc n) ≈ merge _∙_ id generate n ∙ generate n
    merge-pop-last ∙-assoc {id} ∙-id generate n = trans (merge-pop-last' ∙-assoc ∙-id id generate n) (∙-id .proj₂)

    merge-split-lemma :
        Associative A-setoid _∙_ →
        {id : A} →
        Identity A-setoid _∙_ id →
        (start : A) →
        (generate : ℕ → A) →
        (m n : ℕ) →
        merge _∙_ start generate (m + n) ≈
        merge _∙_ id generate m ∙ merge _∙_ start (generate ∘ (m +_)) n
    merge-split-lemma ∙-assoc {id} ∙-id start generate zero n = sym (∙-id .proj₁)
    merge-split-lemma ∙-assoc {id} ∙-id start generate m@(suc m') n = begin
        merge _∙_ start generate (m + n)                                                                       ≈⟨ reflexive (merge-pop-first _∙_ start generate (m' + n)) ⟩
        generate zero ∙ merge _∙_ start (generate ∘ suc) (m' + n)                                              ≈⟨ ∙-cong refl (merge-split-lemma ∙-assoc ∙-id start (generate ∘ suc) m' n) ⟩
        generate zero ∙ (merge _∙_ id (generate ∘ suc) m' ∙ merge _∙_ start ((generate ∘ suc) ∘ _+_ m') n)     ≈⟨ ∙-assoc ⟩
        (generate zero ∙ merge _∙_ id (generate ∘ suc) m') ∙ merge _∙_ start ((generate ∘ suc) ∘ _+_ m') n     ≈⟨ ∙-cong (reflexive (≡-sym (merge-pop-first _∙_ id generate m'))) refl ⟩
        merge _∙_ id generate m ∙ merge _∙_ start ((generate ∘ suc) ∘ _+_ m') n                                ≈⟨ ∙-cong refl (merge-substitute-generate _∙_ ∙-cong start _ _ (λ _ → refl) n) ⟩
        merge _∙_ id generate m ∙ merge _∙_ start (generate ∘ _+_ m) n                                         ∎
        where open import Relation.Binary.Reasoning.Setoid A-setoid hiding (start)

    merge-extend' :
        (∙-assoc : Associative A-setoid _∙_)
        (start : A)
        (f : ℕ → A) →
        (x y : ℕ) →
        (∀ z → .(z < y) → LeftIdentity A-setoid _∙_ (f (z + x))) →
        merge _∙_ start f x ≈
        merge _∙_ start f (y + x)
    merge-extend' ∙-assoc start f x zero _ = refl
    merge-extend' ∙-assoc start f x y@(suc y') extension-is-left-id = begin
        merge _∙_ start f x                         ≈⟨ merge-extend' ∙-assoc start f x y' (λ z z<y' → extension-is-left-id z (<-≤-trans z<y' n≤sn)) ⟩
        merge _∙_ start f (y' + x)                  ≈⟨ merge-substitute-start _∙_ ∙-cong start (f (y' + x) ∙ start) (sym (extension-is-left-id y' n<sn)) f (y' + x) ⟩
        merge _∙_ (f (y' + x) ∙ start) f (y' + x)   ≈⟨ refl ⟩
        merge _∙_ start f (y + x)                   ∎
        where open import Relation.Binary.Reasoning.Setoid A-setoid hiding (start)

    merge-extend :
        (∙-assoc : Associative A-setoid _∙_)
        (start : A)
        (f : ℕ → A) →
        (x y : ℕ) →
        .(x ≤ y) →
        (∀ z → .(x ≤ z) → .(z < y) → LeftIdentity A-setoid _∙_ (f z)) →
        merge _∙_ start f x ≈
        merge _∙_ start f y
    merge-extend ∙-assoc start f x y x≤y extension-is-left-id = ≡-subst (λ q → merge _∙_ start f x ≈ merge _∙_ start f q) {y ∸ x + x} {y} (m∸n+n≡m x≤y) (merge-extend' ∙-assoc start f x (y ∸ x) λ z z<y∸x → extension-is-left-id (z + x) (m≤n+m x z) (∸-cancelˡ-< {x} {z + x} {y} (≡-subst (_< y ∸ x) (≡-sym (m+n∸n≡m z x)) z<y∸x)))

    -- For rectangle merges
    merge-merge' :
        (∙-assoc : Associative A-setoid _∙_)
        {id : A}
        (∙-id : Identity A-setoid _∙_ id)
        (f : ℕ → ℕ → A) →
        (x y : ℕ) →
        .{{_ : NonZero y}} →
        merge _∙_ id (λ i → merge _∙_ id (f i) y) x ≈
        merge _∙_ id (λ i → f (i / y) (i % y)) (x * y)
    merge-merge' ∙-assoc {id} ∙-id f zero _ = refl
    merge-merge' ∙-assoc {id} ∙-id f x@(suc x') y = begin
        merge _∙_ id (λ i → merge _∙_ id (f i) y) x                                                                 ≈⟨ refl ⟩
        merge _∙_ (merge _∙_ id (f x') y ∙ id) (λ i → merge _∙_ id (f i) y) x'                                      ≈⟨ merge-substitute-start _∙_ ∙-cong _ _ (trans (∙-id .proj₂) (sym (∙-id .proj₁))) (λ i → merge _∙_ id (f i) y) x' ⟩
        merge _∙_ (id ∙ merge _∙_ id (f x') y) (λ i → merge _∙_ id (f i) y) x'                                      ≈⟨ merge-pop-startᵣ ∙-assoc id (merge _∙_ id (f x') y) (λ i → merge _∙_ id (f i) y) x' ⟩
        merge _∙_ id (λ i → merge _∙_ id (f i) y) x' ∙ merge _∙_ id (f x') y                                        ≈⟨ ∙-cong (merge-merge' ∙-assoc ∙-id f x' y) refl ⟩
        merge _∙_ id (λ i → f (i / y) (i % y)) (x' * y) ∙ merge _∙_ id (f x') y                                     ≈⟨ ∙-cong refl (merge-local-substitute-generate _∙_ ∙-cong id (f x') ((λ i → f (i / y) (i % y)) ∘ (x' * y +_)) y lemma) ⟩
        merge _∙_ id (λ i → f (i / y) (i % y)) (x' * y) ∙ merge _∙_ id ((λ i → f (i / y) (i % y)) ∘ (x' * y +_)) y  ≈⟨ sym (merge-split-lemma ∙-assoc ∙-id id (λ i → f (i / y) (i % y)) (x' * y) y) ⟩
        merge _∙_ id (λ i → f (i / y) (i % y)) (x' * y + y)                                                         ≈⟨ reflexive (cong (merge _∙_ id (λ i → f (i / y) (i % y))) {x' * y + y} {x * y} (+-comm (x' * y) y)) ⟩
        merge _∙_ id (λ i → f (i / y) (i % y)) (x * y)                                                              ∎
        where
            lemma :
                (i : ℕ) → i < y →
                f x' i ≈
                f ((x' * y + i) / y) ((x' * y + i) % y)
            lemma i i<y = reflexive (
                f x' i                                      ≡⟨ cong (λ q → f q i) (≡-sym ([m*n+i]/n=i {x'} {y} {i} i<y)) ⟩
                f ((x' * y + i) / y) i                      ≡⟨ cong (f ((x' * y + i) / y)) (≡-sym (m<n⇒m%n≡m i<y)) ⟩
                f ((x' * y + i) / y) (i % y)                ≡⟨ cong (f ((x' * y + i) / y)) (≡-sym ([m+kn]%n≡m%n i x' y)) ⟩
                f ((x' * y + i) / y) ((i + x' * y) % y)     ≡⟨ cong (λ q → f ((x' * y + i) / y) (q % y)) (+-comm i (x' * y)) ⟩
                f ((x' * y + i) / y) ((x' * y + i) % y)     ∎)
                where open ≡-Reasoning
            open import Relation.Binary.Reasoning.Setoid A-setoid

    -- This one is better for non-rectangular merges,
    -- though then you have to prove all the bounds and things
    merge-merge :
        (∙-assoc : Associative A-setoid _∙_)
        {id : A}
        (∙-id : Identity A-setoid _∙_ id)
        (f : ℕ → ℕ → A) →
        (x : ℕ) →
        (ys : ℕ → ℕ) →
        .{{_ : ∀ {i} → NonZero (ys i)}} →
        (y-bound : ℕ) →
        .{{_ : NonZero y-bound}} →
        (∀ i → .(i < x) → ys i ≤ y-bound) →
        (∀ i j → .(i < x) → .(ys i ≤ j) → .(j < y-bound) → LeftIdentity A-setoid _∙_ (f i j)) →
        merge _∙_ id (λ i → merge _∙_ id (f i) (ys i)) x ≈
        merge _∙_ id (λ i → f (i / y-bound) (i % y-bound)) (x * y-bound)
    merge-merge ∙-assoc {id} ∙-id f x ys {{ys-nonZero}} y-bound {{y-bound-nonZero}} ys≤y-bound f-id-on-boundary = begin
        merge _∙_ id (λ i → merge _∙_ id (f i) (ys i)) x                    ≈⟨ merge-local-substitute-generate _∙_ ∙-cong id (λ i → merge _∙_ id (f i) (ys i)) (λ i → merge _∙_ id (f i) y-bound) x (λ i i<x → merge-extend ∙-assoc id (f i) (ys i) y-bound (ys≤y-bound i i<x) (λ j ys[i]≤j j<y-bound → f-id-on-boundary i j i<x ys[i]≤j j<y-bound)) ⟩
        merge _∙_ id (λ i → merge _∙_ id (f i) y-bound) x                   ≈⟨ merge-merge' ∙-assoc ∙-id f x y-bound ⟩
        merge _∙_ id (λ i → f (i / y-bound) (i % y-bound)) (x * y-bound)    ∎
        where open import Relation.Binary.Reasoning.Setoid A-setoid hiding (start)

    private
        merge-flip-lemma-helper :
            Associative A-setoid _∙_ →
            Commutative A-setoid _∙_ →
            (start : A) →
            (generate : ℕ → A) →
            (n : ℕ)
            (i : ℕ) →
            .(suc i < suc n) →
            merge _∙_ start (generate ∘ flip i) (suc n) ≈
            merge _∙_ start generate (suc n)
        merge-flip-lemma-helper ∙-assoc ∙-comm start generate zero i si<n = ⊥-irr-elim (case (s≤s⁻¹ si<n) of λ ())
        merge-flip-lemma-helper ∙-assoc ∙-comm start generate n'@(suc n'') i si<n with i ≟ n' | suc i ≟ n'
        ... | yes ≡-refl | yes ()
        ... | yes ≡-refl | no _ = ⊥-irr-elim (<-irrefl ≡-refl si<n)
        ... | no _ | yes ≡-refl with i ≟ n'' | suc i ≟ n''
        ...     | no i≠n'' | no si≠n'' = ⊥-elim (i≠n'' ≡-refl)
        ...     | yes ≡-refl | no si≠n'' = begin
            merge _∙_ (generate n' ∙ (generate n'' ∙ start)) (generate ∘ flip i) n''    ≈⟨ merge-substitute-start _∙_ ∙-cong _ _ (trans ∙-assoc ∙-comm) (generate ∘ flip i) n'' ⟩
            merge _∙_ (start ∙ (generate n' ∙ generate n'')) (generate ∘ flip i) n''    ≈⟨ merge-pop-startᵣ ∙-assoc start (generate n' ∙ generate n'') (generate ∘ flip i) n'' ⟩
            merge _∙_ start (generate ∘ flip i) n'' ∙ (generate n' ∙ generate n'')      ≈⟨ ∙-cong (merge-local-substitute-generate _∙_ ∙-cong start (generate ∘ flip i) generate n'' λ i i<n'' → reflexive (cong generate (swp-no-match⇒id n'' n' i (≢-sym (<⇒≢ i<n'')) (≢-sym (<⇒≢ (<-≤-trans i<n'' n≤sn)))))) refl ⟩
            merge _∙_ start generate n'' ∙ (generate n' ∙ generate n'')                 ≈⟨ sym (merge-pop-startᵣ ∙-assoc start (generate n' ∙ generate n'') generate n'') ⟩
            merge _∙_ (start ∙ (generate n' ∙ generate n'')) generate n''               ≈⟨ merge-substitute-start _∙_ ∙-cong _ _ (trans ∙-assoc (trans ∙-comm (∙-cong refl ∙-comm))) generate n'' ⟩
            merge _∙_ (generate n'' ∙ (generate n' ∙ start)) generate n''               ≈⟨ refl ⟩
            merge _∙_ start generate n                                                  ∎
            where
                open import Relation.Binary.Reasoning.Setoid A-setoid hiding (start)
                n = suc n'
        merge-flip-lemma-helper ∙-assoc ∙-comm start generate n'@(suc n'') i si<n | no i≠n' | no si≠n' = begin
            merge _∙_ (generate n' ∙ start) (generate ∘ flip i) n'  ≈⟨ merge-substitute-start _∙_ ∙-cong _ _ ∙-comm (generate ∘ flip i) n' ⟩
            merge _∙_ (start ∙ generate n') (generate ∘ flip i) n'  ≈⟨ merge-pop-startᵣ ∙-assoc start (generate n') (generate ∘ flip i) n' ⟩
            merge _∙_ start (generate ∘ flip i) n' ∙ generate n'    ≈⟨ ∙-cong (merge-flip-lemma-helper ∙-assoc ∙-comm start generate n'' i (≤∧≢⇒< {suc i} {n'} (s≤s⁻¹ si<n) si≠n')) refl ⟩
            merge _∙_ start generate n' ∙ generate n'               ≈⟨ sym (merge-pop-startᵣ ∙-assoc start (generate n') generate n') ⟩
            merge _∙_ (start ∙ generate n') generate n'             ≈⟨ merge-substitute-start _∙_ ∙-cong _ _ ∙-comm generate n' ⟩
            merge _∙_ (generate n' ∙ start) generate n'             ≈⟨ refl ⟩
            merge _∙_ start generate n                              ∎
            where
                open import Relation.Binary.Reasoning.Setoid A-setoid hiding (start)
                n = suc n'

        merge-flip-lemma :
            Associative A-setoid _∙_ →
            Commutative A-setoid _∙_ →
            (start : A) →
            (generate : ℕ → A) →
            (n : ℕ)
            (i : ℕ) →
            .(suc i < n) →
            merge _∙_ start (generate ∘ flip i) n ≈
            merge _∙_ start generate n
        merge-flip-lemma ∙-assoc ∙-comm start generate n@(suc n') i si<n = merge-flip-lemma-helper ∙-assoc ∙-comm start generate n' i si<n

    merge-permute-theorem :
        Associative A-setoid _∙_ →
        Commutative A-setoid _∙_ →
        (start : A)
        (generate : ℕ → A) →
        (n : ℕ)
        (p : ℕ → ℕ) →
        IsNFuncPermutation n p →
        merge _∙_ start (generate ∘ p) n ≈
        merge _∙_ start generate n
    merge-permute-theorem ∙-assoc ∙-comm start generate n p p-perm@(p-bij , p-nfunc) = begin
        merge _∙_ start (generate ∘ p) n                                                   ≈⟨ merge-substitute-generate _∙_ ∙-cong start (generate ∘ p) (generate ∘ flip-swap-using-list (decompose-permutation n p)) (λ i → reflexive (cong generate (is-permutation-decomposition n p p-perm i))) n ⟩
        merge _∙_ start (generate ∘ flip-swap-using-list (decompose-permutation n p)) n    ≈⟨ lemma (decompose-permutation n p) (decompose-permutation-valid n p) ≡-refl ⟩
        merge _∙_ start generate n                                                         ∎
        where
            open import Relation.Binary.Reasoning.Setoid A-setoid hiding (start)

            -- problem: flip-swap-using-list (x ∷ l) does flip x *last*. So we can't simply delete x from the list.
            -- thus, we perform induction on the length of l, like horrible gremlins.
            lemma :
                (l : FlipList) →
                .(IsValidFlipList n l) →
                {len : ℕ} → .(length l ≡ len) →
                merge _∙_ start (generate ∘ (flip-swap-using-list l)) n ≈
                merge _∙_ start generate n
            lemma [] _ _ = refl
            lemma (x ∷ l) l-valid {suc len'} length=len = begin
                merge _∙_ start (generate ∘ flip-swap-using-list (x ∷ l)) n                            ≈⟨ reflexive (cong (λ q → merge _∙_ start (generate ∘ flip-swap-using-list q) n) (≡-sym (liat∷ʳunsnoc x l))) ⟩
                merge _∙_ start (generate ∘ flip-swap-using-list (liat x l ∷ʳ unsnoc x l)) n           ≈⟨ merge-substitute-generate _∙_ ∙-cong start (generate ∘ flip-swap-using-list (liat x l ∷ʳ unsnoc x l)) (generate ∘ flip-swap-using-list (liat x l) ∘ flip (unsnoc x l)) (λ i → reflexive (cong generate (flip-swap-using-list-pop-last (liat x l) (unsnoc x l) i))) n ⟩
                merge _∙_ start (generate ∘ flip-swap-using-list (liat x l) ∘ flip (unsnoc x l)) n     ≈⟨ merge-flip-lemma ∙-assoc ∙-comm start (generate ∘ flip-swap-using-list (liat x l)) n (unsnoc x l) (All-get-unsnoc l-valid) ⟩
                merge _∙_ start (generate ∘ flip-swap-using-list (liat x l)) n                         ≈⟨ lemma (liat x l) (All-liat l-valid) {len'} (≡-trans (length-liat x l) (s≡s⁻¹ length=len)) ⟩
                merge _∙_ start generate n                                                             ∎


{-
    I-setoid should be some sort of index setoid, but in principle it can be any finite setoid.
    For when you are merging over all of I-setoid (once per element), and you want to
    reorder the elements you're merging over
-}
module Reindex (I-setoid : Setoid α ℓ) where
    open Setoid I-setoid using () renaming (
        Carrier to I;
        _≈_ to _≈I_;
        reflexive to ≈I-reflexive;
        refl to ≈I-refl;
        sym to ≈I-sym;
        trans to ≈I-trans
        )


    bind : (n : ℕ) → (ℕ → ℕ) → (FakeFin n → ℕ)
    bind n f = f ∘ proj₁

    bind' : (n : ℕ) → (ℕ → I) → (FakeFin n → I)
    bind' n f = f ∘ proj₁

    unbind : {n : ℕ} → (FakeFin n → FakeFin n) → (ℕ → ℕ)
    unbind {n} f i with i <? n
    ... | yes i<n = (proj₁ ∘ f) (i , squash i<n)
    ... | no i≥n = i

    unbind' : {n : ℕ} → I → (FakeFin n → I) → (ℕ → I)
    unbind' {n} x f i with i <? n
    ... | yes i<n = f (i , squash i<n)
    ... | no i≥n = x

    unbind-force< : {n : ℕ} → (f : FakeFin n → FakeFin n) → (i-fin@(i , _) : FakeFin n) →
        unbind f i ≡ f i-fin .proj₁
    unbind-force< {n} f i-fin@(i , squash i<n) with i <? n
    ... | yes _ = ≡-refl
    ... | no ¬i<n = ⊥-irr-elim (¬i<n i<n)

    unbind'-force< : {n : ℕ} → (x : I) → (f : FakeFin n → I) → (i-fin@(i , _) : FakeFin n) →
        unbind' x f i ≡ f i-fin
    unbind'-force< {n} x f (i , squash i<n) with i <? n
    ... | yes _ = ≡-refl
    ... | no ¬i<n = ⊥-irr-elim (¬i<n i<n)

    unbind-nfunc :
        {n : ℕ} → (f : FakeFin n → FakeFin n) →
        IsNFunc n (unbind f)
    unbind-nfunc {n} f = lower , upper
        where
            lower : IsNFuncLower n (unbind f)
            lower {i} i<n with i <? n
            ... | no i≮n = ⊥-elim (i≮n i<n)
            ... | yes i<n with f (i , squash i<n)
            ...     | q , squash q<n = ≤-recompute q<n  -- :[

            upper : IsNFuncUpper n (unbind f)
            upper {i} i≥n with i <? n
            ... | no i≮n = ≡-refl
            ... | yes i<n = ⊥-elim (<-irrefl ≡-refl (≤-<-trans i≥n i<n))

    unbind-nfunc-permutation :
        {n : ℕ} → (f : FakeFin n → FakeFin n) →
        Bijective _≡_ _≡_ f →
        IsNFuncPermutation n (unbind f)
    unbind-nfunc-permutation {n} f f-bij = f'-nfunc , f'-inj , f'-surj
        where
            f'-nfunc = unbind-nfunc f
            f' = unbind f

            f'-inj : Injective _≡_ _≡_ f'
            f'-inj {x} {y} f'x=f'y with x <? n | y <? n
            f'-inj {x} {y} f'x=f'y | no x≮n | no y≮n = f'x=f'y
            f'-inj {x} {y} f'x=f'y | no x≮n | yes y<n with f (y , squash y<n)
            ...     | q , squash q<n = ⊥-irr-elim (x≮n (≤-<-trans (≤-reflexive f'x=f'y) q<n))
            f'-inj {x} {y} f'x=f'y | yes x<n | no y≮n with f (x , squash x<n)
            ...     | q , squash q<n = ⊥-irr-elim (y≮n (≤-<-trans (≤-reflexive (≡-sym f'x=f'y)) q<n))
            f'-inj {x} {y} f'x=f'y | yes x<n | yes y<n = proj₁≡ (f-bij .proj₁ fx=fy)
                where
                    fx=fy : f (x , squash x<n) ≡ f (y , squash y<n)
                    fx=fy = Σ≡ f'x=f'y (squash-irrelevant _ _)

            f'-surj : Surjective _≡_ _≡_ f'
            f'-surj z = case z <? n of λ {
                (yes z<n) → x z<n , λ { ≡-refl → f'x=z z<n };
                (no z≮n) → z , λ { ≡-refl → f'-nfunc .proj₂ {z} (≮⇒≥ z≮n) }
                }
                where
                    module _ (z<n : z < n) where
                        thing : Σ (FakeFin n) λ x → ∀ {w} → w ≡ x → f w ≡ (z , squash z<n)
                        thing = f-bij .proj₂ (z , squash z<n)

                        x-fin : FakeFin n
                        x-fin = thing .proj₁

                        x : ℕ
                        x = x-fin .proj₁

                        squash-x<n : Squash (x < n)
                        squash-x<n = x-fin .proj₂

                        pf : f x-fin ≡ (z , squash z<n)
                        pf = thing .proj₂ ≡-refl

                        f'x=z : f' x ≡ z
                        f'x=z with x <? n | squash-x<n
                        ... | no x≮n | squash x<n = ⊥-irr-elim (x≮n x<n)
                        ... | yes _ | _ = proj₁≡ pf


    {-
        I expect this to be the most intuitive way to frame this concept.
        The key here is just that if two functions f and g generate the same index set,
        so that generate ∘ f and generate ∘ g go over the same items.
        So then this specifies that f generates exactly the elements of I,
        so if f and g are both like this, then we can make an nfunc permutation
        switching from one to the other, which we can then show doesn't change things
        via merge-permute-theorem.
    -}
    BijectiveBinding : (n : ℕ) (f : ℕ → I) → Set (α ⊔ ℓ)
    BijectiveBinding n f = Bijective _≡_ _≈I_ (bind' n f)

    bind'-unbind' : {n : ℕ} (x : I) → (f : FakeFin n → I) → bind' n (unbind' x f) ≗ f
    bind'-unbind' {n} x f (i , squash i<n) with i <? n
    ... | no ¬i<n = ⊥-irr-elim (¬i<n i<n)
    ... | yes _ = ≡-refl

    module BijectiveBinding
        {n : ℕ} {f : ℕ → I}
        (bind'-bijective : BijectiveBinding n f)
        where
        open InverseFunction {s₁ = discrete-setoid (FakeFin n)} {I-setoid} (record {to = bind' n f; cong = from-discrete-cong I-setoid (bind' n f); bijective = bind'-bijective})
            using (is-right-inv)
            renaming (
            inv to inverse;
            inv-congruent to inverse-cong;
            inv-bijective to inverse-bijective
            ) public

        inverse-func : SetoidFunction I-setoid (discrete-setoid (FakeFin n))
        inverse-func = inverse which-is-cong inverse-cong

        unbind-bind' : ∀ (g : ℕ → I) → (i : ℕ) → .(i < n) →
            (f ∘ unbind (inverse ∘ (bind' n g))) i ≈I g i
        unbind-bind' g i i<n with i <? n
        ... | no i≮n = ⊥-irr-elim (i≮n i<n)
        ... | yes _ = is-right-inv (g i)
    open BijectiveBinding using (unbind-bind') public

    module ReindexProof
        (A-setoid : Setoid b ℓ₁)
        (∙-op : SetoidFunction₂ A-setoid A-setoid A-setoid)
        (generate-func : SetoidFunction I-setoid A-setoid)
        where

        open Setoid A-setoid using () renaming (
            Carrier to A;
            _≈_ to _≈A_;
            refl to ≈A-refl;
            sym to ≈A-sym;
            trans to ≈A-trans
            )
        open SetoidFunction₂ ∙-op using () renaming (
            func to _∙_;
            respects to ∙-cong
            )
        open SetoidFunction generate-func using () renaming (
            func to generate;
            respects to generate-cong
            )
        open MergeSubstitute A-setoid
        open MergeOnSetoid A-setoid

        g-inv∘f-nfunc-perm :
            (n : ℕ) (f g : ℕ → I) →
            (bind'-f-bij : BijectiveBinding n f) →
            (bind'-g-bij : BijectiveBinding n g) →
            IsNFuncPermutation n (unbind ((BijectiveBinding.inverse bind'-g-bij) ∘ (bind' n f)))
        g-inv∘f-nfunc-perm n f g
            bind'-f-bij
            bind'-g-bij =
                unbind-nfunc-permutation (g-inv ∘ (bind' n f)) (
                    _∘-bijective_ {s₁ = discrete-setoid (FakeFin n)} {I-setoid} {discrete-setoid (FakeFin n)}
                        {g-inv} (BijectiveBinding.inverse-bijective bind'-g-bij)
                        {bind' n f} bind'-f-bij
                    )
            where
                g-inv = BijectiveBinding.inverse bind'-g-bij
                g-inv-cong = BijectiveBinding.inverse-cong bind'-g-bij

        reindex :
            Associative A-setoid _∙_ →
            Commutative A-setoid _∙_ →
            (n : ℕ) (f g : ℕ → I) →
            BijectiveBinding n f →
            BijectiveBinding n g →
            (start : A) →
            merge _∙_ start (generate ∘ f) n ≈A
            merge _∙_ start (generate ∘ g) n
        reindex ∙-assoc ∙-comm n f g bind'-f-bij bind'-g-bij start = begin
            merge _∙_ start (generate ∘ f) n                                   ≈⟨ (merge-local-substitute-generate _∙_ ∙-cong start (generate ∘ f) (generate ∘ g ∘ unbind (g-inv ∘ (bind' n f))) n λ i i<n → ≈A-sym (generate-cong (unbind-bind' {n} {g} bind'-g-bij f i i<n))) ⟩
            merge _∙_ start (generate ∘ g ∘ unbind (g-inv ∘ (bind' n f))) n     ≈⟨ merge-permute-theorem ∙-op ∙-assoc ∙-comm start (generate ∘ g) n (unbind (g-inv ∘ (bind' n f))) (g-inv∘f-nfunc-perm n f g bind'-f-bij bind'-g-bij) ⟩
            merge _∙_ start (generate ∘ g) n                                   ∎
            where
                open import Relation.Binary.Reasoning.Setoid A-setoid hiding (start)

                g-inv = BijectiveBinding.inverse bind'-g-bij
                g-inv-cong = BijectiveBinding.inverse-cong bind'-g-bij

        reindex' :
            Associative A-setoid _∙_ →
            Commutative A-setoid _∙_ →
            (n : ℕ) (f : ℕ → I) →
            BijectiveBinding n f →
            (shuffle : I → I) →
            (shuffle-bijective : Bijective _≈I_ _≈I_ shuffle) →
            (start : A) →
            merge _∙_ start (generate ∘ f) n ≈A
            merge _∙_ start (generate ∘ shuffle ∘ f) n
        reindex' ∙-assoc ∙-comm n f bind'-f-bij shuffle shuffle-bijective start = begin
            merge _∙_ start (generate ∘ f) n                                                ≈⟨ ≈A-sym (merge-permute-theorem ∙-op ∙-assoc ∙-comm start (generate ∘ f) n (unbind (f-inv-fin ∘ shuffle ∘ bind' n f)) nfunc-permutation) ⟩
            merge _∙_ start (generate ∘ f ∘ (unbind (f-inv-fin ∘ shuffle ∘ bind' n f))) n   ≈⟨ merge-local-substitute-generate _∙_ ∙-cong  start _ _ n (λ i i<n → generate-cong (thing i i<n)) ⟩
            merge _∙_ start (generate ∘ shuffle ∘ f) n                                      ∎
            where
                f-inv-fin : I → FakeFin n
                f-inv-fin = BijectiveBinding.inverse bind'-f-bij

                f-inv-fin-bijective = BijectiveBinding.inverse-bijective bind'-f-bij

                f-inv : I → ℕ
                f-inv = proj₁ ∘ f-inv-fin

                f-inv-cong = BijectiveBinding.inverse-cong bind'-f-bij

                nfunc-permutation : IsNFuncPermutation n (unbind (f-inv-fin ∘ shuffle ∘ bind' n f))
                nfunc-permutation = unbind-nfunc-permutation (f-inv-fin ∘ shuffle ∘ bind' n f) (_∘-bijective_ {s₁ = discrete-setoid (FakeFin n)} {s₂ = I-setoid} {s₃ = discrete-setoid (FakeFin n)} {g = f-inv-fin} f-inv-fin-bijective {f = shuffle ∘ bind' n f} (_∘-bijective_ {s₁ = discrete-setoid (FakeFin n)} {s₂ = I-setoid} {s₃ = I-setoid} {g = shuffle} shuffle-bijective {f = bind' n f} bind'-f-bij))

                thing : ∀ i → .(i < n) → f (unbind (f-inv-fin ∘ shuffle ∘ bind' n f) i) ≈I shuffle (f i)
                thing i i<n = begin
                    f (unbind (f-inv-fin ∘ shuffle ∘ (λ x → f (proj₁ x))) i)    ≈⟨ ≈I-reflexive (cong f (unbind-force< (f-inv-fin ∘ shuffle ∘ (λ x → f (proj₁ x))) (i , squash i<n))) ⟩
                    f (f-inv-fin (shuffle (f i)) .proj₁)                        ≈⟨ ≈I-refl ⟩
                    f (f-inv (shuffle (f i)))                                   ≈⟨ BijectiveBinding.is-right-inv bind'-f-bij (shuffle (f i)) ⟩
                    shuffle (f i)                                               ∎
                    where open import Relation.Binary.Reasoning.Setoid I-setoid hiding (start)

                open import Relation.Binary.Reasoning.Setoid A-setoid hiding (start)

    open ReindexProof using (reindex; reindex') public
{-
    TODO:
    - fold commutativity? like (fold n (fold m things) = fold m (fold n flipped-things)) or like, if combine is commutative then you can reindex or swap indices or something?
        - this will be useful for triangle sums, and for proofs about matrices
-}


module AddIdentity
    (A-setoid : Setoid α ℓ)
    (∙-op : SetoidFunction₂ A-setoid A-setoid A-setoid)
    where
    open Setoid A-setoid using (_≈_) renaming (Carrier to A; refl to ≈-refl)
    open SetoidFunction₂ ∙-op using () renaming (func to _∙_; respects to ∙-cong)

    Maybe-A-setoid = maybe-setoid A-setoid
    open Setoid Maybe-A-setoid using () renaming (
        _≈_ to _≈'_
        )

    _∙'_ : Maybe A → Maybe A → Maybe A
    just x ∙' just y = just (x ∙ y)
    just x ∙' nothing = just x
    nothing ∙' just y = just y
    nothing ∙' nothing = nothing

    ∙'-cong : Congruent₂ _≈'_ _≈'_ _≈'_ _∙'_
    ∙'-cong {just x₁} {just x₂} {just y₁} {just y₂} (maybe-rel-just x₁≈x₂) (maybe-rel-just y₁≈y₂) = maybe-rel-just (∙-cong x₁≈x₂ y₁≈y₂)
    ∙'-cong {just x₁} {just x₂} {nothing} {nothing} (maybe-rel-just x₁≈x₂) maybe-rel-nothing = maybe-rel-just x₁≈x₂
    ∙'-cong {nothing} {nothing} {just y₁} {just y₂} maybe-rel-nothing (maybe-rel-just y₁≈y₂) = maybe-rel-just y₁≈y₂
    ∙'-cong {nothing} {nothing} {nothing} {nothing} maybe-rel-nothing maybe-rel-nothing = maybe-rel-nothing

    ∙'-op : SetoidFunction₂ Maybe-A-setoid Maybe-A-setoid Maybe-A-setoid
    ∙'-op = _∙'_ which-is-cong₂ ∙'-cong

    id : Maybe A
    id = nothing

    ∙'-id : Identity Maybe-A-setoid _∙'_ id
    ∙'-id = (λ {
        {just x} → maybe-rel-just ≈-refl;
        {nothing} → maybe-rel-nothing
        }) , λ {
        {just x} → maybe-rel-just ≈-refl;
        {nothing} → maybe-rel-nothing
        }

    assoc-carries : Associative A-setoid _∙_ → Associative Maybe-A-setoid _∙'_
    assoc-carries ∙-assoc {just _} {just _} {just _} = maybe-rel-just ∙-assoc
    assoc-carries ∙-assoc {just _} {just _} {nothing} = maybe-rel-just ≈-refl
    assoc-carries ∙-assoc {just _} {nothing} {just _} = maybe-rel-just ≈-refl
    assoc-carries ∙-assoc {just _} {nothing} {nothing} = maybe-rel-just ≈-refl
    assoc-carries ∙-assoc {nothing} {just _} {just _} = maybe-rel-just ≈-refl
    assoc-carries ∙-assoc {nothing} {just _} {nothing} = maybe-rel-just ≈-refl
    assoc-carries ∙-assoc {nothing} {nothing} {just _} = maybe-rel-just ≈-refl
    assoc-carries ∙-assoc {nothing} {nothing} {nothing} = maybe-rel-nothing

    comm-carries : Commutative A-setoid _∙_ → Commutative Maybe-A-setoid _∙'_
    comm-carries ∙-comm {just _} {just _} = maybe-rel-just ∙-comm
    comm-carries ∙-comm {just _} {nothing} = maybe-rel-just ≈-refl
    comm-carries ∙-comm {nothing} {just _} = maybe-rel-just ≈-refl
    comm-carries ∙-comm {nothing} {nothing} = maybe-rel-nothing


-- module _ {a ℓ : Level} (I-setoid : Setoid a ℓ) where
--     open Setoid I-setoid using () renaming (
--         Carrier to I;
--         _≈_ to _≈I_;
--         refl to ≈I-refl;
--         sym to ≈I-sym;
--         trans to ≈I-trans
--         )
--     open Reindex using (BijectiveBinding)

--     module Filter {ℓ₁ : Level} (F : I → Set ℓ₁) (F-dec : Unary.Decidable F) where

--         module FilterProof
--             (A-setoid : Setoid b ℓ₁)
--             (∙-op : SetoidFunction₂ A-setoid A-setoid A-setoid)
--             (generate-func : SetoidFunction I-setoid A-setoid)
--             where

--             open Setoid A-setoid using () renaming (
--                 Carrier to A;
--                 _≈_ to _≈A_;
--                 refl to ≈A-refl;
--                 sym to ≈A-sym;
--                 trans to ≈A-trans
--                 )
--             open SetoidFunction₂ ∙-op using () renaming (
--                 func to _∙_;
--                 respects to ∙-cong
--                 )
--             open SetoidFunction generate-func using () renaming (
--                 func to generate;
--                 respects to generate-cong
--                 )
--             open MergeSubstitute A-setoid
--             open MergeOnSetoid A-setoid

--             I-restricted-setoid = property-subset-setoid I-setoid F
--             I-restricted = I-restricted-setoid .Setoid.Carrier
--             modded-generate : A → (ℕ → I) → ℕ → A
--             modded-generate id f i with F-dec (f i)
--             ... | yes _ = generate (f i)
--             ... | no _ = id

--             module Restrict (f : ℕ → I) where
--                 open import Plasmaduck.Counting.Generators (F ∘ f) (¬_ ∘ F ∘ f) using (module CeilToGenerator; module ExistsToCeil)
--                 open ExistsToCeil (λ i → case F-dec (f i) of λ { (yes x) → inj₁ x; (no y) → inj₂ y }) {!   !} {!   !} {!   !} using ()

--             thing-lemma :
--                 (start : A) →
--                 -- start is id for _∙_
--                 (m : ℕ) (f : ℕ → I) →
--                 BijectiveBinding I-setoid m f →
--                 let
--                     g : ℕ → I-restricted
--                     g = {!   !}
--                     n = {!   !}
--                 in
--                     merge _∙_ start (modded-generate start f) m ≡ merge _∙_ start (generate ∘ proj₁ ∘ g) n

--             thing-lemma = {!   !}


--             -- thing-lemma :
--             --     (start : A) →
--             --     -- start is id for _∙_
--             --     (m : ℕ) (f : ℕ → I) →
--             --     BijectiveBinding I-setoid m f →
--             --     (n : ℕ) (g : ℕ → I-restricted) →
--             --     BijectiveBinding I-restricted-setoid n g →
--             --     merge _∙_ start (modded-generate start f) m ≡ merge _∙_ start (generate ∘ proj₁ ∘ g) n
--             -- thing-lemma  = {!   !}


open MergeSubstitute public
open MergeOnSetoid public
open Reindex using (bind'; reindex) public
