open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≢_; _≡_; inspect; cong; Reveal_·_is_; [_]; ≢-sym) renaming (subst to ≡-subst; refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open import Relation.Binary using (Setoid; Rel; IsEquivalence; IsDecTotalOrder; tri<; tri≈; tri>)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Function using (_∘_; _∋_; id; Bijective; Bijection; Injective; Surjective)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Bool using (true; false)
open import Data.Nat using (ℕ; zero; suc; _≟_; _≤_; _<_; _>_; _<?_; z≤n; s≤s; s≤s⁻¹; _∸_; _+_; NonZero; >-nonZero)
open import Data.Nat.Properties using (module ≤-Reasoning; <-cmp; suc-pred; ≤-reflexive; ≤-refl; ≤-trans; ≤-<-trans; <-≤-trans; <-trans; ≰⇒≥; <⇒≱; ≮⇒≥; <⇒≤; <⇒≢; ≤∧≢⇒<; ≤-antisym; <-irrefl; +-mono-≤; +-mono-<; ∸-mono; +-suc; +-comm; +-assoc; m≤n+m; m∸n≤m; m≤m+n; m+n≤o⇒m≤o; m+n≤o⇒n≤o; m+n∸n≡m; m+[n∸m]≡n; +-∸-assoc; ∸-monoʳ-<; m∸[m∸n]≡n; m∸n+n≡m)
open import Data.List using (List; []; _∷_; _∷ʳ_; length)
open import Data.List.Relation.Unary.All as All using (All)

open import Plasmaduck.SetoidExperiment.SetoidMachinery using (discrete-setoid; from-discrete-cong; SetoidFunction₂; _which-is-cong₂_; _←₂_; SetoidFunction; _which-is-cong_; _←_; property-subset-setoid)
open import Plasmaduck.Function.Properties using (module SingleOperator)
open import Plasmaduck.Util.Case using (case_of_)
open import Plasmaduck.Data.FakeFin using (FakeFin; realize; falsify; realize-bijection; falsify-bijection; falsify-realize; realize-falsify)
open import Plasmaduck.Data.Squash using (Squash; squash; squash-irrelevant)
open import Plasmaduck.Data.Empty using (⊥-irr-elim)
open import Plasmaduck.Data.Nat using (≤-recompute; n≤n; n≤sn; n<sn; ≤→<≡; ∸-suc; m∸n∸o≡m∸[n+o]; s≡s⁻¹)
open import Plasmaduck.Fold.Nat.Foldl using (foldl; foldl-pop-first-lemma)
open import Plasmaduck.Data.List using (drop-lookup; All-concat; liat; unsnoc; liat∷ʳunsnoc; All-liat; All-get-unsnoc; length-liat)
open import Plasmaduck.Data.Product using (Σ≡; ×≡; proj₁≡; uncurry; curry)
open import Plasmaduck.Util.TypeChange using (change-type-input-dependence-irrelevance)
open import Plasmaduck.Relation.Equivalence using (irrelevant-cong; irrelevant-cong₂)
open import Plasmaduck.Function.Bijection using (_∘-bijective_; id-bijective; bijective-is-functional; _∘-bijection_; module InverseFunction)
open import Plasmaduck.Function.Properties using (DistributiveFunction; Associative; Commutative; LeftIdentity; Identity; Congruent₂)

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

merge :
    {A : Set ℓ}
    (_∙_ : A → A → A) →
    (start : A) → -- should probably be identity for _∙_
    (generate : ℕ → A) →
    (i : ℕ) →
    A
merge _∙_ start generate i = foldl (make-combine _∙_ generate) start i

merge-pop-first-lemma :
    {A : Set ℓ}
    (_∙_ : A → A → A)
    (start : A)
    (generate : ℕ → A) →
    (i : ℕ) →
    merge _∙_ start generate (suc i) ≡ generate zero ∙ merge _∙_ start (λ i → generate (suc i)) i
merge-pop-first-lemma _∙_ start generate i = foldl-pop-first-lemma (make-combine _∙_ generate) start i

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

module MergeOnSetoid
    (A-setoid : Setoid c ℓ)
    (∙-op : SetoidFunction₂ A-setoid A-setoid A-setoid)
    where

    open MergeSubstitute
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
        merge _∙_ (generate i' ∙ (startₗ ∙ startᵣ)) generate i'     ≈⟨ merge-substitute-start A-setoid _∙_ ∙-cong _ _ ∙-assoc generate i' ⟩
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
        merge _∙_ (generate i') generate i' ∙ start         ≈⟨ ∙-cong (merge-substitute-start A-setoid _∙_ ∙-cong (generate i') (generate i' ∙ id) (sym (∙-id .proj₂)) generate i') refl ⟩
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
        f (merge _∙_ start generate n)                                      ≈⟨ reflexive (cong f (merge-pop-first-lemma _∙_ start generate n')) ⟩
        f (generate zero ∙ merge _∙_ start (generate ∘ suc) n')             ≈⟨ f-∙-distributes ⟩
        f (generate zero) ∙ f (merge _∙_ start (generate ∘ suc) n')         ≈⟨ ∙-cong refl (merge-distribute-theorem f f-∙-distributes start (generate ∘ suc) n') ⟩
        f (generate zero) ∙ merge _∙_ (f start) (f ∘ generate ∘ suc) n'     ≈⟨ reflexive (≡-sym (merge-pop-first-lemma _∙_ (f start) (f ∘ generate) n')) ⟩
        merge _∙_ (f start) (f ∘ generate) n                                ∎
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
        merge _∙_ start generate (suc n)                                            ≈⟨ reflexive (merge-pop-first-lemma _∙_ start generate n) ⟩
        generate zero ∙ merge _∙_ start (generate ∘ suc) n                          ≈⟨ ∙-cong refl (merge-pop-last' ∙-assoc ∙-id start (generate ∘ suc) n') ⟩
        generate zero ∙ ((merge _∙_ id (generate ∘ suc) n' ∙ generate n) ∙ start)   ≈⟨ ∙-assoc ⟩
        (generate zero ∙ (merge _∙_ id (generate ∘ suc) n' ∙ generate n)) ∙ start   ≈⟨ ∙-cong ∙-assoc refl ⟩
        (generate zero ∙ merge _∙_ id (generate ∘ suc) n') ∙ generate n ∙ start     ≈⟨ ∙-cong (∙-cong (reflexive (≡-sym (merge-pop-first-lemma _∙_ id generate n'))) refl) refl ⟩
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
        merge _∙_ start generate (m + n)                                                                       ≈⟨ reflexive (merge-pop-first-lemma _∙_ start generate (m' + n)) ⟩
        generate zero ∙ merge _∙_ start (generate ∘ suc) (m' + n)                                              ≈⟨ ∙-cong refl (merge-split-lemma ∙-assoc ∙-id start (generate ∘ suc) m' n) ⟩
        generate zero ∙ (merge _∙_ id (generate ∘ suc) m' ∙ merge _∙_ start ((generate ∘ suc) ∘ _+_ m') n)     ≈⟨ ∙-assoc ⟩
        (generate zero ∙ merge _∙_ id (generate ∘ suc) m') ∙ merge _∙_ start ((generate ∘ suc) ∘ _+_ m') n     ≈⟨ ∙-cong (reflexive (≡-sym (merge-pop-first-lemma _∙_ id generate m'))) refl ⟩
        merge _∙_ id generate m ∙ merge _∙_ start ((generate ∘ suc) ∘ _+_ m') n                                ≈⟨ ∙-cong refl (merge-substitute-generate A-setoid _∙_ ∙-cong start _ _ (λ _ → refl) n) ⟩
        merge _∙_ id generate m ∙ merge _∙_ start (generate ∘ _+_ m) n                                         ∎
        where open import Relation.Binary.Reasoning.Setoid A-setoid hiding (start)

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
        merge _∙_ (generate n' ∙ (generate n'' ∙ start)) (generate ∘ flip i) n''    ≈⟨ merge-substitute-start A-setoid _∙_ ∙-cong _ _ (trans ∙-assoc ∙-comm) (generate ∘ flip i) n'' ⟩
        merge _∙_ (start ∙ (generate n' ∙ generate n'')) (generate ∘ flip i) n''    ≈⟨ merge-pop-startᵣ ∙-assoc start (generate n' ∙ generate n'') (generate ∘ flip i) n'' ⟩
        merge _∙_ start (generate ∘ flip i) n'' ∙ (generate n' ∙ generate n'')      ≈⟨ ∙-cong (merge-local-substitute-generate A-setoid _∙_ ∙-cong start (generate ∘ flip i) generate n'' λ i i<n'' → reflexive (cong generate (swp-no-match⇒id n'' n' i (≢-sym (<⇒≢ i<n'')) (≢-sym (<⇒≢ (<-≤-trans i<n'' n≤sn)))))) refl ⟩
        merge _∙_ start generate n'' ∙ (generate n' ∙ generate n'')                 ≈⟨ sym (merge-pop-startᵣ ∙-assoc start (generate n' ∙ generate n'') generate n'') ⟩
        merge _∙_ (start ∙ (generate n' ∙ generate n'')) generate n''               ≈⟨ merge-substitute-start A-setoid _∙_ ∙-cong _ _ (trans ∙-assoc (trans ∙-comm (∙-cong refl ∙-comm))) generate n'' ⟩
        merge _∙_ (generate n'' ∙ (generate n' ∙ start)) generate n''               ≈⟨ refl ⟩
        merge _∙_ start generate n                                                  ∎
        where
            open import Relation.Binary.Reasoning.Setoid A-setoid hiding (start)
            n = suc n'
    merge-flip-lemma-helper ∙-assoc ∙-comm start generate n'@(suc n'') i si<n | no i≠n' | no si≠n' = begin
        merge _∙_ (generate n' ∙ start) (generate ∘ flip i) n'  ≈⟨ merge-substitute-start A-setoid _∙_ ∙-cong _ _ ∙-comm (generate ∘ flip i) n' ⟩
        merge _∙_ (start ∙ generate n') (generate ∘ flip i) n'  ≈⟨ merge-pop-startᵣ ∙-assoc start (generate n') (generate ∘ flip i) n' ⟩
        merge _∙_ start (generate ∘ flip i) n' ∙ generate n'    ≈⟨ ∙-cong (merge-flip-lemma-helper ∙-assoc ∙-comm start generate n'' i (≤∧≢⇒< {suc i} {n'} (s≤s⁻¹ si<n) si≠n')) refl ⟩
        merge _∙_ start generate n' ∙ generate n'               ≈⟨ sym (merge-pop-startᵣ ∙-assoc start (generate n') generate n') ⟩
        merge _∙_ (start ∙ generate n') generate n'             ≈⟨ merge-substitute-start A-setoid _∙_ ∙-cong _ _ ∙-comm generate n' ⟩
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
        merge _∙_ start (generate ∘ p) n                                                   ≈⟨ merge-substitute-generate A-setoid _∙_ ∙-cong start (generate ∘ p) (generate ∘ flip-swap-using-list (decompose-permutation n p)) (λ i → reflexive (cong generate (is-permutation-decomposition n p p-perm i))) n ⟩
        merge _∙_ start (generate ∘ flip-swap-using-list (decompose-permutation n p)) n    ≈⟨ lemma (decompose-permutation n p) (decompose-permutation-valid n p) ≡-refl ⟩
        merge _∙_ start generate n                                                         ∎
        where
            open import Relation.Binary.Reasoning.Setoid A-setoid hiding (start)

            -- problem: flip-swap-using-list (x ∷ l) does flip x *last*. So we can't simply delete x from the list.
            -- thus, we perform induction on the length of l, like horrible gremlins.
            lemma :
                (l : FlipList) →
                .(IsValidFlipList n l) →
                {len : ℕ} → length l ≡ len →
                merge _∙_ start (generate ∘ (flip-swap-using-list l)) n ≈
                merge _∙_ start generate n
            lemma [] _ _ = refl
            lemma (x ∷ l) l-valid {suc len'} length=len = begin
                merge _∙_ start (generate ∘ flip-swap-using-list (x ∷ l)) n                            ≈⟨ reflexive (cong (λ q → merge _∙_ start (generate ∘ flip-swap-using-list q) n) (≡-sym (liat∷ʳunsnoc x l))) ⟩
                merge _∙_ start (generate ∘ flip-swap-using-list (liat x l ∷ʳ unsnoc x l)) n           ≈⟨ merge-substitute-generate A-setoid _∙_ ∙-cong start (generate ∘ flip-swap-using-list (liat x l ∷ʳ unsnoc x l)) (generate ∘ flip-swap-using-list (liat x l) ∘ flip (unsnoc x l)) (λ i → reflexive (cong generate (flip-swap-using-list-pop-last (liat x l) (unsnoc x l) i))) n ⟩
                merge _∙_ start (generate ∘ flip-swap-using-list (liat x l) ∘ flip (unsnoc x l)) n     ≈⟨ merge-flip-lemma ∙-assoc ∙-comm start (generate ∘ flip-swap-using-list (liat x l)) n (unsnoc x l) (All-get-unsnoc l-valid) ⟩
                merge _∙_ start (generate ∘ flip-swap-using-list (liat x l)) n                         ≈⟨ lemma (liat x l) (All-liat l-valid) {len'} (≡-trans (length-liat x l) (s≡s⁻¹ length=len)) ⟩
                merge _∙_ start generate n                                                             ∎


{-
    I-setoid should be some sort of index setoid, but in principle it can be any finite setoid.
    For when you are merging over all of I-setoid (once per element), and you want to
    reorder the elements you're merging over
-}
module Reindex {a ℓ : Level} (I-setoid : Setoid a ℓ) where
    open Setoid I-setoid using () renaming (
        Carrier to I;
        _≈_ to _≈I_;
        refl to ≈I-refl;
        sym to ≈I-sym;
        trans to ≈I-trans
        )


    bind : (n : ℕ) → (ℕ → I) → (FakeFin n → I)
    bind n f = f ∘ proj₁

    unbind : {n : ℕ} → (FakeFin n → FakeFin n) → (ℕ → ℕ)
    unbind {n} f i with i <? n
    ... | yes i<n = (proj₁ ∘ f) (i , squash i<n)
    ... | no i≥n = i

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
    BijectiveBinding : (n : ℕ) (f : ℕ → I) → Set (a ⊔ ℓ)
    BijectiveBinding n f = Bijective _≡_ _≈I_ (bind n f)

    module BijectiveBinding
        {n : ℕ} {f : ℕ → I}
        (bind-bijective : BijectiveBinding n f)
        where
        open InverseFunction {s₁ = discrete-setoid (FakeFin n)} {I-setoid} (record {to = bind n f; cong = from-discrete-cong I-setoid (bind n f); bijective = bind-bijective})
            using (is-right-inv)
            renaming (
            inv to inverse;
            inv-congruent to inverse-cong;
            inv-bijective to inverse-bijective
            ) public

        inverse-func : SetoidFunction I-setoid (discrete-setoid (FakeFin n))
        inverse-func = inverse which-is-cong inverse-cong

        unbind-bind : ∀ (g : ℕ → I) → (i : ℕ) → .(i < n) →
            (f ∘ unbind (inverse ∘ (bind n g))) i ≈I g i
        unbind-bind g i i<n with i <? n
        ... | no i≮n = ⊥-irr-elim (i≮n i<n)
        ... | yes _ = is-right-inv (g i)
    open BijectiveBinding using (unbind-bind) public

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
            (bind-f-bij : BijectiveBinding n f) →
            (bind-g-bij : BijectiveBinding n g) →
            IsNFuncPermutation n (unbind ((BijectiveBinding.inverse bind-g-bij) ∘ (bind n f)))
        g-inv∘f-nfunc-perm n f g
            bind-f-bij
            bind-g-bij =
                unbind-nfunc-permutation (g-inv ∘ (bind n f)) (
                    _∘-bijective_ {s₁ = discrete-setoid (FakeFin n)} {I-setoid} {discrete-setoid (FakeFin n)}
                        {g-inv} (BijectiveBinding.inverse-bijective bind-g-bij)
                        {bind n f} bind-f-bij
                    )
            where
                g-inv = BijectiveBinding.inverse bind-g-bij
                g-inv-cong = BijectiveBinding.inverse-cong bind-g-bij

        reindex :
            (n : ℕ) (f g : ℕ → I) →
            BijectiveBinding n f →
            BijectiveBinding n g →
            Associative A-setoid _∙_ →
            Commutative A-setoid _∙_ →
            (start : A) →
            merge _∙_ start (generate ∘ f) n ≈A
            merge _∙_ start (generate ∘ g) n
        reindex n f g bind-f-bij bind-g-bij ∙-assoc ∙-comm start = begin
            merge _∙_ start (generate ∘ f) n                                   ≈⟨ (merge-local-substitute-generate _∙_ ∙-cong start (generate ∘ f) (generate ∘ g ∘ unbind (g-inv ∘ (bind n f))) n λ i i<n → ≈A-sym (generate-cong (unbind-bind {n} {g} bind-g-bij f i i<n))) ⟩
            merge _∙_ start (generate ∘ g ∘ unbind (g-inv ∘ (bind n f))) n     ≈⟨ merge-permute-theorem ∙-op ∙-assoc ∙-comm start (generate ∘ g) n (unbind (g-inv ∘ (bind n f))) (g-inv∘f-nfunc-perm n f g bind-f-bij bind-g-bij) ⟩
            merge _∙_ start (generate ∘ g) n                                   ∎
            where
                open import Relation.Binary.Reasoning.Setoid A-setoid hiding (start)

                g-inv = BijectiveBinding.inverse bind-g-bij
                g-inv-cong = BijectiveBinding.inverse-cong bind-g-bij
    open ReindexProof using (reindex) public
{-
    TODO:
    - fold commutativity? like (fold n (fold m things) = fold m (fold n flipped-things)) or like, if combine is commutative then you can reindex or swap indices or something?
        - this will be useful for triangle sums, and for proofs about matrices
-}

open MergeSubstitute public
open MergeOnSetoid public
open Reindex using (bind; reindex) public
