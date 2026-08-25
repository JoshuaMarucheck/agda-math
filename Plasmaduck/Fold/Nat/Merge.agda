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
open import Data.Nat using (ℕ; zero; suc; _≟_; _≤_; _<_; _>_; z≤n; s≤s; s≤s⁻¹; _∸_; _+_; NonZero; >-nonZero)
open import Data.Nat.Properties using (module ≤-Reasoning; <-cmp; suc-pred; ≤-reflexive; ≤-refl; ≤-trans; ≤-<-trans; <-≤-trans; <-trans; ≰⇒≥; <⇒≱; ≮⇒≥; <⇒≤; <⇒≢; ≤∧≢⇒<; ≤-antisym; <-irrefl; +-mono-≤; +-mono-<; ∸-mono; +-suc; +-comm; +-assoc; m≤n+m; m∸n≤m; m≤m+n; m+n≤o⇒m≤o; m+n≤o⇒n≤o; m+n∸n≡m; m+[n∸m]≡n; +-∸-assoc; ∸-monoʳ-<; m∸[m∸n]≡n; m∸n+n≡m)
open import Data.List using (List; []; _∷_; _∷ʳ_; length)
open import Data.List.Relation.Unary.All as All using (All)

open import Plasmaduck.SetoidExperiment.SetoidMachinery using (discrete-setoid; from-discrete-cong; SetoidFunction₂; _which-is-cong₂_; _←₂_; SetoidFunction; _which-is-cong_; _←_; property-subset-setoid)
open import Plasmaduck.Function.Properties using (module SingleOperator)
open import Plasmaduck.Util.Case using (case_of_)
open import Plasmaduck.Data.FakeFin using (FakeFin; realize; falsify; realize-bijection; falsify-bijection; falsify-realize; realize-falsify)
open import Plasmaduck.Data.Squash using (Squash; squash)
open import Plasmaduck.Data.Empty using (⊥-irr-elim)
open import Plasmaduck.Data.Nat using (≤-recompute; n≤n; n≤sn; n<sn; ≤→<≡; ∸-suc; m∸n∸o≡m∸[n+o]; s≡s⁻¹)
open import Plasmaduck.Fold.Nat.Foldl using (foldl; foldl-pop-first-lemma)
open import Plasmaduck.Data.List using (drop-lookup; All-concat; liat; unsnoc; liat∷ʳunsnoc; All-liat; All-get-unsnoc; length-liat)
open import Plasmaduck.Data.Product using (Σ≡; ×≡; proj₁≡; uncurry; curry)
open import Plasmaduck.Util.TypeChange using (change-type-input-dependence-irrelevance)
open import Plasmaduck.Relation.Equivalence using (irrelevant-cong; irrelevant-cong₂)
open import Plasmaduck.Function.Bijection using (_∘-bijective_; id-bijective; bijective-is-functional; _∘-bijection_)
open import Plasmaduck.Function.Properties using (DistributiveFunction; Associative; Commutative; LeftIdentity; Identity; Congruent₂)

open import Plasmaduck.Counting.Permutation.FlipPermutation using (decompose-permutation; is-permutation-decomposition; decompose-permutation-valid)
open import Plasmaduck.Counting.Permutation.FlipList using (flip; FlipList; IsValidFlipList; flip-swap-using-list; flip-swap-using-list-pop-last)
open import Plasmaduck.Counting.Permutation.Defs using (IsNFuncPermutation; swp; swp-helper)
open import Plasmaduck.Counting.Permutation.Swap using (swp-no-match⇒id)



{-
    combining finite sets using commutative associative binary operators.
-}
module Plasmaduck.Fold.Nat.Merge where

variable
    ℓ c α β : Level


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

-- merge-consume-last :
--     {A : Set ℓ}
--     (_∙_ : A → A → A)
--     (start : A)
--     (generate : ℕ → A) →
--     (i : ℕ) →
--     merge _∙_ start generate (suc i) ≡ merge _∙_ (generate i ∙ start) generate i
-- merge-consume-last _∙_ start n generate = ≡-refl

merge-pop-first-lemma :
    {A : Set ℓ}
    (_∙_ : A → A → A)
    (start : A)
    (generate : ℕ → A) →
    (i : ℕ) →
    merge _∙_ start generate (suc i) ≡ generate zero ∙ merge _∙_ start (λ i → generate (suc i)) i
merge-pop-first-lemma _∙_ start generate i = foldl-pop-first-lemma (make-combine _∙_ generate) start i

module _
    (A-setoid : Setoid c ℓ)
    where
    open Setoid A-setoid using (_≈_; refl; sym; trans; reflexive) renaming (
        Carrier to A
        )

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


-- Permutation : ℕ → Set
-- Permutation n = Bijection (discrete-setoid (FakeFin n)) (discrete-setoid (FakeFin n))

-- permute-then-generate-substitute :
--     {A : Set α}
--     (n : ℕ) →
--     (generate : (i : ℕ) → .(i < n) → A) →
--     (p₁ : FakeFin n → FakeFin n) →
--     (p₂ : FakeFin n → FakeFin n) →
--     (∀ k → p₁ k ≡ p₂ k) →
--     (i : ℕ) → .(i<n : i < n) →
--     permute-then-generate n generate p₁ i i<n ≡ permute-then-generate n generate p₂ i i<n
-- permute-then-generate-substitute n generate p₁ p₂ p₁≈p₂ i i<n with p₁ (i , squash i<n) | inspect p₁ (i , squash i<n) | p₂ (i , squash i<n) | inspect p₂ (i , squash i<n)
-- ... | j , squash j<n | [ j= ] | k , squash k<n | [ k= ] =
--     generate j j<n                                      ≡⟨ irrelevant-cong (_< n) generate {j} {p₁-thing} {j<n} {p₁-thing<n} (≡-sym (proj₁≡ j=)) ⟩
--     generate (p₁ (i , squash i<n) .proj₁) p₁-thing<n  ≡⟨ irrelevant-cong (_< n) generate {p₁-thing} {p₂-thing} {p₁-thing<n} {p₂-thing<n} (proj₁≡ (p₁≈p₂ (i , squash i<n))) ⟩
--     generate (p₂ (i , squash i<n) .proj₁) p₂-thing<n  ≡⟨ irrelevant-cong (_< n) generate {p₂-thing} {k} {p₂-thing<n} {k<n} (proj₁≡ k=) ⟩
--     generate k k<n  ∎
--     where
--         open ≡-Reasoning

--         p₁-thing = p₁ (i , squash i<n) .proj₁
--         p₁-thing<n = ≤-<-trans (≤-reflexive (proj₁≡ j=)) (≤-recompute j<n)

--         p₂-thing = p₂ (i , squash i<n) .proj₁
--         p₂-thing<n = ≤-<-trans (≤-reflexive (proj₁≡ k=)) (≤-recompute k<n)


module _
    {A-setoid : Setoid c ℓ}
    (∙-op : SetoidFunction₂ A-setoid A-setoid A-setoid)
    where

    open Setoid A-setoid using (_≈_; refl; sym; trans; reflexive) renaming (Carrier to A)
    open SetoidFunction₂ ∙-op using () renaming (func to _∙_; respects to ∙-cong)


    merge-local-substitute-generate :
        (start : A)
        (generate : ℕ → A) →
        (generate' : ℕ → A) →
        (n : ℕ) →
        (∀ i → i < n → generate i ≈ generate' i) →
        merge _∙_ start generate n ≈
        merge _∙_ start generate' n
    merge-local-substitute-generate start generate generate' zero gen= = refl
    merge-local-substitute-generate start generate generate' n@(suc n') gen= = begin 
        merge _∙_ start generate (suc n') ≈⟨ refl ⟩ 
        merge _∙_ (make-combine _∙_ generate start n') generate n'      ≈⟨ merge-local-substitute-generate (make-combine _∙_ generate start n') generate generate' n' (λ i i<n' → gen= i (≤-trans i<n' n≤sn)) ⟩ 
        merge _∙_ (make-combine _∙_ generate start n') generate' n'     ≈⟨ merge-substitute A-setoid _∙_ _∙_ ∙-cong (make-combine _∙_ generate start n') (make-combine _∙_ generate' start n') (∙-cong (gen= n' n<sn) refl) generate' generate' (λ i → refl) n' ⟩ 
        merge _∙_ (make-combine _∙_ generate' start n') generate' n'    ≈⟨ refl ⟩ 
        merge _∙_ start generate' (suc n')                              ∎     
        where open import Relation.Binary.Reasoning.Setoid A-setoid hiding (start)

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

    merge-pop-last :
        Associative A-setoid _∙_ →
        (id : A) →
        Identity A-setoid _∙_ id →
        (generate : ℕ → A) →
        (n : ℕ) →
        merge _∙_ id generate (suc n) ≈ merge _∙_ id generate n ∙ generate n
    merge-pop-last ∙-assoc id (id-is-left-∙-id , id-is-right-∙-id) generate zero = trans id-is-right-∙-id (sym id-is-left-∙-id)
    merge-pop-last ∙-assoc id id-is-∙-id generate n@(suc n') = begin
        merge _∙_ id generate (suc n)                                       ≈⟨ reflexive (merge-pop-first-lemma _∙_ id generate n) ⟩
        generate zero ∙ merge _∙_ id (generate ∘ suc) n                     ≈⟨ ∙-cong refl (merge-pop-last ∙-assoc id id-is-∙-id (generate ∘ suc) n') ⟩
        generate zero ∙ (merge _∙_ id (generate ∘ suc) n' ∙ generate n)     ≈⟨ ∙-assoc ⟩
        (generate zero ∙ merge _∙_ id (generate ∘ suc) n') ∙ generate n     ≈⟨ ∙-cong (reflexive (≡-sym (merge-pop-first-lemma _∙_ id generate n'))) refl ⟩
        merge _∙_ id generate n ∙ generate n                                ∎
        where open import Relation.Binary.Reasoning.Setoid A-setoid

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
        merge _∙_ start (generate ∘ flip i) n'' ∙ (generate n' ∙ generate n'')      ≈⟨ ∙-cong (merge-local-substitute-generate start (generate ∘ flip i) generate n'' λ i i<n'' → reflexive (cong generate (swp-no-match⇒id n'' n' i (≢-sym (<⇒≢ i<n'')) (≢-sym (<⇒≢ (<-≤-trans i<n'' n≤sn)))))) refl ⟩ 
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
        (id : A) →
        Identity A-setoid _∙_ id →
        (generate : ℕ → A) →
        (n : ℕ)
        (p : ℕ → ℕ) →
        IsNFuncPermutation n p →
        merge _∙_ id (generate ∘ p) n ≈
        merge _∙_ id generate n
    merge-permute-theorem ∙-assoc ∙-comm id ∙-id generate n p p-perm@(p-bij , p-nfunc) = begin 
        merge _∙_ id (generate ∘ p) n                                                   ≈⟨ merge-substitute-generate A-setoid _∙_ ∙-cong id (generate ∘ p) (generate ∘ flip-swap-using-list (decompose-permutation n p)) (λ i → reflexive (cong generate (is-permutation-decomposition n p p-perm i))) n ⟩ 
        merge _∙_ id (generate ∘ flip-swap-using-list (decompose-permutation n p)) n    ≈⟨ lemma (decompose-permutation n p) (decompose-permutation-valid n p) ≡-refl ⟩ 
        merge _∙_ id generate n                                                         ∎
        where
            -- problem: flip-swap-using-list (x ∷ l) does flip x *last*. So we can't simply delete x from the list.
            -- thus, we perform induction on the length of l, like horrible gremlins.
            lemma :
                (l : FlipList) →
                .(IsValidFlipList n l) →
                {len : ℕ} → length l ≡ len →
                merge _∙_ id (generate ∘ (flip-swap-using-list l)) n ≈
                merge _∙_ id generate n
            lemma [] _ _ = refl
            lemma (x ∷ l) l-valid {suc len'} length=len = begin 
                merge _∙_ id (generate ∘ flip-swap-using-list (x ∷ l)) n                            ≈⟨ reflexive (cong (λ q → merge _∙_ id (generate ∘ flip-swap-using-list q) n) (≡-sym (liat∷ʳunsnoc x l))) ⟩
                merge _∙_ id (generate ∘ flip-swap-using-list (liat x l ∷ʳ unsnoc x l)) n           ≈⟨ merge-substitute-generate A-setoid _∙_ ∙-cong id (generate ∘ flip-swap-using-list (liat x l ∷ʳ unsnoc x l)) (generate ∘ flip-swap-using-list (liat x l) ∘ flip (unsnoc x l)) (λ i → reflexive (cong generate (flip-swap-using-list-pop-last (liat x l) (unsnoc x l) i))) n ⟩
                merge _∙_ id (generate ∘ flip-swap-using-list (liat x l) ∘ flip (unsnoc x l)) n     ≈⟨ merge-flip-lemma ∙-assoc ∙-comm id (generate ∘ flip-swap-using-list (liat x l)) n (unsnoc x l) (All-get-unsnoc l-valid) ⟩
                merge _∙_ id (generate ∘ flip-swap-using-list (liat x l)) n                         ≈⟨ lemma (liat x l) (All-liat l-valid) {len'} (≡-trans (length-liat x l) (s≡s⁻¹ length=len)) ⟩ 
                merge _∙_ id generate n                                                             ∎
                where 
                    open import Relation.Binary.Reasoning.Setoid A-setoid

            open import Relation.Binary.Reasoning.Setoid A-setoid
        --  begin
        -- merge _∙_ id n (permute-then-generate n generate f)                                             ≈⟨ {!   !} ⟩
        -- merge _∙_ id n (permute-then-generate n generate (falsify ∘ realize ∘ f ∘ falsify ∘ realize))   ≈⟨ merge-substitute-generate n (permute-then-generate n generate (falsify ∘ realize ∘ f ∘ falsify ∘ realize)) (permute-then-generate n generate (falsify ∘ swap-with-list l ∘ realize)) {!   !} ⟩
        -- merge _∙_ id n (permute-then-generate n generate (falsify ∘ swap-with-list l ∘ realize))        ≈⟨ {!   !} ⟩
        -- merge _∙_ id n generate                                                                         ∎
        -- where
        --     open SwapList
        --     open import Relation.Binary.Reasoning.Setoid A-setoid


        --     helper' :
        --         (l : SwapList n) →
        --         (x y : Fin n) →
        --         merge _∙_ id n (permute-then-generate n generate (falsify ∘ swap-with-list l ∘ swp x y ∘ realize)) ≈
        --         merge _∙_ id n (permute-then-generate n generate (falsify ∘ swap-with-list l ∘ realize))
        --     helper' l x y = {!   !}

        --     helper :
        --         (l : SwapList n) →
        --         merge _∙_ id n (permute-then-generate n generate (falsify ∘ swap-with-list l ∘ realize)) ≈
        --         merge _∙_ id n generate
        --     helper [] = begin
        --         merge _∙_ id n (permute-then-generate n generate (falsify ∘ realize))   ≈⟨ merge-substitute-generate n (permute-then-generate n generate (falsify ∘ realize)) (permute-then-generate n generate Function.id) (λ i i<n → reflexive (permute-then-generate-substitute n generate (falsify ∘ realize) Function.id (λ k → falsify-realize) i i<n)) ⟩
        --         merge _∙_ id n (permute-then-generate n generate Function.id)           ≈⟨ refl ⟩
        --         merge _∙_ id n generate                                                 ∎
        --     helper (xy@(x , y) ∷ l) = begin
        --         merge _∙_ id n (permute-then-generate n generate (falsify ∘ swap-with-list (xy ∷ l) ∘ realize))     ≈⟨ reflexive (cong (λ q → merge _∙_ id n (permute-then-generate n generate (falsify ∘ q ∘ realize))) (swap-pop-initial Function.id l x y)) ⟩
        --         merge _∙_ id n (permute-then-generate n generate (falsify ∘ swap-with-list l ∘ swp x y ∘ realize))  ≈⟨ helper' l x y ⟩
        --         merge _∙_ id n (permute-then-generate n generate (falsify ∘ swap-with-list l ∘ realize))            ≈⟨ helper l ⟩
        --         merge _∙_ id n generate                                                                             ∎

        --     f = p .Bijection.to

        --     p' : FinPermutation n
        --     p' = realize-bijection ∘-bijection p ∘-bijection falsify-bijection

        --     f' = realize ∘ f ∘ falsify

        --     l = decompose-permutation p'


{-
    TODO:
    - fold commutativity? like (fold n (fold m things) = fold m (fold n flipped-things)) or like, if combine is commutative then you can reindex or swap indices or something?
        - this will be useful for triangle sums, and for proofs about matrices
-}