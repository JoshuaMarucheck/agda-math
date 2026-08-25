open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≢_; _≡_; inspect; cong; Reveal_·_is_; [_]) renaming (subst to ≡-subst; refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open import Relation.Binary using (Setoid; Rel; IsEquivalence; IsDecTotalOrder; tri<; tri≈; tri>)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Function using (_∘_; _∋_; id; Bijective; Bijection; Injective; Surjective)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; _>_; z≤n; s≤s; s≤s⁻¹; _∸_; _+_; NonZero; >-nonZero)
open import Data.Nat.Properties using (module ≤-Reasoning; <-cmp; suc-pred; ≤-reflexive; ≤-refl; ≤-trans; ≤-<-trans; <-≤-trans; <-trans; ≰⇒≥; <⇒≱; ≮⇒≥; <⇒≤; ≤-antisym; <-irrefl; +-mono-≤; +-mono-<; ∸-mono; +-suc; +-comm; +-assoc; m≤n+m; m∸n≤m; m≤m+n; m+n≤o⇒m≤o; m+n≤o⇒n≤o; m+n∸n≡m; m+[n∸m]≡n; +-∸-assoc; ∸-monoʳ-<; m∸[m∸n]≡n; m∸n+n≡m)
open import Data.Fin using (Fin; _≟_; _≤?_; _<?_; toℕ; fromℕ<) renaming (zero to zero-fin; suc to suc-fin; _<_ to _<-fin_; _≤_ to _≤-fin_; _≥_ to _≥-fin_)
open import Data.Fin.Properties using (toℕ-fromℕ<; fromℕ<-toℕ; fromℕ<-cong; toℕ<n; toℕ-injective; fromℕ<-injective) renaming (≤-isDecTotalOrder to ≤-fin-isDecTotalOrder)
open import Data.List using (List; foldl; _∷_; []; length; lookup; drop; _++_; reverse)
open import Data.List.Properties using (drop-drop; reverse-++)

open import Plasmaduck.SetoidExperiment.SetoidMachinery using (discrete-setoid; from-discrete-cong; SetoidFunction₂; _which-is-cong₂_; _←₂_; SetoidFunction; _which-is-cong_; _←_; property-subset-setoid)
open import Plasmaduck.Function.Properties using (module SingleOperator)
open import Plasmaduck.Util.Case using (case_of_)
open import Plasmaduck.Data.FakeFin using (FakeFin; realize; falsify; realize-bijection; falsify-bijection; falsify-realize; realize-falsify)
open import Plasmaduck.Data.Squash using (Squash; squash)
open import Plasmaduck.Data.Nat using (≤-recompute; n≤n; n≤sn; n<sn; ≤→<≡; ∸-suc; m∸n∸o≡m∸[n+o])
open import Plasmaduck.Fold.BoundedNat.Foldl using (fold; fold-consume-last-lemma; fold-pop-first-lemma; module Foldl')
open import Plasmaduck.Data.List using (drop-lookup)
open import Plasmaduck.Data.Product using (Σ≡; ×≡; proj₁≡; uncurry; curry)
open import Plasmaduck.Util.TypeChange using (change-type-input-dependence-irrelevance)
open import Plasmaduck.Relation.Equivalence using (irrelevant-cong; irrelevant-cong₂)
open import Plasmaduck.Function.Bijection using (_∘-bijective_; id-bijective; bijective-is-functional; _∘-bijection_)
open import Plasmaduck.Function.Properties using (DistributiveFunction; Associative; Commutative; Identity; Congruent₂)

open import Plasmaduck.Counting.Permutation.FlipPermutation using (decompose-permutation; is-permutation-decomposition)
open import Plasmaduck.Counting.Permutation.FlipList using (FlipList; flip-swap-using-list)
open import Plasmaduck.Counting.Permutation.Defs using () renaming (Permutation to FinPermutation)



{-
    combining finite sets using commutative associative binary operators.
-}
module Plasmaduck.Fold.BoundedNat.Merge where

variable
    ℓ c α β : Level


{-
    Fold, as in BoundedNat/Foldl.agda, but for binary operators.
        That is, when combine can be split into two functions _∙_ and generate
        such that combine acc i i<n = generate i i<n ∙ acc
    This makes proofs about associativity and commutativity more apparent.
    Since fold goes from high indices to low indices, the accumulator adds elements on the left.
    That means the resulting expression is right-associative.
-}
private
    make-combine :
        {A : Set ℓ}
        (_∙_ : A → A → A) →
        {n : ℕ}
        (generate : (i : ℕ) → .(i < n) → A) →
        A → (i : ℕ) → .(i < n) → A
    make-combine _∙_ generate = λ acc i i<n → generate i i<n ∙ acc

merge :
    {A : Set ℓ}
    (_∙_ : A → A → A) →
    (start : A) → -- should probably be identity for _∙_
    (n : ℕ)
    (generate : (i : ℕ) → .(i < n) → A) →
    A
merge _∙_ start n generate = fold n (make-combine _∙_ generate) start

merge-consume-last :
    {A : Set ℓ}
    (_∙_ : A → A → A)
    (start : A)
    (n : ℕ)
    (generate : (i : ℕ) → .(i < suc n) → A) →
    merge _∙_ start (suc n) generate ≡ merge _∙_ (generate n n<sn ∙ start) n (λ i i<n → generate i (≤-trans i<n n≤sn))
merge-consume-last _∙_ start n generate = fold-consume-last-lemma n (make-combine _∙_ generate) start

merge-pop-first-lemma :
    {A : Set ℓ}
    (_∙_ : A → A → A)
    (start : A)
    (n : ℕ)
    (generate : (i : ℕ) → .(i < suc n) → A) →
    merge _∙_ start (suc n) generate ≡ generate zero (s≤s z≤n) ∙ merge _∙_ start n (λ i i<n → generate (suc i) (s≤s i<n))
merge-pop-first-lemma _∙_ start n generate = fold-pop-first-lemma n (make-combine _∙_ generate) start

module _
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
        (n : ℕ)
        (generate : (i : ℕ) → .(i < n) → A) →
        (generate' : (i : ℕ) → .(i < n) → A) →
        (∀ (i) .(i<n : i < n) → generate i i<n ≈ generate' i i<n) →
        merge _∙_ start n generate ≈
        merge _∙'_ start' n generate'
    merge-substitute _∙_ _∙'_ ∙-sim start start' start-sim zero generate generate' generate-sim = start-sim
    merge-substitute _∙_ _∙'_ ∙-sim start start' start-sim n@(suc zero) generate generate' generate-sim = ∙-sim (generate-sim zero n<sn) start-sim
    merge-substitute _∙_ _∙'_ ∙-sim start start' start-sim n@(suc n'@(suc n'')) generate generate' generate-sim = begin
        merge _∙_ start n generate                                                                  ≈⟨ reflexive (merge-consume-last _∙_ start n' generate) ⟩
        merge _∙_ (generate n' n<sn ∙ start) n' (λ i .i<n → generate i (≤-trans i<n n≤sn))          ≈⟨ merge-substitute _∙_ _∙'_ ∙-sim  (generate n' n<sn ∙ start) (generate' n' n<sn ∙' start') (∙-sim (generate-sim n' n<sn) start-sim) n' (λ i .i<n → generate i (≤-trans i<n n≤sn)) (λ i .i<n → generate' i (≤-trans i<n n≤sn)) (λ i .i<n' → generate-sim i (≤-trans i<n' n≤sn)) ⟩
        merge _∙'_ (generate' n' n<sn ∙' start') n' (λ i .i<n → generate' i (≤-trans i<n n≤sn))     ≈⟨ sym (reflexive (merge-consume-last _∙'_ start' n' generate')) ⟩
        merge _∙'_ start' n generate'                                                               ∎
        where
            open import Relation.Binary.Reasoning.Setoid A-setoid hiding (start)


Permutation : ℕ → Set
Permutation n = Bijection (discrete-setoid (FakeFin n)) (discrete-setoid (FakeFin n))

permute-then-generate :
    {A : Set α}
    (n : ℕ) →
    (generate : (i : ℕ) → .(i < n) → A) →
    (FakeFin n → FakeFin n) →
    (i : ℕ) → .(i < n) → A
permute-then-generate n generate p i i<n with p (i , squash i<n)
... | j , squash j<n = generate j j<n

permute-then-generate-substitute :
    {A : Set α}
    (n : ℕ) →
    (generate : (i : ℕ) → .(i < n) → A) →
    (p₁ : FakeFin n → FakeFin n) →
    (p₂ : FakeFin n → FakeFin n) →
    (∀ k → p₁ k ≡ p₂ k) →
    (i : ℕ) → .(i<n : i < n) →
    permute-then-generate n generate p₁ i i<n ≡ permute-then-generate n generate p₂ i i<n
permute-then-generate-substitute n generate p₁ p₂ p₁≈p₂ i i<n with p₁ (i , squash i<n) | inspect p₁ (i , squash i<n) | p₂ (i , squash i<n) | inspect p₂ (i , squash i<n)
... | j , squash j<n | [ j= ] | k , squash k<n | [ k= ] =
    generate j j<n                                      ≡⟨ irrelevant-cong (_< n) generate {j} {p₁-thing} {j<n} {p₁-thing<n} (≡-sym (proj₁≡ j=)) ⟩
    generate (p₁ (i , squash i<n) .proj₁) p₁-thing<n  ≡⟨ irrelevant-cong (_< n) generate {p₁-thing} {p₂-thing} {p₁-thing<n} {p₂-thing<n} (proj₁≡ (p₁≈p₂ (i , squash i<n))) ⟩
    generate (p₂ (i , squash i<n) .proj₁) p₂-thing<n  ≡⟨ irrelevant-cong (_< n) generate {p₂-thing} {k} {p₂-thing<n} {k<n} (proj₁≡ k=) ⟩
    generate k k<n  ∎
    where
        open ≡-Reasoning

        p₁-thing = p₁ (i , squash i<n) .proj₁
        p₁-thing<n = ≤-<-trans (≤-reflexive (proj₁≡ j=)) (≤-recompute j<n)

        p₂-thing = p₂ (i , squash i<n) .proj₁
        p₂-thing<n = ≤-<-trans (≤-reflexive (proj₁≡ k=)) (≤-recompute k<n)


module _
    {A-setoid : Setoid c ℓ}
    (∙-op : SetoidFunction₂ A-setoid A-setoid A-setoid)
    where

    open Setoid A-setoid using (_≈_; refl; sym; trans; reflexive) renaming (Carrier to A)
    open SetoidFunction₂ ∙-op using () renaming (func to _∙_; respects to ∙-cong)



    -- If f distributes over combine, then it distributes through merge
    merge-distribute-theorem :
        (start : A)
        (n : ℕ)
        (generate : (i : ℕ) → .(i < n) → A)
        (f : A → A) →
        DistributiveFunction A-setoid f _∙_ →
        f (merge _∙_ start n generate) ≈ merge _∙_ (f start) n (λ i i<n → f (generate i i<n))
    merge-distribute-theorem start zero generate f f-∙-distributes = refl
    merge-distribute-theorem start (suc n) generate f f-∙-distributes = begin
        f (merge _∙_ start (suc n) generate)                                                            ≈⟨ reflexive (cong f (merge-pop-first-lemma _∙_ start n generate)) ⟩
        f (generate zero (s≤s z≤n) ∙ merge _∙_ start n (λ i .i<n → generate (suc i) (s≤s i<n)))         ≈⟨ f-∙-distributes ⟩
        f (generate zero (s≤s z≤n)) ∙ f (merge _∙_ start n (λ i .i<n → generate (suc i) (s≤s i<n)))     ≈⟨ ∙-cong refl (merge-distribute-theorem start n (λ i .i<n → generate (suc i) (s≤s i<n)) f f-∙-distributes) ⟩
        f (generate zero (s≤s z≤n)) ∙ merge _∙_ (f start) n (λ i .i<n → f (generate (suc i) (s≤s i<n))) ≈⟨ reflexive (≡-sym (merge-pop-first-lemma _∙_ (f start) n (λ i .i<n → f (generate i i<n)))) ⟩
        merge _∙_ (f start) (suc n) (λ i .i<n → f (generate i i<n))                                     ∎
        where open import Relation.Binary.Reasoning.Setoid A-setoid hiding (start)

    merge-pop-last :
        Associative A-setoid _∙_ →
        (start : A) →
        Identity A-setoid _∙_ start →
        (n : ℕ)
        (generate : (i : ℕ) → .(i < suc n) → A) →
        merge _∙_ start (suc n) generate ≈ merge _∙_ start n (λ i i<n → generate i (<-≤-trans i<n n≤sn)) ∙ generate n n<sn
    merge-pop-last ∙-assoc id (id-is-left-∙-id , id-is-right-∙-id) zero generate = trans id-is-right-∙-id (sym id-is-left-∙-id)
    merge-pop-last ∙-assoc id id-is-∙-id (suc n) generate = begin
        merge _∙_ id (suc (suc n)) generate                                                         ≈⟨ reflexive (merge-pop-first-lemma _∙_ id (suc n) generate) ⟩
        generate zero _ ∙ merge _∙_ id (suc n) (λ i .i<n → generate (suc i) _)                      ≈⟨ ∙-cong refl (merge-pop-last ∙-assoc id id-is-∙-id n (λ i .i<n → generate (suc i) _)) ⟩
        generate zero _ ∙ (merge _∙_ id n (λ i .i<n → generate (suc i) _) ∙ generate (suc n) _)     ≈⟨ ∙-assoc ⟩
        (generate zero _ ∙ merge _∙_ id n (λ i .i<n → generate (suc i) _)) ∙ generate (suc n) _     ≈⟨ ∙-cong (reflexive (≡-sym (merge-pop-first-lemma _∙_ id n (λ i .i<n → generate i _)))) refl ⟩
        merge _∙_ id (suc n) (λ i .i<n → generate i _) ∙ generate (suc n) _                         ∎
        where open import Relation.Binary.Reasoning.Setoid A-setoid

    {-
        Permutation? then generate can go through a pair-generation step,
        and permutation of that can be used for permutation of indices.
    -}


        -- permute-then-generate : (n : ℕ) →
        --     (generate : (i : ℕ) → .(i < n) → A) → Permutation n →
        --     (i : ℕ) → .(i < n) → A
        -- permute-then-generate n generate p i i<n with p .Bijection.to (i , squash i<n)
        -- ... | j , squash j<n = generate j j<n

    -- merge-permute-telescope-lemma :
    --     (start : A)
    --     (n : ℕ)
    --     (generate : (i : ℕ) → .(i < n) → A) →
    --     {B : Set β} →
    --     (p : B → B)
    --     (g : B → FakeFin n) →
    --     (f : FakeFin n → B) →
    --     merge _∙_ start n (permute-then-generate n generate (g ∘ p ∘ f)) ≈
    --     merge _∙_ start n (permute-then-generate n generate p)

    merge-permute-theorem :
        Associative A-setoid _∙_ →
        Commutative A-setoid _∙_ →
        (id : A) →
        Identity A-setoid _∙_ id →
        (n : ℕ)
        (generate : (i : ℕ) → .(i < n) → A) →
        (p : Permutation n) →
        merge _∙_ id n (permute-then-generate n generate (p .Bijection.to)) ≈
        merge _∙_ id n generate
    merge-permute-theorem ∙-assoc ∙-comm id ∙-id n generate p = {!   !}
        where
            lemma :
                (l : FlipList n) →
                merge _∙_ id n (permute-then-generate n generate (flip-swap-using-list l)) ≈
                merge _∙_ id n generate
            lemma = ?

        --  begin
        -- merge _∙_ id n (permute-then-generate n generate f)                                             ≈⟨ {!   !} ⟩
        -- merge _∙_ id n (permute-then-generate n generate (falsify ∘ realize ∘ f ∘ falsify ∘ realize))   ≈⟨ merge-substitute-generate n (permute-then-generate n generate (falsify ∘ realize ∘ f ∘ falsify ∘ realize)) (permute-then-generate n generate (falsify ∘ swap-with-list l ∘ realize)) {!   !} ⟩
        -- merge _∙_ id n (permute-then-generate n generate (falsify ∘ swap-with-list l ∘ realize))        ≈⟨ {!   !} ⟩
        -- merge _∙_ id n generate                                                                         ∎
        -- where
        --     open SwapList
        --     open import Relation.Binary.Reasoning.Setoid A-setoid

        --     merge-substitute-generate = merge-substitute A-setoid _∙_ _∙_ ∙-cong id id refl

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