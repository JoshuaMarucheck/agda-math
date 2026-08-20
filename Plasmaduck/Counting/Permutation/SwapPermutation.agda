open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; cong; cong-app; refl; sym; trans; inspect; [_]; ≢-sym)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open import Relation.Binary using (Setoid; Rel; IsEquivalence; IsDecTotalOrder; tri<; tri≈; tri>)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Function using (_∘_; _∋_; ∣_⟩-_; id; Bijective; Bijection; Injective; Surjective)
open import Data.Bool using (true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (ℕ; _≤_; _<_; _>_; z≤n; s≤s; s≤s⁻¹; _∸_; _+_; NonZero; >-nonZero) renaming (zero to zeroℕ; suc to sucℕ; pred to predℕ; _≟_ to _≟ℕ_)
open import Data.Nat.Properties using (module ≤-Reasoning; <-cmp; suc-pred; ≤-reflexive; ≤-refl; ≤-trans; ≤-<-trans; <-≤-trans; <-trans; ≰⇒≥; <⇒≱; ≮⇒≥; <⇒≤; ≰⇒>; ≤-antisym; <-irrefl; +-mono-≤; +-mono-<; +-mono-≤-<; ∸-mono; +-suc; +-comm; +-assoc; n>0⇒n≢0; n∸n≡0; ≤∧≢⇒<; m≤n+m; m∸n≤m; m≤m+n; m+n≤o⇒m≤o; m+n≤o⇒n≤o; m<n⇒0<n∸m; m+n∸n≡m; m+[n∸m]≡n; +-∸-assoc; ∸-monoʳ-<; m∸[m∸n]≡n; m∸n+n≡m)
open import Data.Fin using (Fin; _≟_; _≤?_; _<?_; toℕ; fromℕ<; _↑ˡ_; _↑ʳ_) renaming (zero to zero-fin; suc to suc-fin; pred to pred-fin; _<_ to _<-fin_; _≤_ to _≤-fin_; _≥_ to _≥-fin_)
open import Data.Fin.Properties using (toℕ-fromℕ<; fromℕ<-toℕ; fromℕ<-cong; toℕ<n; toℕ-injective; fromℕ<-injective) renaming (≤-isDecTotalOrder to ≤-fin-isDecTotalOrder)
open import Data.List using (List; foldl; _∷_; []; _∷ʳ_; length; lookup; drop; _++_; reverse; tabulate; map)
open import Data.List.Properties using (drop-drop; reverse-++; ++-identity; foldl-map; foldl-∷ʳ; foldl-cong; map-++)

open import Plasmaduck.SetoidExperiment.SetoidMachinery using (discrete-setoid; from-discrete-cong; SetoidFunction₂; _which-is-cong₂_; _←₂_; SetoidFunction; _which-is-cong_; _←_; property-subset-setoid; discrete-function-setoid)
open import Plasmaduck.Function.Properties using (module SingleOperator)
open import Plasmaduck.Util.Case using (case_of_)
open import Plasmaduck.Data.Empty using (¬-recompute)
open import Plasmaduck.Data.FakeFin using (FakeFin; realize; falsify)
open import Plasmaduck.Data.Squash using (Squash; squash)
open import Plasmaduck.Data.Nat using (≤-recompute; ≤-cmp; n≤n; n≤sn; n<sn; m≤n⇒m≤pn; m<n⇒m≢n; ≤→<≡; ≤≥⇒≡; ∸-suc; m∸n∸o≡m∸o∸n; m∸n∸o≡m∸[n+o]; m>0⇒m=sn; m≡spm; s≡s⁻¹; m<o∧n<p⇒s[m+o]<n+p)
open import Plasmaduck.Data.Fin using (toℕ<<n; _↑ˡ-inverted_; fromℕ<-↑ˡ-inverted)
open import Plasmaduck.Data.List using (drop-lookup; foldl-pop)
open import Plasmaduck.Data.Product using (Σ≡; ×≡; uncurry; curry)
open import Plasmaduck.Util.TypeChange using (change-type; change-type-input-dependence-irrelevance; change-type-output-dependence-commute; change-type-proof-irrelevance; cong₂-dependent)
open import Plasmaduck.Relation.Equivalence using (irrelevant-cong; irrelevant-cong₂)
open import Plasmaduck.Function.Bijection using (_∘-bijective_; id-bijective; bijective-is-functional)
open import Plasmaduck.Function using (_≈_; ≈-sym)

open import Plasmaduck.Counting.Permutation.Swap using (swp; swp-no-match⇒id; low-swp-is-low; swp-match₁-lemma)
open import Plasmaduck.Counting.Permutation.SwapList using (SwapList; IsSwapDecomposition; swap-with-list; swap-pop-initial; swap-with-list-bijective; swap-with-list-reverse-is-right-inverse)
open import Plasmaduck.Counting.Permutation.Defs using (Permutation)



module Plasmaduck.Counting.Permutation.SwapPermutation where

variable
    m n : ℕ


module Monotonicity where
    StrictlyMonotonicFin : (f : Fin m → Fin n) → Set
    StrictlyMonotonicFin {m = m} f = (∀ (i j : ℕ) → .(i<j : i < j) → .(j<m : j < m) → f (fromℕ< {i} (<-trans i<j j<m)) <-fin f (fromℕ< {j} j<m))

    private
        strictly-monotonic⇒is-not-lt : (f : Fin n → Fin n) → StrictlyMonotonicFin f →
            ∀ k → .(k<n : k < n) → ¬ toℕ (f (fromℕ< {k} k<n)) < k
        strictly-monotonic⇒is-not-lt f f-monotonic zeroℕ k<n = λ ()
        strictly-monotonic⇒is-not-lt {n = n} f f-monotonic k@(sucℕ k') k<n fk<k = strictly-monotonic⇒is-not-lt f f-monotonic k' k'<n (begin
            sucℕ (toℕ (f (fromℕ< {k'} k'<n)))   ≤⟨ f-monotonic k' k n<sn k<n ⟩
            (toℕ (f (fromℕ< {k} k<n)))          ≤⟨ s≤s⁻¹ fk<k ⟩
            k'                                  ∎)
            where
                open ≤-Reasoning
                k'<n : k' < n
                k'<n = ≤-trans n≤sn (≤-recompute k<n)

        strictly-monotonic⇒is-not-gt : (f : Fin n → Fin n) → StrictlyMonotonicFin f →
            ∀ k → .(k<n : k < n) → ¬ toℕ (f (fromℕ< {k} k<n)) > k
        strictly-monotonic⇒is-not-gt {n = n} f f-monotonic k k<n = λ fk>k → helper (predℕ n ∸ k) (≤-trans (s≤s (m∸n≤m (predℕ n) k)) (≤-reflexive spn=n)) (<-≤-trans (≤-<-trans (≤-reflexive (m∸[m∸n]≡n {predℕ n} {k} (reduce-≤n (≤-recompute k<n)))) fk>k) (≤-reflexive (irrelevant-cong (_< n) (λ q q<n → toℕ (f (fromℕ< {q} q<n))) {k} {predℕ n ∸ (predℕ n ∸ k)} {y = k<n} {z = ≤-<-trans (≤-reflexive (m∸[m∸n]≡n {predℕ n} {k} (reduce-≤n (≤-recompute k<n)))) k<n} (sym (m∸[m∸n]≡n {predℕ n} {k} (reduce-≤n (≤-recompute k<n)))))))
            where
                n-is-not-zero : NonZero n
                n-is-not-zero = >-nonZero (≤-<-trans z≤n (≤-recompute k<n))

                spn=n : sucℕ (predℕ n) ≡ n
                spn=n = suc-pred n {{n-is-not-zero}}

                pred-n<n : predℕ n < n
                pred-n<n = ≤-reflexive spn=n

                reduce-<n : {k : ℕ} → sucℕ k < n → k < predℕ n
                reduce-<n sk<n = s≤s⁻¹ (<-≤-trans sk<n (≤-reflexive (sym spn=n)))

                reduce-≤n : {k : ℕ} → sucℕ k ≤ n → k ≤ predℕ n
                reduce-≤n sk≤n = s≤s⁻¹ (≤-trans sk≤n (≤-reflexive (sym spn=n)))

                helper : ∀ k → .(k<n : k < n) → ¬ toℕ (f (fromℕ< {predℕ n ∸ k} (≤-<-trans (m∸n≤m (predℕ n) k) pred-n<n))) > predℕ n ∸ k
                helper zeroℕ k<n f[n∸1]>n∸1 = <⇒≱ (toℕ<n (f (fromℕ< {predℕ n} pred-n<n))) (≤-trans (≤-reflexive (sym spn=n)) f[n∸1]>n∸1)
                helper k@(sucℕ k') k<n thing = <⇒≱ thing (s≤s⁻¹ (begin
                    sucℕ (toℕ (f (fromℕ< {predℕ n ∸ k} (≤-<-trans (m∸n≤m (predℕ n) k) pred-n<n)))) ≤⟨ f-monotonic (predℕ n ∸ k) (predℕ n ∸ k') (∸-monoʳ-< {predℕ n} {k} {k'} n<sn (reduce-<n k<n)) (≤-<-trans (m∸n≤m (predℕ n) k') pred-n<n) ⟩
                    toℕ (f (fromℕ< {predℕ n ∸ k'} (≤-<-trans (m∸n≤m (predℕ n) k') pred-n<n))) ≤⟨ ≮⇒≥ (helper k' (≤-<-trans n≤sn k<n)) ⟩
                    predℕ n ∸ k'            ≡⟨ sym (∸-suc (predℕ n) k (reduce-<n k<n)) ⟩
                    sucℕ (predℕ n ∸ k) ∎))
                    where open ≤-Reasoning

    strictly-monotonic⇒is-id : (f : Fin n → Fin n) → StrictlyMonotonicFin f →
        ∀ k → .(k<n : k < n) → toℕ (f (fromℕ< {k} k<n)) ≡ k
    strictly-monotonic⇒is-id f f-monotonic k k<n with <-cmp (toℕ (f (fromℕ< {k} k<n))) k
    ... | tri< fk<k _ _ = ⊥-elim (strictly-monotonic⇒is-not-lt f f-monotonic k k<n fk<k)
    ... | tri≈ _ fk=k _ = fk=k
    ... | tri> _ _ fk>k = ⊥-elim (strictly-monotonic⇒is-not-gt f f-monotonic k k<n fk>k)


module _ where
    private
        module _ {n : ℕ} where
            open import Plasmaduck.Counting.Permutation.SwapSort (≤-fin-isDecTotalOrder {n}) using (module SwapDecomposition) public
    open SwapDecomposition using (partial-decomposition; partial-decomposition-monotonic-theorem)
    open Monotonicity

    decompose-inverse : (p : Permutation n) → SwapList n
    decompose-inverse {n = zeroℕ} p = []
    decompose-inverse {n = sucℕ n'} p = partial-decomposition (p .Bijection.to) n' n<sn []

    decompose-permutation : (p : Permutation n) → SwapList n
    decompose-permutation p = reverse (decompose-inverse p)

    -- This statement is stronger than the lemma in SwapSort,
    -- since we're working with a surjective function,
    -- rather than an arbitrary one.
    partial-decomposition-strictly-monotonic-theorem :
        (p : Permutation n) →
        ∀ (i j : ℕ) → .(i<j : i < j) → .(j<n : j < n) →
        ((p .Bijection.to ∘ (swap-with-list (decompose-inverse p))) (fromℕ< {i} (<-trans i<j j<n))) <-fin
        ((p .Bijection.to ∘ (swap-with-list (decompose-inverse p))) (fromℕ< {j} j<n))
    partial-decomposition-strictly-monotonic-theorem {n = n@(sucℕ n')} p i j i<j j<n =
        case
            ≤→<≡ (partial-decomposition-monotonic-theorem (p .Bijection.to) n' n<sn [] i j (<⇒≤ i<j) (s≤s⁻¹ j<n))
        of λ {
            (inj₁ case<) → case<;
            (inj₂ case=) → ⊥-elim (<-irrefl (fromℕ<-injective i j (<-trans i<j j<n) j<n (swap-with-list-bijective (decompose-inverse p) .proj₁ (p .Bijection.bijective .proj₁ (toℕ-injective case=)))) (≤-recompute i<j))
        }

    decompose-inverse-is-right-inverse : (p : Permutation n) → ∀ k → (p .Bijection.to ∘ swap-with-list (decompose-inverse p)) k ≡ k
    decompose-inverse-is-right-inverse {n = n@(sucℕ n')} p k =
        thing                               ≡⟨ sym (fromℕ<-toℕ thing (toℕ<n thing)) ⟩
        fromℕ< {toℕ thing} (toℕ<n thing)    ≡⟨ irrelevant-cong (_< n) (λ q q<n → fromℕ< {q} q<n) {y = toℕ<n thing} {z = toℕ<n (thing')} (cong (λ q → toℕ (p .Bijection.to (swap-with-list (decompose-inverse p) q))) (sym (fromℕ<-toℕ  k (toℕ<n k)))) ⟩
        fromℕ< {toℕ thing'} (toℕ<n thing')  ≡⟨ irrelevant-cong (_< n) (λ q q<n → fromℕ< {q} q<n) {y = toℕ<n (thing')} {z = toℕ<n k} (strictly-monotonic⇒is-id (p .Bijection.to ∘ swap-with-list (decompose-inverse p)) (partial-decomposition-strictly-monotonic-theorem p) (toℕ k) (toℕ<n k)) ⟩
        fromℕ< {toℕ k} (toℕ<n k)            ≡⟨ fromℕ<-toℕ k (toℕ<n k) ⟩
        k                                   ∎
        where
            open ≡-Reasoning

            thing = p .Bijection.to (swap-with-list (decompose-inverse p) k)
            thing' = p .Bijection.to (swap-with-list (decompose-inverse p) (fromℕ< {toℕ k} (toℕ<n k)))

    is-permutation-decomposition : (p : Permutation n) → IsSwapDecomposition (p .Bijection.to) (decompose-permutation p)
    is-permutation-decomposition {n = n@(sucℕ n')} p k =
        swap-with-list (reverse l) k                                            ≡⟨ sym (decompose-inverse-is-right-inverse p (swap-with-list (reverse l) k)) ⟩
        (p .Bijection.to ∘ swap-with-list l ∘ swap-with-list (reverse l)) k     ≡⟨ cong (p .Bijection.to) (swap-with-list-reverse-is-right-inverse l k) ⟩
        p .Bijection.to k                                                       ∎
        where
            open ≡-Reasoning
            l = partial-decomposition (p .Bijection.to) n' n<sn []
