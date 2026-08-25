open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; cong; cong-app; subst; refl; sym; trans; inspect; [_]; ≢-sym)
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
open import Data.Nat.Properties using (module ≤-Reasoning; ≤-isDecTotalOrder; <-cmp; suc-pred; ≤-reflexive; ≤-refl; ≤-trans; ≤-<-trans; <-≤-trans; <-trans; ≰⇒≥; <⇒≱; ≮⇒≥; <⇒≤; ≰⇒>; ≤-antisym; <-irrefl; +-mono-≤; +-mono-<; +-mono-≤-<; ∸-mono; +-suc; +-comm; +-assoc; n>0⇒n≢0; n∸n≡0; ≤∧≢⇒<; m≤n+m; m∸n≤m; m≤m+n; m+n≤o⇒m≤o; m+n≤o⇒n≤o; m<n⇒0<n∸m; m+n∸n≡m; m+[n∸m]≡n; +-∸-assoc; ∸-monoʳ-<; m∸[m∸n]≡n; m∸n+n≡m)
open import Data.List using (List; foldl; _∷_; []; _∷ʳ_; length; lookup; drop; _++_; reverse; tabulate; map)
open import Data.List.Properties using (drop-drop; reverse-++; ++-identity; foldl-map; foldl-∷ʳ; foldl-cong; map-++)
open import Data.List.Relation.Unary.All using (All)

open import Plasmaduck.SetoidExperiment.SetoidMachinery using (discrete-setoid; from-discrete-cong; SetoidFunction₂; _which-is-cong₂_; _←₂_; SetoidFunction; _which-is-cong_; _←_; property-subset-setoid; discrete-function-setoid)
open import Plasmaduck.Function.Properties using (module SingleOperator)
open import Plasmaduck.Util.Case using (case_of_)
open import Plasmaduck.Data.Empty using (¬-recompute; ⊥-recompute; ⊥-irr-elim)
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
open import Plasmaduck.Counting.Permutation.SwapList using (SwapList; IsValidSwapList; IsSwapDecomposition; IsValidSwapList-reverse; swap-with-list; swap-pop-initial; swap-with-list-bijective; swap-with-list-reverse-is-right-inverse; swap-with-list-nfunc)
open import Plasmaduck.Counting.Permutation.Defs using (IsNFunc; IsNFuncLower; IsNFuncPermutation)



module Plasmaduck.Counting.Permutation.SwapPermutation where

variable
    m n : ℕ


module Monotonicity where
    StrictlyMonotonicNFuncLower : ℕ → (ℕ → ℕ) → Set
    StrictlyMonotonicNFuncLower n f = IsNFuncLower n f × ∀ (i j : ℕ) → .(i<j : i < j) → .(j<m : j < n) → f i < f j

    private
        strictly-monotonic⇒is-not-lt : (f : ℕ → ℕ) → StrictlyMonotonicNFuncLower n f →
            ∀ k → .(k<n : k < n) → ¬ f k < k
        strictly-monotonic⇒is-not-lt f f-monotonic zero k<n = λ ()
        strictly-monotonic⇒is-not-lt {n = n} f f-monotonic k@(suc k') k<n fk<k = strictly-monotonic⇒is-not-lt f f-monotonic k' k'<n (begin
            suc (f k')  ≤⟨ f-monotonic .proj₂ k' k n<sn k<n ⟩
            f k         ≤⟨ s≤s⁻¹ fk<k ⟩
            k'          ∎)
            where
                open ≤-Reasoning
                k'<n : k' < n
                k'<n = ≤-trans n≤sn (≤-recompute k<n)

        strictly-monotonic⇒is-not-gt : (f : ℕ → ℕ) → StrictlyMonotonicNFuncLower n f →
            ∀ k → (k<n : k < n) → ¬ f k > k
        strictly-monotonic⇒is-not-gt {n = n} f f-monotonic k k<n fk>k = helper (pred n ∸ k) ((≤-trans (s≤s (m∸n≤m (pred n) k)) (≤-reflexive spn=n))) (subst (λ q → f q > q) {k} {pred n ∸ (pred n ∸ k)} (sym (m∸[m∸n]≡n {pred n} {k} (s≤s⁻¹ (<-≤-trans k<n (≤-reflexive (sym spn=n)))))) fk>k)
            where
                n-is-not-zero : NonZero n
                n-is-not-zero = >-nonZero (≤-<-trans z≤n (≤-recompute k<n))

                spn=n : suc (pred n) ≡ n
                spn=n = suc-pred n {{n-is-not-zero}}

                pred-n<n : pred n < n
                pred-n<n = ≤-reflexive spn=n

                reduce-<n : {k : ℕ} → suc k < n → k < pred n
                reduce-<n sk<n = s≤s⁻¹ (<-≤-trans sk<n (≤-reflexive (sym spn=n)))

                reduce-≤n : {k : ℕ} → suc k ≤ n → k ≤ pred n
                reduce-≤n sk≤n = s≤s⁻¹ (≤-trans sk≤n (≤-reflexive (sym spn=n)))

                helper : ∀ k → .(k<n : k < n) → ¬ f (pred n ∸ k) > pred n ∸ k
                helper zero k<n f[n∸1]>n∸1 = <-irrefl refl (<-≤-trans (f-monotonic .proj₁ (≤-reflexive spn=n)) (≤-trans (≤-reflexive (sym spn=n)) f[n∸1]>n∸1))
                helper k@(suc k') k<n thing = <⇒≱ thing (s≤s⁻¹ (begin
                    suc (f (pred n ∸ k)) ≤⟨ f-monotonic .proj₂ (pred n ∸ k) (pred n ∸ k') (∸-monoʳ-< {pred n} {k} {k'} n<sn (reduce-<n k<n)) (≤-<-trans (m∸n≤m (pred n) k') pred-n<n) ⟩
                    f (pred n ∸ k') ≤⟨ ≮⇒≥ (helper k' (≤-<-trans n≤sn k<n)) ⟩
                    pred n ∸ k'            ≡⟨ sym (∸-suc (pred n) k (reduce-<n k<n)) ⟩
                    suc (pred n ∸ k) ∎))
                    where open ≤-Reasoning

    strictly-monotonic⇒is-id : (f : ℕ → ℕ) → StrictlyMonotonicNFuncLower n f →
        ∀ k → .(k<n : k < n) → f k ≡ k
    strictly-monotonic⇒is-id f f-monotonic k k<n with <-cmp (f k) k
    ... | tri< fk<k _ _ = ⊥-elim (strictly-monotonic⇒is-not-lt f f-monotonic k k<n fk<k)
    ... | tri≈ _ fk=k _ = fk=k
    ... | tri> _ _ fk>k = ⊥-elim (⊥-recompute (strictly-monotonic⇒is-not-gt f f-monotonic k k<n fk>k))


module _ where
    open import Plasmaduck.Counting.Permutation.SwapSort ≤-isDecTotalOrder using (module SwapDecomposition)
    open SwapDecomposition using (partial-decomposition; partial-decomposition-valid; partial-decomposition-monotonic-theorem)
    open Monotonicity

    decompose-inverse : ℕ → (ℕ → ℕ) → SwapList
    decompose-inverse zero f = []
    decompose-inverse n@(suc n') f = partial-decomposition f n' []

    decompose-permutation : ℕ → (ℕ → ℕ) → SwapList
    decompose-permutation n f = reverse (decompose-inverse n f)

    decompose-inverse-valid :
        (n : ℕ) → (f : ℕ → ℕ) →
        IsValidSwapList n (decompose-inverse n f)
    decompose-inverse-valid zero f = All.[]
    decompose-inverse-valid n@(suc n') f = partial-decomposition-valid f n' n<sn [] All.[]

    decompose-permutation-valid :
        (n : ℕ) → (f : ℕ → ℕ) →
        IsValidSwapList n (decompose-permutation n f)
    decompose-permutation-valid n f = IsValidSwapList-reverse (decompose-inverse-valid n f)

    -- This statement is stronger than the lemma in SwapSort,
    -- since we're working with a injective(?) function,
    -- rather than an arbitrary one.
    partial-decomposition-strictly-monotonic-theorem :
        {n : ℕ}
        (f : ℕ → ℕ) →
        Injective _≡_ _≡_ f →
        ∀ (i j : ℕ) → .(i<j : i < j) → .(j<n : j < n) →
        ((f ∘ (swap-with-list (decompose-inverse n f))) i) <
        ((f ∘ (swap-with-list (decompose-inverse n f))) j)
    partial-decomposition-strictly-monotonic-theorem {n = n@(suc n')} f f-surj i j i<j j<n =
        case
            ≤→<≡ (partial-decomposition-monotonic-theorem f n' [] i j (<⇒≤ i<j) (s≤s⁻¹ j<n))
        of λ {
            (inj₁ case<) → case<;
            (inj₂ case=) → ⊥-irr-elim (<-irrefl (swap-with-list-bijective (decompose-inverse n f) .proj₁ (f-surj case=)) i<j)
        }

    decompose-inverse-is-right-inverse :
        {n : ℕ}
        (f : ℕ → ℕ) →
        IsNFuncPermutation n f →
        ∀ k → .(k < n) → (f ∘ swap-with-list (decompose-inverse n f)) k ≡ k
    decompose-inverse-is-right-inverse {n = n@(suc n')} f ((f-nfunc-lower , _) , (f-inj , _)) k k<n = strictly-monotonic⇒is-id (f ∘ swap-with-list (decompose-inverse n f)) (f-nfunc-lower ∘ (swap-with-list-nfunc {n} (decompose-inverse n f) (partial-decomposition-valid f n' n<sn [] All.[])) .proj₁ , partial-decomposition-strictly-monotonic-theorem {n} f f-inj) k k<n

    is-permutation-decomposition :
        {n : ℕ}
        (f : ℕ → ℕ) →
        IsNFuncPermutation n f →
        IsSwapDecomposition f (decompose-permutation n f)
    is-permutation-decomposition {n = zero} f f-perm@((_ , f-nfunc-upper) , _) k = sym (f-nfunc-upper {k} z≤n)
    is-permutation-decomposition {n = n@(suc n')} f f-perm@((_ , f-nfunc-upper) , _) k with ≤-cmp n k
    ... | inj₁ n≤k =
        swap-with-list (reverse l) k    ≡⟨ swap-with-list-nfunc {n} (reverse l) (IsValidSwapList-reverse {n} {l} (partial-decomposition-valid f n' n<sn [] All.[])) .proj₂ {k} n≤k ⟩
        k                               ≡⟨ sym (f-nfunc-upper {k} n≤k) ⟩
        f k                             ∎
        where
            open ≡-Reasoning
            l = partial-decomposition f n' []
    ... | inj₂ n>k =
        swap-with-list (reverse l) k                            ≡⟨ sym (decompose-inverse-is-right-inverse {n} f f-perm (swap-with-list (reverse l) k) (swap-with-list-nfunc {n} (reverse l) (IsValidSwapList-reverse {n} {l} (partial-decomposition-valid f n' n<sn [] All.[])) .proj₁ {k} n>k)) ⟩
        (f ∘ swap-with-list l ∘ swap-with-list (reverse l)) k   ≡⟨ cong f (swap-with-list-reverse-is-right-inverse l k) ⟩
        f k                                                     ∎
        where
            open ≡-Reasoning
            l = partial-decomposition f n' []
