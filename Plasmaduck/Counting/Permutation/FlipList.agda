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
open import Plasmaduck.Data.Squash using (irrelevant-inspect)
open import Plasmaduck.Util.TypeChange using (change-type; change-type-input-dependence-irrelevance; change-type-output-dependence-commute; change-type-proof-irrelevance; cong₂-dependent)
open import Plasmaduck.Relation.Equivalence using (irrelevant-cong; irrelevant-cong₂)
open import Plasmaduck.Function.Bijection using (_∘-bijective_; id-bijective; bijective-is-functional)
open import Plasmaduck.Function using (_≈_; ≈-sym)


open import Plasmaduck.Counting.Permutation.Swap using (swp; swp-flip; swp-matchₐ-lemma; swp-contract-three')



module Plasmaduck.Counting.Permutation.FlipList where

variable
    a b c : Level
    m n : ℕ


flip : {i n : ℕ} → .(i < n) → Fin (sucℕ n) → Fin (sucℕ n)
flip {i = i} i<n x = swp (fromℕ< {i} (<-trans i<n n<sn)) (fromℕ< {sucℕ i} (s≤s i<n)) x

-- Using flips, swap index i with index i + j
flip-swap : {n i j : ℕ} → .(j + i ≤ n) → Fin (sucℕ n) → Fin (sucℕ n)
flip-swap {n} {i} {zeroℕ} j+i≤n = id
flip-swap {n} {i} {sucℕ zeroℕ} j+i≤n = flip {i} j+i≤n
flip-swap {n} {i} {sucℕ (sucℕ j)} j+i≤n = flip {sucℕ j + i} j+i≤n ∘ flip-swap {n} {i} {sucℕ j} (≤-trans n≤sn j+i≤n) ∘ flip {sucℕ j + i} j+i≤n

IsDecompositionOfSwap : (i j : Fin (sucℕ n)) → (Fin (sucℕ n) → Fin (sucℕ n)) → Set
IsDecompositionOfSwap {n = n} i j p = ∀ (k : Fin (sucℕ n)) → p k ≡ swp i j k

decompose-swap-helper : {n i j : ℕ} → .(i ≤ j) → .(j ≤ n) → Fin (sucℕ n) → Fin (sucℕ n)
decompose-swap-helper {n = n} {i = i} {j} i≤j j≤n = flip-swap {n} {i} {j ∸ i} (≤-trans (≤-reflexive (m∸n+n≡m {j} {i} i≤j)) j≤n)

decompose-swap : {i j : ℕ} → .(i ≤ n) → .(j ≤ n) → Fin (sucℕ n) → Fin (sucℕ n)
decompose-swap {i = i} {j} i≤n j≤n with ≤-cmp i j
... | inj₁ i≤j = decompose-swap-helper i≤j j≤n
... | inj₂ i>j = decompose-swap-helper (<⇒≤ i>j) i≤n

decompose-swap' : (i j : Fin n) → Fin n → Fin n
decompose-swap' {n = zeroℕ} ()
decompose-swap' {n = sucℕ _} i j = decompose-swap {i = toℕ i} {toℕ j} (s≤s⁻¹ (toℕ<n i)) (s≤s⁻¹ (toℕ<n j))

decompose-swap-arg-flip : {i j : ℕ} → .(i≤n : i ≤ n) → .(j≤n : j ≤ n) → decompose-swap i≤n j≤n ≡ decompose-swap j≤n i≤n
decompose-swap-arg-flip {n = n} {i = i} {j} i≤n j≤n with ≤-cmp i j | ≤-cmp j i
... | inj₂ i>j | inj₂ j>i = ⊥-elim (<-irrefl refl (<-trans i>j j>i))
... | inj₂ i>j | inj₁ j≤i = refl
... | inj₁ i≤j | inj₂ j>i = refl
... | inj₁ i≤j | inj₁ j≤i with i ≟ℕ j
...     | yes refl = refl
...     | no i≠j = ⊥-elim (i≠j (≤-antisym i≤j j≤i))

decompose-swap=decompose-swap-helper : {n i j : ℕ} → .(i≤j : i ≤ j) → .(j≤n : j ≤ n) → decompose-swap {n} {i} {j} (≤-trans i≤j j≤n) j≤n ≡ decompose-swap-helper {n} {i} {j} i≤j j≤n
decompose-swap=decompose-swap-helper {n = n} {i} {j} i≤j j≤n with ≤-cmp i j
... | inj₁ _ = refl
... | inj₂ i>j = ⊥-elim (<-irrefl refl (≤-<-trans (≤-recompute i≤j) i>j))

decompose-swap-helper-is-swap-decomposition : {i j : ℕ} → .(i≤j : i ≤ j) → .(j≤n : j ≤ n) → IsDecompositionOfSwap (fromℕ< {i} (s≤s (≤-trans i≤j j≤n))) (fromℕ< {j} (s≤s j≤n)) (decompose-swap-helper i≤j j≤n)
decompose-swap-helper-is-swap-decomposition {n = n} {i = i@zeroℕ} {j = j@zeroℕ} i≤j j≤n k = sym (swp-matchₐ-lemma zero-fin k)
decompose-swap-helper-is-swap-decomposition {n = n@(sucℕ n')} {i = i} {j = j@(sucℕ j')} i≤j j≤n k with i ≟ℕ j | i ≟ℕ j'
... | yes refl | _ =
    decompose-swap-helper {n} {j} {j} i≤j j≤n k     ≡⟨⟩
    flip-swap {n} {j} {j ∸ j} j∸j+j≤n k             ≡⟨ irrelevant-cong (λ q → q + j ≤ n) (λ q q+j≤n → flip-swap {n} {j} {q} q+j≤n k) {j ∸ j} {0} {j∸j+j≤n} {j≤n} (n∸n≡0 j) ⟩
    flip-swap {n} {j} {0} j≤n k                     ≡⟨⟩
    k                                               ≡⟨ sym (swp-matchₐ-lemma (fromℕ< {j} j<sn) k) ⟩
    swp (fromℕ< {j} j<sn) (fromℕ< {j} j<sn) k       ∎
    where
        j∸j+j≤n : j ∸ j + j ≤ n
        j∸j+j≤n = ≤-trans (≤-reflexive (m∸n+n≡m {j} {j} n≤n)) (≤-recompute j≤n)

        j<sn : j < sucℕ n
        j<sn = s≤s (≤-recompute j≤n)
        open ≡-Reasoning

... | no i≠j | yes refl =
    decompose-swap-helper {n} {j'} {j} i≤j j≤n k    ≡⟨⟩
    flip-swap {n} {j'} {j ∸ j'} j∸j'+j'≤n k         ≡⟨ irrelevant-cong (λ q → q + j' ≤ n) (λ q q+j'≤n → flip-swap {n} {j'} {q} q+j'≤n k) {j ∸ j'} {1} {j∸j'+j'≤n} {j≤n} (trans (sym (∸-suc j j n≤n)) (cong sucℕ (n∸n≡0 j))) ⟩
    flip-swap {n} {j'} {1} j≤n k                    ≡⟨⟩
    flip {j'} j'<n k                                ≡⟨⟩
    swp (fromℕ< {j'} j'<sn) (fromℕ< {j} j<sn) k     ∎
    where
        j'<n : j' < n
        j'<n = ≤-recompute j≤n

        j<sn : j < sucℕ n
        j<sn = s≤s j'<n

        j'<sn : j' < sucℕ n
        j'<sn = ≤-<-trans n≤sn j<sn

        j∸j'+j'≤n : j ∸ j' + j' ≤ n
        j∸j'+j'≤n = ≤-trans (≤-reflexive (m∸n+n≡m {j} {j'} n≤sn)) (≤-recompute j≤n)

        open ≡-Reasoning
...  | no i≠j | no i≠j' =
    decompose-swap-helper {n} {i} {j} i≤j j≤n k                 ≡⟨⟩
    flip-swap {n} {i} {sucℕ j' ∸ i} j∸i+i≤n k                   ≡⟨ irrelevant-cong (λ q → q + i ≤ n) (λ q q+i≤n → flip-swap {n} {i} {q} q+i≤n k) {sucℕ j' ∸ i} {sucℕ (sucℕ (j'')) ∸ i} {j∸i+i≤n} {ssj''∸i+i≤n} (cong (λ q → sucℕ q ∸ i) (sym sj''=j')) ⟩
    flip-swap {n} {i} {sucℕ (sucℕ (j'')) ∸ i} ssj''∸i+i≤n k     ≡⟨ irrelevant-cong (λ q → q + i ≤ n) (λ q q+i≤n → flip-swap {n} {i} {q} q+i≤n k) {sucℕ (sucℕ (j'')) ∸ i} {sucℕ (sucℕ (j'' ∸ i))} {ssj''∸i+i≤n} {ss[j''∸i+i]≤n} (trans (sym (∸-suc (sucℕ j'') i i≤sj'')) (cong sucℕ (sym (∸-suc j'' i i≤j'')))) ⟩
    flip-swap {n} {i} {sucℕ (sucℕ (j'' ∸ i))} ss[j''∸i+i]≤n k   ≡⟨⟩
    (flip {sucℕ (j'' ∸ i) + i} s[j''∸i+i]<n ∘ flip-swap {n} {i} {sucℕ (j'' ∸ i)} s[j''∸i+i]≤n ∘ flip {sucℕ (j'' ∸ i) + i} s[j''∸i+i]<n) k   ≡⟨ cong (λ q → (q ∘ flip-swap {n} {i} {sucℕ (j'' ∸ i)} s[j''∸i+i]≤n ∘ q) k) flip= ⟩
    (flip {j'} j'<n ∘ flip-swap {n} {i} {sucℕ (j'' ∸ i)} s[j''∸i+i]≤n   ∘ flip {j'} j'<n) k     ≡⟨ cong (λ q → (flip {j'} j'<n ∘ q ∘ flip {j'} j'<n) k) (irrelevant-cong (λ q → q + i ≤ n) (λ q q+i≤n → flip-swap {n} {i} {q} q+i≤n) {sucℕ (j'' ∸ i)} {j' ∸ i} {s[j''∸i+i]≤n} {j'∸i+i≤n} (trans (∸-suc j'' i i≤j'') (cong (_∸ i) sj''=j'))) ⟩
    (flip {j'} j'<n ∘ flip-swap {n} {i} {j' ∸ i} j'∸i+i≤n               ∘ flip {j'} j'<n) k     ≡⟨⟩
    (flip {j'} j'<n ∘ decompose-swap-helper {n} {i} {j'} i≤j' j'≤n      ∘ flip {j'} j'<n) k     ≡⟨ cong (flip {j'} j'<n) (decompose-swap-helper-is-swap-decomposition {n} {i} {j'} i≤j' j'≤n (flip {j'} j'<n k)) ⟩
    (flip {j'} j'<n ∘ swp (fromℕ< {i} i<sn) (fromℕ< {j'} j'<sn)         ∘ flip {j'} j'<n) k     ≡⟨ swp-contract-three' {i = fromℕ< {j} j<sn} {j = fromℕ< {j'} j'<sn} {k = fromℕ< {i} i<sn} (λ fj=fi → i≠j (sym (fromℕ<-injective j i {sucℕ n} j<sn i<sn fj=fi))) (λ fj'=fi → i≠j' (sym (fromℕ<-injective j' i {sucℕ n} j'<sn i<sn fj'=fi))) k ⟩
    swp (fromℕ< {i} i<sn) (fromℕ< {j} j<sn) k                                                   ∎
    where
        i<j : i < j
        i<j with ≤→<≡ i≤j
        ... | inj₁ i<j = i<j
        ... | inj₂ i=j = ⊥-elim (i≠j i=j)

        i<j' : i < j'
        i<j' with ≤→<≡ (s≤s⁻¹ i<j)
        ... | inj₁ i<j' = i<j'
        ... | inj₂ i=j' = ⊥-elim (i≠j' i=j')


        j'' : ℕ
        j'' = predℕ j'

        sj''=j' : sucℕ j'' ≡ j'
        sj''=j' = sym (m≡spm {j'} (n>0⇒n≢0 (≤-<-trans z≤n i<j')))

        i≤n : i ≤ n
        i≤n = ≤-trans (≤-recompute i≤j) (≤-recompute j≤n)

        i<sn : i < sucℕ n
        i<sn = ≤-<-trans i≤n n<sn

        j<sn : j < sucℕ n
        j<sn = s≤s (≤-recompute j≤n)

        j'<n : j' < n
        j'<n = ≤-recompute j≤n

        j'<sn : j' < sucℕ n
        j'<sn = <-trans j'<n n<sn

        j'≤n : j' ≤ n
        j'≤n = ≤-trans n≤sn (≤-recompute j≤n)

        i≤j'' : i ≤ j''
        i≤j'' with ≤→<≡ i≤j
        ... | inj₂ i=j = ⊥-elim (i≠j i=j)
        ... | inj₁ i<j with ≤→<≡ (s≤s⁻¹ i<j)
        ...     | inj₂ i=j' = ⊥-elim (i≠j' i=j')
        ...     | inj₁ i<j' = s≤s⁻¹ (<-≤-trans i<j' (≤-reflexive (sym sj''=j')))

        i≤sj'' : i ≤ sucℕ j''
        i≤sj'' = ≤-trans i≤j'' n≤sn

        i≤j' : i ≤ j'
        i≤j' = ≤-trans i≤sj'' (≤-reflexive sj''=j')


        j∸i+i≤n : j ∸ i + i ≤ n
        j∸i+i≤n = ≤-trans (≤-reflexive (m∸n+n≡m {j} {i} (≤-recompute i≤j))) (≤-recompute j≤n)

        ssj''∸i+i≤n : sucℕ (sucℕ j'') ∸ i + i ≤ n
        ssj''∸i+i≤n = ≤-trans (≤-reflexive (cong (λ q → sucℕ q ∸ i + i) sj''=j')) j∸i+i≤n

        ss[j''∸i+i]≤n : sucℕ (sucℕ (j'' ∸ i + i)) ≤ n
        ss[j''∸i+i]≤n = ≤-trans (≤-reflexive (trans (cong (sucℕ ∘ sucℕ) (m∸n+n≡m {j''} {i} i≤j'')) (cong sucℕ sj''=j'))) (≤-recompute j≤n)

        s[j''∸i+i]<n : sucℕ (j'' ∸ i + i) < n
        s[j''∸i+i]<n = ss[j''∸i+i]≤n

        s[j''∸i+i]≤n : sucℕ (j'' ∸ i + i) ≤ n
        s[j''∸i+i]≤n = <⇒≤ s[j''∸i+i]<n

        j'∸i+i≤n : j' ∸ i + i ≤ n
        j'∸i+i≤n = ≤-trans (≤-reflexive (m∸n+n≡m {j'} {i} i≤j')) j'≤n

        flip= : flip {sucℕ (j'' ∸ i) + i} s[j''∸i+i]<n ≡ flip {j'} j'<n
        flip= = irrelevant-cong (_< n) (λ q q<n → flip {q} q<n) {sucℕ (j'' ∸ i) + i} {j'} {s[j''∸i+i]<n} {j'<n} (trans (cong sucℕ (m∸n+n≡m {j''} {i} i≤j'')) sj''=j')

        open ≡-Reasoning

decompose-swap-is-swap-decomposition : {i j : ℕ} → .(i≤n : i ≤ n) → .(j≤n : j ≤ n) → IsDecompositionOfSwap (fromℕ< {i} (s≤s i≤n)) (fromℕ< {j} (s≤s j≤n)) (decompose-swap i≤n j≤n)
decompose-swap-is-swap-decomposition {n = n} {i} {j} i≤n j≤n k with ≤-cmp i j
... | inj₁ i≤j = decompose-swap-helper-is-swap-decomposition {n} {i} {j} i≤j j≤n k
... | inj₂ i>j =
    decompose-swap-helper {n} {j} {i} j≤i i≤n k             ≡⟨ decompose-swap-helper-is-swap-decomposition {n} {j} {i} j≤i i≤n k ⟩
    swp (fromℕ< {j} (s≤s j≤n)) (fromℕ< {i} (s≤s i≤n)) k     ≡⟨ swp-flip (fromℕ< {j} (s≤s j≤n)) (fromℕ< {i} (s≤s i≤n)) k ⟩
    swp (fromℕ< {i} (s≤s i≤n)) (fromℕ< {j} (s≤s j≤n)) k     ∎
    where
        open ≡-Reasoning
        j≤i : j ≤ i
        j≤i = <⇒≤ i>j


------------------------------------------------
-- Now we decompose swap into a list of flips --
------------------------------------------------

-- A list for flipping (1 + n) items
FlipList : ℕ → Set
FlipList n = List (FakeFin n)

-- Using flips, swap index i with index i + j
flip-swap-list-helper : {n i j : ℕ} → .(j + i ≤ n) → FlipList n
flip-swap-list-helper {n} {i} {zeroℕ} j+i≤n = []
flip-swap-list-helper {n} {i} {sucℕ zeroℕ} j+i≤n = (i , squash j+i≤n) ∷ []
flip-swap-list-helper {n} {i} {sucℕ (sucℕ j)} j+i≤n = (sucℕ j + i , squash j+i≤n) ∷ flip-swap-list-helper {n} {i} {sucℕ j} (≤-trans n≤sn j+i≤n) ++ (sucℕ j + i , squash j+i≤n) ∷ []

flip-swap-list-mapper : FakeFin n → (Fin (sucℕ n) → Fin (sucℕ n))
flip-swap-list-mapper (i , squash i≤n) = flip {i} i≤n

flip-swap-list-acc : (Fin (sucℕ n) → Fin (sucℕ n)) → FakeFin n → (Fin (sucℕ n) → Fin (sucℕ n))
flip-swap-list-acc = ∣ (λ g f → g ∘ f) ⟩- flip-swap-list-mapper
-- equivalent to: f ∘ flip-swap-list-mapper i

flip-swap-using-list : FlipList n → Fin (sucℕ n) → Fin (sucℕ n)
flip-swap-using-list {n = n} l = foldl flip-swap-list-acc id l

flip-swap-as-list :
    {n i j : ℕ} → .(j+i≤n : j + i ≤ n) →
    ∀ k → flip-swap {n} {i} {j} j+i≤n k ≡ flip-swap-using-list (flip-swap-list-helper {n} {i} {j} j+i≤n) k
flip-swap-as-list {n = n} {i} {zeroℕ} j+i≤n k = refl
flip-swap-as-list {n = n} {i} {sucℕ zeroℕ} j+i≤n k = refl
flip-swap-as-list {n = n} {i} {j@(sucℕ j'@(sucℕ j''))} j+i≤n k =
    flip-swap {n} {i} {j} j+i≤n k                                                                                                                                           ≡⟨⟩
    (flip {j' + i} j+i≤n ∘ flip-swap {n} {i} {j'} (≤-trans n≤sn j+i≤n) ∘ flip {j' + i} j+i≤n) k                                                                             ≡⟨ cong (flip {j' + i} j+i≤n) (flip-swap-as-list {n} {i} {j'} (≤-trans n≤sn j+i≤n) (flip {j' + i} j+i≤n k)) ⟩
    (flip {j' + i} j+i≤n ∘ flip-swap-using-list (flip-swap-list-helper {n} {i} {j'} (≤-trans n≤sn j+i≤n)) ∘ flip {j' + i} j+i≤n) k                                          ≡⟨ cong (λ q → (flip {j' + i} j+i≤n ∘ q ∘ flip {j' + i} j+i≤n) k) (sym (lemma (flip-swap-list-helper {n} {i} {j'} (≤-trans n≤sn j+i≤n)))) ⟩
    (flip {j' + i} j+i≤n ∘ foldl (λ g f → g ∘ f) id (map flip-swap-list-mapper (flip-swap-list-helper {n} {i} {j'} (≤-trans n≤sn j+i≤n))) ∘ flip {j' + i} j+i≤n) k          ≡⟨ sym (foldl-pop (discrete-function-setoid (Fin (sucℕ n)) (Fin (sucℕ n))) {λ g f → g ∘ f} (λ _ → refl) (λ {f} g=h x → cong f (g=h x)) (flip {j' + i} j+i≤n) id l-center (flip {j' + i} j+i≤n k)) ⟩
    (foldl (λ g f → g ∘ f) (flip {j' + i} j+i≤n) (map flip-swap-list-mapper (flip-swap-list-helper {n} {i} {j'} (≤-trans n≤sn j+i≤n))) ∘ flip {j' + i} j+i≤n) k             ≡⟨⟩
    (foldl (λ g f → g ∘ f) id (flip {j' + i} j+i≤n ∷ map flip-swap-list-mapper (flip-swap-list-helper {n} {i} {j'} (≤-trans n≤sn j+i≤n))) ∘ flip {j' + i} j+i≤n) k          ≡⟨ cong-app (sym (foldl-∷ʳ (λ g f → g ∘ f) id (flip {j' + i} j+i≤n) l-left)) k ⟩
    foldl (λ g f → g ∘ f) id (flip {j' + i} j+i≤n ∷ map flip-swap-list-mapper (flip-swap-list-helper {n} {i} {j'} (≤-trans n≤sn j+i≤n)) ∷ʳ flip {j' + i} j+i≤n) k           ≡⟨ cong (λ q → foldl (λ g f → g ∘ f) id q k) (sym (map-++ flip-swap-list-mapper l'-left ((j' + i , squash j+i≤n) ∷ []))) ⟩
    foldl (λ g f → g ∘ f) id (map flip-swap-list-mapper ((j' + i , squash j+i≤n) ∷ flip-swap-list-helper {n} {i} {j'} (≤-trans n≤sn j+i≤n) ∷ʳ (j' + i , squash j+i≤n))) k   ≡⟨ cong-app (lemma l'-full) k ⟩
    flip-swap-using-list (flip-swap-list-helper {n} {i} {j} j+i≤n) k                                                                                                        ∎
    where
        open ≡-Reasoning
        l-center = map flip-swap-list-mapper (flip-swap-list-helper {n} {i} {j'} (≤-trans n≤sn j+i≤n))
        l-left = flip {j' + i} j+i≤n ∷ map flip-swap-list-mapper (flip-swap-list-helper {n} {i} {j'} (≤-trans n≤sn j+i≤n))
        l-full = flip {j' + i} j+i≤n ∷ map flip-swap-list-mapper (flip-swap-list-helper {n} {i} {j'} (≤-trans n≤sn j+i≤n)) ∷ʳ flip {j' + i} j+i≤n

        l'-center = flip-swap-list-helper {n} {i} {j'} (≤-trans n≤sn j+i≤n)
        l'-left = (j' + i , squash j+i≤n) ∷ flip-swap-list-helper {n} {i} {j'} (≤-trans n≤sn j+i≤n)
        l'-full = (j' + i , squash j+i≤n) ∷ flip-swap-list-helper {n} {i} {j'} (≤-trans n≤sn j+i≤n) ∷ʳ (j' + i , squash j+i≤n)

        lemma :
            {m : ℕ} → (l : List (FakeFin m)) →
            foldl (λ g f → g ∘ f) id (map flip-swap-list-mapper l) ≡
            flip-swap-using-list l
        lemma l =
            foldl (λ g f → g ∘ f) id (map flip-swap-list-mapper l)      ≡⟨ foldl-map (λ g f → g ∘ f) flip-swap-list-mapper id l ⟩
            (foldl (∣ (λ g f → g ∘ f) ⟩- flip-swap-list-mapper) id l)   ≡⟨⟩
            (foldl flip-swap-list-acc id l)                             ≡⟨⟩
            (flip-swap-using-list l)                                    ∎

flip-swap-list-helper-is-swap-decomposition : (i j : Fin (sucℕ n)) → .(i≤j : i ≤-fin j) → IsDecompositionOfSwap i j (flip-swap-using-list (flip-swap-list-helper {n} {toℕ i} {toℕ j ∸ toℕ i} (≤-trans (≤-reflexive (m∸n+n≡m {toℕ j} {toℕ i} i≤j)) (s≤s⁻¹ (toℕ<n j)))))
flip-swap-list-helper-is-swap-decomposition {n} i j i≤j k =
    flip-swap-using-list (flip-swap-list-helper {n} {toℕ i} {toℕ j ∸ toℕ i} i∸j+j≤n) k  ≡⟨ sym (flip-swap-as-list {n} {toℕ i} {toℕ j ∸ toℕ i} i∸j+j≤n k) ⟩
    flip-swap {n} {toℕ i} {toℕ j ∸ toℕ i} i∸j+j≤n k                                     ≡⟨⟩
    decompose-swap-helper {n} {toℕ i} {toℕ j} i≤j j≤n k                                 ≡⟨ decompose-swap-helper-is-swap-decomposition {n} {toℕ i} {toℕ j} i≤j j≤n k ⟩
    swp (fromℕ< (toℕ<n i)) (fromℕ< (toℕ<n j)) k                                         ≡⟨ cong (λ q → swp q (fromℕ< (toℕ<n j)) k) (fromℕ<-toℕ i (toℕ<n i)) ⟩
    swp i (fromℕ< (toℕ<n j)) k                                                          ≡⟨ cong (λ q → swp i q k) (fromℕ<-toℕ j (toℕ<n j)) ⟩
    swp i j k                                                                           ∎
    where
        open ≡-Reasoning
        j≤n : toℕ j ≤ n
        j≤n = s≤s⁻¹ (toℕ<n j)

        i∸j+j≤n : toℕ j ∸ toℕ i + toℕ i ≤ n
        i∸j+j≤n = ≤-trans (≤-reflexive (m∸n+n≡m {toℕ j} {toℕ i} (≤-recompute i≤j))) (s≤s⁻¹ (toℕ<n j))


-- using flips, swap indices i and j
flip-swap-list : Fin (sucℕ n) → Fin (sucℕ n) → FlipList n
flip-swap-list {n = n} i j with ≤-cmp (toℕ i) (toℕ j)
... | inj₁ i≤j = flip-swap-list-helper {n} {toℕ i} {toℕ j ∸ toℕ i} (≤-trans (≤-reflexive (m∸n+n≡m {toℕ j} {toℕ i} i≤j)) (s≤s⁻¹ (toℕ<n j)))
... | inj₂ i>j = flip-swap-list-helper {n} {toℕ j} {toℕ i ∸ toℕ j} (≤-trans (≤-reflexive (m∸n+n≡m {toℕ i} {toℕ j} (<⇒≤ i>j))) (s≤s⁻¹ (toℕ<n i)))

flip-swap-list-is-swap-decomposition : (i j : Fin (sucℕ n)) → IsDecompositionOfSwap i j (flip-swap-using-list (flip-swap-list i j))
flip-swap-list-is-swap-decomposition {n = n} i j k with ≤-cmp (toℕ i) (toℕ j)
... | inj₁ i≤j = flip-swap-list-helper-is-swap-decomposition i j i≤j k
... | inj₂ i>j =
    (flip-swap-using-list (flip-swap-list-helper {n} {toℕ j} {toℕ i ∸ toℕ j} i∸j+j≤n)) k    ≡⟨ flip-swap-list-helper-is-swap-decomposition j i (<⇒≤ i>j) k ⟩
    swp j i k                                                                               ≡⟨ swp-flip j i k ⟩
    swp i j k                                                                               ∎
    where
        open ≡-Reasoning
        i∸j+j≤n : toℕ i ∸ toℕ j + toℕ j ≤ n
        i∸j+j≤n = ≤-trans (≤-reflexive (m∸n+n≡m {toℕ i} {toℕ j} (<⇒≤ i>j))) (s≤s⁻¹ (toℕ<n i))
