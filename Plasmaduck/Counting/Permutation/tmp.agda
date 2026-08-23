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
open import Data.Nat using (ℕ; zero; suc; pred; _≟_; _≤_; _≥_; _<_; _>_; z≤n; s≤s; s≤s⁻¹; _∸_; _+_; NonZero; >-nonZero)
open import Data.Nat.Properties using (module ≤-Reasoning; <-cmp; suc-pred; ≤-reflexive; ≤-refl; ≤-trans; ≤-<-trans; <-≤-trans; <-trans; ≰⇒≥; <⇒≱; ≮⇒≥; <⇒≤; ≰⇒>; ≤-antisym; <-irrefl; +-mono-≤; +-mono-<; +-mono-≤-<; ∸-mono; +-suc; +-comm; +-assoc; n>0⇒n≢0; n∸n≡0; ≤∧≢⇒<; m≤n+m; m∸n≤m; m≤m+n; m+n≤o⇒m≤o; m+n≤o⇒n≤o; m<n⇒0<n∸m; m+n∸n≡m; m+[n∸m]≡n; +-∸-assoc; ∸-monoʳ-<; m∸[m∸n]≡n; m∸n+n≡m)
open import Data.List using (List; foldl; _∷_; []; _∷ʳ_; length; lookup; drop; _++_; reverse; tabulate; map)
open import Data.List.Properties using (drop-drop; reverse-++; ++-identity; foldl-map; foldl-∷ʳ; foldl-cong; map-++)
open import Data.List.Relation.Unary.All as All using (All)

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

open import Plasmaduck.Counting.Permutation.Defs using (IsNFuncLower)
open import Plasmaduck.Counting.Permutation.Swap using (swp; swp-no-match⇒id; low-swp-is-low; swp-match₁-lemma)
open import Plasmaduck.Counting.Permutation.SwapList using (SwapList; IsValidSwapList; IsValidSwapList-recompute; IsLowPair<; IsLowPair≤; swap-with-list; swap-with-list-nfunc; swap-with-things; swap-with-things-nfunc; swap-pop-initial; _IsValidSwapList-++_; ++-swap-split)



module Plasmaduck.Counting.Permutation.tmp {a b c : Level} {A : Set a} {_≈A_ : Rel A b} {_≤A_ : Rel A c} (≤A-decTotal : IsDecTotalOrder _≈A_ _≤A_) where

    open import Plasmaduck.Counting.Permutation.SwapSort ≤A-decTotal
    open FindMaxLower
    open SwapDecomposition

    open IsDecTotalOrder ≤A-decTotal using () renaming (
        _≤?_ to _≤A?_;
        _≟_ to _≟A_;
        reflexive to ≤A-reflexive;
        refl to ≤A-refl;
        trans to ≤A-trans;
        antisym to ≤A-antisym;
        isEquivalence to ≈A-isEquivalence
        )
    open IsEquivalence ≈A-isEquivalence using () renaming (
        reflexive to ≈A-reflexive;
        refl to ≈A-refl;
        sym to ≈A-sym;
        trans to ≈A-trans
        )

    partial-decomposition-monotonic-theorem :
        (f : (i : ℕ) → .(i < m) → A) → (o : ℕ) → .(o<m : o < m) → (l : SwapList) → (l-valid : IsValidSwapList m l) →
        ∀ (i j : ℕ) → .(i≤j : i ≤ j) → .(j≤o : j ≤ o) →
        f (swap-with-list (partial-decomposition f o o<m l l-valid) i) ? ≤A --  ( {i} (≤-<-trans (≤-trans i≤j j≤o) o<m))
        f (swap-with-list (partial-decomposition f o o<m l l-valid) j) ? -- (fromℕ< {j} (≤-<-trans j≤o o<m))
    partial-decomposition-monotonic-theorem f o o<m l l-valid zero zero i≤j j≤o = ≤A-refl
    partial-decomposition-monotonic-theorem {m = m} f o@(suc o') o<m l l-valid i j@(suc j') i≤j j≤o = begin
        f (swap-with-list (partial-decomposition f o o<m l l-valid) i) ?                                                                                                                                                               ≡⟨ cong (λ q → f (swap-with-list q (i))) (partial-decomposition-is-range f o o<m l) ⟩
        f (swap-with-list (partial-decomposition-range f o o<m l l-valid o n≤n) i) ?                                                                                                                                                   ≡⟨ irrelevant-cong (_≤ o) (λ q q≤o → f (swap-with-list (partial-decomposition-range f o o<m l q q≤o) (i))) {o} {j + (o ∸ j)} {n≤n} {≤-reflexive (m+[n∸m]≡n j≤o)} (sym (m+[n∸m]≡n (≤-recompute j≤o))) ⟩
        f (swap-with-list (partial-decomposition-range f o o<m l l-valid (j + (o ∸ j)) (≤-reflexive (m+[n∸m]≡n j≤o))) i) ?                                                                                                            ≡⟨ cong (λ q → f (swap-with-list q (i))) (+-range-split f o o<m l l-valid j (o ∸ j) (≤-reflexive (m+[n∸m]≡n j≤o))) ⟩
        f (swap-with-list (partial-decomposition-range f (o ∸ (o ∸ j)) (≤-<-trans (≤-reflexive (m∸[m∸n]≡n j≤o)) j<m) (partial-decomposition-range f o o<m l l-valid (o ∸ j) (m∸n≤m o j)) ? j (≤-reflexive (sym (m∸[m∸n]≡n j≤o)))) (i)) ?   ≡⟨ irrelevant-cong₂ (_< m) (j ≤_) (λ q q<m j≤q → f (swap-with-list (partial-decomposition-range f q q<m (partial-decomposition-range f o o<m l (o ∸ j) (m∸n≤m o j)) j j≤q) (i))) {o ∸ (o ∸ j)} {j} {≤-<-trans (≤-reflexive (m∸[m∸n]≡n (≤-recompute j≤o))) j<m} {j<m} {≤-reflexive (sym (m∸[m∸n]≡n (≤-recompute j≤o)))} {n≤n} (m∸[m∸n]≡n (≤-recompute j≤o)) ⟩
        f (swap-with-list (partial-decomposition-range f j j<m (partial-decomposition-range f o o<m l l-valid (o ∸ j) (m∸n≤m o j)) ? j n≤n) i) ?                                                                                         ≡⟨ cong (λ q → f (q (i))) (partial-decomposition-range-split-lemma f j j<m (partial-decomposition-range f o o<m l (o ∸ j) (m∸n≤m o j)) j n≤n) ⟩
        f ((swap-with-list l' ∘ swap-with-list (partial-decomposition-range (λ x x<m → f (swap-with-list (partial-decomposition-range f o o<m l l-valid (o ∸ j) (m∸n≤m o j)) x) ?) j j<m [] All.[] j n≤n)) i) ?                                            ≤⟨ find-max-lower-is-max (f ∘ swap-with-list l') {swap-with-list (partial-decomposition-range (f ∘ swap-with-list (partial-decomposition-range f o o<m l (o ∸ j) (m∸n≤m o j))) j j<m [] j n≤n) (i)} {j} (partial-decomposition-range-low-stays-low (f ∘ swap-with-list (partial-decomposition-range f o o<m l (o ∸ j) (m∸n≤m o j))) j j<m i j i≤j n≤n) j<m ⟩
        f (swap-with-list l' y) ?                                                                                             ≡⟨ cong (f ∘ swap-with-list l') (sym (swp-match₁-lemma j y)) ⟩
        f (swap-with-list l' (swp j y j)) ?                                                     ≡⟨ cong (λ q → f (q j)) (sym (swap-pop-initial id l' j y)) ⟩
        f (swap-with-list (pair-at f j j<m l' l'-valid ∷ l') j) ?                                                      ≡⟨ irrelevant-cong (_< m) (λ q q<m → f (swap-with-list (pair-at f q q<m l' ∷ l') j)) {j} {suc (o ∸ suc (o ∸ j))} {j<m} {thing<m} (sym thing≡j) ⟩
        f (swap-with-list (pair-at f (suc (o ∸ suc (o ∸ j))) thing<m l' l'-valid ∷ l') j) ?                          ≡⟨⟩
        f (swap-with-list (partial-decomposition-range f o o<m l l-valid (suc (o' ∸ j')) (s≤s (m∸n≤m o' j'))) j) ?    ≡⟨ irrelevant-cong (_≤ o) (λ q q≤o → f (swap-with-list (partial-decomposition-range f o o<m l q q≤o) j)) {suc (o' ∸ j')} {o ∸ j'} {s≤s (m∸n≤m o' j')} {m∸n≤m o j'} (∸-suc o' j' (s≤s⁻¹ j≤o)) ⟩
        f (swap-with-list (partial-decomposition-range f o o<m l l-valid (o ∸ j') (m∸n≤m o j')) j) ?                   ≡⟨ sym (cong f (partial-decomposition-swap-drop-lemma f o o<m l j' j n≤n (≤-trans n≤sn j≤o) j<m)) ⟩
        f (swap-with-list (partial-decomposition f o o<m l l-valid) j) ?                                               ∎
        where
            l' = partial-decomposition-range f o o<m l l-valid (o ∸ j) (≤-trans (m∸n≤m o' j') n≤sn)

            -- Eventually irrelevant proofs
            l'-valid = partial-decomposition-range-is-valid f o (≤-recompute o<m) l (IsValidSwapList-recompute l-valid) (o ∸ j) (≤-trans (m∸n≤m o' j') n≤sn)

            j<m : j < m
            j<m = ≤-<-trans (≤-recompute j≤o) (≤-recompute o<m)

            i<m : i < m
            i<m = ≤-<-trans (≤-recompute i≤j) j<m

            thing≡j : suc (o ∸ suc (o ∸ j)) ≡ j
            thing≡j =
                suc (o ∸ suc (o ∸ j))     ≡⟨ ∸-suc o (suc (o ∸ j)) (s≤s (m∸n≤m o' j')) ⟩
                o ∸ (o ∸ j)                 ≡⟨ m∸[m∸n]≡n {o} {j} (≤-recompute j≤o) ⟩
                j                           ∎
                where open ≡-Reasoning

            thing<m : suc (o ∸ suc (o ∸ j)) < m
            thing<m = ≤-<-trans (≤-reflexive thing≡j) j<m

            -- the core swap's other position
            y = find-max-lower (λ x x<m → f (swap-with-list l' x) ?) j j<m

            open ≤A-Reasoning
