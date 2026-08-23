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
open import Data.List.Relation.Unary.All using (All)

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
open import Plasmaduck.Counting.Permutation.SwapList using (SwapList; IsValidSwapList; IsValidSwapList-recompute; IsLowPair<; IsLowPair≤; swap-with-list; swap-with-list-nfunc; swap-pop-initial; _IsValidSwapList-++_; ++-swap-split)




module Plasmaduck.Counting.Permutation.SwapSort {a b c : Level} {A : Set a} {_≈A_ : Rel A b} {_≤A_ : Rel A c} (≤A-decTotal : IsDecTotalOrder _≈A_ _≤A_) where

variable
    m n : ℕ


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

_≥A_ : Rel A c
_≥A_ x y = y ≤A x

module ≤A-Reasoning where
    open import Relation.Binary.Reasoning.Syntax

    open begin-syntax _≤A_ Function.id public
    open ≡-syntax _≤A_ ((λ a≡b b≤c → ≤A-trans (≤A-reflexive (≈A-reflexive a≡b)) b≤c)) public
    open ≈-syntax {R = _≈A_} _≤A_ _≤A_ (λ a≈b b≤c → ≤A-trans (≤A-reflexive a≈b) b≤c) public
    open ≤-syntax _≤A_ _≤A_ ≤A-trans public
    open end-syntax _≤A_ ≤A-refl public


module FindMaxLower (f : (i : ℕ) → .(i < m) → A) where
    -- Finds the index of the maximum item of f, out of those below o
    -- I'm doing this explicitly because with abstraction interacts badly with irrelevance,
    -- especially when I'm trying to avoid exponential computation blow-up.
    find-max-lower : (o : ℕ) → .(o < m) → ℕ
    find-max-lower-yields-low : (o : ℕ) → .(o<m : o < m) → find-max-lower o o<m ≤ o
    find-max-lower-helper : (o : ℕ) → .(o < m) → (prev-max : ℕ) → .(prev-max≤o : prev-max ≤ o) → ℕ
    find-max-lower-helper-yields-low : (o : ℕ) → .(o<m : o < m) → (prev-max : ℕ) → (prev-max≤o : prev-max ≤ o) → find-max-lower-helper o o<m prev-max prev-max≤o ≤ o

    find-max-lower zero z<m = zero
    find-max-lower o@(suc o') o<m = find-max-lower-helper o o<m (find-max-lower o' (≤-trans n≤sn o<m)) (≤-trans (find-max-lower-yields-low o' (≤-trans n≤sn o<m)) n≤sn)

    find-max-lower-helper o o<m prev-max prev-max≤o with f o o<m ≤A? f prev-max (≤-<-trans prev-max≤o o<m)
    ...   | yes _ = prev-max
    ...   | no _ = o

    find-max-lower-helper-yields-low o o<m prev-max prev-max≤o with f o o<m ≤A? f prev-max (≤-<-trans prev-max≤o o<m)
    ...   | yes _ = prev-max≤o
    ...   | no _ = n≤n

    find-max-lower-yields-low zero o<m = z≤n
    find-max-lower-yields-low o@(suc o') o<m = find-max-lower-helper-yields-low o o<m (find-max-lower o' (≤-trans n≤sn o<m)) (≤-trans (find-max-lower-yields-low o' (≤-trans n≤sn o<m)) n≤sn)

    -- weaker version of find-max-lower-yields-low
    find-max-lower-bounded : (o : ℕ) → (o<m : o < m) → find-max-lower o o<m < m
    find-max-lower-bounded o o<m = ≤-<-trans (find-max-lower-yields-low o o<m) o<m

    find-max-lower-is-max : {i j : ℕ} → .(i≤j : i ≤ j) → .(j<m : j < m) → f (find-max-lower j j<m) (find-max-lower-bounded j j<m) ≥A f i (≤-<-trans i≤j j<m)
    find-max-lower-is-max {zero} {zero} i≤j j<m = ≤A-refl
    find-max-lower-is-max {i} {j@(suc j')} i≤j j<m with i ≟ j | f j j<m ≤A? f (find-max-lower j' (≤-trans n≤sn j<m)) (find-max-lower-bounded j' (≤-trans n≤sn j<m))
    ... | yes refl | yes f[j]≤f[prev] = f[j]≤f[prev] 
    ... | yes refl | no f[j]≰f[prev] = ≤A-refl 
    ... | no i≠j | yes f[j]≤f[prev] = find-max-lower-is-max {i} {j'} (case ≤→<≡ i≤j of λ { (inj₁ (s≤s i≤j')) → i≤j'; (inj₂ i=j) → ⊥-elim (i≠j i=j) }) (≤-trans n≤sn j<m)
    ... | no i≠j | no f[j]≰f[prev] = begin
        f i (≤-<-trans i≤j j<m)     ≤⟨ find-max-lower-is-max {i} {j'} (case ≤→<≡ i≤j of λ { (inj₁ (s≤s i≤j')) → i≤j'; (inj₂ i=j) → ⊥-elim (i≠j i=j) }) (≤-trans n≤sn j<m) ⟩
        f[prev]                     ≤⟨ (case (≤A-decTotal .IsDecTotalOrder.total f[prev] (f j j<m)) of λ { (inj₁ pf) → pf; (inj₂ pf) → ⊥-elim (f[j]≰f[prev] pf) }) ⟩
        f j j<m                     ∎
        where
            open ≤A-Reasoning
            f[prev] = f (find-max-lower j' (≤-trans n≤sn j<m)) (find-max-lower-bounded j' (≤-trans n≤sn j<m))
            
open FindMaxLower


module SwapDecomposition where
    f⇐swap-list : 
        (f : (i : ℕ) → .(i < m) → A) → (l : SwapList) → .(l-valid : IsValidSwapList m l) →
        (i : ℕ) → .(i < m) → A
    f⇐swap-list f l l-valid i i<m = f (swap-with-list l i) (swap-with-list-nfunc l l-valid .proj₁ {i} i<m)

    f⇐swap-list-++ : 
        (f : (i : ℕ) → .(i < m) → A) → 
        (l : SwapList) → .(l-valid : IsValidSwapList m l) →
        (l' : SwapList) → .(l'-valid : IsValidSwapList m l') →
        (i : ℕ) → .(i<m : i < m) → 
        f⇐swap-list (f⇐swap-list f l l-valid) l' l'-valid i i<m ≡
        f⇐swap-list f (l' ++ l) (l'-valid IsValidSwapList-++ l-valid) i i<m
    f⇐swap-list-++ f l₁ l₁-valid l₂ l₂-valid i i<m = irrelevant-cong _ f (cong-app (sym (++-swap-split id l₂ l₁)) i)

    pair-at : (f : (i : ℕ) → .(i < m) → A) → (o : ℕ) → .(o<m : o < m) → (l : SwapList) → .(l-valid : IsValidSwapList m l) → ℕ × ℕ
    pair-at f o o<m l l-valid = o , find-max-lower (f⇐swap-list f l l-valid) o o<m
    
    pair-at-is-bounded : (f : (i : ℕ) → .(i < m) → A) → (o : ℕ) → (o<m : o < m) → (l : SwapList) → .(l-valid : IsValidSwapList m l) → 
        IsLowPair< m (pair-at f o o<m l l-valid)
    pair-at-is-bounded f o o<m l l-valid = o<m , find-max-lower-bounded (f⇐swap-list f l l-valid) o o<m

    pair-at-is-low : (f : (i : ℕ) → .(i < m) → A) → (o : ℕ) → (o<m : o < m) → (l : SwapList) → .(l-valid : IsValidSwapList m l) → 
        IsLowPair≤ o (pair-at f o o<m l l-valid)
    pair-at-is-low f o o<m l l-valid = n≤n , find-max-lower-yields-low (f⇐swap-list f l l-valid) o o<m

    -- finds the maximum item out of the items ≤ o (on function f ∘ swap-with-list l), swaps it to o, then recurses down.
    partial-decomposition : (f : (i : ℕ) → .(i < m) → A) → (o : ℕ) → .(o < m) → (l : SwapList) → .(l-valid : IsValidSwapList m l) → SwapList
    partial-decomposition f zero o<m l l-valid = l
    partial-decomposition f o@(suc o') o<m l l-valid = partial-decomposition f o' (≤-trans n≤sn o<m) (pair-at f o o<m l l-valid ∷ l) (All._∷_ (pair-at-is-bounded f o o<m l l-valid) l-valid)

    partial-decomposition-valid : (f : (i : ℕ) → .(i < m) → A) → (o : ℕ) → (o<m : o < m) → (l : SwapList) → (l-valid : IsValidSwapList m l) → IsValidSwapList m (partial-decomposition f o o<m l l-valid)
    partial-decomposition-valid f zero o<m l l-valid = l-valid
    partial-decomposition-valid f o@(suc o') o<m l l-valid = partial-decomposition-valid f o' (≤-trans n≤sn o<m) (pair-at f o o<m l l-valid ∷ l) (All._∷_ (pair-at-is-bounded f o o<m l l-valid) l-valid)

    partial-decomposition-length-lemma :
        (f : (i : ℕ) → .(i < m) → A) → (o : ℕ) → .(o<m : o < m) → (l : SwapList) → .(l-valid : IsValidSwapList m l) →
        length (partial-decomposition f o o<m l l-valid) ≡ length l + o
    partial-decomposition-length-lemma f zero o<m l l-valid = sym (+-comm (length l) zero)
    partial-decomposition-length-lemma f o@(suc o') o<m l l-valid =
        length (partial-decomposition f o o<m l l-valid)    ≡⟨ partial-decomposition-length-lemma f o' (≤-trans n≤sn o<m) (pair-at f o o<m l l-valid ∷ l) (All._∷_ (pair-at-is-bounded f o o<m l l-valid) l-valid) ⟩
        (1 + length l) + o'                                 ≡⟨ cong (_+ o') (+-comm 1 (length l)) ⟩
        (length l + 1) + o'                                 ≡⟨ +-assoc (length l) 1 o' ⟩
        length l + (1 + o')                                 ≡⟨⟩
        length l + o                                        ∎
        where open ≡-Reasoning

    partial-decomposition-drop-lemma :
        (f : (i : ℕ) → .(i < m) → A) → (o : ℕ) → .(o<m : o < m) → (l : SwapList) → .(l-valid : IsValidSwapList m l) →
        drop o (partial-decomposition f o o<m l l-valid) ≡ l
    partial-decomposition-drop-lemma f zero o<m l l-valid = refl
    partial-decomposition-drop-lemma f o@(suc o') o<m l l-valid =
        drop (1 + o') (partial-decomposition f o o<m l l-valid)                                                                                                     ≡⟨ cong-app (cong drop (+-comm 1 o')) (partial-decomposition f o o<m l l-valid) ⟩
        drop (o' + 1) (partial-decomposition f o o<m l l-valid)                                                                                                     ≡⟨ sym (drop-drop o' 1 (partial-decomposition f o o<m l l-valid)) ⟩
        drop 1 (drop o' (partial-decomposition f o o<m l l-valid))                                                                                                  ≡⟨⟩
        drop 1 (drop o' (partial-decomposition f o' (≤-trans n≤sn o<m) (pair-at f o o<m l l-valid ∷ l) (All._∷_ (pair-at-is-bounded f o o<m l l-valid) l-valid)))   ≡⟨ cong (drop 1) (partial-decomposition-drop-lemma f o' (≤-trans n≤sn o<m) (pair-at f o o<m l l-valid ∷ l) (All._∷_ (pair-at-is-bounded f o o<m l l-valid) l-valid)) ⟩
        drop 1 (pair-at f o o<m l l-valid ∷ l)                                                                                                                      ≡⟨⟩
        l                                                                                                                                                           ∎
        where open ≡-Reasoning

    -- not tail-recursive; use for proofs
    -- only includes the first i entries
    partial-decomposition-range :
        (f : (i : ℕ) → .(i < m) → A) → (o : ℕ) → .(o<m : o < m) → (l : SwapList) → .(l-valid : IsValidSwapList m l) →
        (i : ℕ) → .(i≤o : i ≤ o) →
        SwapList 
    partial-decomposition-range-is-valid :
        (f : (i : ℕ) → .(i < m) → A) → (o : ℕ) → (o<m : o < m) → (l : SwapList) → (l-valid : IsValidSwapList m l) →
        (i : ℕ) → .(i≤o : i ≤ o) →
        IsValidSwapList m (partial-decomposition-range f o o<m l l-valid i i≤o)
    partial-decomposition-range-helper :
        (f : (i : ℕ) → .(i < m) → A) → (o : ℕ) → .(o<m : o < m) →
        (i' : ℕ) → .(i≤o : suc i' ≤ o) →
        (l' : SwapList) → .(IsValidSwapList m l') →
        SwapList
    partial-decomposition-range-helper-is-valid :
        (f : (i : ℕ) → .(i < m) → A) → (o : ℕ) → (o<m : o < m) →
        (i' : ℕ) → .(i≤o : suc i' ≤ o) →
        (l' : SwapList) → (l'-valid : IsValidSwapList m l') →
        IsValidSwapList m (partial-decomposition-range-helper f o o<m i' i≤o l' l'-valid)
    
    partial-decomposition-range f o o<m l l-valid zero i≤o = l
    partial-decomposition-range f o o<m l l-valid i@(suc i') i≤o = partial-decomposition-range-helper f o o<m i' i≤o (partial-decomposition-range f o o<m l l-valid i' (≤-trans n≤sn i≤o)) (partial-decomposition-range-is-valid f o o<m l l-valid i' (≤-trans n≤sn i≤o))

    partial-decomposition-range-helper f o o<m i' i≤o l' l'-valid = pair-at f (suc (o ∸ i)) (≤-<-trans (≤-reflexive (∸-suc o i i≤o)) (≤-<-trans (m∸n≤m o i') o<m)) l' l'-valid ∷ l'
        where i = suc i'

    partial-decomposition-range-is-valid f o o<m l l-valid zero i≤o = l-valid
    partial-decomposition-range-is-valid f o o<m l l-valid i@(suc i') i≤o = partial-decomposition-range-helper-is-valid f o o<m i' i≤o (partial-decomposition-range f o o<m l l-valid i' (≤-trans n≤sn i≤o)) (partial-decomposition-range-is-valid f o o<m l l-valid i' (≤-trans n≤sn i≤o))

    partial-decomposition-range-helper-is-valid f o o<m i' i≤o l' l'-valid = All._∷_ (pair-at-is-bounded f (suc (o ∸ i)) (≤-<-trans (≤-reflexive (∸-suc o i i≤o)) (≤-<-trans (m∸n≤m o i') o<m)) l' l'-valid) l'-valid
        where i = suc i'

    partial-decomposition-range-length :
        (f : (i : ℕ) → .(i < m) → A) → (o : ℕ) → .(o<m : o < m) → (l : SwapList) → .(l-valid : IsValidSwapList m l) →
        (i : ℕ) → .(i≤o : i ≤ o) →
        length (partial-decomposition-range f o o<m l l-valid i i≤o) ≡ length l + i
    partial-decomposition-range-length f o o<m l l-valid zero i≤o = sym (+-comm (length l) zero)
    partial-decomposition-range-length f o o<m l l-valid i@(suc i') i≤o = 
        suc (length l')        ≡⟨ cong suc l'-length ⟩
        suc (length l + i')    ≡⟨ sym (+-suc (length l) i') ⟩
        length l + suc i'      ∎
        where 
            open ≡-Reasoning
            l' = partial-decomposition-range f o o<m l l-valid i' (≤-trans n≤sn i≤o)
            l'-length = partial-decomposition-range-length f o o<m l l-valid i' (≤-trans n≤sn i≤o)

    -- skip by i indices
    partial-decomposition-skip-lemma :
        (f : (i : ℕ) → .(i < m) → A) → (o : ℕ) → .(o<m : o < m) → (l : SwapList) → .(l-valid : IsValidSwapList m l) →
        (i : ℕ) → .(i≤o : i ≤ o) →
        partial-decomposition f o o<m l l-valid ≡ partial-decomposition f (o ∸ i) (≤-<-trans (m∸n≤m o i) o<m) (partial-decomposition-range f o o<m l l-valid i i≤o) (partial-decomposition-range-is-valid f o o<m l l-valid i i≤o)
    partial-decomposition-skip-lemma f o o<m l l-valid zero i≤o = refl
    partial-decomposition-skip-lemma {m = m} f o@(suc o') o<m l l-valid i@(suc i') i≤o with partial-decomposition-skip-lemma f o o<m l l-valid i' (≤-trans n≤sn i≤o)
    ... | l'≡ =
        partial-decomposition f o o<m l l-valid                                                                                 ≡⟨ l'≡ ⟩
        partial-decomposition f (o ∸ i') o∸i'<m l' l'-valid                                                                     ≡⟨ irrelevant-cong (_< m) (λ q q<m → partial-decomposition f q q<m l' l'-valid) {o ∸ i'} {suc (o ∸ i)} (+-∸-assoc 1 {o'} {i'} i'≤o') ⟩
        partial-decomposition f (suc (o ∸ i)) s[o'∸i']<m l' l'-valid                                                            ≡⟨⟩
        partial-decomposition f (o ∸ i) (≤-<-trans n≤sn s[o'∸i']<m) (pair-at f (suc (o ∸ i)) s[o'∸i']<m l' l'-valid ∷ l') _     ∎
        where
            open ≡-Reasoning
            l' = partial-decomposition-range f o o<m l l-valid i' (≤-trans n≤sn i≤o)
            
            -- Eventually irrelevant proofs
            l'-valid = partial-decomposition-range-is-valid f o (≤-recompute o<m) l (IsValidSwapList-recompute l-valid) i' (≤-trans n≤sn i≤o)
            
            i'≤o' : i' ≤ o'
            i'≤o' = s≤s⁻¹ (≤-recompute i≤o)

            o∸i'<m : o ∸ i' < m
            o∸i'<m = ≤-<-trans (m∸n≤m o i') (≤-recompute o<m)

            s[o'∸i']<m : suc (o' ∸ i') < m
            s[o'∸i']<m = ≤-<-trans (≤-reflexive (∸-suc o' i' i'≤o')) o∸i'<m

    -- skip to index i
    partial-decomposition-skip-to-lemma :
        (f : (i : ℕ) → .(i < m) → A) → (o : ℕ) → .(o<m : o < m) → (l : SwapList) → .(l-valid : IsValidSwapList m l) →
        (i : ℕ) → .(i≤o : i ≤ o) →
        partial-decomposition f o o<m l l-valid ≡ partial-decomposition f i (≤-<-trans i≤o o<m) (partial-decomposition-range f o o<m l l-valid (o ∸ i) (m∸n≤m o i)) (partial-decomposition-range-is-valid f o (≤-recompute o<m) l (IsValidSwapList-recompute l-valid) (o ∸ i) (m∸n≤m o i))
    partial-decomposition-skip-to-lemma {m = m} f o o<m l l-valid i i≤o with partial-decomposition-skip-lemma f o o<m l l-valid (o ∸ i) (m∸n≤m o i)
    ... | l'≡ =
        partial-decomposition f o o<m l l-valid                     ≡⟨ l'≡ ⟩
        partial-decomposition f (o ∸ (o ∸ i)) o∸[o∸i]<m l' l'-valid  ≡⟨ irrelevant-cong {A = ℕ} (_< m) (λ q q<m → partial-decomposition f q q<m l' l'-valid) {o ∸ (o ∸ i)} {i} (m∸[m∸n]≡n {o} {i} (≤-recompute i≤o)) ⟩
        partial-decomposition f i (≤-<-trans i≤o o<m) l' l'-valid   ∎
        where
            open ≡-Reasoning
            l' = partial-decomposition-range f o o<m l l-valid (o ∸ i) (m∸n≤m o i)
            
            -- Eventually irrelevant proofs
            l'-valid = partial-decomposition-range-is-valid f o (≤-recompute o<m) l (IsValidSwapList-recompute l-valid) (o ∸ i) (m∸n≤m o i)
            
            o∸[o∸i]≡i = m∸[m∸n]≡n {o} {i} (≤-recompute i≤o)

            i<m : i < m
            i<m = ≤-<-trans (≤-recompute i≤o) (≤-recompute o<m)

            o∸[o∸i]<m = ≤-<-trans (≤-reflexive o∸[o∸i]≡i) i<m

    partial-decomposition-is-range :
        (f : (i : ℕ) → .(i < m) → A) → (o : ℕ) → .(o<m : o < m) → (l : SwapList) → .(l-valid : IsValidSwapList m l) →
        partial-decomposition f o o<m l l-valid ≡ partial-decomposition-range f o o<m l l-valid o n≤n
    partial-decomposition-is-range f o o<m l l-valid = partial-decomposition-skip-to-lemma f o o<m l l-valid 0 z≤n

    -- -- At position i in l, the indices being swapped are i and something less than i
    -- partial-decomposition-index-lemma :
    --     (f : (i : ℕ) → .(i < m) → A) → (o : ℕ) → .(o<m : o < m) → (l : SwapList m) →
    --     (i : ℕ) → .(i<o : i < o) →
    --     Σ ℕ λ j → Σ (Squash (j ≤ suc i)) λ { (squash j≤si) →
    --     lookup (partial-decomposition f o o<m l) (fromℕ< {i} (<-≤-trans (<-≤-trans i<o (m≤n+m o (length l))) (≤-reflexive (sym (partial-decomposition-length-lemma f o o<m l)))))
    --     ≡ (fromℕ< {suc i} (≤-<-trans i<o o<m) , fromℕ< {j} (≤-<-trans (≤-trans j≤si i<o) o<m)) }
    -- partial-decomposition-index-lemma {m = m} f o o<m l i i<o = j , squash j≤si , lookup-correct
    --     where
    --         i<decompose-l : i < length (partial-decomposition f o o<m l)
    --         i<decompose-l = begin
    --             suc i                                      ≤⟨ ≤-recompute i<o ⟩
    --             o                                           ≤⟨ m≤n+m o (length l) ⟩
    --             length l + o                                ≤⟨ ≤-reflexive (sym (partial-decomposition-length-lemma f o o<m l)) ⟩
    --             length (partial-decomposition f o o<m l)    ∎
    --             where open ≤-Reasoning

    --         l' : SwapList m
    --         l' = partial-decomposition-range f o o<m l (o ∸ suc i) (m∸n≤m o (suc i))

    --         j-fin : Fin m
    --         j-fin = pair-at f (suc i) (≤-<-trans i<o o<m) l' .proj₂

    --         j : ℕ
    --         j = toℕ j-fin

    --         -- These are a bunch of proofs that shouldn't ever actually be computed. They're used in several irrelevant contexts,
    --         -- but to have them exist separately out here, they need to be real, apparently
    --         j≤si : j ≤ suc i
    --         j≤si = begin
    --             j                                                                           ≤⟨ ≤-refl ⟩
    --             toℕ (find-max-lower (f ∘ swap-with-list l') (suc i) (≤-<-trans i<o o<m))   ≤⟨ find-max-lower-yields-low (f ∘ swap-with-list l') {suc i} (≤-<-trans i<o o<m) ⟩
    --             suc i                                                                      ∎
    --             where open ≤-Reasoning

    --         si<m : suc i < m
    --         si<m = ≤-<-trans (≤-recompute i<o) (≤-recompute o<m)

    --         i<m : i < m
    --         i<m = ≤-<-trans n≤sn si<m

    --         j<m : j < m
    --         j<m = ≤-<-trans j≤si si<m

    --         weird-len≡o : length (partial-decomposition f i i<m (pair-at f (suc i) si<m l' ∷ l')) ≡ length l + o
    --         weird-len≡o =
    --             length (partial-decomposition f i i<m (pair-at f (suc i) si<m l' ∷ l')) ≡⟨ partial-decomposition-length-lemma f i i<m (pair-at f (suc i) si<m l' ∷ l') ⟩
    --             length (pair-at f (suc i) si<m l' ∷ l') + i    ≡⟨⟩
    --             suc (length l') + i                            ≡⟨ cong (λ q → suc q + i) (partial-decomposition-range-length f o o<m l (o ∸ suc i) (m∸n≤m o (suc i))) ⟩
    --             suc (length l + (o ∸ suc i)) + i              ≡⟨ cong (_+ i) (sym (+-suc (length l) (o ∸ suc i))) ⟩
    --             (length l + suc (o ∸ suc i)) + i              ≡⟨ cong (λ q → (length l + q) + i) (∸-suc o (suc i) i<o) ⟩
    --             (length l + (o ∸ i)) + i                        ≡⟨ +-assoc (length l) (o ∸ i) i ⟩
    --             length l + ((o ∸ i) + i)                        ≡⟨ cong (length l +_) (m∸n+n≡m {o} {i} (<⇒≤ (≤-recompute i<o))) ⟩
    --             length l + o ∎
    --             where open ≡-Reasoning

    --         i<base-len : i < length (partial-decomposition f o o<m l)
    --         i<base-len = begin
    --             suc i                                      ≤⟨ ≤-recompute i<o ⟩
    --             o                                           ≤⟨ m≤n+m o (length l) ⟩
    --             length l + o                                ≡⟨ sym (partial-decomposition-length-lemma f o o<m l) ⟩
    --             length (partial-decomposition f o o<m l)    ∎
    --             where open ≤-Reasoning

    --         i<weird-len : i < length (partial-decomposition f i i<m (pair-at f (suc i) si<m l' ∷ l'))
    --         i<weird-len = begin
    --             suc i                                                                      ≤⟨ m≤n+m (suc i) (length l') ⟩
    --             length l' + suc i                                                          ≡⟨ +-suc (length l') i ⟩
    --             suc (length l') + i                                                        ≡⟨⟩
    --             length (pair-at f (suc i) si<m l' ∷ l') + i                                ≡⟨ sym (partial-decomposition-length-lemma f i i<m (pair-at f (suc i) si<m l' ∷ l')) ⟩
    --             length (partial-decomposition f i i<m (pair-at f (suc i) si<m l' ∷ l'))    ∎
    --             where open ≤-Reasoning

    --         i+0<weird-len : i + 0 < length (partial-decomposition f i i<m (pair-at f (suc i) si<m l' ∷ l'))
    --         i+0<weird-len = ≤-<-trans (≤-reflexive (+-comm i 0)) i<weird-len

    --         0<sub-len : 0 < length (pair-at f (suc i) si<m l' ∷ l')
    --         0<sub-len = s≤s z≤n

    --         0<drop-len : 0 < length (drop i (partial-decomposition f i i<m (pair-at f (suc i) si<m l' ∷ l')))
    --         0<drop-len = begin
    --             1                                                                                   ≤⟨ 0<sub-len ⟩
    --             length (pair-at f (suc i) si<m l' ∷ l')                                            ≡⟨ cong length (sym (partial-decomposition-drop-lemma f i i<m (pair-at f (suc i) si<m l' ∷ l'))) ⟩
    --             length (drop i (partial-decomposition f i i<m (pair-at f (suc i) si<m l' ∷ l')))   ∎
    --             where open ≤-Reasoning

    --         lookup-correct =
    --             lookup (partial-decomposition f o o<m l) (fromℕ< {i} i<base-len)                                            ≡⟨ irrelevant-cong (λ q → i < length q) (λ q i< → lookup q (fromℕ< {i} i<)) {w = partial-decomposition f o o<m l} {x = partial-decomposition f (suc i) si<m l'} {y = i<base-len} {z = i<weird-len} (partial-decomposition-skip-to-lemma f o o<m l (suc i) i<o) ⟩
    --             lookup (partial-decomposition f (suc i) si<m l') (fromℕ< {i} i<weird-len)                                  ≡⟨ irrelevant-cong (_< length (partial-decomposition f (suc i) si<m l')) (λ q q< → lookup (partial-decomposition f (suc i) si<m l') (fromℕ< {q} q<)) {i} {i + 0} {i<weird-len} {i+0<weird-len} (+-comm 0 i) ⟩
    --             lookup (partial-decomposition f (suc i) si<m l') (fromℕ< {i + 0} i+0<weird-len)                            ≡⟨ drop-lookup (partial-decomposition f (suc i) si<m l') i 0 i+0<weird-len ⟩
    --             lookup (drop i (partial-decomposition f (suc i) si<m l')) (fromℕ< {0} 0<drop-len)                          ≡⟨⟩
    --             lookup (drop i (partial-decomposition f i i<m (pair-at f (suc i) si<m l' ∷ l'))) (fromℕ< {0} 0<drop-len)   ≡⟨ irrelevant-cong (λ q → 0 < length q) (λ q 0< → lookup q (fromℕ< {0} 0<)) {w = drop i (partial-decomposition f i i<m (pair-at f (suc i) si<m l' ∷ l'))} {x = pair-at f (suc i) si<m l' ∷ l'} {y = 0<drop-len} {z = 0<sub-len} (partial-decomposition-drop-lemma f i i<m (pair-at f (suc i) si<m l' ∷ l')) ⟩
    --             lookup (pair-at f (suc i) si<m l' ∷ l') (fromℕ< {0} 0<sub-len)                                             ≡⟨⟩
    --             pair-at f (suc i) si<m l'                                                                                  ≡⟨⟩
    --             fromℕ< {suc i} si<m , j-fin                                                                                ≡⟨ ×≡ refl (sym (fromℕ<-toℕ j-fin (toℕ<n j-fin))) ⟩
    --             fromℕ< {suc i} si<m , fromℕ< {j} j<m                                                                       ∎
    --             where open ≡-Reasoning

--     partial-decomposition-low-stays-low :
--         (f : (i : ℕ) → .(i < m) → A) → (o : ℕ) → .(o<m : o < m) →
--         ∀ (i : ℕ) → .(i≤o : i ≤ o) →
--         toℕ (swap-with-list (partial-decomposition f o o<m []) (fromℕ< {i} (≤-<-trans i≤o o<m))) ≤ o
--     partial-decomposition-low-stays-low {m = m} f o o<m i i≤o = begin
--         toℕ (swap-with-list (partial-decomposition f o o<m []) (fromℕ< {i} i<m))                ≡⟨ cong (λ q → toℕ (swap-with-list q (fromℕ< {i} i<m))) (partial-decomposition-is-range f o o<m []) ⟩
--         toℕ (swap-with-list (partial-decomposition-range f o o<m [] o n≤n) (fromℕ< {i} i<m))    ≤⟨ partial-decomposition-range-low-stays-low f o o<m i o i≤o n≤n ⟩
--         o                                                                                       ∎
--         where
--             open ≤-Reasoning
--             i<m : i < m
--             i<m = ≤-<-trans (≤-recompute i≤o) (≤-recompute o<m)

    +-range-split :
        (f : (i : ℕ) → .(i < m) → A) → (o : ℕ) → .(o<m : o < m) → (l : SwapList) → .(l-valid : IsValidSwapList m l) →
        (i j : ℕ) → .(i+j≤o : i + j ≤ o) →
        partial-decomposition-range f o o<m l l-valid (i + j) i+j≤o ≡
        partial-decomposition-range f (o ∸ j) (≤-<-trans (m∸n≤m o j) o<m) (partial-decomposition-range f o o<m l l-valid j (m+n≤o⇒n≤o i i+j≤o)) (partial-decomposition-range-is-valid f o o<m l l-valid j (m+n≤o⇒n≤o i i+j≤o)) i (≤-trans (≤-reflexive (sym (m+n∸n≡m i j))) (∸-mono {i + j} {o} {j} {j} i+j≤o n≤n))
    +-range-split f o o<m l l-valid zero j i+j≤o = refl
    +-range-split {m = m} f o o<m l l-valid i@(suc i') j i+j≤o =
        partial-decomposition-range f o o<m l l-valid (i + j) i+j≤o                         ≡⟨⟩
        partial-decomposition-range f o o<m l l-valid (suc (i' + j)) i+j≤o                  ≡⟨⟩
        xy ∷ partial-decomposition-range f o o<m l l-valid (i' + j) i'+j≤o                  ≡⟨ cong (xy ∷_) l'=l'' ⟩
        xy ∷ partial-decomposition-range f (o ∸ j) o∸j<m l-front l-front-valid i' i'≤o∸j    ≡⟨ cong (_∷ partial-decomposition-range f (o ∸ j) o∸j<m l-front l-front-valid i' i'≤o∸j) (×≡ x=x' y=y') ⟩
        xy' ∷ partial-decomposition-range f (o ∸ j) o∸j<m l-front l-front-valid i' i'≤o∸j   ≡⟨⟩
        partial-decomposition-range f (o ∸ j) o∸j<m l-front l-front-valid i i≤o∸j           ∎
        where
            open ≡-Reasoning

            i≤o : i ≤ o
            i≤o = m+n≤o⇒m≤o i (≤-recompute i+j≤o)

            j≤o : j ≤ o
            j≤o = m+n≤o⇒n≤o i (≤-recompute i+j≤o)

            i'+j≤o : i' + j ≤ o
            i'+j≤o = ≤-trans n≤sn (≤-recompute i+j≤o)

            i'≤o : i' ≤ o
            i'≤o = m+n≤o⇒m≤o i' i'+j≤o

            o∸j<m : o ∸ j < m
            o∸j<m = ≤-<-trans (m∸n≤m o j) (≤-recompute o<m)

            i≤o∸j : i ≤ o ∸ j
            i≤o∸j = ≤-trans (≤-reflexive (sym (m+n∸n≡m i j))) (∸-mono {i + j} {o} {j} {j} (≤-recompute i+j≤o) n≤n)

            i'≤o∸j : i' ≤ o ∸ j
            i'≤o∸j = ≤-trans n≤sn i≤o∸j

            s[o∸[i+j]]=s[o∸j∸i] : suc (o ∸ (i + j)) ≡ suc (o ∸ j ∸ i)
            s[o∸[i+j]]=s[o∸j∸i] = cong suc (trans (cong (o ∸_) (+-comm i j)) (sym (m∸n∸o≡m∸[n+o] o j i)))

            s[o∸[i+j]]<m : suc (o ∸ (i + j)) < m
            s[o∸[i+j]]<m = ≤-<-trans (≤-trans (≤-reflexive (∸-suc o (i + j) i+j≤o)) (m∸n≤m o (i' + j))) (≤-recompute o<m)

            s[o∸j∸i]<m : suc (o ∸ j ∸ i) < m
            s[o∸j∸i]<m = ≤-<-trans (≤-reflexive (sym s[o∸[i+j]]=s[o∸j∸i])) s[o∸[i+j]]<m

            l-front = partial-decomposition-range f o o<m l l-valid j j≤o
            l-front-valid = partial-decomposition-range-is-valid f o (≤-recompute o<m) l (IsValidSwapList-recompute l-valid) j j≤o

            l' = partial-decomposition-range f o o<m l l-valid (i' + j) i'+j≤o
            l'-valid = partial-decomposition-range-is-valid f o (≤-recompute o<m) l (IsValidSwapList-recompute l-valid) (i' + j) i'+j≤o
            xy = pair-at f (suc (o ∸ (i + j))) (≤-<-trans (≤-reflexive (∸-suc o (i + j) i+j≤o)) (≤-<-trans (m∸n≤m o (i' + j)) o<m)) l' l'-valid
            x = suc (o ∸ (i + j)) 
            y = find-max-lower (f⇐swap-list f l' l'-valid) (suc (o ∸ (i + j))) s[o∸[i+j]]<m
            x<m = s[o∸[i+j]]<m

            l'' = partial-decomposition-range f (o ∸ j) o∸j<m l-front l-front-valid i' i'≤o∸j
            l''-valid = partial-decomposition-range-is-valid f (o ∸ j) o∸j<m l-front l-front-valid i' i'≤o∸j
            xy' = pair-at f (suc (o ∸ j ∸ i)) s[o∸j∸i]<m l'' l''-valid
            x' = suc (o ∸ j ∸ i)
            y' = find-max-lower (f⇐swap-list f l'' l''-valid) (suc (o ∸ j ∸ i)) s[o∸j∸i]<m
            x'<m = s[o∸j∸i]<m

            l'=l'' : l' ≡ l''
            l'=l'' = +-range-split f o o<m l l-valid i' j i'+j≤o

            x=x' : x ≡ x'
            x=x' = s[o∸[i+j]]=s[o∸j∸i]

            y=y' : y ≡ y'
            y=y' =
                find-max-lower (f⇐swap-list f l' l'-valid) (suc (o ∸ (i + j))) s[o∸[i+j]]<m     ≡⟨ irrelevant-cong (IsValidSwapList m) (λ q q-valid → find-max-lower (f⇐swap-list f q q-valid) (suc (o ∸ (i + j))) s[o∸[i+j]]<m) {l'} {l''} {l'-valid} {l''-valid} l'=l'' ⟩
                find-max-lower (f⇐swap-list f l'' l''-valid) (suc (o ∸ (i + j))) s[o∸[i+j]]<m   ≡⟨ irrelevant-cong (_< m) (find-max-lower (f⇐swap-list f l'' l''-valid)) {y = s[o∸[i+j]]<m} {z = s[o∸j∸i]<m} s[o∸[i+j]]=s[o∸j∸i] ⟩
                find-max-lower (f⇐swap-list f l'' l''-valid) (suc (o ∸ j ∸ i)) s[o∸j∸i]<m       ∎

















    partial-decomposition-range-split-lemma :
        (f : (i : ℕ) → .(i < m) → A) → (o : ℕ) → .(o<m : o < m) → (l : SwapList) → .(l-valid : IsValidSwapList m l) →
        (i : ℕ) → .(i≤o : i ≤ o) →
        swap-with-list (partial-decomposition-range f o o<m l l-valid i i≤o) ≡
        (swap-with-list l ∘ swap-with-list (partial-decomposition-range (f⇐swap-list f l l-valid) o o<m [] All.[] i i≤o))
    partial-decomposition-range-split-lemma f o o<m l l-valid zero i≤o = refl
    partial-decomposition-range-split-lemma {m = m} f o o<m l l-valid i@(suc i') i≤o =
        swap-with-list (partial-decomposition-range f o o<m l l-valid i i≤o)                                                ≡⟨⟩
        swap-with-list (wz ∷ l')                                                                                            ≡⟨ swap-pop-initial id l' w z  ⟩
        swap-with-list l' ∘ swp w z                                                                                         ≡⟨ cong (_∘ swp w z) (partial-decomposition-range-split-lemma f o o<m l l-valid i' i'≤o) ⟩
        swap-with-list l ∘ swap-with-list l'' ∘ swp w z                                                                     ≡⟨ cong (swap-with-list l ∘_) (sym (swap-pop-initial id (partial-decomposition-range (f⇐swap-list f l l-valid) o o<m [] All.[] i' i'≤o) w z)) ⟩
        swap-with-list l ∘ swap-with-list (wz ∷ l'')                                                                        ≡⟨ cong (λ q → swap-with-list l ∘ swap-with-list ((w , q) ∷ l'')) z=z' ⟩
        swap-with-list l ∘ swap-with-list (wz' ∷ l'')                                                                       ≡⟨⟩
        swap-with-list l ∘ swap-with-list (partial-decomposition-range (f⇐swap-list f l l-valid) o o<m [] All.[] i i≤o)     ∎
        where
            open ≡-Reasoning

            i'≤o : i' ≤ o
            i'≤o = ≤-trans n≤sn (≤-recompute i≤o)

            s[o∸i]<m : suc (o ∸ i) < m
            s[o∸i]<m = ≤-<-trans (≤-trans (≤-reflexive (∸-suc o i i≤o))(m∸n≤m o i')) (≤-recompute o<m)

            l' = partial-decomposition-range f o o<m l l-valid i' i'≤o
            l'-valid = partial-decomposition-range-is-valid f o (≤-recompute o<m) l (IsValidSwapList-recompute l-valid) i' i'≤o 
            wz = pair-at f (suc (o ∸ i)) s[o∸i]<m l' l'-valid
            w = suc (o ∸ i)
            z = find-max-lower (f⇐swap-list f l' l'-valid) (suc (o ∸ i)) s[o∸i]<m

            l'' = partial-decomposition-range (f⇐swap-list f l l-valid) o o<m [] All.[] i' i'≤o
            l''-valid = partial-decomposition-range-is-valid (f⇐swap-list f l l-valid) o (≤-recompute o<m) [] All.[] i' i'≤o
            wz' = pair-at (f⇐swap-list f l l-valid) (suc (o ∸ i)) s[o∸i]<m l'' l''-valid
            w' = suc (o ∸ i)
            z' = find-max-lower (f⇐swap-list (f⇐swap-list f l l-valid) l'' l''-valid) (suc (o ∸ i)) s[o∸i]<m

            z=z' : z ≡ z'
            z=z' = irrelevant-cong (IsNFuncLower m) (λ q q-nfunc → find-max-lower (λ x x<m → f (q x) (q-nfunc x<m)) (suc (o ∸ i)) s[o∸i]<m) {swap-with-list l'} {swap-with-list l ∘ swap-with-list l''} {swap-with-list-nfunc {m} l' l'-valid .proj₁} {swap-with-list-nfunc {m} l l-valid .proj₁ ∘ swap-with-list-nfunc {m} l'' l''-valid .proj₁} (partial-decomposition-range-split-lemma f o o<m l l-valid i' i'≤o)

    -- In the final sort, the any item above index i is completely determined by
    -- everything after the first i swaps in the list.
    -- This includes if j is outside of the sort entirely.
    partial-decomposition-swap-drop-lemma :
        (f : (i : ℕ) → .(i < m) → A) → (o : ℕ) → .(o<m : o < m) → (l : SwapList) → .(l-valid : IsValidSwapList m l) →
        (i j : ℕ) → .(i<j : i < j) → .(i≤o : i ≤ o) .(j<m : j < m) →
        swap-with-list (partial-decomposition f o o<m l l-valid) j ≡
        swap-with-list (partial-decomposition-range f o o<m l l-valid (o ∸ i) (m∸n≤m o i)) j
    partial-decomposition-swap-drop-lemma f o o<m l l-valid zero j i<j i≤o j<m =
        swap-with-list (partial-decomposition f o o<m l l-valid) j                  ≡⟨ cong (λ q → swap-with-list q j) (partial-decomposition-is-range f o o<m l l-valid) ⟩
        swap-with-list (partial-decomposition-range f o o<m l l-valid o ≤-refl) j   ∎
        where open ≡-Reasoning
    partial-decomposition-swap-drop-lemma {m = m} f o o<m l l-valid i@(suc i') j i<j i≤o j<m =
        swap-with-list (partial-decomposition f o o<m l l-valid) j                                  ≡⟨ partial-decomposition-swap-drop-lemma f o o<m l l-valid i' j (≤-trans n≤sn i<j) (≤-trans n≤sn i≤o) j<m ⟩
        swap-with-list (partial-decomposition-range f o o<m l l-valid (o ∸ i') (m∸n≤m o i')) j      ≡⟨ irrelevant-cong (_≤ o) (λ q q<m → swap-with-list (partial-decomposition-range f o o<m l l-valid q q<m) j) {o ∸ i'} {suc (o ∸ i)} {m∸n≤m o i'} {s[o∸i]≤o} (sym (∸-suc o i i≤o)) ⟩
        swap-with-list (partial-decomposition-range f o o<m l l-valid (suc (o ∸ i)) s[o∸i]≤o) j     ≡⟨⟩
        swap-with-list (pair-at f (suc (o ∸ suc (o ∸ i))) thing<m l' l'-valid ∷ l') j               ≡⟨ irrelevant-cong (_< m) (λ q q<m → swap-with-list (pair-at f q q<m l' l'-valid ∷ l') j) {suc (o ∸ suc (o ∸ i))} {i} {thing<m} {i<m} thing≡i ⟩
        swap-with-list (pair-at f i i<m l' l'-valid ∷ l') j                                         ≡⟨ cong-app (uncurry (swap-pop-initial id l') (pair-at f i i<m l' l'-valid)) j ⟩
        (swap-with-list l' ∘ uncurry swp (pair-at f i i<m l' l'-valid)) j                           ≡⟨ cong (swap-with-list l') swap-at-i-leaves-j ⟩
        swap-with-list l' j                                                                         ∎
        where
            open ≡-Reasoning
            l' = partial-decomposition-range f o o<m l l-valid (o ∸ i) (m∸n≤m o i)

            -- Eventually irrelevant proofs
            l'-valid = partial-decomposition-range-is-valid f o (≤-recompute o<m) l (IsValidSwapList-recompute l-valid) (o ∸ i) (m∸n≤m o i)


            i<m : i < m
            i<m = <-trans (≤-recompute i<j) (≤-recompute j<m)

            s[o∸i]≤o : suc (o ∸ suc i') ≤ o
            s[o∸i]≤o = ≤-trans (≤-reflexive (∸-suc o i i≤o)) (m∸n≤m o i')

            thing≡i : suc (o ∸ suc (o ∸ i)) ≡ i
            thing≡i =
                suc (o ∸ suc (o ∸ i))     ≡⟨ ∸-suc o (suc (o ∸ i)) s[o∸i]≤o ⟩
                o ∸ (o ∸ i)                 ≡⟨ m∸[m∸n]≡n {o} {i} (≤-recompute i≤o) ⟩
                i                           ∎

            thing<m : suc (o ∸ suc (o ∸ i)) < m
            thing<m = ≤-<-trans (≤-reflexive thing≡i) i<m

            -- and the core of the proof (of this lemma at least)
            swap-at-i-leaves-j : uncurry swp (pair-at f i i<m l' l'-valid) j ≡ j
            swap-at-i-leaves-j = swp-no-match⇒id x y j x≠j y≠j
                where
                    x = i
                    y = find-max-lower (f⇐swap-list f l' l'-valid) i i<m

                    x≠j : x ≢ j
                    x≠j i=j = <-irrefl {i} {j} i=j (≤-recompute i<j)

                    y≠j : y ≢ j
                    y≠j y=j = <-irrefl {y} {j} y=j (≤-<-trans (find-max-lower-yields-low (f⇐swap-list f l' l'-valid) i i<m) (≤-recompute i<j))

    -- partial-decomposition has two core properties:
    -- anything below o stays below o
    -- anything above o is acted upon by identity
    -- this one does recomputation. Use as proof tool only!
    partial-decomposition-range-low-stays-low :
        (f : (i : ℕ) → .(i < m) → A) → (o : ℕ) → .(o<m : o < m) →
        ∀ (i j : ℕ) → .(i≤o : i ≤ o) → .(j≤o : j ≤ o) →
        swap-with-list (partial-decomposition-range f o o<m [] All.[] j j≤o) i ≤ o
    partial-decomposition-range-low-stays-low {m = m} f o o<m i zero i≤o j≤o = ≤-recompute i≤o
    partial-decomposition-range-low-stays-low {m = m} f o@(suc o') o<m i j@(suc j') i≤o j≤o = begin
        swap-with-list (partial-decomposition-range f o o<m [] All.[] j j≤o) i                                                                    ≡⟨⟩
        swap-with-list (pair-at f (suc (o ∸ j)) s[o'∸i']<m l' l'-valid ∷ l') i                                                                     ≡⟨ cong (λ q → q i) (swap-pop-initial id l' (suc (o ∸ j)) (find-max-lower (f⇐swap-list f l' l'-valid) (suc (o ∸ j)) s[o'∸i']<m)) ⟩
        (swap-with-list l' ∘ swp (suc (o ∸ j)) (find-max-lower (f⇐swap-list f l' l'-valid) (suc (o ∸ j)) s[o'∸i']<m)) i  ≡⟨⟩
        swap-with-list l' new-i                                                                                                                           ≤⟨ partial-decomposition-range-low-stays-low f o o<m new-i j' new-i-low (≤-trans n≤sn j≤o) ⟩
        o                                                                                                                                                       ∎
        where
            open ≤-Reasoning
            l' = partial-decomposition-range f o o<m [] All.[] j' (≤-trans n≤sn j≤o)

            -- Hopefully irrelevant proofs
            l'-valid = partial-decomposition-range-is-valid f o (≤-recompute o<m) [] All.[] j' (≤-trans n≤sn j≤o)

            i<m : i < m
            i<m = ≤-<-trans (≤-recompute i≤o) (≤-recompute o<m)

            j<m : j < m
            j<m = ≤-<-trans (≤-recompute j≤o) (≤-recompute o<m)

            s[o'∸i']<m : suc (o' ∸ j') < m
            s[o'∸i']<m = ≤-<-trans (≤-trans (≤-reflexive (∸-suc o j j≤o)) (m∸n≤m o j')) (≤-recompute o<m)

            new-i = swp (suc (o ∸ j)) (find-max-lower (f⇐swap-list f l' l'-valid) (suc (o ∸ j)) s[o'∸i']<m) i

            new-i-low : new-i ≤ o
            new-i-low = begin
                new-i                   ≤⟨ low-swp-is-low (suc (o ∸ j)) (find-max-lower (f⇐swap-list f l' l'-valid) (suc (o ∸ j)) s[o'∸i']<m) i o
                    (begin
                        suc (o ∸ j)     ≡⟨ ∸-suc o j j≤o ⟩
                        o ∸ j'          ≤⟨ m∸n≤m o j' ⟩
                        o               ∎)
                    (begin
                        find-max-lower (f⇐swap-list f l' l'-valid) (suc (o ∸ j)) s[o'∸i']<m     ≤⟨ find-max-lower-yields-low (f⇐swap-list f l' l'-valid) (suc (o' ∸ j')) s[o'∸i']<m ⟩
                        suc (o ∸ j)     ≡⟨ ∸-suc o j j≤o ⟩
                        o ∸ j'          ≤⟨ m∸n≤m o j' ⟩
                        o               ∎)
                    (≤-recompute i≤o) ⟩
                o                       ∎
