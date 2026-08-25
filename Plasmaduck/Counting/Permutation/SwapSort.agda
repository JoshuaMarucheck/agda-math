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
open import Data.Nat.Properties using (module ≤-Reasoning; <-cmp; suc-pred; ≤-reflexive; ≤-refl; ≤-trans; ≤-<-trans; <-≤-trans; <-trans; ≰⇒≥; <⇒≱; ≮⇒≥; <⇒≤; ≰⇒>; ≤-antisym; <-irrefl; +-mono-≤; +-mono-<; +-mono-≤-<; ∸-mono; +-suc; +-comm; +-assoc; n>0⇒n≢0; n∸n≡0; ≤∧≢⇒<; m≤n+m; m∸n≤m; m≤m+n; m+n≤o⇒m≤o; m+n≤o⇒n≤o; m<n⇒0<n∸m; m+n∸n≡m; m+[n∸m]≡n; m≤n⇒m∸n≡0; +-∸-assoc; ∸-monoʳ-<; m∸[m∸n]≡n; m∸n+n≡m)
open import Data.List using (List; foldl; _∷_; []; _∷ʳ_; length; lookup; drop; _++_; reverse; tabulate; map)
open import Data.List.Properties using (drop-drop; reverse-++; ++-identity; foldl-map; foldl-∷ʳ; foldl-cong; map-++)
open import Data.List.Relation.Unary.All using (All)

open import Plasmaduck.SetoidExperiment.SetoidMachinery using (discrete-setoid; from-discrete-cong; SetoidFunction₂; _which-is-cong₂_; _←₂_; SetoidFunction; _which-is-cong_; _←_; property-subset-setoid; discrete-function-setoid)
open import Plasmaduck.Function.Properties using (module SingleOperator)
open import Plasmaduck.Util.Case using (case_of_)
open import Plasmaduck.Data.Empty using (⊥-recompute)
open import Plasmaduck.Data.FakeFin using (FakeFin; realize; falsify)
open import Plasmaduck.Data.Squash using (Squash; squash)
open import Plasmaduck.Data.Nat using (≤-cmp; n≤n; n≤sn; n<sn; m≤n⇒m≤pn; m<n⇒m≢n; ≤→<≡; ≤≥⇒≡; ∸-suc; m∸n∸o≡m∸o∸n; m∸n∸o≡m∸[n+o]; m>0⇒m=sn; m≡spm; s≡s⁻¹; m<o∧n<p⇒s[m+o]<n+p)
open import Plasmaduck.Data.Fin using (toℕ<<n; _↑ˡ-inverted_; fromℕ<-↑ˡ-inverted)
open import Plasmaduck.Data.List using (drop-lookup; foldl-pop)
open import Plasmaduck.Data.Product using (Σ≡; ×≡; uncurry; curry)
open import Plasmaduck.Util.TypeChange using (change-type; change-type-input-dependence-irrelevance; change-type-output-dependence-commute; change-type-proof-irrelevance; cong₂-dependent)
open import Plasmaduck.Relation.Equivalence using (irrelevant-cong; irrelevant-cong₂)
open import Plasmaduck.Function.Bijection using (_∘-bijective_; id-bijective; bijective-is-functional)
open import Plasmaduck.Function using (_≈_; ≈-sym)

open import Plasmaduck.Counting.Permutation.Defs using (IsNFuncLower)
open import Plasmaduck.Counting.Permutation.Swap using (swp; swp-no-match⇒id; low-swp-is-low; swp-match₁-lemma)
open import Plasmaduck.Counting.Permutation.SwapList using (SwapList; IsValidSwapList; IsLowPair<; IsLowPair≤; swap-with-list; swap-with-list-nfunc; swap-pop-initial; _IsValidSwapList-++_; ++-swap-split)




module Plasmaduck.Counting.Permutation.SwapSort {a b c : Level} {A : Set a} {_≈A_ : Rel A b} {_≤A_ : Rel A c} (≤A-decTotal : IsDecTotalOrder _≈A_ _≤A_) where

variable
    m : ℕ


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


module FindMaxLower (f : ℕ → A) where
    -- Finds the index of the maximum item of f, out of those below o
    -- I'm doing this explicitly because with abstraction interacts badly with irrelevance,
    -- especially when I'm trying to avoid exponential computation blow-up.
    find-max-lower : (o : ℕ) → ℕ
    find-max-lower-yields-low : (o : ℕ) → find-max-lower o ≤ o
    find-max-lower-helper : (o : ℕ) → (prev-max : ℕ) → .(prev-max≤o : prev-max ≤ o) → ℕ
    find-max-lower-helper-yields-low : (o : ℕ) → (prev-max : ℕ) → (prev-max≤o : prev-max ≤ o) → find-max-lower-helper o prev-max prev-max≤o ≤ o

    find-max-lower zero = zero
    find-max-lower o@(suc o') = find-max-lower-helper o (find-max-lower o') (≤-trans (find-max-lower-yields-low o') n≤sn)

    find-max-lower-helper o prev-max prev-max≤o with f o ≤A? f prev-max
    ...   | yes _ = prev-max
    ...   | no _ = o

    find-max-lower-helper-yields-low o prev-max prev-max≤o with f o ≤A? f prev-max
    ...   | yes _ = prev-max≤o
    ...   | no _ = n≤n

    find-max-lower-yields-low zero = z≤n
    find-max-lower-yields-low o@(suc o') = find-max-lower-helper-yields-low o (find-max-lower o') (≤-trans (find-max-lower-yields-low o') n≤sn)

    find-max-lower-is-max : {i j : ℕ} → .(i≤j : i ≤ j) → f (find-max-lower j) ≥A f i
    find-max-lower-is-max {zero} {zero} i≤j = ≤A-refl
    find-max-lower-is-max {i} {j@(suc j')} i≤j with i ≟ j | f j ≤A? f (find-max-lower j')
    ... | yes refl | yes f[j]≤f[prev] = f[j]≤f[prev]
    ... | yes refl | no f[j]≰f[prev] = ≤A-refl
    ... | no i≠j | yes f[j]≤f[prev] = find-max-lower-is-max {i} {j'} (case ≤→<≡ i≤j of λ { (inj₁ (s≤s i≤j')) → i≤j'; (inj₂ i=j) → ⊥-elim (i≠j i=j) })
    ... | no i≠j | no f[j]≰f[prev] = begin
        f i         ≤⟨ find-max-lower-is-max {i} {j'} (case ≤→<≡ i≤j of λ { (inj₁ (s≤s i≤j')) → i≤j'; (inj₂ i=j) → ⊥-elim (i≠j i=j) }) ⟩
        f[prev]     ≤⟨ (case (≤A-decTotal .IsDecTotalOrder.total f[prev] (f j)) of λ { (inj₁ pf) → pf; (inj₂ pf) → ⊥-elim (f[j]≰f[prev] pf) }) ⟩
        f j         ∎
        where
            open ≤A-Reasoning
            f[prev] = f (find-max-lower j')

open FindMaxLower


module SwapDecomposition where

    pair-at : (f : ℕ → A) → (o : ℕ) → (l : SwapList) → ℕ × ℕ
    pair-at f o l = o , find-max-lower (f ∘ swap-with-list l) o

    pair-at-is-bounded : (f : ℕ → A) → (o : ℕ) → (o<m : o < m) → (l : SwapList) →
        IsLowPair< m (pair-at f o l)
    pair-at-is-bounded f o o<m l = o<m , ≤-<-trans (find-max-lower-yields-low (f ∘ swap-with-list l) o) o<m

    pair-at-is-low : (f : ℕ → A) → (o : ℕ) → (l : SwapList) →
        IsLowPair≤ o (pair-at f o l)
    pair-at-is-low f o l = n≤n , find-max-lower-yields-low (f ∘ swap-with-list l) o

    -- finds the maximum item out of the items ≤ o (on function f ∘ swap-with-list l), swaps it to o, then recurses down.
    partial-decomposition : (f : ℕ → A) → (o : ℕ) → (l : SwapList) → SwapList
    partial-decomposition f zero l = l
    partial-decomposition f o@(suc o') l = partial-decomposition f o' (pair-at f o l ∷ l)

    partial-decomposition-valid : (f : ℕ → A) → (o : ℕ) → (o<m : o < m) → (l : SwapList) → (l-valid : IsValidSwapList m l) → IsValidSwapList m (partial-decomposition f o l)
    partial-decomposition-valid f zero o<m l l-valid = l-valid
    partial-decomposition-valid f o@(suc o') o<m l l-valid = partial-decomposition-valid f o' (≤-trans n≤sn o<m) (pair-at f o l ∷ l) (All._∷_ (pair-at-is-bounded f o o<m l) l-valid)

    partial-decomposition-length-lemma :
        (f : ℕ → A) → (o : ℕ) → (l : SwapList) →
        length (partial-decomposition f o l) ≡ length l + o
    partial-decomposition-length-lemma f zero l = sym (+-comm (length l) zero)
    partial-decomposition-length-lemma f o@(suc o') l =
        length (partial-decomposition f o l)    ≡⟨ partial-decomposition-length-lemma f o' (pair-at f o l ∷ l) ⟩
        (1 + length l) + o'     ≡⟨ cong (_+ o') (+-comm 1 (length l)) ⟩
        (length l + 1) + o'     ≡⟨ +-assoc (length l) 1 o' ⟩
        length l + (1 + o')     ≡⟨⟩
        length l + o            ∎
        where open ≡-Reasoning

    partial-decomposition-drop-lemma :
        (f : ℕ → A) → (o : ℕ) → (l : SwapList) →
        drop o (partial-decomposition f o l) ≡ l
    partial-decomposition-drop-lemma f zero l = refl
    partial-decomposition-drop-lemma f o@(suc o') l =
        drop (1 + o') (partial-decomposition f o l)                         ≡⟨ cong-app (cong drop (+-comm 1 o')) (partial-decomposition f o l) ⟩
        drop (o' + 1) (partial-decomposition f o l)                         ≡⟨ sym (drop-drop o' 1 (partial-decomposition f o l)) ⟩
        drop 1 (drop o' (partial-decomposition f o l))                      ≡⟨⟩
        drop 1 (drop o' (partial-decomposition f o' (pair-at f o l ∷ l)))   ≡⟨ cong (drop 1) (partial-decomposition-drop-lemma f o' (pair-at f o l ∷ l)) ⟩
        drop 1 (pair-at f o l ∷ l)                                          ≡⟨⟩
        l                                                                   ∎
        where open ≡-Reasoning

    -- not tail-recursive; use for proofs
    -- only includes the first i entries
    -- no guarantees about what happens when i > o
    partial-decomposition-range :
        (f : ℕ → A) → (o : ℕ) → (l : SwapList) →
        (i : ℕ) →
        SwapList
    partial-decomposition-range-helper :
        (f : ℕ → A) → (o : ℕ) →
        (i' : ℕ) →
        (l' : SwapList) →
        SwapList

    partial-decomposition-range f o l zero = l
    partial-decomposition-range f o l i@(suc i') = partial-decomposition-range-helper f o i' (partial-decomposition-range f o l i')

    partial-decomposition-range-helper f o i' l' = pair-at f (suc (o ∸ i)) l' ∷ l'
        where i = suc i'


    partial-decomposition-range-is-valid :
        (f : ℕ → A) → (o : ℕ) → (o<m : o < m) → (l : SwapList) → (l-valid : IsValidSwapList m l) →
        (i : ℕ) → .(i≤o : i ≤ o) →
        IsValidSwapList m (partial-decomposition-range f o l i)
    partial-decomposition-range-helper-is-valid :
        (f : ℕ → A) → (o : ℕ) → (o<m : o < m) →
        (i' : ℕ) → .(i≤o : suc i' ≤ o) →
        (l' : SwapList) → (l'-valid : IsValidSwapList m l') →
        IsValidSwapList m (partial-decomposition-range-helper f o i' l')

    partial-decomposition-range-is-valid f o o<m l l-valid zero i≤o = l-valid
    partial-decomposition-range-is-valid f o o<m l l-valid i@(suc i') i≤o = partial-decomposition-range-helper-is-valid f o o<m i' i≤o (partial-decomposition-range f o l i') (partial-decomposition-range-is-valid f o o<m l l-valid i' (≤-trans n≤sn i≤o))

    partial-decomposition-range-helper-is-valid f o o<m i' i≤o l' l'-valid = All._∷_ (pair-at-is-bounded f (suc (o ∸ i)) (≤-<-trans (≤-reflexive (∸-suc o i i≤o)) (≤-<-trans (m∸n≤m o i') o<m)) l') l'-valid
        where i = suc i'


    partial-decomposition-range-length :
        (f : ℕ → A) → (o : ℕ) → (l : SwapList) →
        (i : ℕ) →
        length (partial-decomposition-range f o l i) ≡ length l + i
    partial-decomposition-range-length f o l zero = sym (+-comm (length l) zero)
    partial-decomposition-range-length f o l i@(suc i') =
        suc (length l')        ≡⟨ cong suc l'-length ⟩
        suc (length l + i')    ≡⟨ sym (+-suc (length l) i') ⟩
        length l + suc i'      ∎
        where
            open ≡-Reasoning
            l' = partial-decomposition-range f o l i'
            l'-length = partial-decomposition-range-length f o l i'

    -- skip by i indices
    partial-decomposition-skip-lemma :
        (f : ℕ → A) → (o : ℕ) → (l : SwapList) →
        (i : ℕ) → (i ≤ o) →
        partial-decomposition f o l ≡ partial-decomposition f (o ∸ i) (partial-decomposition-range f o l i)
    partial-decomposition-skip-lemma f o l zero i≤o = refl
    partial-decomposition-skip-lemma f o@(suc o') l i@(suc i') i≤o with partial-decomposition-skip-lemma f o l i' (≤-trans n≤sn i≤o)
    ... | l'≡ =
        partial-decomposition f o l                                                                                 ≡⟨ l'≡ ⟩
        partial-decomposition f (o ∸ i') l'                                                                     ≡⟨ cong (λ q → partial-decomposition f q l') (+-∸-assoc 1 {o'} {i'} i'≤o') ⟩
        partial-decomposition f (suc (o ∸ i)) l'                                                            ≡⟨⟩
        partial-decomposition f (o ∸ i) (pair-at f (suc (o ∸ i)) l' ∷ l')     ∎
        where
            open ≡-Reasoning
            l' = partial-decomposition-range f o l i'

            i'≤o' : i' ≤ o'
            i'≤o' = s≤s⁻¹ i≤o


    -- skip to index i
    partial-decomposition-skip-to-lemma :
        (f : ℕ → A) → (o : ℕ) → (l : SwapList) →
        (i : ℕ) → (i≤o : i ≤ o) →
        partial-decomposition f o l ≡ partial-decomposition f i (partial-decomposition-range f o l (o ∸ i))
    partial-decomposition-skip-to-lemma f o l i i≤o with partial-decomposition-skip-lemma f o l (o ∸ i) (m∸n≤m o i)
    ... | l'≡ =
        partial-decomposition f o l                 ≡⟨ l'≡ ⟩
        partial-decomposition f (o ∸ (o ∸ i)) l'    ≡⟨ cong (λ q → partial-decomposition f q l') (m∸[m∸n]≡n {o} {i} i≤o) ⟩
        partial-decomposition f i l'                ∎
        where
            open ≡-Reasoning
            l' = partial-decomposition-range f o l (o ∸ i)

    partial-decomposition-is-range :
        (f : ℕ → A) → (o : ℕ) → (l : SwapList) →
        partial-decomposition f o l ≡ partial-decomposition-range f o l o
    partial-decomposition-is-range f o l = partial-decomposition-skip-to-lemma f o l 0 z≤n

    +-range-split :
        (f : ℕ → A) → (o : ℕ) → (l : SwapList) →
        (i j : ℕ) → .(i+j≤o : i + j ≤ o) →
        partial-decomposition-range f o l (i + j) ≡
        partial-decomposition-range f (o ∸ j) (partial-decomposition-range f o l j) i
    +-range-split f o l zero j i+j≤o = refl
    +-range-split f o l i@(suc i') j i+j≤o =
        partial-decomposition-range f o l (i + j)               ≡⟨⟩
        partial-decomposition-range f o l (suc (i' + j))        ≡⟨⟩
        xy ∷ partial-decomposition-range f o l (i' + j)         ≡⟨ cong (xy ∷_) l'=l'' ⟩
        xy ∷ partial-decomposition-range f (o ∸ j) l-front i'   ≡⟨ cong (_∷ partial-decomposition-range f (o ∸ j) l-front i') (×≡ x=x' y=y') ⟩
        xy' ∷ partial-decomposition-range f (o ∸ j) l-front i'  ≡⟨⟩
        partial-decomposition-range f (o ∸ j) l-front i         ∎
        where
            open ≡-Reasoning

            s[o∸[i+j]]=s[o∸j∸i] : suc (o ∸ (i + j)) ≡ suc (o ∸ j ∸ i)
            s[o∸[i+j]]=s[o∸j∸i] = cong suc (trans (cong (o ∸_) (+-comm i j)) (sym (m∸n∸o≡m∸[n+o] o j i)))

            l-front = partial-decomposition-range f o l j

            l' = partial-decomposition-range f o l (i' + j)
            xy = pair-at f (suc (o ∸ (i + j))) l'
            x = suc (o ∸ (i + j))
            y = find-max-lower (f ∘ swap-with-list l') (suc (o ∸ (i + j)))

            l'' = partial-decomposition-range f (o ∸ j) l-front i'
            xy' = pair-at f (suc (o ∸ j ∸ i)) l''
            x' = suc (o ∸ j ∸ i)
            y' = find-max-lower (f ∘ swap-with-list l'') (suc (o ∸ j ∸ i))

            l'=l'' : l' ≡ l''
            l'=l'' = +-range-split f o l i' j (≤-trans n≤sn i+j≤o)

            x=x' : x ≡ x'
            x=x' = s[o∸[i+j]]=s[o∸j∸i]

            y=y' : y ≡ y'
            y=y' =
                find-max-lower (f ∘ swap-with-list l') (suc (o ∸ (i + j)))      ≡⟨ cong (λ q → find-max-lower (f ∘ swap-with-list q) (suc (o ∸ (i + j)))) l'=l'' ⟩
                find-max-lower (f ∘ swap-with-list l'') (suc (o ∸ (i + j)))     ≡⟨ cong (find-max-lower (f ∘ swap-with-list l'')) s[o∸[i+j]]=s[o∸j∸i] ⟩
                find-max-lower (f ∘ swap-with-list l'') (suc (o ∸ j ∸ i))       ∎

    partial-decomposition-range-split-lemma :
        (f : ℕ → A) → (o : ℕ) → (l : SwapList) →
        (i : ℕ) →
        swap-with-list (partial-decomposition-range f o l i) ≡
        (swap-with-list l ∘ swap-with-list (partial-decomposition-range (f ∘ swap-with-list l) o [] i))
    partial-decomposition-range-split-lemma f o l zero = refl
    partial-decomposition-range-split-lemma f o l i@(suc i') =
        swap-with-list (partial-decomposition-range f o l i)                                            ≡⟨⟩
        swap-with-list (wz ∷ l')                                                                        ≡⟨ swap-pop-initial id l' w z  ⟩
        swap-with-list l' ∘ swp w z                                                                     ≡⟨ cong (_∘ swp w z) (partial-decomposition-range-split-lemma f o l i') ⟩
        swap-with-list l ∘ swap-with-list l'' ∘ swp w z                                                 ≡⟨ cong (swap-with-list l ∘_) (sym (swap-pop-initial id (partial-decomposition-range (f ∘ swap-with-list l) o [] i') w z)) ⟩
        swap-with-list l ∘ swap-with-list (wz ∷ l'')                                                    ≡⟨ cong (λ q → swap-with-list l ∘ swap-with-list ((w , q) ∷ l'')) z=z' ⟩
        swap-with-list l ∘ swap-with-list (wz' ∷ l'')                                                   ≡⟨⟩
        swap-with-list l ∘ swap-with-list (partial-decomposition-range (f ∘ swap-with-list l) o [] i)   ∎
        where
            open ≡-Reasoning

            l' = partial-decomposition-range f o l i'
            wz = pair-at f (suc (o ∸ i)) l'
            w = suc (o ∸ i)
            z = find-max-lower (f ∘ swap-with-list l') (suc (o ∸ i))

            l'' = partial-decomposition-range (f ∘ swap-with-list l) o [] i'
            wz' = pair-at (f ∘ swap-with-list l) (suc (o ∸ i)) l''
            w' = suc (o ∸ i)
            z' = find-max-lower (f ∘ swap-with-list l ∘ swap-with-list l'') (suc (o ∸ i))

            z=z' : z ≡ z'
            z=z' = cong (λ q → find-max-lower (f ∘ q) (suc (o ∸ i))) {swap-with-list l'} {swap-with-list l ∘ swap-with-list l''} (partial-decomposition-range-split-lemma f o l i')

    -- In the final sort, the any item above index i is completely determined by
    -- everything after the first i swaps in the list.
    -- This includes if j is outside of the sort entirely.
    partial-decomposition-swap-drop-lemma :
        (f : ℕ → A) → (o : ℕ) → (l : SwapList) →
        (i j : ℕ) → .(i<j : i < j) → (i ≤ o) →
        swap-with-list (partial-decomposition f o l) j ≡
        swap-with-list (partial-decomposition-range f o l (o ∸ i)) j
    partial-decomposition-swap-drop-lemma f o l zero j i<j i≤o =
        swap-with-list (partial-decomposition f o l) j                  ≡⟨ cong (λ q → swap-with-list q j) (partial-decomposition-is-range f o l) ⟩
        swap-with-list (partial-decomposition-range f o l o) j   ∎
        where open ≡-Reasoning
    partial-decomposition-swap-drop-lemma f o l i@(suc i') j i<j i≤o =
        swap-with-list (partial-decomposition f o l) j                      ≡⟨ partial-decomposition-swap-drop-lemma f o l i' j (≤-trans n≤sn i<j) (≤-trans n≤sn i≤o) ⟩
        swap-with-list (partial-decomposition-range f o l (o ∸ i')) j       ≡⟨ cong (λ q → swap-with-list (partial-decomposition-range f o l q) j) (sym (∸-suc o i i≤o)) ⟩
        swap-with-list (partial-decomposition-range f o l (suc (o ∸ i))) j  ≡⟨⟩
        swap-with-list (pair-at f (suc (o ∸ suc (o ∸ i))) l' ∷ l') j        ≡⟨ cong (λ q → swap-with-list (pair-at f q l' ∷ l') j) thing≡i ⟩
        swap-with-list (pair-at f i l' ∷ l') j                              ≡⟨ cong-app (uncurry (swap-pop-initial id l') (pair-at f i l')) j ⟩
        (swap-with-list l' ∘ uncurry swp (pair-at f i l')) j                ≡⟨ cong (swap-with-list l') swap-at-i-leaves-j ⟩
        swap-with-list l' j                                                 ∎
        where
            open ≡-Reasoning
            l' = partial-decomposition-range f o l (o ∸ i)

            s[o∸i]≤o : suc (o ∸ suc i') ≤ o
            s[o∸i]≤o = ≤-trans (≤-reflexive (∸-suc o i i≤o)) (m∸n≤m o i')

            thing≡i : suc (o ∸ suc (o ∸ i)) ≡ i
            thing≡i =
                suc (o ∸ suc (o ∸ i))   ≡⟨ ∸-suc o (suc (o ∸ i)) s[o∸i]≤o ⟩
                o ∸ (o ∸ i)             ≡⟨ m∸[m∸n]≡n {o} {i} i≤o ⟩
                i                       ∎

            -- and the core of the proof (of this lemma at least)
            swap-at-i-leaves-j : uncurry swp (pair-at f i l') j ≡ j
            swap-at-i-leaves-j = swp-no-match⇒id x y j x≠j y≠j
                where
                    x = i
                    y = find-max-lower (f ∘ swap-with-list l') i

                    x≠j : x ≢ j
                    x≠j i=j = ⊥-recompute (<-irrefl {i} {j} i=j i<j)

                    y≠j : y ≢ j
                    y≠j y=j = ⊥-recompute (<-irrefl {y} {j} y=j (≤-<-trans (find-max-lower-yields-low (f ∘ swap-with-list l') i) i<j))

    -- partial-decomposition has two core properties:
    -- anything below o stays below o
    -- anything above o is acted upon by identity
    -- this one does recomputation. Use as proof tool only!
    partial-decomposition-range-low-stays-low :
        (f : ℕ → A) → (o : ℕ) →
        ∀ (i j : ℕ) → (i≤o : i ≤ o) → .(j≤o : j ≤ o) →
        swap-with-list (partial-decomposition-range f o [] j) i ≤ o
    partial-decomposition-range-low-stays-low f o i zero i≤o j≤o = i≤o
    partial-decomposition-range-low-stays-low f o@(suc o') i j@(suc j') i≤o j≤o = begin
        swap-with-list (partial-decomposition-range f o [] j) i                                             ≡⟨⟩
        swap-with-list (pair-at f (suc (o ∸ j)) l' ∷ l') i                                                  ≡⟨ cong (λ q → q i) (swap-pop-initial id l' (suc (o ∸ j)) (find-max-lower (f ∘ swap-with-list l') (suc (o ∸ j)))) ⟩
        (swap-with-list l' ∘ swp (suc (o ∸ j)) (find-max-lower (f ∘ swap-with-list l') (suc (o ∸ j)))) i    ≡⟨⟩
        swap-with-list l' new-i                                                                             ≤⟨ partial-decomposition-range-low-stays-low f o new-i j' new-i-low (≤-trans n≤sn j≤o) ⟩
        o                                                                                                   ∎
        where
            open ≤-Reasoning
            l' = partial-decomposition-range f o [] j'

            new-i = swp (suc (o ∸ j)) (find-max-lower (f ∘ swap-with-list l') (suc (o ∸ j))) i

            new-i-low : new-i ≤ o
            new-i-low = begin
                new-i                   ≤⟨ low-swp-is-low (suc (o ∸ j)) (find-max-lower (f ∘ swap-with-list l') (suc (o ∸ j))) i o
                    (begin
                        suc (o ∸ j)     ≡⟨ ∸-suc o j j≤o ⟩
                        o ∸ j'          ≤⟨ m∸n≤m o j' ⟩
                        o               ∎)
                    (begin
                        find-max-lower (f ∘ swap-with-list l') (suc (o ∸ j))    ≤⟨ find-max-lower-yields-low (f ∘ swap-with-list l') (suc (o' ∸ j')) ⟩
                        suc (o ∸ j)                                             ≡⟨ ∸-suc o j j≤o ⟩
                        o ∸ j'                                                  ≤⟨ m∸n≤m o j' ⟩
                        o                                                       ∎)
                    i≤o ⟩
                o                       ∎

    partial-decomposition-monotonic-theorem :
        (f : ℕ → A) → (o : ℕ) → (l : SwapList) →
        ∀ (i j : ℕ) → .(i≤j : i ≤ j) → (j≤o : j ≤ o) →
        f (swap-with-list (partial-decomposition f o l) i) ≤A
        f (swap-with-list (partial-decomposition f o l) j)
    partial-decomposition-monotonic-theorem f o l zero zero i≤j j≤o = ≤A-refl
    partial-decomposition-monotonic-theorem f o@(suc o') l i j@(suc j') i≤j j≤o = begin
        f (swap-with-list (partial-decomposition f o l) i)                                                                  ≡⟨ cong (λ q → f (swap-with-list q i)) (partial-decomposition-is-range f o l) ⟩
        f (swap-with-list (partial-decomposition-range f o l o) i)                                                          ≡⟨ cong (λ q → f (swap-with-list (partial-decomposition-range f o l q) i)) (sym (m+[n∸m]≡n j≤o)) ⟩
        f (swap-with-list (partial-decomposition-range f o l (j + (o ∸ j))) i)                                              ≡⟨ cong (λ q → f (swap-with-list q i)) (+-range-split f o l j (o ∸ j) (≤-reflexive (m+[n∸m]≡n j≤o))) ⟩
        f (swap-with-list (partial-decomposition-range f (o ∸ (o ∸ j)) (partial-decomposition-range f o l (o ∸ j)) j) i)    ≡⟨ cong (λ q → f (swap-with-list (partial-decomposition-range f q (partial-decomposition-range f o l (o ∸ j)) j) i)) {o ∸ (o ∸ j)} {j} (m∸[m∸n]≡n j≤o) ⟩
        f (swap-with-list (partial-decomposition-range f j (partial-decomposition-range f o l (o ∸ j)) j) i)                ≡⟨ cong (λ q → f (q i)) (partial-decomposition-range-split-lemma f j (partial-decomposition-range f o l (o ∸ j)) j) ⟩
        f ((swap-with-list l' ∘ swap-with-list (partial-decomposition-range (f ∘ swap-with-list (partial-decomposition-range f o l (o ∸ j))) j [] j)) i)    ≤⟨ find-max-lower-is-max (f ∘ swap-with-list l') {swap-with-list (partial-decomposition-range (f ∘ swap-with-list (partial-decomposition-range f o l (o ∸ j))) j [] j) i} {j} (partial-decomposition-range-low-stays-low (f ∘ swap-with-list (partial-decomposition-range f o l (o ∸ j))) j i j i≤j n≤n) ⟩
        f (swap-with-list l' y)                                                     ≡⟨ cong (f ∘ swap-with-list l') (sym (swp-match₁-lemma j y)) ⟩
        f (swap-with-list l' (swp j y j))                                           ≡⟨ cong (λ q → f (q j)) (sym (swap-pop-initial id l' j y)) ⟩
        f (swap-with-list (pair-at f j l' ∷ l') j)                                  ≡⟨ cong (λ q → f (swap-with-list (pair-at f q l' ∷ l') j)) {j} {suc (o ∸ suc (o ∸ j))} (sym thing≡j) ⟩
        f (swap-with-list (pair-at f (suc (o ∸ suc (o ∸ j))) l' ∷ l') j)            ≡⟨⟩
        f (swap-with-list (partial-decomposition-range f o l (suc (o' ∸ j'))) j)    ≡⟨ cong (λ q → f  (swap-with-list (partial-decomposition-range f o l q) j)) (∸-suc o' j' (s≤s⁻¹ j≤o)) ⟩
        f (swap-with-list (partial-decomposition-range f o l (o ∸ j')) j)           ≡⟨ sym (cong f (partial-decomposition-swap-drop-lemma f o l j' j n≤n (≤-trans n≤sn j≤o))) ⟩
        f (swap-with-list (partial-decomposition f o l) j)                          ∎
        where
            l' = partial-decomposition-range f o l (o ∸ j)

            thing≡j : suc (o ∸ suc (o ∸ j)) ≡ j
            thing≡j =
                suc (o ∸ suc (o ∸ j))   ≡⟨ ∸-suc o (suc (o ∸ j)) (s≤s (m∸n≤m o' j')) ⟩
                o ∸ (o ∸ j)             ≡⟨ m∸[m∸n]≡n {o} {j} j≤o ⟩
                j                       ∎
                where open ≡-Reasoning

            -- the core swap's other position
            y = find-max-lower (f ∘ swap-with-list l') j

            open ≤A-Reasoning
