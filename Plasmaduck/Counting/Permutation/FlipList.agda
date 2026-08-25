open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; _≗_; cong; cong-app; refl; sym; trans; inspect; [_]; ≢-sym)
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
open import Data.Nat.Properties using (module ≤-Reasoning; <-cmp; suc-pred; ≤-reflexive; ≤-refl; ≤-trans; ≤-<-trans; <-≤-trans; <-trans; ≰⇒≥; <⇒≱; ≮⇒≥; <⇒≤; ≰⇒>; ≤-antisym; <-irrefl; +-mono-≤; +-mono-<; +-mono-≤-<; ∸-mono; +-suc; +-comm; +-assoc; n>0⇒n≢0; n∸n≡0; ≤∧≢⇒<; m≤n+m; m∸n≤m; m≤m+n; m+n≤o⇒m≤o; m+n≤o⇒n≤o; m<n⇒0<n∸m; m+n∸n≡m; m+[n∸m]≡n; +-∸-assoc; ∸-monoʳ-<; m∸[m∸n]≡n; m∸n+n≡m)
open import Data.List using (List; foldl; _∷_; []; _∷ʳ_; length; lookup; drop; _++_; reverse; tabulate; map)
open import Data.List.Properties using (drop-drop; reverse-++; ++-identity; foldl-map; foldl-∷ʳ; foldl-cong; map-++; foldl-++)
open import Data.List.Relation.Unary.All using (All)

open import Plasmaduck.SetoidExperiment.SetoidMachinery using (discrete-setoid; from-discrete-cong; SetoidFunction₂; _which-is-cong₂_; _←₂_; SetoidFunction; _which-is-cong_; _←_; property-subset-setoid; discrete-function-setoid)
open import Plasmaduck.Function.Properties using (module SingleOperator)
open import Plasmaduck.Util.Case using (case_of_)
open import Plasmaduck.Data.Empty using (¬-recompute)
open import Plasmaduck.Data.FakeFin using (FakeFin; realize; falsify)
open import Plasmaduck.Data.Squash using (Squash; squash)
open import Plasmaduck.Data.Nat using (≤-recompute; ≤-cmp; n≤n; n≤sn; n<sn; m≤n⇒m≤pn; m<n⇒m≢n; ≤→<≡; ≤≥⇒≡; ∸-suc; m∸n∸o≡m∸o∸n; m∸n∸o≡m∸[n+o]; m>0⇒m=sn; m≡spm; s≡s⁻¹; m<o∧n<p⇒s[m+o]<n+p)
open import Plasmaduck.Data.Fin using (toℕ<<n; _↑ˡ-inverted_; fromℕ<-↑ˡ-inverted)
open import Plasmaduck.Data.List using (drop-lookup; foldl-pop; All-++)
open import Plasmaduck.Data.Product using (Σ≡; ×≡; uncurry; curry)
open import Plasmaduck.Data.Squash using (irrelevant-inspect)
open import Plasmaduck.Util.TypeChange using (change-type; change-type-input-dependence-irrelevance; change-type-output-dependence-commute; change-type-proof-irrelevance; cong₂-dependent)
open import Plasmaduck.Relation.Equivalence using (irrelevant-cong; irrelevant-cong₂)
open import Plasmaduck.Function.Bijection using (_∘-bijective_; id-bijective; bijective-is-functional)
open import Plasmaduck.Function using (_≈_; ≈-sym)


open import Plasmaduck.Counting.Permutation.Defs using (IsNFunc; IsNFuncLower; IsNFunc-transferrable)
open import Plasmaduck.Counting.Permutation.Swap using (swp; swp-flip; swp-nfunc-lower; swp-nfunc; swp-matchₐ-lemma; swp-contract-three')



module Plasmaduck.Counting.Permutation.FlipList where

variable
    a b c : Level
    m n : ℕ


flip : ℕ → ℕ → ℕ
flip i x = swp i (suc i) x

-- Using flips, swap index i with index i + j
flip-swap : (i j : ℕ) → ℕ → ℕ
flip-swap i zero = id
flip-swap i (suc zero) = flip i
flip-swap i (suc (suc j)) = flip (suc j + i) ∘ flip-swap i (suc j) ∘ flip (suc j + i)

decompose-swap-helper : ℕ → ℕ → ℕ → ℕ
decompose-swap-helper i j = flip-swap i (j ∸ i)

-- flip-swap-valid : (n i j : ℕ) → i + j < n → IsNFuncLower n (flip-swap i j)
-- flip-swap-valid n i zero i+j<n {k} k<n = k<n
-- flip-swap-valid n i (suc zero) i+j<n {k} k<n = {!   swp-nfunc-lower   !}
-- flip-swap-valid n i (suc (suc j)) i+j<n {k} k<n = {!   !}
    -- begin
    -- suc (flip-swap i j k) ≤⟨ {!   !} ⟩
    -- suc (flip-swap i j k) ≤⟨ {!   !} ⟩
    -- n ∎
    -- where open ≤-Reasoning
IsDecompositionOfSwap : (i j : ℕ) → (ℕ → ℕ) → Set
IsDecompositionOfSwap i j f = ∀ k → f k ≡ swp i j k

decompose-swap : (i j : ℕ) → ℕ → ℕ
decompose-swap i j with ≤-cmp i j
... | inj₁ i≤j = flip-swap i (j ∸ i)
... | inj₂ i>j = flip-swap j (i ∸ j)

-- decompose-swap' : (i j : Fin n) → Fin n → Fin n
-- decompose-swap' {n = zero} ()
-- decompose-swap' {n = suc _} i j = decompose-swap {i = i} {j} (s≤s⁻¹ (toℕ<n i)) (s≤s⁻¹ (toℕ<n j))

decompose-swap-arg-flip : (i j : ℕ) → decompose-swap i j ≡ decompose-swap j i
decompose-swap-arg-flip i j with ≤-cmp i j | ≤-cmp j i
... | inj₂ i>j | inj₂ j>i = ⊥-elim (<-irrefl refl (<-trans i>j j>i))
... | inj₂ i>j | inj₁ j≤i = refl
... | inj₁ i≤j | inj₂ j>i = refl
... | inj₁ i≤j | inj₁ j≤i with i ≟ j
...     | yes refl = refl
...     | no i≠j = ⊥-elim (i≠j (≤-antisym i≤j j≤i))

decompose-swap=decompose-swap-helper : (i j : ℕ) → .(i≤j : i ≤ j) → decompose-swap i j ≡ flip-swap i (j ∸ i)
decompose-swap=decompose-swap-helper i j i≤j with ≤-cmp i j
... | inj₁ _ = refl
... | inj₂ i>j = ⊥-elim (<-irrefl refl (≤-<-trans (≤-recompute i≤j) i>j))

decompose-swap-helper-is-swap-decomposition : (i j : ℕ) → .(i≤j : i ≤ j) → IsDecompositionOfSwap i j (flip-swap i (j ∸ i))
decompose-swap-helper-is-swap-decomposition zero zero i≤j k = sym (swp-matchₐ-lemma zero k)
decompose-swap-helper-is-swap-decomposition i j@(suc j') i≤j k with i ≟ j | i ≟ j'
... | yes refl | _ =
    flip-swap j (j ∸ j) k     ≡⟨ cong (λ q → flip-swap j q k) (n∸n≡0 j) ⟩
    flip-swap j 0 k                     ≡⟨⟩
    k                                               ≡⟨ sym (swp-matchₐ-lemma j k) ⟩
    swp j j k       ∎
    where open ≡-Reasoning

... | no i≠j | yes refl =
    flip-swap j' (j ∸ j') k     ≡⟨⟩
    flip-swap j' (j ∸ j') k     ≡⟨ cong (λ q → flip-swap j' q k) {j ∸ j'} {1} (trans (sym (∸-suc j j n≤n)) (cong suc (n∸n≡0 j))) ⟩
    flip-swap j' (1) k          ≡⟨⟩
    flip j' k                   ≡⟨⟩
    swp j' j k                  ∎
    where open ≡-Reasoning
...  | no i≠j | no i≠j' =
    flip-swap i (j ∸ i) k                   ≡⟨⟩
    flip-swap i (suc j' ∸ i) k            ≡⟨ cong (λ q → flip-swap i q k) (cong (λ q → suc q ∸ i) (sym sj''=j')) ⟩
    flip-swap i (suc (suc j'') ∸ i) k     ≡⟨ cong (λ q → flip-swap i q k) (trans (sym (∸-suc (suc j'') i i≤sj'')) (cong suc (sym (∸-suc j'' i i≤j'')))) ⟩
    flip-swap i (suc (suc (j'' ∸ i))) k   ≡⟨⟩
    (flip (suc (j'' ∸ i) + i) ∘ flip-swap i (suc (j'' ∸ i)) ∘ flip (suc (j'' ∸ i) + i)) k   ≡⟨ cong (λ q → (q ∘ flip-swap i (suc (j'' ∸ i)) ∘ q) k) flip= ⟩
    (flip j' ∘ flip-swap i (suc (j'' ∸ i))    ∘ flip j') k        ≡⟨ cong (λ q → (flip j' ∘ flip-swap i q ∘ flip j') k) (trans (∸-suc j'' i i≤j'') (cong (_∸ i) sj''=j')) ⟩
    (flip j' ∘ flip-swap i (j' ∸ i)           ∘ flip j') k        ≡⟨⟩
    (flip j' ∘ flip-swap i (j' ∸ i)             ∘ flip j') k        ≡⟨ cong (flip j') (decompose-swap-helper-is-swap-decomposition i j' i≤j' (flip j' k)) ⟩
    (flip j' ∘ swp i j'                         ∘ flip j') k        ≡⟨ swp-contract-three' {j} {j'} {i} (≢-sym i≠j) (≢-sym i≠j') k ⟩
    swp i j k                                                       ∎
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
        j'' = pred j'

        sj''=j' : suc j'' ≡ j'
        sj''=j' = sym (m≡spm {j'} (n>0⇒n≢0 (≤-<-trans z≤n i<j')))

        i≤j'' : i ≤ j''
        i≤j'' with ≤→<≡ i≤j
        ... | inj₂ i=j = ⊥-elim (i≠j i=j)
        ... | inj₁ i<j with ≤→<≡ (s≤s⁻¹ i<j)
        ...     | inj₂ i=j' = ⊥-elim (i≠j' i=j')
        ...     | inj₁ i<j' = s≤s⁻¹ (<-≤-trans i<j' (≤-reflexive (sym sj''=j')))

        i≤sj'' : i ≤ suc j''
        i≤sj'' = ≤-trans i≤j'' n≤sn

        i≤j' : i ≤ j'
        i≤j' = ≤-trans i≤sj'' (≤-reflexive sj''=j')

        flip= : flip (suc (j'' ∸ i) + i) ≡ flip j'
        flip= = cong flip (trans (cong suc (m∸n+n≡m {j''} {i} i≤j'')) sj''=j')

        open ≡-Reasoning

decompose-swap-is-swap-decomposition : (i j : ℕ) → IsDecompositionOfSwap i j (decompose-swap i j)
decompose-swap-is-swap-decomposition i j k with ≤-cmp i j
... | inj₁ i≤j = decompose-swap-helper-is-swap-decomposition i j i≤j k
... | inj₂ i>j =
    flip-swap j (i ∸ j) k   ≡⟨ decompose-swap-helper-is-swap-decomposition j i (<⇒≤ i>j) k ⟩
    swp j i k               ≡⟨ swp-flip j i k ⟩
    swp i j k               ∎
    where open ≡-Reasoning

decompose-swap-valid : {n i j : ℕ} → i < n → j < n → IsNFunc n (decompose-swap i j)
decompose-swap-valid {n} {i} {j} i<n j<n = IsNFunc-transferrable n (swp i j) (decompose-swap i j) (λ k → sym ((decompose-swap-is-swap-decomposition i j) k)) (swp-nfunc i<n j<n)


------------------------------------------------
-- Now we decompose swap into a list of flips --
------------------------------------------------

-- A list for flipping (1 + n) items
FlipList : Set
FlipList = List ℕ

-- In particular, if you have IsValidFlipList n l, then l is a list that can be used to flip nats < n.
IsValidFlipList : ℕ → FlipList → Set
IsValidFlipList n l = All (λ q → suc q < n) l

-- Using flips, swap index i with index i + j
flip-swap-list-helper : (i j : ℕ) → FlipList
flip-swap-list-helper i zero = []
flip-swap-list-helper i (suc zero) = i ∷ []
flip-swap-list-helper i (suc (suc j)) = suc j + i ∷ flip-swap-list-helper i (suc j) ++ suc j + i ∷ []

flip-swap-list-acc : (ℕ → ℕ) → ℕ → (ℕ → ℕ)
flip-swap-list-acc = ∣ (λ g f → g ∘ f) ⟩- flip
-- equivalent to: f ∘ flip i

flip-swap-using-list : FlipList → ℕ → ℕ
flip-swap-using-list l = foldl flip-swap-list-acc id l

flip-swap-using-list-pop-last :
    (l : FlipList) → (x : ℕ) →
    flip-swap-using-list (l ∷ʳ x) ≗
    flip-swap-using-list l ∘ flip x
flip-swap-using-list-pop-last l x k =
    flip-swap-using-list (l ∷ʳ x) k                                         ≡⟨⟩
    foldl flip-swap-list-acc id (l ∷ʳ x) k                                  ≡⟨⟩
    foldl flip-swap-list-acc id (l ++ x ∷ []) k                             ≡⟨ cong-app (foldl-++ flip-swap-list-acc id l (x ∷ [])) k ⟩
    foldl flip-swap-list-acc (foldl flip-swap-list-acc id l) (x ∷ []) k     ≡⟨⟩
    (foldl flip-swap-list-acc id l ∘ flip x) k                              ∎
    where open ≡-Reasoning

flip-swap-as-list :
    (i j : ℕ) →
    ∀ k → flip-swap i j k ≡ flip-swap-using-list (flip-swap-list-helper i j) k
flip-swap-as-list i zero k = refl
flip-swap-as-list i (suc zero) k = refl
flip-swap-as-list i j@(suc j'@(suc j'')) k =
    flip-swap i j k                                                                                         ≡⟨⟩
    (flip (j' + i) ∘ flip-swap i j' ∘ flip (j' + i)) k                                                      ≡⟨ cong (flip (j' + i)) (flip-swap-as-list i j' (flip (j' + i) k)) ⟩
    (flip (j' + i) ∘ flip-swap-using-list (flip-swap-list-helper i j') ∘ flip (j' + i)) k                   ≡⟨ cong (λ q → (flip (j' + i) ∘ q ∘ flip (j' + i)) k) (sym (lemma (flip-swap-list-helper i j'))) ⟩
    (flip (j' + i) ∘ foldl (λ g f → g ∘ f) id (map flip (flip-swap-list-helper i j')) ∘ flip (j' + i)) k    ≡⟨ sym (foldl-pop (discrete-function-setoid ℕ ℕ) {λ g f → g ∘ f} (λ _ → refl) (λ {f} g=h x → cong f (g=h x)) (flip (j' + i)) id l-center (flip (j' + i) k)) ⟩
    (foldl (λ g f → g ∘ f) (flip (j' + i)) (map flip (flip-swap-list-helper i j')) ∘ flip (j' + i)) k       ≡⟨⟩
    (foldl (λ g f → g ∘ f) id (flip (j' + i) ∷ map flip (flip-swap-list-helper i j')) ∘ flip (j' + i)) k    ≡⟨ cong-app (sym (foldl-∷ʳ (λ g f → g ∘ f) id (flip (j' + i)) l-left)) k ⟩
    foldl (λ g f → g ∘ f) id (flip (j' + i) ∷ map flip (flip-swap-list-helper i j') ∷ʳ flip (j' + i)) k     ≡⟨ cong (λ q → foldl (λ g f → g ∘ f) id q k) (sym (map-++ flip l'-left (j' + i ∷ []))) ⟩
    foldl (λ g f → g ∘ f) id (map flip (j' + i ∷ flip-swap-list-helper i j' ∷ʳ (j' + i))) k                 ≡⟨ cong-app (lemma l'-full) k ⟩
    flip-swap-using-list (flip-swap-list-helper i j) k                                                      ∎
    where
        open ≡-Reasoning
        l-center = map flip (flip-swap-list-helper i j')
        l-left = flip (j' + i) ∷ map flip (flip-swap-list-helper i j')
        l-full = flip (j' + i) ∷ map flip (flip-swap-list-helper i j') ∷ʳ flip (j' + i)

        l'-center = flip-swap-list-helper i j'
        l'-left = j' + i ∷ flip-swap-list-helper i j'
        l'-full = j' + i ∷ flip-swap-list-helper i j' ∷ʳ (j' + i)

        lemma :
            (l : FlipList) →
            foldl (λ g f → g ∘ f) id (map flip l) ≡
            flip-swap-using-list l
        lemma l =
            foldl (λ g f → g ∘ f) id (map flip l)       ≡⟨ foldl-map (λ g f → g ∘ f) flip id l ⟩
            (foldl (∣ (λ g f → g ∘ f) ⟩- flip) id l)    ≡⟨⟩
            (foldl flip-swap-list-acc id l)             ≡⟨⟩
            (flip-swap-using-list l)                    ∎

flip-swap-list-helper-is-swap-decomposition : (i j : ℕ) → .(i≤j : i ≤ j) → IsDecompositionOfSwap i j (flip-swap-using-list (flip-swap-list-helper i (j ∸ i)))
flip-swap-list-helper-is-swap-decomposition i j i≤j k =
    flip-swap-using-list (flip-swap-list-helper i (j ∸ i)) k    ≡⟨ sym (flip-swap-as-list i (j ∸ i) k) ⟩
    flip-swap i (j ∸ i) k                                       ≡⟨⟩
    decompose-swap-helper i j k                                 ≡⟨ decompose-swap-helper-is-swap-decomposition i j i≤j k ⟩
    swp i j k                                                   ∎
    where open ≡-Reasoning

-- using flips, swap indices i and j
flip-swap-list : ℕ → ℕ → FlipList
flip-swap-list i j with ≤-cmp i j
... | inj₁ i≤j = flip-swap-list-helper i (j ∸ i)
... | inj₂ i>j = flip-swap-list-helper j (i ∸ j)

flip-swap-list-is-swap-decomposition : (i j : ℕ) → IsDecompositionOfSwap i j (flip-swap-using-list (flip-swap-list i j))
flip-swap-list-is-swap-decomposition i j k with ≤-cmp i j
... | inj₁ i≤j = flip-swap-list-helper-is-swap-decomposition i j i≤j k
... | inj₂ i>j =
    (flip-swap-using-list (flip-swap-list-helper j (i ∸ j))) k  ≡⟨ flip-swap-list-helper-is-swap-decomposition j i (<⇒≤ i>j) k ⟩
    swp j i k                                                   ≡⟨ swp-flip j i k ⟩
    swp i j k                                                   ∎
    where
        open ≡-Reasoning

flip-swap-list-helper-is-valid : (n i j : ℕ) → (j + i < n) →
    IsValidFlipList n (flip-swap-list-helper i j)
flip-swap-list-helper-is-valid n i zero j+i<n = All.[]
flip-swap-list-helper-is-valid n i (suc zero) j+i<n = j+i<n All.∷ All.[]
flip-swap-list-helper-is-valid n i (suc (suc j)) j+i<n = All-++ {l = suc (j + i) ∷ flip-swap-list-helper i (suc j)} {suc (j + i) ∷ []} (j+i<n All.∷ flip-swap-list-helper-is-valid n i (suc j) (≤-trans n≤sn j+i<n)) (j+i<n All.∷ All.[])

flip-swap-list-is-valid : (n i j : ℕ) → (i < n) → (j < n) →
    IsValidFlipList n (flip-swap-list i j)
flip-swap-list-is-valid n i j i<n j<n with ≤-cmp i j
... | inj₁ i≤j = flip-swap-list-helper-is-valid n i (j ∸ i) (≤-<-trans (≤-reflexive (m∸n+n≡m {j} {i} i≤j)) j<n)
... | inj₂ i>j = flip-swap-list-helper-is-valid n j (i ∸ j) (≤-<-trans (≤-reflexive (m∸n+n≡m {i} {j} (<⇒≤ i>j))) i<n)

flip-swap-using-list-is-valid : {n i j : ℕ} → (i < n) → (j < n) → IsNFunc n (flip-swap-using-list (flip-swap-list i j))
flip-swap-using-list-is-valid {n} {i} {j} i<n j<n = IsNFunc-transferrable n (swp i j) (flip-swap-using-list (flip-swap-list i j)) (λ k → sym (flip-swap-list-is-swap-decomposition i j k)) (swp-nfunc i<n j<n)
