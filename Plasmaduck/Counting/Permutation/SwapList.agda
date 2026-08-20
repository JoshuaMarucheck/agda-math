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

open import Plasmaduck.Counting.Permutation.Swap using (swp; swp-involution; swp-is-bijective)



module Plasmaduck.Counting.Permutation.SwapList where

variable
    a b c : Level
    m n : ℕ


SwapList : ℕ → Set
SwapList n = List (Fin n × Fin n)

swap-with-things : (Fin n → Fin n) → SwapList n → Fin n → Fin n
swap-with-things = foldl (λ acc (i , j) → swp i j ∘ acc)

swap-with-list : SwapList n → Fin n → Fin n
swap-with-list l k = swap-with-things id l k

IsSwapDecomposition : (Fin n → Fin n) → SwapList n → Set
IsSwapDecomposition p l = ∀ k → swap-with-list l k ≡ p k

SwapDecomposition : (Fin n → Fin n) → Set
SwapDecomposition {n} p = Σ (SwapList n) (IsSwapDecomposition p)

swap-pop-func :
    (start : Fin m → Fin m)
    (l : SwapList m) →
    swap-with-things start l ≡ swap-with-things id l ∘ start
swap-pop-func start [] = refl
swap-pop-func start (ij@(i , j) ∷ l) =
    swap-with-things start (ij ∷ l)             ≡⟨⟩
    swap-with-things (swp i j ∘ start) l        ≡⟨ swap-pop-func (swp i j ∘ start) l ⟩
    (swap-with-things id l ∘ swp i j ∘ start)   ≡⟨ cong (_∘ start) (sym (swap-pop-func (swp i j) l)) ⟩
    (swap-with-things id (ij ∷ l) ∘ start)      ∎
    where open ≡-Reasoning

swap-pop-initial :
    (start : Fin m → Fin m)
    (l : SwapList m) →
    (i j : Fin m) →
    swap-with-things start ((i , j) ∷ l) ≡ (swap-with-things id l ∘ swp i j ∘ start)
swap-pop-initial start l i j = swap-pop-func (swp i j ∘ start) l

++-swap-split :
    (start : Fin m → Fin m)
    (l₁ l₂ : SwapList m) →
    swap-with-things start (l₁ ++ l₂) ≡ swap-with-list l₂ ∘ swap-with-things start l₁
++-swap-split start [] l₂ = swap-pop-func start l₂
++-swap-split start ((x , y) ∷ l₁) l₂ =
    swap-with-things start (((x , y) ∷ l₁) ++ l₂)               ≡⟨⟩
    swap-with-things (swp x y ∘ start) (l₁ ++ l₂)               ≡⟨ ++-swap-split (swp x y ∘ start) l₁ l₂ ⟩
    swap-with-list l₂ ∘ swap-with-things (swp x y ∘ start) l₁   ≡⟨⟩
    swap-with-list l₂ ∘ swap-with-things start ((x , y) ∷ l₁)   ∎
    where open ≡-Reasoning

swap-with-list-reverse-is-right-inverse : (l : SwapList n) (k : Fin n) → (swap-with-list l ∘ swap-with-list (reverse l)) k ≡ k
swap-with-list-reverse-is-right-inverse [] k = refl
swap-with-list-reverse-is-right-inverse (x ∷ l) k =
    (swap-with-list (x ∷ l) ∘ swap-with-list (reverse (x ∷ l))) k                                           ≡⟨⟩
    (swap-with-list ((x ∷ []) ++ l) ∘ swap-with-list (reverse ((x ∷ []) ++ l))) k                           ≡⟨ cong (λ q → (swap-with-list ((x ∷ []) ++ l) ∘ swap-with-list q) k) (reverse-++ (x ∷ []) l) ⟩
    (swap-with-list ((x ∷ []) ++ l) ∘ swap-with-list (reverse l ++ (x ∷ []))) k                             ≡⟨ cong-app (cong (_∘ swap-with-list (reverse l ++ (x ∷ []))) (++-swap-split id (x ∷ []) l)) k ⟩
    (swap-with-list l ∘ swap-with-list (x ∷ []) ∘ swap-with-list (reverse l ++ (x ∷ []))) k                 ≡⟨ cong-app (cong ((swap-with-list l ∘ swap-with-list (x ∷ [])) ∘_) (++-swap-split id (reverse l) (x ∷ []))) k ⟩
    (swap-with-list l ∘ swap-with-list (x ∷ []) ∘ swap-with-list (x ∷ []) ∘ swap-with-list (reverse l)) k   ≡⟨ cong (swap-with-list l) (swp-involution (x .proj₁) (x .proj₂) (swap-with-list (reverse l) k)) ⟩
    (swap-with-list l ∘ swap-with-list (reverse l)) k                                                       ≡⟨ swap-with-list-reverse-is-right-inverse l k ⟩
    k                                                                                                  ∎
    where open ≡-Reasoning

-- this is horrendous
swap-with-list-bijective : (l : SwapList n) → Bijective _≡_ _≡_ (swap-with-list l)
swap-with-list-bijective [] = id-bijective
swap-with-list-bijective {n = n} ((i , j) ∷ l) =
    bijective-is-functional
        {A-setoid = discrete-setoid (Fin n)}
        {B-setoid = discrete-setoid (Fin n)}
        {f = record {func = f; respects = from-discrete-cong disc-n f}}
        {g = record {func = g; respects = from-discrete-cong disc-n g}}
        (cong-app (sym (swap-pop-initial id l i j)))
        (_∘-bijective_ {s₁ = disc-n} {s₂ = disc-n} {s₃ = disc-n}
            {g = swap-with-list l} (swap-with-list-bijective l)
            {f = swp i j} (swp-is-bijective i j)
        )
    where
        disc-n = discrete-setoid (Fin n)
        f = swap-with-list l ∘ swp i j
        g = swap-with-list ((i , j) ∷ l)
