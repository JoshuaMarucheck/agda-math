open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; _≗_; cong; cong-app; refl; sym; trans; inspect; [_]; ≢-sym)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open import Relation.Binary using (Setoid; Rel; IsEquivalence; IsDecTotalOrder; tri<; tri≈; tri>)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Function using (_∘_; _∋_; ∣_⟩-_; id; flip; Bijective; Bijection; Injective; Surjective)
open import Data.Bool using (true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (ℕ; _≤_; _<_; _>_; z≤n; s≤s; s≤s⁻¹; _∸_; _+_; NonZero; >-nonZero) renaming (zero to zeroℕ; suc to sucℕ; pred to predℕ; _≟_ to _≟ℕ_)
open import Data.Nat.Properties using (module ≤-Reasoning; <-cmp; suc-pred; ≤-reflexive; ≤-refl; ≤-trans; ≤-<-trans; <-≤-trans; <-trans; ≰⇒≥; <⇒≱; ≮⇒≥; <⇒≤; ≰⇒>; ≤-antisym; <-irrefl; +-mono-≤; +-mono-<; +-mono-≤-<; ∸-mono; +-suc; +-comm; +-assoc; n>0⇒n≢0; n∸n≡0; ≤∧≢⇒<; m≤n+m; m∸n≤m; m≤m+n; m+n≤o⇒m≤o; m+n≤o⇒n≤o; m<n⇒0<n∸m; m+n∸n≡m; m+[n∸m]≡n; +-∸-assoc; ∸-monoʳ-<; m∸[m∸n]≡n; m∸n+n≡m)
open import Data.Fin using (Fin; _≟_; _≤?_; _<?_; toℕ; fromℕ<; _↑ˡ_; _↑ʳ_) renaming (zero to zero-fin; suc to suc-fin; pred to pred-fin; _<_ to _<-fin_; _≤_ to _≤-fin_; _≥_ to _≥-fin_)
open import Data.Fin.Properties using (toℕ-fromℕ<; fromℕ<-toℕ; fromℕ<-cong; toℕ<n; toℕ-injective; fromℕ<-injective) renaming (≤-isDecTotalOrder to ≤-fin-isDecTotalOrder)
open import Data.List using (List; foldl; _∷_; []; _∷ʳ_; length; lookup; drop; _++_; reverse; tabulate; map; concat)
open import Data.List.Properties using (drop-drop; reverse-++; ++-identity; foldl-map; foldl-∷ʳ; foldl-cong; map-++; concat-map; map-∘; reverse-map; map-cong; reverse-involutive)
open import Data.List.Relation.Unary.All using (All)

open import Plasmaduck.SetoidExperiment.SetoidMachinery using (discrete-setoid; from-discrete-cong; SetoidFunction₂; _which-is-cong₂_; _←₂_; SetoidFunction; _which-is-cong_; _←_; property-subset-setoid; discrete-function-setoid)
open import Plasmaduck.Function.Properties using (module SingleOperator)
open import Plasmaduck.Util.Case using (case_of_)
open import Plasmaduck.Data.Empty using (¬-recompute)
open import Plasmaduck.Data.FakeFin using (FakeFin; realize; falsify)
open import Plasmaduck.Data.Squash using (Squash; squash)
open import Plasmaduck.Data.Nat using (≤-recompute; ≤-cmp; n≤n; n≤sn; n<sn; m≤n⇒m≤pn; m<n⇒m≢n; ≤→<≡; ≤≥⇒≡; ∸-suc; m∸n∸o≡m∸o∸n; m∸n∸o≡m∸[n+o]; m>0⇒m=sn; m≡spm; s≡s⁻¹; m<o∧n<p⇒s[m+o]<n+p)
open import Plasmaduck.Data.Fin using (toℕ<<n; _↑ˡ-inverted_; fromℕ<-↑ˡ-inverted)
open import Plasmaduck.Data.List using (drop-lookup; foldl-pop; foldl-concat; foldl-reverse'; foldl-reverse; foldl-map-cong)
open import Plasmaduck.Data.Product using (Σ≡; ×≡; uncurry; curry)
open import Plasmaduck.Util.TypeChange using (change-type; change-type-input-dependence-irrelevance; change-type-output-dependence-commute; change-type-proof-irrelevance; cong₂-dependent)
open import Plasmaduck.Relation.Equivalence using (irrelevant-cong; irrelevant-cong₂)
open import Plasmaduck.Function.Bijection using (_∘-bijective_; id-bijective; bijective-is-functional)
open import Plasmaduck.Function.Properties using (Congruent₂; Identity; Associative; Commutative)

open import Plasmaduck.Counting.Permutation.Swap using (swp; swp-involution; swp-is-bijective)
open import Plasmaduck.Counting.Permutation.SwapPermutation as SwapPermutation using (module Monotonicity)
open import Plasmaduck.Counting.Permutation.Defs using (Permutation)
open import Plasmaduck.Counting.Permutation.SwapList using (SwapList; IsSwapDecomposition; swap-with-list)
open import Plasmaduck.Counting.Permutation.FlipList using (FlipList; flip-swap-list; flip-swap-using-list; flip-swap-as-list; flip-swap-list-mapper; decompose-swap; flip-swap-list-is-swap-decomposition)



module Plasmaduck.Counting.Permutation.FlipPermutation where

variable
    a b c α β γ : Level
    n : ℕ


FlipList' : ℕ → Set
FlipList' n = List (FakeFin (predℕ n))

-- decompose-inverse : (p : Permutation n) → FlipList' n
-- decompose-inverse {n = zeroℕ} p = []
-- decompose-inverse {n = sucℕ n'} p = concat (map (uncurry flip-swap-list) (SwapPermutation.decompose-permutation p))

decompose-permutation : (p : Permutation n) → FlipList' n
decompose-permutation {n = zeroℕ} p = []
decompose-permutation {n = sucℕ n'} p = concat (map (uncurry flip-swap-list) (SwapPermutation.decompose-inverse p))

is-permutation-decomposition : (p : Permutation (sucℕ n)) → (p .Bijection.to) ≗ flip-swap-using-list (decompose-permutation p)
is-permutation-decomposition {n = zeroℕ} p zero-fin with p .Bijection.to zero-fin | inspect (p .Bijection.to) zero-fin
... | zero-fin | [ p= ] = refl
is-permutation-decomposition {n = n@(sucℕ n')} p k =
    p .Bijection.to k                                                   ≡⟨ sym (SwapPermutation.is-permutation-decomposition p k) ⟩ -- sym (SwapPermutation.is-permutation-decomposition p k) ⟩
    swap-with-list decompose-p k                                        ≡⟨⟩
    foldl (λ acc (i , j) → swp i j ∘ acc) id decompose-p k              ≡⟨ cong-app ((foldl-cong {f = λ acc (i , j) → swp i j ∘ acc} {∣ flip _∘'_ ⟩- uncurry swp} (λ x y → refl) id) decompose-p) k ⟩
    foldl (∣ flip _∘'_ ⟩- uncurry swp) id decompose-p k                 ≡⟨ sym (cong-app (foldl-map (flip _∘'_) (uncurry swp) id decompose-p) k) ⟩
    foldl (flip _∘'_) id (map (uncurry swp) decompose-p) k              ≡⟨ foldl-reverse' f-setoid {_∘'_} ∘-cong ∘-id (λ _ → refl) (map (uncurry swp) decompose-p) k ⟩
    foldl _∘'_ id (reverse (map (uncurry swp) decompose-p)) k           ≡⟨ cong (λ q → foldl _∘'_ id q k) (sym (reverse-map (uncurry swp) decompose-p)) ⟩
    foldl _∘'_ id (map (uncurry swp) (reverse decompose-p)) k           ≡⟨ cong (λ q → foldl _∘'_ id (map (uncurry swp) q) k) (reverse-involutive invert-decompose-p) ⟩
    foldl _∘'_ id (map (uncurry swp) invert-decompose-p) k                                                                      ≡⟨ foldl-map-cong f-setoid f-setoid (discrete-setoid (Fin (sucℕ n) × Fin (sucℕ n))) {_∘'_} ∘-cong id (uncurry swp) alt-swp (λ { {ij} refl k → swp-via-flip ij k }) invert-decompose-p k ⟩
    foldl _∘'_ id (map (foldl (_∘'_) id ∘ map flip-swap-list-mapper ∘ (uncurry flip-swap-list)) invert-decompose-p) k           ≡⟨ cong (λ q → foldl _∘'_ id q k) (map-∘ {g = foldl (_∘'_) id ∘ map flip-swap-list-mapper} {uncurry flip-swap-list} invert-decompose-p) ⟩
    foldl _∘'_ id (map (foldl (_∘'_) id ∘ map flip-swap-list-mapper) (map (uncurry flip-swap-list) invert-decompose-p)) k       ≡⟨ cong (λ q → foldl _∘'_ id q k) (map-∘ {g = foldl (_∘'_) id} {map flip-swap-list-mapper} (map (uncurry flip-swap-list) invert-decompose-p)) ⟩
    foldl _∘'_ id (map (foldl _∘'_ id) (map (map flip-swap-list-mapper) (map (uncurry flip-swap-list) invert-decompose-p))) k   ≡⟨ foldl-concat f-setoid {_∘'_} ∘-cong {Function.id} ∘-id (λ _ → refl) (map (map flip-swap-list-mapper) ((map (uncurry flip-swap-list) invert-decompose-p))) k ⟩
    foldl _∘'_ id (concat (map (map flip-swap-list-mapper) ((map (uncurry flip-swap-list) invert-decompose-p)))) k              ≡⟨ cong (λ q → foldl _∘'_ id q k) (concat-map {f = flip-swap-list-mapper} ((map (uncurry flip-swap-list) invert-decompose-p))) ⟩
    foldl _∘'_ id (map flip-swap-list-mapper (concat (map (uncurry flip-swap-list) invert-decompose-p))) k                      ≡⟨ cong-app (foldl-map _∘'_ flip-swap-list-mapper id (concat (map (uncurry flip-swap-list) invert-decompose-p))) k ⟩
    foldl (∣ _∘'_ ⟩- flip-swap-list-mapper) id (concat (map (uncurry flip-swap-list) invert-decompose-p)) k                     ≡⟨⟩
    flip-swap-using-list (decompose-permutation p) k                                                                            ∎
    where
        open ≡-Reasoning

        invert-decompose-p : SwapList (sucℕ n)
        invert-decompose-p = SwapPermutation.decompose-inverse p

        decompose-p = reverse invert-decompose-p

        _∘'_ = λ g f → g ∘ f

        f-setoid = discrete-function-setoid (Fin (sucℕ n)) (Fin (sucℕ n))
        open Setoid f-setoid using (_≈_)

        ∘-cong : Congruent₂ _≈_ _≈_ _≈_ _∘'_
        ∘-cong {g₁} {g₂} {f₁} {f₂} g₁≈g₂ f₁≈f₂ x = trans (cong g₁ (f₁≈f₂ x)) (g₁≈g₂ (f₂ x))

        ∘-id : Identity f-setoid _∘'_ Function.id
        ∘-id = (λ {x} x₁ → refl) , (λ {x} x₁ → refl)

        alt-swp = foldl _∘'_ id ∘ map (flip-swap-list-mapper {n}) ∘ uncurry flip-swap-list

        swp-via-flip : ∀ ij k → uncurry swp ij k ≡ alt-swp ij k
        swp-via-flip (i , j) k =
            uncurry swp (i , j) k                                                                   ≡⟨⟩
            swp i j k                                                                               ≡⟨ sym (flip-swap-list-is-swap-decomposition i j k) ⟩
            flip-swap-using-list (flip-swap-list i j) k                                             ≡⟨⟩
            foldl (∣ _∘'_ ⟩- flip-swap-list-mapper) id (flip-swap-list i j) k                       ≡⟨ cong-app (sym (foldl-map _∘'_ flip-swap-list-mapper id (flip-swap-list i j))) k ⟩
            foldl _∘'_ id (map flip-swap-list-mapper (flip-swap-list i j)) k                        ≡⟨⟩
            (foldl _∘'_ id ∘ map flip-swap-list-mapper ∘ uncurry flip-swap-list) (i , j) k          ∎



-- module FlipSort (A-setoid : Setoid a α) where
--     open Setoid A-setoid using (_≈_) renaming (
--         Carrier to A
--         )
        
--     flip-permutation-assoc-comm : 
--         {_*_ : A → A → A} →
--         Congruent₂ _≈_ _≈_ _≈_ _*_ →
--         Associative A-setoid _*_ →
--         Commutative A-setoid _*_ →
--         (generate : Fin n → A) →
--         (p : Permutation n)

