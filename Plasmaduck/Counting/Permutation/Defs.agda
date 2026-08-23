open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; cong; cong-app; refl; sym; trans; inspect; [_]; ≢-sym)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open import Relation.Binary using (Setoid; Rel; IsEquivalence; IsDecTotalOrder; tri<; tri≈; tri>)
open import Relation.Nullary using (¬_; Dec; yes; no) renaming (recompute to dec-recompute)
open import Relation.Nullary.Recomputable using (Recomputable; _→-recompute_; _×-recompute_)
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



module Plasmaduck.Counting.Permutation.Defs where

variable
    a b c : Level
    m n : ℕ


fakefin-setoid : ℕ → Setoid lzero lzero
fakefin-setoid n = discrete-setoid (FakeFin n)

FakeFinPermutation : ℕ → Set
FakeFinPermutation n = Bijection (fakefin-setoid n) (fakefin-setoid n)

IsNFuncLower : ℕ → (ℕ → ℕ) → Set
IsNFuncLower n f = ∀ {i} → i < n → f i < n

IsNFuncUpper : ℕ → (ℕ → ℕ) → Set
IsNFuncUpper n f = ∀ {i} → i ≥ n → f i ≡ i

IsNFunc : ℕ → (ℕ → ℕ) → Set
IsNFunc n f = IsNFuncLower n f × IsNFuncUpper n f

NFunc : ℕ → Set
NFunc n = Σ (ℕ → ℕ) (Squash ∘ IsNFunc n)


--------------------------------
--- Some Properties of NFunc ---
--------------------------------

IsNFuncLower-∘ : {n : ℕ} {g f : ℕ → ℕ} → IsNFuncLower n g → IsNFuncLower n f → IsNFuncLower n (g ∘ f)
IsNFuncLower-∘ g-is-nfunc-lower f-is-nfunc-lower i<n = g-is-nfunc-lower (f-is-nfunc-lower i<n)

IsNFuncUpper-∘ : {n : ℕ} {g f : ℕ → ℕ} → IsNFuncUpper n g → IsNFuncUpper n f → IsNFuncUpper n (g ∘ f)
IsNFuncUpper-∘ {n} {g} {f} g-is-nfunc-upper f-is-nfunc-upper {i} i≥n = trans (g-is-nfunc-upper fi≥n) fi=i
    where
        fi=i : f i ≡ i
        fi=i = f-is-nfunc-upper i≥n
        
        fi≥n : f i ≥ n
        fi≥n = ≤-trans i≥n (≤-reflexive (sym fi=i))

IsNFunc-∘ : {n : ℕ} {g f : ℕ → ℕ} → IsNFunc n g → IsNFunc n f → IsNFunc n (g ∘ f)
IsNFunc-∘ g-nfunc f-nfunc = IsNFuncLower-∘ (g-nfunc .proj₁) (f-nfunc .proj₁) , IsNFuncUpper-∘ (g-nfunc .proj₂) (f-nfunc .proj₂)

IsNFuncLower-recompute : (n : ℕ) → (f : ℕ → ℕ) → Recomputable (IsNFuncLower n f)
IsNFuncLower-recompute n f fi<n-irr i<n = ≤-recompute (fi<n-irr i<n)

IsNFuncUpper-recompute : (n : ℕ) → (f : ℕ → ℕ) → Recomputable (IsNFuncUpper n f)
IsNFuncUpper-recompute n f fi=i-irr {i} i≥n = dec-recompute (f i ≟ i) (fi=i-irr i≥n)

IsNFunc-recompute : (n : ℕ) → (f : ℕ → ℕ) → Recomputable (IsNFunc n f)
IsNFunc-recompute n f f-nfunc = (IsNFuncLower-recompute n f ×-recompute IsNFuncUpper-recompute n f) f-nfunc

id-nfunc : {n : ℕ} → IsNFunc n id
id-nfunc = id , (λ _ → refl)


-----------
--- swp ---
-----------

-- i hate proving things using with abstraction
swp-helper : (i j k : ℕ) → Dec (i ≡ k) → Dec (j ≡ k) → ℕ
swp-helper i j k (yes _) _ = j
swp-helper i j k (no _) (yes _) = i
swp-helper i j k (no _) (no _) = k

swp : ℕ → ℕ → ℕ → ℕ
swp i j k = swp-helper i j k (i ≟ k) (j ≟ k)

swp≤ : {i j k : ℕ} → i ≤ n → j ≤ n → k ≤ n → swp i j k ≤ n
swp≤ {i = i} {j} {k} i≤n j≤n k≤n with (i ≟ k) | (j ≟ k) 
... | (yes _) | _ = j≤n
... | (no _) | (yes _) = i≤n
... | (no _) | (no _) = k≤n

swp< : {i j k : ℕ} → i < n → j < n → k < n → swp i j k < n
swp< {n = suc n} {i} {j} {k} i<n j<n k<n = s≤s (swp≤ {i = i} {j} {k} (s≤s⁻¹ i<n) (s≤s⁻¹ j<n) (s≤s⁻¹ k<n))

-- swp-is-nfunc :
swp-fakefin : FakeFin n → FakeFin n → FakeFin n → FakeFin n
swp-fakefin (i , squash i<n) (j , squash j<n) (k , squash k<n) = swp i j k , squash (swp< {i = i} {j} {k} i<n j<n k<n)
