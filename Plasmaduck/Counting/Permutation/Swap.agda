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

open import Plasmaduck.Counting.Permutation.Defs using (Permutation; fin-setoid)


{-
    Some basic properties of swp.
-}
module Plasmaduck.Counting.Permutation.Swap where
open import Plasmaduck.Counting.Permutation.Defs using (swp) public

variable
    a b c : Level
    m n : ℕ


swp-flip : (i j k : Fin n) → swp i j k ≡ swp j i k
swp-flip i j k with i ≟ k | j ≟ k
... | yes i=k | yes j=k = trans j=k (sym i=k)
... | yes i=k | no j≠k = refl
... | no i≠k | yes j=k = refl
... | no i≠k | no j≠k = refl

-- match args
swp-matchₐ-lemma : (i k : Fin n) → swp i i k ≡ k
swp-matchₐ-lemma i k with i ≟ i | i ≟ k
... | yes i=i | yes i=k = i=k
... | yes i=i | no i≠k = refl
... | no i≠i | _ = ⊥-elim (i≠i refl)

-- match input with 2nd arg
swp-match₂-lemma : (i j : Fin n) → swp i j j ≡ i
swp-match₂-lemma i j with i ≟ j | j ≟ j
... | _ | no j≠j = ⊥-elim (j≠j refl)
... | yes i=j | yes j=j = sym i=j
... | no i≠j | yes j=j = refl

-- match input with 1st arg
swp-match₁-lemma : (i j : Fin n) → swp i j i ≡ j
swp-match₁-lemma i j =
    swp i j i   ≡⟨ swp-flip i j i ⟩
    swp j i i   ≡⟨ swp-match₂-lemma j i ⟩
    j           ∎
    where open ≡-Reasoning

swp-no-match⇒id : (i j k : Fin n) → (i≠k : i ≢ k) (j≠k : j ≢ k) → swp i j k ≡ k
swp-no-match⇒id i j k i≠k j≠k with i ≟ k | j ≟ k
... | yes i=k | _ = ⊥-elim (i≠k i=k)
... | _ | yes j=k = ⊥-elim (j≠k j=k)
... | no _ | no _ = refl

swp-involution : (i j k : Fin n) → swp i j (swp i j k) ≡ k
swp-involution i j k with i ≟ k | j ≟ k
... | yes i=k | _ = trans (swp-match₂-lemma i j) i=k
... | no i≠k | yes j=k = trans (swp-match₁-lemma i j) j=k
... | no i≠k | no j≠k = swp-no-match⇒id i j k i≠k j≠k

low-swp-is-low : (i j k l : Fin n) → i ≤-fin l → j ≤-fin l → k ≤-fin l → swp i j k ≤-fin l
low-swp-is-low i j k l i≤l j≤l k≤l with i ≟ k | j ≟ k
... | yes _ | _ = j≤l
... | no _ | yes _ = i≤l
... | no _ | no _ = k≤l

swp-contract-three :
    {i j k : Fin n} →
    i ≢ k → j ≢ k →
    ∀ l → (swp i j ∘ swp j k ∘ swp i j) l ≡ swp i k l
swp-contract-three {i = i} {j} {k} i≠k j≠k l with i ≟ l | j ≟ l | k ≟ l
... | no i≠l | no j≠l | no k≠l =
    (swp i j ∘ swp j k) l   ≡⟨ cong (swp i j) (swp-no-match⇒id j k l j≠l k≠l) ⟩
    swp i j l               ≡⟨ swp-no-match⇒id i j l i≠l j≠l ⟩
    l                       ∎
    where open ≡-Reasoning
... | no i≠l | no j≠l | yes refl =
    (swp i j ∘ swp j k) k   ≡⟨ cong (swp i j) (swp-match₂-lemma j k) ⟩
    swp i j j               ≡⟨ swp-match₂-lemma i j ⟩
    i                       ∎
    where open ≡-Reasoning
... | no i≠l | yes refl | yes refl = ⊥-elim (j≠k refl)
    where open ≡-Reasoning
... | yes refl | no j≠l | no k≠l =
    (swp i j ∘ swp j k) j   ≡⟨ cong (swp i j) (swp-match₁-lemma j k) ⟩
    swp i j k               ≡⟨ swp-no-match⇒id i j k (λ i=k → k≠l (sym i=k)) j≠k ⟩
    k                       ∎
    where open ≡-Reasoning
... | yes refl | no j≠l | yes refl = ⊥-elim (i≠k refl)
    where open ≡-Reasoning
... | yes refl | yes refl | no k≠l =
    (swp i i ∘ swp i k) i   ≡⟨ cong (swp i i) (swp-match₁-lemma i k) ⟩
    swp i i k               ≡⟨ swp-matchₐ-lemma i k ⟩
    k                       ∎
    where open ≡-Reasoning
... | yes refl | yes refl | yes refl =
    swp i i (swp i i i)     ≡⟨ cong (swp i i) (swp-matchₐ-lemma i i) ⟩
    swp i i i               ≡⟨ swp-matchₐ-lemma i i ⟩
    i                       ∎
    where open ≡-Reasoning
... | no i≠l | yes refl | no k≠l =
    (swp i j ∘ swp j k) i   ≡⟨ cong (swp i j) (swp-no-match⇒id j k i (≢-sym i≠l) (≢-sym i≠k)) ⟩
    swp i j i               ≡⟨ swp-match₁-lemma i j ⟩
    j                       ∎
    where open ≡-Reasoning

swp-contract-three' :
    {i j k : Fin n} →
    i ≢ k → j ≢ k →
    ∀ l → (swp j i ∘ swp k j ∘ swp j i) l ≡ swp k i l
swp-contract-three' {i = i} {j} {k} i≠k j≠k l =
    (swp j i ∘ swp k j ∘ swp j i) l     ≡⟨ (swp-flip j i ((swp k j ∘ swp j i) l)) ⟩
    (swp i j ∘ swp k j ∘ swp j i) l     ≡⟨ cong (swp i j) (swp-flip k j (swp j i l)) ⟩
    (swp i j ∘ swp j k ∘ swp j i) l     ≡⟨ cong (swp i j ∘ swp j k) (swp-flip j i l) ⟩
    (swp i j ∘ swp j k ∘ swp i j) l     ≡⟨ swp-contract-three i≠k j≠k l ⟩
    swp i k l                           ≡⟨ swp-flip i k l ⟩
    swp k i l                           ∎
    where open ≡-Reasoning

swp-is-bijective : (i j : Fin n) → Bijective _≡_ _≡_ (swp i j)
swp-is-bijective i j = inj , surj
    where
        open ≡-Reasoning

        inj : Injective _≡_ _≡_ (swp i j)
        inj {k} {l} k'=l' with i ≟ k | j ≟ k | i ≟ l | j ≟ l
        ... | yes i=k | _ | yes i=l | _ = trans (sym i=k) i=l
        ... | yes i=k | _ | no i≠l | yes j=l = trans (trans (sym i=k) (sym k'=l')) j=l
        ... | yes i=k | _ | no i≠l | no j≠l = ⊥-elim (j≠l k'=l')
        ... | no i≠k | yes j=k | yes i=l | _ = trans (trans (sym j=k) (sym k'=l')) i=l
        ... | no i≠k | yes j=k | no _ | yes j=l = trans (sym j=k) j=l
        ... | no i≠k | yes j=k | no i≠l | no j≠l = ⊥-elim (i≠l k'=l')
        ... | no i≠k | no j≠k | yes i=l | _ = ⊥-elim (j≠k (sym k'=l'))
        ... | no i≠k | no j≠k | no i≠l | yes j=l = ⊥-elim (i≠k (sym k'=l'))
        ... | no _ | no _ | no _ | no _ = k'=l'

        surj : Surjective _≡_ _≡_ (swp i j)
        surj k with i ≟ k | j ≟ k
        ... | yes i=k | j≟k = j , λ { {z} refl →
            swp i z z   ≡⟨ swp-match₂-lemma i z ⟩
            i           ≡⟨ i=k ⟩
            k           ∎ }
        ... | no i≠k | yes j=k = i , λ { {z} refl →
            swp z j z   ≡⟨ swp-match₁-lemma z j ⟩
            j           ≡⟨ j=k ⟩
            k           ∎ }
        ... | no i≠k | no j≠k = k , λ { {z} refl → swp-no-match⇒id i j k i≠k j≠k }

swap : Fin n → Fin n → Permutation n
swap {n} i j = record {
    to = swp i j;
    cong = from-discrete-cong (fin-setoid n) (swp i j);
    bijective = swp-is-bijective i j
    }
