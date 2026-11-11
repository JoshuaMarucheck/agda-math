open import Level using (Level) renaming (_⊔_ to _⊔ℓ_; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; _≗_; cong; cong₂; subst; subst₂; [_]) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open import Relation.Binary using (Setoid; Rel; IsEquivalence; Reflexive; Symmetric; Transitive; Irreflexive; Asymmetric)
open import Relation.Nullary using (¬_; Dec; yes; no; contraposition)
open import Function using (_∘_; Congruent; Bijective; Bijection)
open import Data.Bool using (_∨_)
open import Data.Empty using (⊥)
open import Data.Unit using (tt)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (ℕ; zero; suc; pred; _≟_; _≤_; _≥_; _<_; _>_; _<?_; _≮_; z≤n; s≤s; s≤s⁻¹; _∸_; _+_; _*_; _^_; NonZero; >-nonZero; >-nonZero⁻¹; ≢-nonZero; ≢-nonZero⁻¹; NonTrivial; n>1⇒nonTrivial; nonTrivial⇒n>1; _⊔_; _⊔′_; _⊓_; _⊓′_)
open import Data.Nat.DivMod using (_%_; _/_; /-congʳ; %-congˡ; %-congʳ; m<n⇒m/n≡0; m<n*o⇒m/o<n; m/n*n≡m; m*n/n≡m; m≡m%n+[m/n]*n; m%n%n≡m%n; m%n<n; m<n⇒m%n≡m; m/n<m; n/1≡n; n%1≡0; %-distribˡ-+; m*n%n≡0)
open import Data.Nat.Divisibility using (divides; _∣_; ∣-trans)
open import Data.Nat.Properties using (module ≤-Reasoning; ≤-reflexive; ≤-refl; ≤-trans; ≤-<-trans; <-≤-trans; <-trans; <⇒≤; <-irrefl; <-asym; +-mono-≤; +-mono-<; +-mono-≤-<; +-mono-<-≤; *-mono-≤; ∸-mono; +-suc; +-comm; +-assoc; +-identity; *-comm; *-assoc; *-identity; *-zero; ≤∧≢⇒<; m≤m+n; m≤n+m; m+n∸m≡n; m+n∸n≡m; n≤0⇒n≡0; n<1⇒n≡0; m*n≢0⇒m≢0; m*n≢0⇒n≢0; m*n≡0⇒m≡0∨n≡0; m≤m*n; ⊔≡⊔′; m≤m⊔n; m≤n⊔m)
open import Data.List using (List; length; lookup; drop; _++_; reverse; map; concat)
open import Data.List.Properties using (map-cong)
open import Data.List.Relation.Unary.All using (All)

open import Plasmaduck.SetoidExperiment.SetoidMachinery using (discrete-setoid; from-discrete-cong; _which-is-cong₂_; _which-is-cong_; discrete-function-setoid)
open import Plasmaduck.SetoidExperiment.On using (setoid-on)
open import Plasmaduck.Function.InjectionSurjection using (both-inv→bijective)
open import Plasmaduck.Util.Case using (case_of_)
open import Plasmaduck.Data.Empty using (⊥-irr-elim)
open import Plasmaduck.Data.FakeFin using (FakeFin)
open import Plasmaduck.Data.Squash using (Squash; squash; squash-irrelevant)
open import Plasmaduck.Data.Nat using (¬NonZero⇒is-zero; NonZero-recompute; *-nonZero; ^-nonZero; ≤-recompute; ≤-cmp; n≤n; n≤sn; n<sn; ∸-suc; +-∸-telescope; n=spn; m+[n∸m]≡n; m∸n+n≡m; m≤n⇒m∸n≡0; m+m*n=m*sn; m*n*o=m*o*n; m≠0∧n≠0⇒m*n≠0; m∣n⇒n%m≡0; *-distribʳ-%; *-distribˡ-%; %-cong; [[m%n]/o]%p=[m/o]%p; [m+kn]/n≡k+m/n; 0%n=0; ⊔≥₁; ⊔≥₂; m%n%o=m%n; m%n%o=m%o; missing-part-<; %-/*-commute)
open import Plasmaduck.Data.Product using (Σ≡; ×≡; proj₁≡)
open import Plasmaduck.Data.PropositionalEquality using (≗-eq; module ≗-Properties)
open import Plasmaduck.Util.TypeChange using (change-type)
open import Plasmaduck.Util.Case using (inspect-case_of_)
open import Plasmaduck.Function.Properties using (Congruent₂; LeftInverse; RightInverse)
open import Plasmaduck.Function.Bijection using (_∘-bijection_)
open import Plasmaduck.Counting.Counting using (HasSize; IsFinite)

open import Plasmaduck.Fold.Nat.Foldl using (foldl)
open import Plasmaduck.Fold.Nat.Merge using (merge; merge-pop-first; module MergeSubstitute; module MergeOnSetoid)
open import Plasmaduck.Data.Nat.CeilingDivMod using (_/ᶜ_; _%ᶜ_; m=m/ᶜn*n∸m%ᶜn; m/ᶜn<m; m≤m/ᶜn*n)



{-
    Consider finite lists of Nats. You can bound one above by another if it's bounded above at every index.
    This here is (currently, at least) an attempt at showing a bijection between the set of such lists bounded by a specific list, and the product of the contents of the list.
-}
module Plasmaduck.Fold.Nat.InfiniteReindexing where

variable
    a b c ℓ : Level
    m n : ℕ

open MergeSubstitute (discrete-setoid ℕ) using (merge-local-substitute-generate; merge-substitute-generate)
open MergeOnSetoid (discrete-setoid ℕ) using (merge-pop-last)

private
    *-cong : Congruent₂ _≡_ _≡_ _≡_ _*_
    *-cong ≡-refl ≡-refl = ≡-refl

    +-cong : Congruent₂ _≡_ _≡_ _≡_ _+_
    +-cong ≡-refl ≡-refl = ≡-refl

    merge-*-pop-last :
        (generate : ℕ → ℕ) (n : ℕ) →
        merge _*_ 1 generate (suc n) ≡ merge _*_ 1 generate n * generate n
    merge-*-pop-last = merge-pop-last (_*_ which-is-cong₂ *-cong) (λ {x} {y} {z} → ≡-sym (*-assoc x y z)) {1} ((λ {x} → *-identity .proj₁ x) , (λ {x} → *-identity .proj₂ x))

    merge-+-pop-last :
        (generate : ℕ → ℕ) (n : ℕ) →
        merge _+_ 0 generate (suc n) ≡ merge _+_ 0 generate n + generate n
    merge-+-pop-last = merge-pop-last (_+_ which-is-cong₂ +-cong) (λ {x} {y} {z} → ≡-sym (+-assoc x y z)) {0} ((λ {x} → +-identity .proj₁ x) , (λ {x} → +-identity .proj₂ x))


InfiniteVector : Set
InfiniteVector = ℕ → ℕ

InfiniteVectorSetoid : ℕ → Setoid lzero lzero
InfiniteVectorSetoid n = discrete-function-setoid ℕ ℕ


infix 4 _~_
_~_ : Rel InfiniteVector lzero
_~_ = _≗_

open ≗-Properties {A = ℕ} {B = ℕ} using () renaming (
    ≗-refl to ~-refl;
    ≗-sym to ~-sym;
    ≗-trans to ~-trans;
    ≗-eq to ~-eq
    ) public

infix 4 _≺_
_≺_ : Rel InfiniteVector lzero
_≺_ f g = ∀ i → f i < g i

≺-recomputable : Relation.Binary.Recomputable _≺_
≺-recomputable u≺v i = ≤-recompute (u≺v i)

-- not tight
≺-trans : Transitive _≺_
≺-trans u≺v v≺w i = <-trans (u≺v i) (v≺w i)

≺-asym : Asymmetric _≺_
≺-asym u≺v v≺u = <-asym (u≺v 0) (v≺u 0)

≺-irrefl : Irreflexive _~_ _≺_
≺-irrefl u~v u≺v = <-irrefl (u~v 0) (u≺v 0)

module VectorProperties (vec : InfiniteVector) where
    IsNonZero : Set
    IsNonZero = ∀ i → NonZero (vec i)

    HasZero : Set
    HasZero = Σ ℕ λ i → vec i ≡ 0

    HasTailAt : ℕ → ℕ → Set
    HasTailAt x i = ∀ j → .(i ≤ j) → vec j ≡ x

    HasOneTailAt : ℕ → Set
    HasOneTailAt = HasTailAt 1

    HasOneTail : Set
    HasOneTail = Σ ℕ HasOneTailAt

    HasZeroTailAt : ℕ → Set
    HasZeroTailAt = HasTailAt 0

    HasZeroTail : Set
    HasZeroTail = Σ ℕ HasZeroTailAt

    HasNonTrivialTail : Set
    HasNonTrivialTail = ∀ i → Σ ℕ λ j → vec j > 1 × i ≤ j

    HasNonZeroNonTrivialTail : Set
    HasNonZeroNonTrivialTail = IsNonZero × HasNonTrivialTail

open VectorProperties public

LesserInfiniteVector : InfiniteVector → Set
LesserInfiniteVector vec = Σ InfiniteVector (_≺ vec)

LesserInfiniteVectorSetoid : InfiniteVector → Setoid lzero lzero
LesserInfiniteVectorSetoid vec = setoid-on {A = LesserInfiniteVector vec} (discrete-function-setoid ℕ ℕ) proj₁

FiniteBoundedVector : InfiniteVector → Set
FiniteBoundedVector vec = Σ InfiniteVector λ v → (v ≺ vec × Σ ℕ λ i → HasZeroTailAt v i)

FiniteBoundedVectorSetoid : InfiniteVector → Setoid lzero lzero
FiniteBoundedVectorSetoid vec = setoid-on {A = FiniteBoundedVector vec} (discrete-function-setoid ℕ ℕ) proj₁


SameTail : Rel InfiniteVector lzero
SameTail v₁ v₂ = Σ ℕ λ n → ∀ i → .(i ≥ n) → v₁ i ≡ v₂ i

SameTail-refl : Reflexive SameTail
SameTail-refl = zero , (λ i .z → ≡-refl)

SameTail-sym : Symmetric SameTail
SameTail-sym (n , u~v-at-≥n) = n , λ i i≥n → ≡-sym (u~v-at-≥n i i≥n)

SameTail-trans : Transitive SameTail
SameTail-trans {u} {v} {w} (m , u~v) (n , v~w) = m ⊔′ n , λ i i≥m⊔′n →
    u i     ≡⟨ u~v i (≤-trans (≤-trans (m≤m⊔n m n) (≤-reflexive (⊔≡⊔′ m n))) i≥m⊔′n) ⟩
    v i     ≡⟨ v~w i (≤-trans (≤-trans (m≤n⊔m m n) (≤-reflexive (⊔≡⊔′ m n))) i≥m⊔′n) ⟩
    w i     ∎
    where open ≡-Reasoning

SameTail-eq : IsEquivalence SameTail
SameTail-eq = record {
    refl = SameTail-refl;
    sym = SameTail-sym;
    trans = SameTail-trans
    }

module _ (n : ℕ) where
    SameHead : Rel InfiniteVector lzero
    SameHead v₁ v₂ = ∀ i → .(i < n) → v₁ i ≡ v₂ i

    SameHead-refl : Reflexive SameHead
    SameHead-refl i _ = ≡-refl

    SameHead-sym : Symmetric SameHead
    SameHead-sym u~v i i<n = ≡-sym (u~v i i<n)

    SameHead-trans : Transitive SameHead
    SameHead-trans {u} {v} {w} u~v v~w i i<n = ≡-trans (u~v i i<n) (v~w i i<n)

    SameHead-eq : IsEquivalence SameHead
    SameHead-eq = record {
        refl = SameHead-refl;
        sym = SameHead-sym;
        trans = SameHead-trans
        }

~⇒SameHead : {u v : InfiniteVector} → u ~ v →
    ∀ n → SameHead n u v
~⇒SameHead u~v n i _ = u~v i

~⇒SameTail : {u v : InfiniteVector} → u ~ v →
    SameTail u v
~⇒SameTail u~v = 0 , λ i _ → u~v i

SameHead-decr :
    {m n : ℕ} .(m≤n : m ≤ n) {v₁ v₂ : InfiniteVector} →
    SameHead n v₁ v₂ →
    SameHead m v₁ v₂
SameHead-decr m≤n same-head-n i i<m = same-head-n i (<-≤-trans i<m m≤n)

SameHead-unsuc :
    {n : ℕ} {v₁ v₂ : InfiniteVector} →
    SameHead (suc n) v₁ v₂ →
    SameHead n v₁ v₂
SameHead-unsuc {n} same-head-sn = SameHead-decr {n} {suc n} n≤sn same-head-sn

SameHead-suc :
    {n : ℕ} {v₁ v₂ : InfiniteVector} →
    SameHead n v₁ v₂ →
    v₁ n ≡ v₂ n →
    SameHead (suc n) v₁ v₂
SameHead-suc {n} same-head-n v₁[n]=v₂[n] i i<sn with i ≟ n
... | yes ≡-refl = v₁[n]=v₂[n]
... | no i≠n = same-head-n i (≤∧≢⇒< {i} {n} (s≤s⁻¹ i<sn) i≠n)



-- Product of everything before position i
index-head-product : InfiniteVector → ℕ → ℕ
index-head-product vec i = merge _*_ 1 vec i

index-head-product-weakly-monotonic' :
    {vec : InfiniteVector} → IsNonZero vec →
    (i j : ℕ) →
    index-head-product vec i ≤
    index-head-product vec (j + i)
index-head-product-weakly-monotonic' {vec} vec-nonZero i 0 = ≤-refl
index-head-product-weakly-monotonic' {vec} vec-nonZero i j@(suc j') = begin
    index-head-product vec i                        ≤⟨ index-head-product-weakly-monotonic' vec-nonZero i j' ⟩
    index-head-product vec (j' + i)                 ≤⟨ m≤m*n (index-head-product vec (j' + i)) (vec (j' + i)) {{vec-nonZero (j' + i)}} ⟩
    index-head-product vec (j' + i) * vec (j' + i)  ≡⟨ ≡-sym (merge-*-pop-last vec (j' + i)) ⟩
    index-head-product vec (j + i)                  ∎
    where open ≤-Reasoning

index-head-product-weakly-monotonic :
    {vec : InfiniteVector} → IsNonZero vec →
    {i j : ℕ} → .(i ≤ j) →
    index-head-product vec i ≤
    index-head-product vec j
index-head-product-weakly-monotonic {vec} vec-nonZero {i} {j} i≤j = begin
    index-head-product vec i            ≤⟨ index-head-product-weakly-monotonic' vec-nonZero i (j ∸ i) ⟩
    index-head-product vec (j ∸ i + i)  ≡⟨ cong (index-head-product vec) (m∸n+n≡m {j} {i} i≤j) ⟩
    index-head-product vec j            ∎
    where open ≤-Reasoning

index-head-product-nonZero-decr' : (vec : InfiniteVector) (i j : ℕ) →
    NonZero (index-head-product vec (j + i)) →
    NonZero (index-head-product vec i)
index-head-product-nonZero-decr' vec i zero i-head-nonZero = i-head-nonZero
index-head-product-nonZero-decr' vec i j@(suc j') j+i-head-nonZero = index-head-product-nonZero-decr' vec i j' thing
    where
        thing' : merge _*_ 1 vec (j + i) ≡ merge _*_ 1 vec (j' + i) * vec (j' + i)
        thing' = merge-*-pop-last vec (j' + i)

        thing : NonZero (merge _*_ 1 vec (j' + i))
        thing = m*n≢0⇒m≢0 (merge _*_ 1 vec (j' + i)) {vec (j' + i)} {{change-type (cong NonZero thing') j+i-head-nonZero}}

index-head-product-nonZero-decr : (vec : InfiniteVector) {i j : ℕ} → .(i ≤ j) →
    NonZero (index-head-product vec j) →
    NonZero (index-head-product vec i)
index-head-product-nonZero-decr vec {i} {j} i≤j j-head-nonZero = NonZero-recompute (index-head-product-nonZero-decr' vec i (j ∸ i) (change-type (cong (λ q → NonZero (index-head-product vec q)) {j} {j ∸ i + i} (≡-sym (m∸n+n≡m i≤j))) j-head-nonZero))

SameHead⇒same-index-head-product :
    {n : ℕ} {u v : InfiniteVector} →
    SameHead n u v →
    index-head-product u n ≡
    index-head-product v n
SameHead⇒same-index-head-product {zero} {u} {v} same-head-n = ≡-refl
SameHead⇒same-index-head-product {n@(suc n')} {u} {v} same-head-n =
    merge _*_ 1 u n             ≡⟨ merge-*-pop-last u n' ⟩
    merge _*_ 1 u n' * u n'     ≡⟨ *-cong (SameHead⇒same-index-head-product {n'} {u} {v} (SameHead-unsuc same-head-n)) (same-head-n n' n<sn) ⟩
    merge _*_ 1 v n' * v n'     ≡⟨ ≡-sym (merge-*-pop-last v n') ⟩
    merge _*_ 1 v n             ∎
    where open ≡-Reasoning

index-head-product-SameHead-cong : {n : ℕ} → Congruent (SameHead n) (SameHead (suc n)) index-head-product
index-head-product-SameHead-cong {n} {u} {v} same-head-n i si≤sn = SameHead⇒same-index-head-product {i} {u} {v} (SameHead-decr {i} {n} (s≤s⁻¹ si≤sn) {u} {v} same-head-n)

index-head-product-cong : {u v : InfiniteVector} → u ~ v → (i : ℕ) → index-head-product u i ≡ index-head-product v i
index-head-product-cong {u = u} {v} u~v i = SameHead⇒same-index-head-product (~⇒SameHead u~v i)

index-head-product-is-nonZero? : (vec : InfiniteVector) (i : ℕ) → Dec (NonZero (index-head-product vec i))
index-head-product-is-nonZero? vec i with index-head-product vec i ≟ 0
... | yes prod=0 = no λ prod-nonZero → ≢-nonZero⁻¹ _ {{prod-nonZero}} prod=0
... | no prod≠0 = yes (≢-nonZero prod≠0)

index-head-product-nonZero⇒item-nonZero : (vec : InfiniteVector) {i j : ℕ} → .(i < j) → .(i<n : i < n) →
    NonZero (index-head-product vec j) →
    NonZero (vec i)
index-head-product-nonZero⇒item-nonZero vec {i} {j} i<j i<n j-head-nonZero = m*n≢0⇒n≢0 (index-head-product vec i) {vec i} {{change-type (cong NonZero (merge-*-pop-last vec i)) (index-head-product-nonZero-decr vec i<j j-head-nonZero)}}

vec-nonZero⇒index-head-product-nonZero : {vec : InfiniteVector} → IsNonZero vec → (i : ℕ) →
    NonZero (index-head-product vec i)
vec-nonZero⇒index-head-product-nonZero {vec} vec-nonZero zero = record { nonZero = tt }
vec-nonZero⇒index-head-product-nonZero {vec} vec-nonZero i@(suc i') = change-type (cong NonZero (≡-sym (merge-*-pop-last vec i'))) (m≠0∧n≠0⇒m*n≠0 (index-head-product vec i') (vec i'))
    where
        instance
            i'-prod-nonZero : NonZero (index-head-product vec i')
            i'-prod-nonZero = vec-nonZero⇒index-head-product-nonZero {vec} vec-nonZero i'

            i'-nonZero : NonZero (vec i')
            i'-nonZero = vec-nonZero i'

index-head-product-zero⇒find-zero : (vec : InfiniteVector) (i : ℕ) →
    index-head-product vec i ≡ 0 → ℕ
index-head-product-zero⇒find-zero vec i@(suc i') prod-i=0 with m*n≡0⇒m≡0∨n≡0 (index-head-product vec i') {vec i'} (≡-trans (≡-sym (merge-*-pop-last vec i')) prod-i=0)
... | inj₁ prod-i'=0 = index-head-product-zero⇒find-zero vec i' prod-i'=0
... | inj₂ vec[i']=0 = i'

index-head-product-zero⇒find-zero< : (vec : InfiniteVector) (i : ℕ) →
    (prod=0 : index-head-product vec i ≡ 0) →
    index-head-product-zero⇒find-zero vec i prod=0 < i
index-head-product-zero⇒find-zero< vec i@(suc i') prod-i=0 with m*n≡0⇒m≡0∨n≡0 (index-head-product vec i') {vec i'} (≡-trans (≡-sym (merge-*-pop-last vec i')) prod-i=0)
... | inj₁ prod-i'=0 = s≤s (<⇒≤ (index-head-product-zero⇒find-zero< vec i' prod-i'=0))
... | inj₂ vec[i']=0 = n<sn

index-head-product-zero⇒find-zero-is-zero : (vec : InfiniteVector) (i : ℕ) →
    (prod-is-zero : index-head-product vec i ≡ 0) →
    vec (index-head-product-zero⇒find-zero vec i prod-is-zero) ≡ 0
index-head-product-zero⇒find-zero-is-zero vec i@(suc i') prod-i=0 with m*n≡0⇒m≡0∨n≡0 (index-head-product vec i') {vec i'} (≡-trans (≡-sym (merge-*-pop-last vec i')) prod-i=0)
... | inj₂ vec[i']=0 = vec[i']=0
... | inj₁ prod-i'=0 = index-head-product-zero⇒find-zero-is-zero vec i' prod-i'=0

lesser-vec⇒prod≠0 : (vec : InfiniteVector) → LesserInfiniteVector vec → ∀ n → index-head-product vec n ≢ 0
lesser-vec⇒prod≠0 vec (lesser-vec , lesser-vec≺) n prod=0 =
    case (<-≤-trans {k = 0} (lesser-vec≺ i) (≤-reflexive (index-head-product-zero⇒find-zero-is-zero vec n prod=0))) of λ ()
    where
        i : ℕ
        i = index-head-product-zero⇒find-zero vec n prod=0

lesser-vec⇒prod-nonZero : (vec : InfiniteVector) → LesserInfiniteVector vec → ∀ n → NonZero (index-head-product vec n)
lesser-vec⇒prod-nonZero vec lesser-vec n = ≢-nonZero (lesser-vec⇒prod≠0 vec lesser-vec n)

drop-head : InfiniteVector → ℕ → InfiniteVector
drop-head vec i j = vec (j + i)

drop-head-suc : (v : InfiniteVector) (i : ℕ) →
    drop-head v i ∘ suc ~ drop-head v (suc i)
drop-head-suc v i j = cong v (≡-sym (+-suc j i))

drop-head-~ : ∀ {u v} → u ~ v → ∀ n → drop-head u n ~ drop-head v n
drop-head-~ u~v n i = u~v (i + n)

drop-head-IsNonZero :
    {vec : InfiniteVector} →
    IsNonZero vec →
    (i : ℕ) →
    IsNonZero (drop-head vec i)
drop-head-IsNonZero {vec} vec-nonZero i j = vec-nonZero (j + i)

drop-head-HasNonTrivialTail :
    {vec : InfiniteVector} →
    HasNonTrivialTail vec →
    (i : ℕ) →
    HasNonTrivialTail (drop-head vec i)
drop-head-HasNonTrivialTail {vec} vec-nonTrivial i j = k ∸ i , subst (λ q → vec q > 1) (≡-sym (m∸n+n≡m i≤k)) vec[k]>1 , ≤-trans (≤-reflexive (≡-sym (m+n∸n≡m j i))) (∸-mono {j + i} {k} {i} {i} j+i≤k ≤-refl)
    where
        thing = vec-nonTrivial (j + i)

        k : ℕ
        k = thing .proj₁

        vec[k]>1 : vec k > 1
        vec[k]>1 = thing .proj₂ .proj₁

        j+i≤k : j + i ≤ k
        j+i≤k = thing .proj₂ .proj₂

        i≤k : i ≤ k
        i≤k = ≤-trans (m≤n+m i j) j+i≤k

drop-head-HasNonZeroNonTrivialTail :
    {vec : InfiniteVector} →
    HasNonZeroNonTrivialTail vec →
    (i : ℕ) →
    HasNonZeroNonTrivialTail (drop-head vec i)
drop-head-HasNonZeroNonTrivialTail (vec-nonZero , vec-nonTrivial) i = drop-head-IsNonZero vec-nonZero i , drop-head-HasNonTrivialTail vec-nonTrivial i

-- multiplies items in vec from i (incl) to i + j (excl)
index-range-product : InfiniteVector → (i j : ℕ) → ℕ
index-range-product vec i j = merge _*_ 1 (drop-head vec i) j

-- items from i (incl) to j (excl), as long as i ≤ j
index-range-product' : InfiniteVector → (i j : ℕ) → ℕ
index-range-product' vec i j = index-range-product vec i (j ∸ i)

index-range-product'≥ : (vec : InfiniteVector) → (i j : ℕ) → .(i ≥ j) →
    index-range-product' vec i j ≡ 1
index-range-product'≥ vec i j i≥j =
    merge _*_ 1 (drop-head vec i) (j ∸ i)   ≡⟨ cong (merge _*_ 1 (drop-head vec i)) (m≤n⇒m∸n≡0 {j} {i} i≥j) ⟩
    merge _*_ 1 (drop-head vec i) 0         ≡⟨⟩
    1                                       ∎
    where open ≡-Reasoning

index-range-product-pop-last : (vec : InfiniteVector) → (i j : ℕ) →
    index-range-product vec i (suc j) ≡ index-range-product vec i j * vec (j + i)
index-range-product-pop-last vec i j = merge-*-pop-last (drop-head vec i) j

index-head-product=range : (vec : InfiniteVector) → (i : ℕ) → index-head-product vec i ≡ index-range-product vec 0 i
index-head-product=range vec i = merge-substitute-generate _*_ *-cong 1 vec (vec ∘ (_+ 0)) (λ j → cong vec (+-comm 0 j)) i

index-range-product-split : (vec : InfiniteVector) → (i j k : ℕ) →
    index-range-product vec i (k + j) ≡ index-range-product vec (i + j) k * index-range-product vec i j
index-range-product-split vec i j zero =
    index-range-product vec i j                                         ≡⟨ ≡-sym (*-identity .proj₁ (index-range-product vec i j)) ⟩
    1 * index-range-product vec i j                                     ≡⟨⟩
    index-range-product vec (i + j) zero * index-range-product vec i j  ∎
    where open ≡-Reasoning
index-range-product-split vec i j k@(suc k') =
    index-range-product vec i (k + j)                                                           ≡⟨ merge-*-pop-last (drop-head vec i) (k' + j) ⟩
    index-range-product vec i (k' + j) * vec ((k' + j) + i)                                     ≡⟨ cong (index-range-product vec i (k' + j) *_) (cong vec (
        (k' + j) + i ≡⟨ +-assoc k' j i ⟩
        k' + (j + i) ≡⟨ cong (k' +_) (+-comm j i) ⟩
        k' + (i + j) ∎)) ⟩
    index-range-product vec i (k' + j) * vec (k' + (i + j))                                     ≡⟨ cong (_* vec (k' + (i + j))) (index-range-product-split vec i j k') ⟩
    (index-range-product vec (i + j) k' * index-range-product vec i j) * vec (k' + (i + j))     ≡⟨ m*n*o=m*o*n (index-range-product vec (i + j) k') (index-range-product vec i j) (vec (k' + (i + j))) ⟩
    (index-range-product vec (i + j) k' * vec (k' + (i + j))) * index-range-product vec i j     ≡⟨ cong (_* index-range-product vec i j) (≡-sym (merge-*-pop-last (vec ∘ (_+ (i + j))) k')) ⟩
    index-range-product vec (i + j) k * index-range-product vec i j                             ∎
    where open ≡-Reasoning

index-range-product-split' : (vec : InfiniteVector) → (i j k : ℕ) → .(i ≤ j) → .(j ≤ k) →
    index-range-product' vec i k ≡ index-range-product' vec j k * index-range-product' vec i j
index-range-product-split' vec i j k i≤j j≤k =
    index-range-product' vec i k                                                        ≡⟨⟩
    index-range-product vec i (k ∸ i)                                                   ≡⟨ cong (index-range-product vec i) (≡-sym (+-∸-telescope k j i j≤k i≤j)) ⟩
    index-range-product vec i ((k ∸ j) + (j ∸ i))                                       ≡⟨ index-range-product-split vec i (j ∸ i) (k ∸ j) ⟩
    index-range-product vec (i + (j ∸ i)) (k ∸ j) * index-range-product vec i (j ∸ i)   ≡⟨ cong (λ q → index-range-product vec q (k ∸ j) * index-range-product vec i (j ∸ i)) (m+[n∸m]≡n {i} {j} i≤j) ⟩
    index-range-product vec j (k ∸ j) * index-range-product vec i (j ∸ i)               ≡⟨⟩
    index-range-product' vec j k * index-range-product' vec i j                         ∎
    where open ≡-Reasoning

index-head-product-split : (vec : InfiniteVector) → (i j : ℕ) →
    index-head-product vec (j + i) ≡ index-head-product vec i * index-range-product vec i j
index-head-product-split vec i j =
    index-head-product vec (j + i)                              ≡⟨ index-head-product=range vec (j + i) ⟩
    index-range-product vec 0 (j + i)                           ≡⟨ index-range-product-split vec 0 i j ⟩
    index-range-product vec i j * index-range-product vec 0 i   ≡⟨ cong (index-range-product vec i j *_) (≡-sym (index-head-product=range vec i)) ⟩
    index-range-product vec i j * index-head-product vec i      ≡⟨ *-comm (index-range-product vec i j) (index-head-product vec i) ⟩
    index-head-product vec i * index-range-product vec i j ∎
    where open ≡-Reasoning

index-head-product-split' : (vec : InfiniteVector) → (i j : ℕ) →
    index-head-product vec (j + i) ≡ index-head-product vec i * index-range-product' vec i (j + i)
index-head-product-split' vec i j =
    index-head-product vec (j + i)                                      ≡⟨ index-head-product-split vec i j ⟩
    index-head-product vec i * index-range-product vec i j              ≡⟨ cong (λ q → index-head-product vec i * index-range-product vec i q) (≡-sym (m+n∸n≡m j i)) ⟩
    index-head-product vec i * index-range-product vec i (j + i ∸ i)    ≡⟨⟩
    index-head-product vec i * index-range-product' vec i (j + i)       ∎
    where open ≡-Reasoning

index-range-product-∣ :
    (vec : InfiniteVector) (i j k l : ℕ) →
    index-range-product vec (i + j) k ∣ index-range-product vec i (l + k + j)
index-range-product-∣ vec i j k l = divides (index-range-product vec (i + j + k) l * index-range-product vec i j) (
    index-range-product vec i (l + k + j)                                                                       ≡⟨ index-range-product-split vec i j (l + k) ⟩
    index-range-product vec (i + j) (l + k) * index-range-product vec i j                                       ≡⟨ cong (_* index-range-product vec i j) (index-range-product-split vec (i + j) k l) ⟩
    index-range-product vec (i + j + k) l * index-range-product vec (i + j) k * index-range-product vec i j     ≡⟨ m*n*o=m*o*n (index-range-product vec (i + j + k) l) (index-range-product vec (i + j) k) (index-range-product vec i j) ⟩
    index-range-product vec (i + j + k) l * index-range-product vec i j * index-range-product vec (i + j) k     ∎)
    where open ≡-Reasoning

index-range-product-∣' :
    (vec : InfiniteVector) (i j k l : ℕ) → .(i ≤ j) → .(j ≤ k) → .(k ≤ l) →
    index-range-product' vec j k ∣ index-range-product' vec i l
index-range-product-∣' vec i j k l i≤j j≤k k≤l = subst₂ (λ p q → index-range-product vec p (k ∸ j) ∣ index-range-product vec i q) {u = (l ∸ k + (k ∸ j) + (j ∸ i))} {v = l ∸ i} (m+[n∸m]≡n {i} {j} i≤j) (
    (l ∸ k) + (k ∸ j) + (j ∸ i)     ≡⟨ cong (_+ (j ∸ i)) (+-∸-telescope l k j k≤l j≤k) ⟩
    (l ∸ j) + (j ∸ i)               ≡⟨ +-∸-telescope l j i (≤-trans j≤k k≤l) i≤j ⟩
    l ∸ i                           ∎
    ) (index-range-product-∣ vec i (j ∸ i) (k ∸ j) (l ∸ k))
    where open ≡-Reasoning

index-head-product-∣ :
    (vec : InfiniteVector) (i j : ℕ) →
    index-head-product vec i ∣ index-head-product vec (j + i)
index-head-product-∣ vec i j = subst₂ _∣_ (≡-sym (index-head-product=range vec i)) (≡-trans (cong (index-range-product vec 0) (+-comm (j + i) 0)) (≡-sym (index-head-product=range vec (j + i)))) (index-range-product-∣ vec 0 0 i j)
    where open ≡-Reasoning

index-head-product-∣' :
    (vec : InfiniteVector) (i j : ℕ) → .(i ≤ j) →
    index-head-product vec i ∣ index-head-product vec j
index-head-product-∣' vec i j i≤j = subst (λ q → index-head-product vec i ∣ index-head-product vec q) (m∸n+n≡m i≤j) (index-head-product-∣ vec i (j ∸ i))

HasOneTail⇒index-head-product-∣ : {vec : InfiniteVector} {i : ℕ} → HasOneTailAt vec i → ∀ j → index-head-product vec j ∣ index-head-product vec i
HasOneTail⇒index-head-product-∣ {vec} {i} vec-HasOneTailAt-i j with ≤-cmp j i
... | inj₁ j≤i = index-head-product-∣' vec j i j≤i
... | inj₂ j>i = subst (λ q → index-head-product vec q ∣ index-head-product vec i) {j ∸ i + i} {j} (m∸n+n≡m {j} {i} (<⇒≤ j>i)) (divides 1 (≡-trans (≡-sym (helper (j ∸ i))) (+-comm 0 _)))
    where
        open ≡-Reasoning
        helper : ∀ k → index-head-product vec (k + i) ≡ index-head-product vec i
        helper zero = ≡-refl
        helper (suc k) =
            index-head-product vec (suc k + i)              ≡⟨ merge-*-pop-last vec (k + i) ⟩
            index-head-product vec (k + i) * vec (k + i)    ≡⟨ cong₂ _*_ (helper k) (vec-HasOneTailAt-i (k + i) (m≤n+m i k)) ⟩
            index-head-product vec i * 1                    ≡⟨ *-identity .proj₂ (index-head-product vec i) ⟩
            index-head-product vec i                        ∎

index-range-product-item-∣ :
    (vec : InfiniteVector) (i j k : ℕ) →
    vec (i + j) ∣ index-range-product vec i (k + 1 + j)
index-range-product-item-∣ vec i j k = subst (_∣ index-range-product vec i (k + 1 + j)) (*-identity .proj₂ (vec (i + j))) (index-range-product-∣ vec i j 1 k)

index-range-product-item-∣' :
    (vec : InfiniteVector) (i j k : ℕ) → .(i ≤ j) → .(j ≤ k) →
    vec j ∣ index-range-product' vec i (suc k)
index-range-product-item-∣' vec i j k i≤j j≤k = subst₂ (λ p q → vec p ∣ index-range-product vec i q) {u = k ∸ j + 1 + (j ∸ i)} {v = suc k ∸ i} (m+[n∸m]≡n i≤j) (
    k ∸ j + 1 + (j ∸ i)         ≡⟨ cong (_+ (j ∸ i)) (+-comm (k ∸ j) 1) ⟩
    1 + (k ∸ j) + (j ∸ i)       ≡⟨ +-assoc 1 (k ∸ j) (j ∸ i) ⟩
    1 + ((k ∸ j) + (j ∸ i))     ≡⟨ cong suc (+-∸-telescope k j i j≤k i≤j) ⟩
    1 + (k ∸ i)                 ≡⟨ ∸-suc k i (≤-trans i≤j j≤k) ⟩
    suc k ∸ i                   ∎
    ) (index-range-product-item-∣ vec i (j ∸ i) (k ∸ j))
    where open ≡-Reasoning

private
    HasNonZeroNonTrivialTail⇒index-head-product-unbounded-helper :
        {vec : InfiniteVector} →
        HasNonZeroNonTrivialTail vec →
        ∀ m → (bound : ℕ) → .(m ≤ bound) →
        Σ ℕ λ n →
        m ≤ index-head-product vec n
    HasNonZeroNonTrivialTail⇒index-head-product-unbounded-helper {vec} vec-nonZeroNonTrivial zero bound m≤bound = 0 , z≤n
    HasNonZeroNonTrivialTail⇒index-head-product-unbounded-helper {vec} vec-nonZeroNonTrivial (suc zero) bound m≤bound = 0 , s≤s z≤n
    HasNonZeroNonTrivialTail⇒index-head-product-unbounded-helper {vec} vec-nonZeroNonTrivial@(vec-nonZero , vec-nonTrivial) m@(suc m'@(suc m'')) bound@(suc bound') m≤bound = suc i + k , (begin
        m                                                                                   ≤⟨ m≤m/ᶜn*n m (vec i) ⟩
        m /ᶜ vec i * vec i                                                                  ≤⟨ *-mono-≤ {m /ᶜ vec i} {index-range-product vec (suc i) k} {vec i} (recursive-case .proj₂) ≤-refl ⟩
        index-range-product vec (suc i) k * vec i                                           ≡⟨ cong (index-range-product vec (suc i) k *_) (≡-sym (*-identity .proj₁ (vec i))) ⟩
        index-range-product vec (suc i) k * (1 * vec i)                                     ≤⟨ *-mono-≤ {index-range-product vec (suc i) k} ≤-refl (*-mono-≤ {1} {index-range-product vec 0 i} {vec i} (>-nonZero⁻¹ _ {{vec-nonZero⇒index-head-product-nonZero {drop-head vec 0} (λ l → subst (NonZero ∘ vec) (+-comm 0 l) (vec-nonZero l)) i}}) ≤-refl) ⟩
        index-range-product vec (suc i) k * (index-range-product vec 0 i * vec i)           ≡⟨ cong (λ q → index-range-product vec (suc i) k * (index-range-product vec 0 i * vec q)) (+-comm 0 i) ⟩
        index-range-product vec (suc i) k * (index-range-product vec 0 i * vec (i + 0))     ≡⟨ cong (index-range-product vec (suc i) k *_) (≡-sym (merge-*-pop-last (drop-head vec 0) i)) ⟩
        index-range-product vec (suc i) k * index-range-product vec 0 (suc i)               ≡⟨ ≡-sym (index-range-product-split vec 0 (suc i) k) ⟩
        index-range-product vec 0 (k + suc i)                                               ≡⟨ cong (index-range-product vec 0) (+-comm k (suc i)) ⟩
        index-range-product vec 0 (suc i + k)                                               ≡⟨ ≡-sym (index-head-product=range vec (suc i + k)) ⟩
        index-head-product vec (suc i + k)                                                  ∎)
        where
            open ≤-Reasoning

            i : ℕ
            i = vec-nonTrivial 0 .proj₁

            vec[i]>1 : vec i > 1
            vec[i]>1 = vec-nonTrivial 0 .proj₂ .proj₁

            instance
                vec[i]-nonZero : NonZero (vec i)
                vec[i]-nonZero = >-nonZero (<-trans (s≤s z≤n) vec[i]>1)

                vec[i]-nonTrivial : NonTrivial (vec i)
                vec[i]-nonTrivial = n>1⇒nonTrivial vec[i]>1

            recursive-case : Σ ℕ (λ n → m /ᶜ vec i ≤ index-head-product (drop-head vec (suc i)) n)
            recursive-case = HasNonZeroNonTrivialTail⇒index-head-product-unbounded-helper {drop-head vec (suc i)} (drop-head-HasNonZeroNonTrivialTail vec-nonZeroNonTrivial (suc i)) (m /ᶜ vec i) bound' (s≤s⁻¹ (<-≤-trans (m/ᶜn<m m (vec i)) m≤bound))

            k : ℕ
            k = recursive-case .proj₁

HasNonZeroNonTrivialTail⇒index-head-product-unbounded :
    {vec : InfiniteVector} →
    HasNonZeroNonTrivialTail vec →
    ∀ m → Σ ℕ λ n →
    m ≤ index-head-product vec n
HasNonZeroNonTrivialTail⇒index-head-product-unbounded {vec} vec-nonZeroNonTrivial m = HasNonZeroNonTrivialTail⇒index-head-product-unbounded-helper vec-nonZeroNonTrivial m m ≤-refl

-- less after (incl) a given index
≺-after : ℕ → Rel InfiniteVector lzero
≺-after n u v = drop-head u n ≺ drop-head v n

syntax ≺-after n u v = u ≺[ n ] v

≺-after-incr : ∀ m n .(m≤n : m ≤ n) u v →
    u ≺[ m ] v → u ≺[ n ] v
≺-after-incr m n m≤n u v u≺v-at-m i = subst (λ q → u q < v q) {_} {i + n} (m∸n+n≡m {i + n} {m} (≤-trans m≤n (m≤n+m n i))) (u≺v-at-m (i + n ∸ m))

-- less on some tail
infix 4 _≺'_
_≺'_ : Rel InfiniteVector lzero
u ≺' v = Σ ℕ λ n → u ≺[ n ] v

≺⇒≺' : _≺_ Relation.Binary.⇒ _≺'_
≺⇒≺' {u} {v} u≺v = 0 , λ i → subst (λ q → u q < v q) (+-comm 0 i) (u≺v i)

-- notably, ≺' is not recomputable

-- not tight
≺'-trans : Transitive _≺'_
≺'-trans {u} {v} {w} (m , u≺v-at-m) (n , v≺w-at-n) = m ⊔ n , ≺-trans (≺-after-incr m (m ⊔ n) (⊔≥₁ m n) u v u≺v-at-m) (≺-after-incr n (m ⊔ n) (⊔≥₂ m n) v w v≺w-at-n)

≺'-asym : Asymmetric _≺'_
≺'-asym {u} {v} (m , u≺v-at-m) (n , v≺u-at-n) = ≺-asym (≺-after-incr m (m ⊔ n) (⊔≥₁ m n) u v u≺v-at-m) (≺-after-incr n (m ⊔ n) (⊔≥₂ m n) v u v≺u-at-n)

≺'-irrefl : Irreflexive _~_ _≺'_
≺'-irrefl u~v (m , u≺v-at-m) = ≺-irrefl (drop-head-~ u~v m) u≺v-at-m


module AllIndexVectors
    {vec : InfiniteVector}
    (vec-nonZero : IsNonZero vec)
    (i : ℕ)
    where

    {-
        reading i with positional base described by vec
        i think i want the later items to iterate faster?
        but here the earlier items iterate faster
    -}
    all-index-vectors : InfiniteVector
    all-index-vectors j = (i / (index-head-product vec j)) % (vec j)
        where
            j-prod = index-head-product vec j

            instance
                j-prod-nonZero : NonZero j-prod
                j-prod-nonZero = vec-nonZero⇒index-head-product-nonZero vec-nonZero j

                j-item-nonZero : NonZero (vec j)
                j-item-nonZero = vec-nonZero j

    all-index-vectors≺ :
        all-index-vectors ≺ vec
    all-index-vectors≺ j = m%n<n (i / (index-head-product vec j)) (vec j)
        where
            j-prod = index-head-product vec j

            instance
                j-prod-nonZero : NonZero j-prod
                j-prod-nonZero = vec-nonZero⇒index-head-product-nonZero vec-nonZero j

                j-item-nonZero : NonZero (vec j)
                j-item-nonZero = vec-nonZero j

    all-index-vectors-high-is-zero :
        ∀ j → i < index-head-product vec j →
        all-index-vectors j ≡ 0
    all-index-vectors-high-is-zero j i<J =
        all-index-vectors j                         ≡⟨⟩
        i / index-head-product vec j % vec j    ≡⟨ %-congˡ {vec j} (m<n⇒m/n≡0 {i} {index-head-product vec j} i<J) ⟩
        0 % vec j                               ≡⟨ 0%n=0 (vec j) ⟩
        0                                       ∎
        where
            open ≡-Reasoning
            j-prod = index-head-product vec j

            instance
                j-prod-nonZero : NonZero j-prod
                j-prod-nonZero = vec-nonZero⇒index-head-product-nonZero vec-nonZero j

                j-item-nonZero : NonZero (vec j)
                j-item-nonZero = vec-nonZero j

    all-index-vectors-has-zero-tail : (k : ℕ) → i < index-head-product vec k → HasZeroTailAt all-index-vectors k
    all-index-vectors-has-zero-tail k i<K j k≤j = all-index-vectors-high-is-zero j (<-≤-trans i<K (index-head-product-weakly-monotonic vec-nonZero {k} {j} k≤j))

    -- In theory, the following two theorems cover all possible nonzero vectors.
    -- However, we don't have decidability for which premise is correct.
    all-index-vectors-has-zero-tail-trivial : HasOneTail vec → HasZeroTail all-index-vectors
    all-index-vectors-has-zero-tail-trivial (j , one-tail-at-j) = j , λ k j≤k → n<1⇒n≡0 (<-≤-trans (all-index-vectors≺ k) (≤-reflexive (one-tail-at-j k j≤k)))

    all-index-vectors-has-zero-tail-nontrivial : HasNonTrivialTail vec → HasZeroTail all-index-vectors
    all-index-vectors-has-zero-tail-nontrivial vec-nonTrivial = k , all-index-vectors-has-zero-tail k i<K
        where
            thing = HasNonZeroNonTrivialTail⇒index-head-product-unbounded {vec} (vec-nonZero , vec-nonTrivial) (suc i)

            k : ℕ
            k = thing .proj₁

            i<K : i < index-head-product vec k
            i<K = thing .proj₂

open AllIndexVectors public

SameHead⇒same-all-index-vectors :
    {u v : InfiniteVector}
    (u-nonZero : IsNonZero u)
    (v-nonZero : IsNonZero v)
    (n : ℕ) →
    SameHead n u v →
    (i : ℕ) →
    i < index-head-product u n →
    all-index-vectors u-nonZero i ~
    all-index-vectors v-nonZero i
SameHead⇒same-all-index-vectors {u} {v} u-nonZero v-nonZero n same-head-n i i<N j with ≤-cmp n j
... | inj₁ n≤j =
    all-index-vectors u-nonZero i j     ≡⟨ all-index-vectors-high-is-zero u-nonZero i j i<uj-prod ⟩
    0                                   ≡⟨ ≡-sym (all-index-vectors-high-is-zero v-nonZero i j i<vj-prod) ⟩
    all-index-vectors v-nonZero i j     ∎
    where
        uj-prod = index-head-product u j
        vj-prod = index-head-product v j

        i<uj-prod : i < uj-prod
        i<uj-prod = begin
            suc i                   ≤⟨ i<N ⟩
            index-head-product u n  ≤⟨ index-head-product-weakly-monotonic u-nonZero n≤j ⟩
            index-head-product u j  ∎
            where open ≤-Reasoning

        i<vj-prod : i < vj-prod
        i<vj-prod = begin
            suc i                   ≤⟨ i<N ⟩
            index-head-product u n  ≡⟨ SameHead⇒same-index-head-product {n} {u} {v} same-head-n ⟩
            index-head-product v n  ≤⟨ index-head-product-weakly-monotonic v-nonZero n≤j ⟩
            index-head-product v j  ∎
            where open ≤-Reasoning

        instance
            uj-prod-nonZero : NonZero uj-prod
            uj-prod-nonZero = vec-nonZero⇒index-head-product-nonZero u-nonZero j

            uj-item-nonZero : NonZero (u j)
            uj-item-nonZero = u-nonZero j

            vj-prod-nonZero : NonZero vj-prod
            vj-prod-nonZero = vec-nonZero⇒index-head-product-nonZero v-nonZero j

            vj-item-nonZero : NonZero (v j)
            vj-item-nonZero = v-nonZero j
        open ≡-Reasoning
... | inj₂ n>j =
    i / index-head-product u j % u j    ≡⟨ %-congʳ {u j} {v j} {i / index-head-product u j} (same-head-n j n>j) ⟩
    i / index-head-product u j % v j    ≡⟨ %-congˡ {v j} (/-congʳ {m = i} (index-head-product-SameHead-cong {n} {u} {v} same-head-n j (<-trans n>j n<sn))) ⟩
    i / index-head-product v j % v j    ∎
    where
        open ≡-Reasoning
        uj-prod = index-head-product u j
        vj-prod = index-head-product v j

        instance
            uj-prod-nonZero : NonZero uj-prod
            uj-prod-nonZero = vec-nonZero⇒index-head-product-nonZero u-nonZero j

            uj-item-nonZero : NonZero (u j)
            uj-item-nonZero = u-nonZero j

            vj-prod-nonZero : NonZero vj-prod
            vj-prod-nonZero = vec-nonZero⇒index-head-product-nonZero v-nonZero j

            vj-item-nonZero : NonZero (v j)
            vj-item-nonZero = v-nonZero j

-- Reading u as the vector of bases and v as a vector representing a number in those bases, this function extracts the value of digit i in that number.
inner-sum-vec-of : InfiniteVector → InfiniteVector → InfiniteVector
inner-sum-vec-of u v i = index-head-product u i * v i

inner-sum-vec-of-SameHead-cong : (n : ℕ) → Congruent₂ (SameHead n) (SameHead (suc n)) (SameHead (suc n)) inner-sum-vec-of
inner-sum-vec-of-SameHead-cong n x₁~x₂ y₁~y₂ i i<sn = *-cong (index-head-product-SameHead-cong x₁~x₂ i i<sn) (y₁~y₂ i i<sn)

inner-sum-vec-of-cong : Congruent₂ _~_ _~_ _~_ inner-sum-vec-of
inner-sum-vec-of-cong x₁~x₂ y₁~y₂ i = *-cong (index-head-product-cong x₁~x₂ i) (y₁~y₂ i)

-- Reading u as the vector of bases and v as a vector representing a number in those bases,
-- this function extracts the number, looking only at the first n items.
-- I guess it's a bit p-adic?
sum-lesser-vec : InfiniteVector → InfiniteVector → InfiniteVector
sum-lesser-vec u v n = merge _+_ 0 (inner-sum-vec-of u v) n

sum-lesser-vec-SameHead-cong : (n : ℕ) → Congruent₂ (SameHead n) (SameHead (suc n)) (SameHead (suc n)) sum-lesser-vec
sum-lesser-vec-SameHead-cong n {u₁} {u₂} {v₁} {v₂} u₁~u₂ v₁~v₂ i i<sn =
    merge _+_ 0 (inner-sum-vec-of u₁ v₁) i  ≡⟨ merge-local-substitute-generate _+_ +-cong 0 (inner-sum-vec-of u₁ v₁) (inner-sum-vec-of u₂ v₂) i (λ j j<i → SameHead-unsuc (inner-sum-vec-of-SameHead-cong i {u₁} {u₂} {v₁} {v₂} (SameHead-decr {i} {n} (s≤s⁻¹ i<sn) u₁~u₂) (SameHead-decr i<sn v₁~v₂)) j j<i) ⟩
    merge _+_ 0 (inner-sum-vec-of u₂ v₂) i  ∎
    where open ≡-Reasoning

sum-lesser-vec-cong : Congruent₂ _~_ _~_ _~_ sum-lesser-vec
sum-lesser-vec-cong {u₁} {u₂} {v₁} {v₂} u₁~u₂ v₁~v₂ i = sum-lesser-vec-SameHead-cong i (~⇒SameHead u₁~u₂ i) (~⇒SameHead v₁~v₂ (suc i)) i n<sn

sum-lesser-vec≺ : (v₁ v₂ : InfiniteVector) → v₂ ≺ v₁ → sum-lesser-vec v₁ v₂ ≺ index-head-product v₁
sum-lesser-vec≺ vec lesser-vec lesser-vec≺vec zero = s≤s z≤n
sum-lesser-vec≺ vec lesser-vec lesser-vec≺vec n@(suc n') = begin
    suc (sum-lesser-vec vec lesser-vec n)                                       ≡⟨⟩
    suc (merge _+_ 0 sum-vec n)                                                 ≡⟨ cong suc (merge-+-pop-last sum-vec n') ⟩
    suc (merge _+_ 0 sum-vec n' + sum-vec n')                                   ≡⟨⟩
    suc (merge _+_ 0 sum-vec n') + sum-vec n'                                   ≡⟨⟩
    suc (merge _+_ 0 (inner-sum-vec-of vec lesser-vec) n') + sum-vec n'         ≤⟨ +-mono-≤ {u = sum-vec n'} (sum-lesser-vec≺ vec lesser-vec lesser-vec≺vec n') ≤-refl ⟩
    index-head-product vec n' + sum-vec n'                                      ≡⟨⟩
    index-head-product vec n' + inner-sum-vec-of vec lesser-vec n'              ≡⟨⟩
    index-head-product vec n' + index-head-product vec n' * lesser-vec n'       ≤⟨ +-mono-≤ {index-head-product vec n'} ≤-refl (*-mono-≤ {index-head-product vec n'} ≤-refl (s≤s⁻¹ (<-≤-trans (lesser-vec≺vec n') (≤-reflexive vn'=sp[vn'])))) ⟩
    index-head-product vec n' + index-head-product vec n' * (pred (vec n'))     ≡⟨ m+m*n=m*sn (index-head-product vec n') (pred (vec n')) ⟩
    index-head-product vec n' * suc (pred (vec n'))                             ≡⟨ cong (index-head-product vec n' *_) (≡-sym vn'=sp[vn']) ⟩
    index-head-product vec n' * vec n'                                          ≡⟨ ≡-sym (merge-*-pop-last vec n') ⟩
    index-head-product vec n                                                    ∎
    where
        sum-vec : InfiniteVector
        sum-vec = inner-sum-vec-of vec lesser-vec

        vec-prod≠0 : NonZero (index-head-product vec n)
        vec-prod≠0 = lesser-vec⇒prod-nonZero vec (lesser-vec , lesser-vec≺vec) n

        vn'=sp[vn'] : vec n' ≡ suc (pred (vec n'))
        vn'=sp[vn'] = n=spn {vec n'} {{index-head-product-nonZero⇒item-nonZero vec {n'} {n} n<sn n<sn vec-prod≠0}}

        open ≤-Reasoning

sum-lesser-vec-%' :
    {u : InfiniteVector}
    (u-nonZero : IsNonZero u)
    (v : InfiniteVector) →
    (v ≺ u) →
    (i j : ℕ) →
    .{{_ : NonZero (index-head-product u i)}} →
    sum-lesser-vec u v (j + i) % index-head-product u i ≡ sum-lesser-vec u v i
sum-lesser-vec-%' {u} u-nonZero v v≺vec i zero = m<n⇒m%n≡m {index-head-product u i} {sum-lesser-vec u v i} (sum-lesser-vec≺ u v v≺vec i)
sum-lesser-vec-%' {u} u-nonZero v v≺vec i j@(suc j') =
    sum-lesser-vec u v (suc j' + i) % index-head-product u i                                                                                                ≡⟨ %-congˡ {index-head-product u i} (merge-+-pop-last (inner-sum-vec-of u v) (j' + i)) ⟩
    (sum-lesser-vec u v (j' + i) + inner-sum-vec-of u v (j' + i)) % index-head-product u i                                                                  ≡⟨⟩
    (sum-lesser-vec u v (j' + i) + index-head-product u (j' + i) * v (j' + i)) % index-head-product u i                                                     ≡⟨ %-distribˡ-+ (sum-lesser-vec u v (j' + i)) (index-head-product u (j' + i) * v (j' + i)) (index-head-product u i) ⟩
    (sum-lesser-vec u v (j' + i) % index-head-product u i + index-head-product u (j' + i) * v (j' + i) % index-head-product u i) % index-head-product u i   ≡⟨ %-congˡ (cong (sum-lesser-vec u v (j' + i) % index-head-product u i +_) (m∣n⇒n%m≡0 (∣-trans (index-head-product-∣ u i j') (divides (v (j' + i)) (*-comm (index-head-product u (j' + i)) (v (j' + i))))))) ⟩
    (sum-lesser-vec u v (j' + i) % index-head-product u i + 0) % index-head-product u i                                                                     ≡⟨ %-congˡ (+-identity .proj₂ (sum-lesser-vec u v (j' + i) % index-head-product u i)) ⟩
    (sum-lesser-vec u v (j' + i) % index-head-product u i) % index-head-product u i                                                                         ≡⟨ m%n%n≡m%n (sum-lesser-vec u v (j' + i)) (index-head-product u i) ⟩
    sum-lesser-vec u v (j' + i) % index-head-product u i                                                                                                    ≡⟨ sum-lesser-vec-%' u-nonZero v v≺vec i j' ⟩
    sum-lesser-vec u v i                                                                                                                                    ∎
    where open ≡-Reasoning

private
    sum-lesser-vec-skip-zero-tail-helper : (u v : InfiniteVector) → (i j : ℕ) → HasZeroTailAt v i →
        sum-lesser-vec u v i ≡ sum-lesser-vec u v (j + i)
    sum-lesser-vec-skip-zero-tail-helper u v i zero v-zero-at-i = ≡-refl
    sum-lesser-vec-skip-zero-tail-helper u v i j@(suc j') v-zero-at-i =
        sum-lesser-vec u v i                                                        ≡⟨ sum-lesser-vec-skip-zero-tail-helper u v i j' v-zero-at-i ⟩
        sum-lesser-vec u v (j' + i)                                                 ≡⟨ +-comm 0 (sum-lesser-vec u v (j' + i)) ⟩
        sum-lesser-vec u v (j' + i) + 0                                             ≡⟨ cong (sum-lesser-vec u v (j' + i) +_) (≡-sym (*-zero .proj₂ (index-head-product u (j' + i)))) ⟩
        sum-lesser-vec u v (j' + i) + index-head-product u (j' + i) * 0             ≡⟨ cong (λ q → sum-lesser-vec u v (j' + i) + index-head-product u (j' + i) * q) (≡-sym (v-zero-at-i (j' + i) (m≤n+m i j'))) ⟩
        sum-lesser-vec u v (j' + i) + index-head-product u (j' + i) * v (j' + i)    ≡⟨⟩
        sum-lesser-vec u v (j' + i) + inner-sum-vec-of u v (j' + i)                 ≡⟨ ≡-sym (merge-+-pop-last (inner-sum-vec-of u v) (j' + i)) ⟩
        sum-lesser-vec u v (j + i)                                                  ∎
        where open ≡-Reasoning

sum-lesser-vec-skip-zero-tail' : (u v : InfiniteVector) → (i j : ℕ) → .(i ≤ j) → HasZeroTailAt v i →
    sum-lesser-vec u v i ≡ sum-lesser-vec u v j
sum-lesser-vec-skip-zero-tail' u v i j i≤j v-zero-at-i = ≡-trans (sum-lesser-vec-skip-zero-tail-helper u v i (j ∸ i) v-zero-at-i) (cong (sum-lesser-vec u v) (m∸n+n≡m i≤j))

sum-lesser-vec-skip-zero-tail : (u v : InfiniteVector) → (i j : ℕ) → HasZeroTailAt v i → HasZeroTailAt v j →
    sum-lesser-vec u v i ≡ sum-lesser-vec u v j
sum-lesser-vec-skip-zero-tail u v i j v-zero-at-i v-zero-at-j with ≤-cmp i j
... | inj₁ i≤j = sum-lesser-vec-skip-zero-tail' u v i j i≤j v-zero-at-i
... | inj₂ i>j = ≡-sym (sum-lesser-vec-skip-zero-tail' u v j i (<⇒≤ i>j) v-zero-at-j)

{-
    Reading n as a number with digits,
    If you sum the values of those digits up to digit i,
    that's equivalent to taking n % the product of those digit values
-}
sum-all :
    {vec : InfiniteVector}
    (vec-nonZero : IsNonZero vec)
    (n i : ℕ) →
    .{{_ : NonZero (index-head-product vec i)}} →
    sum-lesser-vec vec (all-index-vectors vec-nonZero n) i ≡ (n % index-head-product vec i)
sum-all {vec} vec-nonZero n zero = ≡-sym (n%1≡0 n)
sum-all {vec} vec-nonZero n (suc i) =
    sum-lesser-vec vec (all-index-vectors vec-nonZero n) (suc i)                                                        ≡⟨ merge-+-pop-last (inner-sum-vec-of vec (all-index-vectors vec-nonZero n)) i ⟩
    sum-lesser-vec vec (all-index-vectors vec-nonZero n) i + inner-sum-vec-of vec (all-index-vectors vec-nonZero n) i   ≡⟨ cong (_+ inner-sum-vec-of vec (all-index-vectors vec-nonZero n) i) (sum-all vec-nonZero n i) ⟩
    n % i-prod + inner-sum-vec-of vec (all-index-vectors vec-nonZero n) i                                               ≡⟨⟩
    n % i-prod + i-prod * all-index-vectors vec-nonZero n i                                                             ≡⟨⟩
    n % i-prod + i-prod * (n / i-prod % vec i)                          ≡⟨ cong (n % i-prod +_) (*-comm (i-prod) (n / i-prod % vec i)) ⟩
    n % i-prod + n / i-prod % vec i * i-prod                            ≡⟨ cong (n % i-prod +_) (*-distribˡ-% i-prod (n / i-prod) (vec i)) ⟩
    n % i-prod + (n / i-prod * i-prod) % (vec i * i-prod)               ≡⟨ cong (n % i-prod +_) (%-congʳ {vec i * i-prod} {si-prod} {n / i-prod * i-prod} thing=si-prod) ⟩
    n % i-prod + n / i-prod * i-prod % si-prod                          ≡⟨ cong (_+ (n / i-prod * i-prod) % si-prod) (≡-sym (m%n%o=m%n n i-prod si-prod (index-head-product-weakly-monotonic {vec} vec-nonZero {i} {suc i} n≤sn))) ⟩
    n % i-prod % si-prod + n / i-prod * i-prod % si-prod                ≡⟨ ≡-sym (m<n⇒m%n≡m {n = si-prod} thing'<si-prod) ⟩
    (n % i-prod % si-prod + n / i-prod * i-prod % si-prod) % si-prod    ≡⟨ ≡-sym (%-distribˡ-+ (n % i-prod) (n / i-prod * i-prod) si-prod) ⟩
    (n % i-prod + n / i-prod * i-prod) % si-prod                        ≡⟨ %-congˡ {si-prod} (≡-sym (m≡m%n+[m/n]*n n i-prod)) ⟩
    n % index-head-product vec (suc i) ∎
    where
        i-prod = index-head-product vec i
        si-prod = index-head-product vec (suc i)

        thing=si-prod : vec i * index-head-product vec i ≡ si-prod
        thing=si-prod =
            vec i * index-head-product vec i    ≡⟨ *-comm (vec i) i-prod ⟩
            index-head-product vec i * vec i    ≡⟨ ≡-sym (merge-*-pop-last vec i) ⟩
            index-head-product vec (suc i)      ∎
            where open ≡-Reasoning

        instance
            i-item-nonZero : NonZero (vec i)
            i-item-nonZero = vec-nonZero i

            i-prod-nonZero : NonZero (index-head-product vec i)
            i-prod-nonZero = vec-nonZero⇒index-head-product-nonZero vec-nonZero i

            si-prod-nonZero : NonZero (index-head-product vec (suc i))
            si-prod-nonZero = vec-nonZero⇒index-head-product-nonZero vec-nonZero (suc i)

            thing-nonZero : NonZero (vec i * index-head-product vec i)
            thing-nonZero = *-nonZero (vec i) (index-head-product vec i)

        thing'<si-prod : n % i-prod % si-prod + n / i-prod * i-prod % si-prod < si-prod
        thing'<si-prod = begin
            suc (n % i-prod % si-prod + n / i-prod * i-prod % si-prod)  ≡⟨ cong (suc (n % i-prod % si-prod) +_) (%-/*-commute n i-prod si-prod (index-head-product-∣ vec i 1)) ⟩
            suc (n % i-prod % si-prod + n % si-prod / i-prod * i-prod)  ≡⟨ cong suc (cong (_+ n % si-prod / i-prod * i-prod) (m%n%o=m%n n i-prod si-prod (index-head-product-weakly-monotonic' vec-nonZero i 1))) ⟩
            suc (n % i-prod + n % si-prod / i-prod * i-prod)            ≡⟨ cong suc (cong (_+ n % si-prod / i-prod * i-prod) (≡-sym (m%n%o=m%o n si-prod i-prod (index-head-product-∣ vec i 1)))) ⟩
            suc (n % si-prod % i-prod + n % si-prod / i-prod * i-prod)  ≡⟨ cong suc (≡-sym (m≡m%n+[m/n]*n (n % si-prod) i-prod)) ⟩
            suc (n % si-prod)                                           ≤⟨ m%n<n n si-prod ⟩
            si-prod                                                     ∎
            where open ≤-Reasoning

        open ≡-Reasoning

private
    all-sum'-lemma :
        {u v : InfiniteVector} → (v ≺ u) → (u-nonZero : IsNonZero u) →
        (i j : ℕ) →
        .{{_ : NonZero (u j)}} →
        .{{_ : NonZero (index-head-product u j)}} →
        all-index-vectors u-nonZero (sum-lesser-vec u v (suc (j + i))) j ≡
        (index-range-product u j i * v (j + i) % u j + sum-lesser-vec u v (j + i) / index-head-product u j % u j) % u j
    all-sum'-lemma {u} {v} v≺u u-nonZero i j =
        all-index-vectors u-nonZero (sum-lesser-vec u v (suc (j + i))) j                                                                ≡⟨ cong (λ q → all-index-vectors u-nonZero q j) (merge-+-pop-last (inner-sum-vec-of u v) (j + i)) ⟩
        all-index-vectors u-nonZero (sum-lesser-vec u v (j + i) + inner-sum-vec-of u v (j + i)) j                                       ≡⟨⟩
        all-index-vectors u-nonZero (sum-lesser-vec u v (j + i) + index-head-product u (j + i) * v (j + i)) j                           ≡⟨⟩
        _%_ (_/_ (sum-lesser-vec u v (j + i) + index-head-product u (j + i) * v (j + i)) (index-head-product u j) {{vec-nonZero⇒index-head-product-nonZero u-nonZero j}}) (u j) {{u-nonZero j}}     ≡⟨ ≡-refl ⟩ -- y'alls, this can't be compressed to ≡⟨⟩ because of how instance search works apparently (it knows they're equal since the instance args are irrelevant, but it tries to unify them during instance resolution anyways. Bleh.)
        (sum-lesser-vec u v (j + i) + index-head-product u (j + i) * v (j + i)) / index-head-product u j % u j                          ≡⟨ cong (λ q → (sum-lesser-vec u v (j + i) + index-head-product u q * v (j + i)) / index-head-product u j % u j) (+-comm j i) ⟩
        (sum-lesser-vec u v (j + i) + index-head-product u (i + j) * v (j + i)) / index-head-product u j % u j                          ≡⟨ cong (λ q → (sum-lesser-vec u v (j + i) + q * v (j + i)) / index-head-product u j % u j) (index-head-product-split u j i) ⟩
        (sum-lesser-vec u v (j + i) + (index-head-product u j * index-range-product u j i) * v (j + i)) / index-head-product u j % u j  ≡⟨ cong (λ q → (sum-lesser-vec u v (j + i) + q) / index-head-product u j % u j) (*-assoc (index-head-product u j) (index-range-product u j i) (v (j + i))) ⟩
        (sum-lesser-vec u v (j + i) + index-head-product u j * (index-range-product u j i * v (j + i))) / index-head-product u j % u j  ≡⟨ cong (λ q → (sum-lesser-vec u v (j + i) + q) / index-head-product u j % u j) (*-comm (index-head-product u j) (index-range-product u j i * v (j + i))) ⟩
        (sum-lesser-vec u v (j + i) + (index-range-product u j i * v (j + i)) * index-head-product u j) / index-head-product u j % u j  ≡⟨ %-congˡ {u j} ([m+kn]/n≡k+m/n (sum-lesser-vec u v (j + i)) (index-range-product u j i * v (j + i)) (index-head-product u j)) ⟩
        (index-range-product u j i * v (j + i) + sum-lesser-vec u v (j + i) / index-head-product u j) % u j                             ≡⟨ %-distribˡ-+ (index-range-product u j i * v (j + i)) (sum-lesser-vec u v (j + i) / index-head-product u j) (u j) ⟩
        (index-range-product u j i * v (j + i) % u j + sum-lesser-vec u v (j + i) / index-head-product u j % u j) % u j                 ∎
        where open ≡-Reasoning

all-sum' :
    {u v : InfiniteVector} → (v ≺ u) → (u-nonZero : IsNonZero u) →
    (i j : ℕ) →
    all-index-vectors u-nonZero (sum-lesser-vec u v (suc j + i)) j ≡ v j
all-sum' {u} {v} v≺u u-nonZero zero j =
    all-index-vectors u-nonZero (sum-lesser-vec u v (suc j + zero)) j                                                           ≡⟨ all-sum'-lemma v≺u u-nonZero zero j ⟩
    (index-range-product u j zero * v (j + zero) % u j + sum-lesser-vec u v (j + zero) / index-head-product u j % u j) % u j    ≡⟨ cong (λ q → (index-range-product u j zero * v q % u j + sum-lesser-vec u v q / index-head-product u j % u j) % u j) (+-comm j 0) ⟩
    (index-range-product u j zero * v j % u j + sum-lesser-vec u v j / index-head-product u j % u j) % u j                      ≡⟨⟩
    (1 * v j % u j + sum-lesser-vec u v j / index-head-product u j % u j) % u j                                                 ≡⟨ cong (λ q → (q % u j + sum-lesser-vec u v j / index-head-product u j % u j) % u j) (*-identity .proj₁ (v j)) ⟩
    (v j % u j + sum-lesser-vec u v j / index-head-product u j % u j) % u j                                                     ≡⟨ cong (λ q → (v j % u j + q % u j) % u j) (m<n⇒m/n≡0 {sum-lesser-vec u v j} {index-head-product u j} (sum-lesser-vec≺ u v v≺u j)) ⟩
    (v j % u j + 0 % u j) % u j                                                                                                 ≡⟨ cong (λ q → (v j % u j + q) % u j) (0%n=0 (u j)) ⟩
    (v j % u j + 0) % u j                                                                                                       ≡⟨ %-congˡ (+-comm (v j % u j) 0) ⟩
    (v j % u j) % u j                                                                                                           ≡⟨ m%n%n≡m%n (v j) (u j) ⟩
    v j % u j                                                                                                                   ≡⟨ m<n⇒m%n≡m {u j} {v j} (v≺u j) ⟩
    v j                                                                                                                         ∎
    where
        open ≡-Reasoning
        instance
            j-item-nonZero : NonZero (u j)
            j-item-nonZero = u-nonZero j

            j-prod-nonZero : NonZero (index-head-product u j)
            j-prod-nonZero = vec-nonZero⇒index-head-product-nonZero u-nonZero j

all-sum' {u} {v} v≺u u-nonZero i@(suc i') j =
    all-index-vectors u-nonZero (sum-lesser-vec u v (suc j + i)) j                                                                                              ≡⟨ all-sum'-lemma v≺u u-nonZero i j ⟩
    (index-range-product u j i * v (j + i) % u j + sum-lesser-vec u v (j + i) / index-head-product u j % u j) % u j                                             ≡⟨⟩
    (merge _*_ 1 (drop-head u j) i * v (j + i) % u j + sum-lesser-vec u v (j + i) / index-head-product u j % u j) % u j                                         ≡⟨ cong (λ q → (q * v (j + i) % u j + sum-lesser-vec u v (j + i) / index-head-product u j % u j) % u j) (merge-pop-first _*_ 1 (drop-head u j) i') ⟩
    (drop-head u j zero * merge _*_ 1 (drop-head u j ∘ suc) i' * v (j + suc i') % u j + sum-lesser-vec u v (j + suc i') / index-head-product u j % u j) % u j   ≡⟨ cong (λ q → (drop-head u j zero * q * v (j + suc i') % u j + sum-lesser-vec u v (j + suc i') / index-head-product u j % u j) % u j) (merge-substitute-generate _*_ *-cong 1 (drop-head u j ∘ suc) (drop-head u (suc j)) (drop-head-suc u j) i') ⟩
    (drop-head u j zero * index-range-product u (suc j) i' * v (j + suc i') % u j + sum-lesser-vec u v (j + suc i') / index-head-product u j % u j) % u j       ≡⟨⟩
    (u j * index-range-product u (suc j) i' * v (j + i) % u j + sum-lesser-vec u v (j + i) / index-head-product u j % u j) % u j                                ≡⟨ cong (λ q → (q % u j + sum-lesser-vec u v (j + i) / index-head-product u j % u j) % u j) (*-assoc (u j) (index-range-product u (suc j) i') (v (j + i))) ⟩
    (u j * (index-range-product u (suc j) i' * v (j + i)) % u j + sum-lesser-vec u v (j + i) / index-head-product u j % u j) % u j                              ≡⟨ cong (λ q → (q % u j + sum-lesser-vec u v (j + i) / index-head-product u j % u j) % u j) (*-comm (u j) (index-range-product u (suc j) i' * v (j + i))) ⟩
    ((index-range-product u (suc j) i' * v (j + i)) * u j % u j + sum-lesser-vec u v (j + i) / index-head-product u j % u j) % u j                              ≡⟨ cong (λ q → (q + sum-lesser-vec u v (j + i) / index-head-product u j % u j) % u j) (m*n%n≡0 (index-range-product u (suc j) i' * v (j + i)) (u j)) ⟩
    (0 + sum-lesser-vec u v (j + i) / index-head-product u j % u j) % u j                                                                                       ≡⟨⟩
    (sum-lesser-vec u v (j + i) / index-head-product u j % u j) % u j                                                                                           ≡⟨ m%n%n≡m%n (sum-lesser-vec u v (j + i) / index-head-product u j) (u j) ⟩
    sum-lesser-vec u v (j + i) / index-head-product u j % u j                                                                                                   ≡⟨⟩
    all-index-vectors u-nonZero (sum-lesser-vec u v (j + i)) j                                                                                                  ≡⟨ cong (λ q → all-index-vectors u-nonZero (sum-lesser-vec u v q) j) (+-suc j i') ⟩
    all-index-vectors u-nonZero (sum-lesser-vec u v (suc j + i')) j                                                                                             ≡⟨ all-sum' v≺u u-nonZero i' j ⟩
    v j                                                                                                                                                         ∎
    where
        open ≡-Reasoning

        instance
            j-item-nonZero : NonZero (u j)
            j-item-nonZero = u-nonZero j

            j-prod-nonZero : NonZero (index-head-product u j)
            j-prod-nonZero = vec-nonZero⇒index-head-product-nonZero u-nonZero j

{-
    Reading v as a number's digits with base u,
    taking the sum of the first i digits
    and then representing that as a vector
    matches on those first i digits.
-}
all-sum :
    {u v : InfiniteVector} → (v ≺ u) → (u-nonZero : IsNonZero u) →
    (i : ℕ) →
    SameHead i (all-index-vectors u-nonZero (sum-lesser-vec u v i)) v
all-sum {u} {v} v≺u u-nonZero i@(suc i') j j<i = ≡-trans (cong (λ q → all-index-vectors u-nonZero (sum-lesser-vec u v q) j) {i} {suc (j + (i' ∸ j))} (cong suc (≡-sym (m+[n∸m]≡n {j} {i'} (s≤s⁻¹ j<i))))) (all-sum' v≺u u-nonZero (i' ∸ j) j)

module FiniteVectorBijections
    {basesVec : InfiniteVector}
    (basesVec-NonZero : IsNonZero basesVec)
    (basesVec-HasOneTail : HasOneTail basesVec)
    where
    private
        j : ℕ
        j = basesVec-HasOneTail .proj₁

        J : ℕ
        J = index-head-product basesVec j

        instance
            J-nonZero : NonZero J
            J-nonZero = vec-nonZero⇒index-head-product-nonZero basesVec-NonZero j

    open import Plasmaduck.Number.NatModSetoid J using (_≃_; NatModSetoid; size-mod)

    all-index-vectors-cyclic : {m n : ℕ} → m ≃ n → all-index-vectors {basesVec} basesVec-NonZero m ~ all-index-vectors {basesVec} basesVec-NonZero n
    all-index-vectors-cyclic {m} {n} m=n-mod-J i =
        all-index-vectors basesVec-NonZero m i                                          ≡⟨⟩
        m / index-head-product basesVec i % basesVec i                                  ≡⟨ ≡-sym ([[m%n]/o]%p=[m/o]%p {m} {index-head-product basesVec j} {index-head-product basesVec i} {basesVec i} thing) ⟩
        m % index-head-product basesVec j / index-head-product basesVec i % basesVec i  ≡⟨ cong (λ q → q / index-head-product basesVec i % basesVec i) m=n-mod-J ⟩
        n % index-head-product basesVec j / index-head-product basesVec i % basesVec i  ≡⟨ [[m%n]/o]%p=[m/o]%p {n} {index-head-product basesVec j} {index-head-product basesVec i} {basesVec i} thing ⟩
        n / index-head-product basesVec i % basesVec i                                  ≡⟨⟩
        all-index-vectors basesVec-NonZero n i                                          ∎
        where
            open ≡-Reasoning

            i-prod = index-head-product basesVec i

            instance
                i-prod-nonZero : NonZero i-prod
                i-prod-nonZero = vec-nonZero⇒index-head-product-nonZero basesVec-NonZero i

                i-item-nonZero : NonZero (basesVec i)
                i-item-nonZero = basesVec-NonZero i

            thing : index-head-product basesVec i * basesVec i ∣ index-head-product basesVec j
            thing = subst (_∣ index-head-product basesVec j) (merge-*-pop-last basesVec i) (HasOneTail⇒index-head-product-∣ {basesVec} {j} (basesVec-HasOneTail .proj₂) (suc i))

    -- These two are inverses ish, being constrained to only IndexVectors less than vec.
    all-index-vectors-lesser : ℕ → LesserInfiniteVector basesVec
    all-index-vectors-lesser i = all-index-vectors basesVec-NonZero i , all-index-vectors≺ basesVec-NonZero i

    sum-lesser-vec-lesser : LesserInfiniteVector basesVec → ℕ
    sum-lesser-vec-lesser vec = sum-lesser-vec basesVec (vec .proj₁) j

    private
        _~′_ = LesserInfiniteVectorSetoid basesVec .Setoid._≈_

    all-index-vectors-lesser-cong : Congruent _≃_ _~′_ all-index-vectors-lesser
    all-index-vectors-lesser-cong = all-index-vectors-cyclic

    sum-lesser-vec-lesser-cong : Congruent _~′_ _≃_ sum-lesser-vec-lesser
    sum-lesser-vec-lesser-cong {u , u≺bases} {v , v≺bases} u~v =
        sum-lesser-vec basesVec u j % J ≡⟨ %-congˡ {J} (sum-lesser-vec-cong {basesVec} ~-refl u~v j) ⟩
        sum-lesser-vec basesVec v j % J ∎
        where open ≡-Reasoning

    sum-all-inverse : LeftInverse {A = ℕ} {LesserInfiniteVector basesVec} _≃_ _~′_ all-index-vectors-lesser sum-lesser-vec-lesser
    sum-all-inverse {n} =
        sum-lesser-vec-lesser (all-index-vectors-lesser n) % J                  ≡⟨⟩
        sum-lesser-vec basesVec (all-index-vectors basesVec-NonZero n) j % J    ≡⟨ %-congˡ (sum-all basesVec-NonZero n j) ⟩
        n % J % J                                                               ≡⟨ m%n%n≡m%n n J ⟩
        n % J                                                                   ∎
        where open ≡-Reasoning

    all-sum-inverse : RightInverse {A = ℕ} {LesserInfiniteVector basesVec} _≃_ _~′_ all-index-vectors-lesser sum-lesser-vec-lesser
    all-sum-inverse lesser-vec@{vec , vec≺basesVec} i with ≤-cmp j i
    ... | inj₁ j≤i =
        (all-index-vectors-lesser (sum-lesser-vec-lesser lesser-vec)) .proj₁ i  ≡⟨⟩
        all-index-vectors basesVec-NonZero (sum-lesser-vec basesVec vec j) i    ≡⟨ n<1⇒n≡0 (<-≤-trans (all-index-vectors≺ basesVec-NonZero (sum-lesser-vec basesVec vec j) i) (≤-reflexive (basesVec-HasOneTail .proj₂ i j≤i))) ⟩
        0                                                                       ≡⟨ ≡-sym (n<1⇒n≡0 (<-≤-trans (vec≺basesVec i) (≤-reflexive (basesVec-HasOneTail .proj₂ i j≤i)))) ⟩
        vec i                                                                   ∎
        where open ≡-Reasoning
    ... | inj₂ j>i =
        (all-index-vectors-lesser (sum-lesser-vec-lesser lesser-vec)) .proj₁ i  ≡⟨⟩
        all-index-vectors basesVec-NonZero (sum-lesser-vec basesVec vec j) i    ≡⟨ all-sum vec≺basesVec basesVec-NonZero j i j>i ⟩
        vec i                                                                   ∎
        where open ≡-Reasoning

    all-index-vectors-lesser-bijective : Bijective _≃_ _~′_ all-index-vectors-lesser
    all-index-vectors-lesser-bijective = both-inv→bijective NatModSetoid (LesserInfiniteVectorSetoid basesVec) (all-index-vectors-lesser which-is-cong all-index-vectors-lesser-cong) ((sum-lesser-vec-lesser which-is-cong λ {x} {y} → sum-lesser-vec-lesser-cong {x} {y}) , sum-all-inverse , λ {x} → all-sum-inverse {x})

    sum-lesser-vec-lesser-bijective : Bijective _~′_ _≃_ sum-lesser-vec-lesser
    sum-lesser-vec-lesser-bijective = both-inv→bijective (LesserInfiniteVectorSetoid basesVec) NatModSetoid (sum-lesser-vec-lesser which-is-cong λ {x} {y} → sum-lesser-vec-lesser-cong {x} {y}) ((all-index-vectors-lesser which-is-cong all-index-vectors-lesser-cong) , (λ {x} → all-sum-inverse {x}), sum-all-inverse)

    finite-vector-bijection : Bijection NatModSetoid (LesserInfiniteVectorSetoid basesVec)
    finite-vector-bijection = record {
        to = all-index-vectors-lesser;
        cong = all-index-vectors-lesser-cong;
        bijective = all-index-vectors-lesser-bijective
        }

    FiniteVectorsFinite : HasSize (LesserInfiniteVectorSetoid basesVec) J
    FiniteVectorsFinite = finite-vector-bijection ∘-bijection size-mod



module InfiniteVectorBijections
    {basesVec : InfiniteVector}
    (basesVec-NonZeroNonTrivial : HasNonZeroNonTrivialTail basesVec)
    where
    private
        basesVec-NonZero : IsNonZero basesVec
        basesVec-NonZero = basesVec-NonZeroNonTrivial .proj₁

        basesVec-HasNonTrivialTail : HasNonTrivialTail basesVec
        basesVec-HasNonTrivialTail = basesVec-NonZeroNonTrivial .proj₂

    -- These two are inverses ish, being constrained to only IndexVectors less than vec.
    all-index-vectors-lesser : ℕ → FiniteBoundedVector basesVec
    all-index-vectors-lesser i = all-index-vectors basesVec-NonZero i , all-index-vectors≺ basesVec-NonZero i , j , all-index-vectors-has-zero-tail basesVec-NonZero i j i<J
        where
            pair = HasNonZeroNonTrivialTail⇒index-head-product-unbounded basesVec-NonZeroNonTrivial (suc i)
            j : ℕ
            j = pair .proj₁

            i<J : i < index-head-product basesVec j
            i<J = pair .proj₂

    sum-lesser-vec-lesser : FiniteBoundedVector basesVec → ℕ
    sum-lesser-vec-lesser (v , _ , j , zero-tail-at-j) = sum-lesser-vec basesVec v j

    private
        _~′_ = FiniteBoundedVectorSetoid basesVec .Setoid._≈_

    all-index-vectors-lesser-cong : Congruent _≡_ _~′_ all-index-vectors-lesser
    all-index-vectors-lesser-cong = from-discrete-cong (FiniteBoundedVectorSetoid basesVec) all-index-vectors-lesser

    sum-lesser-vec-lesser-cong : Congruent _~′_ _≡_ sum-lesser-vec-lesser
    sum-lesser-vec-lesser-cong {u , u≺bases , i , u-zero-at-i} {v , v≺bases , j , v-zero-at-j} u~v =
        sum-lesser-vec basesVec u i     ≡⟨ sum-lesser-vec-cong {basesVec} ~-refl u~v i ⟩
        sum-lesser-vec basesVec v i     ≡⟨ sum-lesser-vec-skip-zero-tail basesVec v i j (λ k i≤k → ≡-trans (≡-sym (u~v k)) (u-zero-at-i k i≤k)) v-zero-at-j ⟩
        sum-lesser-vec basesVec v j     ∎
        where open ≡-Reasoning

    sum-all-inverse : LeftInverse {A = ℕ} {FiniteBoundedVector basesVec} _≡_ _~′_ all-index-vectors-lesser sum-lesser-vec-lesser
    sum-all-inverse {n} =
        sum-lesser-vec-lesser (all-index-vectors-lesser n)                  ≡⟨⟩
        sum-lesser-vec basesVec (all-index-vectors basesVec-NonZero n) j    ≡⟨ sum-all basesVec-NonZero n j ⟩
        n % index-head-product basesVec j                                   ≡⟨ m<n⇒m%n≡m n<J ⟩
        n                                                                   ∎
        where
            open ≡-Reasoning
            pair = HasNonZeroNonTrivialTail⇒index-head-product-unbounded basesVec-NonZeroNonTrivial (suc n)
            j = pair .proj₁
            n<J = pair .proj₂

            instance
                j-item-nonZero : NonZero (basesVec j)
                j-item-nonZero = basesVec-NonZero j

                j-prod-nonZero : NonZero (index-head-product basesVec j)
                j-prod-nonZero = vec-nonZero⇒index-head-product-nonZero basesVec-NonZero j

    all-sum-inverse : RightInverse {A = ℕ} {FiniteBoundedVector basesVec} _≡_ _~′_ all-index-vectors-lesser sum-lesser-vec-lesser
    all-sum-inverse lesser-vec@{u , u≺bases , i , u-zero-at-i} j =
        all-index-vectors-lesser (sum-lesser-vec-lesser (u , u≺bases , i , u-zero-at-i)) .proj₁ j   ≡⟨⟩
        all-index-vectors basesVec-NonZero (sum-lesser-vec basesVec u i) j                          ≡⟨ cong (λ q → all-index-vectors basesVec-NonZero q j) (sum-lesser-vec-skip-zero-tail' basesVec u i (i ⊔ suc j) (⊔≥₁ i (suc j)) u-zero-at-i) ⟩
        all-index-vectors basesVec-NonZero (sum-lesser-vec basesVec u (i ⊔ suc j)) j                ≡⟨ all-sum u≺bases basesVec-NonZero (i ⊔ suc j) j (⊔≥₂ i (suc j)) ⟩
        u j                                                                                         ∎
        where open ≡-Reasoning

    all-index-vectors-lesser-bijective : Bijective _≡_ _~′_ all-index-vectors-lesser
    all-index-vectors-lesser-bijective = both-inv→bijective (discrete-setoid ℕ) (FiniteBoundedVectorSetoid basesVec) (all-index-vectors-lesser which-is-cong all-index-vectors-lesser-cong) ((sum-lesser-vec-lesser which-is-cong λ {x} {y} → sum-lesser-vec-lesser-cong {x} {y}) , sum-all-inverse , λ {x} → all-sum-inverse {x})

    sum-lesser-vec-lesser-bijective : Bijective _~′_ _≡_ sum-lesser-vec-lesser
    sum-lesser-vec-lesser-bijective = both-inv→bijective (FiniteBoundedVectorSetoid basesVec) (discrete-setoid ℕ) (sum-lesser-vec-lesser which-is-cong λ {x} {y} → sum-lesser-vec-lesser-cong {x} {y}) ((all-index-vectors-lesser which-is-cong all-index-vectors-lesser-cong) , (λ {x} → all-sum-inverse {x}), sum-all-inverse)

    infinite-vector-bijection : Bijection (discrete-setoid ℕ) (FiniteBoundedVectorSetoid basesVec)
    infinite-vector-bijection = record {
        to = all-index-vectors-lesser;
        cong = all-index-vectors-lesser-cong;
        bijective = all-index-vectors-lesser-bijective
        }

module Cube (dim : ℕ) (value : ℕ) .{{value-nonZero : NonZero value}} where
    basesVec : InfiniteVector
    basesVec i with i <? dim
    ... | yes _ = value
    ... | no _ = 1

    basesVec-force< : (i : ℕ) → .(i < dim) → basesVec i ≡ value
    basesVec-force< i i<dim with i <? dim
    ... | yes _ = ≡-refl
    ... | no ¬i<dim = ⊥-irr-elim (¬i<dim i<dim)

    basesVec-force≥ : (i : ℕ) → .(i ≥ dim) → basesVec i ≡ 1
    basesVec-force≥ i i≥dim with i <? dim
    ... | yes i<dim = ⊥-irr-elim (<-irrefl ≡-refl (<-≤-trans i<dim i≥dim))
    ... | no _ = ≡-refl

    basesVec-HasOneTail : HasOneTail basesVec
    basesVec-HasOneTail = dim , basesVec-force≥

    basesVec-IsNonZero : IsNonZero basesVec
    basesVec-IsNonZero i with i <? dim
    ... | yes _ = NonZero-recompute value-nonZero
    ... | no _ = record { nonZero = tt }

    open FiniteVectorBijections basesVec-IsNonZero basesVec-HasOneTail public

    private
        J : ℕ
        J = index-head-product basesVec dim

        J' : ℕ
        J' = value ^ dim

        instance
            J-nonZero : NonZero J
            J-nonZero = vec-nonZero⇒index-head-product-nonZero basesVec-IsNonZero dim

            J'-nonZero : NonZero J'
            J'-nonZero = ^-nonZero value dim

    J=J' : J ≡ J'
    J=J' = helper dim ≤-refl
        where
            helper : ∀ i → .(i ≤ dim) → index-head-product basesVec i ≡ value ^ i
            helper zero _ = ≡-refl
            helper i@(suc i') i≤dim =
                index-head-product basesVec i                   ≡⟨ merge-*-pop-last basesVec i' ⟩
                merge _*_ 1 basesVec i' * basesVec i'           ≡⟨⟩
                index-head-product basesVec i' * basesVec i'    ≡⟨ cong₂ _*_ (helper i' (≤-trans n≤sn i≤dim)) (basesVec-force< i' i≤dim) ⟩
                value ^ i' * value                              ≡⟨ *-comm (value ^ i') value ⟩
                value * value ^ i'                              ≡⟨⟩
                value ^ i                                       ∎
                where open ≡-Reasoning

    -- open import Plasmaduck.Number.NatModSetoid J using (_≃_; NatModSetoid; size-mod)
