open import Level using (Level) renaming (_⊔_ to _⊔ℓ_; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; _≗_; cong; cong₂; subst; subst₂; [_]) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open import Relation.Binary using (Setoid; _Respects₂_; Rel; IsEquivalence; Reflexive; Symmetric; Transitive; Trans; Irreflexive; Asymmetric)
open import Relation.Nullary using (¬_; Dec; yes; no; contraposition)
open import Function using (_∘_; Congruent; Bijective; Bijection)
open import Data.Bool using (_∨_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (tt)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (ℕ; zero; suc; pred; _≟_; _≤_; _≥_; _<_; _>_; _≤?_; _<?_; _≮_; z≤n; s≤s; s≤s⁻¹; _∸_; _+_; _*_; NonZero; >-nonZero; >-nonZero⁻¹; ≢-nonZero; ≢-nonZero⁻¹; NonTrivial; n>1⇒nonTrivial; nonTrivial⇒n>1; _⊔_; _⊔′_; _⊓_; _⊓′_)
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
open import Plasmaduck.Data.Nat using (¬NonZero⇒is-zero; NonZero-recompute; *-nonZero; ≤-recompute; ≤-cmp; n≤n; n≤sn; n<sn; ∸-suc; +-∸-telescope; n=spn; m+[n∸m]≡n; m∸n+n≡m; m≤n⇒m∸n≡0; m+m*n=m*sn; m*n*o=m*o*n; m≠0∧n≠0⇒m*n≠0; m∣n⇒n%m≡0; *-distribʳ-%; *-distribˡ-%; %-cong; [m+kn]/n≡k+m/n; 0%n=0; ⊔≥₁; ⊔≥₂; m%n%o=m%n; m%n%o=m%o; missing-part-<; %-/*-commute)
open import Plasmaduck.Data.Product using (Σ≡; ×≡; proj₁≡)
open import Plasmaduck.Data.PropositionalEquality using (≗-eq; module ≗-Properties)
open import Plasmaduck.Util.Case using (inspect-case_of_)
open import Plasmaduck.Function.Properties using (Congruent₂; LeftInverse; RightInverse)
open import Plasmaduck.Function.Bijection using (_∘-bijection_; invert-bijection)
open import Plasmaduck.Counting.Counting using (HasSize; IsFinite)
open import Plasmaduck.Relation.Defs using (CongruentRel)

open import Plasmaduck.Fold.Nat.Foldl using (foldl)
open import Plasmaduck.Fold.Nat.Merge using (merge; merge-pop-first; module MergeSubstitute; module MergeOnSetoid)

open import Plasmaduck.Fold.Nat.InfiniteReindexing as InfiniteReindexing using (InfiniteVector; HasTailAt; index-head-product; module FiniteVectorBijections) renaming (_~_ to _~'_; _≺_ to _≺'_)



{-
    Consider finite lists of Nats. You can bound one above by another if it's bounded above at every index.
    This here is (currently, at least) an attempt at showing a bijection between the set of such lists bounded by a specific list, and the product of the contents of the list.
-}
module Plasmaduck.Fold.Nat.FiniteReindexing where

variable
    a b c ℓ : Level
    m n : ℕ

open MergeSubstitute (discrete-setoid ℕ) using (merge-local-substitute-generate; merge-substitute-generate)
open MergeOnSetoid (discrete-setoid ℕ) using (merge-pop-last)

FiniteVector : ℕ → Set
FiniteVector n = FakeFin n → ℕ

module _ {n : ℕ} where

    infix 4 _~_
    _~_ : Rel (FiniteVector n) lzero
    u ~ v = ∀ i → u i ≡ v i

    infix 4 _≺_
    _≺_ : Rel (FiniteVector n) lzero
    _≺_ f g = ∀ i → f i < g i

    ≺-recomputable : Relation.Binary.Recomputable _≺_
    ≺-recomputable u≺v i = ≤-recompute (u≺v i)

    -- not tight
    ≺-trans : Transitive _≺_
    ≺-trans u≺v v≺w i = <-trans (u≺v i) (v≺w i)

    ≺-asym : .{{_ : NonZero n}} → Asymmetric _≺_
    ≺-asym u≺v v≺u = <-asym (u≺v (0 , squash (>-nonZero⁻¹ n))) (v≺u (0 , squash (>-nonZero⁻¹ n)))

    ≺-irrefl : .{{_ : NonZero n}} → Irreflexive _~_ _≺_
    ≺-irrefl u~v u≺v = <-irrefl (u~v (0 , squash (>-nonZero⁻¹ n))) (u≺v (0 , squash (>-nonZero⁻¹ n)))

    ≺-cong-≗ : CongruentRel (discrete-function-setoid (FakeFin n) ℕ) _≺_
    ≺-cong-≗ {u₁} {u₂} {v₁} {v₂} u₁≗u₂ v₁≗v₂ u₁≺v₁ i = begin
        suc (u₂ i)  ≡⟨ cong suc (≡-sym (u₁≗u₂ i)) ⟩
        suc (u₁ i)  ≤⟨ u₁≺v₁ i ⟩
        v₁ i        ≡⟨ v₁≗v₂ i ⟩
        v₂ i        ∎
        where open ≤-Reasoning

    infix 4 _≼_
    _≼_ : Rel (FiniteVector n) lzero
    u ≼ v = ∀ i → u i ≤ v i

    ≼-refl : Reflexive _≼_
    ≼-refl {u} i = ≤-refl

    ≼-reflexive : _≗_ Relation.Binary.⇒ _≼_
    ≼-reflexive {u} {v} u≗v i = ≤-reflexive (u≗v i)

    ≼-cong-≗ : CongruentRel (discrete-function-setoid (FakeFin n) ℕ) _≼_
    ≼-cong-≗ {u₁} {u₂} {v₁} {v₂} u₁≗u₂ v₁≗v₂ u₁≼v₁ i =  begin
        u₂ i    ≡⟨ ≡-sym (u₁≗u₂ i) ⟩
        u₁ i    ≤⟨ u₁≼v₁ i ⟩
        v₁ i    ≡⟨ v₁≗v₂ i ⟩
        v₂ i    ∎
        where open ≤-Reasoning

    ≼-trans : Transitive _≼_
    ≼-trans {u} {v} {w} u≼v v≼w i = ≤-trans (u≼v i) (v≼w i)

    ≺⇒≼ : _≺_ Relation.Binary.⇒ _≼_
    ≺⇒≼ {u} {v} u≺v i = <⇒≤ (u≺v i)

    ≺-≼-trans : Trans _≺_ _≼_ _≺_
    ≺-≼-trans {u} {v} {w} u≺v v≼w i = <-≤-trans (u≺v i) (v≼w i)

    ≼-≺-trans : Trans _≼_ _≺_ _≺_
    ≼-≺-trans {u} {v} {w} u≼v v≺w i = ≤-<-trans (u≼v i) (v≺w i)


module VectorProperties (vec : FiniteVector n) where
    IsNonZero : Set
    IsNonZero = ∀ i → NonZero (vec i)

open VectorProperties public

LesserFiniteVector : FiniteVector n → Set
LesserFiniteVector {n} vec = Σ (FiniteVector n) (_≺ vec)

LesserFiniteVectorSetoid : FiniteVector n → Setoid lzero lzero
LesserFiniteVectorSetoid {n} vec = setoid-on {A = LesserFiniteVector vec} (discrete-function-setoid (FakeFin n) ℕ) proj₁


extend : ℕ → FiniteVector m → InfiniteVector
extend {m} n v i with i <? m
... | no i≮m = n
... | yes i<m = v (i , squash i<m)

extend-force< :
    (n : ℕ) → (v : FiniteVector m) → (i : ℕ) →
    .(i<m : i < m) →
    extend n v i ≡ v (i , squash i<m)
extend-force< {m} n v i i<m with i <? m
... | no ¬i<m = ⊥-irr-elim (¬i<m i<m)
... | yes i<m = ≡-refl

extend-force¬< :
    (n : ℕ) → (v : FiniteVector m) → (i : ℕ) →
    .(¬i<m : ¬ i < m) →
    extend n v i ≡ n
extend-force¬< {m} n v i ¬i<m with i <? m
... | no ¬i<m = ≡-refl
... | yes i<m = ⊥-irr-elim (¬i<m i<m)

extend≺ : {i j : ℕ} → i < j → {u v : FiniteVector m} → u ≺ v → extend i u ≺' extend j v
extend≺ {m = m} {i = i} {j} i<j {u} {v} u≺v k with k <? m
... | no ¬k<m = i<j
... | yes k<m = u≺v (k , squash k<m)

clip : (n : ℕ) → InfiniteVector → FiniteVector n
clip _ vec (i , _) = vec i

clip≺ : (n : ℕ) → {vec₁ vec₂ : InfiniteVector} → vec₁ ≺' vec₂ → clip n vec₁ ≺ clip n vec₂
clip≺ n {vec₁} {vec₂} vec₁≺vec₂ (i , _) = vec₁≺vec₂ i

clip-extend : (n x : ℕ) → LeftInverse _~_ _~'_ (extend {m = n} x) (clip n)
clip-extend n x u (i , squash i<n) with i <? n
... | no i≮n = ⊥-irr-elim (i≮n i<n)
... | yes i<n = ≡-refl

index-product : FiniteVector n → ℕ
index-product {n} u = index-head-product (extend 1 u) n

IsNonZero⇒extend-nonZero : (x : ℕ) → .{{_ : NonZero x}} → {u : FiniteVector n} → IsNonZero u → InfiniteReindexing.IsNonZero (extend x u)
IsNonZero⇒extend-nonZero {n} (suc _) u-nonZero i with i <? n
... | no i≮n = record { nonZero = tt }
... | yes i<n = u-nonZero (i , squash _)

IsNonZero⇒product-nonZero : {u : FiniteVector n} → IsNonZero u → NonZero (index-product u)
IsNonZero⇒product-nonZero {n} {u} u-nonZero = InfiniteReindexing.vec-nonZero⇒index-head-product-nonZero {extend 1 u} (IsNonZero⇒extend-nonZero 1 u-nonZero) n


module Bijections
    {n : ℕ}
    {basesVec : FiniteVector n}
    (basesVec-NonZero : IsNonZero basesVec)
    where
    private
        N : ℕ
        N = index-product basesVec

        instance
            N-nonZero : NonZero N
            N-nonZero = IsNonZero⇒product-nonZero basesVec-NonZero

        extend-basesVec-nonZero : InfiniteReindexing.IsNonZero (extend 1 basesVec)
        extend-basesVec-nonZero = IsNonZero⇒extend-nonZero 1 basesVec-NonZero

        extend-basesVec-hasOneTailAt-n : InfiniteReindexing.HasOneTailAt (extend 1 basesVec) n
        extend-basesVec-hasOneTailAt-n i n≤i with i <? n
        ... | no ¬i<n = ≡-refl
        ... | yes i<n = ⊥-irr-elim (<-irrefl ≡-refl (<-≤-trans i<n n≤i))

        extend-basesVec-hasOneTail : InfiniteReindexing.HasOneTail (extend 1 basesVec)
        extend-basesVec-hasOneTail = n , extend-basesVec-hasOneTailAt-n

        _~′_ = LesserFiniteVectorSetoid basesVec .Setoid._≈_
        _~'′_ = InfiniteReindexing.LesserInfiniteVectorSetoid (extend 1 basesVec) .Setoid._≈_

    open import Plasmaduck.Number.NatModSetoid N using (_≃_; NatModSetoid; size-mod)
    open FiniteVectorBijections {extend 1 basesVec} extend-basesVec-nonZero extend-basesVec-hasOneTail using () renaming (
        finite-vector-bijection to infinite-finite-vector-bijection
        )

    -----------------------------------------------------------------------------------------
    --- First, establishing a bijection between the two representations of finite vectors ---
    -----------------------------------------------------------------------------------------

    extend-lesser : LesserFiniteVector basesVec → InfiniteReindexing.LesserInfiniteVector (extend 1 basesVec)
    extend-lesser (u , u≺bases) = extend 0 u , extend≺ (s≤s z≤n) u≺bases

    clip-lesser : InfiniteReindexing.LesserInfiniteVector (extend 1 basesVec) → LesserFiniteVector basesVec
    clip-lesser (u' , u'≺'bases) = clip n u' , ≺-cong-≗ (λ _ → ≡-refl) (clip-extend n 1 basesVec) (clip≺ n u'≺'bases)

    extend-lesser-cong : Congruent _~′_ _~'′_ extend-lesser
    extend-lesser-cong {u , u≺bases} {v , v≺bases} u~v i with i <? n
    ... | no ¬i<n = ≡-refl
    ... | yes i<n = u~v (i , squash i<n)

    clip-lesser-cong : Congruent _~'′_ _~′_ clip-lesser
    clip-lesser-cong {u , u≺'bases} {v , v≺'bases} u~′v (i , squash i<n) = u~′v i

    extend-clip-lesser-inverse : RightInverse {A = LesserFiniteVector basesVec} {InfiniteReindexing.LesserInfiniteVector (extend 1 basesVec)} _~′_ _~'′_ extend-lesser clip-lesser
    extend-clip-lesser-inverse (u , u≺'bases) i with i <? n
    ... | yes i<n = ≡-refl
    ... | no ¬i<n = ≡-sym (n<1⇒n≡0 (begin
        suc (u i)               ≤⟨ u≺'bases i ⟩
        extend 1 basesVec i     ≡⟨ extend-force¬< 1 basesVec i ¬i<n ⟩
        1                       ∎))
        where open ≤-Reasoning

    clip-extend-lesser-inverse : LeftInverse {A = LesserFiniteVector basesVec} {InfiniteReindexing.LesserInfiniteVector (extend 1 basesVec)} _~′_ _~'′_ extend-lesser clip-lesser
    clip-extend-lesser-inverse u-lesser@(u , u≺bases) i-fin@(i , squash i<n) =
        clip-lesser (extend-lesser u-lesser) .proj₁ i-fin   ≡⟨⟩
        clip n (extend 0 u) i-fin                           ≡⟨⟩
        extend 0 u i                                        ≡⟨ extend-force< 0 u i i<n ⟩
        u i-fin                                             ∎
        where open ≡-Reasoning

    extend-lesser-bijective : Bijective _~′_ _~'′_ extend-lesser
    extend-lesser-bijective = both-inv→bijective (LesserFiniteVectorSetoid basesVec) (InfiniteReindexing.LesserInfiniteVectorSetoid (extend 1 basesVec))
        (extend-lesser which-is-cong λ {x} {y} → extend-lesser-cong {x} {y}) ((clip-lesser which-is-cong λ {x} {y} → clip-lesser-cong {x} {y}) , clip-extend-lesser-inverse , extend-clip-lesser-inverse)

    clip-lesser-bijective : Bijective _~'′_ _~′_ clip-lesser
    clip-lesser-bijective = both-inv→bijective (InfiniteReindexing.LesserInfiniteVectorSetoid (extend 1 basesVec)) (LesserFiniteVectorSetoid basesVec)
        (clip-lesser which-is-cong λ {x} {y} → clip-lesser-cong {x} {y}) ((extend-lesser which-is-cong (λ {x} {y} → extend-lesser-cong {x} {y})) , extend-clip-lesser-inverse , clip-extend-lesser-inverse)

    finite-vector-representation-bijection : Bijection (LesserFiniteVectorSetoid basesVec) (InfiniteReindexing.LesserInfiniteVectorSetoid (extend 1 basesVec))
    finite-vector-representation-bijection = record {
        to = extend-lesser;
        cong = (λ {x} {y} → extend-lesser-cong {x} {y});
        bijective = extend-lesser-bijective
        }

    ---------------------------------------------------------------------
    --- Then we can just borrow the bijection from InfiniteReindexing ---
    ---------------------------------------------------------------------

    finite-vector-bijection : Bijection NatModSetoid (LesserFiniteVectorSetoid basesVec)
    finite-vector-bijection = invert-bijection finite-vector-representation-bijection ∘-bijection infinite-finite-vector-bijection

    FiniteVectorsFinite : HasSize (LesserFiniteVectorSetoid basesVec) N
    FiniteVectorsFinite = finite-vector-bijection ∘-bijection size-mod
