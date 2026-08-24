open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; cong; refl; sym; trans; inspect; [_])
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open import Relation.Binary using (Setoid; Rel; IsEquivalence; IsDecTotalOrder; IsTotalOrder; Total; IsPartialOrder; IsPreorder; Antisymmetric; _⇒_; Transitive; Decidable)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Function using (_∘_; id; Bijective; Bijection; Injective; Surjective)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (ℕ) renaming (zero to zeroℕ; suc to sucℕ; _≤_ to _≤ℕ_; _<_ to _<ℕ_; _≥_ to _≥ℕ_; _>_ to _>ℕ_; _≟_ to _≟ℕ_; _≤?_ to _≤ℕ?_; _<?_ to _<ℕ?_)
open import Data.Nat.Properties using (≤-<-trans; <-≤-trans) renaming (≤-reflexive to ≤ℕ-reflexive; ≤-refl to ≤ℕ-refl; ≤-trans to ≤ℕ-trans; ≤-total to ≤ℕ-total; ≤-antisym to ≤ℕ-antisym)
open import Data.Fin using (Fin; toℕ; fromℕ<) renaming (zero to zero-fin; suc to suc-fin; _<_ to _<-fin_; _≤_ to _≤-fin_; _≟_ to _≟-fin_; _≤?_ to _≤-fin?_; _<?_ to _<-fin?_)
open import Data.Fin.Properties using (toℕ<n; fromℕ<-toℕ; toℕ-fromℕ<)

open import Plasmaduck.Data.Product using (Σ≡; ×≡)
open import Plasmaduck.Data.Squash using (Squash; squash; squash-irrelevant; squash-change-type)
open import Plasmaduck.SetoidExperiment.SetoidMachinery using (discrete-setoid; from-discrete-cong; _which-is-cong_)
open import Plasmaduck.Function.InjectionSurjection using (both-inv→bijective)
open import Plasmaduck.Util.Case using (case_of_)
open import Plasmaduck.Relation.Equivalence using (≡-isEquivalence)



-- This pattern keeps appearing, so let's just formalize it
module Plasmaduck.Data.FakeFin where

variable
    m n : ℕ
    i j k : Fin n

FakeFin : ℕ → Set
FakeFin n = Σ ℕ λ m → Squash (m <ℕ n)

realize : FakeFin n → Fin n
realize {n} (m , squash m<n) = fromℕ< m<n

falsify : Fin n → FakeFin n
falsify {n} i = toℕ i , squash (toℕ<n i)

module _ {n : ℕ} where
    _≤_ : Rel (FakeFin n) lzero
    (i , _) ≤ (j , _) = i ≤ℕ j

    _<_ : Rel (FakeFin n) lzero
    (i , _) < (j , _) = i <ℕ j

    _≥_ : Rel (FakeFin n) lzero
    (i , _) ≥ (j , _) = i ≥ℕ j

    _>_ : Rel (FakeFin n) lzero
    (i , _) > (j , _) = i >ℕ j

    realize-preserves-≤ : {i j : FakeFin n} → i ≤ j → realize i ≤-fin realize j
    realize-preserves-≤ {i = (i , squash i<n)} {(j , squash j<n)} i≤j = ≤ℕ-trans (≤ℕ-trans (≤ℕ-reflexive (toℕ-fromℕ< i<n)) i≤j) (≤ℕ-reflexive (sym (toℕ-fromℕ< j<n)))

    realize-preserves-< : {i j : FakeFin n} → i < j → realize i <-fin realize j
    realize-preserves-< {i = (i , squash i<n)} {(j , squash j<n)} i<j = <-≤-trans (≤-<-trans (≤ℕ-reflexive (toℕ-fromℕ< i<n)) i<j) (≤ℕ-reflexive (sym (toℕ-fromℕ< j<n)))

    falsify-preserves-≤ : {i j : Fin n} → i ≤-fin j → falsify i ≤ falsify j
    falsify-preserves-≤ i≤j = i≤j

    falsify-preserves-< : {i j : Fin n} → i <-fin j → falsify i < falsify  j
    falsify-preserves-< i<j = i<j

    ≤-trans : Transitive _≤_
    ≤-trans i≤j j≤k = ≤ℕ-trans i≤j j≤k

    ≤-reflexive : _≡_ ⇒ _≤_
    ≤-reflexive refl = ≤ℕ-refl

    ≤-preorder : IsPreorder _≡_ _≤_
    ≤-preorder = record {
        isEquivalence = ≡-isEquivalence;
        reflexive = ≤-reflexive;
        trans = λ {i} {j} {k} i≤j j≤k → ≤-trans {i} {j} {k} i≤j j≤k
        }

    ≤-antisym : Antisymmetric _≡_ _≤_
    ≤-antisym {i = i , squash i<n} {j , squash j<n} i≤j j≤i = Σ≡ i=j (squash-change-type i=j {cong (λ m → Squash (m <ℕ n)) (sym i=j)} {squash i<n} {squash j<n})
        where
            i=j = ≤ℕ-antisym i≤j j≤i

    ≤-partialOrder : IsPartialOrder _≡_ _≤_
    ≤-partialOrder = record {
        isPreorder = ≤-preorder;
        antisym = ≤-antisym
        }

    ≤-total : Total _≤_
    ≤-total (i , squash i<n) (j , squash j<n) = ≤ℕ-total i j

    ≤-totalOrder : IsTotalOrder _≡_ _≤_
    ≤-totalOrder = record {
        isPartialOrder = ≤-partialOrder;
        total = ≤-total
        }

    _≟_ : Decidable (_≡_ {A = FakeFin n})
    _≟_ (i , squash _) (j , squash _) with i ≟ℕ j
    ... | yes i=j = yes (Σ≡ i=j (squash-change-type (sym i=j) {Bx=By = refl}))
    ... | no i≠j = no λ { refl → i≠j refl }

    _≤?_ : Decidable _≤_
    _≤?_ (i , squash _) (j , squash _) = i ≤ℕ? j

    ≤-decTotalOrder : IsDecTotalOrder _≡_ _≤_
    ≤-decTotalOrder = record {
        isTotalOrder = ≤-totalOrder;
        _≟_ = _≟_;
        _≤?_ = _≤?_
        }

realize-falsify : (realize ∘ falsify) i ≡ i
realize-falsify {i = i} = fromℕ<-toℕ i (toℕ<n i)

falsify-realize : ∀ {x : FakeFin n} → (falsify ∘ realize) x ≡ x
falsify-realize {x = m , squash m<n} = Σ≡ (toℕ-fromℕ< m<n) (squash-irrelevant _ _)

falsify-bijective : Bijective _≡_ _≡_ (falsify {n})
falsify-bijective {n = n} = both-inv→bijective (discrete-setoid (Fin n)) (discrete-setoid (FakeFin n)) (falsify {n} which-is-cong from-discrete-cong (discrete-setoid (FakeFin n)) (falsify {n})) ((realize which-is-cong from-discrete-cong (discrete-setoid (Fin n)) realize) , realize-falsify , falsify-realize)

falsify-bijection : Bijection (discrete-setoid (Fin n)) (discrete-setoid (FakeFin n))
falsify-bijection {n = n} = record {
    to = falsify {n};
    cong = from-discrete-cong (discrete-setoid (FakeFin n)) (falsify {n});
    bijective = falsify-bijective
    }

realize-bijective : Bijective _≡_ _≡_ (realize {n})
realize-bijective {n = n} = both-inv→bijective (discrete-setoid (FakeFin n)) (discrete-setoid (Fin n)) (realize {n} which-is-cong from-discrete-cong (discrete-setoid (Fin n)) (realize {n})) ((falsify which-is-cong from-discrete-cong (discrete-setoid (FakeFin n)) falsify) , falsify-realize , realize-falsify)

realize-bijection : Bijection (discrete-setoid (FakeFin n)) (discrete-setoid (Fin n))
realize-bijection {n = n} = record {
    to = realize {n};
    cong = from-discrete-cong (discrete-setoid (Fin n)) (realize {n});
    bijective = realize-bijective
    }
