open import Level using (Level; _⊔_) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary using (Rel; Decidable; Irreflexive; Reflexive; Transitive; Asymmetric; IsEquivalence; IsStrictTotalOrder; IsStrictPartialOrder; tri<; tri≈; tri>; _Respects₂_)
open import Function using (flip)
open import Plasmaduck.Util.Case using (case_of_)
open import Plasmaduck.Relation.OrderHelpers using (WeakTri; cmp₁; cmp₂; cmp₃)



module Plasmaduck.Relation.Order
    {s ℓ : Level} {S : Set s} -- The underlying set
    (_≈_ : Rel S ℓ)   -- The underlying equality relation
    where

variable
    a b c ℓ₁ ℓ₂ : Level


Comparable : Rel S ℓ₂ → Set (s ⊔ ℓ ⊔ ℓ₂)
Comparable _<_ = (x y : S) → WeakTri (x < y) (x ≈ y) (x > y)
    where _>_ = flip _<_

ComparableAt : Rel S ℓ₂ → (x y : S) → Set (ℓ ⊔ ℓ₂)
ComparableAt _<_ x y = WeakTri (x < y) (x ≈ y) (x > y)
    where _>_ = flip _<_

show-total-order :
    (≈-isEquivalence : IsEquivalence _≈_) →
    (_<_ : Rel S ℓ₂) →
    (<-irrefl : Irreflexive _≈_ _<_) →
    (<-trans : Transitive _<_) →
    (<-cmp : Comparable _<_) →
    (<-resp-≈ : _<_ Respects₂ _≈_) →
    IsStrictTotalOrder _≈_ _<_
show-total-order ≈-isEquivalence _<_ <-irrefl <-trans <-cmp <-resp-≈ = record {
    isStrictPartialOrder = isStrictPartialOrder;
    compare = λ x y → case <-cmp x y of λ {
        (cmp₁ x<y) → tri< x<y (λ x≡y → <-irrefl x≡y x<y) (<-asym x<y);
        (cmp₂ x≡y) → tri≈ (<-irrefl x≡y) x≡y (<-irrefl (sym x≡y));
        (cmp₃ x>y) → tri> (<-asym x>y) (λ x≡y → <-irrefl (sym x≡y) x>y) x>y
        }
    }
    where
        open IsEquivalence ≈-isEquivalence using (refl; sym)

        isStrictPartialOrder : IsStrictPartialOrder _≈_ _<_
        isStrictPartialOrder = record {
            isEquivalence = ≈-isEquivalence;
            irrefl = <-irrefl;
            trans = <-trans;
            <-resp-≈ = <-resp-≈
            }

        <-asym : Asymmetric _<_
        <-asym = IsStrictPartialOrder.asym isStrictPartialOrder
