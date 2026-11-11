open import Level using (Level; _⊔_) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary using (_⇒_; Rel; Decidable; Irreflexive; Reflexive; Transitive; Asymmetric; Antisymmetric; IsEquivalence; IsStrictTotalOrder; IsStrictPartialOrder; IsPreorder; IsPartialOrder; tri<; tri≈; tri>; _Respects₂_)
open import Function using (flip)
open import Plasmaduck.Util.Case using (case_of_)
open import Plasmaduck.Relation.OrderHelpers using (_Extends_; WeakTri; cmp₁; cmp₂; cmp₃)



module Plasmaduck.Relation.Order
    {s ℓ : Level} {S : Set s} -- The underlying set
    (_≈_ : Rel S ℓ)   -- The underlying equality relation
    where

variable
    a b c ℓ₁ ℓ₂ : Level


Total : Rel S ℓ₂ → Set (s ⊔ ℓ ⊔ ℓ₂)
Total _<_ = (x y : S) → WeakTri (x < y) (x ≈ y) (x > y)
    where _>_ = flip _<_

ComparableAt : Rel S ℓ₂ → (x y : S) → Set (ℓ ⊔ ℓ₂)
ComparableAt _<_ x y = WeakTri (x < y) (x ≈ y) (x > y)
    where _>_ = flip _<_

if-extends-then-same-comparable-at : {_#_ : Rel S ℓ₂} {_<_ : Rel S ℓ₁} → _#_ Extends _<_ → {x y : S} → ComparableAt _<_ x y → ComparableAt _#_ x y
if-extends-then-same-comparable-at #-extends-< (cmp₁ x<y) = cmp₁ (#-extends-< x<y)
if-extends-then-same-comparable-at #-extends-< (cmp₂ x≈y) = cmp₂ x≈y
if-extends-then-same-comparable-at #-extends-< (cmp₃ x>y) = cmp₃ (#-extends-< x>y)

show-total-order :
    (≈-isEquivalence : IsEquivalence _≈_) →
    (_<_ : Rel S ℓ₂) →
    (<-irrefl : Irreflexive _≈_ _<_) →
    (<-trans : Transitive _<_) →
    (<-cmp : Total _<_) →
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

module _ (≈-isEquivalence : IsEquivalence _≈_) (_≤_ : Rel S a) where
    open IsEquivalence ≈-isEquivalence using () renaming (refl to ≈-refl; sym to ≈-sym; trans to ≈-trans)

    Transitive-flip : Transitive _≤_ → Transitive (flip _≤_)
    Transitive-flip trans = flip trans

    Reflexive-flip : _≈_ ⇒ _≤_ → _≈_ ⇒ flip _≤_
    Reflexive-flip ≈⇒≤ x≈y = ≈⇒≤ (≈-sym x≈y)

    Antisymmetric-flip : Antisymmetric _≈_ _≤_ → Antisymmetric _≈_ (flip _≤_)
    Antisymmetric-flip antisym = flip antisym

    IsPreorder-flip : IsPreorder _≈_ _≤_ → IsPreorder _≈_ (flip _≤_)
    IsPreorder-flip isPreorder = record {
        isEquivalence = IsPreorder.isEquivalence isPreorder;
        reflexive = Reflexive-flip (IsPreorder.reflexive isPreorder);
        trans = Transitive-flip (IsPreorder.trans isPreorder)
        }

    IsPartialOrder-flip : IsPartialOrder _≈_ _≤_ → IsPartialOrder _≈_ (flip _≤_)
    IsPartialOrder-flip isPartialOrder = record {
        isPreorder = IsPreorder-flip (IsPartialOrder.isPreorder isPartialOrder);
        antisym = Antisymmetric-flip (IsPartialOrder.antisym isPartialOrder)
        }
