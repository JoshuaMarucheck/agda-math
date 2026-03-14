open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc; zero to lzero)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Function using (_∘_; flip)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary using (TotalOrder; DecTotalOrder; IsTotalOrder; IsStrictTotalOrder; Irreflexive; Transitive; Trans; Rel; IsEquivalence; _Respects₂_; _Respectsˡ_; _Respectsʳ_; Decidable; IsStrictPartialOrder; Trichotomous; Tri; tri<; tri≈; tri>; Asymmetric; IsDecStrictPartialOrder)

open import Plasmaduck.Util.Case using (case_of_)
open import Plasmaduck.Relation.Equivalence using (≡-isEquivalence; all-respects-≡)
open import Plasmaduck.Relation.Order using (ComparableAt; show-total-order)
open import Plasmaduck.Relation.OrderHelpers using (WeakTri; cmp₁; cmp₂; cmp₃; _Extends_)



module Plasmaduck.Relation.DecStrictPartialOrder {a ℓ ℓ₂ : Level} {A : Set a} {_≈_ : Rel A ℓ} {_<_ : Rel A ℓ₂} (isDecStrictPartialOrder : IsDecStrictPartialOrder _≈_ _<_) where

module Helpers {a ℓ ℓ₂ : Level} {A : Set a} {_≈_ : Rel A ℓ} {_<_ : Rel A ℓ₂} (isDecStrictPartialOrder : IsDecStrictPartialOrder _≈_ _<_) where

    open IsStrictPartialOrder (isDecStrictPartialOrder .IsDecStrictPartialOrder.isStrictPartialOrder) using (isEquivalence; irrefl; <-resp-≈) renaming (trans to <-trans) public
    open IsEquivalence (isDecStrictPartialOrder .IsDecStrictPartialOrder.isStrictPartialOrder .IsStrictPartialOrder.isEquivalence) using (refl; sym; trans) public

    _>_ = flip _<_

    _≤_ : Rel A (ℓ ⊔ ℓ₂)
    x ≤ y = x ≈ y ⊎ x < y

    _#_ : Rel A (ℓ ⊔ ℓ₂)
    x # y = ¬ (ComparableAt _≈_ _<_ x y)

    ≈-dec : Decidable _≈_
    ≈-dec = isDecStrictPartialOrder .IsDecStrictPartialOrder._≟_

    <-dec : Decidable _<_
    <-dec = isDecStrictPartialOrder .IsDecStrictPartialOrder._<?_

    ≤-dec : Decidable _≤_
    ≤-dec x y with <-dec x y
    ...          | (yes x<y) = yes (inj₂ x<y)
    ...          | (no ¬x<y) with ≈-dec x y
    ...                         | (yes x≈y) = yes (inj₁ x≈y)
    ...                         | (no x≉y) = no λ {(inj₁ x≈y) → x≉y x≈y; (inj₂ x<y) → ¬x<y x<y}

    ≤-respˡ-≈ : _≤_ Respectsˡ _≈_
    ≤-respˡ-≈ {x} {y} {z} y≈z (inj₁ y≈x) = inj₁ (trans (sym y≈z) y≈x)
    ≤-respˡ-≈ {x} {y} {z} y≈z (inj₂ y<x) = inj₂ (<-resp-≈ .proj₂ y≈z y<x)

    ≤-respʳ-≈ : _≤_ Respectsʳ _≈_
    ≤-respʳ-≈ {x} {y} {z} y≈z (inj₁ x≈y) = inj₁ (trans x≈y y≈z)
    ≤-respʳ-≈ {x} {y} {z} y≈z (inj₂ x<y) = inj₂ (<-resp-≈ .proj₁ y≈z x<y)

    ≤-resp-≈ : _≤_ Respects₂ _≈_
    ≤-resp-≈ = ≤-respʳ-≈ , ≤-respˡ-≈

    ≤-trans : Transitive _≤_
    ≤-trans (inj₁ x≈y) (inj₁ y≈z) = inj₁ (trans x≈y y≈z)
    ≤-trans (inj₂ x<y) (inj₁ y≈z) = inj₂ (<-resp-≈ .proj₁ y≈z x<y)
    ≤-trans (inj₁ x≈y) (inj₂ y<z) = inj₂ (<-resp-≈ .proj₂ (sym x≈y) y<z)
    ≤-trans (inj₂ x<y) (inj₂ y<z) = inj₂ (<-trans x<y y<z)

    ≤-<-trans-< : Trans _≤_ _<_ _<_
    ≤-<-trans-< (inj₁ x≈y) y<z = <-resp-≈ .proj₂ (sym x≈y) y<z
    ≤-<-trans-< (inj₂ x<y) y<z = <-trans x<y y<z

    <-≤-trans-< : Trans _<_ _≤_ _<_
    <-≤-trans-< x<y (inj₁ y≈z) = <-resp-≈ .proj₁ y≈z x<y
    <-≤-trans-< x<y (inj₂ y<z) = <-trans x<y y<z

    ≤-<-trans-≤ : Trans _≤_ _<_ _≤_
    ≤-<-trans-≤ x≤y y<z = inj₂ (≤-<-trans-< x≤y y<z)

    <-≤-trans-≤ : Trans _<_ _≤_ _≤_
    <-≤-trans-≤ x<y y≤z = inj₂ (<-≤-trans-< x<y y≤z)

open Helpers isDecStrictPartialOrder public


module RelExtension {x y : A} (x#y : x # y) where
    -- _<'_ extends _<_ with the additional comparison x < y.
    -- _<'_ is a minimal such relation.

    _<'_ : Rel A (ℓ ⊔ ℓ₂)
    a <' b = (a ≤ x × y ≤ b) ⊎ a < b

    extend-has-properties : IsDecStrictPartialOrder _≈_ _<'_
    extend-has-properties = record {
        isStrictPartialOrder = record {
            isEquivalence = isDecStrictPartialOrder .IsDecStrictPartialOrder.isStrictPartialOrder .IsStrictPartialOrder.isEquivalence;
            irrefl = <'-irrefl;
            trans = <'-trans;
            <-resp-≈ = <'-resp-≈
            };
        _≟_ = ≈-dec;
        _<?_ = _<'?_
        }
        where
            x≉y : ¬ x ≈ y
            x≉y = x#y ∘ cmp₂

            y≰x : ¬ y ≤ x
            y≰x (inj₁ y≈x) = x#y (cmp₂ (sym y≈x))
            y≰x (inj₂ y<x) = x#y (cmp₃ y<x)

            _<'?_ : Decidable _<'_
            _<'?_ a b with <-dec a b
            ...       | (yes a<b) = yes (inj₂ a<b)
            ...       | (no ¬a<b) with ≤-dec a x | ≤-dec y b
            ...                   | (yes a≤x)    | (yes y≤b) = yes (inj₁ (a≤x , y≤b))
            ...                   | (no ¬a≤x)    | _ = no λ { (inj₁ (a≤x , y≤b)) → ¬a≤x a≤x; (inj₂ a<b) → ¬a<b a<b}
            ...                   | _            | (no ¬y≤b)  = no λ { (inj₁ (a≤x , y≤b)) → ¬y≤b y≤b; (inj₂ a<b) → ¬a<b a<b}

            <'-irrefl : Irreflexive _≈_ _<'_
            <'-irrefl {a} {b} a≈b (inj₁ (a≤x , y≤b)) = y≰x (≤-trans (≤-respʳ-≈ (sym a≈b) y≤b) a≤x)
            <'-irrefl a≈b (inj₂ a<b) = irrefl a≈b a<b

            <'-trans : Transitive _<'_
            <'-trans {a} {b} {c} (inj₁ (a≤x , y≤b)) (inj₁ (b≤x , y≤c)) = ⊥-elim (y≰x (≤-trans y≤b b≤x))
            <'-trans {a} {b} {c} (inj₂ a<b) (inj₁ (b≤x , y≤c)) = inj₁ (<-≤-trans-≤ a<b b≤x , y≤c)
            <'-trans {a} {b} {c} (inj₁ (a≤x , y≤b)) (inj₂ b<c) = inj₁ (a≤x , ≤-<-trans-≤ y≤b b<c)
            <'-trans {a} {b} {c} (inj₂ a<b) (inj₂ b<c) = inj₂ (<-trans a<b b<c)

            <'-respˡ-≈ : _<'_ Respectsˡ _≈_
            <'-respˡ-≈ {a} {b} {c} b≈c (inj₁ (b≤x , y≤a)) = inj₁ (≤-respˡ-≈ b≈c b≤x , y≤a)
            <'-respˡ-≈ {a} {b} {c} b≈c (inj₂ b<a) = inj₂ (<-resp-≈ .proj₂ b≈c b<a)

            <'-respʳ-≈ : _<'_ Respectsʳ _≈_
            <'-respʳ-≈ {a} {b} {c} b≈c (inj₁ (a≤x , y≤b)) = inj₁ (a≤x , ≤-respʳ-≈ b≈c y≤b)
            <'-respʳ-≈ {a} {b} {c} b≈c (inj₂ a<b) = inj₂ (<-resp-≈ .proj₁ b≈c a<b)

            <'-resp-≈ : _<'_ Respects₂ _≈_
            <'-resp-≈ = <'-respʳ-≈ , <'-respˡ-≈

    extend-imposes-x<y : x <' y
    extend-imposes-x<y = inj₁ (inj₁ refl , inj₁ refl)

    extend-extends : _<'_ Extends _<_
    extend-extends = inj₂
    {-
        It's a strict extension, since we know x <' y despite x and y being uncomparable under _<_.
        We never actually use this fact anywhere. The whole proof would go through if we only said ¬ y ≤ x,
        though the extension may not be strict in that case. (In fact, it is strict if and only if ¬ x < y.)
    -}

    extend-is-minimal : {ℓ₃ : Level} {_<''_ : Rel A ℓ₃} → (IsDecStrictPartialOrder _≈_ _<''_) → _<''_ Extends _<_ → x <'' y → _<''_ Extends _<'_
    extend-is-minimal {_<''_ = _<''_} <''-isDecStrictPartialOrder <''-extends-< x<''y {a} {b} (inj₁ (a≤x , y≤b)) =
        <-≤-trans''-< (≤-<-trans''-< (≤''-extends-≤ a≤x) x<''y)  (≤''-extends-≤ y≤b)
        where
            open Helpers <''-isDecStrictPartialOrder renaming (_≤_ to _≤''_; ≤-<-trans-< to ≤-<-trans''-<; <-≤-trans-< to <-≤-trans''-<)
            ≤''-extends-≤ : ∀ {x y} → x ≤ y → x ≤'' y
            ≤''-extends-≤ {x} {y} (inj₁ x≈y) = inj₁ x≈y
            ≤''-extends-≤ {x} {y} (inj₂ x<y) = inj₂ (<''-extends-< x<y)
    extend-is-minimal {_<''_ = _<''_} <''-isDecStrictPartialOrder <''-extends-< x<''y {a} {b} (inj₂ a<b) = <''-extends-< a<b
