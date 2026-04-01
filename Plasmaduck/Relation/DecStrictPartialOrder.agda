open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≢_; _≡_; inspect; cong; Reveal_·_is_; [_]) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Function using (_∘_; _on_; flip; id; Injective; Surjective; Bijection; Congruent)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (ℕ; _+_; _∸_; z≤n; s≤s) renaming (suc to suc-ℕ; zero to zero-ℕ; _≤_ to _≤ℕ_; _<_ to _<ℕ_; _≥_ to _≥ℕ_; _>_ to _>ℕ_)
open import Data.Fin using () renaming (suc to suc-fin; zero to zero-fin)
open import Relation.Binary using (TotalOrder; DecTotalOrder; IsTotalOrder; IsStrictTotalOrder; Reflexive; Irreflexive; Transitive; Trans; Rel; IsEquivalence; _Respects₂_; _Respectsˡ_; _Respectsʳ_; Decidable; IsStrictPartialOrder; Trichotomous; Tri; tri<; tri≈; tri>; Asymmetric; IsDecStrictPartialOrder)
open import Relation.Binary.Bundles using (Setoid)

open import Plasmaduck.Util.Case using (case_of_)
open import Plasmaduck.Relation.Equivalence using (≡-isEquivalence; all-respects-≡)
open import Plasmaduck.Relation.Order using (ComparableAt; show-total-order)
open import Plasmaduck.Relation.OrderHelpers using (WeakTri; cmp₁; cmp₂; cmp₃; _Extends_)
open import Plasmaduck.Counting.Counting using (HasSize; IsFinite; AtMostSize; any; all; subset-of-finite-is-upper-bounded; one-equal-item; fin-setoid; ⊎-size-theorem; _∘-at-most-size_)
open import Plasmaduck.Relation.Defs using (CongruentRel; CongruentProperty; respects→cong-rel; rel-property) renaming (≈-cong to ≈-cong')
open import Plasmaduck.SetoidExperiment.SetoidMachinery using (property-subset-setoid; from-discrete-cong; ⊎-setoid; rel₁; rel₂)
open import Plasmaduck.Counting.Strengthening using (subset-of-finite-is-finite; strengthen-core; at-most-size-subset-decr; n∸1-unequal-items)
open import Plasmaduck.Function.Bijection using (invert-bijection; id-bijection; ⊎-bijection; _∘-bijection_)
open import Plasmaduck.Util.Negation using (¬¬-lift)
open import Plasmaduck.Relation.Restriction using (restrict-relation-dec)
open import Plasmaduck.Property.Restriction using (restrict-property; restrict-property-dec; restrict-collapse)
open import Plasmaduck.Function.InjectionSurjection using (bijection→surjection; _∘-surjection_)
open import Plasmaduck.Function.Surjectionish using (surjection→surjectionish)
open import Plasmaduck.Relation.RelationVector using (module RelationTree)



module Plasmaduck.Relation.DecStrictPartialOrder where

module Helpers {a ℓ ℓ₂ : Level} {A : Set a} {_≈_ : Rel A ℓ} {_<_ : Rel A ℓ₂} (isDecStrictPartialOrder : IsDecStrictPartialOrder _≈_ _<_) where

    open IsStrictPartialOrder (isDecStrictPartialOrder .IsDecStrictPartialOrder.isStrictPartialOrder) using (isEquivalence; irrefl; asym; <-resp-≈) renaming (trans to <-trans) public
    open IsEquivalence (isDecStrictPartialOrder .IsDecStrictPartialOrder.isStrictPartialOrder .IsStrictPartialOrder.isEquivalence) using (refl; sym; trans) public

    A-setoid : Setoid a ℓ
    A-setoid = record {
        Carrier = A;
        _≈_ = _≈_;
        isEquivalence = isDecStrictPartialOrder .IsDecStrictPartialOrder.isStrictPartialOrder .IsStrictPartialOrder.isEquivalence
        }

    <-cong : CongruentRel A-setoid _<_
    <-cong = respects→cong-rel A-setoid (isDecStrictPartialOrder .IsDecStrictPartialOrder.isStrictPartialOrder .IsStrictPartialOrder.<-resp-≈)

    ≈-cong : CongruentRel A-setoid _≈_
    ≈-cong = ≈-cong' A-setoid

    ComparableAt-cong : CongruentRel A-setoid (ComparableAt _≈_ _<_)
    ComparableAt-cong x₁≈x₂ y₁≈y₂ (cmp₁ x₁<y₁) = cmp₁ (<-cong x₁≈x₂ y₁≈y₂ x₁<y₁)
    ComparableAt-cong x₁≈x₂ y₁≈y₂ (cmp₂ x₁≈y₁) = cmp₂ (≈-cong x₁≈x₂ y₁≈y₂ x₁≈y₁)
    ComparableAt-cong x₁≈x₂ y₁≈y₂ (cmp₃ x₁>y₁) = cmp₃ (<-cong y₁≈y₂ x₁≈x₂ x₁>y₁)

    _>_ = flip _<_

    _≤_ : Rel A (ℓ ⊔ ℓ₂)
    x ≤ y = x ≈ y ⊎ x < y

    _#_ : Rel A (ℓ ⊔ ℓ₂)
    x # y = ¬ (ComparableAt _≈_ _<_ x y)

    _≈?_ : Decidable _≈_
    _≈?_ = isDecStrictPartialOrder .IsDecStrictPartialOrder._≟_

    _<?_ : Decidable _<_
    _<?_ = isDecStrictPartialOrder .IsDecStrictPartialOrder._<?_

    _≤?_ : Decidable _≤_
    _≤?_ x y with x <? y
    ...          | (yes x<y) = yes (inj₂ x<y)
    ...          | (no ¬x<y) with x ≈? y
    ...                         | (yes x≈y) = yes (inj₁ x≈y)
    ...                         | (no x≉y) = no λ {(inj₁ x≈y) → x≉y x≈y; (inj₂ x<y) → ¬x<y x<y}

    ≤-cong : CongruentRel A-setoid _≤_
    ≤-cong x₁≈x₂ y₁≈y₂ (inj₁ x₁≈y₁) = inj₁ (trans (sym x₁≈x₂) (trans x₁≈y₁ y₁≈y₂))
    ≤-cong x₁≈x₂ y₁≈y₂ (inj₂ x₁<y₁) = inj₂ (<-cong x₁≈x₂ y₁≈y₂ x₁<y₁)

    ≤-reflexive : ∀ {x y : A} → x ≈ y → x ≤ y
    ≤-reflexive = inj₁

    ≤-refl : Reflexive _≤_
    ≤-refl = ≤-reflexive refl

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

    ≤-<-trans : Trans _≤_ _<_ _<_
    ≤-<-trans (inj₁ x≈y) y<z = <-resp-≈ .proj₂ (sym x≈y) y<z
    ≤-<-trans (inj₂ x<y) y<z = <-trans x<y y<z

    <-≤-trans : Trans _<_ _≤_ _<_
    <-≤-trans x<y (inj₁ y≈z) = <-resp-≈ .proj₁ y≈z x<y
    <-≤-trans x<y (inj₂ y<z) = <-trans x<y y<z

    ≤-<-trans-≤ : Trans _≤_ _<_ _≤_
    ≤-<-trans-≤ x≤y y<z = inj₂ (≤-<-trans x≤y y<z)

    <-≤-trans-≤ : Trans _<_ _≤_ _≤_
    <-≤-trans-≤ x<y y≤z = inj₂ (<-≤-trans x<y y≤z)

    -- Technically, this doesn't require decidability, only irreflexivity of _<_
    weak-tri→tri : {x y : A} → ComparableAt _≈_ _<_ x y → Tri (x < y) (x ≈ y) (x > y)
    weak-tri→tri (cmp₁ x<y) = tri< x<y (λ x≈y → irrefl x≈y x<y) (λ x>y → irrefl refl (<-trans x<y x>y))
    weak-tri→tri (cmp₂ x≈y) = tri≈ (λ x<y → irrefl x≈y x<y) x≈y (λ x>y → irrefl (sym x≈y) x>y)
    weak-tri→tri (cmp₃ x>y) = tri> ((λ x<y → irrefl refl (<-trans x<y x>y))) (λ x≈y → irrefl (sym x≈y) x>y) x>y

    weak-tri-dec : Decidable (ComparableAt _≈_ _<_)
    weak-tri-dec x y with x <? y | x ≈? y | y <? x
    ... | yes pf | _ | _ = yes (cmp₁ pf)
    ... | _ | yes pf | _ = yes (cmp₂ pf)
    ... | _ | _ | yes pf = yes (cmp₃ pf)
    ... | no pf₁ | no pf₂ | no pf₃ = no λ weak-tri → case weak-tri of λ {
        (cmp₁ pf) → pf₁ pf;
        (cmp₂ pf) → pf₂ pf;
        (cmp₃ pf) → pf₃ pf
        }

    tri-dec : (x y : A) → Dec (Tri (x < y) (x ≈ y) (x > y))
    tri-dec x y = sol
        where
            tri→weak-tri : Tri (x < y) (x ≈ y) (x > y) → WeakTri (x < y) (x ≈ y) (x > y)
            tri→weak-tri (tri< pf _ _) = cmp₁ pf
            tri→weak-tri (tri≈ _ pf _) = cmp₂ pf
            tri→weak-tri (tri> _ _ pf) = cmp₃ pf

            sol : Dec (Tri (x < y) (x ≈ y) (x > y))
            sol with weak-tri-dec x y
            ... | no pf = no λ tri → pf (tri→weak-tri tri)
            ... | yes (cmp₁ x<y) = yes (tri< x<y (λ x≈y → irrefl x≈y x<y) (asym x<y))
            ... | yes (cmp₂ x≈y) = yes (tri≈ (irrefl x≈y) x≈y (irrefl (sym x≈y)))
            ... | yes (cmp₃ x>y) = yes (tri> (asym x>y) (λ x≈y → irrefl (sym x≈y) x>y) x>y)

module _ {a ℓ ℓ₂ : Level} {A : Set a} {_≈_ : Rel A ℓ} {_<_ : Rel A ℓ₂} (isDecStrictPartialOrder : IsDecStrictPartialOrder _≈_ _<_) where
    open Helpers isDecStrictPartialOrder
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
            _≟_ = _≈?_;
            _<?_ = _<'?_
            }
            where
                x≉y : ¬ x ≈ y
                x≉y = x#y ∘ cmp₂

                y≰x : ¬ y ≤ x
                y≰x (inj₁ y≈x) = x#y (cmp₂ (sym y≈x))
                y≰x (inj₂ y<x) = x#y (cmp₃ y<x)

                _<'?_ : Decidable _<'_
                _<'?_ a b with a <? b
                ...       | (yes a<b) = yes (inj₂ a<b)
                ...       | (no ¬a<b) with a ≤? x | y ≤? b
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
                open Helpers <''-isDecStrictPartialOrder renaming (_≤_ to _≤''_; ≤-<-trans to ≤-<-trans''-<; <-≤-trans to <-≤-trans''-<)
                ≤''-extends-≤ : ∀ {x y} → x ≤ y → x ≤'' y
                ≤''-extends-≤ {x} {y} (inj₁ x≈y) = inj₁ x≈y
                ≤''-extends-≤ {x} {y} (inj₂ x<y) = inj₂ (<''-extends-< x<y)
        extend-is-minimal {_<''_ = _<''_} <''-isDecStrictPartialOrder <''-extends-< x<''y {a} {b} (inj₂ a<b) = <''-extends-< a<b


module Trees where
    module _ {a ℓ ℓ₂ : Level} {A : Set a} {_≈_ : Rel A ℓ} {_<_ : Rel A ℓ₂} (isDecStrictPartialOrder : IsDecStrictPartialOrder _≈_ _<_) where
        open Helpers isDecStrictPartialOrder
        {-
            Some notes on the below definitions (especially IsLocallyNthPlace and HasGlobalPosition):

            Note that if x < y , x < z are the only relations, then y and z are both locally in 0th place, and x is locally in 2nd.
            Since y and z are uncomparable, only x's position is global.

            Likewise, if you have y < x and z < x as the only relations, then x is in 0th place, and y and z are both in 1st place.
            Again, only x's position is global.
        -}

        LocalAncestorsOf : (x : A) → Setoid (a ⊔ ℓ₂) ℓ
        LocalAncestorsOf x = property-subset-setoid A-setoid (x <_)

        LocalDescendentsOf : (x : A) → Setoid (a ⊔ ℓ₂) ℓ
        LocalDescendentsOf x = property-subset-setoid A-setoid (_< x)

        LocallyComparableTo : (x : A) → Setoid (a ⊔ ℓ ⊔ ℓ₂) ℓ
        LocallyComparableTo x = property-subset-setoid A-setoid (ComparableAt _≈_ _<_ x)

        -- Where 0th place is best place, and 1st is after that
        IsLocallyNthPlace : (x : A) → (n : ℕ) → Set (a ⊔ ℓ ⊔ ℓ₂)
        IsLocallyNthPlace x n = HasSize (LocalAncestorsOf x) n

        BetterThanN : (x : A) → (n : ℕ) → Set (a ⊔ ℓ ⊔ ℓ₂)
        BetterThanN x n = HasSize (LocalDescendentsOf x) n

        local-split-bijection : (x : A) →
            Bijection
                (property-subset-setoid A-setoid (ComparableAt _≈_ _<_ x))
                (⊎-setoid
                    (property-subset-setoid A-setoid (x <_))  (⊎-setoid
                    (property-subset-setoid A-setoid (x ≈_))
                    (property-subset-setoid A-setoid (x >_))
                ))
        local-split-bijection x = record {
            to = to;
            cong = to-cong;
            bijective = to-inj , to-surj
            }
            where
                B-setoid = property-subset-setoid A-setoid (ComparableAt _≈_ _<_ x)
                C-setoid = (⊎-setoid
                        (property-subset-setoid A-setoid (x <_))  (⊎-setoid
                        (property-subset-setoid A-setoid (x ≈_))
                        (property-subset-setoid A-setoid (x >_))
                    ))
                B = B-setoid .Setoid.Carrier
                C = C-setoid .Setoid.Carrier

                _~_ = C-setoid .Setoid._≈_

                -- The relation for B-setoid, but better for reasoning with
                -- open IsEquivalence (A-setoid .Setoid.isEquivalence) renaming (refl to ~-refl; sym to ~-sym; trans to ~-trans)

                to : B → C
                to (y , cmp₁ x<y) = inj₁ (y , x<y)
                to (y , cmp₂ x≈y) = inj₂ (inj₁ (y , x≈y))
                to (y , cmp₃ x>y) = inj₂ (inj₂ (y , x>y))

                to-cong : Congruent (B-setoid .Setoid._≈_) (C-setoid .Setoid._≈_) to
                to-cong {x = (y , cmp₁ _)} {y = (z , cmp₁ _)} y≈z = rel₁ y≈z
                to-cong {x = (y , cmp₂ _)} {y = (z , cmp₂ _)} y≈z = rel₂ (rel₁ y≈z)
                to-cong {x = (y , cmp₃ _)} {y = (z , cmp₃ _)} y≈z = rel₂ (rel₂ y≈z)

                to-cong {x = (y , cmp₁ x<y)} {y = (z , cmp₂ x≈z)} y≈z = ⊥-elim (irrefl (trans x≈z (sym y≈z)) x<y)
                to-cong {x = (y , cmp₁ x<y)} {y = (z , cmp₃ x>z)} y≈z = ⊥-elim (irrefl (sym y≈z) (<-trans x>z x<y))
                to-cong {x = (y , cmp₂ x≈y)} {y = (z , cmp₁ x<z)} y≈z = ⊥-elim (irrefl (trans x≈y y≈z) x<z)
                to-cong {x = (y , cmp₂ x≈y)} {y = (z , cmp₃ x>z)} y≈z = ⊥-elim (irrefl (sym (trans x≈y y≈z)) x>z)
                to-cong {x = (y , cmp₃ x>y)} {y = (z , cmp₁ x<z)} y≈z = ⊥-elim (irrefl y≈z (<-trans x>y x<z))
                to-cong {x = (y , cmp₃ x>y)} {y = (z , cmp₂ x≈z)} y≈z = ⊥-elim (irrefl (trans y≈z (sym x≈z)) x>y)

                to-inj : Injective (B-setoid .Setoid._≈_) _~_ to
                to-inj {x = (y , cmp₁ x<y)} {y = (z , cmp₁ x<z)} (rel₁ y≈z) = y≈z
                to-inj {x = (y , cmp₂ x<y)} {y = (z , cmp₂ x<z)} (rel₂ (rel₁ y≈z)) = y≈z
                to-inj {x = (y , cmp₃ x<y)} {y = (z , cmp₃ x<z)} (rel₂ (rel₂ y≈z)) = y≈z
                to-inj {x = (y , cmp₂ x<y)} {y = (z , cmp₃ x<z)} (rel₂ ())
                to-inj {x = (y , cmp₃ x<y)} {y = (z , cmp₂ x<z)} (rel₂ ())

                to-surj : Surjective (B-setoid .Setoid._≈_) _~_ to
                to-surj (inj₁ (y , x<y))        = (y , cmp₁ x<y) , λ {
                    {z , cmp₁ x<z} z≈y → rel₁ z≈y;
                    {z , cmp₂ x≈z} z≈y → ⊥-elim (irrefl (trans x≈z z≈y) x<y);
                    {z , cmp₃ x>z} z≈y → ⊥-elim (irrefl z≈y (<-trans x>z x<y))
                    }
                to-surj (inj₂ (inj₁ (y , x≈y))) = (y , cmp₂ x≈y) , λ {
                    {z , cmp₁ x<z} z≈y → ⊥-elim (irrefl (trans x≈y (sym z≈y)) x<z);
                    {z , cmp₂ x≈z} z≈y → rel₂ (rel₁ z≈y);
                    {z , cmp₃ x>z} z≈y → ⊥-elim (irrefl (trans z≈y (sym x≈y)) x>z)
                    }
                to-surj (inj₂ (inj₂ (y , x>y))) = (y , cmp₃ x>y) , λ {
                    {z , cmp₁ x<z} z≈y → ⊥-elim (irrefl (sym z≈y) (<-trans x>y x<z));
                    {z , cmp₂ x≈z} z≈y → ⊥-elim (irrefl (sym (trans x≈z z≈y)) x>y);
                    {z , cmp₃ x>z} z≈y → rel₂ (rel₂ z≈y)
                    }

        local-split-bijection' : (x : A) →
            Bijection
                (LocallyComparableTo x)
                (⊎-setoid
                    (LocalAncestorsOf x)  (⊎-setoid
                    (fin-setoid 1)
                    (LocalDescendentsOf x)
                ))
        local-split-bijection' x =
            ⊎-bijection (id-bijection (LocalAncestorsOf x)) (
                ⊎-bijection (invert-bijection (one-equal-item A-setoid x))
                (id-bijection (LocalDescendentsOf x))
            ) ∘-bijection local-split-bijection x

        local-size-split : (x : A) {m n : ℕ} →
            HasSize (LocalAncestorsOf x) m →
            HasSize (LocalDescendentsOf x) n →
            HasSize (LocallyComparableTo x) (m + (1 + n))
        local-size-split x m-ancestors n-descendents =
            (invert-bijection (local-split-bijection' x))
                ∘-bijection
            (⊎-size-theorem m-ancestors (⊎-size-theorem (id-bijection (fin-setoid 1)) n-descendents))

        HasGlobalPosition : (x : A) → Set (a ⊔ ℓ ⊔ ℓ₂)
        HasGlobalPosition x = ∀ (y : A) → ComparableAt _≈_ _<_ x y

        global→comparable-bijection : {x : A} → HasGlobalPosition x → Bijection A-setoid (LocallyComparableTo x)
        global→comparable-bijection {x = x} x-global = record {
            to = λ y → y , x-global y;
            cong = id;
            bijective = id , λ (z , _) → z , id
            }

        -- In every total order extension of this partial order, x is in position n
        IsGloballyNthPlace : (x : A) → (n : ℕ) → Set (a ⊔ ℓ ⊔ ℓ₂)
        IsGloballyNthPlace x n = IsLocallyNthPlace x n × HasGlobalPosition x

        has-global-position-dec : IsFinite A-setoid → (x : A) → Dec (HasGlobalPosition x)
        has-global-position-dec A-finite x = all A-finite (ComparableAt _≈_ _<_ x) (rel-property A-setoid ComparableAt-cong x) (weak-tri-dec x)

        local-position-find : IsFinite A-setoid → (x : A) → Σ ℕ λ n → IsLocallyNthPlace x n
        local-position-find A-finite x = subset-of-finite-is-finite _≈?_ {P = (x <_)} (<-resp-≈ .proj₁) (x <?_) A-finite

        local-descendents-find : IsFinite A-setoid → (x : A) → Σ ℕ λ n → BetterThanN x n
        local-descendents-find A-finite x = subset-of-finite-is-finite _≈?_ {P = (_< x)} (<-resp-≈ .proj₂) (_<? x) A-finite

        -- Is x greater than everything it's comparable to
        IsLocallyMaximal : (x : A) → Set (a ⊔ ℓ₂)
        IsLocallyMaximal x = ¬ Σ A λ y → x < y

        LocallyMaximal : Setoid (a ⊔ ℓ₂) ℓ
        LocallyMaximal = property-subset-setoid A-setoid IsLocallyMaximal

        is-locally-maximal-dec : IsFinite A-setoid → (x : A) → Dec (IsLocallyMaximal x)
        is-locally-maximal-dec A-finite x with any A-finite (x <_) (λ {y₁} {y₂} y₁≈y₂ x<y₁ → <-≤-trans x<y₁ (≤-reflexive y₁≈y₂)) (x <?_)
        ... | yes pf = no (¬¬-lift pf)
        ... | no pf = yes pf

        locally-maximal-find : IsFinite A-setoid → IsFinite LocallyMaximal
        locally-maximal-find A-finite = subset-of-finite-is-finite _≈?_ {P = IsLocallyMaximal} (λ {x} {y} x≈y x-maximal (z , y<z) → x-maximal (z , ≤-<-trans (≤-reflexive x≈y) y<z)) (is-locally-maximal-dec A-finite) A-finite

        -- x and y are separated by z
        separation : (x y z : A) → Set ℓ₂
        separation x y z = x < z × z < y

        ¬separation-edge-refl₁ : (x y : A) → ¬ separation x y x
        ¬separation-edge-refl₁ x y (x<x , _) = irrefl refl x<x

        ¬separation-edge-refl₂ : (x y : A) → ¬ separation x y y
        ¬separation-edge-refl₂ x y (_ , y<y) = irrefl refl y<y

        separation-dec : (x y z : A) → Dec (separation x y z)
        separation-dec x y z with x <? z | z <? y
        ... | yes pf₁ | yes pf₂ = yes (pf₁ , pf₂)
        ... | no ¬x<z | _ = no (¬x<z ∘ proj₁)
        ... | _ | no ¬z<y = no (¬z<y ∘ proj₂)

        separated : Rel A (a ⊔ ℓ₂)
        separated x y = Σ A (separation x y)

        separated-cong : (x y : A) → CongruentProperty A-setoid (separation x y)
        separated-cong x y {z₁} {z₂} z₁≈z₂ (x<z₁ , z₁<y) = <-cong refl z₁≈z₂ x<z₁ , <-cong z₁≈z₂ refl z₁<y

        separated-dec : IsFinite A-setoid → Decidable separated
        separated-dec A-finite x y = any A-finite (separation x y) (separated-cong x y) (separation-dec x y)

        _child-of_ : Rel A (a ⊔ ℓ₂)
        y child-of x = y < x × (∀ (z : A) → ¬ (y < z × z < x))

        is-child-dec : IsFinite A-setoid → Decidable _child-of_
        is-child-dec A-finite y x with y <? x | separated-dec A-finite y x
        ... | yes y<x | no ¬y<z<x = yes (y<x , λ z y<z<x → ¬y<z<x (z , y<z<x))
        ... | _ | yes (z , y<z<x) = no λ (y<x , ¬y<z<x) → ¬y<z<x z y<z<x
        ... | no ¬y<x | _ = no λ (y<x , ¬y<z<x) → ¬y<x y<x

        is-child-cong : CongruentRel A-setoid _child-of_
        is-child-cong y₁≈y₂ x₁≈x₂ (y₁<x₁ , no-separation) = <-cong y₁≈y₂ x₁≈x₂ y₁<x₁ , λ z (y₂<z , z<x₂) → no-separation z (<-cong (sym y₁≈y₂) refl y₂<z , <-cong refl (sym x₁≈x₂) z<x₂)

        ChildrenOf : (x : A) → Setoid (a ⊔ ℓ₂) ℓ
        ChildrenOf x = property-subset-setoid A-setoid (_child-of x)

        HasChildren : (x : A) (n : ℕ) → Set (a ⊔ ℓ ⊔ ℓ₂)
        HasChildren x n = HasSize (ChildrenOf x) n

        count-children : IsFinite A-setoid → (x : A) → IsFinite (ChildrenOf x)
        count-children A-finite x = subset-of-finite-is-finite _≈?_ (rel-property A-setoid {_~_ = flip _child-of_} (flip is-child-cong) x) (λ q → is-child-dec A-finite q x) A-finite

        module DescendentToChild where
            open RelationTree _child-of_ using (RelTree; branch-type; lift-rel-to-branch; trans-branch; pop-last)

            -- Note that this finds *a* path from x to y, not every path
            find-separation : IsFinite A-setoid → {x y : A} → x < y → branch-type x y
            find-separation A-finite@(n , A-size-n) {x} {y} x<y = find-separation-helper x<y (subset-of-finite-is-upper-bounded (separated-cong x y) (separation-dec x y) A-size-n)
                where
                    -- by what amounts to strong induction on n
                    find-separation-helper :
                        {x y : A} → x < y →
                        {n : ℕ} → AtMostSize (property-subset-setoid A-setoid (separation x y)) n →
                        branch-type x y
                    find-separation-helper {x = x} {y} x<y (inj₂ no-sep) = lift-rel-to-branch (x<y , λ z x<z<y → no-sep (z , x<z<y))
                    find-separation-helper {x = x} {y} x<y {zero-ℕ} (inj₁ n-items-at-most) with strengthen-core (λ x₂ y₂ → x₂ .proj₁ ≈? y₂ .proj₁) (inj₁ n-items-at-most)
                    ... | zero-ℕ , m-items , z≤n = lift-rel-to-branch (x<y , λ z x<z<y → case invert-bijection m-items .Bijection.to (z , x<z<y) of λ ())
                    find-separation-helper {x = x} {y} x<y {suc-ℕ n'} (inj₁ n-items-at-most) with strengthen-core (λ x₂ y₂ → x₂ .proj₁ ≈? y₂ .proj₁) (inj₁ n-items-at-most)
                    ... | zero-ℕ , m-items , z≤n = lift-rel-to-branch (x<y , λ z x<z<y → case invert-bijection m-items .Bijection.to (z , x<z<y) of λ ())
                    ... | suc-ℕ m' , m-items , m≤n = recursive-call
                        where
                            base-setoid = property-subset-setoid A-setoid (separation x y)

                            xy-separation : separated x y
                            xy-separation = m-items .Bijection.to zero-fin

                            z = xy-separation .proj₁
                            x<z<y = xy-separation .proj₂
                            x<z = x<z<y .proj₁
                            z<y = x<z<y .proj₂

                            xz-double-separation-size-n' : AtMostSize (property-subset-setoid base-setoid (restrict-property A-setoid (separation x y) (separation x z))) n'
                            xz-double-separation-size-n' =
                                at-most-size-subset-decr
                                    {A-setoid = base-setoid}
                                    (restrict-relation-dec A-setoid (separation x y) _≈?_)
                                    {P = restrict-property A-setoid (separation x y) (separation x z)}
                                    (separated-cong x z)
                                    (restrict-property-dec A-setoid (separation x y) ((separation-dec x z)))
                                    {x = (z , x<z<y)} (λ (_ , z<z) → irrefl refl z<z) {n = n'}
                                    (inj₁ n-items-at-most)

                            xz-separation-size-n' : AtMostSize (property-subset-setoid A-setoid (separation x z)) n'
                            xz-separation-size-n' = surjection→surjectionish (bijection→surjection (restrict-collapse A-setoid (separation x y) (separation x z) (λ (x<q , q<z) → x<q , <-trans q<z z<y))) ∘-at-most-size xz-double-separation-size-n' --

                            recursive-call₁ : branch-type x z
                            recursive-call₁ = find-separation-helper {x = x} {y = z} x<z xz-separation-size-n'

                            zy-double-separation-size-n' : AtMostSize (property-subset-setoid base-setoid (restrict-property A-setoid (separation x y) (separation z y))) n'
                            zy-double-separation-size-n' =
                                at-most-size-subset-decr
                                {A-setoid = base-setoid}
                                (restrict-relation-dec A-setoid (separation x y) _≈?_)
                                {P = restrict-property A-setoid (separation x y) (separation z y)}
                                (separated-cong z y)
                                (restrict-property-dec A-setoid (separation x y) ((separation-dec z y)))
                                {x = (z , x<z<y)} (λ (z<z , _) → irrefl refl z<z) {n = n'}
                                (inj₁ n-items-at-most)

                            zy-separation-size-n' : AtMostSize (property-subset-setoid A-setoid (separation z y)) n'
                            zy-separation-size-n' = surjection→surjectionish (bijection→surjection (restrict-collapse A-setoid (separation x y) (separation z y) (λ (z<q , q<y) → <-trans x<z z<q , q<y))) ∘-at-most-size zy-double-separation-size-n' --

                            recursive-call₂ : branch-type z y
                            recursive-call₂ = find-separation-helper {x = z} {y = y} z<y zy-separation-size-n'

                            recursive-call : branch-type x y
                            recursive-call = trans-branch recursive-call₁ recursive-call₂


            descendent→child : IsFinite A-setoid → (x : A) → LocalDescendentsOf x .Setoid.Carrier → ChildrenOf x .Setoid.Carrier
            descendent→child A-finite x (y , y<x) with pop-last (find-separation A-finite y<x)
            ... | z , (y<z , z-child-of-x) = z , z-child-of-x

            descendent→child-count : IsFinite A-setoid → (x : A) → LocalDescendentsOf x .Setoid.Carrier → (children-size : IsFinite (ChildrenOf x)) → children-size .proj₁ >ℕ 0
            descendent→child-count A-finite x descendent (suc-ℕ n' , x-has-n-children) = s≤s z≤n
            descendent→child-count A-finite x (y , y-descendent-of-x) (zero-ℕ , x-has-zero-children) with descendent→child A-finite x (y , y-descendent-of-x)
            ... | z , z-child-of-x = case invert-bijection x-has-zero-children .Bijection.to (z , z-child-of-x) of λ ()

            descendents→children : IsFinite A-setoid → (x : A) → (descendents-size : IsFinite (LocalDescendentsOf x)) → (descendents-size .proj₁ >ℕ 0) → (children-size : IsFinite (ChildrenOf x)) → children-size .proj₁ >ℕ 0
            descendents→children A-finite x (suc-ℕ _ , x-has-m-descendents) (s≤s z≤n) children-size = descendent→child-count A-finite x (x-has-m-descendents .Bijection.to zero-fin) children-size

        no-children-then-last : (Decidable (A-setoid .Setoid._≈_)) → {n : ℕ} → HasSize A-setoid n → (x : A) → HasGlobalPosition x → ¬ (ChildrenOf x) .Setoid.Carrier → IsLocallyNthPlace x (Data.Nat._∸_ n 1)
        no-children-then-last _~?_ {n = zero-ℕ} A-size-n x _ _ = case invert-bijection A-size-n .Bijection.to x of λ ()
        no-children-then-last _~?_ {n = n@(suc-ℕ n')} A-size-n x x-is-global x-has-no-children = x-is-last
            where
                open DescendentToChild using (descendent→child)

                all-ancestors : {y : A} → ¬ x ≈ y → x < y
                all-ancestors {y} x≉y with x-is-global y
                ... | cmp₁ x<y = x<y
                ... | cmp₂ x≈y = ⊥-elim (x≉y x≈y)
                ... | cmp₃ x>y = case x-has-no-children (descendent→child (n , A-size-n) x (y , x>y)) of λ ()

                all-ancestors-bijection : Bijection (property-subset-setoid A-setoid (λ y → ¬ x ≈ y)) (LocalAncestorsOf x)
                all-ancestors-bijection = record {
                    to = to;
                    cong = id;
                    bijective = id , to-surj
                    }
                    where
                        s₁ = property-subset-setoid A-setoid (λ y → ¬ x ≈ y)
                        s₂ = LocalAncestorsOf x
                        B = s₁ .Setoid.Carrier
                        C = s₂ .Setoid.Carrier
                        _~₁_ = s₁ .Setoid._≈_
                        _~₂_ = s₂ .Setoid._≈_

                        to : B → C
                        to (x , x≉y) = x , all-ancestors x≉y

                        to-surj : Surjective _~₁_ _~₂_ to
                        to-surj (y , x<y) = (y , λ x~y → irrefl x~y x<y) , λ z~y → z~y

                x-is-last : IsLocallyNthPlace x n'
                x-is-last = all-ancestors-bijection ∘-bijection n∸1-unequal-items A-setoid _~?_ {n = n'} A-size-n x

        if-global-then-children : (Decidable (A-setoid .Setoid._≈_)) → {n : ℕ} → HasSize A-setoid n → (x : A) → HasGlobalPosition x → ¬ IsLocallyNthPlace x (Data.Nat._∸_ n 1) → (ChildrenOf x) .Setoid.Carrier
        if-global-then-children _~?_ {n = zero-ℕ} A-size-n x _ _ = case invert-bijection A-size-n .Bijection.to x of λ ()
        if-global-then-children _~?_ {n = n@(suc-ℕ n')} A-size-n x x-is-global x-not-last-place with count-children (n , A-size-n) x
        ... | (suc-ℕ m' , x-has-m-children) = x-has-m-children .Bijection.to zero-fin
        ... | (zero-ℕ , x-has-zero-children) = ⊥-elim (x-not-last-place (no-children-then-last _~?_ A-size-n x x-is-global ((λ ()) ∘ invert-bijection x-has-zero-children .Bijection.to)))
