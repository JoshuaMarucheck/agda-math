open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≢_; _≡_; inspect; cong; Reveal_·_is_; [_]) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Function using (_∘_; _on_; flip; id; Injective; Surjective; Bijection; Congruent)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (ℕ; _+_; _∸_; _*_; z≤n; s≤s) renaming (suc to suc-ℕ; zero to zero-ℕ; _≤_ to _≤ℕ_; _<_ to _<ℕ_; _≥_ to _≥ℕ_; _>_ to _>ℕ_)
open import Data.Fin using () renaming (suc to suc-fin; zero to zero-fin)
open import Relation.Binary using (TotalOrder; DecTotalOrder; IsTotalOrder; IsStrictTotalOrder; Reflexive; Irreflexive; Transitive; Trans; Rel; IsEquivalence; _Respects₂_; _Respectsˡ_; _Respectsʳ_; Decidable; IsStrictPartialOrder; Trichotomous; Tri; tri<; tri≈; tri>; Asymmetric; IsDecStrictPartialOrder)
open import Relation.Binary.Bundles using (Setoid)

open import Plasmaduck.Util.Case using (case_of_)
open import Plasmaduck.Relation.OperatorDefs using (SameRel)
open import Plasmaduck.Relation.Equivalence using (≡-isEquivalence; all-respects-≡)
open import Plasmaduck.Relation.Order using (ComparableAt; show-total-order; if-extends-then-same-comparable-at)
open import Plasmaduck.Relation.OrderHelpers using (WeakTri; cmp₁; cmp₂; cmp₃; _Extends_; extends-trans)
open import Plasmaduck.Counting.Counting using (HasSize; IsFinite; AtMostSize; SubsetHasSize; any; all; subset-of-finite-is-upper-bounded; one-equal-item; fin-setoid; ⊎-size-theorem; ×-size-theorem; _∘-at-most-size_; fold; fold-all-theorem; fold-carrying-theorem)
open import Plasmaduck.Relation.Defs using (CongruentRel; CongruentProperty; respects→cong-rel; rel-property) renaming (≈-cong to ≈-cong')
open import Plasmaduck.SetoidExperiment.SetoidMachinery using (property-subset-setoid; from-discrete-cong; ⊎-setoid; rel₁; rel₂; ×-setoid)
open import Plasmaduck.Counting.Strengthening using (subset-of-finite-is-finite; strengthen-core; at-most-size-subset-decr; n∸1-unequal-items)
open import Plasmaduck.Function.Bijection using (invert-bijection; id-bijection; ⊎-bijection; _∘-bijection_)
open import Plasmaduck.Util.Negation using (¬¬-lift)
open import Plasmaduck.Relation.Restriction using (restrict-relation-dec)
open import Plasmaduck.Property.Restriction using (restrict-property; restrict-property-dec; restrict-collapse)
open import Plasmaduck.Function.InjectionSurjection using (bijection→surjection; _∘-surjection_)
open import Plasmaduck.Function.Surjectionish using (surjection→surjectionish)
open import Plasmaduck.Relation.RelationVector using (module RelationTree)
open import Plasmaduck.Relation.Operator using (MinimalExtension; lift-rel; lift-rel-same-rel; IsDecStrictPartialOrder-transferrable)



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

module _ {a ℓ : Level} (A-setoid : Setoid a ℓ) where
    private
        A : Set a
        A = A-setoid .Setoid.Carrier

        _≈_ : Rel A ℓ
        _≈_ = A-setoid .Setoid._≈_

        open IsEquivalence (A-setoid .Setoid.isEquivalence) using (refl; sym; trans; reflexive)

    module _ {ℓ₂ : Level} {_<_ : Rel A ℓ₂} (isDecStrictPartialOrder : IsDecStrictPartialOrder _≈_ _<_) where
        open Helpers isDecStrictPartialOrder hiding (A-setoid; refl; sym; trans)
        module StrictRelExtension {x y : A} (y≰x : ¬ y ≤ x) where
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
                    x≉y = y≰x ∘ ≤-reflexive ∘ sym

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
                It's not necessarily a strict extension. It's strict if x and y are uncomparable under _<_, since we know x <' y.
                (In fact, it is strict if and only if ¬ x < y.)
            -}

            extend-is-minimal : {ℓ₃ : Level} → MinimalExtension A-setoid ℓ₃ (λ _$_ → IsDecStrictPartialOrder _≈_ _$_ × x $ y) _<'_ _<_
            extend-is-minimal _<''_ <''-extends-< (<''-isDecStrictPartialOrder , x<''y) {a} {b} (inj₁ (a≤x , y≤b)) =
                <-≤-trans''-< (≤-<-trans''-< (≤''-extends-≤ a≤x) x<''y)  (≤''-extends-≤ y≤b)
                where
                    open Helpers <''-isDecStrictPartialOrder renaming (_≤_ to _≤''_; ≤-<-trans to ≤-<-trans''-<; <-≤-trans to <-≤-trans''-<)
                    ≤''-extends-≤ : ∀ {x y} → x ≤ y → x ≤'' y
                    ≤''-extends-≤ {x} {y} (inj₁ x≈y) = inj₁ x≈y
                    ≤''-extends-≤ {x} {y} (inj₂ x<y) = inj₂ (<''-extends-< x<y)
            extend-is-minimal _<''_ <''-extends-< (<''-isDecStrictPartialOrder , x<''y) {a} {b} (inj₂ a<b) = <''-extends-< a<b

        module NonstrictRelExtension (x y : A) where
            -- _<'_ extends _<_ by making x and y comparable if they are not under _<_. (It adds the additional comparison x <' y.)
            -- _<'_ is a minimal such relation.

            open StrictRelExtension {x} {y} using () renaming (
                extend-has-properties to strict-extend-has-properties;
                extend-is-minimal to strict-extend-is-minimal
                )

            _<'_ : Rel A (ℓ ⊔ ℓ₂)
            a <' b with y ≤? x
            ... | no _ = (a ≤ x × y ≤ b) ⊎ a < b
            ... | yes _ = Lift ℓ (a < b)

            x<y→no-mod : x < y → SameRel A _<_ _<'_
            x<y→no-mod x<y with y ≤? x
            ... | no _ = inj₂ , λ { (inj₁ (a≤x , y≤b)) → <-≤-trans (≤-<-trans a≤x x<y) y≤b; (inj₂ a<b) → a<b}
            ... | yes y≤x = ⊥-elim (irrefl refl (≤-<-trans y≤x x<y))

            extend-has-properties : IsDecStrictPartialOrder _≈_ _<'_
            extend-has-properties with y ≤? x
            ... | no ¬y≤x = strict-extend-has-properties ¬y≤x
            ... | yes _ = IsDecStrictPartialOrder-transferrable A-setoid (lift-rel-same-rel A-setoid ℓ _<_) isDecStrictPartialOrder

            extend-imposes-x-cmp-y : ComparableAt _≈_ _<'_ x y
            extend-imposes-x-cmp-y with y ≤? x
            ... | no ¬y≤x = cmp₁ (inj₁ (inj₁ refl , inj₁ refl))
            ... | yes (inj₁ y≈x) = cmp₂ (sym y≈x)
            ... | yes (inj₂ y<x) = cmp₃ (lift y<x)

            extend-extends : _<'_ Extends _<_
            extend-extends with y ≤? x
            ... | no _  = inj₂
            ... | yes _ = lift

            extend-is-minimal : {ℓ₃ : Level} → MinimalExtension A-setoid ℓ₃ (λ _$_ → IsDecStrictPartialOrder _≈_ _$_ × x $ y) _<'_ _<_
            extend-is-minimal _<''_ <''-extends-< (<''-isDecStrictPartialOrder , x<''y) {a} {b} with y ≤? x
            ... | no ¬y≤x = strict-extend-is-minimal ¬y≤x _<''_ <''-extends-< (<''-isDecStrictPartialOrder , x<''y)
            ... | yes _ = <''-extends-< ∘ Lift.lower

    private
        rel-domain : (ℓ₂ : Level) → Set (a ⊔ ℓ ⊔ lsuc ℓ₂)
        rel-domain ℓ₂ = Σ (Rel A ℓ₂) (IsDecStrictPartialOrder _≈_)

        lift-rel-domain : {ℓ₂ : Level} (ℓ₃ : Level) → rel-domain ℓ₂ → rel-domain (ℓ₂ ⊔ ℓ₃)
        lift-rel-domain ℓ₃ (_<_ , <-isDecStrictPartialOrder) = lift-rel A-setoid ℓ₃ _<_ , IsDecStrictPartialOrder-transferrable A-setoid (lift-rel-same-rel A-setoid ℓ₃ _<_) <-isDecStrictPartialOrder

    module MassRelExtension
        {ℓ₄ : Level}
        {P : A → Set ℓ₄}
        {n : ℕ}
        (P-size-n : SubsetHasSize A-setoid P n)
        {ℓ₂ : Level}
        {_<_ : Rel A ℓ₂}
        (<-isDecStrictPartialOrder : IsDecStrictPartialOrder _≈_ _<_)
        where
        open NonstrictRelExtension using () renaming (_<'_ to extend-rel; extend-imposes-x-cmp-y to old-extend-imposes-x-cmp-y; extend-has-properties to old-extend-has-properties; extend-extends to old-extend-extends)
        private
            start : rel-domain ℓ₂
            start = (_<_ , <-isDecStrictPartialOrder)

            elements : Setoid _ _
            elements = property-subset-setoid A-setoid P

            elements-pair : Setoid _ _
            elements-pair = ×-setoid elements elements

            ElementPair : Set _
            ElementPair = elements-pair .Setoid.Carrier

            n²-elements : HasSize (×-setoid elements elements) (n * n)
            n²-elements = ×-size-theorem P-size-n P-size-n

            State = Σ (Rel A (ℓ ⊔ ℓ₂)) (IsDecStrictPartialOrder _≈_)

            combine : State → (×-setoid elements elements .Setoid.Carrier) → State
            combine (_#_ , #-dec-strict-partial) ((x , P[x]) , (y , P[y])) = extend-rel #-dec-strict-partial x y , old-extend-has-properties #-dec-strict-partial x y

        extended-rel' : rel-domain (ℓ ⊔ ℓ₂)
        extended-rel' = fold n²-elements {A = State} combine (lift-rel-domain ℓ start)

        _<'_ : Rel A (ℓ ⊔ ℓ₂)
        _<'_ = extended-rel' .proj₁

        extend-dec-strict-partial : IsDecStrictPartialOrder _≈_ _<'_
        extend-dec-strict-partial = extended-rel' .proj₂

        extend-imposes-pairwise-cmp : (((x , _) , (y , _)) : ×-setoid elements elements .Setoid.Carrier) → ComparableAt _≈_ _<'_ x y
        extend-imposes-pairwise-cmp = fold-all-theorem n²-elements combine (lift-rel-domain ℓ start) (λ (_#_ , _) ((x , _) , (y , _)) → ComparableAt _≈_ _#_ x y)
            (λ {
                (_#_ , #-dec-strict-partial) (x₁≈y₁ , x₂≈y₂) (cmp₁ x₁#x₂) → cmp₁ (Helpers.<-cong #-dec-strict-partial x₁≈y₁ x₂≈y₂ x₁#x₂);
                (_#_ , #-dec-strict-partial) (x₁≈y₁ , x₂≈y₂) (cmp₂ x₁≈x₂) → cmp₂ (trans (trans (sym x₁≈y₁) x₁≈x₂) x₂≈y₂);
                (_#_ , #-dec-strict-partial) (x₁≈y₁ , x₂≈y₂) (cmp₃ x₂#x₁) → cmp₃ (Helpers.<-cong #-dec-strict-partial x₂≈y₂ x₁≈y₁ x₂#x₁)
            })
            (λ (_#_ , #-dec-strict-partial) ((x , _) , (y , _)) → old-extend-imposes-x-cmp-y #-dec-strict-partial x y)
            (λ (_#_ , #-dec-strict-partial) pair₁@((x₁ , P[x₁]) , (x₂ , _)) ((y₁ , _) , (y₂ , _)) y₁-cmp-y₂ → if-extends-then-same-comparable-at _≈_ {_#_ = combine (_#_ , #-dec-strict-partial) pair₁ .proj₁} {_<_ = _#_} (old-extend-extends #-dec-strict-partial x₁ x₂) y₁-cmp-y₂)

        extend-extends : _<'_ Extends _<_
        extend-extends = fold-carrying-theorem n²-elements combine (lift-rel-domain ℓ start) (λ (_#_ , _) → _#_ Extends _<_) (λ (_#_ , #-dec-strict-partial) ((x , _) , (y , _)) #-extends-< → extends-trans {j = _#_} (old-extend-extends #-dec-strict-partial x y) #-extends-<) lift

        -- extend-is-minimal : {ℓ₃ : Level} → MinimalExtension A-setoid ℓ₃ (λ _$_ → IsDecStrictPartialOrder _≈_ _$_ × ∀ (((x , _) , (y , _)): ElementPair) → ComparableAt _≈_ _$_ x y) _<'_ _<_
        -- extend-is-minimal _<''_ <''-extends-< (<''-isDecStrictPartialOrder , cmp-on-P) {a} {b} = {!   !}
