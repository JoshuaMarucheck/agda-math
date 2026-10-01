open import Level using (Level) renaming (zero to lzero; suc to lsuc; _⊔_ to _⊔ℓ_)
open import Relation.Binary using (Rel; Setoid; IsPartialOrder; IsEquivalence)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)

open import Plasmaduck.SetoidExperiment.SetoidMachinery using (SetoidFunction; SetoidFunction₂; _which-is-cong_; _which-is-cong₂_)
open import Plasmaduck.Function.Properties using (Congruent₂)



module Plasmaduck.Algebra.Lattice.Semilattice where

variable
    α β γ : Level


record RawMeetSemilattice (α β γ : Level) : Set (lsuc α ⊔ℓ lsuc β ⊔ℓ lsuc γ) where
    field
        A : Set α
        _≈_ : Rel A β
        _≤_ : Rel A γ
        _⊓_ : A → A → A

    infixl 5 _⊓_
    infix 4 _≈_ _≤_ _≥_

    _≥_ : Rel A γ
    x ≥ y = y ≤ x

    field
        ≤-isPartialOrder : IsPartialOrder _≈_ _≤_
        ⊓-cong : Congruent₂ _≈_ _≈_ _≈_ _⊓_

    open IsPartialOrder ≤-isPartialOrder using (antisym; ≤-respˡ-≈; ≤-respʳ-≈; ≤-resp-≈) renaming (
        reflexive to ≤-reflexive;
        refl to ≤-refl;
        trans to ≤-trans;
        isEquivalence to ≈-isEquivalence;
        isPreorder to ≤-isPreorder
        ) public
    open IsEquivalence ≈-isEquivalence using () renaming (
        reflexive to ≈-reflexive;
        refl to ≈-refl;
        sym to ≈-sym;
        trans to ≈-trans;
        isPartialEquivalence to ≈-isPartialEquivalence
        ) public

    A-setoid : Setoid α β
    A-setoid = record {
        Carrier = A;
        _≈_ = _≈_;
        isEquivalence = ≈-isEquivalence
        }

    ⊓-func : SetoidFunction₂ A-setoid A-setoid A-setoid
    ⊓-func = _⊓_ which-is-cong₂ ⊓-cong

record IsMeetSemilattice (rawSemilattice : RawMeetSemilattice α β γ) : Set (α ⊔ℓ β ⊔ℓ γ) where
    open RawMeetSemilattice rawSemilattice
    field
        ⊓≤₁ : ∀ x y → x ⊓ y ≤ x
        ⊓≤₂ : ∀ x y → x ⊓ y ≤ y
        ⊓-glb : ∀ x y z → x ≤ y → x ≤ z → x ≤ y ⊓ z

    open import Algebra.Definitions _≈_

    ⊓-idem : Idempotent _⊓_
    ⊓-idem x = antisym (⊓≤₁ x x) (⊓-glb x x x ≤-refl ≤-refl)

    ⊓-assoc : Associative _⊓_
    ⊓-assoc x y z = antisym
        (⊓-glb (x ⊓ y ⊓ z) x (y ⊓ z) (≤-trans (⊓≤₁ (x ⊓ y) z) (⊓≤₁ x y)) (⊓-glb (x ⊓ y ⊓ z) y z (≤-trans (⊓≤₁ (x ⊓ y) z) (⊓≤₂ x y)) (⊓≤₂ (x ⊓ y) z)))
        (⊓-glb (x ⊓ (y ⊓ z)) (x ⊓ y) z (⊓-glb (x ⊓ (y ⊓ z)) x y (⊓≤₁ x (y ⊓ z)) (≤-trans (⊓≤₂ x (y ⊓ z)) (⊓≤₁ y z))) (≤-trans (⊓≤₂ x (y ⊓ z)) (⊓≤₂ y z)))

    ⊓-comm : Commutative _⊓_
    ⊓-comm x y = antisym (⊓-glb (x ⊓ y) y x (⊓≤₂ x y) (⊓≤₁ x y)) (⊓-glb (y ⊓ x) x y (⊓≤₂ y x) (⊓≤₁ y x))

    ⊓-selectiveˡ : ∀ x y → x ≤ y → x ⊓ y ≈ x
    ⊓-selectiveˡ x y x≤y = antisym (⊓≤₁ x y) (⊓-glb x x y ≤-refl x≤y)

    ⊓-selectiveʳ : ∀ x y → x ≥ y → x ⊓ y ≈ y
    ⊓-selectiveʳ x y y≤x = antisym (⊓≤₂ x y) (⊓-glb y x y y≤x ≤-refl)

    ⊓-selective : _ × _
    ⊓-selective = ⊓-selectiveˡ , ⊓-selectiveʳ


record MeetSemilattice (α β γ : Level) : Set (lsuc α ⊔ℓ lsuc β ⊔ℓ lsuc γ) where
    field
        rawSemilattice : RawMeetSemilattice α β γ
        isSemilattice : IsMeetSemilattice rawSemilattice

    open RawMeetSemilattice rawSemilattice public
    open IsMeetSemilattice isSemilattice public


-------------------------------
--- With Maximum or Minimum ---
-------------------------------

record HasMaximum (semilattice : MeetSemilattice α β γ) : Set (α ⊔ℓ β ⊔ℓ γ) where
    open MeetSemilattice semilattice
    field
        max : A
        max≥ : ∀ x → max ≥ x

    open import Algebra.Definitions _≈_

    max≤ : ∀ x → max ≤ x → x ≈ max
    max≤ x max≤x = antisym (max≥ x) max≤x

    ⊓-identityˡ : LeftIdentity max _⊓_
    ⊓-identityˡ x = antisym (⊓≤₂ max x) (⊓-glb x max x (max≥ x) ≤-refl)

    ⊓-identityʳ : RightIdentity max _⊓_
    ⊓-identityʳ x = ≈-trans (⊓-comm x max) (⊓-identityˡ x)

    ⊓-identity : Identity max _⊓_
    ⊓-identity = ⊓-identityˡ , ⊓-identityʳ

    ⊓-identity-proj₁ : ∀ x y → x ⊓ y ≈ max → x ≈ max
    ⊓-identity-proj₁ x y x⊓y≈max = max≤ x (≤-trans (≤-reflexive (≈-sym x⊓y≈max)) (⊓≤₁ x y))

    ⊓-identity-proj₂ : ∀ x y → x ⊓ y ≈ max → y ≈ max
    ⊓-identity-proj₂ x y x⊓y≈max = ⊓-identity-proj₁ y x (≈-trans (⊓-comm y x) x⊓y≈max)

record HasMinimum (semilattice : MeetSemilattice α β γ) : Set (α ⊔ℓ β ⊔ℓ γ) where
    open MeetSemilattice semilattice
    field
        min : A
        min≤ : ∀ x → min ≤ x

    open import Algebra.Definitions _≈_

    min≥ : ∀ x → min ≥ x → x ≈ min
    min≥ x x≤min = antisym x≤min (min≤ x)

    ⊓-zeroˡ : LeftZero min _⊓_
    ⊓-zeroˡ x = antisym (⊓≤₁ min x) (min≤ _)

    ⊓-zeroʳ : RightZero min _⊓_
    ⊓-zeroʳ x = antisym (⊓≤₂ x min) (min≤ _)

    ⊓-zero : Zero min _⊓_
    ⊓-zero = ⊓-zeroˡ , ⊓-zeroʳ


record MeetSemilatticeWithExtrema (α β γ : Level) : Set (lsuc α ⊔ℓ lsuc β ⊔ℓ lsuc γ) where
    field
        semilattice : MeetSemilattice α β γ
        hasMax : HasMaximum semilattice
        hasMin : HasMinimum semilattice

    open MeetSemilattice semilattice public
    open HasMaximum hasMax public
    open HasMinimum hasMin public
