open import Level using (Level; _⊔_) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary using (Rel; Decidable; Irreflexive; Reflexive; Transitive; Asymmetric; Trans; IsEquivalence; IsStrictTotalOrder; IsStrictPartialOrder; tri<; tri≈; tri>; _Respects₂_)



module Plasmaduck.Relation.OrderHelpers where

variable
    a b c d ℓ₁ ℓ₂ ℓ₃ : Level
    A : Set a


data WeakTri (A : Set a) (B : Set b) (C : Set c) : Set (a ⊔ b ⊔ c) where
    cmp₁ : (a : A) → WeakTri A B C
    cmp₂ : (b : B) → WeakTri A B C
    cmp₃ : (c : C) → WeakTri A B C

_Extends_ : {A : Set a} → Rel A ℓ₁ → Rel A ℓ₂ → Set (a ⊔ ℓ₁ ⊔ ℓ₂)
_<₂_ Extends _<₁_ = ∀ {x y} → x <₁ y → x <₂ y

extends-trans :  Trans (_Extends_ {ℓ₁ = ℓ₁} {ℓ₂ = ℓ₂} {A = A}) (_Extends_ {ℓ₁ = ℓ₂} {ℓ₂ = ℓ₃} {A = A}) (_Extends_ {ℓ₁ = ℓ₁} {ℓ₂ = ℓ₃} {A = A})
extends-trans 3←2 2←1 x<₁y = 3←2 (2←1 x<₁y)

extends-refl :  {ℓ₁ : Level} → Reflexive (_Extends_ {ℓ₁ = ℓ₁} {ℓ₂ = ℓ₁} {A = A})
extends-refl x<y = x<y
