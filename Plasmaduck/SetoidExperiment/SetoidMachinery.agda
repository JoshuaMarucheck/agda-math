open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary using (Setoid; Rel; IsEquivalence)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Function using (Congruent)

open import Plasmaduck.Function using (_⇔_; ⇔-isEquivalence)
open import Plasmaduck.Relation.Equivalence using (≡-isEquivalence)


module Plasmaduck.SetoidExperiment.SetoidMachinery where

open Setoid using (Carrier; _≈_; isEquivalence)

variable
    a b c d e f ℓ ℓ₁ ℓ₂ : Level

SetoidRespectsType : (S₁ : Setoid a b) (S₂ : Setoid c d) (f : S₁ .Carrier → S₂ .Carrier) → Set (a ⊔ b ⊔ d)
SetoidRespectsType S₁ S₂ func = ∀ {x y : S₁ .Carrier} (x≈y : S₁ ._≈_ x y) → S₂ ._≈_ (func x) (func y)


record SetoidFunction (S₁ : Setoid a b) (S₂ : Setoid c d) : Set (a ⊔ b ⊔ c ⊔ d) where
    field
        func : S₁ .Carrier → S₂ .Carrier
        respects : SetoidRespectsType S₁ S₂ func

SetoidFunctionEquality : (S₁ : Setoid a b) (S₂ : Setoid c d) → Rel (SetoidFunction S₁ S₂) (a ⊔ b ⊔ d)
SetoidFunctionEquality S₁ S₂ = λ f g → ∀ {x y : S₁ .Carrier} → (S₁ ._≈_ x y) → S₂ ._≈_ (f .SetoidFunction.func x) (g .SetoidFunction.func y)

SetoidFunctionSetoid : (S₁ : Setoid a b) (S₂ : Setoid c d) → Setoid (a ⊔ b ⊔ c ⊔ d) (a ⊔ b ⊔ d)
SetoidFunctionSetoid S₁ S₂ = record
    { Carrier = SetoidFunction S₁ S₂
    ; _≈_ = SetoidFunctionEquality S₁ S₂
    ; isEquivalence = record
        { refl = λ {f} x≈y → f .respects x≈y
        ; sym = λ {f} {g} f≈g {x} {y} x≈y → S₂ .isEquivalence .sym (f≈g (S₁ .isEquivalence .sym x≈y))
        ; trans = λ {f} {g} {h} f≈g g≈h {x} {y} x≈y → S₂ .isEquivalence .trans (f≈g (S₁ .isEquivalence .refl)) (g≈h x≈y)
        }
    }
    where
        open IsEquivalence
        open SetoidFunction

PropSetoid : (a : Level) → Setoid (lsuc a) a
PropSetoid a = record
    { Carrier = Set a
    ; _≈_ = _⇔_
    ; isEquivalence = ⇔-isEquivalence
    }

-- PredicateSetoid : (ℓ : Level) → Setoid a b → Setoid (a ⊔ b ⊔ lsuc ℓ) (a ⊔ b ⊔ ℓ)
-- PredicateSetoid ℓ S = SetoidFunctionSetoid S (PropSetoid ℓ)

discrete-setoid : Set a → Setoid a a
discrete-setoid S = record
    { Carrier = S
    ; _≈_ = _≡_
    ; isEquivalence = ≡-isEquivalence
    }

indiscrete-setoid : Set a → Setoid a lzero
indiscrete-setoid S = record
    { Carrier = S
    ; _≈_ = λ _ _ → ⊤
    ; isEquivalence = record
        { refl = λ {x} → tt
        ; sym = λ {x} {y} _ → tt
        ; trans = λ {i} {j} {k} _ _ → tt
        }
    }


data ⊎-rel (setoid : Setoid c ℓ) (setoid₂ : Setoid d ℓ₂) : Rel (setoid .Carrier ⊎ setoid₂ .Carrier) (c ⊔ ℓ ⊔ d ⊔ ℓ₂) where
    rel₁ : {x y : setoid .Carrier} → setoid ._≈_ x y → ⊎-rel setoid setoid₂ (inj₁ x) (inj₁ y)
    rel₂ : {x y : setoid₂ .Carrier} → setoid₂ ._≈_ x y → ⊎-rel setoid setoid₂ (inj₂ x) (inj₂ y)


⊎-setoid : (setoid : Setoid c ℓ) (setoid₂ : Setoid d ℓ₂) → Setoid (c ⊔ d) (c ⊔ ℓ ⊔ d ⊔ ℓ₂)
⊎-setoid {ℓ = ℓ} {ℓ₂ = ℓ₂} setoid setoid₂ = record {
    Carrier = setoid .Carrier ⊎ setoid₂ .Carrier;
    _≈_ = ⊎-rel setoid setoid₂;
    isEquivalence = record {
        refl = λ { {inj₁ x} → rel₁ (setoid .Setoid.refl); {inj₂ x} → rel₂ (setoid₂ .Setoid.refl)};
        sym = λ {
            {inj₁ x} {inj₁ y} (rel₁ x≈₁y) → rel₁ (setoid .Setoid.sym x≈₁y);
            {inj₂ x} {inj₂ y} (rel₂ x≈₂y) → rel₂ (setoid₂ .Setoid.sym x≈₂y)
            };
        trans = λ {
            {inj₁ x} {inj₁ y} {inj₁ z} (rel₁ x≈₁y) (rel₁ y≈₁z) → rel₁ (setoid .Setoid.trans x≈₁y y≈₁z);
            {inj₂ x} {inj₂ y} {inj₂ z} (rel₂ x≈₂y) (rel₂ y≈₂z) → rel₂ (setoid₂ .Setoid.trans x≈₂y y≈₂z)
            }
        }
    }


×-rel : (setoid : Setoid c ℓ) (setoid₂ : Setoid d ℓ₂) → Rel (setoid .Carrier × setoid₂ .Carrier) (ℓ ⊔ ℓ₂)
×-rel setoid setoid₂ (x₁ , y₁) (x₂ , y₂) = (setoid ._≈_ x₁ x₂) × (setoid₂ ._≈_ y₁ y₂)

×-setoid : (setoid : Setoid c ℓ) (setoid₂ : Setoid d ℓ₂) → Setoid (c ⊔ d) (ℓ ⊔ ℓ₂)
×-setoid {ℓ = ℓ} {ℓ₂ = ℓ₂} setoid setoid₂ = record {
    Carrier = setoid .Carrier × setoid₂ .Carrier;
    _≈_ = ×-rel setoid setoid₂;
    isEquivalence = record {
        refl = λ {x} →
            IsEquivalence.refl (isEquivalence setoid) ,
            IsEquivalence.refl (isEquivalence setoid₂);
        sym = λ {x} {y} z →
            IsEquivalence.sym (isEquivalence setoid) (z .proj₁) ,
            IsEquivalence.sym (isEquivalence setoid₂) (z .proj₂);
        trans = λ {i} {j} {k} z z₁ →
            IsEquivalence.trans (isEquivalence setoid) (z .proj₁) (z₁ .proj₁) ,
            IsEquivalence.trans (isEquivalence setoid₂) (z .proj₂) (z₁ .proj₂)
    }
    }
