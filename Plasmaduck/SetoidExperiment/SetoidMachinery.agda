open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary using (Setoid; Rel; IsEquivalence)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; inspect; cong; Reveal_·_is_; [_])

open import Plasmaduck.Function using (_⇔_; ⇔-isEquivalence)
open import Plasmaduck.Relation.Equivalence using (≡-isEquivalence)


module Plasmaduck.SetoidExperiment.SetoidMachinery where

open Setoid using (Carrier; _≈_; isEquivalence)

variable
    a b c d e f : Level

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
