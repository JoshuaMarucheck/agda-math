open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary using (Setoid; Rel; IsEquivalence; Reflexive; Symmetric; Transitive)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Function using (Congruent; _∘_; _on_; Bijection)

open import Plasmaduck.Function using (_⇔_; ⇔-isEquivalence)
open import Plasmaduck.Relation.Equivalence using (≡-isEquivalence)
open import Plasmaduck.Function.Properties using (Congruent₂; Idempotent)



module Plasmaduck.SetoidExperiment.SetoidMachinery where

open Setoid using (Carrier; _≈_; isEquivalence)

variable
    a b c d e f ℓ ℓ₁ ℓ₂ ℓ₃ : Level


equality→setoid : {A : Set a} {_~_ : Rel A ℓ} → IsEquivalence _~_ → Setoid a ℓ
equality→setoid {A = A} {_~_} ~-eq = record {
    Carrier = A;
    _≈_ = _~_;
    isEquivalence = ~-eq
    }


record SetoidFunction (S₁ : Setoid a b) (S₂ : Setoid c d) : Set (a ⊔ b ⊔ c ⊔ d) where
    constructor _which-is-cong_
    field
        func : S₁ .Carrier → S₂ .Carrier
        respects : Congruent (S₁ ._≈_) (S₂ ._≈_) func

_∘'_ : {S₁ : Setoid a ℓ₁} {S₂ : Setoid b ℓ₂} {S₃ : Setoid c ℓ₃} →
    SetoidFunction S₂ S₃ → SetoidFunction S₁ S₂ → SetoidFunction S₁ S₃
f ∘' g = record {
    func = (f .SetoidFunction.func) ∘  (g .SetoidFunction.func);
    respects = (f .SetoidFunction.respects) ∘ (g .SetoidFunction.respects)
    }

_←_ : {A : Setoid a ℓ₁} {B : Setoid b ℓ₂} → SetoidFunction A B → A .Carrier → B .Carrier
_←_ f = f .SetoidFunction.func
infixl 100 _←_

SetoidFunctionEquality : (S₁ : Setoid a b) (S₂ : Setoid c d) → Rel (SetoidFunction S₁ S₂) (a ⊔ b ⊔ d)
SetoidFunctionEquality S₁ S₂ = λ f g → ∀ {x y : S₁ .Carrier} → (S₁ ._≈_ x y) → S₂ ._≈_ (f .SetoidFunction.func x) (g .SetoidFunction.func y)

SetoidFunctionEquality-eq : (S₁ : Setoid a b) (S₂ : Setoid c d) → IsEquivalence (SetoidFunctionEquality S₁ S₂)
SetoidFunctionEquality-eq S₁ S₂ = record
    { refl = λ {f} x≈y → f .respects x≈y
    ; sym = λ {f} {g} f≈g {x} {y} x≈y → S₂ .isEquivalence .sym (f≈g (S₁ .isEquivalence .sym x≈y))
    ; trans = λ {f} {g} {h} f≈g g≈h {x} {y} x≈y → S₂ .isEquivalence .trans (f≈g (S₁ .isEquivalence .refl)) (g≈h x≈y)
    }
    where
        open IsEquivalence
        open SetoidFunction

SetoidFunctionSetoid : (S₁ : Setoid a b) (S₂ : Setoid c d) → Setoid (a ⊔ b ⊔ c ⊔ d) (a ⊔ b ⊔ d)
SetoidFunctionSetoid S₁ S₂ = record
    { Carrier = SetoidFunction S₁ S₂
    ; _≈_ = SetoidFunctionEquality S₁ S₂
    ; isEquivalence = SetoidFunctionEquality-eq S₁ S₂
    }

record SetoidFunction₂ (A : Setoid a ℓ₁) (B : Setoid b ℓ₂) (C : Setoid c ℓ₃) : Set (a ⊔ b ⊔ c ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) where
    constructor _which-is-cong₂_
    field
        func : A .Carrier → B .Carrier → C .Carrier
        respects : Congruent₂ (A ._≈_) (B ._≈_) (C ._≈_) func

SetoidFunction₂→SetoidFunction :
    {A : Setoid a ℓ₁} {B : Setoid b ℓ₂} {C : Setoid c ℓ₃} →
    SetoidFunction₂ A B C →
    SetoidFunction A (SetoidFunctionSetoid B C)
SetoidFunction₂→SetoidFunction {A = A} (f which-is-cong₂ cong) = record {
    func = λ x → record {
        func = f x;
        respects = λ y₁~y₂ → cong (A .Setoid.refl) y₁~y₂
        };
    respects = λ x₁~x₂ y₁~y₂ → cong x₁~x₂ y₁~y₂
    }

_←₂_ : {A : Setoid a ℓ₁} {B : Setoid b ℓ₂} {C : Setoid c ℓ₃} → SetoidFunction₂ A B C → A .Carrier → B .Carrier → C .Carrier
_←₂_ f = f .SetoidFunction₂.func
infixl 100 _←₂_

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

from-discrete-cong : {A : Set a} (B : Setoid c ℓ) (f : A → B .Carrier) → Congruent _≡_ (B ._≈_) f
from-discrete-cong {A} B f {x} {y} x≡y rewrite x≡y = B .Setoid.refl

into-indiscrete-cong : (A : Setoid c ℓ) {B : Set b} (f : A .Carrier → B) → Congruent (A ._≈_) (indiscrete-setoid B ._≈_) f
into-indiscrete-cong A {B} f {x} {y} _ = tt

property-subset-setoid : (A : Setoid a ℓ) → (P : A .Carrier → Set ℓ₂) → Setoid (a ⊔ ℓ₂) ℓ
property-subset-setoid A P = record {
    Carrier = Σ (A .Carrier) P;
    _≈_ = λ x y → A ._≈_ (x .proj₁) (y .proj₁);
    isEquivalence = record {
        refl = A .isEquivalence .refl;
        sym = A .isEquivalence .sym;
        trans = A .isEquivalence .trans
        }
    }
    where
        open IsEquivalence



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


data maybe-rel (setoid : Setoid c ℓ) : Rel (Maybe (setoid .Carrier)) (c ⊔ ℓ) where
    maybe-rel-nothing : maybe-rel setoid nothing nothing
    maybe-rel-just : {x y : setoid .Carrier} → (setoid ._≈_ x y) → maybe-rel setoid (just x) (just y)

maybe-setoid : (setoid : Setoid c ℓ) → Setoid c (c ⊔ ℓ)
maybe-setoid setoid = record {
    Carrier = Maybe (setoid .Carrier);
    _≈_ = maybe-rel setoid;
    isEquivalence = record {
        refl = λ { {nothing} → maybe-rel-nothing; {just x} → maybe-rel-just (setoid .Setoid.refl)};
        sym = λ {
            {nothing} {nothing} maybe-rel-nothing → maybe-rel-nothing;
            {just x} {just y} (maybe-rel-just x≈₂y) → maybe-rel-just (setoid .Setoid.sym x≈₂y)
            };
        trans = λ {
            {nothing} {nothing} {nothing} maybe-rel-nothing maybe-rel-nothing → maybe-rel-nothing;
            {just x} {just y} {just z} (maybe-rel-just x≈₂y) (maybe-rel-just y≈₂z) → maybe-rel-just (setoid .Setoid.trans x≈₂y y≈₂z)
            }
        }
    }

IdempotentFunc : {A-setoid : Setoid a ℓ₁} → (f-func : SetoidFunction A-setoid A-setoid) → Set (a ⊔ ℓ₁)
IdempotentFunc {A-setoid = A-setoid} (f which-is-cong _) = Idempotent A-setoid f
