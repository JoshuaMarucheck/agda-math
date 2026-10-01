open import Level using (Level)
open import Relation.Binary.PropositionalEquality using (_≡_; _≗_; refl; sym; trans)
open import Relation.Binary using (IsEquivalence; Reflexive; Symmetric; Transitive)


module Plasmaduck.Data.PropositionalEquality where

variable
    a b : Level
    A : Set a
    B : Set b

≡-isEquivalence : IsEquivalence (_≡_ {A = A})
≡-isEquivalence = record {
    refl = λ {x} → refl;
    sym = λ {x} {y} x≡y → sym x≡y;
    trans = λ {x} {y} {z} x≡y y≡z → trans x≡y y≡z
    }

≡-proof-unique : {x y : A} → {p₁ p₂ : x ≡ y} → p₁ ≡ p₂
≡-proof-unique {x = x} {.x} {refl} {refl} = refl

module ≗-Properties
    {a : Level} {A : Set a}
    {b : Level} {B : Set b}
    where
    private
        _≗'_ = _≗_ {A = A} {B = B}

    ≗-refl : Reflexive _≗'_
    ≗-refl _ = refl

    ≗-sym : Symmetric _≗'_
    ≗-sym {f} {g} f≗g x = sym (f≗g x)

    ≗-trans : Transitive _≗'_
    ≗-trans {f} {g} {h} f≗g g≗h x = trans (f≗g x) (g≗h x)

    ≗-eq : IsEquivalence _≗'_
    ≗-eq = record {
        refl = ≗-refl;
        sym = ≗-sym;
        trans = ≗-trans
        }

    -- see discrete-function-setoid in setoid-machinery
open ≗-Properties public
