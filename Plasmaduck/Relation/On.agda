open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc; zero to lzero)
open import Function using (_on_)
open import Relation.Binary using (Rel; IsEquivalence)



module Plasmaduck.Relation.On where

variable
    a b c ℓ : Level
    A : Set a
    B : Set b

on-preserves-equality : {_≈_ : Rel B ℓ} → IsEquivalence _≈_ → (f : A → B) → IsEquivalence (_≈_ on f)
on-preserves-equality {_≈_ = _≈_} ≈-eq f = record {
    refl = λ {x} → IsEquivalence.refl ≈-eq;
    sym = λ {x} {y} → IsEquivalence.sym ≈-eq;
    trans = λ {i} {j} {k} → IsEquivalence.trans ≈-eq
    }
