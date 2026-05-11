open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary using (Setoid; Rel; IsEquivalence; Reflexive; Symmetric; Transitive)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Function using (Congruent; _∘_; _on_)

open import Plasmaduck.SetoidExperiment.SetoidMachinery using (SetoidFunction; IdempotentFunc)



{-
    Defining a setoid via a canonical element function.
    Two elements are equal if they map to the same thing under the function.
-}
module Plasmaduck.SetoidExperiment.CanonicalElement
    {a ℓ : Level}
    (A-setoid : Setoid a ℓ)
    (canonical-element : SetoidFunction A-setoid A-setoid)
    (idempotent : IdempotentFunc canonical-element)
    where

open Setoid using (Carrier; _≈_; isEquivalence)

variable
    b c d e f ℓ₁ ℓ₂ ℓ₃ : Level



{-
    What makes a canonical-element function work?
    The idea is, for every element, pick an element. two elements are equal if they choose the same canonical element.
    This requires:
    - the selection function is idempotent
-}
private
    A = A-setoid .Carrier
    _~~_ = A-setoid ._≈_

    canonize : A → A
    canonize = canonical-element .SetoidFunction.func

    canonize-cong' : Congruent _~~_ _~~_ canonize
    canonize-cong' = canonical-element .SetoidFunction.respects

    open import Relation.Binary.Reasoning.Setoid A-setoid


open import Plasmaduck.SetoidExperiment.On A-setoid canonize using (_~_; on-bijection) renaming (setoid-on to coarse-setoid; is-in-image to IsCanonicalElement) public

canonize-cong : Congruent _~~_ _~_ canonize
canonize-cong {x = x} {y} x~~y = begin
    canonize (canonize x)   ≈⟨ canonize-cong' (canonize-cong' x~~y) ⟩
    canonize (canonize y)   ∎

canonize-cong₂ : Congruent _~_ _~~_ canonize
canonize-cong₂ {x = x} {y} x~~y = begin
    canonize x  ≈⟨ x~~y ⟩
    canonize y  ∎


