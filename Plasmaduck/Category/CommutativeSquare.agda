open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Relation.Binary.PropositionalEquality using (_≡_) renaming (refl to ≡-refl)
open import Relation.Binary using (Setoid; Rel; IsEquivalence)
open import Function using (Congruent)
open import Data.Product using (_×_; _,_)

open import Plasmaduck.SetoidExperiment.SetoidMachinery using (SetoidFunction₂)
open import Plasmaduck.Category.Category using (RawCategory; Category; Functor; opposite-category; opposite-functor; IsSidedInverse)
open import Plasmaduck.Util.Case using (case_of_)
open import Plasmaduck.Category.Functor.SimpleFunctors using (id-functor)
open import Plasmaduck.Category.Functor.Properties using (FunctorSetoid; Functor-compose-func)
open import Plasmaduck.Function.Properties using (ExplicitlyCongruent; Congruent₂)



module Plasmaduck.Category.CommutativeSquare where

variable
    a b c α β γ ℓ₁ ℓ₂ ℓ₃ : Level


module _ (𝔸 : Category a b c) where
    open Category 𝔸 using (Object; Morphism; _∘_; _~_; assoc; ∘-respects; ~-refl; ~-sym; ~-trans)
    {-
        A   B   C

        X   Y   Z
    -}
    -- If you're using this to split a proof, it may be useful to give input "by",
    -- since it can't just intuit that from the formulas it's relating.
    --
    -- Also note that if you need to swap the equality, you can always use the opposite category. (Or you can use ~-sym.)
    commutative-square-compose : {A B C X Y Z : Object} →
        {ab : Morphism A B} →
        {bc : Morphism B C} →
        {xy : Morphism X Y} →
        {yz : Morphism Y Z} →
        {ax : Morphism A X} →
        {by : Morphism B Y} →
        {cz : Morphism C Z} →
        (xy ∘ ax ~ by ∘ ab) →
        (yz ∘ by ~ cz ∘ bc) →
        ((yz ∘ xy) ∘ ax ~ cz ∘ (bc ∘ ab))
    commutative-square-compose {A = A} {Z = Z} {ab = ab} {bc} {xy} {yz} {ax} {by} {cz} commutes₁ commutes₂ = begin
        (yz ∘ xy) ∘ ax ≈⟨ assoc yz xy ax ⟩
        yz ∘ (xy ∘ ax) ≈⟨ ∘-respects ~-refl commutes₁ ⟩
        yz ∘ (by ∘ ab) ≈⟨ ~-sym (assoc yz by ab) ⟩
        (yz ∘ by) ∘ ab ≈⟨ ∘-respects commutes₂ ~-refl ⟩
        (cz ∘ bc) ∘ ab ≈⟨ assoc cz bc ab ⟩
        cz ∘ (bc ∘ ab) ∎
        where open import Relation.Binary.Reasoning.Setoid (Category.Morphism' 𝔸 A Z)
