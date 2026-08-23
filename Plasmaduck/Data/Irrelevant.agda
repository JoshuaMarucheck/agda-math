open import Level using (Level; _⊔_)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Function using (_∘_)

open import Plasmaduck.Data.Squash using (Squash; squash)



module Plasmaduck.Data.Irrelevant where

variable
    a b c d α β : Level


-- for contexts where B and D are irrelevant proof data about A and C
IrrelevantFunctionPair :
    (A : Set a)
    (B : A → Set b)
    (C : Set c)
    (D : C → Set d) →
    Set (a ⊔ b ⊔ c ⊔ d)
IrrelevantFunctionPair A B C D = Σ ((x : A) → .(B x) → C) λ f → Squash ((x : A) → .(y : B x) → D (f x y))

-- non-dependent functions with some sort of irrelevant output
_∘'_ :
    {A : Set a}
    {B : A → Set b}
    {C : Set c}
    {D : C → Set d}
    {E : Set α}
    {F : E → Set β} →
    (g : IrrelevantFunctionPair C D E F) →
    (f : IrrelevantFunctionPair A B C D) →
    IrrelevantFunctionPair A B E F
_∘'_ (g , squash g-pf) (f , squash f-pf) = (λ x x-pf → g (f x x-pf) (f-pf x x-pf)) , squash λ x x-pf → g-pf (f x x-pf) (f-pf x x-pf)
