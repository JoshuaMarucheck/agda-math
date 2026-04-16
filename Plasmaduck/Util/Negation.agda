open import Level using (Level; _⊔_; Lift; lift; Setω) renaming (suc to lsuc; zero to lzero)
open import Relation.Nullary.Negation using (¬_)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary.Decidable using (Dec; yes; no)


module Plasmaduck.Util.Negation where

variable
    a : Level
    A : Set a

¬¬-lift : A → ¬ ¬ A
¬¬-lift x ¬x = ¬x x

module DependentInversion where
    variable
        b : Level
        B : A → Set b

    -- Note this makes no promises that A is inhabited.
    invert-product : ¬ (Σ A B) → ∀ x → ¬ B x
    invert-product f = λ x' Bx' → f (x' , Bx')

    invert-product₂ : Dec A → ¬ (Σ A B) → ¬ A ⊎ ¬ (∀ x → B x)
    invert-product₂ (yes x) no-prod = inj₂ λ b-proof → no-prod (x , b-proof x)
    invert-product₂ (no ¬A) _ = inj₁ ¬A

    -- invert-product' : ¬ A ⊎ ¬ B → ¬ (Σ A B)
    -- invert-product' (inj₁ ¬A) (x , y) = ¬A x
    -- invert-product' (inj₂ ¬B) (x , y) = ¬B y

    -- invert-sum : ¬ (A ⊎ B) → ¬ A × ¬ B
    -- invert-sum f = (λ z → f (inj₁ z)) , λ z → f (inj₂ z)

    -- invert-sum' : ¬ A × ¬ B → ¬ (A ⊎ B)
    -- invert-sum' (¬A , ¬B) (inj₁ x) = ¬A x
    -- invert-sum' (¬A , ¬B) (inj₂ y) = ¬B y

module SimpleInversion where
    variable
        b : Level
        B : Set b

    invert-product : Dec A → ¬ (A × B) → ¬ A ⊎ ¬ B
    invert-product (yes x) f = inj₂ λ y → f (x , y)
    invert-product (no ¬A) _ = inj₁ ¬A

    invert-product' : ¬ A × ¬ B → ¬ (A ⊎ B)
    invert-product' (¬A , ¬B) (inj₁ x) = ¬A x
    invert-product' (¬A , ¬B) (inj₂ y) = ¬B y

    invert-sum : ¬ (A ⊎ B) → ¬ A × ¬ B
    invert-sum f = (λ z → f (inj₁ z)) , λ z → f (inj₂ z)

    invert-sum' : ¬ A ⊎ ¬ B → ¬ (A × B)
    invert-sum' (inj₁ ¬A) (x , y) = ¬A x
    invert-sum' (inj₂ ¬B) (x , y) = ¬B y

open SimpleInversion public
