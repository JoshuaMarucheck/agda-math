open import Level using (Level; _⊔_) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary using (Setoid; Rel)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)



module Plasmaduck.Function.Properties where


open Setoid using (Carrier)

variable
    a b c ℓ₁ ℓ₂ ℓ₃ : Level

module GenericFunction
    {A : Set a} {B : Set b}
    (_≈A_ : Rel A ℓ₁) (_≈B_ : Rel B ℓ₂) (f : A → B) where

    ExplicitlyCongruent : Set _
    ExplicitlyCongruent = ∀ (x₁ x₂ : A) → x₁ ≈A x₂ → (f x₁) ≈B (f x₂)

    EssentiallyIdentical : (g : A → B) → Set _
    EssentiallyIdentical g = ∀ {x₁ x₂ : A} → x₁ ≈A x₂ → (f x₁) ≈B (g x₂)

    LeftInverse : (g : B → A) → Set (a ⊔ ℓ₁)
    LeftInverse g = ∀ {x : A} → g (f x) ≈A x

    RightInverse : (g : B → A) → Set (b ⊔ ℓ₂)
    RightInverse g = ∀ {y : B} → f (g y) ≈B y

    SidedInverse = RightInverse

    BothInverse : (g : B → A) → Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂)
    BothInverse g = LeftInverse g × RightInverse g

open GenericFunction public

module GenericOperator
    {A : Set a} {B : Set b} {C : Set c}
    (_≈A_ : Rel A ℓ₁) (_≈B_ : Rel B ℓ₂) (_≈C_ : Rel C ℓ₃) (_∙_ : A → B → C) where

    Congruent₂ : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
    Congruent₂ = ∀ {x₁ x₂ : A} {y₁ y₂ : B} → x₁ ≈A x₂ → y₁ ≈B y₂ → (x₁ ∙ y₁) ≈C (x₂ ∙ y₂)

    RightCongruent : Set (a ⊔ b ⊔ ℓ₂ ⊔ ℓ₃)
    RightCongruent = ∀ {x : A} {y₁ y₂ : B} → y₁ ≈B y₂ → (x ∙ y₁) ≈C (x ∙ y₂)

    LeftCongruent : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₃)
    LeftCongruent = ∀ {x₁ x₂ : A} {y : B} → x₁ ≈A x₂ → (x₁ ∙ y) ≈C (x₂ ∙ y)

    EssentiallyIdentical₂ : (_*_ : A → B → C) → Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
    EssentiallyIdentical₂ _*_ = ∀ {x₁ x₂ : A} {y₁ y₂ : B} → x₁ ≈A x₂ → y₁ ≈B y₂ → (x₁ ∙ y₁) ≈C (x₂ * y₂)

open GenericOperator public


module _ {a ℓ : Level} (A-setoid : Setoid a ℓ) where
    open Setoid A-setoid using (_≈_) renaming (Carrier to A)

    module UnaryFunction (f : A → A) where
        Idempotent : Set (a ⊔ ℓ)
        Idempotent = ∀ (x : A) → f (f x) ≈ f x
    open UnaryFunction public

    module SingleOperator (_∙_ : A → A → A) where
        Associative : Set (a ⊔ ℓ)
        Associative = ∀ {x y z} → x ∙ (y ∙ z) ≈ (x ∙ y) ∙ z

        Commutative : Set (a ⊔ ℓ)
        Commutative = ∀ {x y} → x ∙ y ≈ y ∙ x

        private
            assoc-middle-left : Associative → LeftCongruent _≈_ _≈_ _≈_ _∙_ → ∀ {w x y z} → (w ∙ x) ∙ (y ∙ z) ≈ (w ∙ (x ∙ y)) ∙ z
            assoc-middle-left assoc left-cong {w} {x} {y} {z} = begin
                (w ∙ x) ∙ (y ∙ z)   ≈⟨ assoc ⟩
                ((w ∙ x) ∙ y) ∙ z   ≈⟨ left-cong {y = z} (sym assoc) ⟩
                (w ∙ (x ∙ y)) ∙ z   ∎
                where
                    open import Relation.Binary.Reasoning.Setoid A-setoid
                    open Setoid A-setoid using (refl; sym; trans)

            assoc-middle-right : Associative → RightCongruent _≈_ _≈_ _≈_ _∙_ → ∀ {w x y z} → (w ∙ x) ∙ (y ∙ z) ≈ (w ∙ (x ∙ y)) ∙ z
            assoc-middle-right assoc right-cong {w} {x} {y} {z} = begin
                (w ∙ x) ∙ (y ∙ z)   ≈⟨ sym assoc ⟩
                w ∙ (x ∙ (y ∙ z))   ≈⟨ right-cong {w} assoc ⟩
                w ∙ ((x ∙ y) ∙ z)   ≈⟨ assoc ⟩
                (w ∙ (x ∙ y)) ∙ z   ∎
                where
                    open import Relation.Binary.Reasoning.Setoid A-setoid
                    open Setoid A-setoid using (refl; sym; trans)

        assoc-middle :
            Associative →
            LeftCongruent _≈_ _≈_ _≈_ _∙_ ⊎ RightCongruent _≈_ _≈_ _≈_ _∙_ →
            ∀ {w x y z} → (w ∙ x) ∙ (y ∙ z) ≈ (w ∙ (x ∙ y)) ∙ z
        assoc-middle assoc (inj₁ left-cong) = assoc-middle-left assoc left-cong
        assoc-middle assoc (inj₂ right-cong) = assoc-middle-right assoc right-cong

        exchange-middle : Associative → Commutative → Congruent₂ _≈_ _≈_ _≈_ _∙_ → ∀ {w x y z} → (w ∙ x) ∙ (y ∙ z) ≈ (w ∙ y) ∙ (x ∙ z)
        exchange-middle assoc comm cong {w} {x} {y} {z} = begin
            (w ∙ x) ∙ (y ∙ z) ≈⟨ assoc-middle assoc (inj₁ λ x₁≈x₂ → cong x₁≈x₂ refl) ⟩
            (w ∙ (x ∙ y)) ∙ z ≈⟨ cong (cong refl comm) refl ⟩
            (w ∙ (y ∙ x)) ∙ z ≈⟨ sym (assoc-middle assoc (inj₁ λ x₁≈x₂ → cong x₁≈x₂ refl)) ⟩
            (w ∙ y) ∙ (x ∙ z) ∎
            where
                open import Relation.Binary.Reasoning.Setoid A-setoid
                open Setoid A-setoid using (refl; sym; trans)


        LeftIdentity : A → Set (a ⊔ ℓ)
        LeftIdentity e = ∀ {x} → e ∙ x ≈ x

        RightIdentity : A → Set (a ⊔ ℓ)
        RightIdentity e = ∀ {x} → x ∙ e ≈ x

        Identity : A → Set (a ⊔ ℓ)
        Identity e = LeftIdentity e × RightIdentity e


        LeftAbsorber : A → Set (a ⊔ ℓ)
        LeftAbsorber z = ∀ {x} → z ∙ x ≈ z

        RightAbsorber : A → Set (a ⊔ ℓ)
        RightAbsorber z = ∀ {x} → x ∙ z ≈ z

        Absorber : A → Set (a ⊔ ℓ)
        Absorber z = LeftAbsorber z × RightAbsorber z


        LeftCancellative : Set (a ⊔ ℓ)
        LeftCancellative = ∀ {x y z} → x ∙ y ≈ x ∙ z → y ≈ z

        RightCancellative : Set (a ⊔ ℓ)
        RightCancellative = ∀ {x y z} → x ∙ z ≈ y ∙ z → x ≈ y

        Cancellative : Set (a ⊔ ℓ)
        Cancellative = LeftCancellative × RightCancellative
    open SingleOperator public

    module DoubleOperator (_*_ : A → A → A) (_+_ : A → A → A) where
        LeftDistributive : Set (a ⊔ ℓ)
        LeftDistributive = ∀ {x y z} → x * (y + z) ≈ (x * y) + (x * z)

        RightDistributive : Set (a ⊔ ℓ)
        RightDistributive = ∀ {x y z} → (x + y) * z ≈ (x * z) + (y * z)

        Distributive : Set (a ⊔ ℓ)
        Distributive = LeftDistributive × RightDistributive
    open DoubleOperator public

    module FunctionAndOperator (f : A → A) (_∙_ : A → A → A) where
        DistributiveFunction : Set (a ⊔ ℓ)
        DistributiveFunction = ∀ {x y} → f (x ∙ y) ≈ f x ∙ f y
    open FunctionAndOperator public
