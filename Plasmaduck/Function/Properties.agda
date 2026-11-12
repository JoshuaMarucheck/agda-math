open import Level using (Level; _⊔_) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary using (Setoid; Rel)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
import Algebra.Definitions as Algebra



module Plasmaduck.Function.Properties where

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
    LeftInverse g = ∀ (x : A) → g (f x) ≈A x

    RightInverse : (g : B → A) → Set (b ⊔ ℓ₂)
    RightInverse g = ∀ (y : B) → f (g y) ≈B y

    SidedInverse = RightInverse

    BothInverse : (g : B → A) → Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂)
    BothInverse g = LeftInverse g × RightInverse g

module GenericOperator
    {A : Set a} {B : Set b} {C : Set c}
    (_≈A_ : Rel A ℓ₁) (_≈B_ : Rel B ℓ₂) (_≈C_ : Rel C ℓ₃) (_∙_ : A → B → C) where

    Congruent₂ = Relation.Binary.Monotonic₂ _≈A_ _≈B_ _≈C_ _∙_

    RightCongruent : Set (a ⊔ b ⊔ ℓ₂ ⊔ ℓ₃)
    RightCongruent = ∀ (x : A) {y₁ y₂ : B} → y₁ ≈B y₂ → (x ∙ y₁) ≈C (x ∙ y₂)

    LeftCongruent : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₃)
    LeftCongruent = ∀ (y : B) {x₁ x₂ : A} → x₁ ≈A x₂ → (x₁ ∙ y) ≈C (x₂ ∙ y)

    EssentiallyIdentical₂ : (_*_ : A → B → C) → Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)
    EssentiallyIdentical₂ _*_ = ∀ {x₁ x₂ : A} {y₁ y₂ : B} → x₁ ≈A x₂ → y₁ ≈B y₂ → (x₁ ∙ y₁) ≈C (x₂ * y₂)

module WithEquality {a ℓ : Level} {A : Set a} (eq : Rel A ℓ) where
    infix 2 _≈_
    private
        _≈_ = eq

    open import Algebra.Definitions _≈_ public using (_DistributesOverˡ_; _DistributesOverʳ_; _DistributesOver_)

    module UnaryFunction (f : A → A) where
        Idempotent : Set (a ⊔ ℓ)
        Idempotent = ∀ (x : A) → f (f x) ≈ f x

        Involutive : Set (a ⊔ ℓ)
        Involutive = Algebra.Involutive _≈_ f

    module SingleOperator (_∙_ : A → A → A) where
        module _ (x : A) where
            LeftIdentity = Algebra.LeftIdentity _≈_ x _∙_
            RightIdentity = Algebra.RightIdentity _≈_ x _∙_
            Identity = Algebra.Identity _≈_ x _∙_

        LeftCancellative = Algebra.LeftCancellative _≈_ _∙_
        RightCancellative = Algebra.RightCancellative _≈_ _∙_
        Cancellative = Algebra.Cancellative _≈_ _∙_

        Associative = Algebra.Associative _≈_ _∙_
        Commutative = Algebra.Commutative _≈_ _∙_

        LeftAbsorber : A → Set (a ⊔ ℓ)
        LeftAbsorber z = ∀ x → z ∙ x ≈ z

        RightAbsorber : A → Set (a ⊔ ℓ)
        RightAbsorber z = ∀ x → x ∙ z ≈ z

        Absorber : A → Set (a ⊔ ℓ)
        Absorber z = LeftAbsorber z × RightAbsorber z

    module FunctionAndOperator (f : A → A) (_∙_ : A → A → A) where
        DistributiveFunction : Set (a ⊔ ℓ)
        DistributiveFunction = ∀ x y → f (x ∙ y) ≈ f x ∙ f y

    open UnaryFunction public
    open SingleOperator public
    open FunctionAndOperator public

open GenericFunction public
open GenericOperator public
open WithEquality public

module _ {a ℓ : Level} (A-setoid : Setoid a ℓ) where
    open Setoid A-setoid using () renaming (Carrier to A)

    module Helpers (_∙_ : A → A → A) where
        private
            infix 2 _≈_
            _≈_ = A-setoid .Setoid._≈_

        private
            assoc-middle-left : Associative _≈_ _∙_ → LeftCongruent _≈_ _≈_ _≈_ _∙_ → ∀ w x y z → (w ∙ x) ∙ (y ∙ z) ≈ (w ∙ (x ∙ y)) ∙ z
            assoc-middle-left assoc left-cong w x y z = begin
                (w ∙ x) ∙ (y ∙ z)   ≈⟨ sym (assoc (w ∙ x) y z) ⟩
                ((w ∙ x) ∙ y) ∙ z   ≈⟨ left-cong z (assoc w x y) ⟩
                (w ∙ (x ∙ y)) ∙ z   ∎
                where
                    open import Relation.Binary.Reasoning.Setoid A-setoid
                    open Setoid A-setoid using (refl; sym; trans)

            assoc-middle-right : Associative _≈_ _∙_ → RightCongruent _≈_ _≈_ _≈_ _∙_ → ∀ w x y z → (w ∙ x) ∙ (y ∙ z) ≈ (w ∙ (x ∙ y)) ∙ z
            assoc-middle-right assoc right-cong w x y z = begin
                (w ∙ x) ∙ (y ∙ z)   ≈⟨ assoc _ _ _ ⟩
                w ∙ (x ∙ (y ∙ z))   ≈⟨ right-cong w (sym (assoc _ _ _)) ⟩
                w ∙ ((x ∙ y) ∙ z)   ≈⟨ sym (assoc _ _ _) ⟩
                (w ∙ (x ∙ y)) ∙ z   ∎
                where
                    open import Relation.Binary.Reasoning.Setoid A-setoid
                    open Setoid A-setoid using (refl; sym; trans)

        assoc-middle :
            Associative _≈_ _∙_ →
            LeftCongruent _≈_ _≈_ _≈_ _∙_ ⊎ RightCongruent _≈_ _≈_ _≈_ _∙_ →
            ∀ w x y z → (w ∙ x) ∙ (y ∙ z) ≈ (w ∙ (x ∙ y)) ∙ z
        assoc-middle assoc (inj₁ left-cong) = assoc-middle-left assoc left-cong
        assoc-middle assoc (inj₂ right-cong) = assoc-middle-right assoc right-cong

        exchange-middle :
            Associative _≈_ _∙_ →
            Commutative _≈_ _∙_ →
            Congruent₂ _≈_ _≈_ _≈_ _∙_ →
            ∀ w x y z → (w ∙ x) ∙ (y ∙ z) ≈ (w ∙ y) ∙ (x ∙ z)
        exchange-middle assoc comm cong w x y z = begin
            (w ∙ x) ∙ (y ∙ z) ≈⟨ assoc-middle assoc (inj₁ λ y x₁≈x₂ → cong x₁≈x₂ refl) w x y z ⟩
            (w ∙ (x ∙ y)) ∙ z ≈⟨ cong (cong refl (comm _ _)) refl ⟩
            (w ∙ (y ∙ x)) ∙ z ≈⟨ sym (assoc-middle assoc (inj₁ λ y x₁≈x₂ → cong x₁≈x₂ refl) w y x z) ⟩
            (w ∙ y) ∙ (x ∙ z) ∎
            where
                open import Relation.Binary.Reasoning.Setoid A-setoid
                open Setoid A-setoid using (refl; sym; trans)
open Helpers public
