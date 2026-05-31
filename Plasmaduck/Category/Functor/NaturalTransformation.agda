open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Relation.Binary.PropositionalEquality using (_≡_) renaming (refl to ≡-refl)
open import Relation.Binary using (Setoid; Rel; IsEquivalence)
open import Function using (Congruent)
open import Data.Product using (_×_; _,_)

open import Plasmaduck.SetoidExperiment.SetoidMachinery using (SetoidFunction₂)
open import Plasmaduck.Category.Category using (RawCategory; Category; RawFunctor; Functor; opposite-category; opposite-functor; IsSidedInverse)
open import Plasmaduck.Util.Case using (case_of_)
open import Plasmaduck.Category.Functor.SimpleFunctors using (id-functor)
open import Plasmaduck.Category.Functor.Properties using (RawFunctorSetoid; FunctorSetoid; Functor-compose-func) renaming (_∘_ to _∘-Functor_; _∘'_ to _∘-RawFunctor_)
open import Plasmaduck.Function.Properties using (ExplicitlyCongruent; Congruent₂)
open import Plasmaduck.Category.CommutativeSquare using (commutative-square-compose)
open import Plasmaduck.Relation.On using (on-preserves-equality)



module Plasmaduck.Category.Functor.NaturalTransformation where

variable
    a b c α β γ ℓ₁ ℓ₂ ℓ₃ l₁ l₂ l₃ : Level


module _ {𝔸 : RawCategory a b c} {𝔹 : RawCategory α β γ} where
    open RawFunctor using (mapₒ; mapₘ)
    open RawCategory 𝔹 using () renaming (_∘_ to _∘₂_; _~_ to _~₂_)

    record RawNaturalTransformation (F G : RawFunctor 𝔸 𝔹) : Set (a ⊔ β) where
        field
            η : (X : RawCategory.Object 𝔸) → RawCategory.Morphism 𝔹 (mapₒ F X) (mapₒ G X)

    record IsNaturalTransformation {F G : RawFunctor 𝔸 𝔹} (ε : RawNaturalTransformation F G) : Set (a ⊔ b ⊔ γ) where
        open RawNaturalTransformation ε
        field
            commutes :
                {X Y : RawCategory.Object 𝔸} (f : RawCategory.Morphism 𝔸 X Y) →
                η Y ∘₂ mapₘ F f ~₂ mapₘ G f ∘₂ η X

    open RawNaturalTransformation

    _≈'_ : {F G : RawFunctor 𝔸 𝔹} (θ φ : RawNaturalTransformation F G) → Set (a ⊔ γ)
    _≈'_ θ φ = ∀ (X : RawCategory.Object 𝔸) → (θ .η X) ~₂ (φ .η X)
    infix 1 _≈'_

    module _ (F G : RawFunctor 𝔸 𝔹) where
        ≈'-eq : IsEquivalence (_≈'_ {F} {G})
        ≈'-eq = record {
            refl = λ {θ} X → RawCategory.~-refl 𝔹;
            sym = λ {θ} {φ} θ~φ X → RawCategory.~-sym 𝔹 (θ~φ X);
            trans = λ {θ} {φ} {ψ} θ~φ φ~ψ X → RawCategory.~-trans 𝔹 (θ~φ X) (φ~ψ X)
            }

        RawNaturalTransformationSetoid : Setoid (a ⊔ β) (a ⊔ γ)
        RawNaturalTransformationSetoid = record {
            Carrier = RawNaturalTransformation F G;
            _≈_ = _≈'_;
            isEquivalence = ≈'-eq
            }

    -- Vertical composition
    module _ {F G H : RawFunctor 𝔸 𝔹} where
        _∘'_ :
            (RawNaturalTransformation G H) →
            (RawNaturalTransformation F G) →
            (RawNaturalTransformation F H)
        _∘'_ θ φ = record {
            η = λ X → (θ .η X) ∘₂ (φ .η X)
            }
        infixr 9 _∘'_

    id' : (F : RawFunctor 𝔸 𝔹) → RawNaturalTransformation F F
    id' F = record {
        η = λ X → RawCategory.id 𝔹 (mapₒ F X)
        }

module _ {𝔸 : Category a b c} {𝔹 : Category α β γ} where
    open Functor using (mapₒ; mapₘ; rawFunctor)
    open Category 𝔹 using (assoc; id-is-left-id; id-is-right-id; ~-refl; ~-sym; ~-trans) renaming (_∘_ to _∘₂_; _~_ to _~₂_)


    record NaturalTransformation (F G : Functor 𝔸 𝔹) : Set (a ⊔ b ⊔ β ⊔ γ) where
        field
            rawNaturalTransformation : RawNaturalTransformation (F .rawFunctor) (G .rawFunctor)
            isNaturalTransformation : IsNaturalTransformation rawNaturalTransformation

        open RawNaturalTransformation rawNaturalTransformation public
        open IsNaturalTransformation isNaturalTransformation public
    open NaturalTransformation

    _≈_ : {F G : Functor 𝔸 𝔹} (θ φ : NaturalTransformation F G) → Set (a ⊔ γ)
    _≈_ = _≈'_ Function.on NaturalTransformation.rawNaturalTransformation
    infix 1 _≈_

    module _ (F G : Functor 𝔸 𝔹) where
        ≈-eq : IsEquivalence (_≈_ {F} {G})
        ≈-eq = on-preserves-equality (≈'-eq (F .rawFunctor) (G .rawFunctor)) NaturalTransformation.rawNaturalTransformation

        NaturalTransformationSetoid : Setoid (a ⊔ b ⊔ β ⊔ γ) (a ⊔ γ)
        NaturalTransformationSetoid = record {
            Carrier = NaturalTransformation F G;
            _≈_ = _≈_;
            isEquivalence = ≈-eq
            }

    -- Vertical composition
    module _ {F G H : Functor 𝔸 𝔹} where
        _∘_ :
            (NaturalTransformation G H) →
            (NaturalTransformation F G) →
            (NaturalTransformation F H)
        _∘_ θ φ = record {
            rawNaturalTransformation = record { η = λ X → (θ .η X) ∘₂ (φ .η X) };
            isNaturalTransformation = record { commutes = λ {X} {Y} f → commutative-square-compose 𝔹 (φ .commutes f) (θ .commutes f) }
            }
            where
                module _ {X Y : Category.Object 𝔹} where
                    open import Relation.Binary.Reasoning.Setoid (Category.Morphism' 𝔹 X Y) public
        infixr 9 _∘_

        ∘-respects : Congruent₂ (_≈_ {G} {H}) (_≈_ {F} {G}) (_≈_ {F} {H}) _∘_
        ∘-respects = λ z z₁ X → Category.∘-respects 𝔹 (z X) (z₁ X)

        compose-func : SetoidFunction₂ (NaturalTransformationSetoid G H) (NaturalTransformationSetoid F G) (NaturalTransformationSetoid F H)
        compose-func = record {
            func = _∘_;
            respects = λ {θ₁} {θ₂} {φ₁} {φ₂} θ₁~θ₂ φ₁~φ₂ X → Category.∘-respects 𝔹 (θ₁~θ₂ X) (φ₁~φ₂ X)
            }

    id : (F : Functor 𝔸 𝔹) → NaturalTransformation F F
    id F = record {
        rawNaturalTransformation = record { η = λ X → Category.id 𝔹 (mapₒ F X) };
        isNaturalTransformation = record { commutes = λ {X} {Y} f → ~-trans id-is-left-id (~-sym id-is-right-id) }
        }

    ∘-assoc : {F G H I : Functor 𝔸 𝔹} →
        (θ : NaturalTransformation H I)
        (φ : NaturalTransformation G H)
        (ψ : NaturalTransformation F G) →
        θ ∘ (φ ∘ ψ) ≈
        (θ ∘ φ) ∘ ψ
    ∘-assoc {F = F} {G} {H} {I} θ φ ψ X = ~-sym (assoc (θ .η X) (φ .η X) (ψ .η X))

    module _ {F G : Functor 𝔸 𝔹} where
        ∘-left-id :
            (θ : NaturalTransformation F G) →
            id G ∘ θ ≈ θ
        ∘-left-id θ X = id-is-left-id

        ∘-right-id :
            (θ : NaturalTransformation F G) →
            θ ∘ id F ≈ θ
        ∘-right-id θ X = id-is-right-id


------------------------------
--- Horizontal composition ---
------------------------------
module _ {𝔸 : RawCategory a b c} {𝔹 : RawCategory α β γ} {ℂ : RawCategory ℓ₁ ℓ₂ ℓ₃} where
    module _ {F G : RawFunctor 𝔸 𝔹} {J K : RawFunctor 𝔹 ℂ} where
        open RawFunctor using (mapₒ; mapₘ)
        open RawNaturalTransformation using (η)

        _*'_ : RawNaturalTransformation J K → RawNaturalTransformation F G → RawNaturalTransformation (J ∘-RawFunctor F) (K ∘-RawFunctor G)
        _*'_ φ θ = record {
            η = λ X → (φ .η (mapₒ G X)) ∘₃ (mapₘ J (θ .η X))
            }
            where
                open RawCategory ℂ using (~-refl; ~-sym; ~-trans) renaming (_∘_ to _∘₃_)

module _ {𝔸 : Category a b c} {𝔹 : Category α β γ} {ℂ : Category ℓ₁ ℓ₂ ℓ₃} where
    module _ {F G : Functor 𝔸 𝔹} {J K : Functor 𝔹 ℂ} where
        open Functor using (mapₒ; mapₘ; rawFunctor)
        open NaturalTransformation using (η; commutes)
        {-
            Horizontal composition diagram:
            Given
            f : X → Y in 𝔸
            θ : F → G
            φ : J → K
            we get

            J(F(X)) ---J(θ_X)--> J(G(X)) ---φ_(G(X))--> K(G(X))
            |                       |                   |
            |                       |                   |
            J(F(f))                 J(G(f))             K(G(f))
            |                       |                   |
            V                       V                   V
            J(F(Y)) ---J(θ_Y)--> J(G(Y)) ---φ_(G(Y))--> K(G(Y))
        -}
        _*_ : NaturalTransformation J K → NaturalTransformation F G → NaturalTransformation (J ∘-Functor F) (K ∘-Functor G)
        _*_ φ θ = record {
            rawNaturalTransformation = _*'_ (φ .NaturalTransformation.rawNaturalTransformation) (θ .NaturalTransformation.rawNaturalTransformation);
            isNaturalTransformation = record { commutes = λ {X} {Y} f → commutative-square-compose ℂ {by = mapₘ (J ∘-Functor G) f} (begin
                mapₘ J (θ .η Y) ∘₃ mapₘ (J ∘-Functor F) f   ≈⟨ ~-sym (Functor.consistent-on-∘ J (θ .η Y) (mapₘ F f)) ⟩
                mapₘ J (θ .η Y ∘₂ mapₘ F f)                 ≈⟨ Functor.mapₘ-respects J (θ .commutes f) ⟩
                mapₘ J (mapₘ G f ∘₂ θ .η X)                 ≈⟨ Functor.consistent-on-∘ J (mapₘ G f) (θ .η X) ⟩
                mapₘ (J ∘-Functor G) f ∘₃ mapₘ J (θ .η X)   ∎
                ) (begin
                φ .η (mapₒ G Y) ∘₃ mapₘ (J ∘-Functor G) f   ≈⟨ φ .commutes (mapₘ G f) ⟩
                mapₘ (K ∘-Functor G) f ∘₃ φ .η (mapₒ G X)   ∎
                )}
            }
            where
                open Category ℂ using (~-refl; ~-sym; ~-trans) renaming (_∘_ to _∘₃_)
                open Category 𝔹 using () renaming (_∘_ to _∘₂_)
                module _ {X Y : Category.Object ℂ} where
                    open import Relation.Binary.Reasoning.Setoid (Category.Morphism' ℂ X Y) public
    -- Note whiskering is equivalent to horizontal composition with an identity functor.

module _ {𝔸 : Category a b c} {𝔹 : Category α β γ} {ℂ : Category ℓ₁ ℓ₂ ℓ₃} {𝔻 : Category l₁ l₂ l₃} where
    module _ {J K : Functor ℂ 𝔻} {H I : Functor 𝔹 ℂ} {F G : Functor 𝔸 𝔹} (ψ : NaturalTransformation J K) (φ : NaturalTransformation H I) (θ : NaturalTransformation F G) where
        open Functor using (mapₒ; mapₘ; rawFunctor)
        open NaturalTransformation using (η; commutes)

        -- Maybe worth finding a way to redefine things so this holds of *' too: note that this proof does not require commutativity of the natural transformation itself, only of the categories and functors underlying it
        *-assoc : (ψ * (φ * θ)) .NaturalTransformation.rawNaturalTransformation ≈' ((ψ * φ) * θ) .NaturalTransformation.rawNaturalTransformation
        *-assoc X = begin
            (ψ * (φ * θ)) .η X                                                                  ≈⟨ refl ⟩
            ψ .η (mapₒ I (mapₒ G X)) ∘₄ (mapₘ J ((φ .η (mapₒ G X)) ∘₃ mapₘ H (θ .η X)))         ≈⟨ Category.∘-respects 𝔻 ~-refl (Functor.consistent-on-∘ J (φ .η (mapₒ G X)) (mapₘ H (θ .η X))) ⟩ -- this requires respecfulness of J
            ψ .η (mapₒ I (mapₒ G X)) ∘₄ (mapₘ J (φ .η (mapₒ G X)) ∘₄ mapₘ J (mapₘ H (θ .η X)))  ≈⟨ ~-sym (Category.assoc 𝔻 (ψ .η (mapₒ I (mapₒ G X))) (mapₘ J (φ .η (mapₒ G X))) (mapₘ J (mapₘ H (θ .η X)))) ⟩ -- this requires associativity of ∘₄
            (ψ .η (mapₒ I (mapₒ G X)) ∘₄ mapₘ J (φ .η (mapₒ G X))) ∘₄ mapₘ J (mapₘ H (θ .η X))  ≈⟨ refl ⟩
            ((ψ * φ) * θ) .η X                                                                  ∎
            where
                open Category ℂ using () renaming (_∘_ to _∘₃_)
                open Category 𝔻 using (~-refl; ~-sym; ~-trans) renaming (_∘_ to _∘₄_)
                module _ {X Y : Category.Object 𝔻} where
                    open import Relation.Binary.Reasoning.Setoid (Category.Morphism' 𝔻 X Y) public
                    open IsEquivalence (Category.~-eq 𝔻 X Y) using (reflexive; refl; sym; trans) public

module _ {𝔸 : Category a b c} {𝔹 : Category α β γ} {ℂ : Category ℓ₁ ℓ₂ ℓ₃} where
    open Functor using (mapₒ; mapₘ; rawFunctor)
    open NaturalTransformation using (η; commutes)
     {-
        Interchange law diagram:
        Given
        f : X → Y in 𝔸
        θ : F → G,  φ : G → H
        θ' : J → I, φ' : I → K
        we get

        --------F----\     ------I-------
        |       θ     \   /      θ'     |
        |       V      V /       V      V
        𝔸 ------G-----> 𝔹 -------J----> ℂ
        |       φ      ^ \       φ'     ^
        |       V     /   \      V      |
        --------H----/     ------K-------
    -}
    module _ {F G H : Functor 𝔸 𝔹} {J K I : Functor 𝔹 ℂ} (φ : NaturalTransformation G H) (θ : NaturalTransformation F G) (φ' : NaturalTransformation I K) (θ' : NaturalTransformation J I) where
        interchange-law : (φ' ∘ θ') * (φ ∘ θ) ≈ (φ' * φ) ∘ (θ' * θ)
        interchange-law X = begin
            ((φ' ∘ θ') * (φ ∘ θ)) .η X                                                      ≈⟨ ~-refl ⟩
            (φ' .η (mapₒ H X) ∘₃ θ' .η (mapₒ H X)) ∘₃ mapₘ J (φ .η X ∘₂ θ .η X)             ≈⟨ ∘-respects₃ ~-refl (Functor.consistent-on-∘ J (φ .η X) (θ .η X)) ⟩
            (φ' .η (mapₒ H X) ∘₃ θ' .η (mapₒ H X)) ∘₃ (mapₘ J (φ .η X) ∘₃ mapₘ J (θ .η X))  ≈⟨ assoc₃ (φ' .η (mapₒ H X)) (θ' .η (mapₒ H X)) (mapₘ J (φ .η X) ∘₃ mapₘ J (θ .η X)) ⟩
            φ' .η (mapₒ H X) ∘₃ (θ' .η (mapₒ H X) ∘₃ (mapₘ J (φ .η X) ∘₃ mapₘ J (θ .η X)))  ≈⟨ ∘-respects₃ ~-refl (~-sym (assoc₃ (θ' .η (mapₒ H X)) (mapₘ J (φ .η X)) (mapₘ J (θ .η X)))) ⟩
            φ' .η (mapₒ H X) ∘₃ ((θ' .η (mapₒ H X) ∘₃ mapₘ J (φ .η X)) ∘₃ mapₘ J (θ .η X))  ≈⟨ ∘-respects₃ ~-refl (∘-respects₃ (θ' .commutes (φ .η X)) ~-refl) ⟩
            φ' .η (mapₒ H X) ∘₃ ((mapₘ I (φ .η X) ∘₃ θ' .η (mapₒ G X)) ∘₃ mapₘ J (θ .η X))  ≈⟨ ∘-respects₃ ~-refl (assoc₃ (mapₘ I (φ .η X)) (θ' .η (mapₒ G X)) (mapₘ J (θ .η X))) ⟩
            φ' .η (mapₒ H X) ∘₃ (mapₘ I (φ .η X) ∘₃ (θ' .η (mapₒ G X) ∘₃ mapₘ J (θ .η X)))  ≈⟨ ~-sym (assoc₃ (φ' .η (mapₒ H X)) (mapₘ I (φ .η X)) ((θ' .η (mapₒ G X) ∘₃ mapₘ J (θ .η X)))) ⟩
            (φ' .η (mapₒ H X) ∘₃ mapₘ I (φ .η X)) ∘₃ (θ' .η (mapₒ G X) ∘₃ mapₘ J (θ .η X))  ≈⟨ ~-refl ⟩
            ((φ' * φ) ∘ (θ' * θ)) .η X                                                      ∎
            where
                open Category ℂ using (~-refl; ~-sym; ~-trans) renaming (_∘_ to _∘₃_; ∘-respects to ∘-respects₃; assoc to assoc₃)
                open Category 𝔹 using () renaming (_∘_ to _∘₂_)
                module _ {X Y : Category.Object ℂ} where
                    open import Relation.Binary.Reasoning.Setoid (Category.Morphism' ℂ X Y) public
