open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Relation.Binary.PropositionalEquality using (_≡_) renaming (refl to ≡-refl)
open import Relation.Binary using (Setoid; Rel; IsEquivalence)
open import Function using (Congruent)
open import Data.Product using (_×_; _,_)

open import Plasmaduck.SetoidExperiment.SetoidMachinery using (SetoidFunction₂)
open import Plasmaduck.Category.Category using (Category; Functor; opposite-category; opposite-functor; IsSidedInverse)
open import Plasmaduck.Util.Case using (case_of_)
open import Plasmaduck.Category.Functor.SimpleFunctors using (id-functor)
open import Plasmaduck.Category.Functor.Properties using (FunctorSetoid; Functor-compose-func; _∘-Functor_)
open import Plasmaduck.Function.Properties using (ExplicitlyCongruent; Congruent₂)
open import Plasmaduck.Category.CommutativeSquare using (commutative-square-compose)



module Plasmaduck.Category.Functor.NaturalTransformation where

variable
    a b c α β γ ℓ₁ ℓ₂ ℓ₃ : Level

open Functor using (mapₒ; mapₘ)


module _ {𝔸 : Category a b c} {𝔹 : Category α β γ} where
    open Category 𝔹 using () renaming (_∘_ to _∘₂_; _~_ to _~₂_)
    open Category 𝔹 using (assoc; id-is-left-id; id-is-right-id; ~-refl; ~-sym; ~-trans)


    record NaturalTransformation (F G : Functor 𝔸 𝔹) : Set (a ⊔ b ⊔ β ⊔ γ) where
        field
            η : (X : Category.Object 𝔸) → Category.Morphism 𝔹 (mapₒ F X) (mapₒ G X)
            commutes :
                {X Y : Category.Object 𝔸} (f : Category.Morphism 𝔸 X Y) →
                η Y ∘₂ mapₘ F f ~₂ mapₘ G f ∘₂ η X
    open NaturalTransformation

    _≈_ : {F G : Functor 𝔸 𝔹} (θ φ : NaturalTransformation F G) → Set (a ⊔ γ)
    _≈_ θ φ = ∀ (X : Category.Object 𝔸) → (θ .η X) ~₂ (φ .η X)
    infix 1 _≈_

    module _ (F G : Functor 𝔸 𝔹) where
        ≈-eq : IsEquivalence (_≈_ {F} {G})
        ≈-eq = record {
            refl = λ {θ} X → Category.~-refl 𝔹;
            sym = λ {θ} {φ} θ~φ X → Category.~-sym 𝔹 (θ~φ X);
            trans = λ {θ} {φ} {ψ} θ~φ φ~ψ X → Category.~-trans 𝔹 (θ~φ X) (φ~ψ X)
            }

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
            η = λ X → (θ .η X) ∘₂ (φ .η X);
            commutes = λ {X} {Y} f → commutative-square-compose 𝔹 (φ .commutes f) (θ .commutes f)
            }
            where
                module _ {X Y : Category.Object 𝔹} where
                    open import Relation.Binary.Reasoning.Setoid (Category.Morphism' 𝔹 X Y) public
        infixr 9 _∘_

        ∘-respects : Congruent₂ (_≈_ {G} {H}) (_≈_ {F} {G}) (_≈_ {F} {H}) _∘_
        ∘-respects = λ z z₁ X →
            Plasmaduck.Category.Category.RawCategory.compose
            (Category.rawCategory 𝔹) .SetoidFunction₂.respects (z X) (z₁ X)

        compose-func : SetoidFunction₂ (NaturalTransformationSetoid G H) (NaturalTransformationSetoid F G) (NaturalTransformationSetoid F H)
        compose-func = record {
            func = _∘_;
            respects = λ {θ₁} {θ₂} {φ₁} {φ₂} θ₁~θ₂ φ₁~φ₂ X → Category.∘-respects 𝔹 (θ₁~θ₂ X) (φ₁~φ₂ X)
            }

    id : (F : Functor 𝔸 𝔹) → NaturalTransformation F F
    id F = record {
        η = λ X → Category.id 𝔹 (mapₒ F X);
        commutes = λ {X} {Y} f → ~-trans id-is-left-id (~-sym id-is-right-id)
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

open NaturalTransformation using (η; commutes)
open Functor using (mapₒ; mapₘ)

------------------------------
--- Horizontal composition ---
------------------------------
module _ {𝔸 : Category a b c} {𝔹 : Category α β γ} {ℂ : Category ℓ₁ ℓ₂ ℓ₃} where
    module _ {F G : Functor 𝔸 𝔹} {J K : Functor 𝔹 ℂ} where
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
            η = λ X → (φ .η (mapₒ G X)) ∘₃ (mapₘ J (θ .η X));
            commutes = λ {X} {Y} f → commutative-square-compose ℂ {by = mapₘ (J ∘-Functor G) f} (begin
                mapₘ J (θ .η Y) ∘₃ mapₘ (J ∘-Functor F) f   ≈⟨ ~-sym (Functor.consistent-on-∘ J (θ .η Y) (mapₘ F f)) ⟩
                mapₘ J (θ .η Y ∘₂ mapₘ F f)                 ≈⟨ Functor.mapₘ-respects J (θ .commutes f) ⟩
                mapₘ J (mapₘ G f ∘₂ θ .η X)                 ≈⟨ Functor.consistent-on-∘ J (mapₘ G f) (θ .η X) ⟩
                mapₘ (J ∘-Functor G) f ∘₃ mapₘ J (θ .η X)   ∎
                ) (begin
                φ .η (mapₒ G Y) ∘₃ mapₘ (J ∘-Functor G) f   ≈⟨ φ .commutes (mapₘ G f) ⟩
                mapₘ (K ∘-Functor G) f ∘₃ φ .η (mapₒ G X)   ∎
                )
            }
            where
                open Category ℂ using (~-refl; ~-sym; ~-trans) renaming (_∘_ to _∘₃_)
                open Category 𝔹 using () renaming (_∘_ to _∘₂_)
                module _ {X Y : Category.Object ℂ} where
                    open import Relation.Binary.Reasoning.Setoid (Category.Morphism' ℂ X Y) public
    -- Note whiskering is equivalent to horizontal composition with an identity functor.

-- module _ {𝔸 : Category a b c} {𝔹 : Category α β γ} {ℂ : Category ℓ₁ ℓ₂ ℓ₃} {𝔻 : Category l₁ l₂ l₃} where
--     module _ {J K : Functor ℂ 𝔻} {H I : Functor 𝔹 ℂ} {F G : Functor 𝔸 𝔹} (ψ : NaturalTransformation J K) (φ : NaturalTransformation H I) (θ : NaturalTransformation F G) where
--         *-assoc : {! (ψ * φ) * θ  !} -- : ψ * (φ * θ) ≈ (ψ * φ) * θ
--         *-assoc = {!   !}

module _ {𝔸 : Category a b c} {𝔹 : Category α β γ} {ℂ : Category ℓ₁ ℓ₂ ℓ₃} where
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


