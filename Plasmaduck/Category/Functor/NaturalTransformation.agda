open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Relation.Binary.PropositionalEquality using (_≡_) renaming (refl to ≡-refl)
open import Relation.Binary using (Setoid; Rel; IsEquivalence)
open import Function using (Congruent)
open import Data.Product using (_×_; _,_)

open import Plasmaduck.SetoidExperiment.SetoidMachinery using (SetoidFunction₂)
open import Plasmaduck.Category.Category using (Category; Functor; opposite-category; opposite-functor; IsSidedInverse)
open import Plasmaduck.Util.Case using (case_of_)
open import Plasmaduck.Category.Functor.SimpleFunctors using (id-functor)
open import Plasmaduck.Category.Functor.Properties using (FunctorSetoid; Functor-compose-func)
open import Plasmaduck.Function.Properties using (ExplicitlyCongruent; Congruent₂)



module Plasmaduck.Category.Functor.NaturalTransformation where

variable
    a b c α β γ ℓ₁ ℓ₂ ℓ₃ : Level

open Functor using (mapₒ; mapₘ)


module _ {𝔸 : Category a b c} {𝔹 : Category α β γ} where
    open Category 𝔹 using () renaming (_∘_ to _∘₂_; _~_ to _~₂_)
    open Category 𝔹 using (assoc; id-is-left-id; id-is-right-id; ∘-respects; ~-refl; ~-sym; ~-trans)


    record NaturalTransformation (F G : Functor 𝔸 𝔹) : Set (a ⊔ b ⊔ β ⊔ γ) where
        field
            η : (X : Category.Object 𝔸) → Category.Morphism 𝔹 (mapₒ F X) (mapₒ G X)
            commutes :
                {X Y : Category.Object 𝔸} (f : Category.Morphism 𝔸 X Y) →
                η Y ∘₂ mapₘ F f ~₂ mapₘ G f ∘₂ η X
    open NaturalTransformation

    module _ {F G : Functor 𝔸 𝔹} where
        _≈-NaturalTransformation_ : (θ φ : NaturalTransformation F G) → Set (a ⊔ γ)
        _≈-NaturalTransformation_ θ φ = ∀ (X : Category.Object 𝔸) → (θ .η X) ~₂ (φ .η X)
        infix 1 _≈-NaturalTransformation_

    module _ (F G : Functor 𝔸 𝔹) where
        ≈-NaturalTransformation-eq : IsEquivalence (_≈-NaturalTransformation_ {F} {G})
        ≈-NaturalTransformation-eq = record {
            refl = λ {θ} X → Category.~-refl 𝔹;
            sym = λ {θ} {φ} θ~φ X → Category.~-sym 𝔹 (θ~φ X);
            trans = λ {θ} {φ} {ψ} θ~φ φ~ψ X → Category.~-trans 𝔹 (θ~φ X) (φ~ψ X)
            }

        NaturalTransformationSetoid : Setoid (a ⊔ b ⊔ β ⊔ γ) (a ⊔ γ)
        NaturalTransformationSetoid = record {
            Carrier = NaturalTransformation F G;
            _≈_ = _≈-NaturalTransformation_;
            isEquivalence = ≈-NaturalTransformation-eq
            }

    module _ {F G H : Functor 𝔸 𝔹} where
        _∘-NaturalTransformation_ :
            (NaturalTransformation G H) →
            (NaturalTransformation F G) →
            (NaturalTransformation F H)
        _∘-NaturalTransformation_ θ φ = record {
            η = λ X → (θ .η X) ∘₂ (φ .η X);
            commutes = λ {X} {Y} f → begin
                (θ .η Y ∘₂ φ .η Y) ∘₂ mapₘ F f  ≈⟨ assoc (θ .η Y) (φ .η Y) (mapₘ F f) ⟩
                θ .η Y ∘₂ (φ .η Y ∘₂ mapₘ F f)  ≈⟨ ∘-respects ~-refl (φ .commutes f) ⟩
                θ .η Y ∘₂ (mapₘ G f ∘₂ φ .η X)  ≈⟨ ~-sym (assoc (θ .η Y) (mapₘ G f) (φ .η X)) ⟩
                (θ .η Y ∘₂ mapₘ G f) ∘₂ φ .η X  ≈⟨ ∘-respects (θ .commutes f) ~-refl ⟩
                (mapₘ H f ∘₂ θ .η X) ∘₂ φ .η X  ≈⟨ assoc (mapₘ H f) (θ .η X) (φ .η X) ⟩
                mapₘ H f ∘₂ (θ .η X ∘₂ φ .η X)  ∎
            }
            where
                module _ {X Y : Category.Object 𝔹} where
                    open import Relation.Binary.Reasoning.Setoid (Category.Morphism' 𝔹 X Y) public
        infixr 9 _∘-NaturalTransformation_

        ∘-NaturalTransformation-respects : Congruent₂ (_≈-NaturalTransformation_ {G} {H}) (_≈-NaturalTransformation_ {F} {G}) (_≈-NaturalTransformation_ {F} {H}) _∘-NaturalTransformation_
        ∘-NaturalTransformation-respects = λ z z₁ X →
            Plasmaduck.Category.Category.RawCategory.compose
            (Category.rawCategory 𝔹) .SetoidFunction₂.respects (z X) (z₁ X)

        NaturalTransformation-compose-func : SetoidFunction₂ (NaturalTransformationSetoid G H) (NaturalTransformationSetoid F G) (NaturalTransformationSetoid F H)
        NaturalTransformation-compose-func = record {
            func = _∘-NaturalTransformation_;
            respects = λ {θ₁} {θ₂} {φ₁} {φ₂} θ₁~θ₂ φ₁~φ₂ X → Category.∘-respects 𝔹 (θ₁~θ₂ X) (φ₁~φ₂ X)
            }

    id-NaturalTransformation : (F : Functor 𝔸 𝔹) → NaturalTransformation F F
    id-NaturalTransformation F = record {
        η = λ X → Category.id 𝔹 (mapₒ F X);
        commutes = λ {X} {Y} f → ~-trans id-is-left-id (~-sym id-is-right-id)
        }

    ∘-NaturalTransformation-assoc : {F G H I : Functor 𝔸 𝔹} →
        (θ : NaturalTransformation H I)
        (φ : NaturalTransformation G H)
        (ψ : NaturalTransformation F G) →
        θ ∘-NaturalTransformation (φ ∘-NaturalTransformation ψ) ≈-NaturalTransformation
        (θ ∘-NaturalTransformation φ) ∘-NaturalTransformation ψ
    ∘-NaturalTransformation-assoc {F = F} {G} {H} {I} θ φ ψ X = ~-sym (assoc (θ .η X) (φ .η X) (ψ .η X))

    module _ {F G : Functor 𝔸 𝔹} where
        ∘-NaturalTransformation-left-id :
            (θ : NaturalTransformation F G) →
            id-NaturalTransformation G ∘-NaturalTransformation θ ≈-NaturalTransformation θ
        ∘-NaturalTransformation-left-id θ X = id-is-left-id

        ∘-NaturalTransformation-right-id :
            (θ : NaturalTransformation F G) →
            θ ∘-NaturalTransformation id-NaturalTransformation F ≈-NaturalTransformation θ
        ∘-NaturalTransformation-right-id θ X = id-is-right-id
