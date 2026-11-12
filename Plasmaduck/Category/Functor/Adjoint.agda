open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Relation.Binary.PropositionalEquality using (_≡_) renaming (refl to ≡-refl)
open import Relation.Binary using (Setoid; Rel; IsEquivalence)
open import Function using (Congruent)
open import Data.Product using (Σ; _×_; _,_)

open import Plasmaduck.SetoidExperiment.SetoidMachinery using (SetoidFunction₂)
open import Plasmaduck.Category.Category using (RawCategory; Category; RawFunctor; Functor; opposite-category; opposite-functor; IsSidedInverse)
open import Plasmaduck.Util.Case using (case_of_)
open import Plasmaduck.Category.Functor.SimpleFunctors using (id-functor; id-raw-functor)
open import Plasmaduck.Category.Functor.Properties using (RawFunctorSetoid; FunctorSetoid; Functor-compose-func) renaming (_∘_ to _∘-Functor_; _∘'_ to _∘-RawFunctor_)
open import Plasmaduck.Function.Properties using (ExplicitlyCongruent; Congruent₂)
open import Plasmaduck.Category.CommutativeSquare using (commutative-square-compose)
open import Plasmaduck.Relation.On using (on-preserves-equality)
open import Plasmaduck.Category.Functor.NaturalTransformation using (RawNaturalTransformation; IsNaturalTransformation; NaturalTransformation; RawNaturalTransformation'; _*'_) renaming (id' to id-raw-natural-transformation; _≈'_ to _≈-RawNaturalTransformation_; _∘'_ to _∘-RawNaturalTransformation_)
open import Plasmaduck.Category.UniversalMorphism using (UniversalMorphism; universal-morphism-everywhere-type; opposite-universal-morphism-everywhere-type; induced-functor)
open import Plasmaduck.Category.ExampleFunctors.Hom using (Hom)



module Plasmaduck.Category.Functor.Adjoint where

{-
    According to wikipedia, there are three canonical definitions for what it means for two functors to be adjoint.
    F and G (with F left-adjoint and G right-adjoint) are adjoint if:
    - for each object X : C, there is a universal morphism from F to X.
      - alternatively, for each object Y : D, there is a universal morphism from Y to G.
    - there is a natural isomorphism between Hom_C(FY , X) and Hom_D(Y, GX) for all objects X : C, Y : D
    - There are two natural transformations ε : FG → 1_C (the counit) and η : GF → 1_D (the unit) such that the compositions:
        F ---(1_F * η)--> FGF ---(ε * 1_F)--> F
        G ---(η * 1_G)--> GFG ---(1_G * ε)--> G
      are identity morphisms on F and G, respectively.
-}

variable
    a b c α β γ : Level

module HomSetAdjoint {ℂ : Category a b c} {𝔻 : Category α β γ} (F : Functor 𝔻 ℂ) (G : Functor ℂ 𝔻) where



module _ {ℂ : RawCategory a b c} {𝔻 : RawCategory α β γ} where
    record RawAdjointFunctorsProof (F : RawFunctor 𝔻 ℂ) (G : RawFunctor ℂ 𝔻) : Set (a ⊔ b ⊔ c ⊔ α ⊔ β ⊔ γ) where
        field
            raw-counit : RawNaturalTransformation (F ∘-RawFunctor G) (id-raw-functor ℂ)
            raw-unit : RawNaturalTransformation (id-raw-functor 𝔻) (G ∘-RawFunctor F)

    module _ {F : RawFunctor 𝔻 ℂ} {G : RawFunctor ℂ 𝔻} (rawAdjointFunctorsProof : RawAdjointFunctorsProof F G) where
        open RawAdjointFunctorsProof rawAdjointFunctorsProof

        F-equation-type : Set _
        F-equation-type = (id-raw-natural-transformation F) ≈-RawNaturalTransformation ((raw-counit *' (id-raw-natural-transformation F)) ∘-RawNaturalTransformation ((id-raw-natural-transformation F) *' raw-unit))

        G-equation-type : Set _
        G-equation-type = (id-raw-natural-transformation G) ≈-RawNaturalTransformation (((id-raw-natural-transformation G) *' raw-counit) ∘-RawNaturalTransformation (raw-unit *' (id-raw-natural-transformation G)))

        record IsAdjointProof : Set (a ⊔ b ⊔ c ⊔ α ⊔ β ⊔ γ) where
            field
                is-counit : IsNaturalTransformation raw-counit
                is-unit : IsNaturalTransformation raw-unit

                F-equation : F-equation-type
                G-equation : G-equation-type


module _ {ℂ : Category a b c} {𝔻 : Category α β γ} where
    open Functor using (mapₒ; mapₘ)

    module _ (F : Functor 𝔻 ℂ) (G : Functor ℂ 𝔻) where
        RawAdjointFunctorsProof' = RawAdjointFunctorsProof (F .Functor.rawFunctor) (G .Functor.rawFunctor)

        -- F is left adjoint to G, and G is right adjoint to F.
        record AreAdjointFunctors : Set (a ⊔ b ⊔ c ⊔ α ⊔ β ⊔ γ) where
            field
                rawAdjointFunctorsProof : RawAdjointFunctorsProof'
                isAdjointProof : IsAdjointProof rawAdjointFunctorsProof

            open RawAdjointFunctorsProof rawAdjointFunctorsProof public
            open IsAdjointProof isAdjointProof public

            counit : NaturalTransformation (F ∘-Functor G) (id-functor ℂ)
            counit = record {rawNaturalTransformation = raw-counit; isNaturalTransformation = is-counit}

            unit : NaturalTransformation (id-functor 𝔻) (G ∘-Functor F)
            unit = record {rawNaturalTransformation = raw-unit; isNaturalTransformation = is-unit}

    IsLeftAdjoint : (F : Functor 𝔻 ℂ) → Set _
    IsLeftAdjoint F = Σ (Functor ℂ 𝔻) λ G → AreAdjointFunctors F G

    IsRightAdjoint : (G : Functor ℂ 𝔻) → Set _
    IsRightAdjoint G = Σ (Functor 𝔻 ℂ) λ F → AreAdjointFunctors F G


module _ {ℂ : Category a b c} {𝔻 : Category α β γ} where
    open Functor using (mapₒ; mapₘ)
    open UniversalMorphism using (u; A)

    -- In terms of universal morphisms:
    thing : {G : Functor ℂ 𝔻} → (pf : universal-morphism-everywhere-type G) → AreAdjointFunctors (induced-functor G pf) G
    thing {G = G} pf = record {
        rawAdjointFunctorsProof = record {
            raw-counit = record { η = λ X → UniversalMorphism.generate-morph (pf (mapₒ G X)) X (Category.id 𝔻 (mapₒ G X)) };
            raw-unit = record { η = λ Y → (pf Y) .u}
            };
        isAdjointProof = record {
            is-counit = record {
                commutes = λ {X} {Y} f → {!   !}
                };
            is-unit = record
              { commutes =
                  λ {X} {Y} f →
                    IsEquivalence.sym
                    (Setoid.isEquivalence
                     (RawCategory.Morphism' (Category.rawCategory 𝔻)
                      (RawFunctor.mapₒ (id-raw-functor (Category.rawCategory 𝔻)) X)
                      (RawFunctor.mapₒ
                       (G .Functor.rawFunctor ∘-RawFunctor
                        induced-functor G pf .Functor.rawFunctor)
                       Y)))
                    (Plasmaduck.Category.UniversalMorphism.IsUniversalMorphism.commutes
                     (pf (RawFunctor.mapₒ (id-raw-functor (Category.rawCategory 𝔻)) X)
                      .UniversalMorphism.isUniversalMorphism)
                     (RawFunctor.mapₒ (induced-functor G pf .Functor.rawFunctor) Y)
                     ((𝔻 Category.∘
                       Plasmaduck.Category.UniversalMorphism.RawUniversalMorphism.u
                       (UniversalMorphism.rawUniversalMorphism (pf Y)))
                      f))
              };
            F-equation = λ X → {!   !};
            G-equation = λ X → {!   !}
            }
        }
        where
            F = induced-functor G pf
            F' = F .Functor.rawFunctor
            G' = G .Functor.rawFunctor

            open NaturalTransformation
            raw-counit : RawNaturalTransformation' (F ∘-Functor G) (id-functor ℂ)
            raw-counit = record { η = λ X → UniversalMorphism.generate-morph (pf (mapₒ G X)) X (Category.id 𝔻 (mapₒ G X)) }
            raw-unit : RawNaturalTransformation' (id-functor 𝔻) (G ∘-Functor F)
            raw-unit = record { η = λ Y → (pf Y) .u}

            is-counit : IsNaturalTransformation raw-counit
            is-counit = record { commutes = λ {X} {Y} f → begin
                    UniversalMorphism.generate-morph (pf (mapₒ G Y)) Y (Category.id 𝔻 (mapₒ G Y)) ∘ mapₘ (F ∘-Functor G) f                                                                              ≈⟨ refl ⟩
                    UniversalMorphism.generate-morph (pf (mapₒ G Y)) Y (Category.id 𝔻 (mapₒ G Y)) ∘ mapₘ (induced-functor G pf) (mapₘ G f)                                                              ≈⟨ refl ⟩
                    UniversalMorphism.generate-morph (pf (mapₒ G Y)) Y (Category.id 𝔻 (mapₒ G Y)) ∘ UniversalMorphism.generate-morph (pf (mapₒ G X)) (pf (mapₒ G Y) .A) (pf (mapₒ G Y) .u ∘₂ mapₘ G f)  ≈⟨ {!   !} ⟩
                    f ∘ UniversalMorphism.generate-morph (pf (mapₒ G X)) X (Category.id 𝔻 (mapₒ G X))                                                                                                   ≈⟨ refl ⟩
                    mapₘ (id-functor ℂ) f ∘ UniversalMorphism.generate-morph (pf (mapₒ G X)) X (Category.id 𝔻 (mapₒ G X))                                                                               ∎
                    }
                where
                    open Category ℂ using (_∘_)
                    open Category 𝔻 using () renaming (_∘_ to _∘₂_)
                    module _ {X Y : Category.Object ℂ} where
                        open import Relation.Binary.Reasoning.Setoid (Category.Morphism' ℂ X Y) public
                        open IsEquivalence (Category.~-eq ℂ X Y) using (refl; sym; trans) public

            is-unit : IsNaturalTransformation raw-unit
            is-unit = record { commutes = λ {X} {Y} f → IsEquivalence.sym
                  (Setoid.isEquivalence
                   (RawCategory.Morphism' (Category.rawCategory 𝔻)
                    (RawFunctor.mapₒ (id-functor 𝔻 .Functor.rawFunctor) X)
                    (RawFunctor.mapₒ ((G ∘-Functor F) .Functor.rawFunctor) Y)))
                  (Plasmaduck.Category.UniversalMorphism.IsUniversalMorphism.commutes
                   (pf (RawFunctor.mapₒ (id-functor 𝔻 .Functor.rawFunctor) X)
                    .UniversalMorphism.isUniversalMorphism)
                   (RawFunctor.mapₒ F' Y)
                   ((𝔻 Category.∘
                     Plasmaduck.Category.UniversalMorphism.RawUniversalMorphism.u
                     (UniversalMorphism.rawUniversalMorphism (pf Y)))
                    f)) }

            raw-pf : RawAdjointFunctorsProof' F G
            raw-pf = record { raw-counit = raw-counit; raw-unit = raw-unit }

            F-equation : F-equation-type raw-pf
            F-equation Y = begin
                (id-raw-natural-transformation F') .RawNaturalTransformation.η Y                                                                                            ≈⟨ refl ⟩
                Category.id ℂ (mapₒ F Y)                                                                                                                                    ≈⟨ {!   !} ⟩
                ((raw-counit *' id-raw-natural-transformation F') ∘-RawNaturalTransformation (id-raw-natural-transformation F' *' raw-unit)) .RawNaturalTransformation.η Y  ∎
                where
                    open Category ℂ using (_∘_)
                    open Category 𝔻 using () renaming (_∘_ to _∘₂_)
                    module _ {X Y : Category.Object ℂ} where
                        open import Relation.Binary.Reasoning.Setoid (Category.Morphism' ℂ X Y) public
                        open IsEquivalence (Category.~-eq ℂ X Y) using (refl; sym; trans) public


            G-equation : G-equation-type raw-pf
            G-equation X = {!   !}
                where
                    open Category ℂ using (_∘_)
                    open Category 𝔻 using () renaming (_∘_ to _∘₂_)
                    module _ {X Y : Category.Object 𝔻} where
                        open import Relation.Binary.Reasoning.Setoid (Category.Morphism' 𝔻 X Y) public
                        open IsEquivalence (Category.~-eq 𝔻 X Y) using (refl; sym; trans) public



    -- thing2 : {G : Functor ℂ 𝔻} → (pf : opposite-universal-morphism-everywhere-type G) → AreAdjointFunctors (induced-functor (opposite-functor G) pf) (opposite-functor G)
    -- thing2 {G = G} pf = record {
    --     rawAdjointFunctorsProof = record {
    --         raw-counit = record { η = λ X → {! pf X .UniversalMorphism.u  !} };
    --         raw-unit = record { η = λ X → {! pf  !}}
    --         };
    --     isAdjointProof = record {
    --         is-counit = {!   !};
    --         is-unit = {!   !};
    --         F-equation = {!   !};
    --         G-equation = {!   !}
    --         }
    --     }

    -- open AreAdjointFunctors
    -- open NaturalTransformation

    -- opposites-invert-adjoint : {F : Functor 𝔻 ℂ} {G : Functor ℂ 𝔻} → AreAdjointFunctors F G → AreAdjointFunctors (opposite-functor G) (opposite-functor F)
    -- opposites-invert-adjoint {F = F} {G} FG-adjoint = record {
    --     rawAdjointFunctorsProof = record {
    --         raw-counit = record { η = AreAdjointFunctors.unit FG-adjoint .η };
    --         raw-unit = record { η = AreAdjointFunctors.counit FG-adjoint .η }
    --         };
    --     isAdjointProof = record {
    --         is-counit = record { commutes = {! AreAdjointFunctors.unit FG-adjoint .commutes  !} };
    --         is-unit = record { commutes = {!   !} };
    --         F-equation = {!   !};
    --         G-equation = {!   !}
    --         }
    --     }
