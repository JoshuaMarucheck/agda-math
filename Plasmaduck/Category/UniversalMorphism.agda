open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Relation.Binary.PropositionalEquality using (_≡_) renaming (refl to ≡-refl)
open import Relation.Binary using (Setoid; Rel; IsEquivalence)
open import Function using (Congruent)
open import Data.Product using (_×_; _,_)

open import Plasmaduck.SetoidExperiment.SetoidMachinery using (SetoidFunction; _←_)
open import Plasmaduck.Category.Category using (Category; Functor; opposite-category; opposite-functor; Isomorphic; IsSidedInverse)
open import Plasmaduck.Util.Case using (case_of_)
open import Plasmaduck.Category.Functor.SimpleFunctors using (id-functor)
open import Plasmaduck.Category.Functor.Properties using (FunctorSetoid; Functor-compose-func)



module Plasmaduck.Category.UniversalMorphism where

variable
    a b c α β γ ℓ₁ ℓ₂ ℓ₃ : Level

open Functor using (mapₒ; mapₘ)


module _ {𝔸 : Category a b c} {𝔹 : Category α β γ} where
    open Category 𝔸 using () renaming (Object to Object₁; Morphism to Morphism₁; Morphism' to Morphism₁'; _~_ to _~₁_)
    open Category 𝔹 using () renaming (Object to Object₂; Morphism to Morphism₂; Morphism' to Morphism₂'; _∘_ to _∘₂_; _~_ to _~₂_)
    {-
        Universal morphism from X to F

            𝔸               𝔹

        X ---u--> F(A)      A
        |          |        |
        |         F(h)      h
        f          |        |
        |          V        V
        --------> F(B)      B

        The universal morphism from X to F is the object A and u, such that:
        - for every B, F, there is a *unique* h such that the diagram commutes.
    -}
    record RawUniversalMorphism (X : Object₂) (F : Functor 𝔸 𝔹) : Set (a ⊔ b ⊔ β) where
        field
            A : Object₁
            u : Morphism₂ X (mapₒ F A)

            -- This function generates h in the above diagram.
            -- Together with IsUniversalMorphism, it can be shown that this is a setoid function.
            -- See generate-morph-respects and generate-morph' below.
            generate-morph : ∀ (B : Object₁) (f : Morphism₂ X (mapₒ F B)) → Morphism₁ A B

    record IsUniversalMorphism {X : Object₂} {F : Functor 𝔸 𝔹} (rawUniversalMorphism : RawUniversalMorphism X F) : Set (a ⊔ b ⊔ c ⊔ β ⊔ γ) where
        open RawUniversalMorphism rawUniversalMorphism
        field
            commutes :
                ∀ (B : Object₁) (f : Morphism₂ X (mapₒ F B)) →
                mapₘ F (generate-morph B f) ∘₂ u ~₂ f
            unique :
                ∀ (B : Object₁) (f : Morphism₂ X (mapₒ F B)) →
                (h : Morphism₁ A B) →
                mapₘ F h ∘₂ u ~₂ f →
                generate-morph B f ~₁ h

    record UniversalMorphism (X : Object₂) (F : Functor 𝔸 𝔹) : Set (a ⊔ b ⊔ c ⊔ β ⊔ γ) where
        field
            rawUniversalMorphism : RawUniversalMorphism X F
            isUniversalMorphism : IsUniversalMorphism rawUniversalMorphism
        open RawUniversalMorphism rawUniversalMorphism public
        open IsUniversalMorphism isUniversalMorphism public

        generate-morph-respects : (B : Object₁) → {f g : Morphism₂ X (mapₒ F B)} → f ~₂ g → (generate-morph B f) ~₁ (generate-morph B g)
        generate-morph-respects B {f} {g} f~g = unique B f (generate-morph B g) (begin
            mapₘ F (generate-morph B g) ∘₂ u    ≈⟨ commutes B g ⟩
            g                                   ≈⟨ Category.~-sym 𝔹 f~g ⟩
            f                                   ∎
            )
            where
                module _ {X Y : Category.Object 𝔹} where
                    open import Relation.Binary.Reasoning.Setoid (Category.Morphism' 𝔹 X Y) public

        generate-morph' : (B : Object₁) → SetoidFunction (Morphism₂' X (mapₒ F B)) (Morphism₁' A B)
        generate-morph' B = record {
            func = generate-morph B;
            respects = generate-morph-respects B
            }

        generate-morph-id : generate-morph A u ~₁ Category.id 𝔸 A
        generate-morph-id = unique A u (Category.id 𝔸 A) (begin
            mapₘ F (Category.id 𝔸 A) ∘₂ u   ≈⟨ ∘-respects (Functor.consistent-on-id F) ~-refl ⟩
            Category.id 𝔹 (mapₒ F A) ∘₂ u   ≈⟨ id-is-left-id ⟩
            u                               ∎)
            where
                module _ {Y Z : Category.Object 𝔹} where
                    open import Relation.Binary.Reasoning.Setoid (Category.Morphism' 𝔹 Y Z) public
                open Category 𝔹 using (~-refl; ~-sym; ~-trans; ∘-respects; id-is-left-id; assoc)



------------------
--- Properties ---
------------------

module _ {𝔸 : Category a b c} {𝔹 : Category α β γ} (F : Functor 𝔸 𝔹) where
    open Category 𝔸 using () renaming (Object to Object₁; Morphism to Morphism₁; _∘_ to _∘₁_)
    open Category 𝔹 using () renaming (Object to Object₂; Morphism to Morphism₂; _∘_ to _∘₂_; _~_ to _~₂_)
    open UniversalMorphism using (generate-morph; A; u)

    -- Universal morphism from F to X
    OppositeUniversalMorphism : (X : Object₂) → Set _
    OppositeUniversalMorphism X = UniversalMorphism X (opposite-functor F)

    {-
        How do we know that the objects are isomorphic?

        Consider the diagram:

        X -u-> F(A)
        |       |      ^ F(h')
        u'      V F(h) |
        ----> F(A')

        where there are two universal morphisms, one at A and one at A'

        Then h' ∘ h is a morphism at A, as is id_A.

        By the universal property, we have
        F(h) ∘ u = u'
        F(h') ∘ u' = u
        thus
        F(h ∘ h') ∘ u = F(id_A) ∘ u = f_u

        by uniqueness of the universal property, h ∘ h' = id_A.
    -}

    distributivity-thing :
        {X Y Z : Category.Object 𝔹} →
        (m₁ : UniversalMorphism X F)
        (m₂ : UniversalMorphism Y F)
        (m₃ : UniversalMorphism Z F) →
        (g : Category.Morphism 𝔹 Y Z) (f : Category.Morphism 𝔹 X Y) →
        mapₘ F (
            generate-morph m₂ (m₃ .A) (m₃ .u ∘₂ g) ∘₁
            generate-morph m₁ (m₂ .A) (m₂ .u ∘₂ f)
        ) ∘₂ (m₁ .u)
        ~₂ m₃ .u ∘₂ (g ∘₂ f)
    distributivity-thing {X} {Y} {Z} m₁ m₂ m₃ g f = begin
        mapₘ F (generate-morph m₂ (m₃ .A) (m₃ .u ∘₂ g) ∘₁ generate-morph m₁ (m₂ .A) (m₂ .u ∘₂ f)) ∘₂ (m₁ .u)            ≈⟨ ∘-respects (Functor.consistent-on-∘ F (generate-morph m₂ (m₃ .A) (m₃ .u ∘₂ g)) (generate-morph m₁ (m₂ .A) (m₂ .u ∘₂ f))) ~-refl ⟩
        (mapₘ F (generate-morph m₂ (m₃ .A) (m₃ .u ∘₂ g)) ∘₂ mapₘ F (generate-morph m₁ (m₂ .A) (m₂ .u ∘₂ f))) ∘₂ (m₁ .u) ≈⟨ assoc (mapₘ F (generate-morph m₂ (m₃ .A) (m₃ .u ∘₂ g))) (mapₘ F (generate-morph m₁ (m₂ .A) (m₂ .u ∘₂ f))) (m₁ .u) ⟩
        mapₘ F (generate-morph m₂ (m₃ .A) (m₃ .u ∘₂ g)) ∘₂ (mapₘ F (generate-morph m₁ (m₂ .A) (m₂ .u ∘₂ f)) ∘₂ (m₁ .u)) ≈⟨ ∘-respects ~-refl (commutes m₁ (m₂ .A) (m₂ .u ∘₂ f)) ⟩
        mapₘ F (generate-morph m₂ (m₃ .A) (m₃ .u ∘₂ g)) ∘₂ ((m₂ .u) ∘₂ f)                                               ≈⟨ ~-sym (assoc (mapₘ F (generate-morph m₂ (m₃ .A) (m₃ .u ∘₂ g))) (m₂ .u) f) ⟩
        (mapₘ F (generate-morph m₂ (m₃ .A) (m₃ .u ∘₂ g)) ∘₂ (m₂ .u)) ∘₂ f                                               ≈⟨ ∘-respects (commutes m₂ (m₃ .A) (m₃ .u ∘₂ g)) ~-refl ⟩
        (m₃ .u ∘₂ g) ∘₂ f                                                                                               ≈⟨ assoc (m₃ .u) g f ⟩
        m₃ .u ∘₂ (g ∘₂ f)                                                                                               ∎
        where
            module _ {X Y : Category.Object 𝔹} where
                open import Relation.Binary.Reasoning.Setoid (Category.Morphism' 𝔹 X Y) public
            open Category 𝔹 using (∘-respects; assoc; ~-refl; ~-sym; ~-trans)
            open UniversalMorphism using (commutes; unique)

    -- This doesn't guarantee the existence of the universal morphism.
    generated-morph-inverse-lemma : {X : Object₂} → (m₁ m₂ : UniversalMorphism X F) → IsSidedInverse 𝔸 (generate-morph m₁ (m₂ .A) (m₂ .u)) (generate-morph m₂ (m₁ .A) (m₁ .u))
    generated-morph-inverse-lemma m₁ m₂ = begin
        (generate-morph m₁ (m₂ .A) (m₂ .u)) ∘₁ (generate-morph m₂ (m₁ .A) (m₁ .u))    ≈⟨ Category.~-sym 𝔸 (m₂ .unique (m₂ .A) (m₂ .u) ((generate-morph m₁ (m₂ .A) (m₂ .u)) ∘₁ (generate-morph m₂ (m₁ .A) (m₁ .u))) pf) ⟩
        (generate-morph m₂ (m₂ .A) (m₂ .u))                                            ≈⟨ UniversalMorphism.generate-morph-id m₂ ⟩
        Category.id 𝔸 (m₂ .A)                                                           ∎
        where
            open UniversalMorphism using (unique; commutes)

            module _ where
                private
                    module _ {Y Z : Category.Object 𝔹} where
                        open import Relation.Binary.Reasoning.Setoid (Category.Morphism' 𝔹 Y Z) public
                open Category 𝔹 using (~-refl; ~-sym; ~-trans; ∘-respects; id-is-left-id; assoc)
                pf : mapₘ F (generate-morph m₁ (m₂ .A) (m₂ .u) ∘₁ generate-morph m₂ (m₁ .A) (m₁ .u)) ∘₂ m₂ .u ~₂ m₂ .u
                pf = begin
                    mapₘ F (generate-morph m₁ (m₂ .A) (m₂ .u) ∘₁ generate-morph m₂ (m₁ .A) (m₁ .u)) ∘₂ m₂ .u                ≈⟨ ∘-respects (Functor.consistent-on-∘ F (generate-morph m₁ (m₂ .A) (m₂ .u)) (generate-morph m₂ (m₁ .A) (m₁ .u))) ~-refl ⟩
                    (mapₘ F (generate-morph m₁ (m₂ .A) (m₂ .u)) ∘₂ mapₘ F (generate-morph m₂ (m₁ .A) (m₁ .u))) ∘₂ m₂ .u     ≈⟨ assoc (mapₘ F (generate-morph m₁ (m₂ .A) (m₂ .u))) (mapₘ F (generate-morph m₂ (m₁ .A) (m₁ .u))) (m₂ .u) ⟩
                    mapₘ F (generate-morph m₁ (m₂ .A) (m₂ .u)) ∘₂ (mapₘ F (generate-morph m₂ (m₁ .A) (m₁ .u)) ∘₂ m₂ .u)     ≈⟨ ∘-respects ~-refl (commutes m₂ (m₁ .A) (m₁ .u)) ⟩
                    mapₘ F (generate-morph m₁ (m₂ .A) (m₂ .u)) ∘₂ m₁ .u                                                     ≈⟨ commutes m₁ (m₂ .A) (m₂ .u) ⟩
                    m₂ .u                                                                                                   ∎


            module _ {X Y : Category.Object 𝔸} where
                open import Relation.Binary.Reasoning.Setoid (Category.Morphism' 𝔸 X Y) public

    unique-up-to-isomorphism : {X : Object₂} → (m₁ m₂ : UniversalMorphism X F) → Isomorphic 𝔸 (m₁ .A) (m₂ .A)
    unique-up-to-isomorphism X→F₁ X→F₂ = generate-morph X→F₁ (X→F₂ .A) (X→F₂ .u) , generate-morph X→F₂ (X→F₁ .A) (X→F₁ .u) , generated-morph-inverse-lemma X→F₁ X→F₂ , generated-morph-inverse-lemma X→F₂ X→F₁

    -- TODO what name?
    back-functor : (∀ (X : Object₂) → UniversalMorphism X F) → Functor 𝔹 𝔸
    back-functor get-universal-morphism = record {
        rawFunctor = record {
            mapₒ = object-map;
            mapₘ-func = λ {X} {Y} → record {
                func = morphism-map {X} {Y};
                respects = λ {f} {g} → morphism-map-respects f g
                }
            };
        isFunctor = record {
            consistent-on-id = λ {X} → begin
                morphism-map (Category.id 𝔹 X)                                                                                              ≈⟨ ~-refl {object-map X} {object-map X} ⟩
                generate-morph (get-universal-morphism X) (get-universal-morphism X .A) (get-universal-morphism X .u ∘₂ Category.id 𝔹 X)    ≈⟨ UniversalMorphism.generate-morph-respects (get-universal-morphism X) (get-universal-morphism X .A) (Category.id-is-right-id 𝔹) ⟩
                generate-morph (get-universal-morphism X) (get-universal-morphism X .A) (get-universal-morphism X .u)                       ≈⟨ UniversalMorphism.generate-morph-id (get-universal-morphism X) ⟩
                Category.id 𝔸 (get-universal-morphism X .A)                                                                                 ≈⟨ ~-refl {object-map X} {object-map X} ⟩
                Category.id 𝔸 (object-map X)                                                                                                ∎;
            consistent-on-∘ = λ {X} {Y} {Z} g f → begin
                morphism-map (g ∘₂ f)                                                                                               ≈⟨ ~-refl {object-map X} {object-map Z} ⟩
                generate-morph (get-universal-morphism X) (get-universal-morphism Z .A) (get-universal-morphism Z .u ∘₂ (g ∘₂ f))   ≈⟨ UniversalMorphism.unique (get-universal-morphism X) (get-universal-morphism Z .A) (get-universal-morphism Z .u ∘₂ (g ∘₂ f)) (generate-morph (get-universal-morphism Y) (get-universal-morphism Z .A) (get-universal-morphism Z .u ∘₂ g) ∘₁ generate-morph (get-universal-morphism X) (get-universal-morphism Y .A) (get-universal-morphism Y .u ∘₂ f)) (pf g f) ⟩
                generate-morph (get-universal-morphism Y) (get-universal-morphism Z .A) (get-universal-morphism Z .u ∘₂ g) ∘₁
                    generate-morph (get-universal-morphism X) (get-universal-morphism Y .A) (get-universal-morphism Y .u ∘₂ f)      ≈⟨ ~-refl {object-map X} {object-map Z} ⟩
                morphism-map g ∘₁ morphism-map f    ∎
            }
        }
        where
            object-map : Category.Object 𝔹 → Category.Object 𝔸
            object-map X = get-universal-morphism X .A

            morphism-map : {X Y : Category.Object 𝔹} → (f : Category.Morphism 𝔹 X Y) → Category.Morphism 𝔸 (object-map X) (object-map Y)
            morphism-map {X} {Y} f = generate-morph (get-universal-morphism X) (get-universal-morphism Y .A) (get-universal-morphism Y .u ∘₂ f)

            morphism-map-respects : {X Y : Category.Object 𝔹} → (f g : Category.Morphism 𝔹 X Y) → Category._~_ 𝔹 f g → Category._~_ 𝔸 (morphism-map f) (morphism-map g)
            morphism-map-respects {X} {Y} f g f~g = UniversalMorphism.generate-morph-respects (get-universal-morphism X) (get-universal-morphism Y .A) (∘-respects ~-refl f~g)
                where
                    open Category 𝔹 using (∘-respects; ~-refl; ~-sym; ~-trans)

            pf : {X Y Z : Category.Object 𝔹} → (g : Category.Morphism 𝔹 Y Z) (f : Category.Morphism 𝔹 X Y) →
                mapₘ F (
                    generate-morph (get-universal-morphism Y) (get-universal-morphism Z .A) (get-universal-morphism Z .u ∘₂ g) ∘₁
                    generate-morph (get-universal-morphism X) (get-universal-morphism Y .A) (get-universal-morphism Y .u ∘₂ f)
                ) ∘₂ (get-universal-morphism X .u) ~₂ get-universal-morphism Z .u ∘₂ (g ∘₂ f)
            pf {X} {Y} {Z} g f = distributivity-thing (get-universal-morphism X) (get-universal-morphism Y) (get-universal-morphism Z) g f

            module _ {X Y : Category.Object 𝔸} where
                open import Relation.Binary.Reasoning.Setoid (Category.Morphism' 𝔸 X Y) public
                open Category 𝔸 using (∘-respects; ~-refl; ~-sym; ~-trans) public

    -- TODO show that back-functor is adjoint to F


----------------------------------
--- Example Universal Morphism ---
----------------------------------

-- TODO: product and sum as universal morphisms.