open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Relation.Binary.PropositionalEquality using (_≡_) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open import Relation.Binary using (Setoid; Rel; IsEquivalence)
open import Function using (Congruent)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Bool using (Bool; true; false)

open import Plasmaduck.SetoidExperiment.SetoidMachinery using (SetoidFunction; _←_)
open import Plasmaduck.Category.Category using (Category; Functor; RawFunctor'; opposite-category; opposite-functor; Isomorphic; IsSidedInverse)
open import Plasmaduck.Util.Case using (case_of_)
open import Plasmaduck.Category.Functor.SimpleFunctors using (id-functor)
open import Plasmaduck.Category.Functor.Properties using (FunctorSetoid; Functor-compose-func)
open import Plasmaduck.Category.CommutativeSquare using (commutative-square-compose)
open import Plasmaduck.Category.ExampleCategories.FunctorCategory using (FunctorCategory; _^_; Δ; product-category)
open import Plasmaduck.Category.ExampleCategories.SimpleCategories using (discrete-category; 𝐒𝐞𝐭)
open import Plasmaduck.Category.Functor.NaturalTransformation using (NaturalTransformation)
open import Plasmaduck.Data.Product using (Σ≡)
open import Plasmaduck.Util.TypeChange using (change-type-elim)



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
        - for every B, f, there is a *unique* h such that the diagram commutes.
    -}
    record RawUniversalMorphism (X : Object₂) (F : Functor 𝔸 𝔹) : Set (a ⊔ b ⊔ β) where
        field
            A : Object₁
            u : Morphism₂ X (mapₒ F A)

            -- This function generates h in the above diagram.
            -- Together with IsUniversalMorphism, it can be shown that this is a setoid function.
            -- See generate-morph-respects and generate-morph' below.
            -- TODO rename this to factor-morph
            generate-morph : ∀ (B : Object₁) (f : Morphism₂ X (mapₒ F B)) → Morphism₁ A B

    module _ {X : Object₂} {F : Functor 𝔸 𝔹} (rawUniversalMorphism : RawUniversalMorphism X F) where
        open RawUniversalMorphism rawUniversalMorphism

        commutes-type =
            ∀ (B : Object₁) (f : Morphism₂ X (mapₒ F B)) →
            mapₘ F (generate-morph B f) ∘₂ u ~₂ f

        unique-type =
            ∀ (B : Object₁) (f : Morphism₂ X (mapₒ F B)) →
            (h : Morphism₁ A B) →
            mapₘ F h ∘₂ u ~₂ f →
            generate-morph B f ~₁ h

        record IsUniversalMorphism : Set (a ⊔ b ⊔ c ⊔ β ⊔ γ) where
            field
                commutes : commutes-type
                unique : unique-type

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

    {-
        Universal morphism from F to X:

            𝔸               𝔹

        X <--u--- F(A)      A
        ^          ^        ^
        |          |        |
        f         F(h)      h
        |          |        |
        --------- F(B)      B

        which just turns all the morphisms around,
        which is the same as using the opposite categories and the opposite functor.
    -}

    -- TODO maybe call this one a terminal universal morphism and the other one an initial universal morphism?
    -- Universal morphism from F to X
    OppositeUniversalMorphism : (X : Object₂) → Set _
    OppositeUniversalMorphism X = UniversalMorphism X (opposite-functor F)

    OppositeRawUniversalMorphism : (X : Object₂) → Set _
    OppositeRawUniversalMorphism X = RawUniversalMorphism X (opposite-functor F)

    universal-morphism-everywhere-type : Set _
    universal-morphism-everywhere-type = ∀ (X : Object₂) → UniversalMorphism X F

    opposite-universal-morphism-everywhere-type : Set _
    opposite-universal-morphism-everywhere-type = ∀ (X : Object₂) → OppositeUniversalMorphism X

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

    -- TODO this isn't distributivity, it's like, associativity?
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
        (mapₘ F (generate-morph m₂ (m₃ .A) (m₃ .u ∘₂ g)) ∘₂ mapₘ F (generate-morph m₁ (m₂ .A) (m₂ .u ∘₂ f))) ∘₂ (m₁ .u)  ≈⟨ commutative-square-compose 𝔹 (commutes m₁ (m₂ .A) (m₂ .u ∘₂ f)) (commutes m₂ (m₃ .A) (m₃ .u ∘₂ g)) ⟩
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

    -- generate-morph-id' : (X : Object₁) → (m : UniversalMorphism (mapₒ F X) F) → IsSidedInverse 𝔹 (mapₘ F (generate-morph m X (Category.id 𝔹 (mapₒ F X)))) (m .u)
    -- generate-morph-id' X m = IsUniversalMorphism.commutes
    --   (m .UniversalMorphism.isUniversalMorphism) X
    --   (Plasmaduck.Category.Category.RawCategory.id
    --    (Category.rawCategory 𝔹)
    --    (Plasmaduck.Category.Category.RawFunctor.mapₒ
    --     (Functor.rawFunctor F) X))

    -- TODO what name?
    induced-functor : universal-morphism-everywhere-type → Functor 𝔹 𝔸
    induced-functor get-universal-morphism = record {
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

    -- TODO show that induced-functor is adjoint to F

-- module _ {𝔸 : Category a b c} {𝔹 : Category α β γ} (F : Functor 𝔸 𝔹) where
--     open Functor using (mapₒ; mapₘ)
--     open UniversalMorphism using (generate-morph; u; A)
--     open Category 𝔸 using () renaming (_∘_ to _∘₁_)
--     open Category 𝔹 using () renaming (_∘_ to _∘₂_)

--     invert-universal-morphism : (pf : universal-morphism-everywhere-type F) → opposite-universal-morphism-everywhere-type (induced-functor F pf)
--     invert-universal-morphism get-universal-morphism X = record {
--         rawUniversalMorphism = raw-univ-morph;
--         isUniversalMorphism = record {
--             commutes = commutes-pf;
--             unique = unique-pf
--             }
--         }
--         where
--             {-
--                 let G = induced-functor F _

--                 We have this universal morphism for all Q:

--                 𝔹

--                 Q --u_Q-> FG(Q)
--                 |           |
--                 f           h_Q,B,f
--                 |           V
--                 --------> FG(B)



--             -}
--             raw-univ-morph : OppositeRawUniversalMorphism (induced-functor F get-universal-morphism) X
--             raw-univ-morph = record {
--                 A = mapₒ F X;
--                 u = generate-morph (get-universal-morphism (mapₒ F X)) X (Category.id 𝔹 (mapₒ F X));
--                 generate-morph = λ B f → mapₘ F f ∘₂ get-universal-morphism B .u
--                 }

--             commutes-pf : commutes-type raw-univ-morph
--             commutes-pf B f = -- UniversalMorphism.unique (get-universal-morphism ?) ? ? ? ?
--                 begin
--                 (RawUniversalMorphism.u raw-univ-morph) ∘₁ (mapₘ (induced-functor F get-universal-morphism) (RawUniversalMorphism.generate-morph raw-univ-morph B f))                                                                                                           ≈⟨ refl ⟩
--                 (generate-morph (get-universal-morphism (mapₒ F X)) X (Category.id 𝔹 (mapₒ F X))) ∘₁ (mapₘ (induced-functor F get-universal-morphism) (mapₘ F f ∘₂ u (get-universal-morphism B)))                                                                               ≈⟨ refl ⟩
--                 (generate-morph (get-universal-morphism (mapₒ F X)) X (Category.id 𝔹 (mapₒ F X))) ∘₁ (generate-morph (get-universal-morphism B) (get-universal-morphism (mapₒ F X) .A) (get-universal-morphism (mapₒ F X) .u ∘₂ (mapₘ F f ∘₂ get-universal-morphism B .u)))     ≈⟨ {! f  !} ⟩
--                 f ∎
--                 where
--                     module _ {X Y : Category.Object 𝔸} where
--                         open import Relation.Binary.Reasoning.Setoid (Category.Morphism' 𝔸 X Y) public
--                         open Setoid (Category.Morphism' 𝔸 X Y) using (refl; sym; trans) public

--             unique-pf : unique-type raw-univ-morph
--             unique-pf B f h pf = begin
--                 RawUniversalMorphism.generate-morph raw-univ-morph B f  ≈⟨ refl ⟩
--                 mapₘ F f ∘₂ get-universal-morphism B .u                 ≈⟨ {!   !} ⟩
--                 h                                                       ∎
--                 where
--                     module _ {X Y : Category.Object 𝔹} where
--                         open import Relation.Binary.Reasoning.Setoid (Category.Morphism' 𝔹 X Y) public
--                         open Setoid (Category.Morphism' 𝔹 X Y) using (refl; sym; trans) public


----------------------------------
--- Example Universal Morphism ---
----------------------------------

module Product (ℓ : Level) where

    all-universal-morphisms : ∀ (X : product-category (𝐒𝐞𝐭 ℓ) .Category.Object) → OppositeUniversalMorphism (Δ (discrete-category Bool) (𝐒𝐞𝐭 ℓ)) X
    all-universal-morphisms X×Y = record {
        rawUniversalMorphism = record {
            A = X × Y;
            u = record {
                rawNaturalTransformation = record { η = η };
                isNaturalTransformation = record { commutes = commutes-proof }
                };
            generate-morph = λ A' g b → (g .NaturalTransformation.η false b) , (g .NaturalTransformation.η true b)
            };
        isUniversalMorphism = record {
            commutes = λ {
                A' f false b → ≡-refl;
                A' f true b → ≡-refl
                };
            unique = λ A' f h pf b → Σ≡ (≡-sym (pf false b)) (≡-trans (≡-sym (pf true b)) (≡-sym (change-type-elim _)))
            }
        }
        where
            open Category (𝐒𝐞𝐭 ℓ) using (_∘_; _~_)

            𝐁 = discrete-category Bool
            F' = opposite-functor (Δ 𝐁 (𝐒𝐞𝐭 ℓ))

            X = mapₒ X×Y false
            Y = mapₒ X×Y true

            η : (b : Category.Object 𝐁) →
                Category.Morphism (𝐒𝐞𝐭 ℓ)
                (mapₒ (mapₒ F' (X × Y)) b)
                (mapₒ X×Y b)
            η false = proj₁
            η true = proj₂

            commutes-proof : {X₁ Y₁ : Bool} (f : Category.Morphism 𝐁 X₁ Y₁) →
                η Y₁ ∘ mapₘ (mapₒ F' (X × Y)) f ~
                mapₘ X×Y f ∘ η X₁
            commutes-proof {false} {false} ≡-refl (x , y) =
                (η false ∘ mapₘ (mapₒ F' (X × Y)) (≡-refl {x = true})) (x , y)  ≡⟨ ≡-refl ⟩
                (η false ∘ Category.id (𝐒𝐞𝐭 ℓ) (X × Y)) (x , y)                 ≡⟨ ≡-refl ⟩
                η false (x , y)                                                 ≡⟨ ≡-refl ⟩
                x                                                               ≡⟨ ≡-refl ⟩
                Category.id (𝐒𝐞𝐭 ℓ) X x                                         ≡⟨ ≡-sym (Functor.consistent-on-id X×Y x) ⟩
                mapₘ X×Y ≡-refl x                                               ≡⟨ ≡-refl ⟩
                (mapₘ X×Y ≡-refl ∘ η false) (x , y)                             ∎
                where open ≡-Reasoning
            commutes-proof {true} {true} ≡-refl (x , y) = ≡-sym (Functor.consistent-on-id X×Y y)

-- TODO: product and sum as universal morphisms.
