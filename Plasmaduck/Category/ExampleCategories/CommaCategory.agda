open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; inspect; cong; Reveal_·_is_; [_]) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Relation.Binary using (Setoid; Rel; IsEquivalence; Transitive)
open import Function using (flip; _∋_; Congruent)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (z≤n; s≤s)
open import Data.Nat.Properties using (<-irrefl; ≤-<-trans)
open import Data.Fin using (Fin; zero; suc; _<_; toℕ; fromℕ<; _≤_)

open import Plasmaduck.SetoidExperiment.SetoidMachinery using (SetoidFunction; _←_; discrete-setoid; indiscrete-setoid; from-discrete-cong; into-indiscrete-cong)
open import Plasmaduck.Relation.RelationVector using (module RelationList; module Flattening; module Mapping; tree→list; branch→cons; cons→branch; trans-flatten-branch; tree→list-branch→cons-same; _++_; []; _∷_; _∷'_; foldl)
open import Plasmaduck.Function.Properties using (Congruent₂)
open import Plasmaduck.Category.Category using (RawCategory; Category; ExtraRawFunctor; Functor; module CategoryProperties; module MakeFunctor; module MakeFunctor'; opposite-category)
open import Plasmaduck.Category.Diagram using (module CommutativeSquare; module Diagram)
open import Plasmaduck.Category.CommutativeSquare using (commutative-square-compose)



module Plasmaduck.Category.ExampleCategories.CommaCategory where

variable
    a b c α β γ ℓ₁ ℓ₂ ℓ₃ : Level


open CommutativeSquare using (commutative-square; CommutativeSquareBaseMorphism; m₀₁; m₁₃; m₀₂; m₂₃; one; two; three; module CommutativeSquareCoreProperty)



module CommaCategory
    {𝔸 : Category a b c} {𝔹 : Category α β γ} {ℂ : Category ℓ₁ ℓ₂ ℓ₃}
    (S : Functor 𝔸 ℂ) (T : Functor 𝔹 ℂ)
    where

    open Category using (Object; Morphism; id)
    open Functor using (mapₒ; mapₘ)

    _↓'_ : RawCategory _ _ _
    _↓'_ = record {
        Object = Obj;
        Morphism' = λ x y → record {
            Carrier = Morph x y;
            _≈_ = ~-Morph;
            isEquivalence = ~-Morph-eq
            };
        id = identity;
        compose = record {
            func = concat;
            respects = λ g₁~g₂ f₁~f₂ →
                Category.∘-respects 𝔸 (g₁~g₂ .proj₁) (f₁~f₂ .proj₁) ,
                Category.∘-respects 𝔹 (g₁~g₂ .proj₂) (f₁~f₂ .proj₂)
            }
        }
        where

            Obj = Σ (𝔸 .Object) λ x → Σ (𝔹 .Object) λ y → (Morphism ℂ (S .mapₒ x) (T .mapₒ y))

            map-obj : Obj → Obj → commutative-square .Object → ℂ .Object
            map-obj (A , B , h) (A' , B' , h') zero = S .mapₒ A
            map-obj (A , B , h) (A' , B' , h') one = S .mapₒ A'
            map-obj (A , B , h) (A' , B' , h') two = T .mapₒ B
            map-obj (A , B , h) (A' , B' , h') three = T .mapₒ B'

            map-morph : ((A , B , h) (A' , B' , h') : Obj) → (Morphism 𝔸 A A') → (Morphism 𝔹 B B') → {x y : commutative-square .Object} → CommutativeSquareBaseMorphism x y → Morphism ℂ (map-obj (A , B , h) (A' , B' , h') x) (map-obj (A , B , h) (A' , B' , h') y)
            map-morph (A , B , h) (A' , B' , h') f g m₀₁ = mapₘ S f
            map-morph (A , B , h) (A' , B' , h') f g m₁₃ = h'
            map-morph (A , B , h) (A' , B' , h') f g m₀₂ = h
            map-morph (A , B , h) (A' , B' , h') f g m₂₃ = mapₘ T g

            RawMorph : Obj → Obj → Set _
            RawMorph (A , B , h) (A' , B' , h') = (Morphism 𝔸 A A') × (Morphism 𝔹 B B')

            Morph : Obj → Obj → Set _
            Morph (A , B , h) (A' , B' , h') = Σ (Morphism 𝔸 A A') λ f → Σ (Morphism 𝔹 B B') λ g → Diagram.IsValidDiagramEmbedding CommutativeSquareBaseMorphism ℂ (map-obj (A , B , h) (A' , B' , h')) (map-morph (A , B , h) (A' , B' , h') f g)

            get-raw-morph : {x y : Obj} → Morph x y → RawMorph x y
            get-raw-morph (f , g , _) = f , g

            ~-Morph : {x y : Obj} → Rel (Morph x y) _
            ~-Morph {x} {y} (f₁ , g₁ , _) (f₂ , g₂ , _) = Category._~_ 𝔸 f₁ f₂ × Category._~_ 𝔹 g₁ g₂

            ~-Morph-eq : {x y : Obj} → IsEquivalence (~-Morph {x} {y})
            ~-Morph-eq {A , B , _} {A' , B' , _} = record {
                refl = refl₁ , refl₂;
                sym = λ (f₁~f₂ , g₁~g₂) → sym₁ f₁~f₂ , sym₂ g₁~g₂;
                trans = λ (f₁~f₂ , g₁~g₂) (f₂~f₃ , g₂~g₃) → trans₁ f₁~f₂ f₂~f₃ , trans₂ g₁~g₂ g₂~g₃
                }
                where
                    open IsEquivalence (Category.~-eq 𝔸 A A') renaming (refl to refl₁; sym to sym₁; trans to trans₁)
                    open IsEquivalence (Category.~-eq 𝔹 B B') renaming (refl to refl₂; sym to sym₂; trans to trans₂)

            module DiagramEmbed {x y : Obj} ((f , g) : RawMorph x y) where
                diagram-embedₒ : Fin 4 → Category.Object ℂ
                diagram-embedₒ = map-obj x y

                diagram-embedₘ : {i j : Fin 4} → Category.Morphism commutative-square i j → Category.Morphism ℂ (diagram-embedₒ i) (diagram-embedₒ j)
                diagram-embedₘ = Diagram.diagram-embedding CommutativeSquareBaseMorphism ℂ (map-obj x y) (map-morph x y f g)

                IsCongruent : Set _
                IsCongruent = Diagram.IsValidDiagramEmbedding CommutativeSquareBaseMorphism ℂ (map-obj x y) (map-morph x y f g)

            module _ {x y : Obj} ((f , g , is-valid) : Morph x y) where
                morph→diagram-functor : Functor commutative-square ℂ
                morph→diagram-functor = Diagram.make-diagram-functor CommutativeSquareBaseMorphism ℂ (map-obj x y) (map-morph x y f g) is-valid

            open Category commutative-square using () renaming (_∘_ to _∘□_)
            open Category 𝔸                  using () renaming (_∘_ to _∘a_)
            open Category 𝔹                  using () renaming (_∘_ to _∘b_)
            open Category ℂ                  using () renaming (_∘_ to _∘c_)

            identity : (x : Obj) → Morph x x
            identity obj@(A , B , h) = id 𝔸 A , id 𝔹 B , P→commutative thing
                where
                    open DiagramEmbed {x = obj} {y = obj} (id 𝔸 A , id 𝔹 B) using (diagram-embedₒ; diagram-embedₘ)
                    open CommutativeSquareCoreProperty (ℂ .Category.rawCategory) (record {mapₒ = diagram-embedₒ; mapₘ = diagram-embedₘ}) using (P→commutative; P)

                    -- Note to future self: the type of P here is diagram-embedₘ of a list of like diagram-inj calls,
                    -- but since the list is explicit, it evaluates down to _∘_ in the target category
                    thing : P
                    thing = begin
                        diagram-embedₘ (
                            (Plasmaduck.Category.Diagram.diagram-inj CommutativeSquareBaseMorphism m₁₃) ∘□
                            (Plasmaduck.Category.Diagram.diagram-inj CommutativeSquareBaseMorphism m₀₁)
                            )                                                                                   ≈⟨ refl ⟩
                        h ∘c (mapₘ S (id 𝔸 A))                                                                  ≈⟨ Category.∘-respects ℂ refl (Functor.consistent-on-id S) ⟩
                        h ∘c (id ℂ (mapₒ S A))                                                                  ≈⟨ Category.id-is-right-id ℂ ⟩
                        h                                                                                       ≈⟨ sym (Category.id-is-left-id ℂ) ⟩
                        (id ℂ (mapₒ T B)) ∘c h                                                                  ≈⟨ Category.∘-respects ℂ (sym (Functor.consistent-on-id T)) refl ⟩
                        (mapₘ T (id 𝔹 B)) ∘c h                                                                  ≈⟨ refl ⟩
                        diagram-embedₘ (
                                (Plasmaduck.Category.Diagram.diagram-inj CommutativeSquareBaseMorphism m₂₃) ∘□
                                (Plasmaduck.Category.Diagram.diagram-inj CommutativeSquareBaseMorphism m₀₂)
                            )                                                                                   ∎
                        where
                            open import Relation.Binary.Reasoning.Setoid (Category.Morphism' ℂ (diagram-embedₒ zero) (diagram-embedₒ three))
                            module _ {X Y : Category.Object ℂ} where
                                open Setoid (Category.Morphism' ℂ X Y) using (refl; sym; trans) public


            concat : {x y z : Obj} → Morph y z → Morph x y → Morph x z
            concat {x@(_ , _ , m₁)} {y@(_ , _ , m₂)} {z@(_ , _ , m₃)} (f' , g' , cong') (f , g , cong) = f' ∘a f , g' ∘b g , P→commutative pf
                where
                    {-
                        x       y       z

                        * --f-> * -f'-> *
                        |       |       |
                        m₁      m₂      m₃
                        |       |       |
                        V       V       V
                        * --g-> * -g'-> *
                    -}

                    open DiagramEmbed {x = x} {y = z} (f' ∘a f , g' ∘b g) using (diagram-embedₒ; diagram-embedₘ)
                    open CommutativeSquareCoreProperty (ℂ .Category.rawCategory) (record {mapₒ = diagram-embedₒ; mapₘ = diagram-embedₘ}) using (P→commutative; P)

                    module _ {a b : Category.Object ℂ} where
                        open import Relation.Binary.Reasoning.Setoid (Category.Morphism' ℂ a b) public
                        open Setoid (Category.Morphism' ℂ a b) using (refl; sym; trans) public

                    pf : P
                    pf = begin
                        diagram-embedₘ (
                            (Plasmaduck.Category.Diagram.diagram-inj CommutativeSquareBaseMorphism m₁₃) ∘□
                            (Plasmaduck.Category.Diagram.diagram-inj CommutativeSquareBaseMorphism m₀₁)
                            )                                                                                   ≈⟨ refl ⟩
                        m₃ ∘c (Functor.mapₘ S (f' ∘a f))                                                        ≈⟨ Category.∘-respects ℂ refl (Functor.consistent-on-∘ S f' f) ⟩
                        m₃ ∘c ((Functor.mapₘ S f') ∘c (Functor.mapₘ S f))                                       ≈⟨ commutative-square-compose (opposite-category ℂ) (cong' (m₀₁ ∷ m₁₃ ∷ []) (m₀₂ ∷ m₂₃ ∷ []) tt) (cong (m₀₁ ∷ m₁₃ ∷ []) (m₀₂ ∷ m₂₃ ∷ []) tt) ⟩
                        ((Functor.mapₘ T g') ∘c (Functor.mapₘ T g)) ∘c m₁                                       ≈⟨ Category.∘-respects ℂ (sym (Functor.consistent-on-∘ T g' g)) refl ⟩
                        (Functor.mapₘ T (g' ∘b g)) ∘c m₁                                                        ≈⟨ refl ⟩
                        diagram-embedₘ (
                                (Plasmaduck.Category.Diagram.diagram-inj CommutativeSquareBaseMorphism m₂₃) ∘□
                                (Plasmaduck.Category.Diagram.diagram-inj CommutativeSquareBaseMorphism m₀₂)
                            )                                                                                   ∎

    _↓_ : Category _ _ _
    _↓_ = record {
        rawCategory = _↓'_;
        isCategory = record {
            assoc = λ (h₁ , h₂ , _) (g₁ , g₂ , _) (f₁ , f₂ , _) → Category.assoc 𝔸 h₁ g₁ f₁ , Category.assoc 𝔹 h₂ g₂ f₂;
            id-is-left-id = Category.id-is-left-id 𝔸 , Category.id-is-left-id 𝔹;
            id-is-right-id = Category.id-is-right-id 𝔸 , Category.id-is-right-id 𝔹
            }
        }
open CommaCategory public