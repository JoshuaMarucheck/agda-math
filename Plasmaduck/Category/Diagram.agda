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
open import Plasmaduck.Category.Category using (RawCategory; Category; ExtraRawFunctor; Functor; module CategoryProperties; module MakeFunctor; module MakeFunctor')



{-
    Diagrams using PairwiseRelationList. This makes them subject to the slowness of _++_,
    but as long as the lists are only 3-4 elements long (as is common in most explicit diagrams),
    the difference should be negligible, if lists aren't simply faster.
-}
module Plasmaduck.Category.Diagram where

variable
    a b c α β γ ℓ₁ ℓ₂ ℓ₃ : Level

make-commutative-diagram' :
    {Object : Set a} →
    (Morphism : Object → Object → Set b) →
    (id : (x : Object) → Morphism x x) →
    (_∘_ : {x y z : Object} → Morphism y z → Morphism x y → Morphism x z) →
    Category a b lzero
make-commutative-diagram' {Object = Object} Morphism id _∘_ = record {
    rawCategory = record {
        Object = Object;
        Morphism' = λ x y → indiscrete-setoid (Morphism x y);
        id = id;
        compose = record { func = _∘_ }
        };
    isCategory = record {}
    }

module _
    {Object : Set a}
    (BaseMorphism : Object → Object → Set b)
    where
    open RelationList using (PairwiseRelationList)

    make-commutative-diagram : Category a (a ⊔ b) lzero
    make-commutative-diagram = make-commutative-diagram' Morphism id _∘ₘ_
        where
            Morphism : Object → Object → Set (a ⊔ b)
            Morphism = PairwiseRelationList BaseMorphism

            id : (x : Object) → Morphism x x
            id x = []

            _∘ₘ_ : {x y z : Object} → Morphism y z → Morphism x y → Morphism x z
            _∘ₘ_ = flip _++_
            infixr 9 _∘ₘ_

    diagram-inj : {x y : Object} → BaseMorphism x y → Category.Morphism make-commutative-diagram x y
    diagram-inj = _∷ []


commutative-diagram-commutes :
    {Object : Set a} →
    {Morphism : Object → Object → Set b} →
    {id : (x : Object) → Morphism x x} →
    {_∘_ : {x y z : Object} → Morphism y z → Morphism x y → Morphism x z} →
    CategoryProperties.IsCommutative (make-commutative-diagram' Morphism id _∘_)
commutative-diagram-commutes _ _ = tt


module Diagram
    {Object : Set a}
    (BaseMorphism : Object → Object → Set b)
    (TargetCategory : Category α β γ)
    (mapₒ : Object → TargetCategory .Category.Object)
    (mapₘ : {x y : Object} → BaseMorphism x y → Category.Morphism TargetCategory (mapₒ x) (mapₒ y))
    where
    private
        DomainCategory : Category a (a ⊔ b) lzero
        DomainCategory = make-commutative-diagram BaseMorphism

        DomainMorphism : (x y : Object) → Set (a ⊔ b)
        DomainMorphism x y = Category.Morphism DomainCategory x y

        _~₂_ = Category._~_ TargetCategory

    has-morphism-in-target : Object → Object → Set _
    has-morphism-in-target x y = Category.Morphism TargetCategory (mapₒ x) (mapₒ y)

    open Mapping {A = Object} {_~_ = BaseMorphism} {_#_ = has-morphism-in-target} Function.id mapₘ using (map-cons)

    diagram-embedding : {x y : Object} → (Category.Morphism DomainCategory x y) → Category.Morphism TargetCategory (mapₒ x) (mapₒ y)
    diagram-embedding {x} {y} (x~z ∷ zy) = foldl has-morphism-in-target (flip (Category._∘_ TargetCategory)) (map-cons (x~z ∷' zy))
    diagram-embedding {x} {.x} [] = Category.id TargetCategory (mapₒ x)

    open MakeFunctor DomainCategory TargetCategory mapₒ diagram-embedding using (IsValidEmbedding; make-functor)
    open MakeFunctor DomainCategory TargetCategory mapₒ diagram-embedding using (IsCongruent) public

    IsValidDiagramEmbedding : Set _
    IsValidDiagramEmbedding = IsValidEmbedding

    make-diagram-functor : IsValidDiagramEmbedding → Functor DomainCategory TargetCategory
    make-diagram-functor = make-functor



-----------------------------------
--- Some examples of Categories ---
-----------------------------------

-- TODO Maybe I should figure out how to write down universal properties as tiny explicit categories or something
module ExampleCategories where
    open import Function using (_∘_)

    -- A diagram is a category, typically one with only a few objects. The diagram is injected into other categories via functor.
    -- A commutative diagram is one where all morphisms between two objects are equal.

    {-
        0 ----> 1
        |       |
        V       V
        2 ----> 3
    -}

    private
        pattern one = suc zero
        pattern two = suc (suc zero)
        pattern three = suc (suc (suc zero))


    data CommutativeSquareBaseMorphism : (Fin 4) → (Fin 4) → Set where
        m₀₁ : CommutativeSquareBaseMorphism zero one
        m₀₂ : CommutativeSquareBaseMorphism zero two
        m₁₃ : CommutativeSquareBaseMorphism one three
        m₂₃ : CommutativeSquareBaseMorphism two three

    commutative-square : Category lzero lzero lzero
    commutative-square = make-commutative-diagram CommutativeSquareBaseMorphism

    module CommutativeSquareCoreProperty
        (Target : RawCategory a b c)
        (F : ExtraRawFunctor (commutative-square .Category.rawCategory) Target)
        where
        open ExtraRawFunctor F using (mapₒ; mapₘ)
        open RawCategory Target using (Object; Morphism; _~_; ~-refl; ~-sym; ~-trans) renaming (_∘_ to _∘₂_)
        open Category commutative-square using () renaming (_∘_ to _∘₁_)

        open RelationList CommutativeSquareBaseMorphism using (PairwiseRelationListCons)

        private
            inj : {i j : Fin 4} → CommutativeSquareBaseMorphism i j → Category.Morphism commutative-square i j
            inj = diagram-inj CommutativeSquareBaseMorphism

        P : Set _
        P = mapₘ (inj m₁₃ ∘₁ inj m₀₁) ~ mapₘ (inj m₂₃ ∘₁ inj m₀₂)
        thing : MakeFunctor'.IsCongruent (commutative-square .Category.rawCategory) Target mapₒ mapₘ → P
        thing cong = cong {zero} {(suc ∘ suc ∘ suc) zero} {x = inj m₁₃ ∘₁ inj m₀₁} {y = inj m₂₃ ∘₁ inj m₀₂} tt

        incr-lemma' : {i j : Fin 4} → PairwiseRelationListCons i j → i < j
        incr-lemma' (m₀₁ ∷' []) = s≤s z≤n
        incr-lemma' (m₀₂ ∷' []) = s≤s z≤n
        incr-lemma' (m₁₃ ∷' []) = s≤s (s≤s z≤n)
        incr-lemma' (m₂₃ ∷' []) = s≤s (s≤s (s≤s z≤n))
        incr-lemma' (m₀₁ ∷' m₁₃ ∷ []) = s≤s z≤n
        incr-lemma' (m₀₂ ∷' m₂₃ ∷ []) = s≤s z≤n

        thing' : P → MakeFunctor'.IsCongruent (commutative-square .Category.rawCategory) Target mapₒ mapₘ
        thing' pf {x = _} {_} {[]} {[]} tt = ~-refl
        thing' pf {x = _} {_} {[]} {x ∷ y} tt = ⊥-elim (<-irrefl ≡-refl (incr-lemma' (x ∷' y)))
        thing' pf {x = _} {_} {x ∷ y} {[]} tt = ⊥-elim (<-irrefl ≡-refl (incr-lemma' (x ∷' y)))
        thing' pf {x = _} {_} {m₀₁ ∷ m₁₃ ∷ []} {m₀₁ ∷ m₁₃ ∷ []} tt = ~-refl
        thing' pf {x = _} {_} {m₀₁ ∷ m₁₃ ∷ []} {m₀₂ ∷ m₂₃ ∷ []} tt = pf
        thing' pf {x = _} {_} {m₀₂ ∷ m₂₃ ∷ []} {m₀₁ ∷ m₁₃ ∷ []} tt = ~-sym pf
        thing' pf {x = _} {_} {m₀₂ ∷ m₂₃ ∷ []} {m₀₂ ∷ m₂₃ ∷ []} tt = ~-refl
        thing' pf {x = _} {_} {m₀₁ ∷ []} {m₀₁ ∷ []} tt = ~-refl
        thing' pf {x = _} {_} {m₀₁ ∷ []} {m₀₁ ∷ m₁₃ ∷ () ∷ y} tt
        thing' pf {x = _} {_} {m₀₁ ∷ []} {m₀₂ ∷ m₂₃ ∷ () ∷ y} tt
        thing' pf {x = _} {_} {m₀₂ ∷ []} {m₀₁ ∷ m₁₃ ∷ () ∷ y} tt
        thing' pf {x = _} {_} {m₀₂ ∷ []} {m₀₂ ∷ []} tt = ~-refl
        thing' pf {x = _} {_} {m₀₂ ∷ []} {m₀₂ ∷ m₂₃ ∷ () ∷ y} tt
        thing' pf {x = _} {_} {m₁₃ ∷ []} {m₁₃ ∷ []} tt = ~-refl
        thing' pf {x = _} {_} {m₂₃ ∷ []} {m₂₃ ∷ []} tt = ~-refl

open ExampleCategories public
