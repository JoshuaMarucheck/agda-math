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
open import Plasmaduck.Relation.Operator using (transitive-closure-fold)
open import Plasmaduck.Relation.RelationVector using (module RelationTree; module RelationList; module Flattening; module Mapping; tree→list; branch→cons; cons→branch; trans-flatten-branch; PairwiseRelationList; PairwiseRelationListCons; []; _∷_; init; cons; tree→list-branch→cons-same)
open import Plasmaduck.Util.Case using (case_of_)
open import Plasmaduck.Function.Properties using (Congruent₂)
open import Plasmaduck.Category.Category using (RawCategory; Category; ExtraRawFunctor; Functor; module CategoryProperties; module MakeFunctor; module MakeFunctor')



module Plasmaduck.Category.TreeDiagram where

variable
    a b c α β γ ℓ₁ ℓ₂ ℓ₃ : Level



make-commutative-diagram' :
    (Object : Set a) →
    (Morphism : Object → Object → Set b) →
    (id : (x : Object) → Morphism x x) →
    (_∘_ : {x y z : Object} → Morphism y z → Morphism x y → Morphism x z) →
    Category a b lzero
make-commutative-diagram' Object Morphism id _∘_ = record {
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

    make-commutative-diagram : Category a (a ⊔ b) lzero
    make-commutative-diagram = make-commutative-diagram' Object Morphism id _∘ₘ_
        where
            open import Plasmaduck.Relation.Operator (discrete-setoid Object) using (reflexive-transitive-closure; reflexive-transitive-closure-is-extensive; reflexive-transitive-closure-is-reflexive; reflexive-transitive-closure-is-transitive)

            Morphism : Object → Object → Set (a ⊔ b)
            Morphism = reflexive-transitive-closure BaseMorphism

            id : (x : Object) → Morphism x x
            id x = reflexive-transitive-closure-is-reflexive BaseMorphism

            _∘ₘ_ : {x y z : Object} → Morphism y z → Morphism x y → Morphism x z
            _∘ₘ_ = flip (reflexive-transitive-closure-is-transitive BaseMorphism)
            infixr 9 _∘ₘ_

    diagram-inj : {x y : Object} → BaseMorphism x y → Category.Morphism make-commutative-diagram x y
    diagram-inj = reflexive-transitive-closure-is-extensive BaseMorphism
        where open Plasmaduck.Relation.Operator (discrete-setoid Object)


commutative-diagram-commutes :
    {Object : Set a} →
    {Morphism : Object → Object → Set b} →
    {id : (x : Object) → Morphism x x} →
    {_∘_ : {x y z : Object} → Morphism y z → Morphism x y → Morphism x z} →
    CategoryProperties.IsCommutative (make-commutative-diagram' Object Morphism id _∘_)
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

    diagram-embedding : {x y : Object} → (Category.Morphism DomainCategory x y) → Category.Morphism TargetCategory (mapₒ x) (mapₒ y)
    diagram-embedding {x} {y} (inj₁ x~y) = transitive-closure-fold (discrete-setoid Object) BaseMorphism (λ i j → Category.Morphism TargetCategory (mapₒ i) (mapₒ j)) mapₘ (flip (Category._∘_ TargetCategory)) x~y
    diagram-embedding {x} {.x} (inj₂ ≡-refl) = Category.id TargetCategory (mapₒ x)

    open MakeFunctor DomainCategory TargetCategory mapₒ diagram-embedding using (IsValidEmbedding; make-functor)
    open MakeFunctor DomainCategory TargetCategory mapₒ diagram-embedding using (IsCongruent) public

    IsValidDiagramEmbedding : Set _
    IsValidDiagramEmbedding = IsValidEmbedding

    make-diagram-functor : IsValidDiagramEmbedding → Functor DomainCategory TargetCategory
    make-diagram-functor = make-functor

    {-
        Basically,
        - flatten is used on branches, which are DomainCategory morphisms. Flatten, in this case, uses _∘_ in TargetCategory.
        - fold is used on lists, which are modded DomainCategory morphisms.

        So A is the domain.
        A = Object
        _~_ is morphisms in TargetCategory from mapₒ x to mapₒ y
        ~-trans is _∘_ in TargetCategory
        ≈-eq is from the morphism setoid in TargetCategory
        ~-trans-assoc is ∘-assoc in TargetCategory
        ~-trans-cong is ...? idk in TargetCategory.
    -}
    has-morphism-in-target : Object → Object → Set _
    has-morphism-in-target x y = Category.Morphism TargetCategory (mapₒ x) (mapₒ y)

    open RelationTree using (branch-type; branch)
    open Flattening
        {A = Object}
        {_~_ = has-morphism-in-target}
        (flip (Category._∘_ TargetCategory))
        (Category._~_ TargetCategory)
        (λ {x y : Object} → Category.~-eq TargetCategory (mapₒ x) (mapₒ y))
        (λ {w x y z} {f g h} → Category.assoc TargetCategory h g f)
        (flip (Category.∘-respects TargetCategory))
        using (foldl-flatten-same; fold; flatten)
    open Mapping {A = Object} {_~_ = BaseMorphism} {_#_ = has-morphism-in-target} Function.id mapₘ using (map-list; map-cons; map-branch; map-tree; tree→list-mapping-commutes)

    -- inject-list : {x y : Object} → PairwiseRelationList BaseMorphism x y → Category.Morphism DomainCategory x y
    -- inject-list (init _) = inj₂ ≡-refl
    -- inject-list (cons xy) = inj₁ (cons→branch xy)

    -- my-fold : {x y : Object} → PairwiseRelationList has-morphism-in-target x y → Category.Morphism TargetCategory (mapₒ x) (mapₒ y)
    -- my-fold (init x) = Category.id TargetCategory (mapₒ x)
    -- my-fold (cons xy) = fold xy

    -- IsListCongruent : Set _
    -- IsListCongruent = {x y : Object} → (f g : PairwiseRelationList BaseMorphism x y) → my-fold (map-list f) ~₂ my-fold (map-list g)

    -- diagram-embedding-as-list :
    --      {x y : Object} → (f : branch-type BaseMorphism x y) →
    --      diagram-embedding (inj₁ f) ~₂ my-fold (map-list (tree→list (branch f)))
    -- diagram-embedding-as-list {x} {y} f = begin
    --     diagram-embedding (inj₁ f)                                                                                                                                              ≈⟨ refl ⟩
    --     transitive-closure-fold (discrete-setoid Object) BaseMorphism (λ i j → Category.Morphism TargetCategory (mapₒ i) (mapₒ j)) mapₘ (flip (TargetCategory .Category._∘_)) f ≈⟨ refl ⟩
    --     trans-flatten-branch (λ i j → Category.Morphism TargetCategory (mapₒ i) (mapₒ j)) (flip (TargetCategory .Category._∘_)) (map-branch f)                 ≈⟨ refl ⟩
    --     flatten (map-branch f)                                                                                                                                 ≈⟨ sym (foldl-flatten-same (map-branch f)) ⟩
    --     fold (branch→cons (map-branch f))                                                                                                                      ≈⟨ refl ⟩
    --     my-fold (cons (branch→cons (map-branch f)))                                                                                                            ≈⟨ reflexive (cong my-fold (≡-sym (tree→list-branch→cons-same (map-branch f)))) ⟩
    --     my-fold (tree→list (branch (map-branch f)))                                                                                                            ≈⟨ refl ⟩
    --     my-fold (tree→list (map-tree (branch f)))                                                                                                              ≈⟨ reflexive (cong my-fold (tree→list-mapping-commutes (branch f))) ⟩
    --     my-fold (map-list (tree→list (branch f)))                                                                                                              ∎
    --     where
    --         open import Relation.Binary.Reasoning.Setoid (Category.Morphism' TargetCategory (mapₒ x) (mapₒ y))
    --         open IsEquivalence (Category.~-eq TargetCategory (mapₒ x) (mapₒ y))

    -- list-cong→cong : IsListCongruent → IsCongruent
    -- list-cong→cong list-cong {x} {y} {inj₁ f} {inj₁ g} tt = begin
    --     diagram-embedding (inj₁ f)                                                                                                                                              ≈⟨ diagram-embedding-as-list f ⟩
    --     my-fold (map-list (tree→list (branch f)))                                                                                                              ≈⟨ list-cong (tree→list (branch f)) (tree→list (branch g)) ⟩
    --     my-fold (map-list (tree→list (branch g)))                                                                                                              ≈⟨ sym (diagram-embedding-as-list g) ⟩
    --     diagram-embedding (inj₁ g)                                                                                                                                              ∎
    --     where
    --         open import Relation.Binary.Reasoning.Setoid (Category.Morphism' TargetCategory (mapₒ x) (mapₒ y))
    --         open IsEquivalence (Category.~-eq TargetCategory (mapₒ x) (mapₒ y))
    -- list-cong→cong list-cong {x} {.x} {inj₁ f} {inj₂ ≡-refl} tt = begin
    --     diagram-embedding (inj₁ f)                  ≈⟨ diagram-embedding-as-list f ⟩
    --     my-fold (map-list (tree→list (branch f)))   ≈⟨ list-cong (tree→list (branch f)) [] ⟩
    --     my-fold (map-list [])                       ≈⟨ refl ⟩
    --     diagram-embedding (inj₂ ≡-refl) ∎
    --     where
    --         open import Relation.Binary.Reasoning.Setoid (Category.Morphism' TargetCategory (mapₒ x) (mapₒ x))
    --         open IsEquivalence (Category.~-eq TargetCategory (mapₒ x) (mapₒ x))
    -- list-cong→cong list-cong {x} {.x} {inj₂ ≡-refl} {inj₁ f} tt = begin
    --     diagram-embedding (inj₂ ≡-refl)             ≈⟨ refl ⟩
    --     my-fold (map-list [])                       ≈⟨ list-cong [] (tree→list (branch f)) ⟩
    --     my-fold (map-list (tree→list (branch f)))   ≈⟨ sym (diagram-embedding-as-list f) ⟩
    --     diagram-embedding (inj₁ f) ∎
    --     where
    --         open import Relation.Binary.Reasoning.Setoid (Category.Morphism' TargetCategory (mapₒ x) (mapₒ x))
    --         open IsEquivalence (Category.~-eq TargetCategory (mapₒ x) (mapₒ x))
    -- list-cong→cong list-cong {x} {.x} {inj₂ ≡-refl} {inj₂ ≡-refl} tt = refl
    --     where open IsEquivalence (Category.~-eq TargetCategory (mapₒ x) (mapₒ x))

    -- IsValidListEmbedding : Set _
    -- IsValidListEmbedding = Σ IsListCongruent λ cong → (IsFunctor (make-raw-functor (list-cong→cong cong)))



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
        open RawCategory Target using (Object; Morphism; _~_) renaming (_∘_ to _∘₂_)
        open Category commutative-square using () renaming (_∘_ to _∘₁_)

        open RelationTree CommutativeSquareBaseMorphism using (leaf; branch; branch-type)
        open RelationList CommutativeSquareBaseMorphism using (init; cons; _∷_; _∷'_; [])

        private
            inj : {i j : Fin 4} → CommutativeSquareBaseMorphism i j → Category.Morphism commutative-square i j
            inj = diagram-inj CommutativeSquareBaseMorphism

            inj' : {i j : Fin 4} → CommutativeSquareBaseMorphism i j → RawCategory.Morphism Target (mapₒ i) (mapₒ j)
            inj' = mapₘ ∘ inj

        P : Set _
        -- P = inj' m₁₃ ∘ₘ inj' m₀₁ ~ inj' m₂₃ ∘ₘ inj' m₀₂
        P = mapₘ (inj m₁₃ ∘₁ inj m₀₁) ~ mapₘ (inj m₂₃ ∘₁ inj m₀₂)
        thing : MakeFunctor'.IsCongruent (commutative-square .Category.rawCategory) Target mapₒ mapₘ → P
        thing cong = cong {zero} {(suc ∘ suc ∘ suc) zero} {x = inj m₁₃ ∘₁ inj m₀₁} {y = inj m₂₃ ∘₁ inj m₀₂} tt

        variable
            Whatever : Set

        incr-lemma' : {i j : Fin 4} → branch-type i j → i < j
        incr-lemma' b with branch→cons b
        ... | m₀₁ ∷' [] = s≤s z≤n
        ... | m₀₂ ∷' [] = s≤s z≤n
        ... | m₁₃ ∷' [] = s≤s (s≤s z≤n)
        ... | m₂₃ ∷' [] = s≤s (s≤s (s≤s z≤n))
        ... | m₀₁ ∷' m₁₃ ∷ [] = s≤s z≤n
        ... | m₀₂ ∷' m₂₃ ∷ [] = s≤s z≤n

        -- TODO make it so that a proof that the List version of morphisms is congruent
        -- leads to a proof that the branch version of morphisms is congruent

        thing' : P → MakeFunctor'.IsCongruent (commutative-square .Category.rawCategory) Target mapₒ mapₘ
        thing' pf {i} {j} {inj₁ f} {inj₁ g} tt with branch→cons f | branch→cons g
        ... | m₀₁ ∷' m₁₃ ∷ [] | m₀₁ ∷' m₁₃ ∷ [] = {!   !}
        ... | m₀₁ ∷' m₁₃ ∷ [] | m₀₂ ∷' m₂₃ ∷ [] = {!   !}
        ... | m₀₂ ∷' m₂₃ ∷ [] | m₀₁ ∷' m₁₃ ∷ [] = {!   !}
        ... | m₀₂ ∷' m₂₃ ∷ [] | m₀₂ ∷' m₂₃ ∷ [] = {!   !}
        ... | m₀₁ ∷' [] | m₀₁ ∷' [] = {!   !}
        ... | m₀₁ ∷' [] | m₀₁ ∷' m₁₃ ∷ () ∷ y
        ... | m₀₁ ∷' [] | m₀₂ ∷' m₂₃ ∷ () ∷ y
        ... | m₀₂ ∷' [] | m₀₁ ∷' m₁₃ ∷ () ∷ y
        ... | m₀₂ ∷' [] | m₀₂ ∷' [] = {!   !}
        ... | m₀₂ ∷' [] | m₀₂ ∷' m₂₃ ∷ () ∷ y
        ... | m₁₃ ∷' [] | m₁₃ ∷' [] = {!   !}
        ... | m₂₃ ∷' [] | m₂₃ ∷' [] = {!   !}
        thing' pf {i} {j} {inj₂ f} {inj₁ g} tt = {!   !}
        thing' pf {i} {j} {inj₁ f} {inj₂ g} tt = {!   !}
        thing' pf {i} {j} {inj₂ f} {inj₂ g} tt = {!   !}

open ExampleCategories public
