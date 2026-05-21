open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; inspect; cong; Reveal_·_is_; [_]) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
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
open import Plasmaduck.Relation.RelationVector using (module RelationList; module Flattening; module Mapping; tree→list; branch→cons; cons→branch; trans-flatten-branch; tree→list-branch→cons-same; _++_; _++'_; []; _∷_; _∷'_; foldl; ++-left-cons; ++-left-cons-make; ++-right-empty)
open import Plasmaduck.Function.Properties using (Congruent₂)
open import Plasmaduck.Category.Category using (RawCategory; Category; ExtraRawFunctor; Functor; module CategoryProperties; module MakeFunctor; module MakeFunctor')
import Plasmaduck.Function



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

        Object₁ = Object
        Object₂ = TargetCategory .Category.Object

        Morphism₁ = DomainMorphism

        Morphism₂ : Object₁ → Object₁ → Set _
        Morphism₂ x y = Category.Morphism TargetCategory (mapₒ x) (mapₒ y)

        open Category DomainCategory using () renaming (_∘_ to _∘₁_; id to id₁; _~_ to _~₁_)
        open Category TargetCategory using () renaming (_∘_ to _∘₂_; id to id₂; _~_ to _~₂_)
        open Mapping {A = Object} {_~_ = BaseMorphism} {_#_ = Morphism₂} Function.id mapₘ using (map-cons; map-cons-++')

    diagram-embedding : {x y : Object} → Morphism₁ x y → Morphism₂ x y
    diagram-embedding {x} {y} (x~z ∷ zy) = foldl Morphism₂ (flip _∘₂_) (map-cons (x~z ∷' zy))
    diagram-embedding {x} {.x} [] = Category.id TargetCategory (mapₒ x)

    private
        open Flattening
            {A = Object}
            {_~_ = Morphism₂}
            (flip (Category._∘_ TargetCategory))
            (Category._~_ TargetCategory)
            (λ {x y : Object} → Category.~-eq TargetCategory (mapₒ x) (mapₒ y))
            (λ {w x y z} {f g h} → Category.assoc TargetCategory h g f)
            (flip (Category.∘-respects TargetCategory))
            using (foldl-++')

        is-consistent-on-id : {x : Object₁} → diagram-embedding (id₁ x) ~₂ id₂ (mapₒ x)
        is-consistent-on-id = Category.~-refl TargetCategory

        is-consistent-on-∘ :
            {x y z : Object₁} → (g : Morphism₁ y z) (f : Morphism₁ x y) →
            diagram-embedding (g ∘₁ f) ~₂ (diagram-embedding g) ∘₂ (diagram-embedding f)
        is-consistent-on-∘ _ [] = Category.~-sym TargetCategory (TargetCategory .Category.id-is-right-id)
        is-consistent-on-∘ {x = x} {z = z} [] (b ∷ m) = begin
                diagram-embedding ([] ∘₁ (b ∷ m))                                   ≈⟨ ~-refl ⟩
                diagram-embedding ((b ∷ m) ++ [])                                   ≈⟨ ~-reflexive (cong diagram-embedding (++-right-empty (b ∷ m))) ⟩
                diagram-embedding (b ∷ m)                                           ≈⟨ ~-refl ⟩
                foldl Morphism₂ (flip _∘₂_) (map-cons (b ∷' m))                     ≈⟨ ~-sym (Category.id-is-left-id TargetCategory) ⟩
                (id₂ (mapₒ z) ∘₂ foldl Morphism₂ (flip _∘₂_) (map-cons (b ∷' m)))   ≈⟨ ~-refl ⟩
                diagram-embedding [] ∘₂ diagram-embedding (b ∷ m)                   ∎
                where
                    open import Relation.Binary.Reasoning.Setoid (Category.Morphism' TargetCategory (mapₒ x) (mapₒ z))
                    open Category TargetCategory using (~-reflexive; ~-refl; ~-sym; ~-trans)
        is-consistent-on-∘ {x = x} {z = z} (b₁ ∷ m₁) (b₂ ∷ m₂) = begin
            diagram-embedding ((b₁ ∷ m₁) ∘₁ (b₂ ∷ m₂))                                                              ≈⟨ ~-refl ⟩
            diagram-embedding ((b₂ ∷ m₂) ++ (b₁ ∷ m₁))                                                              ≈⟨ ~-reflexive (cong diagram-embedding (++-left-cons (b₂ ∷' m₂) (b₁ ∷ m₁))) ⟩
            diagram-embedding (b₂ ∷ (m₂ ++ (b₁ ∷ m₁)))                                                              ≈⟨ ~-refl ⟩
            foldl Morphism₂ (flip _∘₂_) (map-cons (b₂ ∷' (m₂ ++ (b₁ ∷ m₁))))                                        ≈⟨ ~-refl ⟩
            foldl Morphism₂ (flip _∘₂_) (map-cons ((b₂ ∷' m₂) ++' (b₁ ∷' m₁)))                                      ≈⟨ ~-reflexive (cong (foldl Morphism₂ (flip _∘₂_)) (map-cons-++' (b₂ ∷' m₂) (b₁ ∷' m₁))) ⟩
            foldl Morphism₂ (flip _∘₂_) (map-cons (b₂ ∷' m₂) ++' map-cons (b₁ ∷' m₁))                               ≈⟨ foldl-++' (map-cons (b₂ ∷' m₂)) (map-cons (b₁ ∷' m₁)) ⟩
            foldl Morphism₂ (flip _∘₂_) (map-cons (b₁ ∷' m₁)) ∘₂ foldl Morphism₂ (flip _∘₂_) (map-cons (b₂ ∷' m₂))  ≈⟨ ~-refl ⟩
            diagram-embedding (b₁ ∷ m₁) ∘₂ diagram-embedding (b₂ ∷ m₂)                                              ∎
            where
                open import Relation.Binary.Reasoning.Setoid (Category.Morphism' TargetCategory (mapₒ x) (mapₒ z))
                open Category TargetCategory using (~-reflexive; ~-refl; ~-sym; ~-trans)

    open MakeFunctor DomainCategory TargetCategory mapₒ diagram-embedding using (IsValidEmbedding; IsExplicitlyCongruent; make-functor)

    IsValidDiagramEmbedding : Set _
    IsValidDiagramEmbedding = IsExplicitlyCongruent

    make-diagram-functor : IsValidDiagramEmbedding → Functor DomainCategory TargetCategory
    make-diagram-functor cong = make-functor (cong , record { consistent-on-id = is-consistent-on-id; consistent-on-∘ = is-consistent-on-∘ })



-----------------------------------
--- Some examples of Categories ---
-----------------------------------

𝟘 : Category lzero lzero lzero
𝟘 = record {
    rawCategory = record {
        Object = ⊥;
        Morphism' = λ ();
        id = λ ();
        compose = λ {}
        };
    isCategory = record {
        assoc = λ {};
        id-is-left-id = λ {};
        id-is-right-id = λ {}
        }
    }

𝟙 : Category lzero lzero lzero
𝟙 = record {
    rawCategory = record {
        Object = ⊤;
        Morphism' = λ _ _ → discrete-setoid ⊤;
        id = λ _ → tt;
        compose = record {
            func = λ _ _ → tt;
            respects = λ _ _ → ≡-refl
            }
        };
    isCategory = record {
        assoc = λ _ _ _ → ≡-refl;
        id-is-left-id = ≡-refl;
        id-is-right-id = ≡-refl
        }
    }

𝐒𝐞𝐭 : (ℓ : Level) → Category (lsuc ℓ) ℓ ℓ
𝐒𝐞𝐭 ℓ = record {
    rawCategory = record {
        Object = Set ℓ;
        Morphism' = λ A B → record {
            Carrier = A → B;
            _≈_ = Plasmaduck.Function._≈_;
            isEquivalence = Plasmaduck.Function.≈-isEquivalence
            };
        id = λ A → Function.id;
        compose = record {
            func = λ g f → Function._∘_ g f;
            respects = λ {g₁} {g₂} {f₁} {f₂} g₁≈g₂ f₁≈f₂ x →
                g₁ (f₁ x)   ≡⟨ cong g₁ (f₁≈f₂ x) ⟩
                g₁ (f₂ x)   ≡⟨ g₁≈g₂ (f₂ x) ⟩
                g₂ (f₂ x)   ∎
            }
        };
    isCategory = record {
        assoc = λ _ _ _ _ → ≡-refl;
        id-is-left-id = λ _ → ≡-refl;
        id-is-right-id = λ _ → ≡-refl
        }
    }
    where open ≡-Reasoning

-- Also see make-net from Net.agda.
setoid-category : Setoid a b → Category a b lzero
setoid-category setoid = record {
    rawCategory = record {
        Object = setoid .Setoid.Carrier;
        Morphism' = λ A B → indiscrete-setoid (A ~ B);
        id = λ x → Setoid.refl setoid {x = x};
        compose = record { func = flip (Setoid.trans setoid) }
        };
    isCategory = record {}
    }
    where open Setoid setoid using () renaming (_≈_ to _~_)

discrete-category : Set a → Category a a lzero
discrete-category A = setoid-category (discrete-setoid A)

module ObjectPicker (ℂ : Category a b c) where
    open Category ℂ using (Object; Morphism; id; ~-refl; ~-sym; ~-trans)

    object-picker : Object → Functor 𝟙 ℂ
    object-picker X = record {
        rawFunctor = record {
            mapₒ = λ _ → X;
            mapₘ-func = record {
                func = λ _ → id X;
                respects = λ _ → ~-refl
                }
            };
        isFunctor = record {
            consistent-on-id = ~-refl;
            consistent-on-∘ = λ g f → ~-sym (Category.id-is-left-id ℂ)
            }
        }

id-functor : (ℂ : Category a b c) → Functor ℂ ℂ
id-functor ℂ = record {
    rawFunctor = record {
        mapₒ = Function.id;
        mapₘ-func = record {
            func = Function.id;
            respects = Function.id
            }
        };
    isFunctor = record {
        consistent-on-id = Category.~-refl ℂ;
        consistent-on-∘ = λ g f → Category.~-refl ℂ
        }
    }

constant-functor : (ℂ : Category a b c) → ℂ .Category.Object → Functor ℂ ℂ
constant-functor ℂ X = record {
    rawFunctor = record {
        mapₒ = λ _ → X;
        mapₘ-func = record {
            func = λ _ → Category.id ℂ X;
            respects = λ z → Category.~-refl ℂ
            }
        };
    isFunctor = record {
        consistent-on-id = Category.~-refl ℂ;
        consistent-on-∘ = λ g f → Category.~-sym ℂ (Category.id-is-left-id ℂ)
        }
    }

-- TODO Maybe I should figure out how to write down universal properties as tiny explicit categories or something
module CommutativeSquare where
    open import Function using (_∘_)

    -- A diagram is a category, typically one with only a few objects. The diagram is injected into other categories via functor.
    -- A commutative diagram is one where all morphisms between two objects are equal.

    {-
        0 ----> 1
        |       |
        V       V
        2 ----> 3
    -}

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
        commutative→P : MakeFunctor'.IsExplicitlyCongruent (commutative-square .Category.rawCategory) Target mapₒ mapₘ → P
        commutative→P cong = cong (inj m₁₃ ∘₁ inj m₀₁) (inj m₂₃ ∘₁ inj m₀₂) tt

        incr-lemma' : {i j : Fin 4} → PairwiseRelationListCons i j → i < j
        incr-lemma' (m₀₁ ∷' []) = s≤s z≤n
        incr-lemma' (m₀₂ ∷' []) = s≤s z≤n
        incr-lemma' (m₁₃ ∷' []) = s≤s (s≤s z≤n)
        incr-lemma' (m₂₃ ∷' []) = s≤s (s≤s (s≤s z≤n))
        incr-lemma' (m₀₁ ∷' m₁₃ ∷ []) = s≤s z≤n
        incr-lemma' (m₀₂ ∷' m₂₃ ∷ []) = s≤s z≤n

        P→commutative : P → MakeFunctor'.IsExplicitlyCongruent (commutative-square .Category.rawCategory) Target mapₒ mapₘ
        P→commutative pf [] [] tt = ~-refl
        P→commutative pf [] (x ∷ y) tt = ⊥-elim (<-irrefl ≡-refl (incr-lemma' (x ∷' y)))
        P→commutative pf (x ∷ y) [] tt = ⊥-elim (<-irrefl ≡-refl (incr-lemma' (x ∷' y)))
        P→commutative pf (m₀₁ ∷ m₁₃ ∷ []) (m₀₁ ∷ m₁₃ ∷ []) tt = ~-refl
        P→commutative pf (m₀₁ ∷ m₁₃ ∷ []) (m₀₂ ∷ m₂₃ ∷ []) tt = pf
        P→commutative pf (m₀₂ ∷ m₂₃ ∷ []) (m₀₁ ∷ m₁₃ ∷ []) tt = ~-sym pf
        P→commutative pf (m₀₂ ∷ m₂₃ ∷ []) (m₀₂ ∷ m₂₃ ∷ []) tt = ~-refl
        P→commutative pf (m₀₁ ∷ []) (m₀₁ ∷ []) tt = ~-refl
        P→commutative pf (m₀₁ ∷ []) (m₀₁ ∷ m₁₃ ∷ () ∷ y) tt
        P→commutative pf (m₀₁ ∷ []) (m₀₂ ∷ m₂₃ ∷ () ∷ y) tt
        P→commutative pf (m₀₂ ∷ []) (m₀₁ ∷ m₁₃ ∷ () ∷ y) tt
        P→commutative pf (m₀₂ ∷ []) (m₀₂ ∷ []) tt = ~-refl
        P→commutative pf (m₀₂ ∷ []) (m₀₂ ∷ m₂₃ ∷ () ∷ y) tt
        P→commutative pf (m₁₃ ∷ []) (m₁₃ ∷ []) tt = ~-refl
        P→commutative pf (m₂₃ ∷ []) (m₂₃ ∷ []) tt = ~-refl

open CommutativeSquare public
