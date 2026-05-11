open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; inspect; cong; Reveal_·_is_; [_]) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Relation.Binary using (Setoid; Rel; IsEquivalence; Transitive)
open import Function using (flip; _∋_; Congruent)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)

open import Plasmaduck.SetoidExperiment.SetoidMachinery using (SetoidFunction; SetoidFunction₂; _←_; discrete-setoid; indiscrete-setoid; from-discrete-cong; into-indiscrete-cong)
open import Plasmaduck.Function.Properties using (Congruent₂)



module Plasmaduck.Category.Category where

variable
    a b c α β γ ℓ₁ ℓ₂ ℓ₃ : Level


----------------
--- Category ---
----------------

record RawCategory (a b c : Level) : Set (lsuc a ⊔ lsuc b ⊔ lsuc c) where
    field
        Object : Set a
        Morphism' : Object → Object → Setoid b c

    Morphism : Object → Object → Set b
    Morphism x y = Morphism' x y .Setoid.Carrier

    _~_ : {x y : Object} → Rel (Morphism x y) c
    _~_ {x = x} {y} = Morphism' x y .Setoid._≈_
    infix 1 _~_

    ~-eq : (x y : Object) → IsEquivalence (_~_ {x} {y})
    ~-eq x y = Morphism' x y .Setoid.isEquivalence

    field
        id : (x : Object) → Morphism x x
        compose : {x y z : Object} → SetoidFunction₂ (Morphism' y z) (Morphism' x y) (Morphism' x z)
    _∘_ : {x y z : Object} → Morphism y z → Morphism x y → Morphism x z
    _∘_ = compose .SetoidFunction₂.func

    -- This is here instead of in IsCategory because _∘_ is supposed to be a SetoidFunction that takes two arguments,
    -- but setoid functions get unwieldy when they take more than one argument.
    ∘-respects : {x y z : Object} → Congruent₂ (_~_ {y} {z}) (_~_ {x} {y}) _~_ _∘_
    ∘-respects = compose .SetoidFunction₂.respects

    infixr 9 _∘_

    module _ {x y : Object} where
        open Setoid (Morphism' x y) using () renaming (refl to ~-refl; sym to ~-sym; trans to ~-trans) public


record IsCategory (rawCategory : RawCategory a b c) : Set (a ⊔ b ⊔ c) where
    open RawCategory rawCategory
    field
        assoc : {w x y z : Object} → (h : Morphism y z) → (g : Morphism x y) → (f : Morphism w x) → (h ∘ g) ∘ f ~ h ∘ (g ∘ f)
        id-is-left-id : {x y : Object} → {f : Morphism x y} → id y ∘ f ~ f
        id-is-right-id : {x y : Object} → {f : Morphism x y} → f ∘ id x ~ f


record Category (a b c : Level) : Set (lsuc a ⊔ lsuc b ⊔ lsuc c) where
    field
        rawCategory : RawCategory a b c
        isCategory : IsCategory rawCategory

    open RawCategory rawCategory public
    open IsCategory isCategory public



---------------------------
--- Category Properties ---
---------------------------

module RawCategoryProperties (rawCategory : RawCategory a b c) where
    open RawCategory rawCategory

    AtMostOneMorphism : (x y : Object) → Set (b ⊔ c)
    AtMostOneMorphism x y = ∀ (f g : Morphism x y) → f ~ g

    AtLeastOneMorphism : (x y : Object) → Set b
    AtLeastOneMorphism x y = Morphism x y

    UniqueMorphism : (x y : Object) → Set (b ⊔ c)
    UniqueMorphism x y = AtLeastOneMorphism x y × AtMostOneMorphism x y

    IsCommutative : Set (a ⊔ b ⊔ c)
    IsCommutative = ∀ {x y : Object} → AtMostOneMorphism x y


module CategoryProperties (category : Category a b c) where
    open Category category
    open RawCategoryProperties rawCategory using (
        AtMostOneMorphism;
        AtLeastOneMorphism;
        UniqueMorphism;
        IsCommutative
        ) public

opposite-category' : RawCategory a b c → RawCategory a b c
opposite-category' category = record {
    Object = Object;
    Morphism' = λ x y → Morphism' y x;
    id = id;
    compose = record {
        func = flip _∘_;
        respects = flip ∘-respects
        }
    }
    where open RawCategory category

opposite-category : Category a b c → Category a b c
opposite-category category = record {
    rawCategory = opposite-category' rawCategory;
    isCategory = record {
        assoc = λ h g f → ~-sym (assoc f g h);
        id-is-left-id = id-is-right-id;
        id-is-right-id = id-is-left-id
        }
    }
    where open Category category



---------------------------
--- Morphism Properties ---
---------------------------

module MorphismProperties (category : Category a b c) where
    open Category category
    open CategoryProperties category

    module _ {x y : Object} where

        IsSidedInverse : Morphism x y → Morphism y x → Set c
        IsSidedInverse f g = f ∘ g ~ id y

        -- Right cancellative. In a sense, this morphism fully represents its target.
        IsEpimorphism : Morphism x y → Set (a ⊔ b ⊔ c)
        IsEpimorphism f = ∀ {z : Object} (g₁ g₂ : Morphism y z) → g₁ ∘ f ~ g₂ ∘ f → g₁ ~ g₂

        -- Left cancellative. In a sense, this morphism fully represents its domain.
        IsMonomorphism : Morphism x y → Set (a ⊔ b ⊔ c)
        IsMonomorphism g = ∀ {w : Object} (f₁ f₂ : Morphism w x) → g ∘ f₁ ~ g ∘ f₂ → f₁ ~ f₂

    module _ {x y : Object} where
        IsInverse : Morphism x y → Morphism y x → Set c
        IsInverse f g = IsSidedInverse f g × IsSidedInverse g f

        IsIsomorphism : Morphism x y → Set (b ⊔ c)
        IsIsomorphism f = Σ (Morphism y x) (IsInverse f)

    IsInitial : (x : Object) → Set (a ⊔ b ⊔ c)
    IsInitial x = ∀ (y : Object) → UniqueMorphism x y

    IsFinal : (x : Object) → Set (a ⊔ b ⊔ c)
    IsFinal x = ∀ (y : Object) → UniqueMorphism y x

    IsZero : (x : Object) → Set (a ⊔ b ⊔ c)
    IsZero x = IsInitial x × IsFinal x



--------------------------
--- Functor Definition ---
--------------------------

record ExtraRawFunctor (cat₁ : RawCategory a b c) (cat₂ : RawCategory α β γ) : Set (a ⊔ b ⊔ c ⊔ α ⊔ β ⊔ γ) where
    open RawCategory cat₁ using () renaming (Object to Object₁; Morphism to Morphism₁; Morphism' to Morphism'₁; _~_ to _~₁_)
    open RawCategory cat₂ using () renaming (Object to Object₂; Morphism to Morphism₂; Morphism' to Morphism'₂; _~_ to _~₂_)
    field
        mapₒ : Object₁ → Object₂
        mapₘ : {x y : Object₁} → Morphism₁ x y → Morphism₂ (mapₒ x) (mapₒ y)

record RawFunctor (cat₁ : RawCategory a b c) (cat₂ : RawCategory α β γ) : Set (a ⊔ b ⊔ c ⊔ α ⊔ β ⊔ γ) where
    open RawCategory cat₁ using () renaming (Object to Object₁; Morphism to Morphism₁; Morphism' to Morphism'₁; _~_ to _~₁_)
    open RawCategory cat₂ using () renaming (Object to Object₂; Morphism to Morphism₂; Morphism' to Morphism'₂; _~_ to _~₂_)
    field
        mapₒ : Object₁ → Object₂
        mapₘ-func : {x y : Object₁} → SetoidFunction (Morphism'₁ x y) (Morphism'₂ (mapₒ x) (mapₒ y))

    mapₘ : {x y : Object₁} → Morphism₁ x y → Morphism₂ (mapₒ x) (mapₒ y)
    mapₘ f = mapₘ-func ← f

    mapₘ-respects : {x y : Object₁} → {f g :  Morphism₁ x y} → f ~₁ g → mapₘ f ~₂ mapₘ g
    mapₘ-respects = mapₘ-func .SetoidFunction.respects

    extra-raw-functor : ExtraRawFunctor cat₁ cat₂
    extra-raw-functor = record {
        mapₒ = mapₒ;
        mapₘ = mapₘ
        }

module ExtraRawFunctorProperties
    {𝔸 : RawCategory a b c} {𝔹 : RawCategory α β γ}
    (F : ExtraRawFunctor 𝔸 𝔹)
    where

    open RawCategory 𝔸 using () renaming (Object to Object₁; Morphism to Morphism₁; Morphism' to Morphism'₁; _~_ to _~₁_)
    open RawCategory 𝔹 using () renaming (Object to Object₂; Morphism to Morphism₂; Morphism' to Morphism'₂; _~_ to _~₂_)
    open ExtraRawFunctor F using (mapₒ; mapₘ)

    IsCongruent : Set _
    IsCongruent = {x y : Object₁} → {f g :  Morphism₁ x y} → f ~₁ g → mapₘ f ~₂ mapₘ g

    extra-raw-congruent→raw-functor : IsCongruent → RawFunctor 𝔸 𝔹
    extra-raw-congruent→raw-functor cong = record {
        mapₒ = mapₒ;
        mapₘ-func = record {
            func = mapₘ;
            respects = cong
            }
        }

record IsFunctor {cat₁ : RawCategory a b c} {cat₂ : RawCategory α β γ} (F : RawFunctor cat₁ cat₂) : Set (a ⊔ b ⊔ γ) where
    open RawFunctor F
    open RawCategory cat₁ using () renaming (_∘_ to _∘₁_; id to id₁; Object to Object₁; Morphism to Morphism₁)
    open RawCategory cat₂ using (_~_) renaming (_∘_ to _∘₂_; id to id₂)

    field
        consistent-on-id : {x : Object₁} → mapₘ (id₁ x) ~ id₂ (mapₒ x)
        consistent-on-∘ :
            {x y z : Object₁} → (g : Morphism₁ y z) (f : Morphism₁ x y) →
            mapₘ (g ∘₁ f) ~ (mapₘ g) ∘₂ (mapₘ f)

record Functor (cat₁ : Category a b c) (cat₂ : Category α β γ) : Set (a ⊔ b ⊔ c ⊔ α ⊔ β ⊔ γ) where
    field
        rawFunctor : RawFunctor (cat₁ .Category.rawCategory) (cat₂ .Category.rawCategory)
        isFunctor : IsFunctor rawFunctor

    open RawFunctor rawFunctor public
    open IsFunctor isFunctor public

ContravariantFunctor : (cat₁ : Category a b c) (cat₂ : Category α β γ) → Set _
ContravariantFunctor cat₁ cat₂ = Functor (opposite-category cat₁) cat₂

opposite-functor :
    {cat₁ : Category a b c} {cat₂ : Category α β γ} →
    (F : Functor cat₁ cat₂) →
    Functor (opposite-category cat₁) (opposite-category cat₂)
opposite-functor F = record {
    rawFunctor = record {
        mapₒ = F .Functor.mapₒ;
        mapₘ-func = F .Functor.mapₘ-func
        };
    isFunctor = record {
        consistent-on-id = F .Functor.consistent-on-id;
        consistent-on-∘ = λ g f → F .Functor.consistent-on-∘ f g
        }
    }


module MakeFunctor'
    (DomainCategory : RawCategory a b c)
    (TargetCategory : RawCategory α β γ)
    (mapₒ : DomainCategory .RawCategory.Object → TargetCategory .RawCategory.Object)
    (mapₘ : {x y : DomainCategory .RawCategory.Object} → RawCategory.Morphism DomainCategory x y → RawCategory.Morphism TargetCategory (mapₒ x) (mapₒ y))
    where

    private
        DomainObject = DomainCategory .RawCategory.Object

        DomainMorphism : (x y : DomainObject) → Set _
        DomainMorphism x y = RawCategory.Morphism DomainCategory x y

    make-extra-raw-functor : ExtraRawFunctor DomainCategory TargetCategory
    make-extra-raw-functor = record { mapₒ = mapₒ; mapₘ = mapₘ }

    IsCongruent : Set _
    IsCongruent = {x y : DomainObject} → Congruent (RawCategory._~_ DomainCategory) (RawCategory._~_ TargetCategory) (mapₘ {x} {y})

    make-raw-functor : IsCongruent → RawFunctor DomainCategory TargetCategory
    make-raw-functor map-cong = record {
        mapₒ = mapₒ;
        mapₘ-func = record {
            func = mapₘ;
            respects = map-cong
            }
        }

    IsValidEmbedding : Set _
    IsValidEmbedding = Σ IsCongruent λ cong → (IsFunctor (make-raw-functor cong))

module MakeFunctor
    (DomainCategory : Category a b c)
    (TargetCategory : Category α β γ)
    (mapₒ : DomainCategory .Category.Object → TargetCategory .Category.Object)
    (mapₘ : {x y : DomainCategory .Category.Object} → Category.Morphism DomainCategory x y → Category.Morphism TargetCategory (mapₒ x) (mapₒ y))
    where

    open MakeFunctor' (DomainCategory .Category.rawCategory) (TargetCategory .Category.rawCategory) mapₒ mapₘ public

    make-functor : IsValidEmbedding → Functor DomainCategory TargetCategory
    make-functor is-valid = record { rawFunctor = make-raw-functor (is-valid .proj₁); isFunctor = is-valid .proj₂ }




-- module CommaCategory
--     {𝔸 : Category a b c} {𝔹 : Category α β γ} {ℂ : Category ℓ₁ ℓ₂ ℓ₃}
--     (S : Functor 𝔸 ℂ) (T : Functor 𝔹 ℂ)
--     where

--     _↓'_ : RawCategory _ _ _
--     _↓'_ = record {
--         Object = Obj;
--         Morphism' = λ x y → record {
--             Carrier = Morph x y;
--             _≈_ = ~-Morph;
--             isEquivalence = ~-Morph-eq
--             };
--         id = identity;
--         _∘_ = concat;
--         ∘-respects = concat-respects
--         }
--         where
--             open Category
--             open Functor

--             Obj = Σ (𝔸 .Object) λ x → Σ (𝔹 .Object) λ y → (Morphism ℂ (S .mapₒ x) (T .mapₒ y))

--             map-obj : Obj → Obj → commutative-square .Object → ℂ .Object
--             map-obj (A , B , h) (A' , B' , h') zero = S .mapₒ A
--             map-obj (A , B , h) (A' , B' , h') (suc zero) = S .mapₒ A'
--             map-obj (A , B , h) (A' , B' , h') (suc (suc zero)) = T .mapₒ B
--             map-obj (A , B , h) (A' , B' , h') (suc (suc (suc zero))) = T .mapₒ B'

--             map-morph : ((A , B , h) (A' , B' , h') : Obj) → (Morphism 𝔸 A A') → (Morphism 𝔹 B B') → {x y : commutative-square .Object} → CommutativeSquareBaseMorphism x y → Morphism ℂ (map-obj (A , B , h) (A' , B' , h') x) (map-obj (A , B , h) (A' , B' , h') y)
--             map-morph (A , B , h) (A' , B' , h') f g m₀₁ = mapₘ S f
--             map-morph (A , B , h) (A' , B' , h') f g m₁₃ = h'
--             map-morph (A , B , h) (A' , B' , h') f g m₀₂ = h
--             map-morph (A , B , h) (A' , B' , h') f g m₂₃ = mapₘ T g

--             RawMorph : Obj → Obj → Set _
--             RawMorph (A , B , h) (A' , B' , h') = (Morphism 𝔸 A A') × (Morphism 𝔹 B B')

--             Morph : Obj → Obj → Set _
--             Morph (A , B , h) (A' , B' , h') = Σ (Morphism 𝔸 A A') λ f → Σ (Morphism 𝔹 B B') λ g → Diagram.IsValidDiagramEmbedding CommutativeSquareBaseMorphism ℂ (map-obj (A , B , h) (A' , B' , h')) (map-morph (A , B , h) (A' , B' , h') f g)

--             get-raw-morph : {x y : Obj} → Morph x y → RawMorph x y
--             get-raw-morph (f , g , _) = f , g

--             ~-Morph : {x y : Obj} → Rel (Morph x y) _
--             ~-Morph {x} {y} (f₁ , g₁ , _) (f₂ , g₂ , _) = Category._~_ 𝔸 f₁ f₂ × Category._~_ 𝔹 g₁ g₂

--             ~-Morph-eq : {x y : Obj} → IsEquivalence (~-Morph {x} {y})
--             ~-Morph-eq {A , B , _} {A' , B' , _} = record {
--                 refl = refl₁ , refl₂;
--                 sym = λ (f₁~f₂ , g₁~g₂) → sym₁ f₁~f₂ , sym₂ g₁~g₂;
--                 trans = λ (f₁~f₂ , g₁~g₂) (f₂~f₃ , g₂~g₃) → trans₁ f₁~f₂ f₂~f₃ , trans₂ g₁~g₂ g₂~g₃
--                 }
--                 where
--                     open IsEquivalence (Category.~-eq 𝔸 A A') renaming (refl to refl₁; sym to sym₁; trans to trans₁)
--                     open IsEquivalence (Category.~-eq 𝔹 B B') renaming (refl to refl₂; sym to sym₂; trans to trans₂)

--             module DiagramEmbed {x y : Obj} ((f , g) : RawMorph x y) where
--                 diagram-embedₒ : Fin 4 → Category.Object ℂ
--                 diagram-embedₒ = map-obj x y

--                 diagram-embedₘ : {i j : Fin 4} → Category.Morphism commutative-square i j → Category.Morphism ℂ (diagram-embedₒ i) (diagram-embedₒ j)
--                 diagram-embedₘ = Diagram.diagram-embedding CommutativeSquareBaseMorphism ℂ (map-obj x y) (map-morph x y f g)

--                 IsCongruent : Set _
--                 IsCongruent = Diagram.IsCongruent CommutativeSquareBaseMorphism ℂ (map-obj x y) (map-morph x y f g)

--             module _ {x y : Obj} ((f , g , is-valid) : Morph x y) where
--                 morph→diagram-functor : Functor commutative-square ℂ
--                 morph→diagram-functor = Diagram.make-diagram-functor CommutativeSquareBaseMorphism ℂ (map-obj x y) (map-morph x y f g) is-valid

--             identity : (x : Obj) → Morph x x
--             identity obj@(A , B , h) = id 𝔸 A , id 𝔹 B , diagram-commutes , record {
--                 consistent-on-id = {!   !};
--                 consistent-on-∘ = {!   !}
--                 }
--                 where
--                     open DiagramEmbed {x = obj} {y = obj} (id 𝔸 A , id 𝔹 B)

--                     diagram-commutes : IsCongruent
--                     diagram-commutes {zero} {zero} {inj₁ (x , y , thing , hi , two)} {inj₁ x₁} tt = {! two  !}
--                     diagram-commutes {zero} {zero} {inj₁ x} {inj₂ y} tt = {!   !}
--                     diagram-commutes {zero} {zero} {inj₂ y} {inj₁ x} tt = {!   !}
--                     diagram-commutes {zero} {zero} {inj₂ y} {inj₂ y₁} tt = {!   !}
--                     diagram-commutes {zero} {suc j} {inj₁ x} {inj₁ x₁} tt = {!   !}
--                     diagram-commutes {suc i} {zero} {inj₁ x} {inj₁ x₁} tt = {!   !}
--                     diagram-commutes {suc i} {suc j} {inj₁ x} {inj₁ x₁} tt = {!   !}
--                     diagram-commutes {suc i} {suc j} {inj₁ x} {inj₂ y} tt = {!   !}
--                     diagram-commutes {suc i} {suc j} {inj₂ y} {inj₁ x} tt = {!   !}
--                     diagram-commutes {suc i} {suc j} {inj₂ y} {inj₂ y₁} tt = {!   !}
--             {-
--             (x y : Fin 4)
--       {x = x₁ : Σ (Fin 4)
--                         (λ x₂ →
--                             Σ (Fin 4)
--                             (λ y₁ →
--                             Σ
--                             (Plasmaduck.Relation.RelationVector.RelationTree.RelTree
--                                 CommutativeSquareBaseMorphism x x₂)
--                             (λ x₃ →
--                                 Σ (CommutativeSquareBaseMorphism x₂ y₁)
--                                 (λ x₄ →
--                                     Plasmaduck.Relation.RelationVector.RelationTree.RelTree
--                                     CommutativeSquareBaseMorphism y₁ y))))
--          ⊎ x ≡ y}
--       {y = y₁
--        : Σ (Fin 4)
--          (λ x₂ →
--             Σ (Fin 4)
--             (λ y₂ →
--                Σ
--                (Plasmaduck.Relation.RelationVector.RelationTree.RelTree
--                 CommutativeSquareBaseMorphism x x₂)
--                (λ x₃ →
--                   Σ (CommutativeSquareBaseMorphism x₂ y₂)
--                   (λ x₄ →
--                      Plasmaduck.Relation.RelationVector.RelationTree.RelTree
--                      CommutativeSquareBaseMorphism y₂ y))))
--          ⊎ x ≡ y} →
--       Data.Unit.⊤ →
--       (RawCategory.Morphism' (rawCategory ℂ)
--        (map-obj (A , B , h) (A , B , h) x)
--        (map-obj (A , B , h) (A , B , h) y)
--        Setoid.≈
--        Diagram.diagram-embedding CommutativeSquareBaseMorphism ℂ
--        (map-obj (A , B , h) (A , B , h))
--        (map-morph (A , B , h) (A , B , h)
--         (RawCategory.id (rawCategory 𝔸) A)
--         (RawCategory.id (rawCategory 𝔹) B))
--        x₁)
--       (Diagram.diagram-embedding CommutativeSquareBaseMorphism ℂ
--        (map-obj (A , B , h) (A , B , h))
--        (map-morph (A , B , h) (A , B , h)
--         (RawCategory.id (rawCategory 𝔸) A)
--         (RawCategory.id (rawCategory 𝔹) B))
--        y₁)
--             -}

--             concat : {x y z : Obj} → Morph y z → Morph x y → Morph x z
--             concat (f' , g' , is-valid') (f , g , is-valid) = _∘_ 𝔸 f' f ,  _∘_ 𝔹 g' g , {!   !}

--             concat-respects :
--                 {x y z : Obj} {g₁ g₂ : Morph y z} {f₁ f₂ : Morph x y} →
--                 ~-Morph g₁ g₂ → ~-Morph f₁ f₂ → ~-Morph (concat g₁ f₁) (concat g₂ f₂)
--             concat-respects = {!   !}

--     _↓_ : Category _ _ _
--     _↓_ = record {
--         rawCategory = _↓'_;
--         isCategory = record {}
--         }









-- -- module Theorems (category : Category a b c) where
-- --     module First (category : Category a b c) where
-- --         open Category category
-- --         open MorphismProperties category

-- --         left-inv→mono : {y z : Object} → (g-inv : Morphism z y) (g : Morphism y z) → IsSidedInverse g-inv g → IsMonomorphism g
-- --         left-inv→mono {y = y} {z} g-inv g g-inv∘g~id {x} f₁ f₂ g∘f₁~g∘f₂ = begin
-- --             f₁                  ≈⟨ ~-sym id-is-left-id ⟩
-- --             id y ∘ f₁           ≈⟨ ∘-respects (~-sym g-inv∘g~id) ~-refl ⟩
-- --             (g-inv ∘ g) ∘ f₁    ≈⟨ assoc g-inv g f₁ ⟩
-- --             g-inv ∘ (g ∘ f₁)    ≈⟨ ∘-respects ~-refl g∘f₁~g∘f₂ ⟩
-- --             g-inv ∘ (g ∘ f₂)    ≈⟨ ~-sym (assoc g-inv g f₂) ⟩
-- --             (g-inv ∘ g) ∘ f₂    ≈⟨ ∘-respects g-inv∘g~id ~-refl ⟩
-- --             id y ∘ f₂           ≈⟨ id-is-left-id ⟩
-- --             f₂                  ∎
-- --             where open import Relation.Binary.Reasoning.Setoid (Morphism' x y)

-- --     open Category category
-- --     open MorphismProperties category
-- --     -- Hey look a dual theorem
-- --     right-inv→epi : {x y : Object} → (f : Morphism x y) (f-inv : Morphism y x) → IsSidedInverse f f-inv → IsEpimorphism f
-- --     right-inv→epi f f-inv = First.left-inv→mono (opposite-category category) f-inv f

-- --     iso→mono : {x y : Object} → (f : Morphism x y) → IsIsomorphism f → IsMonomorphism f
-- --     iso→mono f (g , fg~ , gf~) = First.left-inv→mono category g f gf~

-- --     iso→epi : {x y : Object} → (f : Morphism x y) → IsIsomorphism f → IsEpimorphism f
-- --     iso→epi f (g , fg~ , gf~) = right-inv→epi f g fg~

-- --     open First category public

-- -- open MorphismProperties public
-- -- open CategoryProperties public
-- open MakeFunctor public

open MorphismProperties public
open CategoryProperties public