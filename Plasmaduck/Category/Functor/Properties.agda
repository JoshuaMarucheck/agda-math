open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; cong) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open import Relation.Binary using (Setoid; Rel; IsEquivalence)
open import Function using (Congruent)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)

open import Plasmaduck.SetoidExperiment.SetoidMachinery using (SetoidFunction; discrete-setoid; SetoidFunction₂)
open import Plasmaduck.Function.Properties using (Congruent₂)
open import Plasmaduck.Category.Category using (RawCategory; Category; RawFunctor; Functor)
open import Plasmaduck.Util.TypeChange using (change-type; change-type-trans'; change-type-proof-irrelevance; change-type-relation-dependence-irrelevance; change-type-flatten; change-type-elim)
open import Plasmaduck.Function using (≈-isEquivalence)
open import Plasmaduck.Data.Product using (×≡)
open import Plasmaduck.Util.Case using (case_of_)
open import Plasmaduck.Relation.OperatorDefs using (SameRel)
open import Plasmaduck.Relation.Operator using (IsEquivalence-transferrable)
open import Plasmaduck.Category.Functor.SimpleFunctors using (id-functor; id-raw-functor)
open import Plasmaduck.Relation.On using (on-preserves-equality)



module Plasmaduck.Category.Functor.Properties where

variable
    a b c α β γ ℓ₁ ℓ₂ ℓ₃ l₁ l₂ l₃ : Level


module RawFunctorEquality (𝔸 : RawCategory a b c) (𝔹 : RawCategory α β γ) where
    open RawFunctor using (mapₒ; mapₘ)
    open RawCategory 𝔸 using () renaming (Object to Object₁; Morphism to Morphism₁)
    open RawCategory 𝔹 using () renaming (Object to Object₂; Morphism to Morphism₂; Morphism' to Morphism'₂)

    -- This is a normal and sane thing to do, I assure you
    private
        module _ {ℓ₁ ℓ₂ : Level} {A : Set ℓ₁} {B : Set ℓ₂} where
            open IsEquivalence (≈-isEquivalence {A = A} {B = λ _ → B}) using () renaming (refl to ≈-refl; sym to ≈-sym; trans to ≈-trans) public

    -- If we just jump into defining things, we need to use change-type to show that the functors are acting on the same items,
    -- which makes proving the equality hard at the end.
    -- So first, we define this weak equality, and then below we'll generalize it.
    mapₒ-type = Object₁ → Object₂
    mapₘ-type : mapₒ-type → Set _
    mapₘ-type mapₒ = {x y : Object₁} → Morphism₁ x y → Morphism₂ (mapₒ x) (mapₒ y)

    standard-proof' : {m₁ m₂ : mapₒ-type} (m≈ : Plasmaduck.Function._≈_ m₁ m₂) →
        {X Y : 𝔸 .RawCategory.Object} → Morphism'₂ (m₁ X) (m₁ Y) ≡ Morphism'₂ (m₂ X) (m₂ Y)
    standard-proof' {m₁} {m₂} m₁≈m₂ {X} {Y} =
        Morphism'₂ (m₁ X) (m₁ Y) ≡⟨ cong (λ q → Morphism'₂ (m₁ X) q) (m₁≈m₂ Y) ⟩
        Morphism'₂ (m₁ X) (m₂ Y) ≡⟨ cong (λ q → Morphism'₂ q (m₂ Y)) (m₁≈m₂ X) ⟩
        Morphism'₂ (m₂ X) (m₂ Y) ∎
        where open ≡-Reasoning

    standard-proof : {m₁ m₂ : mapₒ-type} (m≈ : Plasmaduck.Function._≈_ m₁ m₂) →
        {X Y : 𝔸 .RawCategory.Object} → Morphism₂ (m₁ X) (m₁ Y) ≡ Morphism₂ (m₂ X) (m₂ Y)
    standard-proof m₁≈m₂ = cong Setoid.Carrier (standard-proof' m₁≈m₂)

    change-to-m :
        (F : RawFunctor 𝔸 𝔹) →
        (m : mapₒ-type) → (F≈m : Plasmaduck.Function._≈_ (F .mapₒ) m) →
        {X Y : 𝔸 .RawCategory.Object} (f : RawCategory.Morphism 𝔹 (F .mapₒ X) (F .mapₒ Y)) →
        RawCategory.Morphism 𝔹 (m X) (m Y)
    change-to-m F m F≈m {X} {Y} f = change-type (standard-proof F≈m) f

    ≈-morph-map-on : (S T : RawFunctor 𝔸 𝔹) (m : mapₒ-type) → Set _
    ≈-morph-map-on S T m =
        Σ (Plasmaduck.Function._≈_ (S .mapₒ) m) λ S≈m →
        Σ (Plasmaduck.Function._≈_ (T .mapₒ) m) λ T≈m →
        ∀ {X Y : 𝔸 .RawCategory.Object} (f : RawCategory.Morphism 𝔸 X Y) → RawCategory._~_ 𝔹 (change-to-m S m S≈m (mapₘ S f)) (change-to-m T m T≈m (mapₘ T f))

    strong-≈-morph-map : (S T : RawFunctor 𝔸 𝔹) → Set _
    strong-≈-morph-map S T = Σ mapₒ-type (≈-morph-map-on S T)

    strong-≈-morph-map-transfer : (S T : RawFunctor 𝔸 𝔹) → (m₁ m₂ : mapₒ-type) → Plasmaduck.Function._≈_ m₁ m₂ → ≈-morph-map-on S T m₁ → ≈-morph-map-on S T m₂
    strong-≈-morph-map-transfer S T m₁ m₂ m₁≈m₂ (S≈m₁ , T≈m₁ , ST-same-map) = ≈-trans S≈m₁ m₁≈m₂ , ≈-trans T≈m₁ m₁≈m₂ , λ {X} {Y} f → begin
        change-to-m S m₂ (≈-trans S≈m₁ m₁≈m₂) (mapₘ S f)                                                                        ≈⟨ reflexive (≡-sym (change-type-trans' (standard-proof S≈m₁) (cong (λ q → Morphism₂ (q .proj₁) (q .proj₂)) (×≡ (m₁≈m₂ X) (m₁≈m₂ Y))) (standard-proof (≈-trans S≈m₁ m₁≈m₂)) {x = mapₘ S f})) ⟩
        change-type (cong (λ q → Morphism₂ (q .proj₁) (q .proj₂)) (×≡ (m₁≈m₂ X) (m₁≈m₂ Y))) (change-to-m S m₁ S≈m₁ (mapₘ S f))  ≈⟨ change-type-relation-dependence-irrelevance {A = Object₂ × Object₂} (λ (X , Y) → RawCategory.Morphism 𝔹 X Y) (λ {(X , Y)} f g → RawCategory._~_ 𝔹 f g) {i = m₁ X , m₁ Y} {j = m₂ X , m₂ Y} (×≡ (m₁≈m₂ X) (m₁≈m₂ Y)) (change-to-m S m₁ S≈m₁ (mapₘ S f)) (change-to-m T m₁ T≈m₁ (mapₘ T f)) (ST-same-map f) ⟩
        change-type (cong (λ q → Morphism₂ (q .proj₁) (q .proj₂)) (×≡ (m₁≈m₂ X) (m₁≈m₂ Y))) (change-to-m T m₁ T≈m₁ (mapₘ T f))  ≈⟨ reflexive (change-type-trans' (standard-proof T≈m₁) (cong (λ q → Morphism₂ (q .proj₁) (q .proj₂)) (×≡ (m₁≈m₂ X) (m₁≈m₂ Y))) (standard-proof (≈-trans T≈m₁ m₁≈m₂)) {x = mapₘ T f}) ⟩
        change-to-m T m₂ (≈-trans T≈m₁ m₁≈m₂) (mapₘ T f)                                                                        ∎
        where
            module _ {X Y : Object₂} where
                open import Relation.Binary.Reasoning.Setoid (RawCategory.Morphism' 𝔹 X Y) public
                open IsEquivalence (RawCategory.Morphism' 𝔹 X Y .Setoid.isEquivalence) using (reflexive) public

    strong-≈-morph-map-eq : IsEquivalence strong-≈-morph-map
    strong-≈-morph-map-eq = record {
        refl = λ {F} → F .mapₒ , (λ _ → ≡-refl) , (λ _ → ≡-refl) , (λ f → RawCategory.~-refl 𝔹);
        sym = λ {F} {G} (m , F≈m , G≈m , same-map) → m , G≈m , F≈m , λ f → RawCategory.~-sym 𝔹 (same-map f);
        trans = λ {F} {G} {H} (m₁ , F≈m₁ , G≈m₁ , FG-same-map) (m₂ , m₂-pf@(G≈m₂ , H≈m₂ , GH-same-map₂)) → case (strong-≈-morph-map-transfer G H m₂ m₁ (≈-trans (≈-sym G≈m₂) G≈m₁) m₂-pf) of λ {
            (G≈m₁' , H≈m₁ , GH-same-map₁) → m₁ , F≈m₁ , H≈m₁ , (λ {X} {Y} f → RawCategory.~-trans 𝔹 (FG-same-map f) (begin
                change-to-m G m₁ G≈m₁ (mapₘ G f)    ≈⟨ reflexive (change-type-proof-irrelevance (standard-proof G≈m₁) (standard-proof G≈m₁')) ⟩
                change-to-m G m₁ G≈m₁' (mapₘ G f)   ≈⟨ GH-same-map₁ f ⟩
                change-to-m H m₁ H≈m₁ (mapₘ H f)    ∎
                ))
            }
        }
        where
            module _ {X Y : Object₂} where
                open import Relation.Binary.Reasoning.Setoid (RawCategory.Morphism' 𝔹 X Y) public
                open IsEquivalence (RawCategory.Morphism' 𝔹 X Y .Setoid.isEquivalence) using (reflexive) public


    -- And now we define the actual relation we're using
    ≈-obj-map : Rel (RawFunctor 𝔸 𝔹) _
    ≈-obj-map S T = Plasmaduck.Function._≈_ (S .mapₒ) (T .mapₒ)

    ≈-morph-map : (S T : RawFunctor 𝔸 𝔹) → ≈-obj-map S T → Set _
    ≈-morph-map S T same-obj-map = ∀ {X Y : 𝔸 .RawCategory.Object} (f : RawCategory.Morphism 𝔸 X Y) → RawCategory._~_ 𝔹 (change-type (
        RawCategory.Morphism 𝔹 (S .mapₒ X) (S .mapₒ Y)   ≡⟨ cong (λ q → RawCategory.Morphism 𝔹 (S .mapₒ X) q) (same-obj-map Y) ⟩
        RawCategory.Morphism 𝔹 (S .mapₒ X) (T .mapₒ Y)   ≡⟨ cong (λ q → RawCategory.Morphism 𝔹 q (T .mapₒ Y)) (same-obj-map X) ⟩
        RawCategory.Morphism 𝔹 (T .mapₒ X) (T .mapₒ Y)   ∎
        ) (mapₘ S f)) (mapₘ T f)
        where open ≡-Reasoning

    SameRawFunctor : Rel (RawFunctor 𝔸 𝔹) _
    SameRawFunctor S T = Σ (≈-obj-map S T) λ same-obj-map → ≈-morph-map S T same-obj-map

    same-rel-pf : SameRel (RawFunctor 𝔸 𝔹) strong-≈-morph-map SameRawFunctor
    same-rel-pf = (λ {F} {G} (m , F≈m , G≈m , same-map) → ≈-trans F≈m (≈-sym G≈m) , λ {X} {Y} f → begin
            change-type _ (mapₘ F f)                                                                                                            ≈⟨ reflexive (≡-sym (change-type-trans' (standard-proof F≈m) (cong (λ q → Morphism₂ (q .proj₁) (q .proj₂)) (×≡ (≡-sym (G≈m X)) (≡-sym (G≈m Y)))) _)) ⟩
            change-type (cong (λ q → Morphism₂ (q .proj₁) (q .proj₂)) (×≡ (≡-sym (G≈m X)) (≡-sym (G≈m Y)))) (change-to-m F m F≈m (mapₘ F f))    ≈⟨ change-type-relation-dependence-irrelevance {A = Object₂ × Object₂} (λ (X , Y) → RawCategory.Morphism 𝔹 X Y) (λ {(X , Y)} f g → RawCategory._~_ 𝔹 f g) {i = m X , m Y} {j = mapₒ G X , mapₒ G Y} (×≡ (≡-sym (G≈m X)) (≡-sym (G≈m Y))) (change-to-m F m F≈m (mapₘ F f)) (change-to-m G m G≈m (mapₘ G f)) (same-map f) ⟩
            change-type (cong (λ q → Morphism₂ (q .proj₁) (q .proj₂)) (×≡ (≡-sym (G≈m X)) (≡-sym (G≈m Y)))) (change-to-m G m G≈m (mapₘ G f))    ≈⟨ reflexive (change-type-flatten (standard-proof G≈m) (cong (λ q → Morphism₂ (q .proj₁) (q .proj₂)) (×≡ (≡-sym (G≈m X)) (≡-sym (G≈m Y)))) {x = mapₘ G f}) ⟩
            mapₘ G f                                                                                                                            ∎
        ) , (
            λ {F} {G} (same-obj-map , same-morph-map) → G .mapₒ , same-obj-map , ≈-refl , λ {X} {Y} f → begin
            change-to-m F (mapₒ G) same-obj-map (mapₘ F f)  ≈⟨ reflexive (change-type-proof-irrelevance (standard-proof same-obj-map) _) ⟩
            change-type _ (mapₘ F f)                        ≈⟨ same-morph-map f ⟩
            mapₘ G f                                        ≈⟨ reflexive (≡-sym (change-type-elim _)) ⟩
            change-to-m G (mapₒ G) ≈-refl (mapₘ G f)        ∎
            )
        where
            module _ {X Y : Object₂} where
                open import Relation.Binary.Reasoning.Setoid (RawCategory.Morphism' 𝔹 X Y) public
                open IsEquivalence (RawCategory.Morphism' 𝔹 X Y .Setoid.isEquivalence) using (reflexive) public

    ≈'-eq : IsEquivalence SameRawFunctor
    ≈'-eq = IsEquivalence-transferrable (discrete-setoid (RawFunctor 𝔸 𝔹)) same-rel-pf strong-≈-morph-map-eq

    RawFunctorSetoid : Setoid _ _
    RawFunctorSetoid = record {
        Carrier = RawFunctor 𝔸 𝔹;
        _≈_ = SameRawFunctor;
        isEquivalence = ≈'-eq
        }

    mapₘ-change-type-commute :
        (F G : RawFunctor 𝔸 𝔹) →
        SameRawFunctor F G →
        {W X Y Z : Object₁} (f : Morphism₁ W X) →
        W ≡ Y → X ≡ Z →
        (pf₁ : Morphism₁ W X ≡ Morphism₁ Y Z) →
        (pf₂ : Morphism₂ (mapₒ F W) (mapₒ F X) ≡ Morphism₂ (mapₒ G Y) (mapₒ G Z)) →
        RawCategory._~_ 𝔹 (change-type pf₂ (mapₘ F f)) (mapₘ G (change-type pf₁ f))
    mapₘ-change-type-commute F G (same-obj-map , same-morph-map) f ≡-refl ≡-refl ≡-refl pf₂ = begin
        change-type pf₂ (mapₘ F f)  ≈⟨ reflexive (change-type-proof-irrelevance _ _ {x = mapₘ F f}) ⟩
        change-type _ (mapₘ F f)    ≈⟨ same-morph-map f ⟩
        mapₘ G f                    ∎
        where
            module _ {X Y : Object₂} where
                open import Relation.Binary.Reasoning.Setoid (RawCategory.Morphism' 𝔹 X Y) public
                open IsEquivalence (RawCategory.Morphism' 𝔹 X Y .Setoid.isEquivalence) using (reflexive) public
open RawFunctorEquality

_≈'_ : {𝔸 : RawCategory a b c} {𝔹 : RawCategory α β γ} → Rel (RawFunctor 𝔸 𝔹) _
_≈'_ {𝔸 = 𝔸} {𝔹} = SameRawFunctor 𝔸 𝔹
infix 1 _≈'_


-- the above definitions, but on Functors rather than RawFunctors
module FunctorEquality (𝔸 : Category a b c) (𝔹 : Category α β γ) where
    SameFunctor : Rel (Functor 𝔸 𝔹) _
    SameFunctor = (SameRawFunctor (𝔸 .Category.rawCategory) (𝔹 .Category.rawCategory)) Function.on Functor.rawFunctor

    ≈-eq : IsEquivalence SameFunctor
    ≈-eq = on-preserves-equality (≈'-eq (𝔸 .Category.rawCategory) (𝔹 .Category.rawCategory)) Functor.rawFunctor

    FunctorSetoid : Setoid _ _
    FunctorSetoid = record {
        Carrier = Functor 𝔸 𝔹;
        _≈_ = SameFunctor;
        isEquivalence = ≈-eq
        }
open FunctorEquality

_≈_ : {𝔸 : Category a b c} {𝔹 : Category α β γ} → Rel (Functor 𝔸 𝔹) _
_≈_ {𝔸 = 𝔸} {𝔹} = SameFunctor 𝔸 𝔹
infix 1 _≈_


module RawFunctorComposition {𝔸 : RawCategory a b c} {𝔹 : RawCategory α β γ} {ℂ : RawCategory ℓ₁ ℓ₂ ℓ₃} where
    open RawCategory 𝔸 using () renaming (Object to Object₁; Morphism to Morphism₁)
    open RawCategory 𝔹 using () renaming (Object to Object₂; Morphism to Morphism₂)
    open RawCategory ℂ using () renaming (Object to Object₃)
    open RawFunctor using (mapₒ; mapₘ)

    module _ {ℓ₁' ℓ₂' : Level} {A : Set ℓ₁'} {B : Set ℓ₂'} where
        open IsEquivalence (≈-isEquivalence {A = A} {B = λ _ → B}) using () renaming (refl to ≈-refl; sym to ≈-sym; trans to ≈-trans) public

    _∘'_ : RawFunctor 𝔹 ℂ → RawFunctor 𝔸 𝔹 → RawFunctor 𝔸 ℂ
    _∘'_ G F = record {
        mapₒ = Function._∘_ (G .mapₒ) (F .mapₒ);
        mapₘ-func = record {
            func = Function._∘_ (mapₘ G) (mapₘ F);
            respects = λ {x = x₁} {y = y₁} z →
                RawFunctor.mapₘ-func G .SetoidFunction.respects
                (RawFunctor.mapₘ-func F .SetoidFunction.respects z)
            }
        }
    infixr 9 _∘'_

    ∘'-respects : Congruent₂ (SameRawFunctor 𝔹 ℂ) (SameRawFunctor 𝔸 𝔹) (SameRawFunctor 𝔸 ℂ) _∘'_
    ∘'-respects {G₁} {G₂} {F₁} {F₂} G≈@(G-same-obj-map , G-same-morph-map) F≈@(F-same-obj-map , F-same-morph-map) = FG-same-obj-map , FG-same-morph-map
        where
            module _ where
                open ≡-Reasoning

                FG-same-obj-map : ≈-obj-map 𝔸 ℂ (G₁ ∘' F₁) (G₂ ∘' F₂)
                FG-same-obj-map x =
                    mapₒ G₁ (mapₒ F₁ x) ≡⟨ cong (mapₒ G₁) (F-same-obj-map x) ⟩
                    mapₒ G₁ (mapₒ F₂ x) ≡⟨ G-same-obj-map (mapₒ F₂ x) ⟩
                    mapₒ G₂ (mapₒ F₂ x) ∎

            module _ {X Y : Object₃} where
                open import Relation.Binary.Reasoning.Setoid (RawCategory.Morphism' ℂ X Y) public
                open IsEquivalence (RawCategory.Morphism' ℂ X Y .Setoid.isEquivalence) using (reflexive) public

            FG-same-morph-map : ≈-morph-map 𝔸 ℂ (G₁ ∘' F₁) (G₂ ∘' F₂) FG-same-obj-map
            FG-same-morph-map {X} {Y} f = begin
                change-type _ (mapₘ G₁ (mapₘ F₁ f))                                     ≈⟨ mapₘ-change-type-commute 𝔹 ℂ G₁ G₂ G≈ (mapₘ F₁ f) (F-same-obj-map X) (F-same-obj-map Y) (standard-proof 𝔸 𝔹 F-same-obj-map) _ ⟩
                mapₘ G₂ (change-type (standard-proof 𝔸 𝔹 F-same-obj-map) (mapₘ F₁ f))   ≈⟨ RawFunctor.mapₘ-respects G₂ (mapₘ-change-type-commute 𝔸 𝔹 F₁ F₂ F≈ f ≡-refl ≡-refl ≡-refl (standard-proof 𝔸 𝔹 F-same-obj-map)) ⟩
                mapₘ G₂ (mapₘ F₂ f)                                                     ∎

    RawFunctor-compose-func : SetoidFunction₂ (RawFunctorSetoid 𝔹 ℂ) (RawFunctorSetoid 𝔸 𝔹) (RawFunctorSetoid 𝔸 ℂ)
    RawFunctor-compose-func = record {
        func = _∘'_;
        respects = λ {G₁} {G₂} {F₁} {F₂} → ∘'-respects {G₁} {G₂} {F₁} {F₂}
        }
open RawFunctorComposition

∘'-assoc :
    {𝔸 : RawCategory a b c} {𝔹 : RawCategory α β γ} {ℂ : RawCategory ℓ₁ ℓ₂ ℓ₃} {𝔻 : RawCategory l₁ l₂ l₃} →
    (H : RawFunctor ℂ 𝔻) → (G : RawFunctor 𝔹 ℂ) → (F : RawFunctor 𝔸 𝔹) →
    H ∘' (G ∘' F) ≈' (H ∘' G) ∘' F
∘'-assoc {𝔸 = 𝔸} {𝔹} {ℂ} {𝔻} H G F = ≈'-eq 𝔸 𝔻 .IsEquivalence.refl {x = H ∘' G ∘' F}

∘'-left-id :
    {𝔸 : RawCategory a b c} {𝔹 : RawCategory α β γ} {F : RawFunctor 𝔸 𝔹} →
    id-raw-functor 𝔹 ∘' F ≈' F
∘'-left-id {𝔸 = 𝔸} {𝔹} {F} = ≈'-eq 𝔸 𝔹 .IsEquivalence.refl {x = F}

∘'-right-id :
    {𝔸 : RawCategory a b c} {𝔹 : RawCategory α β γ} {F : RawFunctor 𝔸 𝔹} →
    F ∘' id-raw-functor 𝔸 ≈' F
∘'-right-id {𝔸 = 𝔸} {𝔹} {F} = ≈'-eq 𝔸 𝔹 .IsEquivalence.refl {x = F}



module FunctorComposition {𝔸 : Category a b c} {𝔹 : Category α β γ} {ℂ : Category ℓ₁ ℓ₂ ℓ₃} where
    open Category 𝔸 using () renaming (Object to Object₁; Morphism to Morphism₁)
    open Category 𝔹 using () renaming (Object to Object₂; Morphism to Morphism₂)
    open Category ℂ using () renaming (Object to Object₃)
    open Functor using (mapₒ; mapₘ)

    module _ {ℓ₁' ℓ₂' : Level} {A : Set ℓ₁'} {B : Set ℓ₂'} where
        open IsEquivalence (≈-isEquivalence {A = A} {B = λ _ → B}) using () renaming (refl to ≈-refl; sym to ≈-sym; trans to ≈-trans) public

    _∘_ : Functor 𝔹 ℂ → Functor 𝔸 𝔹 → Functor 𝔸 ℂ
    _∘_ G F = record {
        rawFunctor = (G .Functor.rawFunctor) ∘' (F .Functor.rawFunctor);
        isFunctor = record {
            consistent-on-id = λ {x} →
                Category.~-trans ℂ
                (Functor.mapₘ-respects G (Functor.consistent-on-id F))
                (Functor.consistent-on-id G);
            consistent-on-∘ = λ {x} {y} {z} g f →
                Category.~-trans ℂ
                (Functor.mapₘ-respects G (Functor.consistent-on-∘ F g f))
                (Functor.consistent-on-∘ G (mapₘ F g) (mapₘ F f))
            }
        }
    infixr 9 _∘_

    ∘-respects : Congruent₂ (SameFunctor 𝔹 ℂ) (SameFunctor 𝔸 𝔹) (SameFunctor 𝔸 ℂ) _∘_
    ∘-respects {G₁} {G₂} {F₁} {F₂} G≈ F≈ = ∘'-respects {𝔸 = 𝔸 .Category.rawCategory} {𝔹 = 𝔹 .Category.rawCategory} {ℂ = ℂ .Category.rawCategory} {G₁ .Functor.rawFunctor} {G₂ .Functor.rawFunctor} {F₁ .Functor.rawFunctor} {F₂ .Functor.rawFunctor} G≈ F≈

    Functor-compose-func : SetoidFunction₂ (FunctorSetoid 𝔹 ℂ) (FunctorSetoid 𝔸 𝔹) (FunctorSetoid 𝔸 ℂ)
    Functor-compose-func = record {
        func = _∘_;
        respects = λ {G₁} {G₂} {F₁} {F₂} → ∘-respects {G₁} {G₂} {F₁} {F₂}
        }
open FunctorComposition

∘-assoc :
    {𝔸 : Category a b c} {𝔹 : Category α β γ} {ℂ : Category ℓ₁ ℓ₂ ℓ₃} {𝔻 : Category l₁ l₂ l₃} →
    (H : Functor ℂ 𝔻) → (G : Functor 𝔹 ℂ) → (F : Functor 𝔸 𝔹) →
    (H ∘ (G ∘ F)) ≈ ((H ∘ G) ∘ F)
∘-assoc {𝔸 = 𝔸} {𝔹} {ℂ} {𝔻} H G F = (λ _ → ≡-refl) , (λ {X} {Y} f → Category.~-refl 𝔻)

∘-left-id :
    {𝔸 : Category a b c} {𝔹 : Category α β γ} {F : Functor 𝔸 𝔹} →
    id-functor 𝔹 ∘ F ≈ F
∘-left-id {𝔸 = 𝔸} {𝔹} {F} = (λ _ → ≡-refl) , (λ {X} {Y} f → Category.~-refl 𝔹)

∘-right-id :
    {𝔸 : Category a b c} {𝔹 : Category α β γ} {F : Functor 𝔸 𝔹} →
    F ∘ id-functor 𝔸 ≈ F
∘-right-id {𝔸 = 𝔸} {𝔹} {F} = (λ _ → ≡-refl) , (λ {X} {Y} f → Category.~-refl 𝔹)


open RawFunctorEquality using (≈'-eq; RawFunctorSetoid) public
open RawFunctorComposition using (_∘'_; ∘'-respects; RawFunctor-compose-func) public

open FunctorEquality using (≈-eq; FunctorSetoid) public
open FunctorComposition using (_∘_; ∘-respects; Functor-compose-func) public
