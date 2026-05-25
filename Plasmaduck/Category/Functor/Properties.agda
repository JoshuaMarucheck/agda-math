open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; cong) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open import Relation.Binary using (Setoid; Rel; IsEquivalence)
open import Function using (Congruent)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)

open import Plasmaduck.SetoidExperiment.SetoidMachinery using (SetoidFunction; discrete-setoid; SetoidFunction₂)
open import Plasmaduck.Function.Properties using (Congruent₂)
open import Plasmaduck.Category.Category using (Category; Functor)
open import Plasmaduck.Util.TypeChange using (change-type; change-type-trans'; change-type-proof-irrelevance; change-type-relation-dependence-irrelevance; change-type-flatten; change-type-elim)
open import Plasmaduck.Function using (≈-isEquivalence)
open import Plasmaduck.Data.Product using (×≡)
open import Plasmaduck.Util.Case using (case_of_)
open import Plasmaduck.Relation.OperatorDefs using (SameRel)
open import Plasmaduck.Relation.Operator using (IsEquivalence-transferrable)
open import Plasmaduck.Category.Functor.SimpleFunctors using (id-functor)



module Plasmaduck.Category.Functor.Properties where

variable
    a b c α β γ ℓ₁ ℓ₂ ℓ₃ l₁ l₂ l₃ : Level


open Functor using (mapₒ; mapₘ)
module FunctorEquality (𝔸 : Category a b c) (𝔹 : Category α β γ) where
    open Category 𝔸 using () renaming (Object to Object₁; Morphism to Morphism₁)
    open Category 𝔹 using () renaming (Object to Object₂; Morphism to Morphism₂; Morphism' to Morphism'₂)

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
        {X Y : 𝔸 .Category.Object} → Morphism'₂ (m₁ X) (m₁ Y) ≡ Morphism'₂ (m₂ X) (m₂ Y)
    standard-proof' {m₁} {m₂} m₁≈m₂ {X} {Y} =
        Morphism'₂ (m₁ X) (m₁ Y) ≡⟨ cong (λ q → Morphism'₂ (m₁ X) q) (m₁≈m₂ Y) ⟩
        Morphism'₂ (m₁ X) (m₂ Y) ≡⟨ cong (λ q → Morphism'₂ q (m₂ Y)) (m₁≈m₂ X) ⟩
        Morphism'₂ (m₂ X) (m₂ Y) ∎
        where open ≡-Reasoning

    standard-proof : {m₁ m₂ : mapₒ-type} (m≈ : Plasmaduck.Function._≈_ m₁ m₂) →
        {X Y : 𝔸 .Category.Object} → Morphism₂ (m₁ X) (m₁ Y) ≡ Morphism₂ (m₂ X) (m₂ Y)
    standard-proof m₁≈m₂ = cong Setoid.Carrier (standard-proof' m₁≈m₂)

    change-to-m :
        (F : Functor 𝔸 𝔹) →
        (m : mapₒ-type) → (F≈m : Plasmaduck.Function._≈_ (F .mapₒ) m) →
        {X Y : 𝔸 .Category.Object} (f : Category.Morphism 𝔹 (F .mapₒ X) (F .mapₒ Y)) →
        Category.Morphism 𝔹 (m X) (m Y)
    change-to-m F m F≈m {X} {Y} f = change-type (standard-proof F≈m) f

    ≈-morph-map-on : (S T : Functor 𝔸 𝔹) (m : mapₒ-type) → Set _
    ≈-morph-map-on S T m =
        Σ (Plasmaduck.Function._≈_ (S .mapₒ) m) λ S≈m →
        Σ (Plasmaduck.Function._≈_ (T .mapₒ) m) λ T≈m →
        ∀ {X Y : 𝔸 .Category.Object} (f : Category.Morphism 𝔸 X Y) → Category._~_ 𝔹 (change-to-m S m S≈m (mapₘ S f)) (change-to-m T m T≈m (mapₘ T f))

    strong-≈-morph-map : (S T : Functor 𝔸 𝔹) → Set _
    strong-≈-morph-map S T = Σ mapₒ-type (≈-morph-map-on S T)

    strong-≈-morph-map-transfer : (S T : Functor 𝔸 𝔹) → (m₁ m₂ : mapₒ-type) → Plasmaduck.Function._≈_ m₁ m₂ → ≈-morph-map-on S T m₁ → ≈-morph-map-on S T m₂
    strong-≈-morph-map-transfer S T m₁ m₂ m₁≈m₂ (S≈m₁ , T≈m₁ , ST-same-map) = ≈-trans S≈m₁ m₁≈m₂ , ≈-trans T≈m₁ m₁≈m₂ , λ {X} {Y} f → begin
        change-to-m S m₂ (≈-trans S≈m₁ m₁≈m₂) (mapₘ S f)                                                                        ≈⟨ reflexive (≡-sym (change-type-trans' (standard-proof S≈m₁) (cong (λ q → Morphism₂ (q .proj₁) (q .proj₂)) (×≡ (m₁≈m₂ X) (m₁≈m₂ Y))) (standard-proof (≈-trans S≈m₁ m₁≈m₂)) {x = mapₘ S f})) ⟩
        change-type (cong (λ q → Morphism₂ (q .proj₁) (q .proj₂)) (×≡ (m₁≈m₂ X) (m₁≈m₂ Y))) (change-to-m S m₁ S≈m₁ (mapₘ S f))  ≈⟨ change-type-relation-dependence-irrelevance {A = Object₂ × Object₂} (λ (X , Y) → Category.Morphism 𝔹 X Y) (λ {(X , Y)} f g → Category._~_ 𝔹 f g) {i = m₁ X , m₁ Y} {j = m₂ X , m₂ Y} (×≡ (m₁≈m₂ X) (m₁≈m₂ Y)) (change-to-m S m₁ S≈m₁ (mapₘ S f)) (change-to-m T m₁ T≈m₁ (mapₘ T f)) (ST-same-map f) ⟩
        change-type (cong (λ q → Morphism₂ (q .proj₁) (q .proj₂)) (×≡ (m₁≈m₂ X) (m₁≈m₂ Y))) (change-to-m T m₁ T≈m₁ (mapₘ T f))  ≈⟨ reflexive (change-type-trans' (standard-proof T≈m₁) (cong (λ q → Morphism₂ (q .proj₁) (q .proj₂)) (×≡ (m₁≈m₂ X) (m₁≈m₂ Y))) (standard-proof (≈-trans T≈m₁ m₁≈m₂)) {x = mapₘ T f}) ⟩
        change-to-m T m₂ (≈-trans T≈m₁ m₁≈m₂) (mapₘ T f)                                                                        ∎
        where
            module _ {X Y : Object₂} where
                open import Relation.Binary.Reasoning.Setoid (Category.Morphism' 𝔹 X Y) public
                open IsEquivalence (Category.Morphism' 𝔹 X Y .Setoid.isEquivalence) using (reflexive) public

    strong-≈-morph-map-eq : IsEquivalence strong-≈-morph-map
    strong-≈-morph-map-eq = record {
        refl = λ {F} → F .mapₒ , (λ _ → ≡-refl) , (λ _ → ≡-refl) , (λ f → Category.~-refl 𝔹);
        sym = λ {F} {G} (m , F≈m , G≈m , same-map) → m , G≈m , F≈m , λ f → Category.~-sym 𝔹 (same-map f);
        trans = λ {F} {G} {H} (m₁ , F≈m₁ , G≈m₁ , FG-same-map) (m₂ , m₂-pf@(G≈m₂ , H≈m₂ , GH-same-map₂)) → case (strong-≈-morph-map-transfer G H m₂ m₁ (≈-trans (≈-sym G≈m₂) G≈m₁) m₂-pf) of λ {
            (G≈m₁' , H≈m₁ , GH-same-map₁) → m₁ , F≈m₁ , H≈m₁ , (λ {X} {Y} f → Category.~-trans 𝔹 (FG-same-map f) (begin
                change-to-m G m₁ G≈m₁ (mapₘ G f)    ≈⟨ reflexive (change-type-proof-irrelevance (standard-proof G≈m₁) (standard-proof G≈m₁')) ⟩
                change-to-m G m₁ G≈m₁' (mapₘ G f)   ≈⟨ GH-same-map₁ f ⟩
                change-to-m H m₁ H≈m₁ (mapₘ H f)    ∎
                ))
            }
        }
        where
            module _ {X Y : Object₂} where
                open import Relation.Binary.Reasoning.Setoid (Category.Morphism' 𝔹 X Y) public
                open IsEquivalence (Category.Morphism' 𝔹 X Y .Setoid.isEquivalence) using (reflexive) public


    -- And now we define the actual relation we're using
    ≈-obj-map : Rel (Functor 𝔸 𝔹) _
    ≈-obj-map S T = Plasmaduck.Function._≈_ (S .mapₒ) (T .mapₒ)

    ≈-morph-map : (S T : Functor 𝔸 𝔹) → ≈-obj-map S T → Set _
    ≈-morph-map S T same-obj-map = ∀ {X Y : 𝔸 .Category.Object} (f : Category.Morphism 𝔸 X Y) → Category._~_ 𝔹 (change-type (
        Category.Morphism 𝔹 (S .mapₒ X) (S .mapₒ Y)   ≡⟨ cong (λ q → Category.Morphism 𝔹 (S .mapₒ X) q) (same-obj-map Y) ⟩
        Category.Morphism 𝔹 (S .mapₒ X) (T .mapₒ Y)   ≡⟨ cong (λ q → Category.Morphism 𝔹 q (T .mapₒ Y)) (same-obj-map X) ⟩
        Category.Morphism 𝔹 (T .mapₒ X) (T .mapₒ Y)   ∎
        ) (Functor.mapₘ S f)) (Functor.mapₘ T f)
        where open ≡-Reasoning

    SameFunctor : Rel (Functor 𝔸 𝔹) _
    SameFunctor S T = Σ (≈-obj-map S T) λ same-obj-map → ≈-morph-map S T same-obj-map

    same-rel-pf : SameRel (Functor 𝔸 𝔹) strong-≈-morph-map SameFunctor
    same-rel-pf = (λ {F} {G} (m , F≈m , G≈m , same-map) → ≈-trans F≈m (≈-sym G≈m) , λ {X} {Y} f → begin
            change-type _ (mapₘ F f)                                                                                                            ≈⟨ reflexive (≡-sym (change-type-trans' (standard-proof F≈m) (cong (λ q → Morphism₂ (q .proj₁) (q .proj₂)) (×≡ (≡-sym (G≈m X)) (≡-sym (G≈m Y)))) _)) ⟩
            change-type (cong (λ q → Morphism₂ (q .proj₁) (q .proj₂)) (×≡ (≡-sym (G≈m X)) (≡-sym (G≈m Y)))) (change-to-m F m F≈m (mapₘ F f))    ≈⟨ change-type-relation-dependence-irrelevance {A = Object₂ × Object₂} (λ (X , Y) → Category.Morphism 𝔹 X Y) (λ {(X , Y)} f g → Category._~_ 𝔹 f g) {i = m X , m Y} {j = mapₒ G X , mapₒ G Y} (×≡ (≡-sym (G≈m X)) (≡-sym (G≈m Y))) (change-to-m F m F≈m (mapₘ F f)) (change-to-m G m G≈m (mapₘ G f)) (same-map f) ⟩
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
                open import Relation.Binary.Reasoning.Setoid (Category.Morphism' 𝔹 X Y) public
                open IsEquivalence (Category.Morphism' 𝔹 X Y .Setoid.isEquivalence) using (reflexive) public

    ≈-Functor-eq : IsEquivalence SameFunctor
    ≈-Functor-eq = IsEquivalence-transferrable (discrete-setoid (Functor 𝔸 𝔹)) same-rel-pf strong-≈-morph-map-eq

    FunctorSetoid : Setoid _ _
    FunctorSetoid = record {
        Carrier = Functor 𝔸 𝔹;
        _≈_ = SameFunctor;
        isEquivalence = ≈-Functor-eq
        }

    mapₘ-change-type-commute :
        (F G : Functor 𝔸 𝔹) →
        SameFunctor F G →
        {W X Y Z : Object₁} (f : Morphism₁ W X) →
        W ≡ Y → X ≡ Z →
        (pf₁ : Morphism₁ W X ≡ Morphism₁ Y Z) →
        (pf₂ : Morphism₂ (mapₒ F W) (mapₒ F X) ≡ Morphism₂ (mapₒ G Y) (mapₒ G Z)) →
        Category._~_ 𝔹 (change-type pf₂ (mapₘ F f)) (mapₘ G (change-type pf₁ f))
    mapₘ-change-type-commute F G (same-obj-map , same-morph-map) f ≡-refl ≡-refl ≡-refl pf₂ = begin
        change-type pf₂ (mapₘ F f)  ≈⟨ reflexive (change-type-proof-irrelevance _ _ {x = mapₘ F f}) ⟩
        change-type _ (mapₘ F f)    ≈⟨ same-morph-map f ⟩
        mapₘ G f                    ∎
        where
            module _ {X Y : Object₂} where
                open import Relation.Binary.Reasoning.Setoid (Category.Morphism' 𝔹 X Y) public
                open IsEquivalence (Category.Morphism' 𝔹 X Y .Setoid.isEquivalence) using (reflexive) public
open FunctorEquality

_≈-Functor_ : {𝔸 : Category a b c} {𝔹 : Category α β γ} → Rel (Functor 𝔸 𝔹) _
_≈-Functor_ {𝔸 = 𝔸} {𝔹} = SameFunctor 𝔸 𝔹
infix 1 _≈-Functor_

module FunctorComposition {𝔸 : Category a b c} {𝔹 : Category α β γ} {ℂ : Category ℓ₁ ℓ₂ ℓ₃} where
    open Category 𝔸 using () renaming (Object to Object₁; Morphism to Morphism₁)
    open Category 𝔹 using () renaming (Object to Object₂; Morphism to Morphism₂)
    open Category ℂ using () renaming (Object to Object₃)

    module _ {ℓ₁' ℓ₂' : Level} {A : Set ℓ₁'} {B : Set ℓ₂'} where
        open IsEquivalence (≈-isEquivalence {A = A} {B = λ _ → B}) using () renaming (refl to ≈-refl; sym to ≈-sym; trans to ≈-trans) public

    _∘-Functor_ : Functor 𝔹 ℂ → Functor 𝔸 𝔹 → Functor 𝔸 ℂ
    _∘-Functor_ G F = record {
        rawFunctor = record {
            mapₒ = Function._∘_ (G .mapₒ) (F .mapₒ);
            mapₘ-func = record {
                func = Function._∘_ (mapₘ G) (mapₘ F);
                respects = λ {x = x₁} {y = y₁} z →
                    Plasmaduck.Category.Category.RawFunctor.mapₘ-func
                    (G .Functor.rawFunctor) .SetoidFunction.respects
                    (Plasmaduck.Category.Category.RawFunctor.mapₘ-func
                        (F .Functor.rawFunctor) .SetoidFunction.respects z)
                }
            };
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
    infixr 9 _∘-Functor_

    ∘-Functor-respects : Congruent₂ (SameFunctor 𝔹 ℂ) (SameFunctor 𝔸 𝔹) (SameFunctor 𝔸 ℂ) _∘-Functor_
    ∘-Functor-respects {G₁} {G₂} {F₁} {F₂} G≈@(G-same-obj-map , G-same-morph-map) F≈@(F-same-obj-map , F-same-morph-map) = FG-same-obj-map , FG-same-morph-map
        where
            module _ where
                open ≡-Reasoning

                FG-same-obj-map : ≈-obj-map 𝔸 ℂ (G₁ ∘-Functor F₁) (G₂ ∘-Functor F₂)
                FG-same-obj-map x =
                    mapₒ G₁ (mapₒ F₁ x) ≡⟨ cong (mapₒ G₁) (F-same-obj-map x) ⟩
                    mapₒ G₁ (mapₒ F₂ x) ≡⟨ G-same-obj-map (mapₒ F₂ x) ⟩
                    mapₒ G₂ (mapₒ F₂ x) ∎

            module _ {X Y : Object₃} where
                open import Relation.Binary.Reasoning.Setoid (Category.Morphism' ℂ X Y) public
                open IsEquivalence (Category.Morphism' ℂ X Y .Setoid.isEquivalence) using (reflexive) public

            FG-same-morph-map : ≈-morph-map 𝔸 ℂ (G₁ ∘-Functor F₁) (G₂ ∘-Functor F₂) FG-same-obj-map
            FG-same-morph-map {X} {Y} f = begin
                change-type _ (mapₘ G₁ (mapₘ F₁ f))                                     ≈⟨ mapₘ-change-type-commute 𝔹 ℂ G₁ G₂ G≈ (mapₘ F₁ f) (F-same-obj-map X) (F-same-obj-map Y) (standard-proof 𝔸 𝔹 F-same-obj-map) _ ⟩
                mapₘ G₂ (change-type (standard-proof 𝔸 𝔹 F-same-obj-map) (mapₘ F₁ f))   ≈⟨ Functor.mapₘ-respects G₂ (mapₘ-change-type-commute 𝔸 𝔹 F₁ F₂ F≈ f ≡-refl ≡-refl ≡-refl (standard-proof 𝔸 𝔹 F-same-obj-map)) ⟩
                mapₘ G₂ (mapₘ F₂ f)                                                     ∎

    Functor-compose-func : SetoidFunction₂ (FunctorSetoid 𝔹 ℂ) (FunctorSetoid 𝔸 𝔹) (FunctorSetoid 𝔸 ℂ)
    Functor-compose-func = record {
        func = _∘-Functor_;
        respects = λ {G₁} {G₂} {F₁} {F₂} → ∘-Functor-respects {G₁} {G₂} {F₁} {F₂}
        }
open FunctorComposition

∘-Functor-assoc :
    {𝔸 : Category a b c} {𝔹 : Category α β γ} {ℂ : Category ℓ₁ ℓ₂ ℓ₃} {𝔻 : Category l₁ l₂ l₃} →
    (H : Functor ℂ 𝔻) → (G : Functor 𝔹 ℂ) → (F : Functor 𝔸 𝔹) →
    (H ∘-Functor (G ∘-Functor F)) ≈-Functor ((H ∘-Functor G) ∘-Functor F)
∘-Functor-assoc {𝔸 = 𝔸} {𝔹} {ℂ} {𝔻} H G F = (λ _ → ≡-refl) , (λ {X} {Y} f → Category.~-refl 𝔻)

∘-Functor-left-id :
    {𝔸 : Category a b c} {𝔹 : Category α β γ} {F : Functor 𝔸 𝔹} →
    id-functor 𝔹 ∘-Functor F ≈-Functor F
∘-Functor-left-id {𝔸 = 𝔸} {𝔹} {F} = (λ _ → ≡-refl) , (λ {X} {Y} f → Category.~-refl 𝔹)

∘-Functor-right-id :
    {𝔸 : Category a b c} {𝔹 : Category α β γ} {F : Functor 𝔸 𝔹} →
    F ∘-Functor id-functor 𝔸 ≈-Functor F
∘-Functor-right-id {𝔸 = 𝔸} {𝔹} {F} = (λ _ → ≡-refl) , (λ {X} {Y} f → Category.~-refl 𝔹)


open FunctorEquality using (≈-Functor-eq; FunctorSetoid) public
open FunctorComposition using (_∘-Functor_; ∘-Functor-respects; Functor-compose-func) public
