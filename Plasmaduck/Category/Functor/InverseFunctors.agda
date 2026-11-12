open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_) renaming (cong to ≡-cong; refl to ≡-refl)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
import Function
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary using (Setoid; IsEquivalence; Reflexive; Symmetric; Transitive; Sym; Trans)

open import Plasmaduck.Data.Product using (×≡)
open import Plasmaduck.Util.TypeChange using (change-type; change-type-relation-dependence-irrelevance'; change-type-swap-to-right)
open import Plasmaduck.Category.Category using (RawCategory; Category; RawFunctor; Functor; ContravariantFunctor; opposite-category)
open import Plasmaduck.Category.ExampleCategories.SimpleCategories using (𝟙; 𝐒𝐞𝐭𝐨𝐢𝐝)
open import Plasmaduck.Category.ExampleCategories.Product using (restrict-bifunctor-left; restrict-bifunctor-right) renaming (_×_ to _×-category_)
open import Plasmaduck.Category.Functor.SimpleFunctors using (id-functor)
open import Plasmaduck.Category.Functor.Properties using (module RawFunctorEquality; module FunctorEquality) renaming (_∘_ to _∘-Functor_; _≈_ to _≈-Functor_; ≈-eq to ≈-Functor-eq)

{-
    This module defines an extremely strong form of category equality.
    Usually, this is too strong for most purposes, but it can be nice for, say,
    showing that ℂ = ℂ × 𝟙 or something like that.
-}
module Plasmaduck.Category.Functor.InverseFunctors where

variable
    a b c α β γ ℓ₁ ℓ₂ ℓ₃ l₁ l₂ l₃ : Level

open Functor using (mapₒ; mapₘ)

-- record SidedInverseFunctors {𝔸 : Category a b c} {𝔹 : Category α β γ} (G : Functor 𝔹 𝔸) (F : Functor 𝔸 𝔹) : Set (a ⊔ b ⊔ c) where
--     open Category 𝔸 using () renaming (_~_ to _~₁_)
--     field
--         mapₒ-inverse : ∀ (X : Category.Object 𝔸) → mapₒ G (mapₒ F X) ≡ X

--         mapₘ-inverse : ∀ {X Y : Category.Object 𝔸} (f : Category.Morphism 𝔸 X Y) →
--             change-type (≡-cong (λ (p , q) → Category.Morphism 𝔸 p q) (×≡ (mapₒ-inverse X) (mapₒ-inverse Y))) (mapₘ G (mapₘ F f)) ~₁ f
-- open SidedInverseFunctors

-- Note that morphism equality here requires a change-type.
-- The change-type is on the left, so that
-- change-type _ (mapₘ G (mapₘ F f)) ~ f
SidedInverseFunctors : {𝔸 : Category a b c} {𝔹 : Category α β γ} (G : Functor 𝔹 𝔸) (F : Functor 𝔸 𝔹) → Set _
SidedInverseFunctors {𝔸 = 𝔸} G F = G ∘-Functor F ≈-Functor id-functor 𝔸

InverseFunctors : {𝔸 : Category a b c} {𝔹 : Category α β γ} (G : Functor 𝔹 𝔸) (F : Functor 𝔸 𝔹) → Set _
InverseFunctors G F = SidedInverseFunctors G F × SidedInverseFunctors F G

-- TODO what to call this
HasFunctorInjection : (𝔸 : Category a b c) (𝔹 : Category α β γ) → Set _
HasFunctorInjection 𝔸 𝔹 = Σ (Functor 𝔸 𝔹) λ G → Σ (Functor 𝔹 𝔸) λ F → SidedInverseFunctors G F

-- TODO I can probably make the functor args implicit if I do this with raw functors instead
thing-resp : {𝔸 : Category a b c} {𝔹 : Category α β γ} {ℂ : Category ℓ₁ ℓ₂ ℓ₃} (F : Functor 𝔹 𝔸) (G : Functor ℂ 𝔹) (G' : Functor 𝔹 ℂ) (F' : Functor 𝔸 𝔹) →
    SidedInverseFunctors F F' → SidedInverseFunctors G G' → SidedInverseFunctors (F ∘-Functor G) (G' ∘-Functor F')
thing-resp {𝔸 = 𝔸} {𝔹} F G G' F' (FF'X=X , FF'f~f) (GG'X=X , GG'f~f) = fst , snd
    where
        open RawFunctorEquality using (≈-obj-map; ≈-morph-map)
        open FunctorEquality using (≈-eq)

        fst : ≈-obj-map (Category.rawCategory 𝔸) (Category.rawCategory 𝔸)
            (((λ r → Functor.rawFunctor r) Function.-⟨ Function.const ∣)
            ((F ∘-Functor G) ∘-Functor G' ∘-Functor F') (id-functor 𝔸))
            ((Function.∣ Function.constᵣ ⟩- (λ r → Functor.rawFunctor r))
            ((F ∘-Functor G) ∘-Functor G' ∘-Functor F') (id-functor 𝔸))
        fst X = begin
            mapₒ F (mapₒ G (mapₒ G' (mapₒ F' X))) ≡⟨ ≡-cong (mapₒ F) (GG'X=X (mapₒ F' X)) ⟩
            mapₒ F (mapₒ F' X)                    ≡⟨ FF'X=X X ⟩
            X                                     ∎
            where open ≡-Reasoning

        snd : ≈-morph-map (Category.rawCategory 𝔸) (Category.rawCategory 𝔸)
            (((λ r → Functor.rawFunctor r) Function.-⟨ Function.const ∣)
            ((F ∘-Functor G) ∘-Functor G' ∘-Functor F') (id-functor 𝔸))
            ((Function.∣ Function.constᵣ ⟩- (λ r → Functor.rawFunctor r))
            ((F ∘-Functor G) ∘-Functor G' ∘-Functor F') (id-functor 𝔸))
            fst
        snd {X} {Y} f = begin
            change-type pf₁ (mapₘ F (mapₘ G (mapₘ G' (mapₘ F' f))))   ≈⟨ {! ≡-cong (λ q → change-type _ (mapₘ F q)) ?  !} ⟩
            change-type pf₁ (mapₘ F (mapₘ G (mapₘ G' (mapₘ F' f))))   ≈⟨ change-type-relation-dependence-irrelevance' {A = Object₁ × Object₁} (λ (X , Y) → Category.Morphism 𝔸 X Y) (Category._~_ 𝔸) (×≡ (fst X) (fst Y)) pf₁ _ _ (Functor.mapₘ-respects F (Category.~-sym 𝔹 ((≈-eq 𝔹 𝔹 .IsEquivalence.sym pf₂ .proj₂ (mapₘ F' f))))) ⟩  -- Functor.mapₘ-respects F ? -- Category.~-reflexive 𝔸 (≡-cong (λ q → change-type _ (mapₘ F q)) ?)
            change-type pf₁ (mapₘ F (change-type _ (mapₘ F' f)))      ≈⟨ {! GG'f~f (mapₘ F' f)  !} ⟩
            f ∎
            where
                -- lol, did u know u can do this? i didn't
                -- this lets me force all the change-type proofs to be the same,
                -- without needing to know what the proof is
                pf₁ = _
                pf₂ = _

                open Category 𝔸 using () renaming (Object to Object₁)
                module _ {A B : Category.Object 𝔸} where
                    open import Relation.Binary.Reasoning.Setoid (Category.Morphism' 𝔸 A B) public

SameCategory : (𝔸 : Category a b c) (𝔹 : Category α β γ) → Set _
SameCategory 𝔸 𝔹 = Σ (Functor 𝔸 𝔹) λ G → Σ (Functor 𝔹 𝔸) λ F → InverseFunctors G F

SameCategory-refl : Reflexive (SameCategory {a} {b} {c})
SameCategory-refl {x = 𝔸} = id-functor 𝔸 , id-functor 𝔸 , ((λ x → ≡-refl) , λ {X} {Y} f → Category.~-refl 𝔸) , ((λ x → ≡-refl) , λ {X} {Y} f → Category.~-refl 𝔸)

SameCategory-sym : Sym (SameCategory {a} {b} {c} {α} {β} {γ}) SameCategory
SameCategory-sym {x = 𝔸} {y = 𝔹} (G , F , GF~id , FG~id) = F , G , FG~id , GF~id

-- HasFunctorInjection-trans : Trans (HasFunctorInjection {a} {b} {c} {α} {β} {γ}) (HasFunctorInjection {α} {β} {γ} {ℓ₁} {ℓ₂} {ℓ₃}) HasFunctorInjection
-- HasFunctorInjection-trans {i = 𝔸} {j = 𝔹} {k = ℂ} (F , F' , FF'-inv) (G , G' , GG'-inv) = G ∘-Functor F , F' ∘-Functor G' , {!   !} , {!   !}

SameCategory-trans : Trans (SameCategory {a} {b} {c} {α} {β} {γ}) (SameCategory {α} {β} {γ} {ℓ₁} {ℓ₂} {ℓ₃}) SameCategory
SameCategory-trans {i = 𝔸} {j = 𝔹} {k = ℂ} (F , F' , FF'-inv , F'F-inv) (G , G' , GG'-inv , G'G-inv) = G ∘-Functor F , F' ∘-Functor G' , thing-resp G F F' G' GG'-inv FF'-inv , thing-resp F' G' G F F'F-inv G'G-inv
-- record {
--     mapₒ-inverse = λ X → begin
--         mapₒ G (mapₒ F (mapₒ F' (mapₒ G' X)))   ≡⟨ ≡-cong (mapₒ G) (FF'-inv .mapₒ-inverse (mapₒ G' X)) ⟩
--         mapₒ G (mapₒ G' X)                      ≡⟨ GG'-inv .mapₒ-inverse X ⟩
--         X                                       ∎;
--     mapₘ-inverse = λ {X} {Y} f → {! begin   !}
--     } , {!   !}
--     where open ≡-Reasoning

--     -- begin
--     --     mapₒ F' (mapₒ G' (mapₒ G (mapₒ F X)))   ≡⟨ {! G'G-inv .mapₒ-inverse   !} ⟩
--     --     mapₒ F' (mapₒ F X)                      ≡⟨ {!   !} ⟩
--     --     X                                       ∎


-- SameCategory-refl : Reflexive (SameCategory {a} {b} {c})
-- SameCategory-refl {x = 𝔸} = id-functor 𝔸 , id-functor 𝔸 , record {
--         mapₒ-inverse = λ X → ≡-refl;
--         mapₘ-inverse = λ f → Category.~-refl 𝔸
--     } , record {
--         mapₒ-inverse = λ X → ≡-refl;
--         mapₘ-inverse = λ f → Category.~-refl 𝔸
--     }

-- SameCategory-sym : Sym (SameCategory {a} {b} {c} {α} {β} {γ}) SameCategory
-- SameCategory-sym {x = 𝔸} {y = 𝔹} (G , F , GF~id , FG~id) = F , G , FG~id , GF~id

-- SameCategory-trans : Trans (SameCategory {a} {b} {c} {α} {β} {γ}) (SameCategory {α} {β} {γ} {ℓ₁} {ℓ₂} {ℓ₃}) SameCategory
-- SameCategory-trans {i = 𝔸} {j = 𝔹} {k = ℂ} (F , F' , FF'-inv , F'F-inv) (G , G' , GG'-inv , G'G-inv) = G ∘-Functor F , F' ∘-Functor G' , record {
--     mapₒ-inverse = λ X → begin
--         mapₒ G (mapₒ F (mapₒ F' (mapₒ G' X)))   ≡⟨ ≡-cong (mapₒ G) (FF'-inv .mapₒ-inverse (mapₒ G' X)) ⟩
--         mapₒ G (mapₒ G' X)                      ≡⟨ GG'-inv .mapₒ-inverse X ⟩
--         X                                       ∎;
--     mapₘ-inverse = λ {X} {Y} f → {! begin   !}
--     } , {!   !}
--     where open ≡-Reasoning

--     -- begin
--     --     mapₒ F' (mapₒ G' (mapₒ G (mapₒ F X)))   ≡⟨ {! G'G-inv .mapₒ-inverse   !} ⟩
--     --     mapₒ F' (mapₒ F X)                      ≡⟨ {!   !} ⟩
--     --     X                                       ∎
