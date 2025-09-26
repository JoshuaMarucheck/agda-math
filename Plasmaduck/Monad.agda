open import Level using (Level; _⊔_) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary.Negation using (¬_)

open import Plasmaduck.Function using (_≈_)

module Plasmaduck.Monad where


record Monad (α β : Level) : Set (lsuc (α ⊔ β)) where
    field
        M : Set α → Set β

    _⇛_ : (A B : Set α) → Set (α ⊔ β)
    _⇛_ A B = A → M B
    infixr 0 _⇛_

    field
        _>>=_ : {A B : Set α} → M A → (A ⇛ B) → M B
        unit : {A : Set α} → A ⇛ A

    map : {A B : Set α} → (A → B) → (M A → M B)
    map = λ f mx → mx >>= (λ x → unit (f x))

    _>=>_ : {A B C : Set α} → (f : A ⇛ B) (g : B ⇛ C) → A ⇛ C
    _>=>_ f g x = f x >>= g

    field
        -- Axioms
        unit-left-id-for-bind : {A B : Set α} → (f : A ⇛ B) (x : A) → unit x >>= f ≡ f x
        unit-right-id-for-bind : {A : Set α} → (mx : M A) → mx >>= unit ≡ mx
        >=>-assoc : {A B C D : Set α} → (f : A ⇛ B) (g : B ⇛ C) (h : C ⇛ D) → (f >=> g) >=> h ≈ f >=> (g >=> h)

-- Only works for some monads
join : {α : Level} → (m : Monad α α) → (A : Set α) → Monad.M m (Monad.M m A) → Monad.M m A
join m A mmA = mmA >>= λ z → z
    where open Monad m

-------------------------------
--- Some examples of monads ---
-------------------------------

¬¬-monad : (α : Level) → Monad α α
¬¬-monad α = record {
    M = λ S → ¬ ¬ S;
    _>>=_ = λ {A} {B} z z₁ z₂ → z (λ z₃ → z₁ z₃ z₂);
    unit = λ {A} z z₁ → z₁ z;
    unit-left-id-for-bind = λ {A} {B} f x → _≡_.refl;
    unit-right-id-for-bind = λ {A} mx → _≡_.refl;
    >=>-assoc = λ {A} {B} {C} {D} f g h x → _≡_.refl
    }
