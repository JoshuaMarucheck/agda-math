open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; inspect; Reveal_·_is_; [_])
open import Relation.Nullary.Negation using (¬_)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_; _×_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Function using (_∘_)

open import Plasmaduck.Util.Case using (case_of_)
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

maybe-monad : (α : Level) → Monad α α
maybe-monad α = record {
    M = λ A → Maybe A;
    _>>=_ = bind;
    unit = just;
    unit-left-id-for-bind = λ f x → _≡_.refl;
    unit-right-id-for-bind = just-right-id-for-bind;
    >=>-assoc = >=>-assoc
    } where
        bind : {A B : Set α} → Maybe A → (A → Maybe B) → Maybe B
        bind mx f = case mx of λ {(just x) → f x; nothing → nothing}

        just-right-id-for-bind : {A : Set α} → (mx : Maybe A) → bind mx just ≡ mx
        just-right-id-for-bind (just x) = _≡_.refl
        just-right-id-for-bind nothing = _≡_.refl

        _⇛_ : (A B : Set α) → Set α
        _⇛_ A B = A → Maybe B
        infixr 0 _⇛_

        _>=>_ : {A B C : Set α} → (f : A ⇛ B) (g : B ⇛ C) → A ⇛ C
        _>=>_ f g x = bind (f x) g

        >=>-assoc : {A B C D : Set α} → (f : A ⇛ B) (g : B ⇛ C) (h : C ⇛ D) → (f >=> g) >=> h ≈ f >=> (g >=> h)
        >=>-assoc f g h x with f x | inspect f x
        >=>-assoc f g h x | nothing | [ _ ] = _≡_.refl
        >=>-assoc f g h x | just y | [ _ ] = _≡_.refl


unit-monad : (α : Level) → Monad α lzero
unit-monad α = record {
    M = λ A → ⊤;
    _>>=_ = λ _ _ → tt;
    unit = λ _ → tt;
    unit-left-id-for-bind = λ f x → _≡_.refl;
    unit-right-id-for-bind = λ mx → _≡_.refl;
    >=>-assoc = λ f g h x → _≡_.refl
    }

-------------------------------------
-- Some Properties Monads can have --
-------------------------------------

record ProvesEverything {α β : Level} (m : Monad α β) : Set β where
    open Monad m
    field
        proves-bottom : M (Lift α ⊥)

    proves-anything : (A : Set α) → M A
    proves-anything A = map {A = Lift α ⊥} {B = A} (λ ()) proves-bottom

record DoesNotProveBottom {α β : Level} (m : Monad α β) : Set (lsuc α ⊔ β) where
    open Monad m
    field
        does-not-prove-bottom : ¬ M (Lift α ⊥)

-- As an inverse to unit, a monad having this property means we have M A ⇔ A.
-- In some sense, this property is classically inverse to ProvesEverything m.
-- I still have yet to find a classical monad where that holds though.
record IsProofAligned {α β : Level} (m : Monad α β) : Set (lsuc α ⊔ β) where
    open Monad m
    field
        undoable : {A : Set α} → M A → A

    does-not-prove-bottom : DoesNotProveBottom m
    does-not-prove-bottom = record {does-not-prove-bottom = λ empty → case undoable empty of λ ()}


record HasFreeNesting {α : Level} (m : Monad α α) : Set (lsuc α) where
    open Monad m
    field
        acquire : (A : Set α) → M (M A → A)

    integrate-input : (A B : Set α) → (A → M B) → (M (A → B))
    integrate-input A B f = acquire B >>= λ unpackB → unit (unpackB ∘ f)
