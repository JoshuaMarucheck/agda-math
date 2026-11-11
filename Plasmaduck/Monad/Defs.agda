open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; _≗_; inspect; Reveal_·_is_; [_]; cong)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_; _×_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Function using (_∘_)

open import Plasmaduck.Data.Squash using (Squash; squash; squash-function; unsquash-function)
open import Plasmaduck.Util.Case using (case_of_)



module Plasmaduck.Monad.Defs where


record RawMonad (α β : Level) : Set (lsuc (α ⊔ β)) where
    infixr 0 _⇛_
    infixl 1 _>>=_ _>=>_

    field
        M : Set α → Set β

    _⇛_ : (A B : Set α) → Set (α ⊔ β)
    _⇛_ A B = A → M B

    field
        _>>=_ : {A B : Set α} → M A → (A ⇛ B) → M B
        unit : {A : Set α} → A ⇛ A

    bind = _>>=_
    return = unit

    map : {A B : Set α} → (A → B) → (M A → M B)
    map = λ f mx → mx >>= (λ x → unit (f x))

    _>=>_ : {A B C : Set α} → (A ⇛ B) → (B ⇛ C) → (A ⇛ C)
    _>=>_ f g x = f x >>= g

    -- bind-arrow : {A B C : Set α} → (A ⇛ B) → ((A → B) → M C) → M C
    -- bind-arrow x f = (({!   !} >>= x) >>= λ b → {!   !}) >>= f


record IsMonad {α β : Level} (rawMonad : RawMonad α β) : Set (lsuc α ⊔ β) where
    open RawMonad rawMonad
    field
        unit-left-id-for-bind : {A B : Set α} → (f : A ⇛ B) (x : A) → (unit x >>= f) ≡ f x
        unit-right-id-for-bind : {A : Set α} → (mx : M A) → (mx >>= unit) ≡ mx
        >=>-assoc : {A B C D : Set α} → (f : A ⇛ B) (g : B ⇛ C) (h : C ⇛ D) → ((f >=> g) >=> h) ≗ (f >=> (g >=> h))

record Monad (α β : Level) : Set (lsuc (α ⊔ β)) where
    field
        rawMonad : RawMonad α β
        isMonad : IsMonad rawMonad

    open RawMonad rawMonad public
    open IsMonad isMonad public



-- Only works for some monads
join : {α : Level} → (m : Monad α α) → (A : Set α) → Monad.M m (Monad.M m A) → Monad.M m A
join m A mmA = mmA >>= λ z → z
    where open Monad m

-------------------------------
--- Some examples of monads ---
-------------------------------

¬¬-monad : (α : Level) → Monad α α
¬¬-monad α = record {
    rawMonad = record {
        M = λ S → ¬ ¬ S;
        _>>=_ = λ {A} {B} z z₁ z₂ → z (λ z₃ → z₁ z₃ z₂);
        unit = λ {A} z z₁ → z₁ z
        };
    isMonad = record {
        unit-left-id-for-bind = λ {A} {B} f x → _≡_.refl;
        unit-right-id-for-bind = λ {A} mx → _≡_.refl;
        >=>-assoc = λ {A} {B} {C} {D} f g h x → _≡_.refl
        }
    }

maybe-monad : (α : Level) → Monad α α
maybe-monad α = record {
    rawMonad = rawMonad;
    isMonad = record {
        unit-left-id-for-bind = λ f x → _≡_.refl;
        unit-right-id-for-bind = just-right-id-for-bind;
        >=>-assoc = >=>-assoc
        }
    } where
        bind : {A B : Set α} → Maybe A → (A → Maybe B) → Maybe B
        bind (just x) f = f x
        bind nothing f = nothing

        rawMonad : RawMonad α α
        rawMonad = record {
            M = Maybe;
            _>>=_ = bind;
            unit = just
            }
        open RawMonad rawMonad using (_⇛_; _>=>_; _>>=_)

        just-right-id-for-bind : {A : Set α} → (mx : Maybe A) → (mx >>= just) ≡ mx
        just-right-id-for-bind (just x) = _≡_.refl
        just-right-id-for-bind nothing = _≡_.refl

        >=>-assoc : {A B C D : Set α} → (f : A ⇛ B) (g : B ⇛ C) (h : C ⇛ D) → ((f >=> g) >=> h) ≗ (f >=> (g >=> h))
        >=>-assoc f g h x with f x | inspect f x
        >=>-assoc f g h x | nothing | [ _ ] = _≡_.refl
        >=>-assoc f g h x | just y | [ _ ] = _≡_.refl


unit-monad : (α : Level) → Monad α lzero
unit-monad α = record {
    rawMonad = record {
        M = λ A → ⊤;
        _>>=_ = λ _ _ → tt;
        unit = λ _ → tt
        };
    isMonad = record {
        unit-left-id-for-bind = λ f x → _≡_.refl;
        unit-right-id-for-bind = λ mx → _≡_.refl;
        >=>-assoc = λ f g h x → _≡_.refl
        }
    }

identity-monad : (α : Level) → Monad α α
identity-monad α = record {
    rawMonad = record {
        M = Function.id;
        _>>=_ = λ x f → f x;
        unit = Function.id
        };
    isMonad = record {
        unit-left-id-for-bind = λ {A} {B} f x → _≡_.refl;
        unit-right-id-for-bind = λ {A} mx → _≡_.refl;
        >=>-assoc = λ {A} {B} {C} {D} f g h x → _≡_.refl
        }
    }

axiom-monad : {α : Level} (A : Set α) → Monad α α
axiom-monad Axiom = record {
    rawMonad = record {
        M = λ B → Axiom → B;
        _>>=_ = λ ma f axiom → f (ma axiom) axiom;
        unit = λ x _ → x
        };
    isMonad = record {
        unit-left-id-for-bind = λ {A} {B} f x → _≡_.refl;
        unit-right-id-for-bind = λ {A} mx → _≡_.refl;
        >=>-assoc = λ {A} {B} {C} {D} f g h x → _≡_.refl
        }
    }

-- we cannot lift the first argument,
-- since we don't have a way to make M work on higher level things
lift-proof-monad : {α β : Level} (monad : Monad α β) → (γ : Level) → Monad α (β ⊔ γ)
lift-proof-monad monad γ = record {
    rawMonad = record {
        M = λ A → Lift γ (M A);
        _>>=_ = λ mx f → lift (mx .Lift.lower >>= λ x → f x .Lift.lower);
        unit = λ z → lift (unit z)
        };
    isMonad = record {
        unit-left-id-for-bind = λ f x → cong lift (unit-left-id-for-bind (Lift.lower ∘ f) x);
        unit-right-id-for-bind = λ mx → cong lift (unit-right-id-for-bind (mx .Lift.lower));
        >=>-assoc = λ f g h x → cong lift (>=>-assoc (Lift.lower ∘ f) (Lift.lower ∘ g) (Lift.lower ∘ h) x)
        }
    }
    where open Monad monad

-- irrelevant-monad : (α : Level) → Monad α α
-- irrelevant-monad α = record {
--     rawMonad = record {
--         M = Squash;
--         _>>=_ = λ (squash x) f → {!   !};
--         unit = λ x → squash x
--         };
--     isMonad = record {
--         unit-left-id-for-bind = {!   !};
--         unit-right-id-for-bind = {!   !};
--         >=>-assoc = {!   !}
--         }
--     }
--     where
--         beep-boop : ∀ {A : Set α} → .(Squash A) → Squash A
--         beep-boop x = squash {!   !}

--         squash-join : ∀ {A : Set α} → Squash (Squash A) → Squash A
--         squash-join (squash x) = squash {!   !}

--         irr-bind : {A B : Set α} → .A → (A → Squash B) → Squash B
--         irr-bind x f = {!     !}


-------------------------------------
-- Some properties Monads can have --
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


record ProofEquivalent {α β γ : Level} (m : Monad α β) (n : Monad α γ) : Set (lsuc α ⊔ β ⊔ γ) where
    open Monad
    field
        ⇒ : ∀ {A : Set α} → M m A → M n A
        ⇐ : ∀ {A : Set α} → M n A → M m A


--------------------
--- Monad Lemmas ---
--------------------

module MonadLemmas {α β : Level} (m : Monad α β) where
    open Monad m
    variable
        A B : Set α


-- open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc)
-- open import Function using (_∘_)
-- open import Relation.Binary using (Setoid)

-- open import Plasmaduck.SetoidExperiment.SetoidMachinery using (SetoidFunction; _⇒_; _⇒'_; _which-is-cong_; SetoidFunction₂; _←_; _←₂_; SetoidFunction₂→SetoidFunction; _∘'_; ∘'-func; flipSetoidFunction₂)



-- module Plasmaduck.Monad.Defs where

-- open Setoid using (Carrier)
-- open SetoidFunction using (domain; codomain)



-- infix 2 ≈-step
-- ≈-step : {α β : Level} (S : Setoid α β) → S .Carrier → S .Carrier → Set β
-- ≈-step S x y = S .Setoid._≈_ x y

-- syntax ≈-step S x y = x ≈[ S ] y

-- record Monad (α β γ ε : Level) : Set (lsuc α ⊔ lsuc β ⊔ lsuc γ ⊔ lsuc ε) where

--     field
--         M : Setoid α β → Setoid γ ε

--     m = Carrier ∘ M

--     field
--         Unit : {A : Setoid α β} → A ⇒' M A
--         Bind : {A B : Setoid α β} → SetoidFunction₂ (M A) (A ⇒ M B) (M B)


--     unit : {A : Setoid α β} → A .Carrier → m A
--     unit = Unit ←_

--     bind : {A B : Setoid α β} → (m A) → (A ⇒' M B) → m B
--     bind = Bind ←₂_

--     infixl 1 _>>='_ _>>=_ _>=>'_ _>=>_
--     _>>=_ = bind

--     Lift : {A B : Setoid α β} → SetoidFunction₂ (A ⇒ M B) (M A) (M B)
--     Lift = flipSetoidFunction₂ Bind

--     lift : {A B : Setoid α β} → (A ⇒' M B) → (M A ⇒' M B)
--     lift = SetoidFunction₂→SetoidFunction Lift ←_

--     _>=>'_ : {A B C : Setoid α β} → SetoidFunction₂ (A ⇒ M B) (B ⇒ M C) (A ⇒ M C)
--     _>=>'_ = {! SetoidFunction₂→SetoidFunction Lift   !}

--     -- _>=>'_ : {A B C : Set α} → (f : A ⇛ B) (g : B ⇛ C) → A ⇛ C
--     -- _>=>'_ f g x = f x >>= g

--     field
--         bind-identityˡ : {A B : Setoid α β} (x : A .Carrier) (f : A ⇒' M B) → (unit x >>= f) ≈[ codomain f ] f ← x
--         bind-identityʳ : {A B : Setoid α β} (x : m A) → (x >>= Unit) ≈[ M A ] x
--         bind-assoc :  {A B C : Setoid α β} → (x : m A) → (f : A ⇒' M B) → (g : B ⇒' M C) → (x >>= (lift g ∘' f)) ≈[ codomain g ] (x >>= f >>= g)

--     variable
--         A B : Setoid α β
--         x : A .Carrier
--         f : A ⇒' B


--     Return = Unit
--     _>>='_ = Bind

--     return = unit

--     Map : (A ⇒ B) ⇒' (M A ⇒ M B)
--     Map = SetoidFunction₂→SetoidFunction Lift ∘' (SetoidFunction₂→SetoidFunction ∘'-func ← Unit)

--     map : (A ⇒' B) → m A → m B
--     map = _←_ ∘ Map ←_
