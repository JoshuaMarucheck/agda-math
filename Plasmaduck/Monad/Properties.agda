open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc)
open import Function using (_∘_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (∃; Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Plasmaduck.Monad.Defs using (Monad)



module Plasmaduck.Monad.Properties {α β : Level} (monad : Monad α β) where

open Monad monad
private
    variable
        A B : Set α
        C : A → Set α

--------------
--- Arrows ---
--------------

{-
    In order from strong to weak we have:
    M A → B
    A → B
    M (A → B)
    M A → M B   =   A → M B
    (Note we can't apply M more than once to any given type since we could be in a rising monad)
-}

[MA⇒B]→[A⇒B] : (M A → B) → (A → B)
[MA⇒B]→[A⇒B] f = f ∘ unit

thing : (A → B) → M (A → B)
thing = unit

thing₁ : M (A → B) → (M A → M B)
thing₁ mf ma = mf >>= λ f → ma >>= (unit ∘ f)

thing₂ : (M A → M B) → (A → M B)
thing₂ f = f ∘ unit

thing₂∙₅ : (A → M B) → (M A → M B)
thing₂∙₅ f ma = ma >>= f

-- maybe we try to find a counterexample. Is there a monad where this doesn't hold?
maybe-thing : (A → M B) → M (A → B)
maybe-thing f = {!   !}

thing' : (A → ¬ ¬ B) → ¬ ¬ (A → B)
thing' f ¬[A→B] = ¬[A→B] {! f  !}

-- this implies the specific example of:
thing'' : ((A : Set α) → ¬ ¬ (Dec A)) → ¬ ¬ ((A : Set α) → Dec A)
thing'' f = {!   !}

-- but the arg is satisfiable:
thing''' : (A : Set α) → ¬ ¬ (Dec A)
thing''' A f = f (no λ a → f (yes a))

-- meaning we're actually proving
pf : ¬ ¬ ((A : Set α) → Dec A)
pf ¬dec = ¬dec λ A → no λ a → ¬dec λ B → {!   !}


---------------------------------------------------------------
--- On the possibility of treating monads as proof contexts ---
---------------------------------------------------------------

×-intro : M A → M B → M (A × B)
×-intro ma mb = ma >>= (λ a → mb >>= (λ b → unit (a , b)))

×-elim₁ : M (A × B) → M A
×-elim₁ m[a×b] = m[a×b] >>= (unit ∘ proj₁)

×-elim₂ : M (A × B) → M B
×-elim₂ m[a×b] = m[a×b] >>= (unit ∘ proj₂)

⊎-intro₁ : M A → M (A ⊎ B)
⊎-intro₁ ma = ma >>= (unit ∘ inj₁)
-- ⊎-intro₂ : ?

{-
    ⊎-elim : M (A ⊎ B) → M A ⊎ M B
    this one is not possible.
    Proof: AFSOC ⊎-elim exists.
    Consider the double negation monad, and let B = ¬ A.
    Then A ⊎ B is an assertion of decidability of A, which holds in the double negation monad.
    We would thus have decidablility of ¬ ¬ A (equivalently decidability of ¬ A).
    This does not hold.
-}


-- →-intro : (M A → M B) → M (A → B)
-- →-intro f = {!   !}

→-elim : M (A → B) → M A → M B
→-elim mf ma = mf >>= λ f → ma >>= λ a → unit (f a)

-- Let's try to find other types for these.
-- _∨_ : {γ ε : Level} → Set γ → Set ε → Set (γ ⊔ ε)
-- A ∨ B = ¬ (¬ (A ⊎ B))

-- ∨-intro₁ : M A → M (A ∨ B)
-- ∨-intro₁ = λ z → z >>= (λ z₁ → unit (λ z₂ → z₂ (inj₁ z₁)))

-- ∨-intro₂ : M B → M (A ∨ B)
-- ∨-intro₂ = {!   !}

-- em : M (A ∨ (¬ A))
-- em = unit (λ z → z (inj₂ (λ z₁ → z (inj₁ z₁))))

-- ∨-elim : M (A ∨ B) → M A ∨ M B
-- ∨-elim m[a∨b] ¬[ma⊎mb] = ¬[ma⊎mb] {!   !}

-- _⇒_ : {γ ε : Level} → Set γ → Set ε → Set (γ ⊔ ε)
-- A ⇒ B = ¬ A ∨ B

-- ⇒-intro : (M A ⇒ M B) → M (A ⇒ B)
-- ⇒-intro f = {!   !}

-- ⇒-elim : M (A ⇒ B) → M A ⇒ M B
-- ⇒-elim mf = {!   !}

-- The key here is, the monad lets you intake a finite number of specific things from the outside. If A is an infinite set, this doesn't work
-- ∀-intro : (∀ x → M (C x)) → M (∀ x → C x)
-- ∀-intro f = {!   !}

-- ∀-elim : M (∀ x → C x) → (∀ x → M (C x))
-- ∀-elim mf x = mf >>= λ f → unit (f x)

-- ∃-intro : (∃ λ x → M (C x)) → M (∃ λ x → C x)
-- ∃-intro = λ z → z .proj₂ >>= (λ z₁ → unit (z .proj₁ , z₁))

-- ∃-elim : M (∃ λ x → C x) → (∃ λ x → M (C x))
-- ∃-elim mf = {!    !}
