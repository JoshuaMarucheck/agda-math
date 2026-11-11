open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc)
open import Function using (_∘_)
open import Data.Product using (∃; Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Plasmaduck.Monad.Defs using (Monad) renaming (join to join')



module Plasmaduck.Monad.FlatProperties {α : Level} (monad : Monad α α) where

open import Plasmaduck.Monad.Properties monad public

open Monad monad
private
    variable
        S T : Set α
        U : S → Set α

-- note the existence of join
join : M (M S) → M S
join = λ z → z >>= (λ z₁ → z₁)
-- since join and unit are opposites, M M S and M S are proof-identical.

--------------
--- Arrows ---
--------------

{-
    more arrows are possible in a flat monad.

    standard arrows:
    M S → T
    S → T
    M (S → T)
    M S → M T
    S → M T

    new arrows:
    M (M S → T)
    M (M S → M T)
    M (S → M T)

    none of the new arrows can prove S → T. Proof: consider the trivially true monad, and let S = ⊤ and T = ⊥. Then the new arrows are trivially provable, but we cannot prove S → T.

    order from strong to weak:
    M S → T
    S → T       <>  M (M S → T)
    M (S → T)
    M S → M T   =   S → M T  =  M (M S → M T)  =  M (S → M T)
-}

blob₁ : (M S → T) → M (M S → T)
blob₁ = unit

-- -- This one won't work
-- blob₂5 : M (M S → T) → (S → T)
-- blob₂5 f = {!   !}

-- I doubt this one will work
-- blob₂ : (S → T) → M (M S → T)
-- blob₂ f = {!  f !}
--     where
--         mb : M T
--         mb = {!   !}

blob₃ : M (M S → T) → M (S → T)
blob₃ = map [MA⇒B]→[A⇒B]

-- this one only works if blob₂ works; they can both be reduced to the other
-- blob₃5 : M (S → T) → M (M S → T)
-- blob₃5 mf = mf >>= λ f → {!   !}

blob₄ : (M S → M T) → M (M S → M T)
blob₄ = unit

blob₅ : M (M S → M T) → (M S → M T)
blob₅ mf ma = mf >>= λ f → f ma

blob₆ : (S → M T) → M (S → M T)
blob₆ = unit

blob₆5 : M (S → M T) → (S → M T)
blob₆5 mf a = mf >>= λ f → f a


-------------------------------------------------------------------
--- On the possibility of using a flat monad as a proof context ---
-------------------------------------------------------------------

{-
    The goal for each of these connectors is to replace a standard connector
    in such a way that, if the monad is the identity monad,
    then the new connector and the standard connector are the same.

    I also want each of these connectors to behave in a relatively logical way regardless of the monad used,
    meaning I want to be able to do proofs of a constructive or type theory-ish nature using them.
    M A is a proof of A in the context of the monad (think of it as a proof of judgement A,
    and think of M as a constructor turning types into judgements).
    So for example, in a classical monad, there ought to be a proof of A ∨ ¬ A, which is represented as a proof
    of M (A ∨ ¬ A). Obviously this shouldn't hold in general, but for a specific monad maybe.

    an intro form should turn something reasonable into a judgement
    an elim form should turn a judgement into something usable
    (but note that sometimes the thing will not be usable, due to the monad
    proving everything; it will still need to be mixed up with the monad).

    The constructors below are judgement formers that interact with types the way we expect them to.
-}

infixr 2 _∧_
infixr 1 _∨_
infixr 100 _⇒_

_∧_ : Set α → Set α → Set α
S ∧ T = M S × M T

∧-consistency : M (S ∧ T) → S ∧ T
∧-consistency m[s∧t] = m[s∧t] >>= proj₁ , m[s∧t] >>= proj₂

∧-intro' : S × T → S ∧ T
∧-intro' = λ z → unit (z .proj₁) , unit (z .proj₂)

∧-intro : M S → M T → S ∧ T
∧-intro = _,_

∧-elim₁ : S ∧ T → M S
∧-elim₁ = proj₁

∧-elim₂ : S ∧ T → M T
∧-elim₂ = proj₂


_∨_ : Set α → Set α → Set α
S ∨ T = M (S ⊎ T)

∨-consistency : M (S ∨ T) → (S ∨ T)
∨-consistency = λ z → z >>= (λ z₁ → z₁)

∨-intro' : (S ⊎ T) → (S ∨ T)
∨-intro' = unit

∨-intro₁ : M S → (S ∨ T)
∨-intro₁ ma = ma >>= (λ a → (unit (inj₁ a)))

∨-intro₂ : M T → (S ∨ T)
∨-intro₂ mb = mb >>= (λ b → (unit (inj₂ b)))

-- ∨-elim : M (S ∨ T) → M S ∨ M T
-- ∨-elim {S = S} {T} m[a∨b] = m[a⊎b] >>= λ { (inj₁ a) → unit (inj₁ (unit a)) ; (inj₂ b) → unit (inj₂ (unit b)) }
--     where
--         m[a⊎b] : M (S ⊎ T)
--         m[a⊎b] = join m[a∨b]


-- _⇒'_ : (S : Set α) → (T : S → Set α) → Set α
-- S ⇒' T = (x : S) → M (T x)

-- ⇒'-consistency : M (S ⇒' U) → (S ⇒' U)
-- ⇒'-consistency = {!   !}

-- ⇒'-intro' : ((x : S) → U x) → (S ⇒' U)
-- ⇒'-intro' = {!   !}

-- ⇒'-intro : {S : Set α} {U : S → Set α} (x : M S) → (S ⇒' U) → x >>= (unit ∘ U)
-- ⇒'-intro = ?

_⇒_ : Set α → Set α → Set α
S ⇒ T = S → M T

⇒-consistency : M (S ⇒ T) → (S ⇒ T)
⇒-consistency = blob₆5

⇒-intro' : (S → T) → (S ⇒ T)
⇒-intro' f = unit ∘ f

⇒-intro : (M S → M T) → (S ⇒ T)
⇒-intro = λ z → (λ z₁ → z (unit z₁))

⇒-elim : (S ⇒ T) → (M S → M T)
⇒-elim mf ms = ms >>= mf

∨-elim : {S T U : Set α} → (S ∨ T) → (S ⇒ U) → (T ⇒ U) → M U
∨-elim m[s⊎t] f g = m[s⊎t] >>= λ { (inj₁ s) → f s; (inj₂ t) → g t }



A : (S → Set α) → Set α
A U = ∀ x → M (U x)

A-consistency : M (A U) → A U
A-consistency mf x = mf >>= λ f → f x

A-intro' : (∀ x → U x) → (A λ x → U x)
A-intro' = λ z x → unit (z x)

-- A-intro : (∀ x → M (U x)) → (A λ x → U x)
-- A-intro = unit

-- A-elim : (A λ x → U x) → (∀ x → M (U x))
-- A-elim = {!   !}

-- A-intro : (A λ x → M (U x)) → M (A λ x → U x)
-- A-intro f = unit (λ x → f x >>= (λ z → z))

-- A-elim : M (A λ x → U x) → (A λ x → M (U x))
-- A-elim mf x = mf >>= λ f → unit (f x)


E : (S → Set α) → Set α
E U = M (∃ U)

E-consistency : M (E U) → E U
E-consistency = λ z → z >>= (λ z₁ → z₁)

E-intro' : (∃ λ x → U x) → (E λ x → U x)
E-intro' = unit

-- E-intro : (E λ x → M (U x)) → M (E λ x → U x)
-- E-intro m[pair] = m[pair] >>= λ (x , mmUx) → unit (mmUx >>= (λ z → unit (x , z)))

-- E-elim : M (E λ x → U x) → (E λ x → M (U x))
-- E-elim mm[pair] = join mm[pair] >>= λ (x , mmUx) → unit (x , unit mmUx)
