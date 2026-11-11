open import Level using (Level; _⊔_; lift) renaming (zero to lzero; suc to lsuc)
open import Relation.Nullary using (¬_; Dec; yes; no; contraposition)
open import Function using (_∘_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (∃; Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; map₁; map₂)
open import Plasmaduck.Monad.Defs using (Monad; ¬¬-monad)
open import Plasmaduck.Function using (_⇔_)

module Plasmaduck.Monad.DoubleNegation where



private
    -- demorgan's laws --
    module _ where
        private
            variable
                α β : Level
                A : Set α
                B : Set β

        -- thing₁ : ¬ (A × B) → ¬ A ⊎ ¬ B
        -- thing₁ = {!   !}

        thing₂ : ¬ (A ⊎ B) → ¬ A × ¬ B
        thing₂ = λ z → (λ z₁ → z (inj₁ z₁)) , (λ z₁ → z (inj₂ z₁))

        thing₃ : ¬ A ⊎ ¬ B → ¬ (A × B)
        thing₃ (inj₁ ¬A) (a , b) = ¬A a
        thing₃ (inj₂ ¬B) (a , b) = ¬B b

        thing₄ : ¬ A × ¬ B → ¬ (A ⊎ B)
        thing₄ (¬A , ¬B) (inj₁ a) = ¬A a
        thing₄ (¬A , ¬B) (inj₂ b) = ¬B b

        ¬-distrib-⊎-× : (¬ (A ⊎ B)) ⇔ (¬ A × ¬ B)
        ¬-distrib-⊎-× = thing₂ , thing₄

        meep : A × ¬ B → ¬ (A → B)
        meep (a , ¬B) f = ¬B (f a)

        morp : ¬ A ⊎ B → (A → B)
        morp (inj₁ ¬A) a = ⊥-elim (¬A a)
        morp (inj₂ b) a = b

    module _ where
        private
            variable
                α β : Level
                A : Set α
                B : A → Set β

        -- ¬∀⇒∃¬ : ¬ (∀ x → B x) → (∃ λ x → ¬ B x)
        -- ¬∀⇒∃¬ = {!   !}

        ∃¬⇒¬∀ : (∃ λ x → ¬ B x) → ¬ (∀ x → B x)
        ∃¬⇒¬∀ = λ z z₁ → z .proj₂ (z₁ (z .proj₁))

        ¬∃⇒∀¬ : ¬ ∃ B → (∀ x → ¬ B x)
        ¬∃⇒∀¬ = λ z x z₁ → z (x , z₁)

        ∀¬⇒¬∃ : (∀ x → ¬ B x) → ¬ ∃ B
        ∀¬⇒¬∃ = λ z z₁ → z (z₁ .proj₁) (z₁ .proj₂)

decide : {α : Level} {A : Set α} → ¬ ¬ (Dec A)
decide ¬dec = ¬dec (no λ a → ¬dec (yes a))


module DoubleNegationThings {α : Level} (¬¬-cancel : {A : Set α} → ¬ ¬ A → A) where
    private
        variable
            A : Set α
            B : Set α
            B' : A → Set α

    contraposition-¬ : (¬ B → ¬ A) → (A → B)
    contraposition-¬ = λ z z₁ → ¬¬-cancel (λ z₂ → z z₂ z₁)

    ¬-distrib-→-×¬ : ¬ (A → B) → A × ¬ B
    ¬-distrib-→-×¬ {A = A} ¬[A→B] = a , λ b → ¬[A→B] λ _ → b
        where
            a : A
            a = ¬¬-cancel λ ¬A → ¬[A→B] λ a' → ⊥-elim (¬A a')

    thing₁ : ¬ (A × B) → ¬ A ⊎ ¬ B
    thing₁ = contraposition-¬ λ thing ¬[A×B] → ¬[A×B] (¬¬-cancel (thing₂ thing .proj₁) , ¬¬-cancel (thing₂ thing .proj₂))

    ¬-distrib-×-⊎ : ¬ (A × B) ⇔ ¬ A ⊎ ¬ B
    ¬-distrib-×-⊎ = thing₁ , thing₃

    →-split : (A → B) → ¬ A ⊎ B
    →-split {A = A} {B = B} f = map₂ ¬¬-cancel (thing₁ (thing f))
        where
            thing : (A → B) → ¬ (A × ¬ B)
            thing = contraposition-¬ (meep ∘ ¬¬-cancel)

    ¬∀⇒∃¬ : ¬ (∀ x → B' x) → (∃ λ x → ¬ B' x)
    ¬∀⇒∃¬ ¬∀ = ¬¬-cancel λ z → ¬∀ (λ x → ¬¬-cancel (λ z₁ → z (x , z₁)))

    decide' : Dec A
    decide' = ¬¬-cancel decide


module _ (α : Level) where
    open Monad (¬¬-monad (lsuc α)) using (
        M; _⇛_; _>>=_; unit; bind; return; map; _>=>_;
        unit-left-id-for-bind; unit-right-id-for-bind; >=>-assoc)

    M-¬¬-single-cancel : {A : Set (lsuc α)} → M (¬ ¬ A → A)
    M-¬¬-single-cancel {A} = decide >>= thing'
        where
            thing : Dec A → ¬ ¬ A → A
            thing (no ¬A) ¬¬A = ⊥-elim (¬¬A ¬A)
            thing (yes a) ¬¬A = a

            thing' : Dec A → M (¬ ¬ A → A)
            thing' = unit ∘ thing

    M-¬¬-cancel : M ({A : Set α} → ¬ ¬ A → A)
    M-¬¬-cancel ¬[¬¬A→A] = ¬[¬¬A→A] λ {A = A} ¬¬A → ⊥-elim (¬[¬¬A→A] λ {B} → {! (decide {A = A})   !})

    -- open DoubleNegationThings ?





module _ where
    module _ {α : Level} where
        open Monad (¬¬-monad α) public

    pf' : {α : Level} → ((A : Set (lsuc α)) → ¬ (¬ (Dec A))) → ¬ (¬ ((A : Set α) → Dec A))
    pf' {α} ¬¬dec-lsuc-α ¬dec-α = ¬dec-α λ A → no λ a → {!   !}
        where
            beep : ¬ (¬ Dec ((B : Set α) → Dec B))
            beep = ¬¬dec-lsuc-α ((B : Set α) → Dec B)

            blep : {!   !}
            blep = beep >>= λ { (yes dec) → ⊥-elim (¬dec-α dec); (no ¬dec) → {!   !} }
