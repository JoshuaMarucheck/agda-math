open import Level using (Level; _⊔_) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Function using (id; _∘_; flip)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary using (Rel; IsEquivalence; Reflexive; Symmetric; Transitive; Sym; Trans)
open import Relation.Nullary using (¬_; contraposition)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)


module Plasmaduck.Function where

variable
    α β γ ℓ : Level
    A : Set α
    B : Set β
    C : Set γ

module _ {α β : Level} {A : Set α} {B : A → Set β} where
    _≈_ : (f g : (x : A) → B x) → Set (α ⊔ β)
    _≈_ f g = ∀ x → f x ≡ g x
    infix 1 _≈_

    ≈-refl : Reflexive _≈_
    ≈-refl = λ _ → refl

    ≈-sym : Symmetric _≈_
    ≈-sym = λ f≈g x → sym (f≈g x)

    ≈-trans : Transitive _≈_
    ≈-trans = λ f≈g g≈h x → trans (f≈g x) (g≈h x)

    ≈-isEquivalence : IsEquivalence _≈_
    ≈-isEquivalence = record {
        refl = ≈-refl;
        sym = ≈-sym;
        trans = ≈-trans
        }

    -- A property that only depends on IO behavior of the function
    FunctionalProperty : (P : ((x : A) → B x) → Set γ) → Set (α ⊔ β ⊔ γ)
    FunctionalProperty P = ∀ {f g : (x : A) → B x} → f ≈ g → P f → P g



{-
    Suppose you're defining a type. Supposing f and g have all the same outputs, you want to show that the two following types are equal:
        ∀ x → P (f x)
        ∀ x → P (g x)
    You can't just invoke cong, since that requires x to be instantiated.

    P depends only on its input of type B.

    f g : A → B
    P : B → C

    tbh, this should be the same as saying that P ∘ f and P ∘ g are the same function, no?
    That is, P ∘ f ≈ P ∘ g
-}
-- dependent-equality : (f g : A → B) → f ≈ g → (P : B → Set γ) → (∀ (x : A) → P (f x)) ≡ (∀ (x : A) → P (g x))
-- dependent-equality f g f≈g P = {!   !}

-- I want to talk about the function arrow
_⇒_ : {α β : Level} (A : Set α) (B : Set β) → Set (α ⊔ β)
A ⇒ B = A → B

infixr 100 _⇒_


⇒-refl : Reflexive (_⇒_ {α})
⇒-refl = Function.id

⇒-trans : A ⇒ B → B ⇒ C → A ⇒ C
⇒-trans f g = g ∘ f


_⇔_ : {α β : Level} (A : Set α) (B : Set β) → Set (α ⊔ β)
A ⇔ B = (A → B) × (B → A)
infix 0 _⇔_

⇔-refl : Reflexive (_⇔_ {α = ℓ})
⇔-refl = (λ z → z) , (λ z → z)

⇔-sym : Sym (_⇔_ {α} {β}) _⇔_
⇔-sym = λ z → z .proj₂ , z .proj₁

⇔-trans : Trans (_⇔_ {α} {β}) (_⇔_ {β} {γ}) _⇔_
⇔-trans = λ z z₁ → (λ z₂ → z₁ .proj₁ (z .proj₁ z₂)) , (λ z₂ → z .proj₂ (z₁ .proj₂ z₂))

⇔-isEquivalence : {ℓ : Level} → IsEquivalence (_⇔_ {α = ℓ} {β = ℓ})
⇔-isEquivalence = record {
    refl = ⇔-refl;
    sym = ⇔-sym;
    trans = ⇔-trans
    }
