open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; inspect; cong; Reveal_·_is_; [_]) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Relation.Nullary.Recomputable using (Recomputable)
open import Relation.Nullary using (¬_)
open import Function using (_∘_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Bool using (Bool; true; false; T)


open import Plasmaduck.Util.TypeChange using (change-type)


module Plasmaduck.Data.Product where

variable
    a b c : Level
    A : Set a
    B : Set b
    B' : A → Set b
    C₁ : (x : A) → B' x → Set c
    C₂ : Σ A B' → Set c

Σ≡ : {x@(x₁ , x₂) y@(y₁ , y₂) : Σ A B'} → (pf : x₁ ≡ y₁) → x₂ ≡ change-type (cong B' (≡-sym pf)) y₂ → x ≡ y
Σ≡ ≡-refl ≡-refl = ≡-refl

×≡ : {x@(x₁ , x₂) y@(y₁ , y₂) : A × B} → (pf₁ : x₁ ≡ y₁) (pf₂ : x₂ ≡ y₂) → x ≡ y
×≡ ≡-refl ≡-refl = ≡-refl

proj₁≡ : {x@(x₁ , x₂) y@(y₁ , y₂) : Σ A B'} → x ≡ y → x₁ ≡ y₁
proj₁≡ ≡-refl = ≡-refl

proj₂≡ : {x@(x₁ , x₂) y@(y₁ , y₂) : Σ A B'} → (pf : x ≡ y) → x₂ ≡ change-type (cong B' (≡-sym (proj₁≡ pf))) y₂
proj₂≡ ≡-refl = ≡-refl

uncurry : (f : (x : A) → (y : B' x) → C₁ x y) → ((x , y) : Σ A B') → C₁ x y
uncurry f (x , y) = f x y

curry : (f : (p : Σ A B') → C₂ p) → (x : A) → (y : B' x) → C₂ (x , y)
curry f x y = f (x , y)

×-recompute : Recomputable A → Recomputable B → Recomputable (A × B)
×-recompute A-recompute B-recompute x = A-recompute (x .proj₁) , B-recompute (x .proj₂)

Σ-recompute : Recomputable A → (.(Σ A B') → ∀ y → B' y) → Recomputable (Σ A B')
Σ-recompute A-recompute B'-recompute pair = A-recompute (pair .proj₁) , B'-recompute pair (A-recompute (pair .proj₁))
{-
    Note it is not enough that all B' x are recomputable.
    If we have some irrelevant pair (x , y), where y : B' x,
    then we have no (irrelevant) evidence of B' (A-recompute x), despite having (irrelevant) evidence of B' x. 

    Since x is irrelevant, the only relevant thing of type A we have is A-recompute x.
    So for example, we could say:

    A = Bool
    B' = T

    Bool-recompute _ = false
    T-recompute true _ = tt
    T-recompute false ()

    then we provide (true , tt) as evidence, and ask it to recompute Σ Bool T using these functions.
    It comes up with (false , ?), with no way to fill in the ?.
    Coming up instead with (true , tt) would be a form of choice, it seems.
-}
indirect-recompute-is-strong : (.(Σ A B') → ∀ y → B' y) → (∀ x → Recomputable (B' x))
indirect-recompute-is-strong indirect-recompute x irr = indirect-recompute (x , irr) x
