open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; inspect; cong; Reveal_·_is_; [_]) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)

open import Plasmaduck.Util.TypeChange using (change-type)


module Plasmaduck.Data.Product where

variable
    a b c : Level
    A : Set a
    B : Set b
    B' : A → Set b

Σ≡ : {x@(x₁ , x₂) y@(y₁ , y₂) : Σ A B'} → (pf : x₁ ≡ y₁) → x₂ ≡ change-type (cong B' (≡-sym pf)) y₂ → x ≡ y
Σ≡ ≡-refl ≡-refl = ≡-refl

×≡ : {x@(x₁ , x₂) y@(y₁ , y₂) : A × B} → (pf₁ : x₁ ≡ y₁) (pf₂ : x₂ ≡ y₂) → x ≡ y
×≡ ≡-refl ≡-refl = ≡-refl
