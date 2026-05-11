open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; inspect; cong; Reveal_·_is_; [_]; refl; sym; trans)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Function using (_∘_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Vec using (Vec)
open import Data.List using (List)
open import Relation.Binary using (TotalOrder; DecTotalOrder; IsTotalOrder; IsStrictTotalOrder; Rel; IsEquivalence; _Respects₂_; _Respectsˡ_; _Respectsʳ_)



module Plasmaduck.Relation.Equivalence where

open import Plasmaduck.Util.TypeChange using (cong₂-dependent) public

variable
    ℓ α β : Level
    A : Set ℓ


record Equivalence (A : Set α) (ℓ : Level) : Set (α ⊔ lsuc ℓ) where
    field
        _~_ : Rel A ℓ
        isEquivalence : IsEquivalence _~_


≡-isEquivalence : IsEquivalence (_≡_ {A = A})
≡-isEquivalence = record {
    refl = λ {x} → refl;
    sym = λ {x} {y} x≡y → sym x≡y;
    trans = λ {x} {y} {z} x≡y y≡z → trans x≡y y≡z
    }

all-respectsˡ-≡ : (_#_ : Rel A α) → _#_ Respectsˡ _≡_
all-respectsˡ-≡ _#_ {x} {y} {z} y≡z y#x with y≡z
all-respectsˡ-≡ _#_ {x} {y} {z} y≡z y#x | refl = y#x

all-respectsʳ-≡ : (_#_ : Rel A α) → _#_ Respectsʳ _≡_
all-respectsʳ-≡ _#_ {x} {y} {z} y≡z x#y with y≡z
all-respectsʳ-≡ _#_ {x} {y} {z} y≡z x#y | refl = x#y

all-respects-≡ : (_#_ : Rel A α) → _#_ Respects₂ _≡_
all-respects-≡ _#_ = record {
    fst = all-respectsʳ-≡ _#_;
    snd = all-respectsˡ-≡ _#_
    }
