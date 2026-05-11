open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary using (Setoid; Rel; IsEquivalence; Reflexive; Symmetric; Transitive)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Function using (Congruent; _∘_; _on_; id; Bijection)

open import Plasmaduck.Function using (_⇔_; ⇔-isEquivalence)
open import Plasmaduck.Relation.Equivalence using (≡-isEquivalence)
open import Plasmaduck.SetoidExperiment.SetoidMachinery using (property-subset-setoid; _which-is-cong_; SetoidFunction)
open import Plasmaduck.Function.InjectionSurjection using (both-inv→bijective; LeftInverse; RightInverse)



module Plasmaduck.SetoidExperiment.On {a b ℓ : Level} {A : Set a} (B-setoid : Setoid b ℓ) (f : A → B-setoid .Setoid.Carrier) where

open Setoid using (Carrier; _≈_; isEquivalence; refl; sym; trans)

private
    B : Set b
    B = B-setoid .Carrier

    _~B_ : Rel B ℓ
    _~B_ = B-setoid ._≈_


_~_ : Rel A ℓ
_~_ = (B-setoid ._≈_) on f

~-eq : IsEquivalence _~_
~-eq = record {
    refl = B-setoid .refl;
    sym = B-setoid .sym;
    trans = B-setoid .trans
    }

setoid-on : Setoid a ℓ
setoid-on = record {
    Carrier = A;
    _≈_ = _~_;
    isEquivalence = ~-eq
    }

is-in-image : B-setoid .Carrier → Set (a ⊔ ℓ)
is-in-image y = Σ A λ x → f x ~B y

on-bijection : Bijection setoid-on (property-subset-setoid B-setoid is-in-image)
on-bijection = record {
    to = to;
    cong = id;
    bijective = (λ {x} {y} z → z) ,
        (λ (fx , x , f[x]~fx) → x , (λ z~f[x] → (B-setoid .trans) z~f[x] f[x]~fx))
    }
    where
        C-setoid = property-subset-setoid B-setoid (λ y → Σ A λ x → f x ~B y)
        C = C-setoid .Carrier

        to : A → C
        to x = f x , x , B-setoid .refl
