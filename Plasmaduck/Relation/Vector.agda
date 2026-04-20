open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; inspect; cong; Reveal_·_is_; [_]) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Relation.Binary using (Setoid; Rel; IsEquivalence; Reflexive; Symmetric; Transitive)
open import Relation.Nullary.Negation using (¬_)
open import Data.Vec using (Vec; []; _∷_; lookup; head; tail)
open import Data.Vec.Properties using ()
open import Data.Nat using (ℕ; _+_; _≤_; _≥_) renaming (zero to zero-ℕ; suc to suc-ℕ)
open import Data.Fin using (Fin) renaming (zero to zero-fin; suc to suc-fin)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)

open import Plasmaduck.Util.TypeChange using (change-type)



module Plasmaduck.Relation.Vector {a ℓ : Level} (A-setoid : Setoid a ℓ) where

open Setoid using (Carrier)
private
    A = A-setoid .Carrier
    _~A_ = A-setoid .Setoid._≈_

    open IsEquivalence (A-setoid .Setoid.isEquivalence) using (refl; sym; trans)

variable
    b c ℓ₁ : Level


data _~_ : {n : ℕ} → Rel (Vec A n) (a ⊔ ℓ) where
    empty-related : [] ~ []
    cons-related : {n : ℕ} → {xs : Vec A (suc-ℕ n)} {ys : Vec A (suc-ℕ n)} → head xs ~A head ys → tail xs ~ tail ys → xs ~ ys

lookup-proof : {n : ℕ} → {xs ys : Vec A n} → xs ~ ys → (i : Fin n) → lookup xs i ~A lookup ys i
lookup-proof {n = zero-ℕ} _ ()
lookup-proof {n = suc-ℕ n'} (cons-related {xs = x ∷ xs} {ys = y ∷ ys} x~y xs~ys) zero-fin = x~y
lookup-proof {n = suc-ℕ n'} (cons-related {xs = x ∷ xs} {ys = y ∷ ys} x~y xs~ys) (suc-fin i) = lookup-proof xs~ys i

~-refl : {n : ℕ} → Reflexive (_~_ {n = n})
~-refl {n} {x = []} = empty-related
~-refl {n} {x = x ∷ xs} = cons-related refl ~-refl

~-sym : {n : ℕ} → Symmetric (_~_ {n = n})
~-sym {x = []} {y = []} empty-related = empty-related
~-sym {x = x ∷ xs} {y = y ∷ ys} (cons-related x~y xs~ys) = cons-related (sym x~y) (~-sym xs~ys)

~-trans : {n : ℕ} → Transitive (_~_ {n = n})
~-trans empty-related empty-related = empty-related
~-trans (cons-related x~y xs~ys) (cons-related y~z ys~zs) = cons-related (trans x~y y~z) (~-trans xs~ys ys~zs)

~-eq : {n : ℕ} → IsEquivalence (_~_ {n = n})
~-eq = record {
    refl = ~-refl;
    sym = ~-sym;
    trans = ~-trans
    }

VectorSetoid : (n : ℕ) → Setoid a (a ⊔ ℓ)
VectorSetoid n = record {
    Carrier = Vec A n;
    _≈_ = _~_;
    isEquivalence = ~-eq
    }



_~'_ : Rel (Σ ℕ λ n → Vec A n) (a ⊔ ℓ)
_~'_ (i , xs) (j , ys) = Σ (i ≡ j) λ i=j → xs ~ change-type (cong (Vec A) (≡-sym i=j)) ys

~'-refl : Reflexive _~'_
~'-refl {x = i , xs} = ≡-refl , ~-refl

~'-sym : Symmetric _~'_
~'-sym (≡-refl , xs~ys) = ≡-refl , ~-sym xs~ys

~'-trans : Transitive _~'_
~'-trans (≡-refl , xs~ys) (≡-refl , ys~zs) = ≡-refl , ~-trans xs~ys ys~zs

~'-eq : IsEquivalence _~'_
~'-eq = record {refl = ~'-refl; sym = ~'-sym; trans = ~'-trans}

VectorSetoid' : Setoid a (a ⊔ ℓ)
VectorSetoid' = record {
    Carrier = Σ ℕ λ n → Vec A n;
    _≈_ = _~'_;
    isEquivalence = ~'-eq
    }
