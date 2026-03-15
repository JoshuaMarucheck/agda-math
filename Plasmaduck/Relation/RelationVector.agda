open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc; zero to lzero)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; z≤n; s≤s) renaming (zero to zero-ℕ; suc to suc-ℕ)
open import Data.Fin using (Fin; zero; suc; toℕ) renaming (_<_ to _<-fin_)
open import Data.Vec using (Vec; lookup; []; _∷_)
open import Relation.Binary using (Rel; Transitive)



module Plasmaduck.Relation.RelationVector where

variable
    ℓ ℓ₂ : Level


vec-pairwise-rel : {A : Set ℓ} {n : ℕ} → Vec A n → Rel A ℓ₂ → Set ℓ₂
vec-pairwise-rel [] _~_ = Lift _ ⊤
vec-pairwise-rel (_ ∷ []) _~_ = Lift _ ⊤
vec-pairwise-rel (x ∷ xs@(y ∷ vec)) _~_ = x ~ y × vec-pairwise-rel xs _~_

vec-pairwise-rel-lookup :
    {A : Set ℓ} {n : ℕ} → (vec : Vec A n) →
    {_~_ : Rel A ℓ₂} → (Transitive _~_) →
    (vec-pairwise-rel vec _~_) →
    {i j : Fin n} → i <-fin j →
    lookup vec i ~ lookup vec j
vec-pairwise-rel-lookup {n = 0}         [] {_~_} ~-trans _ {()}
vec-pairwise-rel-lookup {n = 1}   (_ ∷ []) {_~_} ~-trans _ {_} {zero} ()
vec-pairwise-rel-lookup (x ∷ xs@(y ∷ vec)) {_~_} ~-trans (x~y , pfs) {zero} {suc zero} i<j = x~y
vec-pairwise-rel-lookup (x ∷ xs@(y ∷ vec)) {_~_} ~-trans (x~y , pfs) {zero} {suc (suc j)} i<j = ~-trans x~y (vec-pairwise-rel-lookup xs ~-trans pfs {zero} {suc j} (s≤s (z≤n {n = toℕ j})))
vec-pairwise-rel-lookup (x ∷ xs@(y ∷ vec)) {_~_} ~-trans (x~y , pfs) {suc i} {suc j} (s≤s pf) = vec-pairwise-rel-lookup xs ~-trans pfs {i} {j} pf
