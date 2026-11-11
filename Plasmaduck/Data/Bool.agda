open import Level using (Level)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans; cong to ≡-cong)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥-elim)
open import Data.Bool using (Bool; T; true; false; not; if_then_else_)
import Relation.Nullary as Nullary
open import Relation.Nullary using (¬_)



module Plasmaduck.Data.Bool where

variable
    a : Level
    A : Set a

not-opposite : (x : Bool) → x ≢ not x
not-opposite true ()
not-opposite false ()

deconstruct-T : {b : Bool} → .(T b) → b ≡ true
deconstruct-T {true} _ = ≡-refl

form-T-true : {b : Bool} → .(b ≡ true) → T b
form-T-true {true} _ = tt

form-T-false : {b : Bool} → .(b ≡ false) → ¬ T b
form-T-false {false} _ ()
form-T-false {true} ()

T-recompute : {b : Bool} → Nullary.Recomputable (T b)
T-recompute {true} _ = tt

if-force-true : (b : Bool) (x y : A) → T b → (if b then x else y) ≡ x
if-force-true true x y _ = ≡-refl

if-force-false : (b : Bool) (x y : A) → ¬ (T b) → (if b then x else y) ≡ y
if-force-false false x y thing = ≡-refl
if-force-false true x y ¬true = ⊥-elim (¬true tt)
