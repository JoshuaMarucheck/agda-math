open import Relation.Binary.PropositionalEquality using (_≡_; _≢_) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans; cong to ≡-cong)
open import Data.Unit using (⊤; tt)
open import Data.Bool using (Bool; T; true; false; not)
import Relation.Nullary as Nullary



module Plasmaduck.Data.Bool where

not-opposite : (x : Bool) → x ≢ not x
not-opposite true ()
not-opposite false ()

deconstruct-T : (b : Bool) → .(T b) → b ≡ true
deconstruct-T true _ = ≡-refl

T-recompute : {b : Bool} → Nullary.Recomputable (T b)
T-recompute {true} _ = tt
