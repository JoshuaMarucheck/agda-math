open import Relation.Binary.PropositionalEquality using (_≡_; _≢_) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans; cong to ≡-cong)
open import Data.Bool using (Bool; true; false; not)



module Plasmaduck.Data.Bool where

not-opposite : (x : Bool) → x ≢ not x
not-opposite true ()
not-opposite false ()
