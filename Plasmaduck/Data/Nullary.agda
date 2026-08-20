open import Level using (Level)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; cong; cong-app; refl; sym; trans; inspect; [_]; ≢-sym)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Empty using (⊥-elim)
open import Data.Bool using (true; false)


module Plasmaduck.Data.Nullary where

variable
    α : Level
    A : Set α


dec-agree : (x y : Dec A) → Dec.does x ≡ Dec.does y
dec-agree (no _) (no _) = refl
dec-agree (no ¬a) (yes a) = ⊥-elim (¬a a)
dec-agree (yes a) (no ¬a) = ⊥-elim (¬a a)
dec-agree (yes _) (yes _) = refl
