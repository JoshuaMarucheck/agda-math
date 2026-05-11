open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; inspect; cong; Reveal_·_is_; [_]; refl; sym; trans)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open import Data.Maybe using (Maybe; just; nothing)



module Plasmaduck.Data.Maybe where

variable
    a : Level
    A : Set a

_orelse_ : Maybe A → Maybe A → Maybe A
(just x) orelse _ = just x
nothing orelse x = x

orelse-nothing-is-fst : {x : Maybe A} → x orelse nothing ≡ x
orelse-nothing-is-fst {x = just x} = refl
orelse-nothing-is-fst {x = nothing} = refl

infixl 6 _orelse_

orelse-assoc : {x y z : Maybe A} → x orelse (y orelse z) ≡ (x orelse y) orelse z
orelse-assoc {x = just x} = refl
orelse-assoc {x = nothing} = refl
