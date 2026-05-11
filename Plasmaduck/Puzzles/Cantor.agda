open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans; cong to ≡-cong)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Binary using (Setoid)
open import Function using (Bijection)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (Bool; true; false; not)

open import Plasmaduck.SetoidExperiment.SetoidMachinery using (SetoidFunctionSetoid; SetoidFunction; _←_; discrete-setoid)
open import Plasmaduck.Function.Bijection using (invert-bijection; invert-is-right-inverse)
open import Plasmaduck.Data.Bool using (not-opposite)



module Plasmaduck.Puzzles.Cantor where

open Setoid using (Carrier)
variable
    a b c : Level

ℙ : Setoid a b → Setoid (a ⊔ b) (a ⊔ b)
ℙ setoid = SetoidFunctionSetoid setoid (discrete-setoid Bool)

ℙ' : Setoid a b → Set a
ℙ' setoid = setoid .Carrier → Bool

cantor : {A : Setoid a b} → ¬ (Bijection A (ℙ A))
cantor {a = a} {A = A-setoid} bijection = not-opposite (f x) discrepency-on-fx
    where
        A : Set a
        A = A-setoid .Carrier

        bij : A → ℙ A-setoid .Carrier
        bij x = bijection .Bijection.to x

        inv-bij : ℙ A-setoid .Carrier → A
        inv-bij = invert-bijection bijection .Bijection.to

        f : ℙ' A-setoid
        f x = not ((bij x) ← x)

        f-func : ℙ A-setoid .Carrier
        f-func = record {
            func = f;
            respects = λ {x} {y} x~y →
                not ((bij x) ← x) ≡⟨ ≡-cong not (bijection .Bijection.to x .SetoidFunction.respects x~y) ⟩
                not ((bij x) ← y) ≡⟨ ≡-cong not ((bijection .Bijection.cong x~y) (A-setoid .Setoid.refl)) ⟩
                not ((bij y) ← y) ∎
            }
            where open ≡-Reasoning

        x : A
        x = inv-bij f-func

        discrepency-on-fx : f x ≡ not (f x)
        discrepency-on-fx =
            f x                                 ≡⟨⟩
            not ((bij x) ← x)                   ≡⟨⟩
            not ((bij (inv-bij f-func)) ← x)    ≡⟨ ≡-cong not (invert-is-right-inverse bijection (A-setoid .Setoid.refl)) ⟩
            not (f-func ← x)                    ≡⟨⟩
            not (f x)                           ∎
            where open ≡-Reasoning
