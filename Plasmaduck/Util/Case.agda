open import Level using (Level; _⊔_) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; inspect; [_]) renaming (refl to ≡-refl)
open import Data.Product using (Σ; _,_; proj₁; proj₂)


module Plasmaduck.Util.Case where
variable
    α β : Level
    A : Set α
    B : Set β

-- For structural decomposition lambdas
case_of_ : A → (A → B) → B
case x of f = f x

-- Similarly, for casing on arguments that are ambient in a context and thus cannot be cased on in the usual way
-- Alternatively, for casing on and inspecting something without it abstracting over the rest of the type.
inspect-case_of_ : (x : A) → (Σ A (x ≡_) → B) → B
inspect-case x of f = f (x , ≡-refl)
