open import Level using (Level; _⊔_) renaming (suc to lsuc; zero to lzero)


module Plasmaduck.Util.Case where
variable
    α β : Level
    A : Set α
    B : Set β

-- For structural decomposition lambdas
case_of_ : A → (A → B) → B
case x of f = f x