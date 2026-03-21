open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary using (Reflexive; Symmetric; Transitive; IsDecPreorder; Irreflexive; Trans; Rel; IsEquivalence; _Respects₂_; _Respectsˡ_; _Respectsʳ_; Decidable; IsStrictPartialOrder; Trichotomous; Tri; tri<; tri≈; tri>; Asymmetric; IsDecStrictPartialOrder)
open import Data.Product using (_×_; _,_)
open import Function using (_∘_; id)

open import Plasmaduck.Relation.OrderHelpers using (WeakTri; cmp₁; cmp₂; cmp₃; _Extends_)



module Plasmaduck.Relation.OperatorDefs {a : Level} (A : Set a) where

open IsEquivalence using (refl; sym; trans)

variable
    ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ : Level

SameRel : Rel A ℓ₂ → Rel A ℓ₃ → Set (a ⊔ ℓ₂ ⊔ ℓ₃)
SameRel _#_ _#'_ = (_#'_ Extends _#_) × (_#_ Extends _#'_)

SameRel-refl : {_#_ : Rel A ℓ₁} → SameRel _#_ _#_
SameRel-refl = id , id

SameRel-sym : {_#_ : Rel A ℓ₁} {_#'_ : Rel A ℓ₂} → SameRel _#_ _#'_ → SameRel _#'_ _#_
SameRel-sym (#→#' , #'→#) = #'→# , #→#'

SameRel-trans : {_#_ : Rel A ℓ₁} {_#'_ : Rel A ℓ₂} {_#''_ : Rel A ℓ₃} → SameRel _#_ _#'_ → SameRel _#'_ _#''_ → SameRel _#_ _#''_
SameRel-trans {#} {#'} {#''} (#→#' , #'→#) (#'→#'' , #''→#') = #'→#'' ∘ #→#' , #'→# ∘ #''→#'

-- Weaker than the above for sym and trans. Use the above if the relation levels are not all the same.
SameRel-eq : IsEquivalence (SameRel {ℓ₂ = ℓ₂} {ℓ₃ = ℓ₂})
SameRel-eq = record {
    refl = SameRel-refl;
    sym = SameRel-sym;
    trans = SameRel-trans
    }
