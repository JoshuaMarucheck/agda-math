open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc; zero to lzero)

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Function using (Bijective; Injective; Surjective; Congruent; Bijection; Injection; Surjection; _∘_; id)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary using (IsEquivalence; Decidable)
open import Relation.Nullary using (¬_; Dec; yes; no)

open import Plasmaduck.SetoidExperiment.SetoidMachinery using (⊎-setoid; ⊎-rel; rel₁; rel₂; ×-setoid; ×-rel; discrete-setoid; from-discrete-cong; SetoidFunction; _which-is-cong_; property-subset-setoid)
open import Plasmaduck.Relation.Defs using (CongruentProperty)
open import Plasmaduck.Property.Defs using (DecidableProperty; _Extends_)
open import Plasmaduck.Function.InjectionSurjection using (_∘-surjection_; surjection-weak-right-inv; subset-surjection)
open import Plasmaduck.Property.Defs using (any-type)


-- For use of surjections as set size comparisons (since weird things happen with empty sets)
module Plasmaduck.Function.Surjectionish where

open Setoid using (Carrier)

variable
    a b c ℓ ℓ₁ ℓ₂ ℓ₃ ℓ' : Level


Surjectionish : (A-setoid : Setoid a ℓ₁) → (B-setoid : Setoid b ℓ₂) → Set (a ⊔ ℓ₁ ⊔ b ⊔ ℓ₂)
Surjectionish A-setoid B-setoid = Surjection A-setoid B-setoid ⊎ ¬ (B-setoid .Carrier)

_∘-surjectionish_ :
    {A-setoid : Setoid a ℓ₁} {B-setoid : Setoid b ℓ₂} {C-setoid : Setoid c ℓ₃} →
    Surjectionish B-setoid C-setoid →
    Surjectionish A-setoid B-setoid →
    Surjectionish A-setoid C-setoid
(inj₁ g) ∘-surjectionish (inj₁ f) = inj₁ (g ∘-surjection f)
_∘-surjectionish_ {A-setoid = A-setoid} {B-setoid} {C-setoid} (inj₁ g) (inj₂ ¬B) = inj₂ (¬B ∘ surjection-weak-right-inv B-setoid C-setoid g)
(inj₂ ¬C) ∘-surjectionish _ = inj₂ ¬C

surjection→surjectionish :
    {A-setoid : Setoid a ℓ₁} {B-setoid : Setoid b ℓ₂} →
    Surjection A-setoid B-setoid →
    Surjectionish A-setoid B-setoid
surjection→surjectionish = inj₁

surjectionish→surjection :
    {A-setoid : Setoid a ℓ₁} {B-setoid : Setoid b ℓ₂} →
    Surjectionish A-setoid B-setoid →
    B-setoid .Carrier →
    Surjection A-setoid B-setoid
surjectionish→surjection (inj₁ f) _ = f
surjectionish→surjection (inj₂ ¬B) x = ⊥-elim (¬B x)
