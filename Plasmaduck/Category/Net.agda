open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary using (Setoid; Rel)
open import Function using (flip)

open import Plasmaduck.SetoidExperiment.SetoidMachinery using (indiscrete-setoid)
open import Plasmaduck.Category.Category using (Category; RawCategory; IsSidedInverse; IsCommutative)



-- This is definitely not what this concept is called normally, but idk what to call it.
module Plasmaduck.Category.Net where

variable
    a b c : Level

module _ (category : Category a b c) where
    open Category category

    record AllMorphismsHaveInverses : Set (a ⊔ b ⊔ c) where
        field
            invert : {x y : Object} → Morphism x y → Morphism y x
            invert-is-left-inverse : {x y : Object} → (f : Morphism x y) → IsSidedInverse category (invert f) f
            invert-is-right-inverse : {x y : Object} → (f : Morphism x y) → IsSidedInverse category f (invert f)

    record IsNet : Set (a ⊔ b ⊔ c) where
        field
            isCommutative : IsCommutative category
            allInverses : AllMorphismsHaveInverses

        open AllMorphismsHaveInverses allInverses public

record Net (a b c : Level) : Set (lsuc a ⊔ lsuc b ⊔ lsuc c) where
    field
        category : Category a b c
        isNet : IsNet category

    open Category category public
    open IsNet isNet public


make-net : Setoid a b → Net a b lzero
make-net setoid = record {
    category = record {
        rawCategory = record {
            Object = domain;
            Morphism' = λ A B → indiscrete-setoid (A ~ B);
            id = λ x → Setoid.refl setoid {x = x};
            compose = record { func = flip (Setoid.trans setoid) }
            };
        isCategory = record {}
        };
    isNet = record {
        allInverses = record {
            invert = Setoid.sym setoid
            }
        }
    }
    where
        domain = setoid .Setoid.Carrier
        _~_ = setoid. Setoid._≈_
