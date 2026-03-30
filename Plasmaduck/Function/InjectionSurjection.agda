open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc; zero to lzero)

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Function using (Bijective; Injective; Surjective; Congruent; Bijection; Injection; Surjection; _∘_; id)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary using (IsEquivalence; Decidable)
open import Relation.Nullary using (Dec; yes; no)

open import Plasmaduck.SetoidExperiment.SetoidMachinery using (⊎-setoid; ⊎-rel; rel₁; rel₂; ×-setoid; ×-rel; discrete-setoid; from-discrete-cong; SetoidFunction; _which-is-cong_; property-subset-setoid)
open import Plasmaduck.Relation.Defs using (CongruentProperty)
open import Plasmaduck.Property.Defs using (DecidableProperty)


module Plasmaduck.Function.InjectionSurjection where

open Plasmaduck.SetoidExperiment.SetoidMachinery using (SetoidFunction; _which-is-cong_) public
open Setoid using (Carrier; isEquivalence)

module _
    {a b ℓ₁ ℓ₂ : Level}
    {A-setoid : Setoid a ℓ₁} {B-setoid : Setoid b ℓ₂}
    ((f which-is-cong f-cong) : SetoidFunction A-setoid B-setoid)
    where

    private
        A = A-setoid .Carrier
        B = B-setoid .Carrier

        _~_ = A-setoid .Setoid._≈_
        _≈_ = B-setoid .Setoid._≈_

        ~-refl = A-setoid .isEquivalence .IsEquivalence.refl
        ~-sym = A-setoid .isEquivalence .IsEquivalence.sym
        ~-trans = A-setoid .isEquivalence .IsEquivalence.trans

        ≈-refl = B-setoid .isEquivalence .IsEquivalence.refl
        ≈-sym = B-setoid .isEquivalence .IsEquivalence.sym
        ≈-trans = B-setoid .isEquivalence .IsEquivalence.trans


    LeftInverse : (g : B → A) → Set (a ⊔ ℓ₁)
    LeftInverse g = ∀ {x : A} → g (f x) ~ x

    RightInverse : (g : B → A) → Set (b ⊔ ℓ₂)
    RightInverse g = ∀ {y : B} → f (g y) ≈ y

    BothInverse : (g : B → A) → Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂)
    BothInverse g = LeftInverse g × RightInverse g

    -- Technically this is too strong; g only needs to be congruent when its domain is restricted to the range of f.
    HasLeftInverse : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂)
    HasLeftInverse = Σ (SetoidFunction B-setoid A-setoid) λ { (g which-is-cong _) → LeftInverse g }

    left-inv→injective : HasLeftInverse → Injective _~_ _≈_ f
    left-inv→injective (g which-is-cong g-cong , gfx~x) fx≈fy = ~-trans (~-trans (~-sym gfx~x) (g-cong fx≈fy)) gfx~x


    -- Likewise, I suspect this one is too strong too
    HasRightInverse : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂)
    HasRightInverse = Σ (SetoidFunction B-setoid A-setoid) λ { (g which-is-cong _) → RightInverse g }

    right-inv→surjective : HasRightInverse → Surjective _~_ _≈_ f
    right-inv→surjective (g which-is-cong g-cong , fgy~y) y = g y , λ {z} z~gy → ≈-trans (f-cong z~gy) fgy~y


    -- This, however, is just right
    HasBothInverse : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂)
    HasBothInverse = Σ (SetoidFunction B-setoid A-setoid) λ { (g which-is-cong _) → BothInverse g }

    both-inv→bijective : HasBothInverse → Bijective _~_ _≈_ f
    both-inv→bijective (g , left-inv , right-inv) = left-inv→injective  (g , left-inv) , right-inv→surjective (g , right-inv)

    bijective→both-inv : Bijective _~_ _≈_ f → HasBothInverse
    bijective→both-inv (injective , surjective) = g which-is-cong g-cong , (λ {x} →  gfx~x) , (λ {y} → fgy≈y)
        where
            g : B → A
            g = proj₁ ∘ surjective

            gfx~x : ∀ {x : A} → g (f x) ~ x
            gfx~x {x} = injective (surjective (f x) .proj₂ ~-refl)

            fgy≈y : ∀ {y : B} → f (g y) ≈ y
            fgy≈y {y} = surjective y .proj₂ ~-refl

            g-cong : Congruent _≈_ _~_ g
            g-cong {x} {y} x≈y = injective (begin
                f (g x)   ≈⟨ fgy≈y ⟩
                x           ≈⟨ x≈y ⟩
                y           ≈⟨ ≈-sym (fgy≈y) ⟩
                f (g y)   ∎)
                where open import Relation.Binary.Reasoning.Setoid B-setoid

module _
    {a b ℓ₁ ℓ₂ : Level}
    {A-setoid : Setoid a ℓ₁} {B-setoid : Setoid b ℓ₂}
    where

    bijection→injection : Bijection A-setoid B-setoid → Injection A-setoid B-setoid
    bijection→injection bij = record
      { to = bij .Bijection.to
      ; cong = bij .Bijection.cong
      ; injective = bij .Bijection.bijective .proj₁
      }

    bijection→surjection : Bijection A-setoid B-setoid → Surjection A-setoid B-setoid
    bijection→surjection bij = record
      { to = bij .Bijection.to
      ; cong = bij .Bijection.cong
      ; surjective = bij .Bijection.bijective .proj₂
      }

    {-
        Am I certain that the right inverse is congruent?

        f is surjective. This means that it hits every output (up to setoid equality)

        ∀ y → ∃ λ x → ∀ {z} → z ≈₁ x → f z ≈₂ y
        For everything in the output set, there is an input where everything equal to that input is equal to the given output. 
        (but like, obviously by congruence of the function. So I think this is equal to congruence + there is an input which maps to something equal to the output.)

        For each output equality class, grab all the corresponding inputs.
        mmm, this is not congruent. It doesn't pick one input equality class.

        For example, consider:
        setoid {{0} {1}} and setoid {{0 , 1}}
        id maps from the first to the second, and so is surjective.
        the obvious inverse maps equality class {0,1} to classes {0} and {1}, which means it is not congruent.
    -}

module _
    {a b c ℓ₁ ℓ₂ ℓ₃ : Level}
    {A-setoid : Setoid a ℓ₁} {B-setoid : Setoid b ℓ₂} {C-setoid : Setoid c ℓ₃}
    where

    infixr 9 _∘-injection_
    infixr 9 _∘-surjection_

    _∘-injection_ :  Injection B-setoid C-setoid → Injection A-setoid B-setoid → Injection A-setoid C-setoid
    _∘-injection_ g f = record {
        to = g .Injection.to ∘ f .Injection.to;
        cong = g .Injection.cong ∘ f .Injection.cong;
        injective = f .Injection.injective ∘ g .Injection.injective
        }

    _∘-surjection_ : Surjection B-setoid C-setoid → Surjection A-setoid B-setoid → Surjection A-setoid C-setoid
    _∘-surjection_ g f = record {
        to = g .Surjection.to ∘ f .Surjection.to;
        cong = g .Surjection.cong ∘ f .Surjection.cong;
        surjective = λ y →
            f .Surjection.surjective (g .Surjection.surjective y .proj₁) .proj₁
            ,
            (λ {z} z₁ →
               g .Surjection.surjective y .proj₂
               (f .Surjection.surjective (g .Surjection.surjective y .proj₁)
                .proj₂ z₁))
        }


module _
    {a ℓ ℓ₁ : Level}
    {A-setoid : Setoid a ℓ}
    (_~?_ : Decidable (A-setoid .Setoid._≈_))
    {P : A-setoid .Setoid.Carrier → Set ℓ₁}
    (P-cong : CongruentProperty A-setoid P)
    (P-dec : DecidableProperty P)
    where

    private
        A = A-setoid .Setoid.Carrier
        _~_ = A-setoid .Setoid._≈_
        open IsEquivalence (A-setoid .Setoid.isEquivalence) using (reflexive; refl; sym; trans)

    subset-surjection : {w : A} → P w → Surjection A-setoid (property-subset-setoid A-setoid P)
    subset-surjection {w} P[w] = record {
        to = to;
        cong = to-cong;
        surjective = to-surj
        }
        where
            B-setoid = property-subset-setoid A-setoid P
            B = B-setoid .Carrier
            _≈_ = B-setoid .Setoid._≈_

            to : A → B
            to x with P-dec x
            ... | yes P[x] = x , P[x]
            ... | no ¬P[x] = w , P[w]

            to-cong : Congruent _~_ _≈_ to
            to-cong {x = x} {y} x~y with P-dec x | P-dec y
            ... | yes P[x] | yes P[y] = x~y
            ... | yes P[x] | no ¬P[y] = ⊥-elim (¬P[y] (P-cong x~y P[x]))
            ... | no ¬P[x] | yes P[y] = ⊥-elim (¬P[x] (P-cong (sym x~y) P[y]))
            ... | no ¬P[x] | no ¬P[y] = refl

            to-surj' : (z : B) → {z₁ : A} → z₁ ~ z .proj₁ → to z₁ ≈ z
            to-surj' (z , P[z]) {z₁} z₁~z with P-dec z₁
            ... | yes P[z₁] = z₁~z
            ... | no ¬P[z₁] = ⊥-elim (¬P[z₁] (P-cong (sym z₁~z) P[z]))

            to-surj : Surjective _~_ _≈_ to
            to-surj (z , P[z]) = z , to-surj' (z , P[z])
