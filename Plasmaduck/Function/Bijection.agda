open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc; zero to lzero)

open import Relation.Binary.PropositionalEquality using (_≡_; inspect; Reveal_·_is_; [_]) renaming (cong to ≡-cong; refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Data.Empty using (⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Function using (Bijective; Injective; Surjective; Congruent; Bijection; _∘_; id; flip)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary using (Rel; IsEquivalence; Reflexive; Symmetric; Transitive)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Nullary using (Dec; yes; no)

open import Plasmaduck.SetoidExperiment.SetoidMachinery using (⊎-setoid; ⊎-rel; rel₁; rel₂; ×-setoid; ×-rel; discrete-setoid; from-discrete-cong; property-subset-setoid; _which-is-cong_; SetoidFunction; SetoidFunctionEquality; SetoidFunctionEquality-eq; SetoidFunctionSetoid)
open import Plasmaduck.Property.Defs using (DecidableProperty; CongruentProperty)
open import Plasmaduck.Function.InjectionSurjection using (both-inv→bijective; bijective→both-inv; LeftInverse; RightInverse)
open import Plasmaduck.Relation.Defs using (CongruentRel)
open import Plasmaduck.Util.TypeChange using (change-type)
open import Plasmaduck.SetoidExperiment.On using (setoid-on)



module Plasmaduck.Function.Bijection where

variable
    a b c d e ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ : Level

open Setoid using (Carrier; _≈_)
open Bijection using (to; cong; bijective)


extract-func : {A-setoid : Setoid a ℓ₁} {B-setoid : Setoid b ℓ₂} → Bijection A-setoid B-setoid → SetoidFunction A-setoid B-setoid
extract-func bij = bij .to which-is-cong bij .cong

id-bijection : (A-setoid : Setoid a ℓ₁) → Bijection A-setoid A-setoid
id-bijection A-setoid = record {
    to = id;
    cong = id;
    bijective = id , λ y → (y , id)
    }

discrete-id-bijection : (A : Set a) → Bijection (discrete-setoid A) (discrete-setoid A)
discrete-id-bijection = id-bijection ∘ discrete-setoid

module InverseFunction {s₁ : Setoid c ℓ₁} {s₂ : Setoid d ℓ₂} (bij : Bijection s₁ s₂) where
    private
        f = bij .Bijection.to
        f-cong = bij .Bijection.cong
        f-surj = bij .Bijection.bijective .proj₂
        f-inj = bij .Bijection.bijective .proj₁

        _≈₁_ = s₁ ._≈_
        _≈₂_ = s₂ ._≈_

    inv : s₂ .Carrier → s₁ .Carrier
    inv y = f-surj y .proj₁

    is-right-inv : (x : s₂ .Carrier) → (bij .to (inv x)) ≈₂ x
    is-right-inv x = f-surj x .proj₂ (s₁ .Setoid.refl)

    is-left-inv : (x : s₁ .Carrier) →  (inv (bij .to x)) ≈₁ x
    is-left-inv i = f-inj (f-surj (f i) .proj₂ (s₁ .Setoid.refl))

    open IsEquivalence

    inv-congruent : Congruent _≈₂_ _≈₁_ inv
    inv-congruent {x} {y} x≈₂y = f-inj (begin
        f (inv x)   ≈⟨ is-right-inv x ⟩
        x           ≈⟨ x≈₂y ⟩
        y           ≈⟨ s₂ .Setoid.sym (is-right-inv y) ⟩
        f (inv y)   ∎)
        where open import Relation.Binary.Reasoning.Setoid s₂

    inv-injective : Injective _≈₂_ _≈₁_ inv
    inv-injective {x} {y} inv-x≈₁inv-y = begin
        x           ≈⟨ s₂ .Setoid.sym (is-right-inv x) ⟩
        f (inv x)   ≈⟨ f-cong inv-x≈₁inv-y ⟩
        f (inv y)   ≈⟨ is-right-inv y ⟩
        y           ∎
        where open import Relation.Binary.Reasoning.Setoid s₂

    inv-surjective : Surjective _≈₂_ _≈₁_ inv
    inv-surjective i = f i , λ {z} z≈₂f-i → begin
        inv z       ≈⟨ inv-congruent z≈₂f-i ⟩
        inv (f i)   ≈⟨ is-left-inv i ⟩
        i           ∎
        where open import Relation.Binary.Reasoning.Setoid s₁



invert-bijection : {s₁ : Setoid c ℓ₁} {s₂ : Setoid d ℓ₂} → Bijection s₁ s₂ → Bijection s₂ s₁
invert-bijection {s₁ = s₁} {s₂} bij = record {
    to = inv;
    cong = inv-congruent;
    bijective = inv-injective , inv-surjective
    }
    where open InverseFunction bij


infixr 9 _∘-bijection_

_∘-bijection_ : {s₁ : Setoid c ℓ₁} {s₂ : Setoid d ℓ₂} {s₃ : Setoid e ℓ₃} → Bijection s₂ s₃ → Bijection s₁ s₂ → Bijection s₁ s₃
_∘-bijection_ {s₁ = s₁} {s₂} {s₃} bij₂ bij₁ = record {
    to = f;
    cong = f-cong;
    bijective = bij₁ .bijective .proj₁ ∘ bij₂ .bijective .proj₁ , surjective
    }
    where
        f = bij₂ .to ∘ bij₁ .to

        f-cong : Congruent (s₁ ._≈_) (s₃ ._≈_) f
        f-cong = bij₂ .cong ∘ bij₁ .cong

        surj₁ = bij₁ .bijective .proj₂
        surj₂ = bij₂ .bijective .proj₂

        surjective : Surjective (s₁ ._≈_) (s₃ ._≈_) f
        surjective z with surj₂ z
        ...             | (y , f₂y≈₃z) with surj₁ y
        ...                               | (x , f₁x≈₂y) = x , λ {w} w≈₁x → begin
            f w         ≈⟨ f-cong w≈₁x ⟩
            f x         ≈⟨ bij₂ .cong (f₁x≈₂y (s₁ .Setoid.refl)) ⟩
            bij₂ .to y  ≈⟨ f₂y≈₃z (s₂ .Setoid.refl) ⟩
            z           ∎
            where open import Relation.Binary.Reasoning.Setoid s₃

bijection-eq : {a ℓ : Level} → IsEquivalence (Bijection {a} {ℓ})
bijection-eq = record {
    refl = id-bijection _;
    sym = invert-bijection;
    trans = flip _∘-bijection_
    }




BijectionSetoid : (A : Setoid a b) (B : Setoid c d) → Setoid (a ⊔ b ⊔ c ⊔ d) (a ⊔ b ⊔ d)
BijectionSetoid A B = setoid-on (SetoidFunctionSetoid A B) extract-func

same-bijection : {A : Setoid a b} {B : Setoid c d} → Rel (Bijection A B) (a ⊔ b ⊔ d)
same-bijection {A = A} {B} = BijectionSetoid A B .Setoid._≈_

module _ {A : Setoid a b} {B : Setoid c d} where
    same-bijection-left-inverse : (f : Bijection A B) → same-bijection ((invert-bijection f) ∘-bijection f) (id-bijection A)
    same-bijection-left-inverse f {x} {y} x~y = begin
        (invert-bijection f ∘-bijection f) .to x    ≈⟨ is-left-inv x ⟩
        x                                           ≈⟨ x~y ⟩
        y                                           ≈⟨ A .Setoid.refl ⟩
        id-bijection A .to y                        ∎
        where
            open import Relation.Binary.Reasoning.Setoid A
            open InverseFunction f

    same-bijection-right-inverse : (f : Bijection A B) → same-bijection (f ∘-bijection (invert-bijection f)) (id-bijection B)
    same-bijection-right-inverse f {x} {y} x~y = begin
        (f ∘-bijection invert-bijection f) .to x    ≈⟨ is-right-inv x ⟩
        x                                           ≈⟨ x~y ⟩
        y                                           ≈⟨ B .Setoid.refl ⟩
        id-bijection B .to y                        ∎
        where
            open import Relation.Binary.Reasoning.Setoid B
            open InverseFunction f

module _ {A : Setoid a b} {B : Setoid c d} {C : Setoid ℓ₁ ℓ₂} where
    ∘-bijection-respects :(g₁ g₂ : Bijection B C) (g₁~g₂ : same-bijection g₁ g₂) (f₁ f₂ : Bijection A B) (f₁~f₂ : same-bijection f₁ f₂) → same-bijection (g₁ ∘-bijection f₁) (g₂ ∘-bijection f₂)
    ∘-bijection-respects g₁ g₂ g₁~g₂ f₁ f₂ f₁~f₂ = λ z → g₁~g₂ (f₁~f₂ z)

same-bijection-left-cancel :
    {A : Setoid a b} {B : Setoid c d} {C : Setoid ℓ₁ ℓ₂} →
    (g : Bijection B C) (f₁ f₂ : Bijection A B) →
    same-bijection (g ∘-bijection f₁) (g ∘-bijection f₂) →
    same-bijection f₁ f₂
same-bijection-left-cancel {A = A} {B} {C} g f₁ f₂ g∘f₁~g∘f₂ = begin
    f₁                                      ≈⟨ refl {x = f₁} ⟩
    id-bijection B ∘-bijection f₁           ≈⟨ ∘-bijection-respects (id-bijection B) (g-inv ∘-bijection g) (sym {x = g-inv ∘-bijection g} {y = id-bijection B} (same-bijection-left-inverse g)) f₁ f₁ (refl {x = f₁}) ⟩
    g-inv ∘-bijection g ∘-bijection f₁      ≈⟨ ∘-bijection-respects g-inv g-inv (refl {x = g-inv}) (g ∘-bijection f₁) (g ∘-bijection f₂) g∘f₁~g∘f₂ ⟩
    g-inv ∘-bijection g ∘-bijection f₂      ≈⟨ ∘-bijection-respects (g-inv ∘-bijection g) (id-bijection B) (same-bijection-left-inverse g) f₂ f₂ (refl {x = f₂}) ⟩
    id-bijection B ∘-bijection f₂           ≈⟨ refl {x = f₂} ⟩
    f₂                                      ∎
    where
        open import Relation.Binary.Reasoning.Setoid (BijectionSetoid A B)
        module _ {S₁ : Setoid ℓ₃ ℓ₄} {S₂ : Setoid ℓ₅ ℓ₆} where
            open Setoid (BijectionSetoid S₁ S₂) using (refl; sym; trans) public
        g-inv = invert-bijection g





-- This setoid is not terribly useful. Since a permutation is a bijection between a setoid and itself,
-- it's an equality of setoids! Which means you can't actually tell two elements in the setoid apart.
-- It's a blur of all possible arrangements of n-item setoids (or any other bijection-equivalent class of setoids).
bijection-setoid : (c ℓ : Level) → Setoid (lsuc c ⊔ lsuc ℓ) (c ⊔ ℓ)
bijection-setoid c ℓ = record {
    Carrier = Setoid c ℓ;
    _≈_ = Bijection;
    isEquivalence = bijection-eq
    }


{-
    So maybe instead we have a consistent bijection setoid?
    Where we take bijections as objects.
    and we say that two bijections are equal if they share a key setoid.

    So this is the setoid of all setoids that are bijective with A-setoid, indexed by their bijection.
    In particular, two versions of the same setoid are different if their bijections are different.

    (But they're the same as long as the mapping function is essentially the same.)
-}
consistent-bijection-setoid : {a ℓ₁ : Level} → Setoid a ℓ₁ → (b ℓ₂ : Level) → Setoid (a ⊔ ℓ₁ ⊔ lsuc b ⊔ lsuc ℓ₂) (a ⊔ ℓ₁ ⊔ lsuc b ⊔ lsuc ℓ₂)
consistent-bijection-setoid {a = a} {ℓ₁} A-setoid b ℓ₂ = record {
    Carrier = Σ (Setoid b ℓ₂) (Bijection A-setoid);
    _≈_ = is-same-bijection;
    isEquivalence = record {
        refl = λ {x} → is-same-bijection-refl {x};
        sym = λ {x} {y} → is-same-bijection-sym {x} {y};
        trans = λ {x} {y} {z} → is-same-bijection-trans {x} {y} {z}
        }
    }
    where
        open IsEquivalence

        is-same-bijection : Rel (Σ (Setoid b ℓ₂) (Bijection A-setoid)) (a ⊔ ℓ₁ ⊔ lsuc b ⊔ lsuc ℓ₂)
        is-same-bijection (B₁-setoid , bij₁) (B₂-setoid , bij₂) = Σ (B₁-setoid ≡ B₂-setoid) λ B₁≡B₂ → SetoidFunctionEquality A-setoid B₂-setoid (change-type (≡-cong (SetoidFunction A-setoid) B₁≡B₂) (extract-func bij₁)) (extract-func bij₂)

        is-same-bijection-refl : Reflexive is-same-bijection
        is-same-bijection-refl {B-setoid , bij} = ≡-refl , SetoidFunctionEquality-eq A-setoid B-setoid .refl {x = extract-func bij}

        is-same-bijection-sym : Symmetric is-same-bijection
        is-same-bijection-sym {B₁-setoid , bij₁} {B₂-setoid , bij₂} (B₁≡B₂ , f₁~f₂) rewrite B₁≡B₂ = ≡-refl , λ x~y → B₂-setoid .Setoid.sym (f₁~f₂ (A-setoid .Setoid.sym x~y))

        is-same-bijection-trans : Transitive is-same-bijection
        is-same-bijection-trans {B₁-setoid , bij₁} {B₂-setoid , bij₂} {B₃-setoid , bij₃} (B₁≡B₂ , f₁~f₂) (B₂≡B₃ , f₂~f₃) rewrite B₁≡B₂ rewrite B₂≡B₃ = ≡-refl , λ x~y → B₃-setoid .Setoid.trans (f₁~f₂ (A-setoid .Setoid.refl)) (f₂~f₃ x~y)


module _
    {s₁ : Setoid c ℓ₁} {s₂ : Setoid d ℓ₂} (bij : Bijection s₁ s₂)
    where

    private
        A = s₁ .Carrier
        B = s₂ .Carrier

        f-func : SetoidFunction s₁ s₂
        f-func = (bij .Bijection.to) which-is-cong (bij .Bijection.cong)

        g : B → A
        g = (invert-bijection bij) .Bijection.to

    open InverseFunction bij

    invert-is-left-inverse : LeftInverse s₁ s₂ f-func g
    invert-is-left-inverse {x = x} = is-left-inv x

    invert-is-right-inverse : RightInverse s₁ s₂ f-func g
    invert-is-right-inverse {y = y} = is-right-inv y

module _ (A-setoid : Setoid a ℓ₁) where
    private
        A = A-setoid .Carrier
        _~-fine_ = A-setoid ._≈_

    module _ (P : A → Set ℓ₂) (all-P : (x : A) → P x) where
        property-split : Bijection A-setoid (property-subset-setoid A-setoid P)
        property-split = record {
            to = f;
            cong = id;
            bijective = id , (λ (x , P[x]) → x , id)
            }
            where
                B-setoid = (property-subset-setoid A-setoid P)
                B = B-setoid .Carrier

                f : A → B
                f x = x , all-P x


⊎-bijection :
    {s₁ : Setoid a ℓ₁} {s₂ : Setoid b ℓ₂} {s₃ : Setoid c ℓ₃} {s₄ : Setoid d ℓ₄} →
    Bijection s₁ s₂ → Bijection s₃ s₄ → Bijection (⊎-setoid s₁ s₃) (⊎-setoid s₂ s₄)
⊎-bijection {s₁ = s₁} {s₂} {s₃} {s₄} bij₁₂ bij₃₄ = record {
    to = f;
    cong = f-cong;
    bijective = f-injective , f-surjective
    }
    where
        f : (⊎-setoid s₁ s₃) .Carrier → (⊎-setoid s₂ s₄) .Carrier
        f (inj₁ x) = inj₁ (bij₁₂ .to x)
        f (inj₂ x) = inj₂ (bij₃₄ .to x)

        f-cong : Congruent ((⊎-setoid s₁ s₃) ._≈_) ((⊎-setoid s₂ s₄) ._≈_) f
        f-cong {inj₁ x} {inj₁ y} (rel₁ x≈₁y) = rel₁ (bij₁₂ .cong x≈₁y)
        f-cong {inj₂ x} {inj₂ y} (rel₂ x≈₃y) = rel₂ (bij₃₄ .cong x≈₃y)

        f-injective : Injective ((⊎-setoid s₁ s₃) ._≈_) ((⊎-setoid s₂ s₄) ._≈_) f
        f-injective {inj₁ x} {inj₁ y} (rel₁ fx≈₂fy) = rel₁ (bij₁₂ .bijective .proj₁ fx≈₂fy)
        f-injective {inj₂ x} {inj₂ y} (rel₂ fx≈₄fy) = rel₂ (bij₃₄ .bijective .proj₁ fx≈₄fy)

        f-surjective : Surjective ((⊎-setoid s₁ s₃) ._≈_) ((⊎-setoid s₂ s₄) ._≈_) f
        f-surjective (inj₁ x) = inj₁ (inv x) , λ { {inj₁ z} (rel₁ z≈₁invx) → rel₁ (begin
            bij₁₂ .to z         ≈⟨ bij₁₂ .cong z≈₁invx ⟩
            bij₁₂ .to (inv x)   ≈⟨ is-right-inv x ⟩
            x                   ∎)}
            where
                open InverseFunction bij₁₂
                open import Relation.Binary.Reasoning.Setoid s₂
        f-surjective (inj₂ x) = inj₂ (inv x) , λ { {inj₂ z} (rel₂ z≈₃invx) → rel₂ (begin
            bij₃₄ .to z         ≈⟨ bij₃₄ .cong z≈₃invx ⟩
            bij₃₄ .to (inv x)   ≈⟨ is-right-inv x ⟩
            x                   ∎)}
            where
                open InverseFunction bij₃₄
                open import Relation.Binary.Reasoning.Setoid s₄

⊎-discrete-distributivity : (A : Set a) (B : Set b) → Bijection (discrete-setoid (A ⊎ B)) (⊎-setoid (discrete-setoid A) (discrete-setoid B))
⊎-discrete-distributivity A B = record {
    to = f;
    cong = from-discrete-cong {A = A ⊎ B} (⊎-setoid (discrete-setoid A) (discrete-setoid B)) f;
    bijective = injective , surjective
    }
    where
        open import Relation.Binary.PropositionalEquality using (_≡_; inspect; Reveal_·_is_; [_]) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans; cong to ≡-cong)

        f : A ⊎ B → A ⊎ B
        f = id

        injective : Injective _≡_ (⊎-rel (discrete-setoid A) (discrete-setoid B)) f
        injective {inj₁ x} {inj₁ y} (rel₁ x≡y) = ≡-cong inj₁ x≡y
        injective {inj₂ x} {inj₂ y} (rel₂ x≡y) = ≡-cong inj₂ x≡y

        surjective : Surjective _≡_ (⊎-rel (discrete-setoid A) (discrete-setoid B)) f
        surjective (inj₁ x) = inj₁ x , λ { {inj₁ y} ≡-refl → rel₁ ≡-refl }
        surjective (inj₂ x) = inj₂ x , λ { {inj₂ y} ≡-refl → rel₂ ≡-refl }

⊎-property-split-bijection :
    (s : Setoid a ℓ₁) (P : s .Carrier → Set ℓ₂) →
    (P-cong : CongruentProperty s P) →
    (P-dec : DecidableProperty P) →
    Bijection s (⊎-setoid (property-subset-setoid s P) (property-subset-setoid s (¬_ ∘ P)))
⊎-property-split-bijection s₁ P P-cong P-dec = record {
    to = f;
    cong = f-cong;
    bijective = both-inv→bijective s₁ s₂ (f which-is-cong f-cong) ((inv which-is-cong inv-cong) , is-left-inv , is-right-inv)
    }
    where
        s₂ = (⊎-setoid (property-subset-setoid s₁ P) (property-subset-setoid s₁ (¬_ ∘ P)))
        A = s₁ .Carrier
        B = s₂ .Carrier
        _≈₁_ = s₁ ._≈_
        _≈₂_ = s₂ ._≈_

        f : A → B
        f x with P-dec x
        ... | yes pf = inj₁ (x , pf)
        ... | no pf = inj₂ (x , pf)

        f-cong : Congruent _≈₁_ _≈₂_ f
        f-cong {x = x} {y} x≈₁y with P-dec x | P-dec y
        ... | yes P[x] | yes P[y] = rel₁ x≈₁y
        ... | yes P[x] | no ¬P[y] = ⊥-elim (¬P[y] (P-cong x≈₁y P[x]))
        ... | no ¬P[x] | yes P[y] = ⊥-elim (¬P[x] (P-cong (IsEquivalence.sym (Setoid.isEquivalence s₁) x≈₁y) P[y]))
        ... | no ¬P[x] | no ¬P[y] = rel₂ x≈₁y

        inv : B → A
        inv (inj₁ (x , _)) = x
        inv (inj₂ (x , _)) = x

        inv-cong : Congruent _≈₂_ _≈₁_ inv
        inv-cong {x = inj₁ (x , P[x])} {inj₁ (y , P[y])} (rel₁ x≈₁y) = x≈₁y
        inv-cong {x = inj₂ (x , ¬P[x])} {inj₂ (y , ¬P[y])} (rel₂ x≈₁y) = x≈₁y

        is-left-inv : LeftInverse s₁ s₂ (f which-is-cong f-cong) inv
        is-left-inv {x = x} with P-dec x
        ... | yes _ = IsEquivalence.refl (Setoid.isEquivalence s₁)
        ... | no _ = IsEquivalence.refl (Setoid.isEquivalence s₁)

        is-right-inv : RightInverse s₁ s₂ (f which-is-cong f-cong) inv
        is-right-inv {inj₁ (x , P[x])} with P-dec x
        ... | yes P[x]' = rel₁ (IsEquivalence.refl (Setoid.isEquivalence s₁))
        ... | no ¬P[x]' = ⊥-elim (¬P[x]' P[x])
        is-right-inv {inj₂ (x , ¬P[x])} with P-dec x
        ... | yes P[x]' = ⊥-elim (¬P[x] P[x]')
        ... | no ¬P[x]' = rel₂ (IsEquivalence.refl (Setoid.isEquivalence s₁))


×-bijection :
    {s₁ : Setoid a ℓ₁} {s₂ : Setoid b ℓ₂} {s₃ : Setoid c ℓ₃} {s₄ : Setoid d ℓ₄} →
    Bijection s₁ s₂ → Bijection s₃ s₄ → Bijection (×-setoid s₁ s₃) (×-setoid s₂ s₄)
×-bijection {s₁ = s₁} {s₂} {s₃} {s₄} bij₁₂ bij₃₄ = record {
    to = f;
    cong = f-cong;
    bijective = f-injective , f-surjective
    }
    where
        f : (×-setoid s₁ s₃) .Carrier → (×-setoid s₂ s₄) .Carrier
        f (x₁ , x₂) = bij₁₂ .to x₁ , bij₃₄ .to x₂

        f-cong : Congruent ((×-setoid s₁ s₃) ._≈_) ((×-setoid s₂ s₄) ._≈_) f
        f-cong (x₁ , x₂) = bij₁₂ .cong x₁ , bij₃₄ .cong x₂

        f-injective : Injective ((×-setoid s₁ s₃) ._≈_) ((×-setoid s₂ s₄) ._≈_) f
        f-injective (x₁ , x₂) =
            bij₁₂ .bijective .proj₁ x₁ ,
            bij₃₄ .bijective .proj₁ x₂

        f-surjective : Surjective ((×-setoid s₁ s₃) ._≈_) ((×-setoid s₂ s₄) ._≈_) f
        f-surjective (x₁ , x₂) =
            (bij₁₂ .bijective .proj₂ x₁ .proj₁ ,
             bij₃₄ .bijective .proj₂ x₂ .proj₁)
            ,
            (λ {z} z~x →
               bij₁₂ .bijective .proj₂ x₁ .proj₂ (z~x .proj₁) ,
               bij₃₄ .bijective .proj₂ x₂ .proj₂ (z~x .proj₂))

×-discrete-distributivity : (A : Set a) (B : Set b) → Bijection (discrete-setoid (A × B)) (×-setoid (discrete-setoid A) (discrete-setoid B))
×-discrete-distributivity A B = record {
    to = f;
    cong = from-discrete-cong {A = A × B} (×-setoid (discrete-setoid A) (discrete-setoid B)) f;
    bijective = injective , surjective
    }
    where
        open import Relation.Binary.PropositionalEquality using (_≡_; inspect; Reveal_·_is_; [_]) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans; cong to ≡-cong)

        f : A × B → A × B
        f = id

        injective : Injective _≡_ (×-rel (discrete-setoid A) (discrete-setoid B)) f
        injective (≡-refl , ≡-refl) = ≡-refl

        surjective : Surjective _≡_ (×-rel (discrete-setoid A) (discrete-setoid B)) f
        surjective (x₁ , y₁) = (x₁ , y₁) , λ { ≡-refl → ≡-refl , ≡-refl }
