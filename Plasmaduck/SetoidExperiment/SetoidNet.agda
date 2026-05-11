open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_) renaming (refl to ≡-refl)
open import Relation.Binary using (Setoid; Rel; IsEquivalence)
open import Function using (Bijection; flip)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)

open import Plasmaduck.Function.Bijection using (_∘-bijection_; id-bijection; same-bijection; BijectionSetoid; same-bijection-left-cancel; invert-bijection; ∘-bijection-respects)
open import Plasmaduck.SetoidExperiment.SetoidMachinery using (indiscrete-setoid; SetoidFunctionEquality; SetoidFunctionEquality-eq)
open import Plasmaduck.Category.Category using (Category; RawCategory; IsSidedInverse; IsCategory)
open import Plasmaduck.Category.Net using (Net; IsNet; make-net)


-- Goal: define dependent setoid functions
module Plasmaduck.SetoidExperiment.SetoidNet where


variable
    a b c d l α β γ δ : Level

{-
    I want a Net where:
    - the carrier is (partitioned) setoids
    - the morphisms are up to one specific bijection for each pair of objects
    but I don't really want to specify the bijections by property.
-}
record SetoidNet (c l a b : Level) : Set (lsuc a ⊔ lsuc c ⊔ lsuc l ⊔ lsuc b) where
    field
        include : Setoid c l → Set a

    domain = Σ (Setoid c l) include

    field
        _~-setoid_ : Rel domain b
        ~-setoid-eq : IsEquivalence _~-setoid_
        generate-bijection : {A B : domain} → A ~-setoid B → Bijection (A .proj₁) (B .proj₁)
        trans' : {A B C : domain} → (A~B : A ~-setoid B) → (B~C : B ~-setoid C) (A~C : A ~-setoid C) → same-bijection ((generate-bijection B~C) ∘-bijection (generate-bijection A~B)) (generate-bijection A~C)


    net : Net (lsuc c ⊔ lsuc l ⊔ a) b lzero
    net = make-net record { isEquivalence = ~-setoid-eq }
    open Net net public

    id-bijection-lemma : {A : domain} → (A~A : A ~-setoid A) → same-bijection (generate-bijection A~A) (id-bijection (A .proj₁))
    id-bijection-lemma {A} A~A = same-bijection-left-cancel (generate-bijection A~A) (generate-bijection A~A) (id-bijection (A .proj₁)) 2~1
        where
            2~1 : same-bijection (generate-bijection A~A ∘-bijection generate-bijection A~A) (generate-bijection A~A)
            2~1 = trans' A~A A~A A~A

    unique-bijection : {A B : domain} → (A~B A~B' : A ~-setoid B) → same-bijection (generate-bijection A~B) (generate-bijection A~B')
    unique-bijection {A = A} {B} A~B A~B' = begin
        f                               ≈⟨ ∘-bijection-respects f f (refl {x = f}) (id-bijection (A .proj₁)) id-A ((sym {x = id-A} {y = id-bijection (A .proj₁)} (id-bijection-lemma A~A))) ⟩
        f ∘-bijection id-A              ≈⟨ ∘-bijection-respects f f (refl {x = f}) id-A (g ∘-bijection f') (sym {x = g ∘-bijection f'} {y = id-A} (trans' A~B' B~A A~A)) ⟩
        f ∘-bijection g ∘-bijection f'  ≈⟨ ∘-bijection-respects (f ∘-bijection g) id-B (trans' B~A A~B B~B) f' f' (refl {x = f'}) ⟩
        id-B ∘-bijection f'             ≈⟨ ∘-bijection-respects id-B (id-bijection (B .proj₁)) (id-bijection-lemma B~B) f' f' (refl {x = f'}) ⟩
        f'                              ∎
        where
            open import Relation.Binary.Reasoning.Setoid (BijectionSetoid (A .proj₁) (B .proj₁))
            module _ {ℓ₃ ℓ₄ ℓ₅ ℓ₆ : Level} {S₁ : Setoid ℓ₃ ℓ₄} {S₂ : Setoid ℓ₅ ℓ₆} where
                open Setoid (BijectionSetoid S₁ S₂) using (refl; sym; trans) public

            A~A : A ~-setoid A
            A~A = ~-setoid-eq .IsEquivalence.refl

            B~B : B ~-setoid B
            B~B = ~-setoid-eq .IsEquivalence.refl

            B~A : B ~-setoid A
            B~A = ~-setoid-eq .IsEquivalence.sym A~B

            id-A = generate-bijection A~A
            id-B = generate-bijection B~B
            f = generate-bijection A~B
            f' = generate-bijection A~B'
            g = generate-bijection B~A


lift-setoid : Setoid c l → SetoidNet c l (lsuc c ⊔ lsuc l) lzero
lift-setoid setoid = record {
    include = (setoid ≡_);
    _~-setoid_ = λ _ _ → ⊤;
    ~-setoid-eq = record
      { refl = λ {x} → tt
      ; sym = λ {x} {y} _ → tt
      ; trans = λ {i} {j} {k} _ _ → tt
      };
    generate-bijection = λ { {A , ≡-refl} {.A , ≡-refl} tt → id-bijection A };
    trans' = λ { {A , ≡-refl} {.A , ≡-refl} {.A , ≡-refl} tt tt tt x~y → x~y}
    }


module Tooling where
    record DependentSetoidFunctionToNet (A-setoid : Setoid a l) (B-net : SetoidNet α β γ δ) : Set (a ⊔ l ⊔ lsuc α ⊔ lsuc β ⊔ γ ⊔ δ) where
        open Setoid A-setoid using () renaming (Carrier to A-Carrier; _≈_ to _~A_)
        open SetoidNet B-net using (_~-setoid_) renaming (domain to B-domain)
        field
            type-gen : A-Carrier → SetoidNet.domain B-net
        
        type-gen-setoid : A-Carrier → Setoid α β
        type-gen-setoid = proj₁ Function.∘ type-gen

        field
            type-gen-respects : {x y : A-Carrier} → x ~A y → type-gen x ~-setoid type-gen y
            func : (x : A-Carrier) → type-gen-setoid x .Setoid.Carrier
            consistent : {x y : A-Carrier} → (x~y : x ~A y) → type-gen-setoid y .Setoid._≈_ (B-net .SetoidNet.generate-bijection {type-gen x} {type-gen y} (type-gen-respects x~y) .Bijection.to (func x)) (func y)


    -- record SetoidNetFunction (A-net : SetoidNet a b c d) (B-net : SetoidNet α β γ δ) : Set {!   !} where
    --     open SetoidNet A-net using () renaming (domain to A-domain; _~-setoid_ to _~-A-setoid_)
    --     open SetoidNet B-net using () renaming (domain to B-domain; _~-setoid_ to _~-B-setoid_)
        
    --     field
    --         funcs : ((setoid , _) : A-domain) → DependentSetoidFunctionToNet setoid B-net
    --         consistent' : 