open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary using (Setoid; Rel; IsEquivalence)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)

open import Plasmaduck.SetoidExperiment.SetoidMachinery using (SetoidFunction₂; _which-is-cong₂_; _←₂_; SetoidFunction; _which-is-cong_; _←_; property-subset-setoid)
open import Plasmaduck.Function.Properties using (module SingleOperator)



module Plasmaduck.Algebra.Group.Defs where

variable
    a b c ℓ ℓ₁ ℓ₂ : Level

record RawGroup (c ℓ : Level) : Set (lsuc c ⊔ lsuc ℓ) where
    field
        CarrierSetoid : Setoid c ℓ

    Carrier : Set c
    Carrier = CarrierSetoid .Setoid.Carrier

    field
        op : SetoidFunction₂ CarrierSetoid CarrierSetoid CarrierSetoid
        inverse : SetoidFunction CarrierSetoid CarrierSetoid
        id : Carrier

    _≈_ : Rel Carrier ℓ
    _≈_ = CarrierSetoid .Setoid._≈_
    infix 6 _≈_

    _∙_ : Carrier → Carrier → Carrier
    _∙_ = _←₂_ op
    infixr 10 _∙_

    ∙-cong = op .SetoidFunction₂.respects
    inv-cong = inverse .SetoidFunction.respects

    inv : Carrier → Carrier
    inv = _←_ inverse

record IsGroup (rawGroup : RawGroup c ℓ) : Set (c ⊔ ℓ) where
    open RawGroup rawGroup
    open SingleOperator CarrierSetoid

    field
        id-is-left-id : LeftIdentity _∙_ id
        inv-is-left-inv : ∀ {x : Carrier} → inv x ∙ x ≈ id
        assoc : Associative _∙_

    open import Relation.Binary.Reasoning.Setoid CarrierSetoid
    open IsEquivalence (CarrierSetoid .Setoid.isEquivalence)

    inv-is-right-inv : ∀ {x : Carrier} → x ∙ inv x ≈ id
    inv-is-right-inv {x} = begin
        x ∙ inv x                           ≈⟨ sym id-is-left-id ⟩
        id ∙ (x ∙ inv x)                    ≈⟨ ∙-cong (sym inv-is-left-inv) refl ⟩
        (inv (inv x) ∙ inv x) ∙ (x ∙ inv x) ≈⟨ sym assoc ⟩
        inv (inv x) ∙ (inv x ∙ (x ∙ inv x)) ≈⟨ ∙-cong refl assoc ⟩
        inv (inv x) ∙ ((inv x ∙ x) ∙ inv x) ≈⟨ ∙-cong refl (∙-cong inv-is-left-inv refl) ⟩
        inv (inv x) ∙ (id ∙ inv x)          ≈⟨ ∙-cong refl id-is-left-id ⟩
        inv (inv x) ∙ inv x                 ≈⟨ inv-is-left-inv ⟩
        id                                  ∎

    id-is-right-id : RightIdentity _∙_ id
    id-is-right-id {x} = begin
        x ∙ id          ≈⟨ ∙-cong refl (sym inv-is-left-inv) ⟩
        x ∙ (inv x ∙ x) ≈⟨ assoc ⟩
        (x ∙ inv x) ∙ x ≈⟨ ∙-cong inv-is-right-inv refl ⟩
        id ∙ x          ≈⟨ id-is-left-id ⟩
        x               ∎

record Group (c ℓ : Level) : Set (lsuc c ⊔ lsuc ℓ) where
    field
        rawGroup : RawGroup c ℓ
        isGroup : IsGroup rawGroup
    open RawGroup rawGroup public
    open IsGroup isGroup public

--------------------
--- Homomorphism ---
--------------------

record GroupHomomorphism (A : RawGroup a ℓ₁) (B : RawGroup b ℓ₂) : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
    open RawGroup A using (_∙_) renaming ()
    open RawGroup B using (_≈_) renaming (_∙_ to _*_)
    field
        func : SetoidFunction (A .RawGroup.CarrierSetoid) (B .RawGroup.CarrierSetoid)
        respects-∙ : ∀ {x y : RawGroup.Carrier A} → func ← (x ∙ y) ≈ (func ← x) * (func ← y)

RawSubgroupOf : (G : Set a) (ℓ₂ : Level) → Set (a ⊔ lsuc ℓ₂)
RawSubgroupOf G ℓ₂ = G → Set ℓ₂

record IsSubgroupOf (G : RawGroup a ℓ) {ℓ₂ : Level} (include : RawSubgroupOf (RawGroup.Carrier G) ℓ₂) : Set (a ⊔ ℓ₂) where
    open RawGroup G
    field
        contains-id : include id
        closed-under-inv : ∀ {x : Carrier} → include x → include (inv x)
        closed-under-∙ : ∀ {x y : Carrier} → include x → include y → include (x ∙ y)

record SubgroupOf (G : Group a ℓ) (ℓ₂ : Level) : Set (a ⊔ lsuc ℓ₂) where
    open Group G
    field
        include : RawSubgroupOf Carrier ℓ₂
        isSubgroup : IsSubgroupOf rawGroup include
    open IsSubgroupOf isSubgroup public

    group : Group (a ⊔ ℓ₂) ℓ
    group = record {
        rawGroup = record {
            CarrierSetoid = property-subset-setoid CarrierSetoid include;
            op = (λ (x , x-pf) (y , y-pf) → x ∙ y , closed-under-∙ x-pf y-pf) which-is-cong₂ ∙-cong;
            inverse = (λ (x , x-pf) → inv x , closed-under-inv x-pf) which-is-cong inv-cong;
            id = id , contains-id
            };
        isGroup = record {
            id-is-left-id = id-is-left-id;
            inv-is-left-inv = inv-is-left-inv;
            assoc = assoc
            }
        }

-- Normal Subgroup: N ◃ G if N is a normal subgroup of G
-- record _◃_ {ℓ₃ : Level} (N : Group a ℓ₁) (G : Group b ℓ₂) : Set {!   !} where
--     field
--         isSubgroup :


---------------
--- Abelian ---
---------------

IsAbelian : (rawGroup : RawGroup c ℓ) → Set (c ⊔ ℓ)
IsAbelian rawGroup = ∀ {x y} → x ∙ y ≈ y ∙ x
    where open RawGroup rawGroup

record IsAbelianGroup (rawGroup : RawGroup c ℓ) : Set (c ⊔ ℓ) where
    field
        isGroup : IsGroup rawGroup
        abelian : IsAbelian rawGroup
    open IsGroup isGroup public

record AbelianGroup (c ℓ : Level) : Set (lsuc c ⊔ lsuc ℓ) where
    field
        rawGroup : RawGroup c ℓ
        isAbelianGroup : IsAbelianGroup rawGroup
    open RawGroup rawGroup public
    open IsAbelianGroup isAbelianGroup public