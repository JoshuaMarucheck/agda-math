open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary using (Setoid; Rel; IsEquivalence)
open import Function using (Bijective; Injective; Surjective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₂)

open import Plasmaduck.SetoidExperiment.SetoidMachinery using (SetoidFunction₂; _which-is-cong₂_; _←₂_; SetoidFunction; _which-is-cong_; _←_; property-subset-setoid; flipSetoidFunction₂)
open import Plasmaduck.Function.Properties using (module SingleOperator; module Helpers; Involutive)



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

    open import Algebra.Definitions _≈_

    _∙_ : Carrier → Carrier → Carrier
    _∙_ = _←₂_ op
    infixl 10 _∙_ _∸_

    inv : Carrier → Carrier
    inv = _←_ inverse

    ∙-cong = op .SetoidFunction₂.respects
    inv-cong = inverse .SetoidFunction.respects

    _∸_ : Carrier → Carrier → Carrier
    x ∸ y = x ∙ inv y

    ∸-cong : Congruent₂ _∸_
    ∸-cong ≈₁ ≈₂ = ∙-cong ≈₁ (inv-cong ≈₂)

record IsGroup (rawGroup : RawGroup c ℓ) : Set (c ⊔ ℓ) where
    open RawGroup rawGroup
    open SingleOperator _≈_ using (LeftIdentity; RightIdentity; Identity; Associative)
    open Helpers CarrierSetoid using () renaming (assoc-middle to assoc-middle')

    field
        id-is-left-id : LeftIdentity _∙_ id
        inv-is-left-inv : ∀ x → inv x ∙ x ≈ id
        assoc : Associative _∙_

    open import Relation.Binary.Reasoning.Setoid CarrierSetoid
    open IsEquivalence (CarrierSetoid .Setoid.isEquivalence)
    -- TODO Eventually I'd like to switch to using these, which use explicit inputs
    -- TOOD renamine id to e
    open import Algebra.Definitions _≈_ using (LeftCancellative; RightCancellative; Cancellative)
    open import Algebra.Consequences.Setoid CarrierSetoid
        using (comm∧cancelʳ⇒cancelˡ; comm∧distrʳ⇒distrˡ; comm∧distrˡ⇒distrʳ
            ; comm⇒sym[distribˡ])

    assoc-middle = assoc-middle' _∙_ assoc (inj₂ (λ _ → ∙-cong refl))

    inv-is-right-inv : ∀ x → x ∙ inv x ≈ id
    inv-is-right-inv x = begin
        x ∙ inv x                           ≈⟨ sym (id-is-left-id (x ∙ inv x)) ⟩
        id ∙ (x ∙ inv x)                    ≈⟨ ∙-cong (sym (inv-is-left-inv (inv x))) refl ⟩
        (inv (inv x) ∙ inv x) ∙ (x ∙ inv x) ≈⟨ assoc-middle (inv (inv x)) (inv x) x (inv x) ⟩
        (inv (inv x) ∙ (inv x ∙ x)) ∙ inv x ≈⟨ assoc (inv (inv x)) (inv x ∙ x) (inv x) ⟩
        inv (inv x) ∙ ((inv x ∙ x) ∙ inv x) ≈⟨ ∙-cong refl (∙-cong (inv-is-left-inv x) refl) ⟩
        inv (inv x) ∙ (id ∙ inv x)          ≈⟨ ∙-cong refl (id-is-left-id (inv x)) ⟩
        inv (inv x) ∙ inv x                 ≈⟨ inv-is-left-inv (inv x) ⟩
        id                                  ∎

    id-is-right-id : RightIdentity _∙_ id
    id-is-right-id x = begin
        x ∙ id          ≈⟨ ∙-cong refl (sym (inv-is-left-inv x)) ⟩
        x ∙ (inv x ∙ x) ≈⟨ sym (assoc x (inv x) x) ⟩
        (x ∙ inv x) ∙ x ≈⟨ ∙-cong (inv-is-right-inv x) refl ⟩
        id ∙ x          ≈⟨ id-is-left-id x ⟩
        x               ∎

    identity : Identity _∙_ id
    identity = id-is-left-id , id-is-right-id

    inv-is-involution : Involutive _≈_ inv
    inv-is-involution x = begin
        inv (inv x)                 ≈⟨ sym (id-is-right-id (inv (inv x))) ⟩
        inv (inv x) ∙ id            ≈⟨ ∙-cong refl (sym (inv-is-left-inv x)) ⟩
        inv (inv x) ∙ (inv x ∙ x)   ≈⟨ sym (assoc (inv (inv x)) (inv x) x) ⟩
        (inv (inv x) ∙ inv x) ∙ x   ≈⟨ ∙-cong (inv-is-left-inv (inv x)) refl ⟩
        id ∙ x                      ≈⟨ id-is-left-id x ⟩
        x                           ∎

    inv-flip-distributes : ∀ x y → inv (x ∙ y) ≈ inv y ∙ inv x
    inv-flip-distributes x y = begin
        inv (x ∙ y)                                 ≈⟨ sym (id-is-right-id _) ⟩
        inv (x ∙ y) ∙ id                            ≈⟨ ∙-cong refl (sym (inv-is-right-inv x)) ⟩
        inv (x ∙ y) ∙ (x ∙ inv x)                   ≈⟨ ∙-cong refl (∙-cong (sym (id-is-right-id x)) refl) ⟩
        inv (x ∙ y) ∙ (x ∙ id ∙ inv x)              ≈⟨ ∙-cong refl (∙-cong (∙-cong refl (sym (inv-is-right-inv y))) refl) ⟩
        inv (x ∙ y) ∙ (x ∙ (y ∙ inv y) ∙ inv x)     ≈⟨ ∙-cong refl (sym (assoc-middle x y (inv y) (inv x))) ⟩
        inv (x ∙ y) ∙ ((x ∙ y) ∙ (inv y ∙ inv x))   ≈⟨ sym (assoc _ _ _) ⟩
        (inv (x ∙ y) ∙ (x ∙ y)) ∙ (inv y ∙ inv x)   ≈⟨ ∙-cong (inv-is-left-inv _) refl ⟩
        id ∙ (inv y ∙ inv x)                        ≈⟨ id-is-left-id _ ⟩
        inv y ∙ inv x                               ∎

    inv-id-is-id : inv id ≈ id
    inv-id-is-id = begin
        inv id                  ≈⟨ sym (id-is-right-id (inv id)) ⟩
        inv id ∙ id             ≈⟨ ∙-cong refl (sym (inv-is-involution id)) ⟩
        inv id ∙ inv (inv id)   ≈⟨ sym (inv-flip-distributes (inv id) id) ⟩
        inv (inv id ∙ id)       ≈⟨ inv-cong (id-is-right-id (inv id)) ⟩
        inv (inv id)            ≈⟨ inv-is-involution id ⟩
        id ∎

    inv-flips-∸ : ∀ x y → inv (x ∸ y) ≈ y ∸ x
    inv-flips-∸ x y = begin
        inv (x ∸ y)             ≈⟨ inv-flip-distributes x (inv y) ⟩
        inv (inv y) ∙ inv x     ≈⟨ ∙-cong (inv-is-involution y) refl ⟩
        y ∙ inv x               ≈⟨ refl ⟩
        y ∸ x                   ∎

    m∙n∸n=m : ∀ m n → m ∙ n ∸ n ≈ m
    m∙n∸n=m m n = begin
        m ∙ n ∙ inv n       ≈⟨ assoc m n (inv n) ⟩
        m ∙ (n ∙ inv n)     ≈⟨ ∙-cong refl (inv-is-right-inv n) ⟩
        m ∙ id              ≈⟨ id-is-right-id m ⟩
        m                   ∎

    m∸n∙n=m : ∀ m n → m ∸ n ∙ n ≈ m
    m∸n∙n=m m n = begin
        m ∙ inv n ∙ n       ≈⟨ assoc m (inv n) n ⟩
        m ∙ (inv n ∙ n)     ≈⟨ ∙-cong refl (inv-is-left-inv n) ⟩
        m ∙ id              ≈⟨ id-is-right-id m ⟩
        m                   ∎

    -m∙[m∙n]=n : ∀ m n → inv m ∙ (m ∙ n) ≈ n
    -m∙[m∙n]=n m n = begin
        inv m ∙ (m ∙ n)     ≈⟨ sym (assoc (inv m) m n) ⟩
        (inv m ∙ m) ∙ n     ≈⟨ ∙-cong (inv-is-left-inv m) refl ⟩
        id ∙ n              ≈⟨ id-is-left-id n ⟩
        n                   ∎

    ∙-cancelʳ : RightCancellative _∙_
    ∙-cancelʳ m n o n∙m=o∙m = begin
        n           ≈⟨ sym (m∙n∸n=m n m) ⟩
        n ∙ m ∸ m   ≈⟨ ∸-cong n∙m=o∙m refl ⟩
        o ∙ m ∸ m   ≈⟨ m∙n∸n=m o m ⟩
        o           ∎

    ∙-cancelˡ : LeftCancellative _∙_
    ∙-cancelˡ m n o m∙n=m∙o = begin
        n                   ≈⟨ sym (-m∙[m∙n]=n m n) ⟩
        inv m ∙ (m ∙ n)     ≈⟨ ∙-cong refl m∙n=m∙o ⟩
        inv m ∙ (m ∙ o)     ≈⟨ -m∙[m∙n]=n m o ⟩
        o                   ∎

    ∙-cancel : Cancellative _∙_
    ∙-cancel = ∙-cancelˡ , ∙-cancelʳ

    inv-injective : Injective _≈_ _≈_ inv
    inv-injective {x} {y} inv-x=inv-y = begin
        x               ≈⟨ sym (inv-is-involution x) ⟩
        inv (inv x)     ≈⟨ inv-cong inv-x=inv-y ⟩
        inv (inv y)     ≈⟨ inv-is-involution y ⟩
        y               ∎

    inv-surjective : Surjective _≈_ _≈_ inv
    inv-surjective x = inv x , λ {z} z≈inv-x → begin
        inv z           ≈⟨ inv-cong z≈inv-x ⟩
        inv (inv x)     ≈⟨ inv-is-involution x ⟩
        x               ∎

    inv-bijective : Bijective _≈_ _≈_ inv
    inv-bijective = inv-injective , inv-surjective

    ∙-∸-assoc : ∀ m n o → (m ∙ n) ∸ o ≈ m ∙ (n ∸ o)
    ∙-∸-assoc m n o = assoc m n (inv o)


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
    open RawGroup A using (_∙_)
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
            id-is-left-id = λ x → id-is-left-id (x .proj₁);
            inv-is-left-inv = λ x → inv-is-left-inv (x .proj₁);
            assoc = λ x y z → assoc (x .proj₁) (y .proj₁) (z .proj₁)
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
IsAbelian rawGroup = Commutative _∙_
    where
        open RawGroup rawGroup
        open import Algebra.Definitions _≈_ using (Commutative)

record IsAbelianGroup (rawGroup : RawGroup c ℓ) : Set (c ⊔ ℓ) where
    field
        isGroup : IsGroup rawGroup
        abelian : IsAbelian rawGroup
    open IsGroup isGroup public

    open RawGroup rawGroup
    open import Relation.Binary.Reasoning.Setoid CarrierSetoid
    open IsEquivalence (CarrierSetoid .Setoid.isEquivalence)
    open import Algebra.Definitions _≈_ using (Commutative)

    inv-distributes : ∀ {x y} → inv (x ∙ y) ≈ inv x ∙ inv y
    inv-distributes {x} {y} = begin
        inv (x ∙ y)     ≈⟨ inv-flip-distributes x y ⟩
        inv y ∙ inv x   ≈⟨ abelian (inv y) (inv x) ⟩
        inv x ∙ inv y   ∎

    comm = abelian

    m∙n∙o=m∙o∙n : ∀ m n o → m ∙ n ∙ o ≈ m ∙ o ∙ n
    m∙n∙o=m∙o∙n m n o = begin
        m ∙ n ∙ o       ≈⟨ assoc m n o ⟩
        m ∙ (n ∙ o)     ≈⟨ ∙-cong {m} refl (comm n o) ⟩
        m ∙ (o ∙ n)     ≈⟨ sym (assoc m o n) ⟩
        m ∙ o ∙ n       ∎

    m∙n∸m=n : ∀ m n → m ∙ n ∸ m ≈ n
    m∙n∸m=n m n = trans (∸-cong {u = m} (comm m n) refl) (m∙n∸n=m n m)

record AbelianGroup (c ℓ : Level) : Set (lsuc c ⊔ lsuc ℓ) where
    field
        rawGroup : RawGroup c ℓ
        isAbelianGroup : IsAbelianGroup rawGroup
    open RawGroup rawGroup public
    open IsAbelianGroup isAbelianGroup public

----------------------
--- Opposite Group ---
----------------------

opposite-raw-group : RawGroup c ℓ → RawGroup c ℓ
opposite-raw-group rawGroup = record {
    CarrierSetoid = CarrierSetoid;
    op = flipSetoidFunction₂ op;
    inverse = inverse;
    id = id
    }
    where open RawGroup rawGroup

opposite-is-group : {rawGroup : RawGroup c ℓ} → IsGroup rawGroup → IsGroup (opposite-raw-group rawGroup)
opposite-is-group {rawGroup = rawGroup} isGroup = record {
    id-is-left-id = id-is-right-id;
    inv-is-left-inv = inv-is-right-inv;
    assoc = λ x y z → sym (assoc z y x)
    }
    where
        open RawGroup rawGroup
        open IsGroup isGroup
        open Setoid CarrierSetoid using (sym)

opposite-group : Group c ℓ → Group c ℓ
opposite-group group = record {
    rawGroup = opposite-raw-group rawGroup;
    isGroup = opposite-is-group isGroup
    }
    where open Group group

opposite-is-abelian-group : {rawGroup : RawGroup c ℓ} → IsAbelianGroup rawGroup → IsAbelianGroup (opposite-raw-group rawGroup)
opposite-is-abelian-group {rawGroup = rawGroup} isAbelianGroup = record {
    isGroup = opposite-is-group isGroup;
    abelian = Function.flip abelian
    }
    where open IsAbelianGroup isAbelianGroup

opposite-abelian-group : AbelianGroup c ℓ → AbelianGroup c ℓ
opposite-abelian-group group = record {
    rawGroup = opposite-raw-group rawGroup;
    isAbelianGroup = opposite-is-abelian-group isAbelianGroup
    }
    where open AbelianGroup group
