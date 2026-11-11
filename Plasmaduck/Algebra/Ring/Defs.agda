open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Relation.Binary.PropositionalEquality using (subst)
open import Relation.Binary using (Setoid; Rel; IsEquivalence; IsPartialOrder; IsPreorder; Reflexive; Symmetric; Transitive; Antisymmetric)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Function using ()
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (ℕ) renaming (zero to zeroℕ; suc to sucℕ; _+_ to _+ℕ_; _*_ to _*ℕ_; _∸_ to _∸ℕ_; _≤_ to _≤ℕ_)
open import Data.Nat.Properties using (m∸n+n≡m)

open import Plasmaduck.SetoidExperiment.SetoidMachinery using (SetoidFunction₂; _←₂_; SetoidFunction; _←_; property-subset-setoid; _which-is-cong₂_; flipSetoidFunction₂)
open import Plasmaduck.Algebra.Group.Defs using (RawGroup; IsGroup; IsAbelianGroup; Group; opposite-is-abelian-group)
open import Plasmaduck.Function.Properties using (Associative; Commutative; LeftIdentity; Identity; LeftDistributive; Distributive; LeftAbsorber; RightAbsorber; Absorber; Congruent₂; module SingleOperator)
open import Plasmaduck.Relation.Defs using (CongruentRel; CongruentProperty)
open import Plasmaduck.Util.Case using (case_of_)

open import Plasmaduck.Algebra.Lattice.Semilattice using (MeetSemilatticeWithExtrema)


module Plasmaduck.Algebra.Ring.Defs where

variable
    α β γ c ℓ : Level

record RawRing (c ℓ : Level) : Set (lsuc c ⊔ lsuc ℓ) where
    field
        S : Setoid c ℓ

    open Setoid S using () renaming (
        reflexive to ≈-reflexive;
        refl to ≈-refl;
        sym to ≈-sym;
        trans to ≈-trans;
        isEquivalence to ≈-isEquivalence
        ) public
    open IsEquivalence (S .Setoid.isEquivalence)

    Carrier : Set c
    Carrier = S .Setoid.Carrier

    field
        +-op : SetoidFunction₂ S S S
        +-inverse : SetoidFunction S S
        zero : Carrier
        *-op : SetoidFunction₂ S S S
        one : Carrier

    open import Relation.Binary.Reasoning.Setoid S

    _≈_ : Rel Carrier ℓ
    _≈_ = S .Setoid._≈_
    infix 6 _≈_

    +-raw-group : RawGroup c ℓ
    +-raw-group = record {
        CarrierSetoid = S;
        op = +-op;
        inverse = +-inverse;
        id = zero
        }
    open RawGroup +-raw-group using () renaming (_∙_ to _+_; ∙-cong to +-cong; inv to -_; inv-cong to neg-cong) public

    _*_ : Carrier → Carrier → Carrier
    _*_ = _←₂_ *-op
    infixl 11 _*_

    *-cong : Congruent₂ _≈_ _≈_ _≈_ _*_
    *-cong = *-op .SetoidFunction₂.respects

    ----------------------------
    --- Some other operators ---
    ----------------------------
    _∸_ : Carrier → Carrier → Carrier
    x ∸ y = x + - y
    infixr 10 _∸_

    ∸-cong : Congruent₂ _≈_ _≈_ _≈_ _∸_
    ∸-cong x₁~x₂ y₁~y₂ = +-op .SetoidFunction₂.respects x₁~x₂ (neg-cong y₁~y₂)

    inject-ℕ : ℕ → Carrier
    inject-ℕ zeroℕ = zero
    inject-ℕ (sucℕ n) = one + inject-ℕ n

    _^_ : Carrier → ℕ → Carrier
    x ^ zeroℕ = one
    x ^ (sucℕ n) = x * (x ^ n)
    infix 12 _^_

    ^-cong : ∀ {x y : Carrier} {n : ℕ} → x ≈ y → x ^ n ≈ y ^ n
    ^-cong {n = zeroℕ} x≈y = S .Setoid.refl
    ^-cong {n = sucℕ n} x≈y = *-cong x≈y (^-cong {n = n} x≈y)

    --- Some properties elements can have ---
    AreSidedInverses : (x y : Carrier) → Set ℓ
    AreSidedInverses x y = x * y ≈ one

    AreInverses : (x y : Carrier) → Set ℓ
    AreInverses x y = AreSidedInverses x y × AreSidedInverses y x

    module _ (x : Carrier) where
        IsZero : Set ℓ
        IsZero = x ≈ zero

        IsNonzero : Set ℓ
        IsNonzero = ¬ (x ≈ zero)

    module _ (x : Carrier) where
        IsLeftZeroDivisor : Set (c ⊔ ℓ)
        IsLeftZeroDivisor = Σ Carrier λ y → IsNonzero y × x * y ≈ zero

        IsRightZeroDivisor : Set (c ⊔ ℓ)
        IsRightZeroDivisor = Σ Carrier λ y → IsNonzero y × y * x ≈ zero

        IsZeroDivisor : Set (c ⊔ ℓ)
        IsZeroDivisor = IsLeftZeroDivisor × IsRightZeroDivisor


        IsNilpotent : Set ℓ
        IsNilpotent = Σ ℕ λ n → x ^ n ≈ zero

        IsIdempotent : Set ℓ
        IsIdempotent = x * x ≈ x

        IsUnit : Set (c ⊔ ℓ)
        IsUnit = Σ Carrier λ y → AreInverses x y

        IsLeftCancellative : Set (c ⊔ ℓ)
        IsLeftCancellative = ∀ y z → x * y ≈ x * z → y ≈ z

        IsRightCancellative : Set (c ⊔ ℓ)
        IsRightCancellative = ∀ y z → y * x ≈ z * x → y ≈ z

        IsCancellative : Set (c ⊔ ℓ)
        IsCancellative = IsLeftCancellative × IsRightCancellative

        data Trivial : Set (c ⊔ ℓ) where
            trivial-zero : IsZero x → Trivial
            trivial-unit : IsUnit → Trivial

        NonTrivial : Set (c ⊔ ℓ)
        NonTrivial = ¬ Trivial

    -- Left divisibility
    -- Note this is \|
    record _∣_ (x y : Carrier) : Set (c ⊔ ℓ) where
        pattern
        constructor divides
        field
            quotient : Carrier
            equality : y ≈ quotient * x

    -- Mutual divisibility.
    -- These elements will be in all the same ideals.
    _∥_ : Rel Carrier (c ⊔ ℓ)
    x ∥ y = x ∣ y × y ∣ x

    -- Two elements being off by a factor of a unit.
    record _~_ (x y : Carrier) : Set (c ⊔ ℓ) where
        field
            u : Carrier
            isUnit : IsUnit u
            equality : x ≈ u * y

    {-
        Some notes on the differences between _∥_ and _~_:

        In a decidable ring (i.e. one where _≈_ is decidable), these are the same relation.
        The weirdness mostly occurs when two elements are zero-divisors.
        (A zero divisor is a number (well a pair of numbers) that are nonzero but multiply to zero.)


    -}

    infix 4 _∣_ _∥_ _~_

    ~-cong : CongruentRel S _~_
    ~-cong {x₁} {x₂} {y₁} {y₂} x₁≈x₂ y₁≈y₂ x₁~y₁ = record {
        u = u;
        isUnit = x₁~y₁ ._~_.isUnit;
        equality = begin
            x₂      ≈⟨ sym x₁≈x₂ ⟩
            x₁      ≈⟨ x₁~y₁ ._~_.equality ⟩
            u * y₁  ≈⟨ *-cong refl y₁≈y₂ ⟩
            u * y₂  ∎
        }
        where
            u = x₁~y₁ ._~_.u

    ∣-cong : CongruentRel S _∣_
    ∣-cong {x₁} {x₂} {y₁} {y₂} x₁≈x₂ y₁≈y₂ (divides m y₁≈m*x₁) = divides m (begin
        y₂      ≈⟨ sym y₁≈y₂ ⟩
        y₁      ≈⟨ y₁≈m*x₁ ⟩
        m * x₁  ≈⟨ *-cong refl x₁≈x₂ ⟩
        m * x₂  ∎)

    ∥-cong : CongruentRel S _∥_
    ∥-cong {x₁} {x₂} {y₁} {y₂} x₁≈x₂ y₁≈y₂ (x₁∣y₁ , y₁∣x₁) = ∣-cong x₁≈x₂ y₁≈y₂ x₁∣y₁ , ∣-cong y₁≈y₂ x₁≈x₂ y₁∣x₁


    module _ (x : Carrier) where
        record Composite : Set (c ⊔ ℓ) where
            pattern
            constructor composite
            field
                i j : Carrier
                i-nonTrivial : NonTrivial i
                j-nonTrivial : NonTrivial j
                factors : x ≈ i * j

        PseudoIrreducible : Set (c ⊔ ℓ)
        PseudoIrreducible = ∀ y z → x ≈ y * z → Trivial y ⊎ Trivial z

        PseudoPrime : Set (c ⊔ ℓ)
        PseudoPrime = ∀ y z → x ∣ y * z → x ∣ y ⊎ x ∣ z
        -- y = m * x or z = m * x
        -- i.e. either y or z flattens, in equation y * z = m * x
        -- i.e. either y is a left unit or z is a right unit?

        Irreducible : Set (c ⊔ ℓ)
        Irreducible = NonTrivial x × PseudoIrreducible

        Prime : Set (c ⊔ ℓ)
        Prime = NonTrivial x × PseudoPrime

        -- PseudoIrreducible⇒PseudoPrime : PseudoIrreducible → PseudoPrime
        -- PseudoIrreducible⇒PseudoPrime irr y z (divides m yz=mx) = {! irr m (y * z)    !}

        -- PseudoPrime⇒PseudoIrreducible : PseudoPrime → PseudoIrreducible
        -- PseudoPrime⇒PseudoIrreducible pseudo-prime y z x≈yz with pseudo-prime y z (divides one (trans (sym x≈yz) {!   sym one-is-*-left-id !}))
        -- ... | inj₁ x∣y@(divides m y≈m*x) = inj₂ (trivial-unit {!   !})
        -- ... | inj₂ x∣z@(divides m z≈m*x) = inj₁ (trivial-unit {!  x∣z !})

        -- -- minimum, x needs to be nonzero
        -- -- if x is a zero divisor, then multiplying by x can be info-reducing
        -- PseudoIrreducible⇒IsCancellative : PseudoIrreducible → IsLeftCancellative x
        -- PseudoIrreducible⇒IsCancellative irr y z xy≈xz = {!   !}

        -- PseudoIrreducible⇒¬Composite : PseudoIrreducible → Composite → ⊥
        -- PseudoIrreducible⇒¬Composite irr (composite i j i-nonTrivial j-nonTrivial x≈ij) with irr i j x≈ij
        -- ... | inj₁ i-trivial = i-nonTrivial i-trivial
        -- ... | inj₂ j-trivial = j-nonTrivial j-trivial

        -- Trivial⇒PseudoIrreducible : IsUnit x → PseudoIrreducible
        -- Trivial⇒PseudoIrreducible (w , xw≈1 , wx≈1) y z x≈yz = inj₁ (inj₂ ((z * w) , ? , ?))




    --------------
    --- Ideals ---
    --------------

    open import Plasmaduck.Relation.Unary Carrier using () renaming (
        Pred to RawIdeal;
        _≐_ to _≈RawIdeal_;
        _⊆_ to _⊆RawIdeal_;
        ⊆-refl to ⊆RawIdeal-refl;
        ⊆-trans to ⊆RawIdeal-trans;
        ⊆-isPartialOrder to ⊆RawIdeal-isPartialOrder
        ) public

    _∈Raw_ : {α : Level} → Carrier → RawIdeal α → Set α
    x ∈Raw I = I x
    infix 5 _∈Raw_

    PrincipalRawIdeal : Carrier → RawIdeal (c ⊔ ℓ)
    PrincipalRawIdeal x = x ∣_

    module _ {α : Level} (I : RawIdeal α) where
        IsDecidableIdeal : Set (c ⊔ α)
        IsDecidableIdeal = ∀ x → Dec (x ∈Raw I)

        IsPrimeIdeal : Set (c ⊔ α)
        IsPrimeIdeal = ∀ x y → x * y ∈Raw I → x ∈Raw I ⊎ y ∈Raw I

        IsPrincipalIdeal : Set (c ⊔ ℓ ⊔ α)
        IsPrincipalIdeal = Σ Carrier λ x → I ≈RawIdeal (PrincipalRawIdeal x)

    RawChain : (α : Level) → Set (c ⊔ lsuc α)
    RawChain α = ℕ → RawIdeal α

    IsAscendingRawIdealChain : RawChain α → Set (c ⊔ α)
    IsAscendingRawIdealChain chain = ∀ i → chain i ⊆RawIdeal chain (sucℕ i)

    record AscendingRawIdealChain (α : Level) : Set (c ⊔ lsuc α) where
        field
            rawChain : RawChain α
            ascending : IsAscendingRawIdealChain rawChain

        ascending-+ : ∀ i j → rawChain i ⊆RawIdeal rawChain (j +ℕ i)
        ascending-+ i zeroℕ = ⊆RawIdeal-refl
        ascending-+ i (sucℕ j) = ⊆RawIdeal-trans (ascending-+ i j) (ascending (j +ℕ i))

        ascending-≤ : ∀ i j → i ≤ℕ j → rawChain i ⊆RawIdeal rawChain j
        ascending-≤ i j i≤j = subst (λ q → rawChain i ⊆RawIdeal rawChain q) (m∸n+n≡m i≤j) (ascending-+ (i) (j ∸ℕ i))

    -- IntegralClosure : RawIdeal α → RawIdeal {!   !}
    -- IntegralClosure I = {!   !}

    -- record PrimeIdeal (α : Level) : Set (c ⊔ ℓ ⊔ lsuc α) where
    --     field
    --         ideal : Ideal α
    --         factors : IsPrimeIdeal ideal

    record IsIdeal {α : Level} (I : RawIdeal α) : Set (c ⊔ ℓ ⊔ α) where
        field
            ideal-cong : CongruentProperty S I
            *-closure : ∀ x y → y ∈Raw I → x * y ∈Raw I
            +-closure : ∀ x y → x ∈Raw I → y ∈Raw I → x + y ∈Raw I

    record Ideal (α : Level) : Set (c ⊔ ℓ ⊔ lsuc α) where
        field
            rawIdeal : RawIdeal α
            isIdeal : IsIdeal rawIdeal
        open IsIdeal isIdeal public

    _∈_ : {α : Level} → Carrier → Ideal α → Set α
    x ∈ I = Ideal.rawIdeal I x
    infix 5 _∈_

    _⊆_ : {α β : Level} → Ideal α → Ideal β → Set (c ⊔ α ⊔ β)
    I ⊆ J = ∀ x → x ∈ I → x ∈ J

    _≐_ : {α β : Level} → Ideal α → Ideal β → Set (c ⊔ α ⊔ β)
    I ≐ J = I ⊆ J × J ⊆ I

    module _ {α : Level} where
        open import Plasmaduck.Relation.GeneralizedSubset (_∈_ {α}) hiding (_⊆_; _≐_) public

    Chain : (α : Level) → Set (c ⊔ ℓ ⊔ lsuc α)
    Chain α = ℕ → Ideal α

    Chain⇒RawChain : (α : Level) → Chain α → RawChain α
    Chain⇒RawChain α chain i = chain i .Ideal.rawIdeal

    IsAscendingIdealChain : Chain α → Set (c ⊔ α)
    IsAscendingIdealChain chain = ∀ i → chain i ⊆ chain (sucℕ i)

    record AscendingIdealChain (α : Level) : Set (c ⊔ ℓ ⊔ lsuc α) where
        field
            chain : Chain α
            ascending : IsAscendingIdealChain chain

        ascending-+ : ∀ i j → chain i ⊆ chain (j +ℕ i)
        ascending-+ i zeroℕ = ⊆RawIdeal-refl
        ascending-+ i (sucℕ j) = ⊆RawIdeal-trans (ascending-+ i j) (ascending (j +ℕ i))

        ascending-≤ : ∀ i j → i ≤ℕ j → chain i ⊆ chain j
        ascending-≤ i j i≤j = subst (λ q → chain i ⊆ chain q) (m∸n+n≡m i≤j) (ascending-+ (i) (j ∸ℕ i))


    -- ≈Ideal-refl : {α : Level} → Reflexive (_≈Ideal_ {α})
    -- ≈Ideal-refl = λ x₁ → (λ z → z) , (λ z → z)

    -- ≈Ideal-sym : {α β : Level} → {x : Ideal α} {y : Ideal β} → x ≈Ideal y → y ≈Ideal x
    -- ≈Ideal-sym = λ z x → z x .proj₂ , z x .proj₁

    -- ≈Ideal-trans : {α β γ : Level} → {i : Ideal α} {j : Ideal β} {k : Ideal γ} → i ≈Ideal j → j ≈Ideal k → i ≈Ideal k
    -- ≈Ideal-trans = λ z z₁ x →
    --     (λ z₂ → z₁ x .proj₁ (z x .proj₁ z₂)) ,
    --     (λ z₂ → z x .proj₂ (z₁ x .proj₂ z₂))

    -- ≈Ideal-isEquivalence : {α : Level} → IsEquivalence (_≈Ideal_ {α} {α})
    -- ≈Ideal-isEquivalence = record {
    --     refl = λ {x} → ≈Ideal-refl {x = x};
    --     sym = λ {x} {y} → ≈Ideal-sym {x = x} {y};
    --     trans = λ {i} {j} {k} → ≈Ideal-trans {i = i} {j} {k}
    --     }

IsIntegralDomain : RawRing c ℓ → Set (c ⊔ ℓ)
IsIntegralDomain R = ∀ x y → IsZero (x * y) → IsZero x ⊎ IsZero y
    where open RawRing R

record IsGCDDomain (R : RawRing c ℓ) : Set (c ⊔ ℓ) where
    open RawRing R
    field
        gcd : Carrier → Carrier → Carrier
        gcd-cong : Congruent₂ _≈_ _≈_ _≈_ gcd

        gcd∣₁ : ∀ x y → gcd x y ∣ x
        gcd∣₂ : ∀ x y → gcd x y ∣ y
        gcd-glb : ∀ {x y z} → x ∣ y → x ∣ z → x ∣ gcd y z

-- Noetherian : (R : RawRing c ℓ) (α : Level) → Set (c ⊔ ℓ ⊔ lsuc α)
-- Noetherian R α = ∀ (chain : AscendingIdealChain α) → Σ ℕ λ i → ∀ j → i ≤ℕ j → chain .AscendingIdealChain.chain j ⊆ chain .AscendingIdealChain.chain i
--     where open RawRing R


record IsRing (rawRing : RawRing c ℓ) : Set (c ⊔ ℓ) where
    open RawRing rawRing

    field
        +-isAbelianGroup : IsAbelianGroup +-raw-group

        one-is-*-id : Identity S _*_ one
        *-assoc : Associative S _*_
        *-+-distributive : Distributive S _*_ _+_

    *-+-left-distributive = *-+-distributive .proj₁
    *-+-right-distributive = *-+-distributive .proj₂
    one-is-*-left-id = one-is-*-id .proj₁
    one-is-*-right-id = one-is-*-id .proj₂

    open IsAbelianGroup +-isAbelianGroup using () renaming (
        abelian to +-comm;
        assoc to +-assoc;
        id-is-left-id to zero-is-+-left-id;
        id-is-right-id to zero-is-+-right-id;
        identity to +-identity;
        inv-is-left-inv to neg-is-+-left-inv;
        inv-is-right-inv to neg-is-+-right-inv;
        inv-is-involution to neg-is-involution;
        inv-distributes to neg-distributes;
        inv-id-is-id to neg-zero-is-zero
        ) public
    -- Note neg-is-+-right-inv proves x ∸ x ≈ zero

    open import Relation.Binary.Reasoning.Setoid S
    open IsEquivalence (S .Setoid.isEquivalence)
    open SingleOperator using (assoc-middle)

    one-unit : IsUnit one
    one-unit = one , one-is-*-left-id , one-is-*-left-id

    zero-zero : IsZero zero
    zero-zero = refl

    *-assoc-middle : ∀ {w x y z} → (w * x) * (y * z) ≈ w * (x * y) * z
    *-assoc-middle = assoc-middle S _*_ *-assoc (inj₂ (*-cong refl))

    +-assoc-middle : ∀ {w x y z} → (w + x) + (y + z) ≈ w + (x + y) + z
    +-assoc-middle = assoc-middle S _+_ +-assoc (inj₂ (+-cong refl))

    unique-inverse : {x₁ x₂ y₁ y₂ : Carrier} → x₁ ≈ x₂ → AreInverses x₁ y₁ → AreInverses x₂ y₂ → y₁ ≈ y₂
    unique-inverse {x₁} {x₂} {y₁} {y₂} x₁≈x₂ (x₁*y₁=1 , y₁*x₁=1) (x₂*y₂=1 , y₂*x₂=1) = begin
        y₁              ≈⟨ sym one-is-*-right-id ⟩
        y₁ * one        ≈⟨ *-cong refl (sym x₂*y₂=1) ⟩
        y₁ * (x₂ * y₂)  ≈⟨ *-assoc ⟩
        (y₁ * x₂) * y₂  ≈⟨ *-cong (*-cong refl (sym x₁≈x₂)) refl ⟩
        (y₁ * x₁) * y₂  ≈⟨ *-cong y₁*x₁=1 refl ⟩
        one * y₂        ≈⟨ one-is-*-left-id ⟩
        y₂              ∎

    -- The group of units of this ring
    S* : Setoid (c ⊔ ℓ) ℓ
    S* = property-subset-setoid S IsUnit

    Carrier* : Set (c ⊔ ℓ)
    Carrier* = S* .Setoid.Carrier

    S*-rawGroup : RawGroup (c ⊔ ℓ) ℓ
    S*-rawGroup = record {
        CarrierSetoid = S*;
        op = record {
            func = λ (x , x⁻¹ , x*x⁻¹=1 , x⁻¹*x=1) (y , y⁻¹ , y*y⁻¹=1 , y⁻¹*y=1) → (x * y , y⁻¹ * x⁻¹ , (begin
                (x * y) * (y⁻¹ * x⁻¹)   ≈⟨ sym *-assoc ⟩
                x * (y * (y⁻¹ * x⁻¹))   ≈⟨ *-cong refl *-assoc ⟩
                x * ((y * y⁻¹) * x⁻¹)   ≈⟨ *-cong refl (*-cong y*y⁻¹=1 refl) ⟩
                x * (one * x⁻¹)         ≈⟨ *-cong refl one-is-*-left-id ⟩
                x * x⁻¹                 ≈⟨ x*x⁻¹=1 ⟩
                one                     ∎
                ) , (begin
                (y⁻¹ * x⁻¹) * (x * y)   ≈⟨ sym *-assoc ⟩
                y⁻¹ * (x⁻¹ * (x * y))   ≈⟨ *-cong refl *-assoc ⟩
                y⁻¹ * ((x⁻¹ * x) * y)   ≈⟨ *-cong refl (*-cong x⁻¹*x=1 refl) ⟩
                y⁻¹ * (one * y)         ≈⟨ *-cong refl one-is-*-left-id ⟩
                y⁻¹ * y                 ≈⟨ y⁻¹*y=1 ⟩
                one                     ∎
                ));
            respects = *-cong
            };
        inverse = record {
            func = λ (x , x⁻¹ , x*x⁻¹=1 , x⁻¹*x=1) → x⁻¹ , x , x⁻¹*x=1 , x*x⁻¹=1;
            respects = λ {(x₁ , x₁⁻¹ , x₁-inv)} {(x₂ , x₂⁻¹ , x₂-inv)} x₁=x₂ → unique-inverse x₁=x₂ x₁-inv x₂-inv
            };
        id = one , one , one-is-*-id .proj₁ , one-is-*-id .proj₁
        }

    S*-isGroup : IsGroup S*-rawGroup
    S*-isGroup = record {
        id-is-left-id = λ {(x , x⁻¹ , x*x⁻¹=1 , x⁻¹*x=1)} → one-is-*-left-id;
        inv-is-left-inv = λ {(x , x⁻¹ , x*x⁻¹=1 , x⁻¹*x=1)} → x⁻¹*x=1;
        assoc = *-assoc
        }

    S*-group : Group (c ⊔ ℓ) ℓ
    S*-group = record {
        rawGroup = S*-rawGroup;
        isGroup = S*-isGroup
        }


    ^-+ℕ-*-distributivity : ∀ (x : Carrier) (m n : ℕ) → x ^ (m +ℕ n) ≈ x ^ m * x ^ n
    ^-+ℕ-*-distributivity x zeroℕ n = sym one-is-*-left-id
    ^-+ℕ-*-distributivity x (sucℕ m) n = begin
        x ^ (sucℕ m +ℕ n)       ≈⟨ refl ⟩
        x * x ^ (m +ℕ n)        ≈⟨ *-cong refl (^-+ℕ-*-distributivity x m n) ⟩
        x * (x ^ m * x ^ n)     ≈⟨ *-assoc ⟩
        (x * x ^ m) * x ^ n     ≈⟨ refl ⟩
        x ^ sucℕ m * x ^ n      ∎

    inverse→left-cancellative : {x y : Carrier} → AreSidedInverses x y → ∀ {v w} → y * v ≈ y * w → v ≈ w
    inverse→left-cancellative {x} {y} x*y=1 {v} {w} y*v=y*w = begin
        v               ≈⟨ sym one-is-*-left-id ⟩
        one * v         ≈⟨ *-cong (sym x*y=1) refl ⟩
        (x * y) * v     ≈⟨ sym *-assoc ⟩
        x * (y * v)     ≈⟨ *-cong refl y*v=y*w ⟩
        x * (y * w)     ≈⟨ *-assoc ⟩
        (x * y) * w     ≈⟨ *-cong x*y=1 refl ⟩
        one * w         ≈⟨ one-is-*-left-id ⟩
        w               ∎

    swap-inverse : {x y : Carrier} → AreInverses x y → AreInverses y x
    swap-inverse {x} {y} (x*y=1 , y*x=1) = y*x=1 , x*y=1


    zero-is-*-left-absorber : LeftAbsorber S _*_ zero
    zero-is-*-left-absorber {x} = begin
        zero * x                        ≈⟨ sym zero-is-+-right-id ⟩
        zero * x + zero                 ≈⟨ +-cong refl (sym neg-is-+-right-inv) ⟩
        zero * x + (one * x ∸ one * x)  ≈⟨ +-assoc ⟩
        (zero * x + one * x) ∸ one * x  ≈⟨ ∸-cong (sym *-+-right-distributive) refl ⟩
        (zero + one) * x ∸ one * x      ≈⟨ ∸-cong (*-cong zero-is-+-left-id refl) refl ⟩
        one * x ∸ one * x               ≈⟨ neg-is-+-right-inv ⟩
        zero                            ∎

    zero-is-*-right-absorber : RightAbsorber S _*_ zero
    zero-is-*-right-absorber {x} = begin
        x * zero                        ≈⟨ sym zero-is-+-right-id ⟩
        x * zero + zero                 ≈⟨ +-cong refl (sym neg-is-+-right-inv) ⟩
        x * zero + (x * one ∸ x * one)  ≈⟨ +-assoc ⟩
        (x * zero + x * one) ∸ x * one  ≈⟨ ∸-cong (sym *-+-left-distributive) refl ⟩
        x * (zero + one) ∸ x * one      ≈⟨ ∸-cong (*-cong refl zero-is-+-left-id) refl ⟩
        x * one ∸ x * one               ≈⟨ neg-is-+-right-inv ⟩
        zero                            ∎

    zero-is-*-absorber : Absorber S _*_ zero
    zero-is-*-absorber = zero-is-*-left-absorber , zero-is-*-right-absorber

    zero-is-*-strong-absorber : ∀ {x y} → IsZero x ⊎ IsZero y → IsZero (x * y)
    zero-is-*-strong-absorber {x} {y} (inj₁ x≈0) = begin
        x * y       ≈⟨ *-cong x≈0 refl ⟩
        zero * y    ≈⟨ zero-is-*-left-absorber ⟩
        zero        ∎
    zero-is-*-strong-absorber {x} {y} (inj₂ y≈0) = begin
        x * y       ≈⟨ *-cong refl y≈0 ⟩
        x * zero    ≈⟨ zero-is-*-right-absorber ⟩
        zero        ∎


    neg-one-*-is-neg : ∀ {x} → (- one) * x ≈ - x
    neg-one-*-is-neg {x} = begin
        (- one) * x                     ≈⟨ sym zero-is-+-right-id ⟩
        (- one) * x + zero              ≈⟨ +-cong refl (sym neg-is-+-right-inv) ⟩
        (- one) * x + (x ∸ x)           ≈⟨ +-assoc ⟩
        ((- one) * x + x) ∸ x           ≈⟨ ∸-cong (+-cong refl (sym one-is-*-left-id)) refl ⟩
        ((- one) * x + one * x) ∸ x     ≈⟨ ∸-cong (sym *-+-right-distributive) refl ⟩
        ((- one + one) * x) ∸ x         ≈⟨ ∸-cong (*-cong neg-is-+-left-inv refl) refl ⟩
        (zero * x) ∸ x                  ≈⟨ ∸-cong zero-is-*-left-absorber refl ⟩
        zero ∸ x                        ≈⟨ zero-is-+-left-id ⟩
        - x                             ∎

    *-sidedInverses : ∀ {x⁻¹ x y⁻¹ y} → AreSidedInverses x⁻¹ x → AreSidedInverses y⁻¹ y → AreSidedInverses (y⁻¹ * x⁻¹) (x * y)
    *-sidedInverses {x⁻¹} {x} {y⁻¹} {y} x⁻¹x=1 y⁻¹y=1 = begin
        (y⁻¹ * x⁻¹) * (x * y)   ≈⟨ *-assoc-middle ⟩
        y⁻¹ * (x⁻¹ * x) * y     ≈⟨ *-cong (*-cong refl x⁻¹x=1) refl ⟩
        y⁻¹ * one * y           ≈⟨ *-cong one-is-*-right-id refl ⟩
        y⁻¹ * y                 ≈⟨ y⁻¹y=1 ⟩
        one                     ∎

    *-unit : ∀ {x y} → IsUnit x → IsUnit y → IsUnit (x * y)
    *-unit {x} {y} (u , xu=1 , ux=1) (v , yv=1 , vy=1) = v * u , *-sidedInverses yv=1 xu=1 , *-sidedInverses ux=1 vy=1

    sidedInverse-idem : ∀ {x y} → AreSidedInverses x y → IsIdempotent (y * x)
    sidedInverse-idem {x} {y} xy=1 = begin
        (y * x) * (y * x)   ≈⟨ *-assoc-middle ⟩
        y * (x * y) * x     ≈⟨ *-cong (*-cong refl xy=1) refl ⟩
        y * one * x         ≈⟨ *-cong one-is-*-right-id refl ⟩
        y * x               ∎

    inject-ℕ-respects-+ : ∀ m n → inject-ℕ (m +ℕ n) ≈ inject-ℕ m + inject-ℕ n
    inject-ℕ-respects-+ zeroℕ n = sym zero-is-+-left-id
    inject-ℕ-respects-+ (sucℕ m) n = begin
        inject-ℕ (sucℕ m +ℕ n)              ≈⟨ refl ⟩
        one + inject-ℕ (m +ℕ n)             ≈⟨ +-cong refl (inject-ℕ-respects-+ m n) ⟩
        one + (inject-ℕ m + inject-ℕ n)     ≈⟨ +-assoc ⟩
        (one + inject-ℕ m) + inject-ℕ n     ≈⟨ refl ⟩
        inject-ℕ (sucℕ m) + inject-ℕ n      ∎

    inject-ℕ-respects-* : ∀ m n → inject-ℕ (m *ℕ n) ≈ inject-ℕ m * inject-ℕ n
    inject-ℕ-respects-* zeroℕ n = sym zero-is-*-left-absorber
    inject-ℕ-respects-* (sucℕ m) n = begin
        inject-ℕ (sucℕ m *ℕ n)                      ≈⟨ refl ⟩
        inject-ℕ (n +ℕ m *ℕ n)                      ≈⟨ inject-ℕ-respects-+ n (m *ℕ n) ⟩
        inject-ℕ n + inject-ℕ (m *ℕ n)              ≈⟨ +-cong refl (inject-ℕ-respects-* m n) ⟩
        inject-ℕ n + inject-ℕ m * inject-ℕ n        ≈⟨ +-cong (sym one-is-*-left-id) refl ⟩
        one * inject-ℕ n + inject-ℕ m * inject-ℕ n  ≈⟨ sym *-+-right-distributive ⟩
        (one + inject-ℕ m) * inject-ℕ n             ≈⟨ refl ⟩
        inject-ℕ (sucℕ m) * inject-ℕ n              ∎

    ∈-neg-closure : {α : Level} (I : Ideal α) → ∀ x → x ∈ I → - x ∈ I
    ∈-neg-closure I x x∈I = Ideal.ideal-cong I neg-one-*-is-neg (Ideal.*-closure I (- one) x x∈I)


    any-nonzero-implies-one-not-zero : ∀ {x} → IsNonzero x → IsNonzero one
    any-nonzero-implies-one-not-zero {x} x≄0 1≈0 = x≄0 (begin
        x           ≈⟨ sym one-is-*-left-id ⟩
        one * x     ≈⟨ *-cong 1≈0 refl ⟩
        zero * x    ≈⟨ zero-is-*-left-absorber ⟩
        zero        ∎)

    LeftZeroDiv[x]∧x∣1⇒⊥ : ∀ {x} → IsLeftZeroDivisor x → x ∣ one → ⊥
    LeftZeroDiv[x]∧x∣1⇒⊥ {x} (y , y-nonZero , xy=0) (divides x⁻¹ 1=x⁻¹x) = y-nonZero (begin
        y               ≈⟨ sym one-is-*-left-id ⟩
        one * y         ≈⟨ *-cong 1=x⁻¹x refl ⟩
        (x⁻¹ * x) * y   ≈⟨ sym *-assoc ⟩
        x⁻¹ * (x * y)   ≈⟨ *-cong refl xy=0 ⟩
        x⁻¹ * zero      ≈⟨ zero-is-*-right-absorber ⟩
        zero            ∎)


    ~-reflexive : _≈_ Relation.Binary.⇒ _~_
    ~-reflexive x≈y = record {
        u = one;
        isUnit = one , one-is-*-left-id , one-is-*-left-id;
        equality = trans x≈y (sym one-is-*-left-id)
        }

    ~-refl : Reflexive _~_
    ~-refl = ~-reflexive refl

    ~-sym : Symmetric _~_
    ~-sym {x} {y} x~y = record {
        u = v;
        isUnit = u , isUnit .proj₂ .proj₂ , isUnit .proj₂ .proj₁;
        equality = begin
            y               ≈⟨ sym one-is-*-left-id ⟩
            one * y         ≈⟨ *-cong (sym (isUnit .proj₂ .proj₂)) refl ⟩
            (v * u) * y     ≈⟨ sym *-assoc ⟩
            v * (u * y)     ≈⟨ *-cong refl (sym equality) ⟩
            v * x           ∎
        }
        where
            open _~_ x~y
            v = isUnit .proj₁

    ~-trans : Transitive _~_
    ~-trans {x} {y} {z} x~y y~z = record {
        u = u * v;
        isUnit = *-unit uIsUnit vIsUnit;
        equality = begin
            x               ≈⟨ xyEquality ⟩
            u * y           ≈⟨ *-cong refl yzEquality ⟩
            u * (v * z)     ≈⟨ *-assoc ⟩
            (u * v) * z     ∎
        }
        where
            open _~_ x~y using (u) renaming (isUnit to uIsUnit; equality to xyEquality)
            open _~_ y~z using () renaming (u to v; isUnit to vIsUnit; equality to yzEquality)

    ~-isEquivalence : IsEquivalence _~_
    ~-isEquivalence = record {
        refl = ~-refl;
        sym = ~-sym;
        trans = ~-trans
        }

    -- Divisibility. Technically, left-divisibility
    ∣-trans : Transitive _∣_
    ∣-trans {i} {j} {k} (divides m j≈m*i) (divides n k≈n*j) = divides (n * m) (begin
        k               ≈⟨ k≈n*j ⟩
        n * j           ≈⟨ *-cong refl j≈m*i ⟩
        n * (m * i)     ≈⟨ *-assoc ⟩
        (n * m) * i     ∎)

    ∣-refl : Reflexive _∣_
    ∣-refl = divides one (sym one-is-*-left-id)

    ∣-reflexive-∥ : _∥_ Relation.Binary.⇒ _∣_
    ∣-reflexive-∥ = proj₁

    ∣-reflexive-~ : _~_ Relation.Binary.⇒ _∣_
    ∣-reflexive-~ x~y = divides (y~x ._~_.u) (y~x ._~_.equality)
        where y~x = ~-sym x~y

    ∣-max : ∀ {x} → x ∣ zero
    ∣-max = divides zero (sym zero-is-*-left-absorber)

    ∣-min : ∀ {x} → one ∣ x
    ∣-min {x} = divides x (sym one-is-*-right-id)

    ∣-unit-divides-all : ∀ {x} → IsUnit x → ∀ {y} → x ∣ y
    ∣-unit-divides-all {x} (x⁻¹ , _ , x⁻¹*x≈1) {y} = divides (y * x⁻¹) (begin
        y               ≈⟨ sym one-is-*-right-id ⟩
        y * one         ≈⟨ *-cong refl (sym x⁻¹*x≈1) ⟩
        y * (x⁻¹ * x)   ≈⟨ *-assoc ⟩
        (y * x⁻¹) * x   ∎)

    ∥-refl : Reflexive _∥_
    ∥-refl = ∣-refl , ∣-refl

    ∥-sym : Symmetric _∥_
    ∥-sym (x∣y , y∣x) = y∣x , x∣y

    ∥-trans : Transitive _∥_
    ∥-trans (i∣j , j∣i) (j∣k , k∣j) = ∣-trans i∣j j∣k , ∣-trans k∣j j∣i

    ∥-isEquivalence : IsEquivalence _∥_
    ∥-isEquivalence = record {
        refl = ∥-refl;
        sym = ∥-sym;
        trans = ∥-trans
        }

    ~⇒∥ : ∀ {x y} → x ~ y → x ∥ y
    ~⇒∥ x~y = ∣-reflexive-~ x~y , ∣-reflexive-~ y~x
        where y~x = ~-sym x~y

    {-
        Mutual divisibility vs off by a unit.

        If off by a unit, then obviously they are mutually divisible.
        If mutually divisibile, then...
        - if x and y do not divide 0, then neither does their factor. That means their factor is a unit, I think?
        - specifically, if x does not divide 0, then multiplication by x is cancellable, I think.
    -}

    -- This holds if x (or y (equivalently and y)) does not divide 0.
    -- It also might hold in general, but consider e.g. matrices of not full rank.
    -- ∥⇒~ : ∀ {x y} → x ∥ y → x ~ y
    -- ∥⇒~ {x} {y} (x∣y@(divides m y=m*x) , y∣x@(divides n x=n*y)) = record {
    --     u = {!   !};
    --     isUnit = {!   !};
    --     equality = {!   !}
    --     }

    -- ∥⇒~ : ∀ {x y} → Dec (IsZero x) → x ∥ y → x ~ y
    -- ∥⇒~ {x} {y} (yes x-zero) (x∣y@(divides m y=m*x) , y∣x) = record {
    --     u = one;
    --     isUnit = one-unit;
    --     equality = begin
    --         x       ≈⟨ x-zero ⟩
    --         zero    ≈⟨ sym y-zero ⟩
    --         y       ≈⟨ sym one-is-*-left-id ⟩
    --         one * y ∎
    --     }
    --     where
    --         y-zero : IsZero y
    --         y-zero = begin
    --             y           ≈⟨ y=m*x ⟩
    --             m * x       ≈⟨ *-cong refl x-zero ⟩
    --             m * zero    ≈⟨ zero-is-*-right-absorber ⟩
    --             zero        ∎
    -- ∥⇒~ (no x-nonZero) (x∣y , y∣x@(divides m x=m*y)) = record {
    --     u = m;
    --     isUnit = {!   !};
    --     equality = x=m*y
    --     }

    -- [∥⇒~]⇒DecZero : (∀ {x y} → x ∥ y → x ~ y) → Dec (zero ≈ one)
    -- [∥⇒~]⇒DecZero find-unit = {! find-unit {zero} {zero} ?  !}

    ∣-antisym : Antisymmetric _∥_ _∣_
    ∣-antisym x∣y y∣x = x∣y , y∣x

    -- This requires us to know if our item is 0 or not, I think
    -- ∣-antisym-~ : Antisymmetric _~_ _∣_

    ∣-isPreorder : IsPreorder _∥_ _∣_
    ∣-isPreorder = record {
        isEquivalence = ∥-isEquivalence;
        reflexive = ∣-reflexive-∥;
        trans = ∣-trans
        }

    ∣-isPartialOrder : IsPartialOrder _∥_ _∣_
    ∣-isPartialOrder = record {
        isPreorder = ∣-isPreorder;
        antisym = ∣-antisym
        }


record Ring (c ℓ : Level) : Set (lsuc c ⊔ lsuc ℓ) where
    field
        rawRing : RawRing c ℓ
        isRing : IsRing rawRing

    open RawRing rawRing public
    open IsRing isRing public

record GCDDomain (c ℓ : Level) : Set (lsuc c ⊔ lsuc ℓ) where
    field
        R : RawRing c ℓ
        isRing : IsRing R
        isGCDDomain : IsGCDDomain R

    open RawRing R public
    open IsRing isRing public
    open IsGCDDomain isGCDDomain public

    gcd-∥-cong : Congruent₂ _∥_ _∥_ _∥_ gcd
    gcd-∥-cong {x₁} {x₂} {y₁} {y₂} (x₁∣x₂ , x₂∣x₁) (y₁∣y₂ , y₂∣y₁) =
        gcd-glb
            (∣-trans (gcd∣₁ x₁ y₁) x₁∣x₂)
            (∣-trans (gcd∣₂ x₁ y₁) y₁∣y₂) ,
        gcd-glb
            (∣-trans (gcd∣₁ x₂ y₂) x₂∣x₁)
            (∣-trans (gcd∣₂ x₂ y₂) y₂∣y₁)

    gcd-semilattice : MeetSemilatticeWithExtrema c (c ⊔ ℓ) (c ⊔ ℓ)
    gcd-semilattice = record {
        semilattice = record {
            rawSemilattice = record {
                A = Carrier;
                _≈_ = _∥_;
                _≤_ = _∣_;
                ≤-isPartialOrder = ∣-isPartialOrder;
                _⊓_ = gcd;
                ⊓-cong = gcd-∥-cong
                };
            isSemilattice = record {
                ⊓≤₁ = gcd∣₁;
                ⊓≤₂ = gcd∣₂;
                ⊓-glb = λ x y z → gcd-glb {x} {y} {z}
                }
            };
        hasMax = record {
            max = zero;
            max≥ = λ x → ∣-max {x}
            };
        hasMin = record {
            min = one;
            min≤ = λ x → ∣-min {x}
            }
        }


---------------------
--- Commutativity ---
---------------------

IsCommutative : (rawRing : RawRing c ℓ) → Set (c ⊔ ℓ)
IsCommutative rawRing = Commutative S _*_
    where open RawRing rawRing

-- Reduced the proofs needed by using commutativity of *
record IsCommutativeRing (rawRing : RawRing c ℓ) : Set (c ⊔ ℓ) where
    open RawRing rawRing
    field
        +-isAbelianGroup : IsAbelianGroup +-raw-group
        one-is-*-left-id : LeftIdentity S _*_ one
        *-assoc : Associative S _*_
        *-+-left-distributive : LeftDistributive S _*_ _+_
        *-comm : IsCommutative rawRing

    open import Relation.Binary.Reasoning.Setoid S
    open IsEquivalence (S .Setoid.isEquivalence)

    isRing : IsRing rawRing
    isRing = record {
        +-isAbelianGroup = +-isAbelianGroup;
        one-is-*-id = one-is-*-left-id , (λ {x} → begin
            x * one     ≈⟨ *-comm ⟩
            one * x     ≈⟨ one-is-*-left-id ⟩
            x           ∎);
        *-assoc = *-assoc;
        *-+-distributive = *-+-left-distributive , λ {x} {y} {z} → begin
            (x + y) * z     ≈⟨ *-comm ⟩
            z * (x + y)     ≈⟨ *-+-left-distributive ⟩
            z * x + z * y   ≈⟨ +-cong *-comm *-comm ⟩
            x * z + y * z   ∎
        }
    open IsRing isRing public hiding (one-is-*-left-id; *-+-left-distributive)

record CommutativeRing (c ℓ : Level) : Set (lsuc c ⊔ lsuc ℓ) where
    field
        rawRing : RawRing c ℓ
        isCommutativeRing : IsCommutativeRing rawRing

    open RawRing rawRing public
    open IsCommutativeRing isCommutativeRing public

    ring : Ring c ℓ
    ring = record {
        rawRing = rawRing;
        isRing = isRing
        }

commuting-ring-is-commutative : (ring : Ring c ℓ) → IsCommutative (ring .Ring.rawRing) → IsCommutativeRing (ring .Ring.rawRing)
commuting-ring-is-commutative ring *-comm = record {
    +-isAbelianGroup = +-isAbelianGroup;
    one-is-*-left-id = one-is-*-left-id;
    *-assoc = *-assoc;
    *-+-left-distributive = *-+-left-distributive;
    *-comm = *-comm
    }
    where open Ring ring

--------------
--- Fields ---
--------------

record IsField (rawRing : RawRing c ℓ) : Set (c ⊔ ℓ) where
    open RawRing rawRing

    private
        -- This will end up being equal to S*, as long as there is at least one nonzero element
        NonzeroS = property-subset-setoid S IsNonzero
        NonzeroCarrier = Σ Carrier IsNonzero

    field
        isRing : IsRing rawRing
        ⁻¹-op' : SetoidFunction NonzeroS S

    open IsRing isRing


    _⁻¹' : NonzeroCarrier → Carrier
    _⁻¹' = ⁻¹-op' ←_

    ⁻¹'-cong = ⁻¹-op' .SetoidFunction.respects

    field
        inv-gives-inverse : ∀ {x : NonzeroCarrier} → AreInverses (x .proj₁) (x ⁻¹')

    open import Relation.Binary.Reasoning.Setoid S
    open IsEquivalence (S .Setoid.isEquivalence)


    inverse-is-not-zero : ∀ {x : NonzeroCarrier} → IsNonzero (x ⁻¹')
    inverse-is-not-zero {x , x≄0} x⁻¹≈0 = any-nonzero-implies-one-not-zero x≄0 (begin
        one                 ≈⟨ sym (inv-gives-inverse {x , x≄0} .proj₁) ⟩
        x * (x , x≄0) ⁻¹'    ≈⟨ *-cong refl x⁻¹≈0 ⟩
        x * zero            ≈⟨ zero-is-*-right-absorber ⟩
        zero                ∎)

    _⁻¹ : NonzeroCarrier → NonzeroCarrier
    _⁻¹ = λ x → ⁻¹-op' ← x , inverse-is-not-zero

    ⁻¹-op : SetoidFunction NonzeroS NonzeroS
    ⁻¹-op = record {
        func = _⁻¹;
        respects = ⁻¹'-cong
        }

    ⁻¹-cong = ⁻¹-op .SetoidFunction.respects

    all-unit : ∀ {x : NonzeroCarrier} → IsUnit (x .proj₁)
    all-unit {x'@(x , x≄0)} = (x' ⁻¹') , inv-gives-inverse


-----------------------
--- Other operators ---
-----------------------

-- I flip the + operator, but since + is commutative, this doesn't really matter
opposite-raw-ring : RawRing c ℓ → RawRing c ℓ
opposite-raw-ring rawRing = record {
    S = S;
    +-op = flipSetoidFunction₂ +-op;
    +-inverse = +-inverse;
    zero = zero;
    *-op = flipSetoidFunction₂ *-op;
    one = one
    }
    where
        open RawRing rawRing

opposite-is-ring : {rawRing : RawRing c ℓ} → IsRing rawRing → IsRing (opposite-raw-ring rawRing)
opposite-is-ring {rawRing = rawRing} isRing =
    record {
        +-isAbelianGroup = opposite-is-abelian-group +-isAbelianGroup;
        one-is-*-id = one-is-*-id .proj₂ , one-is-*-id .proj₁;
        *-assoc = sym *-assoc;
        *-+-distributive = (λ {x} {y} {z} → *-+-distributive .proj₂) , (λ {x} {y} {z} → *-+-distributive .proj₁)
        }
    where
        open RawRing rawRing
        open IsRing isRing
        open Setoid S using (refl; sym; trans)

opposite-ring : Ring c ℓ → Ring c ℓ
opposite-ring ring = record {
    rawRing = opposite-raw-ring rawRing;
    isRing = opposite-is-ring isRing
    }
    where open Ring ring
