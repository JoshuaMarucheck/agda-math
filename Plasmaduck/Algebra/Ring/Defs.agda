open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary using (Setoid; Rel; IsEquivalence)
open import Relation.Nullary using (¬_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Nat using (ℕ) renaming (zero to zero-ℕ; suc to suc-ℕ; _+_ to _+ℕ_)

open import Plasmaduck.SetoidExperiment.SetoidMachinery using (SetoidFunction₂; _which-is-cong₂_; _←₂_; SetoidFunction; _←_; property-subset-setoid)
open import Plasmaduck.Algebra.Group.Defs using (RawGroup; IsGroup; IsAbelianGroup; Group)
open import Plasmaduck.Function.Properties using (Associative; Commutative; Identity; Distributive; LeftAbsorber; RightAbsorber; Absorber; Congruent₂)



module Plasmaduck.Algebra.Ring.Defs where

variable
    a b c ℓ : Level

record RawRing (c ℓ : Level) : Set (lsuc c ⊔ lsuc ℓ) where
    field
        S : Setoid c ℓ

    Carrier : Set c
    Carrier = S .Setoid.Carrier

    field
        +-op : SetoidFunction₂ S S S
        +-inverse : SetoidFunction S S
        zero : Carrier
        *-op : SetoidFunction₂ S S S
        *-inverse : SetoidFunction S S
        one : Carrier

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
    infixr 11 _*_

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
    inject-ℕ zero-ℕ = zero
    inject-ℕ (suc-ℕ n) = one + inject-ℕ n

    _^_ : Carrier → ℕ → Carrier
    x ^ zero-ℕ = one
    x ^ (suc-ℕ n) = x * (x ^ n)
    infix 12 _^_

    ^-cong : ∀ {x y : Carrier} {n : ℕ} → x ≈ y → x ^ n ≈ y ^ n
    ^-cong {n = zero-ℕ} x≈y = S .Setoid.refl
    ^-cong {n = suc-ℕ n} x≈y = *-cong (x≈y) (^-cong {n = n} x≈y)

    --- Some properties elements can have ---
    AreDirectInverses : (x y : Carrier) → Set ℓ
    AreDirectInverses x y = x * y ≈ one

    AreInverses : (x y : Carrier) → Set ℓ
    AreInverses x y = AreDirectInverses x y × AreDirectInverses y x

    module _ (x : Carrier) where
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
        inv-is-left-inv to neg-is-+-left-inv;
        inv-is-right-inv to neg-is-+-right-inv) public
    -- Note neg-is-+-right-inv proves x ∸ x ≈ zero

    open import Relation.Binary.Reasoning.Setoid S
    open IsEquivalence (S .Setoid.isEquivalence)


    unique-inverse : {x₁ x₂ y₁ y₂ : Carrier} → x₁ ≈ x₂ → AreInverses x₁ y₁ → AreInverses x₂ y₂ → y₁ ≈ y₂
    unique-inverse {x₁} {x₂} {y₁} {y₂} x₁≈x₂ (x₁*y₁=1 , y₁*x₁=1) (x₂*y₂=1 , y₂*x₂=1) = begin 
        y₁              ≈⟨ sym one-is-*-right-id ⟩ 
        y₁ * one        ≈⟨ *-cong refl (sym x₂*y₂=1) ⟩ 
        y₁ * (x₂ * y₂)   ≈⟨ *-assoc ⟩ 
        (y₁ * x₂) * y₂   ≈⟨ *-cong (*-cong refl (sym x₁≈x₂)) refl ⟩ 
        (y₁ * x₁) * y₂   ≈⟨ *-cong y₁*x₁=1 refl ⟩ 
        one * y₂        ≈⟨ one-is-*-left-id ⟩ 
        y₂              ∎

    -- The group of units of this ring
    S* : Setoid (c ⊔ ℓ) ℓ
    S* = property-subset-setoid S IsUnit

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
    ^-+ℕ-*-distributivity x zero-ℕ n = sym one-is-*-left-id
    ^-+ℕ-*-distributivity x (suc-ℕ m) n = begin
        x ^ (suc-ℕ m +ℕ n)      ≈⟨ refl ⟩
        x * x ^ (m +ℕ n)        ≈⟨ *-cong refl (^-+ℕ-*-distributivity x m n) ⟩
        x * (x ^ m * x ^ n)     ≈⟨ *-assoc ⟩
        (x * x ^ m) * x ^ n     ≈⟨ refl ⟩
        x ^ suc-ℕ m * x ^ n     ∎


    inverse→left-cancellative : {x y : Carrier} → AreDirectInverses x y → ∀ {v w} → y * v ≈ y * w → v ≈ w
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

IsCommutative : (rawRing : RawRing c ℓ) → Set (c ⊔ ℓ)
IsCommutative rawRing = Commutative S _*_
    where open RawRing rawRing
