open import Level using (Level) renaming (zero to lzero; suc to lsuc)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; cong; cong₂) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open import Relation.Binary using (Setoid; Rel; Decidable; Recomputable; Reflexive; Symmetric; Transitive; IsEquivalence)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (recompute)
open import Function using (Congruent)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _×_; proj₁; proj₂)
open import Data.Bool using (Bool; T; true; false)
open import Data.Integer using (ℤ; 0ℤ; _+_; _-_; _*_; _/_; _%ℕ_; ∣_∣; sign; _◃_; _≟_; NonZero) renaming (-_ to ~_)
open import Data.Integer.Properties using (abs-*; +-assoc; +-comm; +-identity; +-inverse; *-assoc; *-comm; *-identity; *-zero; *-distrib-+; neg-involutive; neg-distrib-+; +-minus-telescope)
open import Data.Integer.Divisibility using () renaming (_∣_ to _∣'_)
open import Data.Integer.DivMod using (a≡a%ℕn+[a/ℕn]*n)

open import Plasmaduck.SetoidExperiment.SetoidMachinery using (discrete-setoid)
open import Plasmaduck.Data.Integer using (+-pos; i+j-j=i; i-j+j=i; -[i*j]=-i*j; i*j*k=i*k*j; foil)
open import Plasmaduck.Data.Integer.Divisibility using (divides; _∣_; ∣'⇒∣; i*j/i=j; i*[j/i]=j; ∣-dec; ∣-recompute; ∣-refl; ∣-trans; i∣j⇒i∣-j)
open import Plasmaduck.Function.Properties using (Congruent₂; exchange-middle)


{-
    Design for the setoid of integers mod m.
-}
module Plasmaduck.Number.IntegerModSetoid (m : ℤ) {{m-nonZero : NonZero m}} where

_≈_ : Rel ℤ lzero
_≈_ x y = m ∣ y - x
infix 4 _≈_

_≈?_ : Decidable _≈_
_≈?_ i j = ∣-dec m (j - i)

≈-recompute : Recomputable _≈_
≈-recompute {i} {j} = recompute (i ≈? j)

refl : Reflexive _≈_
refl {i} = divides 0ℤ (
    i - i   ≡⟨ +-inverse .proj₂ i ⟩
    0ℤ      ≡⟨ *-zero .proj₁ m ⟩
    0ℤ * m  ∎)
    where open ≡-Reasoning

sym : Symmetric _≈_
sym {i} {j} m∣j-i = subst (m ∣_) (
    ~ (j - i)   ≡⟨ neg-distrib-+ j (~ i) ⟩
    ~ j - ~ i   ≡⟨ cong (λ q → ~ j + q) (neg-involutive i) ⟩
    ~ j + i     ≡⟨ +-comm (~ j) i ⟩
    i - j       ∎) (i∣j⇒i∣-j m∣j-i)
    where open ≡-Reasoning

trans : Transitive _≈_
trans {i} {j} {k} m∣j-i@(divides p j-i=p*m) m∣k-j@(divides q k-j=q*m) = divides (q + p) (
    k - i               ≡⟨ ≡-sym (+-minus-telescope k j i) ⟩
    (k - j) + (j - i)   ≡⟨ cong₂ _+_ k-j=q*m j-i=p*m ⟩
    q * m + p * m       ≡⟨ ≡-sym (*-distrib-+ .proj₂ m q p) ⟩
    (q + p) * m         ∎)
    where open ≡-Reasoning

isEquivalence : IsEquivalence _≈_
isEquivalence = record {
    refl = λ {x} → refl {x};
    sym = λ {x} {y} → sym {x} {y};
    trans = λ {x} {y} {z} → trans {x} {y} {z}
    }

i≈jm+i : ∀ i j → i ≈ j * m + i
i≈jm+i i j = divides j (i+j-j=i (j * m) i)

i≈j+i⇒m∣j : ∀ i j → i ≈ j + i → m ∣ j
i≈j+i⇒m∣j i j (divides k j+i-i=k*m) = divides k (≡-trans (≡-sym (i+j-j=i j i)) j+i-i=k*m)

ModSetoid : Setoid lzero lzero
ModSetoid = record {
    Carrier = ℤ;
    _≈_ = _≈_;
    isEquivalence = isEquivalence
    }


------------------------------------------
--- Congruence of a bunch of functions ---
------------------------------------------

neg-cong : Congruent _≈_ _≈_ ~_
neg-cong {i} {j} (divides k j-i=k*m) = divides (~ k) (
    ~ j - ~ i   ≡⟨ ≡-sym (neg-distrib-+ j (~ i)) ⟩
    ~ (j - i)   ≡⟨ cong ~_ j-i=k*m ⟩
    ~ (k * m)   ≡⟨ -[i*j]=-i*j k m ⟩
    ~ k * m     ∎)
    where open ≡-Reasoning

+-cong : Congruent₂ _≈_ _≈_ _≈_ _+_
+-cong {i₁} {i₂} {j₁} {j₂} (divides qᵢ i₂-i₁=qᵢ*m) (divides qⱼ j₂-j₁=qⱼ*m) = divides (qᵢ + qⱼ) (
    (i₂ + j₂) - (i₁ + j₁)       ≡⟨ cong (λ q → (i₂ + j₂) + q) (neg-distrib-+ i₁ j₁) ⟩
    (i₂ + j₂) + (~ i₁ + ~ j₁)   ≡⟨ exchange-middle (discrete-setoid ℤ) _+_ (λ {x} {y} {z} → ≡-sym (+-assoc x y z)) (λ {x} {y} → +-comm x y) (λ { ≡-refl ≡-refl → ≡-refl }) {i₂} {j₂} {~ i₁} {~ j₁} ⟩
    (i₂ - i₁) + (j₂ - j₁)       ≡⟨ cong₂ _+_ i₂-i₁=qᵢ*m j₂-j₁=qⱼ*m ⟩
    qᵢ * m + qⱼ * m             ≡⟨ ≡-sym (*-distrib-+ .proj₂ m qᵢ qⱼ) ⟩
    (qᵢ + qⱼ) * m               ∎)
    where open ≡-Reasoning

minus-cong : Congruent₂ _≈_ _≈_ _≈_ _-_
minus-cong {i} {j} {k} {l} i≈j k≈l = +-cong {i} {j} i≈j (neg-cong {k} {l} k≈l)

{-
    *-cong:
                    i₁       i₂
    --------------------------
    |               |        |
    |               |        |
  j₁|-------------------------
    |               |        |
  j₂|-------------------------

  the target area is the bottom right 3 quadrants.

  Their areas are
  qᵢ*m*j₁ + qᵢ*qⱼ*m^2 + qⱼ*m*i₁

  so divided by m is
  qᵢ*j₁ + qᵢ*qⱼ*m + qⱼ*i₁

-}

*-cong : Congruent₂ _≈_ _≈_ _≈_ _*_
*-cong {i₁} {i₂} {j₁} {j₂} (divides qᵢ i₂-i₁=qᵢ*m) (divides qⱼ j₂-j₁=qⱼ*m) = divides (qᵢ * m * qⱼ + qᵢ * j₁ + i₁ * qⱼ) (
    i₂ * j₂ - i₁ * j₁                                                               ≡⟨ cong (_- i₁ * j₁) (cong₂ _*_ (≡-sym (i-j+j=i i₂ i₁)) (≡-sym (i-j+j=i j₂ j₁))) ⟩
    (i₂ - i₁ + i₁) * (j₂ - j₁ + j₁) - i₁ * j₁                                       ≡⟨ cong (_- i₁ * j₁) (foil (i₂ - i₁) i₁ (j₂ - j₁) j₁) ⟩
    (i₂ - i₁) * (j₂ - j₁) + (i₂ - i₁) * j₁ + i₁ * (j₂ - j₁) + i₁ * j₁ - i₁ * j₁     ≡⟨ i+j-j=i ((i₂ - i₁) * (j₂ - j₁) + (i₂ - i₁) * j₁ + i₁ * (j₂ - j₁)) (i₁ * j₁) ⟩
    (i₂ - i₁) * (j₂ - j₁) + (i₂ - i₁) * j₁ + i₁ * (j₂ - j₁)                         ≡⟨ cong₂ _+_ (cong₂ _+_ (cong₂ _*_ i₂-i₁=qᵢ*m j₂-j₁=qⱼ*m) (cong (_* j₁) i₂-i₁=qᵢ*m)) (cong (i₁ *_) j₂-j₁=qⱼ*m) ⟩
    (qᵢ * m) * (qⱼ * m) + (qᵢ * m) * j₁ + i₁ * (qⱼ * m)                             ≡⟨ cong₂ _+_ (cong₂ _+_ (≡-sym (*-assoc (qᵢ * m) qⱼ m)) (i*j*k=i*k*j qᵢ m j₁)) (≡-sym (*-assoc i₁ qⱼ m)) ⟩
    qᵢ * m * qⱼ * m     + qᵢ * j₁ * m   + i₁ * qⱼ * m                               ≡⟨ cong (_+ i₁ * qⱼ * m) (≡-sym (*-distrib-+ .proj₂ m (qᵢ * m * qⱼ) (qᵢ * j₁))) ⟩
    (qᵢ * m * qⱼ + qᵢ * j₁) * m         + i₁ * qⱼ * m                               ≡⟨ ≡-sym (*-distrib-+ .proj₂ m (qᵢ * m * qⱼ + qᵢ * j₁) (i₁ * qⱼ)) ⟩
    (qᵢ * m * qⱼ + qᵢ * j₁ + i₁ * qⱼ) * m                                           ∎)
    where open ≡-Reasoning
