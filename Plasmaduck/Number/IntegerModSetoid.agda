open import Level using (Level) renaming (zero to lzero; suc to lsuc)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; cong; cong₂; inspect; [_]) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open import Relation.Binary using (Setoid; Rel; Decidable; Recomputable; Reflexive; Symmetric; Transitive; IsEquivalence)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (recompute)
open import Function using (Congruent; Bijective)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥-elim-irr)
open import Data.Bool using (Bool; T; true; false)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Integer using (ℤ; 0ℤ; _+_; _-_; _⊖_; _*_; _/_; _%_; _%ℕ_; ∣_∣; sign; _◃_; _≟_; NonZero) renaming (-_ to ~_)
open import Data.Integer.Properties using ([+m]-[+n]≡m⊖n; abs-*; pos-+; pos-*; +-assoc; +-comm; +-identity; +-inverse; *-assoc; *-comm; *-identity; *-zero; *-distrib-+; neg-involutive; neg-distrib-+; +-minus-telescope)
open import Data.Integer.Divisibility using () renaming (_∣_ to _∣'_; divides to divides')
open import Data.Integer.DivMod using (a≡a%ℕn+[a/ℕn]*n; a≡a%n+[a/n]*n; n%ℕd<d; n%d<d)

open import Plasmaduck.SetoidExperiment.SetoidMachinery using (discrete-setoid; _which-is-cong_; from-discrete-cong)
open import Plasmaduck.Data.Bool using (form-T-true)
open import Plasmaduck.Data.Integer using (+-pos; ⊖-force-pos; i+j-j=i; i-j+j=i; -[i*j]=-i*j; i*j*k=i*k*j; foil)
open import Plasmaduck.Data.Integer.DivMod using ([i+kd]%d=i%d)
open import Plasmaduck.Data.Integer.Divisibility using (divides; _∣_; ∣'⇒∣; i*j/i=j; i*[j/i]=j; ∣-dec; ∣-recompute; ∣-refl; ∣-trans; i∣j⇒i∣-j)
open import Plasmaduck.Function.Properties using (Congruent₂; exchange-middle)
open import Plasmaduck.Function.InjectionSurjection using (both-inv→bijective)


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

----------------------------------------------
--- Relation between this and NatModSetoid ---
----------------------------------------------

module NatModSetoid where
    open import Data.Nat as ℕ using (ℕ; zero; suc)
    open import Data.Nat.Properties using (<ᵇ⇒<; <-irrefl; ≤-<-trans; ≤-trans; ≤-reflexive; m≤n+m)
    open import Data.Nat.DivMod using (m<n⇒m%n≡m)
    open import Plasmaduck.Data.Nat using (m=n+o⇒m∸o=n)
    open import Plasmaduck.Number.NatModSetoid ∣ m ∣ using (_≲_; _≃_; m%mod≃m; NatModSetoid; ≃⇒≃′)

    toNat : ℤ → ℕ
    toNat i = i % m

    fromNat : ℕ → ℤ
    fromNat = Data.Integer.+_

    toNat-fromNat : ∀ n → toNat (fromNat n) ≃ n
    toNat-fromNat n = m%mod≃m n

    fromNat-toNat : ∀ i → fromNat (toNat i) ≈ i
    fromNat-toNat i = divides (i / m) (
        i - fromNat (toNat i)                       ≡⟨⟩
        i - ℤ.pos (i % m)                           ≡⟨ cong (_- ℤ.pos (i % m)) (a≡a%n+[a/n]*n i m) ⟩
        ℤ.pos (i % m) + i / m * m - ℤ.pos (i % m)   ≡⟨ cong (_- ℤ.pos (i % m)) (+-comm (ℤ.pos (i % m)) (i / m * m)) ⟩
        i / m * m + ℤ.pos (i % m) - ℤ.pos (i % m)   ≡⟨ i+j-j=i (i / m * m) (ℤ.pos (i % m)) ⟩
        i / m * m                                   ∎)
        where open ≡-Reasoning

    toNat-cong : Congruent _≈_ _≃_ toNat
    toNat-cong {i} {j} (divides k j-i=k*m) = cong (ℕ._% ∣ m ∣) (
        toNat i             ≡⟨ ≡-sym ([i+kd]%d=i%d m i k) ⟩
        toNat (i + k * m)   ≡⟨ cong toNat (+-comm i (k * m)) ⟩
        toNat (k * m + i)   ≡⟨ cong toNat (cong (_+ i) (≡-sym j-i=k*m)) ⟩
        toNat (j - i + i)   ≡⟨ cong toNat (i-j+j=i j i) ⟩
        toNat j             ∎)
        where open ≡-Reasoning

    fromNat-thing : Congruent _≲_ _≈_ fromNat
    fromNat-thing {n} {o} (p , o=p*∣m∣+n) = ∣'⇒∣ (divides' p (
        ∣ ℤ.pos o - ℤ.pos n ∣   ≡⟨ cong ∣_∣ ([+m]-[+n]≡m⊖n o n) ⟩
        ∣ o Data.Integer.⊖ n ∣  ≡⟨ ⊖-force-pos o n (≤-trans (m≤n+m n (p ℕ.* ∣ m ∣)) (≤-reflexive (≡-sym o=p*∣m∣+n))) ⟩
        o ℕ.∸ n                 ≡⟨ m=n+o⇒m∸o=n o (p ℕ.* ∣ m ∣) n o=p*∣m∣+n ⟩
        p ℕ.* ∣ m ∣             ∎))
        where open ≡-Reasoning

    fromNat-cong : Congruent _≃_ _≈_ fromNat
    fromNat-cong {n} {o} n≃o with ≃⇒≃′ n≃o
    ... | inj₁ n≲o = fromNat-thing n≲o
    ... | inj₂ o≲n = sym {ℤ.pos o} {ℤ.pos n} (fromNat-thing {o} {n} o≲n)

    fromNat-bijective : Bijective _≃_ _≈_ fromNat
    fromNat-bijective = both-inv→bijective NatModSetoid ModSetoid (fromNat which-is-cong fromNat-cong) ((toNat which-is-cong λ {x} {y} → toNat-cong {x} {y}) , (λ {x} → toNat-fromNat x) , (λ {x} → fromNat-toNat x))


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
