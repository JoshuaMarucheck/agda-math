open import Relation.Binary.PropositionalEquality using (_≡_; cong; inspect; [_]) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open import Data.Product using (proj₁; proj₂)
open import Data.Bool using (true; false)
open import Data.Nat as ℕ using (ℕ; zero; suc; s≤s⁻¹)
open import Data.Sign.Base as Sign using (Sign)
import Data.Sign.Properties as SignProperties
open import Data.Integer using (ℤ; 0ℤ; +_; -_; -[1+_]; _+_; _-_; _*_; _/_; _%_; _/ℕ_; _%ℕ_; NonZero; ∣_∣; sign; _◃_)
open import Data.Integer.Properties using (pos-+; +-assoc; +-comm; +-identity; +-inverse; +-injective; +◃n≡+n; -◃n≡-n; ◃-distrib-+; neg-distrib-+)
open import Data.Integer.DivMod using (a≡a%n+[a/n]*n)

open import Plasmaduck.Data.Bool using (form-T-true)
open import Plasmaduck.Data.Integer using (i-j+j=i; ◃-onto-fst)



module Plasmaduck.Data.Integer.DivMod where

i/j*j=i-i%j : ∀ i j .{{_ : NonZero j}} → i / j * j ≡ i - + (i % j)
i/j*j=i-i%j i j =
    i / j * j                               ≡⟨ ≡-sym (+-identity .proj₁ (i / j * j)) ⟩
    0ℤ + i / j * j                          ≡⟨ cong (_+ i / j * j) (≡-sym (+-inverse .proj₁ (+ (i % j)))) ⟩
    (- + (i % j) + + (i % j)) + i / j * j   ≡⟨ +-assoc (- + (i % j)) (+ (i % j)) (i / j * j) ⟩
    - + (i % j) + (+ (i % j) + i / j * j)   ≡⟨ cong (λ q → - + (i % j) + q) (≡-sym (a≡a%n+[a/n]*n i j)) ⟩
    - + (i % j) + i                         ≡⟨ +-comm (- + (i % j)) i ⟩
    i - + (i % j)                           ∎
    where open ≡-Reasoning

module _ (d : ℕ) .{{_ : ℕ.NonZero d}} where
    open import Data.Nat.DivMod using ([m+kn]%n≡m%n; [m+n]%n≡m%n; n%n≡0; m<n⇒m%n≡m; m%n≤n; m%n%n≡m%n)
    open import Data.Nat.Properties as Nat using (<ᵇ⇒<; ≤-refl; <⇒≤)
    open import Plasmaduck.Data.Nat using (m∸n<m; ¬<ᵇ⇒≥; ∸-suc; [m∸n]%n≡m%n)
    open import Plasmaduck.Number.NatModSetoid d using (∸-partial-cong; minus-is-∸; _≃_; m%mod≃m; minus-cong) renaming (_-_ to _-mod_)
    open ≡-Reasoning

    -1+m%ℕd=nat-thing : ∀ m → -[1+ m ] %ℕ d ≡ (d ℕ.∸ (suc m ℕ.% d)) ℕ.% d
    -1+m%ℕd=nat-thing m with suc m ℕ.% d | inspect (ℕ._% d) (suc m)
    ... | zero | [ eq ] = ≡-sym (n%n≡0 d)
    ... | suc k | [ eq ] = ≡-sym (m<n⇒m%n≡m {d} {d ℕ.∸ suc k} (m∸n<m d (suc k)))

    [i+d]%ℕd=i%ℕd : ∀ i → (i + ℤ.pos d) %ℕ d ≡ i %ℕ d
    [i+d]%ℕd=i%ℕd (+_ n) = [m+n]%n≡m%n n d
    [i+d]%ℕd=i%ℕd (-[1+_] n) with d ℕ.<ᵇ (suc n) | inspect (d ℕ.<ᵇ_) (suc n)
    ... | false | [ ¬d<ᵇsn ] =
        (d ℕ.∸ suc n) ℕ.% d             ≡⟨ ∸-partial-cong {d} {d} {suc n} {suc n ℕ.% d} d>n (m%n≤n (suc n) d) ≡-refl (≡-sym (m%mod≃m (suc n))) ⟩
        (d ℕ.∸ suc n ℕ.% d) ℕ.% d       ≡⟨ ≡-sym (-1+m%ℕd=nat-thing n) ⟩
        -[1+ n ] %ℕ d                   ∎
        where
            d>n : d ℕ.≥ suc n
            d>n = ¬<ᵇ⇒≥ {m = d} {n = suc n} ¬d<ᵇsn
    ... | true | [ d<ᵇsn ] =
        - (+ (suc n ℕ.∸ d)) %ℕ d ≡⟨ cong (λ q → - (+ q) %ℕ d) (≡-sym sk≡s[n-d]) ⟩
        - (+ suc (n ℕ.∸ d)) %ℕ d ≡⟨⟩
        -[1+ (n ℕ.∸ d) ] %ℕ d ≡⟨ -1+m%ℕd=nat-thing (n ℕ.∸ d) ⟩
        (d ℕ.∸ suc (n ℕ.∸ d) ℕ.% d) ℕ.% d ≡⟨ cong (λ q → (d ℕ.∸ q ℕ.% d) ℕ.% d) sk≡s[n-d] ⟩
        (d ℕ.∸ (suc n ℕ.∸ d) ℕ.% d) ℕ.% d ≡⟨ cong (λ q → (d ℕ.∸ q) ℕ.% d) ([m∸n]%n≡m%n (suc n) d (<⇒≤ d<sn)) ⟩
        (d ℕ.∸ suc n ℕ.% d) ℕ.% d   ≡⟨ ≡-sym (-1+m%ℕd=nat-thing n) ⟩
        -[1+ n ] %ℕ d ∎
        where
            d<sn : d ℕ.< suc n
            d<sn = <ᵇ⇒< d (suc n) (form-T-true d<ᵇsn)

            k = n ℕ.∸ d
            sk≡s[n-d] : suc k ≡ suc n ℕ.∸ d
            sk≡s[n-d] = ∸-suc n d (s≤s⁻¹ d<sn)

    [i-d]%ℕd=i%ℕd : ∀ i → (i - ℤ.pos d) %ℕ d ≡ i %ℕ d
    [i-d]%ℕd=i%ℕd i =
        (i - + d) %ℕ d          ≡⟨ ≡-sym ([i+d]%ℕd=i%ℕd (i - + d)) ⟩
        (i - + d + + d) %ℕ d    ≡⟨ cong (_%ℕ d) (i-j+j=i i (+ d)) ⟩
        i %ℕ d                  ∎
        where open ≡-Reasoning

    [i+kd]%ℕd=i%ℕd : ∀ i k → (i + k * ℤ.pos d) %ℕ d ≡ i %ℕ d
    [i+kd]%ℕd=i%ℕd i (+_ zero) = cong (_%ℕ d) (+-identity .proj₂ i)
    [i+kd]%ℕd=i%ℕd i (+_ (suc n)) =
        (i + + suc n * + d) %ℕ d                ≡⟨⟩
        (i + (Sign.+ ◃ suc n ℕ.* d)) %ℕ d       ≡⟨ cong (λ q → (i + q) %ℕ d) (+◃n≡+n (suc n ℕ.* d)) ⟩
        (i + ℤ.pos (suc n ℕ.* d)) %ℕ d          ≡⟨⟩
        (i + (ℤ.pos d + ℤ.pos (n ℕ.* d))) %ℕ d  ≡⟨ cong (λ q → (i + q) %ℕ d) (+-comm (ℤ.pos d) (ℤ.pos (n ℕ.* d))) ⟩
        (i + (ℤ.pos (n ℕ.* d) + ℤ.pos d)) %ℕ d  ≡⟨ cong (_%ℕ d) (≡-sym (+-assoc i (ℤ.pos (n ℕ.* d)) (ℤ.pos d))) ⟩
        (i + ℤ.pos (n ℕ.* d) + ℤ.pos d) %ℕ d    ≡⟨ [i+d]%ℕd=i%ℕd (i + ℤ.pos (n ℕ.* d)) ⟩
        (i + ℤ.pos (n ℕ.* d)) %ℕ d              ≡⟨ cong (λ q → (i + q) %ℕ d) (≡-sym (+◃n≡+n (n ℕ.* d))) ⟩
        (i + (Sign.+ ◃ n ℕ.* d)) %ℕ d           ≡⟨⟩
        (i + + n * + d) %ℕ d                    ≡⟨ [i+kd]%ℕd=i%ℕd i (+ n) ⟩
        i %ℕ d                                  ∎
        where open ≡-Reasoning
    [i+kd]%ℕd=i%ℕd i (-[1+_] zero) =
        (i + -[1+ zero ] * + d) %ℕ d    ≡⟨⟩
        (i + (Sign.- ◃ d ℕ.+ 0)) %ℕ d   ≡⟨ cong (λ q → (i + (Sign.- ◃ q)) %ℕ d) (Nat.+-comm d 0) ⟩
        (i + (Sign.- ◃ d)) %ℕ d         ≡⟨ cong (λ q → (i + q) %ℕ d) (-◃n≡-n d) ⟩
        (i + (- + d)) %ℕ d              ≡⟨⟩
        (i - + d) %ℕ d                  ≡⟨ [i-d]%ℕd=i%ℕd i ⟩
        i %ℕ d                          ∎
        where open ≡-Reasoning
    [i+kd]%ℕd=i%ℕd i (-[1+_] (suc n)) =
        (i + -[1+ suc n ] * + d) %ℕ d               ≡⟨⟩
        (i + (Sign.- ◃ d ℕ.+ suc n ℕ.* d)) %ℕ d     ≡⟨ cong (λ q → (i + q) %ℕ d) (◃-distrib-+ Sign.- d (suc n ℕ.* d)) ⟩
        (i + ((Sign.- ◃ d) + -sn*d)) %ℕ d           ≡⟨ cong (λ q → (i + (q + -sn*d)) %ℕ d) (-◃n≡-n d) ⟩
        (i + (- + d + -sn*d)) %ℕ d                  ≡⟨ cong (λ q → (i + q) %ℕ d) (+-comm (- + d) -sn*d) ⟩
        (i + (-sn*d + - + d)) %ℕ d                  ≡⟨ cong (_%ℕ d) (≡-sym (+-assoc i -sn*d (- + d))) ⟩
        (i + -sn*d + - + d) %ℕ d                    ≡⟨ [i-d]%ℕd=i%ℕd (i + -sn*d) ⟩
        (i + -sn*d) %ℕ d                            ≡⟨⟩
        (i + -[1+ n ] * + d) %ℕ d                   ≡⟨ [i+kd]%ℕd=i%ℕd i -[1+ n ] ⟩
        i %ℕ d                                      ∎
        where
            open ≡-Reasoning
            -sn*d = Sign.- ◃ suc n ℕ.* d

[i+kd]%d=i%d : ∀ d i k .{{_ : NonZero d}} → (i + k * d) % d ≡ i % d
[i+kd]%d=i%d d i k =
    (i + k * d) % d                                     ≡⟨ cong (λ q → (i + q) % d) (◃-onto-fst (sign k Sign.* sign d) ∣ k ∣ ∣ d ∣) ⟩
    (i + (sign k Sign.* sign d ◃ ∣ k ∣) * + ∣ d ∣) % d  ≡⟨ [i+kd]%ℕd=i%ℕd ∣ d ∣ i (sign k Sign.* sign d ◃ ∣ k ∣) ⟩
    i % d ∎
    where open ≡-Reasoning
