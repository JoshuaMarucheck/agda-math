open import Relation.Binary.PropositionalEquality using (_≡_; cong; [_]) renaming (sym to ≡-sym)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open import Data.Product using (proj₁)
open import Data.Nat as ℕ using (ℕ; zero)
open import Data.Sign.Base as Sign using (Sign)
import Data.Sign.Properties as SignProperties
open import Data.Integer using (ℤ; 0ℤ; +_; -_; -[1+_]; _+_; _-_; _*_; _/_; _%_; _/ℕ_; _%ℕ_; NonZero; ∣_∣; sign; _◃_)
open import Data.Integer.Properties using (+-assoc; +-comm; +-identity; +-inverse)
open import Data.Integer.DivMod using (a≡a%n+[a/n]*n)



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
