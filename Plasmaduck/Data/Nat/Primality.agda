open import Relation.Binary.PropositionalEquality using (_≡_; subst; cong) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Empty using (⊥)
open import Data.Unit using (tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_)
open import Data.Nat using (ℕ; zero; suc; pred; _+_; _*_; _≤_; _≥_; _<_; _>_; _<?_; s≤s⁻¹; _≟_; NonZero; NonTrivial; n>1⇒nonTrivial; nonTrivial⇒nonZero; nonTrivial⇒n>1)
open import Data.Nat.Properties using (*-comm; +-mono-≤; m≤m+n; ≤-reflexive; ≤-refl; ≤-trans; <-trans; <-≤-trans; <-irrefl; n<1⇒n≡0; ≤∧≢⇒<; m<m*n; module ≤-Reasoning)
open import Data.Nat.Divisibility using (_∣_; divides)

open import Plasmaduck.Data.Nat.Divisibility using (∣-dec)
open import Plasmaduck.Data.Nat using (n<sn; n=spn; NonTrivial-divisor; nonTrivial⇒pred-nonZero)
open import Plasmaduck.Util.Case using (case_of_)
open import Plasmaduck.Util.Negation using (¬¬-lift)



module Plasmaduck.Data.Nat.Primality where


module _ (n : ℕ) where
    record Composite : Set where
        field
            i j : ℕ
            {{i-nonTrivial}} : NonTrivial i
            {{j-nonTrivial}} : NonTrivial j
            factors : n ≡ i * j

    -- Definitions of these two taken from ring theory; they should be proof-identical
    Irreducible : Set
    Irreducible = NonTrivial n × ¬ Composite

    Prime : Set
    Prime = NonTrivial n × ∀ x y → n ∣ x * y → n ∣ x ⊎ n ∣ y

    record _HasDivisorLessThan_ (m : ℕ) : Set where
        field
            divisor : ℕ
            {{nonTrivial}} : NonTrivial divisor
            divisor< : divisor < m
            divisor∣ : divisor ∣ n

    _Rough_ : (m : ℕ) → Set
    _Rough_ m = ¬ (_HasDivisorLessThan_ m)

open _HasDivisorLessThan_

_HasDivisorLessThan?_ : ∀ m n → Dec (m HasDivisorLessThan n)
m HasDivisorLessThan? zero = no λ div → case div .divisor< of λ ()
m HasDivisorLessThan? (suc zero) = no λ div → case subst NonTrivial {div .divisor} {0} (n<1⇒n≡0 (div .divisor<)) (div .nonTrivial) of λ ()
m HasDivisorLessThan? (suc (suc zero)) = no λ div → <-irrefl {1} ≡-refl (<-≤-trans (nonTrivial⇒n>1 _ {{div .nonTrivial}}) (s≤s⁻¹ (div .divisor<)))
m HasDivisorLessThan? n@(suc n'@(suc (suc _))) with m HasDivisorLessThan? n' | ∣-dec n' m
... | yes pf | _ = yes (record {
    divisor = pf .divisor;
    divisor< = <-trans (pf .divisor<) n<sn;
    divisor∣ = pf .divisor∣
    })
... | no _ | yes n'∣m = yes (record {
    divisor = n';
    nonTrivial = record { nonTrivial = tt };
    divisor< = n<sn;
    divisor∣ = n'∣m
    })
... | no no-low-divisors | no ¬n'∣m = no λ div → case div .divisor ≟ n' of λ {
    (yes divisor=n') → ¬n'∣m (subst (_∣ m) divisor=n' (div .divisor∣));
    (no divisor≠n') → no-low-divisors (record {
        divisor = div .divisor;
        nonTrivial = div .nonTrivial;
        divisor< = ≤∧≢⇒< (s≤s⁻¹ (div .divisor<)) divisor≠n';
        divisor∣ = div .divisor∣
        })
    }

Composite⇒HasDivisor : ∀ {n} → Composite n → n HasDivisorLessThan n
Composite⇒HasDivisor {n} n-composite = record {
    divisor = i;
    divisor< = subst (i <_) (≡-sym factors) (m<m*n i j (nonTrivial⇒n>1 j));
    divisor∣ = divides j (≡-trans factors (*-comm i j))
    }
    where
        open Composite n-composite
        instance
            i-nonZero : NonZero i
            i-nonZero = nonTrivial⇒nonZero i

HasDivisor⇒Composite : ∀ {n} → n HasDivisorLessThan n → Composite n
HasDivisor⇒Composite {n} n-divisor = record {
    i = i;
    j = j;
    i-nonTrivial = NonTrivial-divisor j i (<-≤-trans (n-divisor .divisor<) (≤-reflexive (≡-trans (n-divisor .divisor∣ ._∣_.equality) (*-comm i j))));
    j-nonTrivial = n-divisor .nonTrivial;
    factors = n-divisor .divisor∣ ._∣_.equality
    }
    where
        i = n-divisor .divisor∣ ._∣_.quotient
        j = n-divisor .divisor

Irreducible⇒Rough : ∀ {n} → Irreducible n → n Rough n
Irreducible⇒Rough {n} n-irreducible n-hasDivisor = n-irreducible .proj₂ (HasDivisor⇒Composite n-hasDivisor)

Irreducible⇒NonTrivial : ∀ {n} → Irreducible n → NonTrivial n
Irreducible⇒NonTrivial = proj₁

Rough⇒Irreducible : ∀ {n} {{_ : NonTrivial n}} → n Rough n → Irreducible n
Rough⇒Irreducible {n} {{n-nonTrivial}} n-rough = n-nonTrivial , λ n-composite → n-rough (Composite⇒HasDivisor n-composite)

Rough? : ∀ n → Dec (n Rough n)
Rough? n with n HasDivisorLessThan? n
... | yes n-divisor = no (¬¬-lift n-divisor)
... | no n-rough = yes n-rough

Irreducible? : ∀ n → Dec (Irreducible n)
Irreducible? n with 1 <? n | n HasDivisorLessThan? n
... | no 1≮n | _ = no λ n-irreducible → 1≮n (nonTrivial⇒n>1 _ {{n-irreducible .proj₁}})
... | yes 1<n | yes n-divisor = no λ n-irreducible → Irreducible⇒Rough n-irreducible n-divisor
... | yes 1<n | no n-rough = yes (Rough⇒Irreducible {n} {{n>1⇒nonTrivial 1<n}} n-rough)


-- Composite≥4 : ∀ n → Composite n → n ≥ 4
-- Composite≥4 n n-composite = begin
--     4                           ≡⟨⟩
--     2 + 2                       ≤⟨ +-mono-≤ {2} {j} {2} {j} (nonTrivial⇒n>1 j) (nonTrivial⇒n>1 j) ⟩
--     j + j                       ≤⟨ +-mono-≤ {j} ≤-refl (m≤m+n j (pred (pred i) * j)) ⟩
--     j + (j + pred (pred i) * j) ≡⟨ cong (j +_) (cong (_* j) {suc (pred (pred i))} {pred i} (≡-sym (n=spn {pred i} {{nonTrivial⇒pred-nonZero i}}))) ⟩
--     j + pred i * j              ≡⟨ cong (_* j) {suc (pred i)} {i} (≡-sym (n=spn {i} )) ⟩
--     i * j                       ≡⟨ ≡-sym n=i*j ⟩
--     n                           ∎
--     where
--         open ≤-Reasoning
--         i = n-composite .Composite.i
--         j = n-composite .Composite.j
--         n=i*j : n ≡ i * j
--         n=i*j = n-composite .Composite.factors

--         instance
--             i-nonZero : NonZero i
--             i-nonZero = nonTrivial⇒nonZero i
--         i<i*j = m<m*n i j (nonTrivial⇒n>1 j)

-- 2-irr : Irreducible 2
-- 2-irr = record { nonTrivial = tt } , λ 2-composite → {! <-irrefl (Composite≥4 2 2-composite)  !}
