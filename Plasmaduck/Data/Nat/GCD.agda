open import Level using (Level) renaming (zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; cong₂; subst; inspect; [_]) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁)
open import Data.Nat using (ℕ; zero; suc; pred; _*_; _/_; _%_; NonZero; ≢-nonZero; ≢-nonZero⁻¹; _≟_; _≤_; _≥_; _<_; _>_; z≤n; s≤s; s≤s⁻¹)
open import Data.Nat.Properties using (*-assoc; *-comm; *-identity; *-zero; ≤-reflexive; ≤-refl; <-≤-trans; ≤-trans; <-irrefl; *-mono-≤; *-monoˡ-<)
open import Data.Nat.DivMod using (m%n<n; m*n/n≡m; /-congʳ)
open import Data.Nat.Divisibility using (_∣_; divides; n/m≡quotient; *-monoˡ-∣)
open import Algebra.Definitions {A = ℕ} _≡_

open import Plasmaduck.SetoidExperiment.SetoidMachinery using (from-discrete-cong₂; discrete-setoid)
open import Plasmaduck.Data.Empty using (⊥-irr-elim)
open import Plasmaduck.Data.Nat using (sn≠0; n<sn; m*n*o=m*o*n; m<n*m; m=n*o⇒m/n=o; n=spn; *-nonZero; *-distribʳ-%; ≤-recompute)
open import Plasmaduck.Data.Nat.Divisibility using (∣-refl; ∣-combine-%; ∣-mod-%; ∣-isPartialOrder; ∣-min; ∣-max; ∣-max'; ∣-trans; ∣-antisym; ∣⇒≤; 0-divisor)
open import Plasmaduck.Algebra.Lattice.Semilattice using (MeetSemilatticeWithExtrema)
open import Plasmaduck.Relation.Equivalence using (irrelevant-cong)
open import Plasmaduck.Util.Case using (case_of_)
open import Plasmaduck.Function.Properties using (assoc-middle)


module Plasmaduck.Data.Nat.GCD where

variable
    α β : Level

open ≡-Reasoning

-- generally, we let m < n
module GCDHelper where
    gcd-≤-step : (n : ℕ) → {m' o' : ℕ} → suc m' ≤ suc o' → n % suc m' ≤ o'
    gcd-≤-step n {m'} {o'} m≤o = s≤s⁻¹ (<-≤-trans (m%n<n n (suc m')) m≤o)

    gcd-helper : (m n o : ℕ) → .(m≤o : m ≤ o) → ℕ
    gcd-helper zero n o _ = n
    gcd-helper m@(suc m') n (suc o') m≤o = gcd-helper (n % m) m o' (gcd-≤-step n m≤o)

    gcd-helper-third-arg-irr : (m n o p : ℕ) → .(m≤o : m ≤ o) → .(m≤p : m ≤ p) → gcd-helper m n o m≤o ≡ gcd-helper m n p m≤p
    gcd-helper-third-arg-irr zero n o p m≤o m≤p = ≡-refl
    gcd-helper-third-arg-irr m@(suc _) n (suc o') (suc p') m≤o m≤p = gcd-helper-third-arg-irr (n % m) m o' p' (gcd-≤-step n m≤o) (gcd-≤-step n m≤p)

    gcd-helper-div₁ : (m n o : ℕ) → .(m≤o : m ≤ o) → gcd-helper m n o m≤o ∣ m
    gcd-helper-div₂ : (m n o : ℕ) → .(m≤o : m ≤ o) → gcd-helper m n o m≤o ∣ n
    -- I split these two cases from each other so that the factor chosen is symmetric (see gcd-div₁-div₂-comm below)
    -- I chose 1 as the factor of 0 / 0 so that gcd-div₁ and gcd-div₂ are always coprime (see gcd-factors-coprime below)
    gcd-helper-div₁ zero zero o m≤o = ∣-refl
    gcd-helper-div₁ zero (suc n) o m≤o = divides 0 ≡-refl
    gcd-helper-div₁ m@(suc m') n o@(suc o') m≤o = gcd-helper-div₂ (n % m) m o' (s≤s⁻¹ (<-≤-trans (m%n<n n (suc m')) m≤o))
    gcd-helper-div₂ zero n o m≤o = ∣-refl
    gcd-helper-div₂ m@(suc m') n o@(suc o') m≤o = ∣-combine-% m n (gcd-helper (n % m) m o' (gcd-≤-step n m≤o)) (gcd-helper-div₁ (n % m) m o' (gcd-≤-step n m≤o)) (gcd-helper-div₂ (n % m) m o' (gcd-≤-step n m≤o))

    gcd-helper-glb : ∀ (m n o : ℕ) → .(m≤o : m ≤ o) → (p : ℕ) → p ∣ m → p ∣ n → p ∣ gcd-helper m n o m≤o
    gcd-helper-glb zero n o m≤o p o∣zero p∣n = p∣n
    gcd-helper-glb m@(suc m') n o m≤o zero (divides q m=q*0) p∣n = ⊥-elim (sn≠0 m' (≡-trans m=q*0 (*-zero .proj₂ q)))
    gcd-helper-glb m@(suc m') n o@(suc o') m≤o p@(suc _) p∣m p∣n = gcd-helper-glb (n % m) m o' (gcd-≤-step n m≤o) p (∣-mod-% p n m p∣n p∣m) p∣m

    gcd-helper-induction-up :
        (P : ℕ → ℕ → Set α) →
        (∀ (m n : ℕ) .{{_ : NonZero m}} → P (n % m) m → P m n) →
        ∀ (m n o : ℕ) → .(m≤o : m ≤ o) → P 0 (gcd-helper m n o m≤o) →
        P m n
    gcd-helper-induction-up P IH zero n o m≤o P[0,gcd] = P[0,gcd]
    gcd-helper-induction-up P IH m@(suc m') n o@(suc o') m≤o P[0,gcd] = IH m n (gcd-helper-induction-up P IH (n % m) m o' (gcd-≤-step n m≤o) P[0,gcd])

    gcd-helper-induction-down :
        (P : ℕ → ℕ → Set α) →
        (∀ (m n : ℕ) .{{_ : NonZero m}} → P m n → P (n % m) m) →
        ∀ m n → P m n →
        (o : ℕ) → .(m≤o : m ≤ o) → P 0 (gcd-helper m n o m≤o)
    gcd-helper-induction-down P IH zero n P[m,n] o m≤o = P[m,n]
    gcd-helper-induction-down P IH m@(suc m') n P[m,n] o@(suc o') m≤o = gcd-helper-induction-down P IH (n % m) m (IH m n P[m,n]) o' (gcd-≤-step n m≤o)


    *-distribʳ-gcd-helper : ∀ m n o → .(m≤o : m ≤ o) → (k : ℕ) → gcd-helper m n o m≤o * k ≡ gcd-helper (m * k) (n * k) (o * k) (*-mono-≤ {u = k} m≤o ≤-refl)
    *-distribʳ-gcd-helper zero n o m≤o k = ≡-refl
    *-distribʳ-gcd-helper m@(suc m') n o@(suc o') m≤o zero =
        gcd-helper m n o m≤o * zero                                     ≡⟨ *-zero .proj₂ (gcd-helper m n o m≤o) ⟩
        0                                                               ≡⟨⟩
        gcd-helper zero zero (o * zero) z≤n                             ≡⟨ cong (λ q → gcd-helper zero q (o * zero) z≤n)  {zero} {n * zero} (≡-sym (*-zero .proj₂ n)) ⟩
        gcd-helper zero (n * zero) (o * zero) z≤n                       ≡⟨ irrelevant-cong (_≤ o * 0) (λ q q≤o*0 → gcd-helper q (n * zero) (o * zero) q≤o*0) {0} {m * 0} {z≤n} {*-mono-≤ m≤o z≤n} (≡-sym (*-zero .proj₂ m')) ⟩
        gcd-helper (m * zero) (n * zero) (o * zero) (*-mono-≤ m≤o z≤n)  ∎
    *-distribʳ-gcd-helper m@(suc m') n o@(suc o') m≤o k@(suc k') =
        gcd-helper m n o m≤o * k                                                        ≡⟨⟩
        gcd-helper (n % m) m o' (gcd-≤-step n m≤o) * k                                  ≡⟨ *-distribʳ-gcd-helper (n % m) m o' (gcd-≤-step n m≤o) k ⟩
        gcd-helper ((n % m) * k) (m * k) (o' * k) [n%m]*k≤o'*k                          ≡⟨ irrelevant-cong (_≤ o' * k) (λ q q≤o'*k → gcd-helper q (m * k) (o' * k) q≤o'*k) {(n % m) * k} {(n * k) % (m * k)} {[n%m]*k≤o'*k} {[n*k]%[m*k]≤o'*k} (*-distribʳ-% k n m) ⟩
        gcd-helper ((n * k) % (m * k)) (m * k) (o' * k) [n*k]%[m*k]≤o'*k                ≡⟨ gcd-helper-third-arg-irr ((n * k) % (m * k)) (m * k) (o' * k) (pred (o * k)) [n*k]%[m*k]≤o'*k [n*k]%[m*k]≤pred[o*k] ⟩
        gcd-helper ((n * k) % (m * k)) (m * k) (pred (o * k)) [n*k]%[m*k]≤pred[o*k]     ≡⟨⟩
        gcd-helper (m * k) (n * k) (o * k) (*-mono-≤ {u = k} m≤o ≤-refl)                ∎
        where
            instance
                m*k-nonZero : NonZero (m * k)
                m*k-nonZero = *-nonZero m k

                o*k-nonZero : NonZero (o * k)
                o*k-nonZero = *-nonZero o k

            o*k=sp[o*k] : suc (pred (o * k)) ≡ o * k
            o*k=sp[o*k] = n=spn {o * k}

            [n%m]*k≤o'*k : n % m * k ≤ o' * k
            [n%m]*k≤o'*k = *-mono-≤ {u = k} (gcd-≤-step n (≤-recompute m≤o)) ≤-refl

            [n*k]%[m*k]≤o'*k : (n * k) % (m * k) ≤ o' * k
            [n*k]%[m*k]≤o'*k = subst (_≤ o' * k) (*-distribʳ-% k n m) [n%m]*k≤o'*k

            [n*k]%[m*k]≤pred[o*k] : (n * k) % (m * k) ≤ pred (o * k)
            [n*k]%[m*k]≤pred[o*k] = ≤-trans [n*k]%[m*k]≤o'*k (s≤s⁻¹ (*-monoˡ-< k {o'} {o} n<sn))



open GCDHelper
gcd : ℕ → ℕ → ℕ
gcd m n = gcd-helper m n m ≤-refl

gcd-induction-up :
    (P : ℕ → ℕ → Set α) →
    (IH : ∀ (m n : ℕ) .{{_ : NonZero m}} → P (n % m) m → P m n) →
    ∀ (m n : ℕ) → P 0 (gcd m n) →
    P m n
gcd-induction-up P IH m n P[0,gcd] = gcd-helper-induction-up P IH m n m ≤-refl P[0,gcd]

gcd-induction-down :
    (P : ℕ → ℕ → Set α) →
    (IH : ∀ (m n : ℕ) .{{_ : NonZero m}} → P m n → P (n % m) m) →
    ∀ m n → P m n →
    P 0 (gcd m n)
gcd-induction-down P IH m n P[m,n] = gcd-helper-induction-down P IH m n P[m,n] m ≤-refl

-- -- Eucliean algorithm
-- module _ where
--     open import Data.Integer using (ℤ) renaming (+_ to injℤ; _+_ to _+ℤ_; _*_ to _*ℤ_)
--     euc : ℕ → ℕ → ℤ × ℤ
--     euc zero n = injℤ 0 , injℤ 1
--     euc m@(suc m') n = {!   !}

--     euc₁ : ℕ → ℕ → ℤ
--     euc₁ m n = euc m n .proj₁

--     euc₂ : ℕ → ℕ → ℤ
--     euc₂ m n = euc m n .proj₁

--     euclidean-algorithm-proof : (m n : ℕ) → euc₁ m n *ℤ injℤ m +ℤ euc₂ m n *ℤ injℤ n ≡ injℤ (gcd m n)
--     euclidean-algorithm-proof m n = {!   !}

-- private
--     gcd-step : (m n : ℕ) .{{_ : NonZero m}} → gcd m n ≡ gcd (n % m) m
--     gcd-step m@(suc m') n = gcd-helper-third-arg-irr (n % m) m m' (n % m) (gcd-≤-step n ≤-refl) ≤-refl

gcd-∣₁ : ∀ m n → gcd m n ∣ m
gcd-∣₁ m n = gcd-helper-div₁ m n m ≤-refl

gcd-∣₂ : ∀ m n → gcd m n ∣ n
gcd-∣₂ m n = gcd-helper-div₂ m n m ≤-refl

gcd-glb : ∀ m n o → m ∣ n → m ∣ o → m ∣ gcd n o
gcd-glb m n o m∣n m∣o = gcd-helper-glb n o n ≤-refl m m∣n m∣o

gcd-glb' : ∀ {m n o} → m ∣ n → m ∣ o → m ∣ gcd n o
gcd-glb' {m} {n} {o} m∣n m∣o = gcd-glb m n o m∣n m∣o

gcd-semilattice : MeetSemilatticeWithExtrema lzero lzero lzero
gcd-semilattice = record {
    semilattice = record {
        rawSemilattice = record {
            A = ℕ;
            _≤_ = _∣_;
            _⊓_ = gcd;
            ≤-isPartialOrder = ∣-isPartialOrder;
            ⊓-cong = from-discrete-cong₂ (discrete-setoid ℕ) gcd
            };
        isSemilattice = record {
            ⊓≤₁ = gcd-∣₁;
            ⊓≤₂ = gcd-∣₂;
            ⊓-glb = gcd-glb
            }
        };
    hasMax = record {
        max = 0;
        max≥ = ∣-max
        };
    hasMin = record {
        min = 1;
        min≤ = ∣-min
        }
    }

open MeetSemilatticeWithExtrema gcd-semilattice using () renaming (
    ⊓-idem to gcd-idem;
    ⊓-assoc to gcd-assoc;
    ⊓-comm to gcd-comm;
    ⊓-identity to gcd-zero;
    ⊓-zero to gcd-one;
    ⊓-identity-proj₁ to gcd-zero-proj₁;
    ⊓-identity-proj₂ to gcd-zero-proj₂;
    ⊓-selective to gcd-selective
    )

gcd-nonZeroˡ : ∀ m n .{{_ : NonZero m}} → NonZero (gcd m n)
gcd-nonZeroˡ m@(suc m') n = ≢-nonZero λ gcd=0 → sn≠0 m' (∣-max' (subst (_∣ m) gcd=0 (gcd-∣₁ m n)))

gcd-nonZeroʳ : ∀ m n .{{_ : NonZero n}} → NonZero (gcd m n)
gcd-nonZeroʳ m n@(suc n') = ≢-nonZero λ gcd=0 → sn≠0 n' (gcd-zero-proj₂ m n gcd=0)


{-
    These let us not case on if m is zero or not
    since if we want to work with the factor, we can either say

    m = gcd-div₁ m n * gcd m n
    or we can say that the factor is m / gcd m n (if m ≠ 0, and thus gcd m n ≠ 0) or 0 (if m = 0)

    of course, if gcd m n = 0, then m = 0 and gcd-div₁ m n is arbitrary. (It is 1 so that gcd-div₁ 0 0 and gcd-div₂ 0 0 are coprime.)
-}
-- m / gcd m n
gcd-div₁ : ℕ → ℕ → ℕ
gcd-div₁ m n = gcd-∣₁ m n ._∣_.quotient

gcd-div₁=/ : ∀ m n .{{_ : NonZero (gcd m n)}} →
    gcd-div₁ m n ≡ m / gcd m n
gcd-div₁=/ m n = ≡-sym (n/m≡quotient (gcd-∣₁ m n))

-- Dividing out the second argument as much as possible from the first argument
_//_ = gcd-div₁
infixl 7 _//_

m//n*gcd[mn]=m : ∀ m n → m // n * gcd m n ≡ m
m//n*gcd[mn]=m m n = ≡-sym (gcd-∣₁ m n ._∣_.equality)

m*n//n=m : ∀ m n .{{_ : NonZero n}} → m * n // n ≡ m
m*n//n=m m n =
    m * n // n              ≡⟨ gcd-div₁=/ (m * n) n ⟩
    m * n / gcd (m * n) n   ≡⟨ /-congʳ {m = m * n} (gcd-selective .proj₂ (m * n) n (divides m ≡-refl)) ⟩
    m * n / n               ≡⟨ m*n/n≡m m n ⟩
    m                       ∎
    where instance gcd-nonZero = gcd-nonZeroʳ (m * n) n


gcd-div₁-factor : ∀ m n → m ≡ gcd-div₁ m n * gcd m n
gcd-div₁-factor m n = gcd-∣₁ m n ._∣_.equality

-- n / gcd m n
gcd-div₂ : ℕ → ℕ → ℕ
gcd-div₂ m n = gcd-∣₂ m n ._∣_.quotient

gcd-div₂-factor : ∀ m n → n ≡ gcd-div₂ m n * gcd m n
gcd-div₂-factor m n = gcd-∣₂ m n ._∣_.equality

{-
    m = 2 * 2 * 3
    n = 2 * 2 * 2 * 5
    o = 2 * 7
    then gcd m (n * o) = 2 * 2
    gcd m n = 2 * 2
    gcd m o = 2
    gcd-div₁ m n = 3
    gcd-div₂ m n = 2 * 5
    gcd-div₁ m o = 2 * 3
    gcd-div₂ m o = 7


    m = 2 ^ 10000
    n = 2 * 2 * 2 * 5
    o = 2 * 7
    then gcd m (n * o) = 2 ^ 4
    gcd m n = 2^3
    gcd m o = 2
    gcd-div₁ m n = 2 ^ 9997
    gcd-div₂ m n = 5
    gcd-div₁ m o = 2 ^ 9999
    gcd-div₂ m o = 7
    gcd m n o = 2

    so it's upper bounded by m (obviously) and n * o (obviously)



    m = 2 ^ 5 * 3
    n = 2 ^ 6 * 5
    o = 2 ^ 7 * 7
    then gcd m (n * o) = 2 ^ 5
    gcd m n = 2 ^ 5
    gcd m o = 2 ^ 5
    gcd-div₁ m n = 3
    gcd-div₂ m n = 2 * 5
    gcd-div₁ m o = 3
    gcd-div₂ m o = 2^2 * 7
    gcd m n o = 2^5


    m = 2 ^ 7 * 3
    n = 2 ^ 6 * 5
    o = 2 ^ 5 * 7
    then gcd m (n * o) = 2 ^ 7
    gcd m n = 2 ^ 6
    gcd m o = 2 ^ 5
    gcd-div₁ m n = 2 * 3
    gcd-div₂ m n = 5
    gcd-div₁ m o = 2^2 * 3
    gcd-div₂ m o = 7
    gcd m n o = 2^5


    Think of it as a histogram, with each column being a prime factor.
    you stack histograms n and o on each other, and then clip at histogram m.
    consider one column.

    by analogy:
    gcd -> min
    * -> +
    gcd-div₁ i j -> i - min i j = i ∸ j
    ∣ -> ≤
    1 -> 0
    0 -> infinity (in all columns)

    so consider one column


    we're taking
    min m (n + o)
    and trying to split it into smaller functions

    some numbers:

    min m n
    min m o
    min m n o
    m ∸ n
    m ∸ o
    n ∸ m
    o ∸ m


    so it is at most min m n + min m o
    and also at most m

    so it is
    min m (min m n + min m o)
    ... obviously

    ideally no nested min's (rather, no + inside a min)

    ideally it would be an upper-level thing


    if m ≤ o, then it is m
    if m ≤ n, then it is m
    if o ≤ m and n ≤ m, then

    there's no good way to reference the overflow quantity without referring to n + o

    n + o ∸ (n + o ∸ m)

    or
    m ∸ (m ∸ (n + o))
    which I think is just another way to phrase min m (n + o)?

    translated, this is

    gcd m (n * o) = m div (m div (n * o))
    =


    what about another tactic? what if we don't care specificly about the number?

    so we say that
    if k ∣ n * o
    then k ∣ gcd k n * o
    since that's the most of a factor that could be held in n



    if m and n are coprime
    then if gcd (k * m) n = gcd k n
    but more generally

    gcd (k * m) n ∣ gcd k n * gcd m n
-}

*-distribʳ-gcd : _*_ DistributesOverʳ gcd
*-distribʳ-gcd m n o = *-distribʳ-gcd-helper n o n ≤-refl m

*-distribˡ-gcd : _*_ DistributesOverˡ gcd
*-distribˡ-gcd m n o =
    m * gcd n o             ≡⟨ *-comm m (gcd n o) ⟩
    gcd n o * m             ≡⟨ *-distribʳ-gcd m n o ⟩
    gcd (n * m) (o * m)     ≡⟨ cong₂ gcd (*-comm n m) (*-comm o m) ⟩
    gcd (m * n) (m * o)     ∎

{-
    With this, the general strategy for showing that something divides
    a product of gcds is to subsume the products into the gcds, and then use gcd-glb.
    Similarly, you can remove gcds on the left using gcd-∣₁ and gcd-∣₂,
    so generally you want to subsume the *'s into the gcds on the left as well.
-}
*-distrib-gcd : _*_ DistributesOver gcd
*-distrib-gcd = *-distribˡ-gcd , *-distribʳ-gcd

gcd-*-foil : ∀ m n o p → gcd m n * gcd o p ≡ gcd (gcd (m * o) (n * o)) (gcd (m * p) (n * p))
gcd-*-foil m n o p =
    gcd m n * gcd o p ≡⟨ *-distrib-gcd .proj₁ (gcd m n) o p ⟩
    gcd (gcd m n * o) (gcd m n * p) ≡⟨ cong₂ gcd (*-distrib-gcd .proj₂ o m n) (*-distrib-gcd .proj₂ p m n) ⟩
    gcd (gcd (m * o) (n * o)) (gcd (m * p) (n * p)) ∎

gcd-sym : {α : Level} → (P Q : ℕ → Set α) → (∀ m n → P (gcd m n) → Q m) → ∀ m n → P (gcd m n) → Q n
gcd-sym P Q P⇒Q m n P[gcd] = P⇒Q n m (subst P (gcd-comm m n) P[gcd])

gcd-div₂=/ : ∀ m n .{{_ : NonZero n}} → let instance gcd-nonZero = gcd-nonZeroʳ m n in
    gcd-div₂ m n ≡ n / gcd m n
gcd-div₂=/ m n = ≡-sym (n/m≡quotient (gcd-∣₂ m n))
    where instance gcd-nonZero = gcd-nonZeroʳ m n

gcd-div₁-div₂-comm : ∀ m n → gcd-div₁ m n ≡ gcd-div₂ n m
gcd-div₁-div₂-comm zero zero = ≡-refl
gcd-div₁-div₂-comm zero (suc _) = ≡-refl
gcd-div₁-div₂-comm m@(suc m') n =
    gcd-div₁ m n    ≡⟨ gcd-div₁=/ m n ⟩
    m / gcd m n     ≡⟨ /-congʳ {m = m} (gcd-comm m n) ⟩
    m / gcd n m     ≡⟨ ≡-sym (gcd-div₂=/ n m) ⟩
    gcd-div₂ n m    ∎
    where
        instance
            gcd[mn]-nonZero : NonZero (gcd m n)
            gcd[mn]-nonZero = gcd-nonZeroˡ m n

            gcd[nm]-nonZero : NonZero (gcd n m)
            gcd[nm]-nonZero = gcd-nonZeroʳ n m

gcd-div₁-∣ : ∀ m n → gcd-div₁ m n ∣ m
gcd-div₁-∣ m n = divides (gcd m n) (≡-trans (gcd-div₁-factor m n) (*-comm (gcd-div₁ m n) (gcd m n)))

gcd-div₂-∣ : ∀ m n → gcd-div₂ m n ∣ n
gcd-div₂-∣ m n = subst (_∣ n) (gcd-div₁-div₂-comm n m) (gcd-div₁-∣ n m)

gcd-div₁^2=gcd : ∀ m n .{{_ : NonZero m}} → gcd-div₁ m (gcd-div₁ m n) ≡ gcd m n
gcd-div₁^2=gcd m n =
    gcd-div₁ m (gcd-div₁ m n)   ≡⟨ gcd-div₁=/ m (gcd-div₁ m n) ⟩
    m / gcd m (gcd-div₁ m n)    ≡⟨ /-congʳ {m = m} (gcd-selective .proj₂ m (gcd-div₁ m n) (gcd-div₁-∣ m n)) ⟩
    m / gcd-div₁ m n            ≡⟨ m=n*o⇒m/n=o m (gcd-div₁ m n) (gcd m n) (gcd-div₁-factor m n) ⟩
    gcd m n                     ∎
    where
        instance
            gcd-div₁-nonZero : NonZero (gcd-div₁ m n)
            gcd-div₁-nonZero = ≢-nonZero λ q=0 → ≢-nonZero⁻¹ m (
                m                       ≡⟨ gcd-div₁-factor m n ⟩
                gcd-div₁ m n * gcd m n  ≡⟨ cong (_* gcd m n) q=0 ⟩
                0 * gcd m n             ≡⟨⟩
                0                       ∎)

            gcd-gcd-div₁-nonZero : NonZero (gcd m (gcd-div₁ m n))
            gcd-gcd-div₁-nonZero = gcd-nonZeroˡ m (gcd-div₁ m n)


-- gcd-∣-* : ∀ m n o p → gcd m n * gcd o p ∣ gcd (m * o) (n * p)
-- gcd-∣-* m n o p = gcd-glb (gcd m n * gcd o p) (m * o) (n * p)
--     {!   !}
--     {!   !}

gcd-∣-*ˡ : ∀ m n o p → gcd m n ∣ gcd (o * m) (p * n)
gcd-∣-*ˡ m n o p = gcd-glb (gcd m n) (o * m) (p * n)
    (∣-trans (gcd-∣₁ m n) (divides o ≡-refl))
    (∣-trans (gcd-∣₂ m n) (divides p ≡-refl))

gcd-∣-*ʳ : ∀ m n o p → gcd m n ∣ gcd (m * o) (n * p)
gcd-∣-*ʳ m n o p = subst (gcd m n ∣_) {gcd (o * m) (p * n)} {gcd (m * o) (n * p)} (cong₂ gcd (*-comm o m) (*-comm p n)) (gcd-∣-*ˡ m n o p)

{-


gcd (m * o) (n * o)
= gcd m o * gcd n o


gcd m o * gcd n o
= gcd (gcd (m * n) (o * n)) (gcd (m * o) (o * o))
-}
gcd-distribˡ-* : ∀ m n o → gcd (m * n) o ∣ gcd m o * gcd n o
gcd-distribˡ-* m n o = subst (gcd (m * n) o ∣_) (≡-sym (gcd-*-foil m o n o)) (gcd-glb _ (gcd (m * n) (o * n)) (gcd (m * o) (o * o))
    (gcd-glb _ (m * n) (o * n) (gcd-∣₁ (m * n) o) (∣-trans (gcd-∣₂ (m * n) o) (divides n (*-comm o n))))
    (gcd-glb _ (m * o) (o * o) (∣-trans (gcd-∣₂ (m * n) o) (divides m ≡-refl)) (∣-trans (gcd-∣₂ (m * n) o) (divides o ≡-refl))))


---------------
--- Coprime ---
---------------

record GCDCoprime (m n : ℕ) : Set where
    constructor gcdCoprime
    field
        gcd=1 : gcd m n ≡ 1
{-
    n * o = k * m
    but m and n are coprime (gcd m n = 1)

    maybe I do want that gcd-*

    regardless,
-}
-- gcd m n * o ≡ gcd (m * o) (n * o)
gcd-distribʳ-coprime-* : ∀ m n o → GCDCoprime n o → gcd (n * o) m ≡ gcd n m * gcd o m
gcd-distribʳ-coprime-* m n o (gcdCoprime gcd[no]=1) =
    gcd (n * o) m           ≡⟨ cong (gcd (n * o)) (≡-sym (gcd-selective .proj₁ m (m * m) (divides m ≡-refl))) ⟩
    gcd (n * o) (gcd m (m * m))     ≡⟨ ≡-sym (gcd-assoc (n * o) m (m * m)) ⟩
    gcd (gcd (n * o) m) (m * m)     ≡⟨ cong (λ q → gcd (gcd (n * o) q) (m * m)) {m} {gcd (m * o) (n * m)} (
        m                       ≡⟨ ≡-sym (*-identity .proj₁ m) ⟩
        1 * m                   ≡⟨ cong (_* m) (≡-sym gcd[no]=1) ⟩
        gcd n o * m             ≡⟨ *-distrib-gcd .proj₂ m n o ⟩
        gcd (n * m) (o * m)     ≡⟨ gcd-comm (n * m) (o * m) ⟩
        gcd (o * m) (n * m)     ≡⟨ cong (λ q → gcd q (n * m)) (*-comm o m) ⟩
        gcd (m * o) (n * m)     ∎) ⟩
    gcd (gcd (n * o) (gcd (m * o) (n * m))) (m * m)     ≡⟨ ≡-sym (assoc-middle (discrete-setoid ℕ) gcd (λ {i} {j} {o} → ≡-sym (gcd-assoc i j o)) (inj₁ λ { ≡-refl → ≡-refl }) {n * o} {m * o} {n * m} {m * m}) ⟩
    gcd (gcd (n * o) (m * o)) (gcd (n * m) (m * m))     ≡⟨ ≡-sym (gcd-*-foil n m o m) ⟩
    gcd n m * gcd o m       ∎

gcd-distribˡ-coprime-* : ∀ m n o → GCDCoprime n o → gcd m (n * o) ≡ gcd m n * gcd m o
gcd-distribˡ-coprime-* m n o no-coprime =
    gcd m (n * o)       ≡⟨ gcd-comm m (n * o) ⟩
    gcd (n * o) m       ≡⟨ gcd-distribʳ-coprime-* m n o no-coprime ⟩
    gcd n m * gcd o m   ≡⟨ cong₂ _*_ (gcd-comm n m) (gcd-comm o m) ⟩
    gcd m n * gcd m o   ∎



    -- gcd (gcd (m * n) (1 * o)) (o * o)     ≡⟨ {!   !} ⟩
    -- gcd (gcd (m * n) (gcd m n * o)) (o * o)     ≡⟨ {!   !} ⟩
    -- gcd (gcd (m * n) (gcd (m * o) (n * o))) (o * o)     ≡⟨ {!   !} ⟩
    -- ∣-antisym ()
    -- {!  gcd-*-foil m o n o !}
    -- gcd-*-foil m o n o
    -- *-distrib-gcd .proj₂ o m n
-- coprime-* : ∀ m n o → GCDCoprime m o → gcd m n ≡ gcd m (n * o)
-- coprime-* m n o (gcdCoprime gcd[mo]=1) = gcd-induction-up P (λ i j (gcdCoprime gcd[io]=1 , gcd=) → gcdCoprime {! gcd=  !} , coprime-* j i o {!   !}) n m (gcdCoprime (
--     gcd (gcd n m) o     ≡⟨ gcd-assoc n m o ⟩
--     gcd n (gcd m o)     ≡⟨ cong (gcd n) gcd[mo]=1 ⟩
--     gcd n 1             ≡⟨ gcd-one .proj₂ n ⟩
--     1                   ∎) ,
--     ≡-refl) .proj₂
--     where
--         P : ℕ → ℕ → Set
--         P i j = GCDCoprime j o × gcd j i ≡ gcd j (i * o)

coprime-delete : ∀ m n o → GCDCoprime m n → m ∣ n * o → m ∣ o
coprime-delete m zero o (gcdCoprime gcd[mn]=1) _ = divides o (
    o       ≡⟨ ≡-sym(*-identity .proj₂ o) ⟩
    o * 1   ≡⟨ cong (o *_) (≡-sym m=1) ⟩
    o * m   ∎)
    where
        m=1 : m ≡ 1
        m=1 =
            m           ≡⟨ ≡-sym (gcd-zero .proj₂ m) ⟩
            gcd m 0     ≡⟨ gcd[mn]=1 ⟩
            1           ∎
coprime-delete m n@(suc n') o (gcdCoprime gcd[mn]=1) m∣n*o@(divides k n*o=k*m) = {!   !}




gcd-gcd-factor : ∀ m n → gcd (gcd-div₁ m n) (gcd-div₂ m n) * gcd m n ∣ gcd m n
gcd-gcd-factor m n = gcd-glb (gcd (gcd-div₁ m n) (gcd-div₂ m n) * gcd m n) m n
    (subst (gcd (gcd-div₁ m n) (gcd-div₂ m n) * gcd m n ∣_) (≡-sym (gcd-div₁-factor m n)) (*-monoˡ-∣ (gcd m n) (gcd-∣₁ (gcd-div₁ m n) (gcd-div₂ m n))))
    (subst (gcd (gcd-div₁ m n) (gcd-div₂ m n) * gcd m n ∣_) (≡-sym (gcd-div₂-factor m n)) (*-monoˡ-∣ (gcd m n) (gcd-∣₂ (gcd-div₁ m n) (gcd-div₂ m n))))

gcd-factors-coprime : ∀ m n → GCDCoprime (gcd-div₁ m n) (gcd-div₂ m n)
gcd-factors-coprime zero zero = gcdCoprime ≡-refl
gcd-factors-coprime zero (suc n) = gcdCoprime ≡-refl
gcd-factors-coprime m@(suc m') n with gcd (gcd-div₁ m n) (gcd-div₂ m n) ≟ 1
... | yes gcd=1 = gcdCoprime gcd=1
... | no gcd≠1 = ⊥-elim (helper' gcd≠1)
    where
        instance
            gcd-nonZero : NonZero (gcd m n)
            gcd-nonZero = gcd-nonZeroˡ m n

        blob = gcd (gcd-div₁ m n) (gcd-div₂ m n)

        helper : ∀ k → gcd (gcd-div₁ m n) (gcd-div₂ m n) ≡ k → k ≡ 1
        helper zero gcd-gcd-div=0 = ⊥-irr-elim (sn≠0 m' (
            m                       ≡⟨ gcd-div₁-factor m n ⟩
            gcd-div₁ m n * gcd m n  ≡⟨ cong (_* gcd m n) (gcd-zero-proj₁ (gcd-div₁ m n) (gcd-div₂ m n) gcd-gcd-div=0) ⟩
            0 * gcd m n             ≡⟨⟩
            0                       ∎))
        helper (suc zero) _ = ≡-refl
        helper k@(suc (suc k')) gcd-gcd-div=k = ⊥-irr-elim (<-irrefl ≡-refl (<-≤-trans gcd<blob blob≤gcd))
            where
                gcd<blob : gcd m n < blob * gcd m n
                gcd<blob = m<n*m (gcd m n) blob (<-≤-trans (s≤s (s≤s z≤n)) (≤-reflexive (≡-sym gcd-gcd-div=k)))

                blob≤gcd : blob * gcd m n ≤ gcd m n
                blob≤gcd = ∣⇒≤ (gcd-gcd-factor m n)

        helper' : ¬ ¬ (gcd (gcd-div₁ m n) (gcd-div₂ m n) ≡ 1)
        helper' ¬gcd=1 with gcd (gcd-div₁ m n) (gcd-div₂ m n) | inspect (gcd (gcd-div₁ m n)) (gcd-div₂ m n)
        ... | zero | [ eq ] = case helper zero eq of λ ()
        ... | suc zero | [ eq ] = ¬gcd=1 ≡-refl
        ... | suc (suc k) | [ eq ] = case helper (suc (suc k)) eq of λ ()


lcm : ℕ → ℕ → ℕ
lcm zero _ = zero
lcm (suc _) zero = zero
lcm m@(suc m') n@(suc n') = m * n / gcd m n
    where
        instance
            gcd-nonZero : NonZero (gcd m n)
            gcd-nonZero = gcd-nonZeroˡ m n

lcm-decomposition-helper : ∀ m n → ((divides p _) : gcd m n ∣ m) → ((divides q _) : gcd m n ∣ n) → lcm m n ≡ p * q * gcd m n
lcm-decomposition-helper zero zero (divides p _) (divides q _) = ≡-sym (*-zero .proj₂ (p * q))
lcm-decomposition-helper zero n@(suc n') gcd∣m@(divides p _) (divides q _) =
    zero                    ≡⟨⟩
    zero * q * gcd zero n   ≡⟨ cong (λ x → x * q * gcd zero n) (≡-sym (0-divisor gcd∣m)) ⟩
    p * q * gcd zero n      ∎
lcm-decomposition-helper m@(suc m') zero (divides p _) gcd∣n@(divides q _) =
    zero                    ≡⟨⟩
    zero * gcd m zero       ≡⟨ cong (_* gcd m zero) (≡-sym (*-zero .proj₂ p)) ⟩
    p * zero * gcd m zero   ≡⟨ cong (λ x → p * x * gcd m zero) (≡-sym (0-divisor gcd∣n)) ⟩
    p * q * gcd m zero ∎
lcm-decomposition-helper m@(suc m') n@(suc n') (divides p m=p*gcd) (divides q n=q*gcd) =
    m * n / gcd m n                             ≡⟨ cong (_/ gcd m n) (cong₂ _*_ m=p*gcd n=q*gcd) ⟩
    (p * gcd m n) * (q * gcd m n) / gcd m n     ≡⟨ cong (_/ gcd m n) (≡-sym (*-assoc (p * gcd m n) q (gcd m n))) ⟩
    ((p * gcd m n) * q) * gcd m n / gcd m n   ≡⟨  m*n/n≡m (p * gcd m n * q) (gcd m n) ⟩
    p * gcd m n * q                             ≡⟨ m*n*o=m*o*n p (gcd m n) q ⟩
    p * q * gcd m n                             ∎
    where
        instance
            gcd-nonZero : NonZero (gcd m n)
            gcd-nonZero = gcd-nonZeroˡ m n

lcm-decomposition : ∀ m n → lcm m n ≡ gcd-div₁ m n * gcd-div₂ m n * gcd m n
lcm-decomposition m n = lcm-decomposition-helper m n (gcd-∣₁ m n) (gcd-∣₂ m n)

lcm-∣₁ : ∀ m n → m ∣ lcm m n
lcm-∣₁ m n = divides (gcd-div₂ m n) (
    lcm m n                                     ≡⟨ lcm=p*q*gcd ⟩
    gcd-div₁ m n * gcd-div₂ m n * gcd m n       ≡⟨ cong (_* gcd m n) (*-comm (gcd-div₁ m n) (gcd-div₂ m n)) ⟩
    gcd-div₂ m n * gcd-div₁ m n * gcd m n       ≡⟨ *-assoc (gcd-div₂ m n) (gcd-div₁ m n) (gcd m n) ⟩
    gcd-div₂ m n * (gcd-div₁ m n * gcd m n)     ≡⟨ cong (gcd-div₂ m n *_) (≡-sym (_∣_.equality (gcd-∣₁ m n))) ⟩
    gcd-div₂ m n * m                            ∎)
    where lcm=p*q*gcd = lcm-decomposition m n

lcm-∣₂ : ∀ m n → n ∣ lcm m n
lcm-∣₂ m n = divides (gcd-div₁ m n) (
    lcm m n                                     ≡⟨ lcm=p*q*gcd ⟩
    gcd-div₁ m n * gcd-div₂ m n * gcd m n       ≡⟨ *-assoc (gcd-div₁ m n) (gcd-div₂ m n) (gcd m n) ⟩
    gcd-div₁ m n * (gcd-div₂ m n * gcd m n)     ≡⟨ cong (gcd-div₁ m n *_) (≡-sym (_∣_.equality (gcd-∣₂ m n))) ⟩
    gcd-div₁ m n * n                            ∎)
    where lcm=p*q*gcd = lcm-decomposition m n

{-
    m = p * n
    m = q * o

    show gcd n o divides m

    p * n
    p * gcd-div₁ n o * gcd n o

    m =
    q * gcd-div₂ n o * gcd n o

    thus

    p * gcd-div₁ n o = q * gcd-div₂ n o
    or else gcd n o = 0 (and thus n and o = 0)

    but since gcd-div₁ and gcd-div₂ are coprime, all their factors are in the other number
    so p = gcd-div₂
    and q = gcd-div₁

-}
lcm-glb : ∀ m n o → n ∣ m → o ∣ m → lcm n o ∣ m
lcm-glb m zero o n∣m@(divides p m=p*n) o∣m@(divides q m=q*o) = divides 0 (∣-max' n∣m)
lcm-glb m n@(suc n') o n∣m@(divides p m=p*n) o∣m@(divides q m=q*o) = divides {!   !} (
    m               ≡⟨ {!   !} ⟩
    {!   !} * lcm n o ∎)
