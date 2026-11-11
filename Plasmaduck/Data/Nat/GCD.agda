open import Level using (Level) renaming (zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; cong₂; subst; inspect; [_]) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Function using ()
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (ℕ; zero; suc; pred; _*_; _/_; _%_; NonZero; ≢-nonZero; ≢-nonZero⁻¹; >-nonZero; _≟_; _≤_; _≥_; _<_; _>_; z≤n; s≤s; s≤s⁻¹)
open import Data.Nat.Properties using (*-assoc; *-comm; *-identity; *-zero; m*n≡1⇒n≡1; ≤-reflexive; ≤-refl; <-≤-trans; ≤-trans; <-irrefl; *-mono-≤; *-monoˡ-<; *-cancelʳ-≡)
open import Data.Nat.DivMod using (m%n<n; m*n/n≡m; /-congʳ; /-congˡ; n/n≡1; n/1≡n; m/n/o≡m/[n*o]; *-/-assoc)
open import Data.Nat.Divisibility using (_∣_; divides; n/m≡quotient; *-monoˡ-∣; *-monoʳ-∣; m∣m*n; n∣m*n)
open import Algebra.Definitions {A = ℕ} _≡_

open import Plasmaduck.SetoidExperiment.SetoidMachinery using (from-discrete-cong₂; discrete-setoid)
open import Plasmaduck.Data.Empty using (⊥-irr-elim)
open import Plasmaduck.Data.Nat using (sn≠0; n<sn; m*n*o=m*o*n; m<n*m; m=n*o⇒m/n=o; n=spn; *-nonZero; *-distribˡ-%; ≤-recompute; *-factor-nonZero; NonZero-recompute; *-/-exchange)
open import Plasmaduck.Data.Nat.Divisibility using (∣-refl; ∣-reflexive; ∣-combine-%; ∣-mod-%; ∣-isPartialOrder; ∣-min; ∣-max; ∣-max'; ∣-trans; ∣-antisym; ∣⇒≤; 0-divisor; *-mono-∣; module ∣-Reasoning)
open import Plasmaduck.Algebra.Lattice.Semilattice using (MeetSemilatticeWithExtrema)
open import Plasmaduck.Relation.Equivalence using (irrelevant-cong)
open import Plasmaduck.Util.Case using (case_of_)
open import Plasmaduck.Function.Properties using (assoc-middle)



module Plasmaduck.Data.Nat.GCD where

variable
    α β : Level

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
    -- I split these two cases from each other so that the factor chosen is symmetric (see //=//' below)
    -- I chose 1 as the factor of 0 / 0 so that gcd-div₁ and gcd-div₂ are always coprime (see //-coprime below)
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
        where open ≡-Reasoning
    *-distribʳ-gcd-helper m@(suc m') n o@(suc o') m≤o k@(suc k') =
        gcd-helper m n o m≤o * k                                                        ≡⟨⟩
        gcd-helper (n % m) m o' (gcd-≤-step n m≤o) * k                                  ≡⟨ *-distribʳ-gcd-helper (n % m) m o' (gcd-≤-step n m≤o) k ⟩
        gcd-helper ((n % m) * k) (m * k) (o' * k) [n%m]*k≤o'*k                          ≡⟨ irrelevant-cong (_≤ o' * k) (λ q q≤o'*k → gcd-helper q (m * k) (o' * k) q≤o'*k) {(n % m) * k} {(n * k) % (m * k)} {[n%m]*k≤o'*k} {[n*k]%[m*k]≤o'*k} (*-distribˡ-% k n m) ⟩
        gcd-helper ((n * k) % (m * k)) (m * k) (o' * k) [n*k]%[m*k]≤o'*k                ≡⟨ gcd-helper-third-arg-irr ((n * k) % (m * k)) (m * k) (o' * k) (pred (o * k)) [n*k]%[m*k]≤o'*k [n*k]%[m*k]≤pred[o*k] ⟩
        gcd-helper ((n * k) % (m * k)) (m * k) (pred (o * k)) [n*k]%[m*k]≤pred[o*k]     ≡⟨⟩
        gcd-helper (m * k) (n * k) (o * k) (*-mono-≤ {u = k} m≤o ≤-refl)                ∎
        where
            open ≡-Reasoning
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
            [n*k]%[m*k]≤o'*k = subst (_≤ o' * k) (*-distribˡ-% k n m) [n%m]*k≤o'*k

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
-- I wait to define gcd-∣₂ until I've defined _//_ and the semilattice below.
-- That way, both quotients reduce to the same expression (m // n) when given symmetric inputs.

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
            ⊓≤₂ = λ m n → gcd-helper-div₂ m n m ≤-refl;
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
    ⊓-identity to gcd-identity;
    ⊓-zero to gcd-one;
    ⊓-identity-proj₁ to gcd-zero-proj₁;
    ⊓-identity-proj₂ to gcd-zero-proj₂;
    ⊓-selective to gcd-selective;
    max≤ to 0∣n⇒n=0
    ) public

gcd-nonZeroˡ : ∀ m n .{{_ : NonZero m}} → NonZero (gcd m n)
gcd-nonZeroˡ m@(suc m') n = ≢-nonZero λ gcd=0 → sn≠0 m' (∣-max' (subst (_∣ m) gcd=0 (gcd-∣₁ m n)))

gcd-nonZeroʳ : ∀ m n .{{_ : NonZero n}} → NonZero (gcd m n)
gcd-nonZeroʳ m n@(suc n') = ≢-nonZero λ gcd=0 → sn≠0 n' (gcd-zero-proj₂ m n gcd=0)

gcd-nonZero⁻¹ : ∀ m n .{{_ : NonZero (gcd m n)}} → NonZero m ⊎ NonZero n
gcd-nonZero⁻¹ zero (suc n) = inj₂ _
gcd-nonZero⁻¹ (suc m) n = inj₁ _

{-
    Dividing out the second argument as much as possible from the first argument, i.e. m / gcd m n.

    This lets us not case on if m is zero or not
    since if we want to work with the factor, we can either say

    m = m // n * gcd m n
    or we can say that the factor is m / gcd m n (if m ≠ 0, and thus gcd m n ≠ 0) or 0 (if m = 0)

    of course, if gcd m n = 0, then m = 0 and m // n is arbitrary. (It is 1 so that 0 // 0 is coprime with itself; see //-coprime below.)
-}
_//_ : ℕ → ℕ → ℕ
m // n = gcd-∣₁ m n ._∣_.quotient

infixl 8 _//_

//=/gcd : ∀ m n .{{_ : NonZero (gcd m n)}} →
    m // n ≡ m / gcd m n
//=/gcd m n = ≡-sym (n/m≡quotient (gcd-∣₁ m n))

//=/gcd' : ∀ m n .{{_ : NonZero (gcd n m)}} →
    m // n ≡ m / gcd n m
//=/gcd' m n {{gcd[nm]-nonZero}} = ≡-trans (//=/gcd m n) (/-congʳ {m = m} (gcd-comm m n))
    where
        instance
            gcd[mn]-nonZero : NonZero (gcd m n)
            gcd[mn]-nonZero = NonZero-recompute (subst NonZero (gcd-comm n m) gcd[nm]-nonZero)

//-factor : ∀ m n → m ≡ m // n * gcd m n
//-factor m n = gcd-∣₁ m n ._∣_.equality

//-factor' : ∀ m n → n ≡ n // m * gcd m n
//-factor' m n = ≡-trans (//-factor n m) (cong (n // m *_) (gcd-comm n m))

gcd-∣₂ : ∀ m n → gcd m n ∣ n
gcd-∣₂ m n = divides (n // m) (//-factor' m n)

∣⇒gcd=id₁ : ∀ {m n} → m ∣ n → gcd m n ≡ m
∣⇒gcd=id₁ {m} {n} m∣n = gcd-selective .proj₁ m n m∣n

∣⇒gcd=id₂ : ∀ {m n} → n ∣ m → gcd m n ≡ n
∣⇒gcd=id₂ {m} {n} n∣m = gcd-selective .proj₂ m n n∣m

gcd=id₁⇒∣ : ∀ m n → gcd m n ≡ m → m ∣ n
gcd=id₁⇒∣ m n gcd= = subst (_∣ n) gcd= (gcd-∣₂ m n)

gcd=id₂⇒∣ : ∀ m n → gcd m n ≡ n → n ∣ m
gcd=id₂⇒∣ m n gcd= = subst (_∣ m) gcd= (gcd-∣₁ m n)

m*n//n=m : ∀ m n .{{_ : NonZero n}} → (m * n) // n ≡ m
m*n//n=m m n =
    (m * n) // n            ≡⟨ //=/gcd (m * n) n ⟩
    m * n / gcd (m * n) n   ≡⟨ /-congʳ {m = m * n} (∣⇒gcd=id₂ (divides m ≡-refl)) ⟩
    m * n / n               ≡⟨ m*n/n≡m m n ⟩
    m                       ∎
    where
        open ≡-Reasoning
        instance gcd-nonZero = gcd-nonZeroʳ (m * n) n

m//n*n=m : ∀ m n → n ∣ m → m // n * n ≡ m
m//n*n=m m n n∣m =
    m // n * n          ≡⟨ cong (m // n *_) (≡-sym (∣⇒gcd=id₂ n∣m)) ⟩
    m // n * gcd m n    ≡⟨ ≡-sym (//-factor m n) ⟩
    m                   ∎
    where open ≡-Reasoning

gcd≤₁ : ∀ m n .{{_ : NonZero m}} → gcd m n ≤ m
gcd≤₁ m n = ∣⇒≤ (gcd-∣₁ m n)

gcd≤₂ : ∀ m n .{{_ : NonZero n}} → gcd m n ≤ n
gcd≤₂ m n = ∣⇒≤ (gcd-∣₂ m n)

//gcd₂ : ∀ m n o → m ∣ n → m // gcd n o ≡ m // o
//gcd₂ zero n o m∣n =
    zero // gcd n o     ≡⟨ cong (λ q → zero // gcd q o) (0∣n⇒n=0 n m∣n) ⟩
    zero // gcd 0 o     ≡⟨ cong (zero //_) (gcd-identity .proj₁ o) ⟩
    zero // o           ∎
    where open ≡-Reasoning
//gcd₂ m@(suc m') n o m∣n =
    m // gcd n o            ≡⟨ //=/gcd m (gcd n o) ⟩
    m / gcd m (gcd n o)     ≡⟨ /-congʳ {gcd m (gcd n o)} {gcd m o} {m} gcd[m,gcd[no]]=gcd[mo] ⟩
    m / gcd m o             ≡⟨ ≡-sym (//=/gcd m o) ⟩
    m // o ∎
    where
        open ≡-Reasoning

        gcd[m,gcd[no]]=gcd[mo] : gcd m (gcd n o) ≡ gcd m o
        gcd[m,gcd[no]]=gcd[mo] =
            gcd m (gcd n o)     ≡⟨ ≡-sym (gcd-assoc m n o) ⟩
            gcd (gcd m n) o     ≡⟨ cong (λ q → gcd q o) {gcd m n} {m} (∣⇒gcd=id₁ m∣n) ⟩
            gcd m o             ∎

        instance
            gcd[mo]-nonZero : NonZero (gcd m o)
            gcd[mo]-nonZero = gcd-nonZeroˡ m o

            gcd[m,gcd[no]]-nonZero : NonZero (gcd m (gcd n o))
            gcd[m,gcd[no]]-nonZero = gcd-nonZeroˡ m (gcd n o)

//gcd₁ : ∀ m n o → m ∣ o → m // gcd n o ≡ m // n
//gcd₁ m n o m∣o = ≡-trans (cong (m //_) (gcd-comm n o)) (//gcd₂ m o n m∣o)

//=//gcd : ∀ m n → m // n ≡ m // gcd m n
//=//gcd m n = ≡-sym (//gcd₂ m m n ∣-refl)

//=//gcd' : ∀ m n → m // n ≡ m // gcd n m
//=//gcd' m n = ≡-sym (//gcd₁ m n m ∣-refl)

n∣m⇒m//n=m/n : ∀ {m n} .{{_ : NonZero n}} → n ∣ m → m // n ≡ m / n
n∣m⇒m//n=m/n {m} {n} n∣m =
    m // n          ≡⟨ //=/gcd m n ⟩
    m / gcd m n     ≡⟨ /-congʳ {m = m} (∣⇒gcd=id₂ n∣m) ⟩
    m / n           ∎
    where
        open ≡-Reasoning
        instance
            gcd[mn]-nonZero : NonZero (gcd m n)
            gcd[mn]-nonZero = gcd-nonZeroʳ m n

m∣n⇒m//n=1 : ∀ {m n} → m ∣ n → m // n ≡ 1
m∣n⇒m//n=1 {zero} {n} m∣n =
    0 // n          ≡⟨ cong (0 //_) {n} {0} (∣-max' {n} m∣n) ⟩
    0 // 0          ≡⟨⟩
    1               ∎
    where open ≡-Reasoning
m∣n⇒m//n=1 m@{suc m'} {n} m∣n =
    m // n          ≡⟨ //=/gcd m n ⟩
    m / gcd m n     ≡⟨ /-congʳ {m = m} (∣⇒gcd=id₁ m∣n) ⟩
    m / m           ≡⟨ n/n≡1 m ⟩
    1               ∎
    where
        open ≡-Reasoning
        instance
            gcd[mn]-nonZero : NonZero (gcd m n)
            gcd[mn]-nonZero = gcd-nonZeroˡ m n

//0=1 : ∀ m → m // 0 ≡ 1
//0=1 m = m∣n⇒m//n=1 (∣-max m)

n//n=1 : ∀ n → n // n ≡ 1
n//n=1 n = m∣n⇒m//n=1 {n} ∣-refl

1//n=1 : ∀ n → 1 // n ≡ 1
1//n=1 n = m∣n⇒m//n=1 {1} {n} (∣-min n)

0//=0 : ∀ m .{{_ : NonZero m}} → 0 // m ≡ 0
0//=0 (suc _) = ≡-refl

//-nonZero : ∀ m n .{{_ : NonZero m}} → NonZero (m // n)
//-nonZero m@(suc m') n {{m-nonZero}} = *-factor-nonZero .proj₁ (m // n) (gcd m n) {{subst NonZero (//-factor m n) m-nonZero}}

-- Apparently the expression on the right is equal to lcm m n
m∣m//n*n : ∀ m n → m ∣ m // n * n
m∣m//n*n zero n@(suc n') = divides 0 ≡-refl
m∣m//n*n zero zero = ∣-refl
m∣m//n*n m@(suc m') n = divides (n // m) (
    m // n * n ≡⟨ cong (m // n *_) (//-factor' m n) ⟩
    m // n * (n // m * gcd m n) ≡⟨ cong (m // n *_) (*-comm (n // m) (gcd m n)) ⟩
    m // n * (gcd m n * n // m) ≡⟨ ≡-sym (*-assoc (m // n) (gcd m n) (n // m)) ⟩
    (m // n * gcd m n) * n // m ≡⟨ cong (_* n // m) (≡-sym (//-factor m n)) ⟩
    m * n // m                  ≡⟨ *-comm m (n // m) ⟩
    n // m * m ∎)
    where
        open ≡-Reasoning
        instance
            gcd[mn]-nonZero : NonZero (gcd m n)
            gcd[mn]-nonZero = gcd-nonZeroˡ m n

private
    module Div₂ where
        -- Alternate representation of _//_; see //=//' below
        _//'_ : ℕ → ℕ → ℕ
        m //' n = (gcd-helper-div₂ n m n ≤-refl) ._∣_.quotient
        infixl 8 _//'_

        gcd-div₂-factor : ∀ m n → n ≡ n //' m * gcd m n
        gcd-div₂-factor m n = gcd-helper-div₂ m n m ≤-refl ._∣_.equality

        //'=/gcd : ∀ m n .{{_ : NonZero n}} → let instance gcd-nonZero = gcd-nonZeroʳ m n in
            n //' m ≡ n / gcd m n
        //'=/gcd m n = ≡-sym (n/m≡quotient (gcd-helper-div₂ m n m ≤-refl))
            where instance gcd-nonZero = gcd-nonZeroʳ m n

        -- and with this, we discourage the use of _//'_
        //=//' : ∀ m n → m // n ≡ m //' n
        //=//' zero zero = ≡-refl
        //=//' zero (suc _) = ≡-refl
        //=//' m@(suc m') n =
            m // n          ≡⟨ //=/gcd m n ⟩
            m / gcd m n     ≡⟨ /-congʳ {m = m} (gcd-comm m n) ⟩
            m / gcd n m     ≡⟨ ≡-sym (//'=/gcd n m) ⟩
            m //' n         ∎
            where
                open ≡-Reasoning
                instance
                    gcd[mn]-nonZero : NonZero (gcd m n)
                    gcd[mn]-nonZero = gcd-nonZeroˡ m n

                    gcd[nm]-nonZero : NonZero (gcd n m)
                    gcd[nm]-nonZero = gcd-nonZeroʳ n m
open Div₂ using () renaming (//=//' to gcd-∣-swap)

*-distribʳ-gcd : _*_ DistributesOverʳ gcd
*-distribʳ-gcd m n o = *-distribʳ-gcd-helper n o n ≤-refl m

*-distribˡ-gcd : _*_ DistributesOverˡ gcd
*-distribˡ-gcd m n o =
    m * gcd n o             ≡⟨ *-comm m (gcd n o) ⟩
    gcd n o * m             ≡⟨ *-distribʳ-gcd m n o ⟩
    gcd (n * m) (o * m)     ≡⟨ cong₂ gcd (*-comm n m) (*-comm o m) ⟩
    gcd (m * n) (m * o)     ∎
    where open ≡-Reasoning

{-
    With this, the general strategy for showing that something divides
    a product of gcds is to subsume the products into the gcds, and then use gcd-glb.
    Similarly, you can remove gcds on the left using gcd-∣₁ and gcd-∣₂,
    so generally you want to subsume the *'s into the gcds on the left as well.
    (And due to ∣-antisym, you can use this strategy to show equalities as well.)
-}
*-distrib-gcd : _*_ DistributesOver gcd
*-distrib-gcd = *-distribˡ-gcd , *-distribʳ-gcd

-- Tight on valid inputs, due to inverse proof ∣//⇒*∣
-- However, if n and o are zero, we have 0 ∣ 0, so this reduces to m ∣ 1
*∣⇒∣// : ∀ m n o .{{_ : NonZero (gcd n o)}} → m * gcd n o ∣ n → m ∣ n // o
*∣⇒∣// zero (suc n') zero 0∣n = ⊥-elim (sn≠0 n' (∣-max' 0∣n))
*∣⇒∣// m@(suc m') n@(suc n') zero m*gcd[no]∣n@(divides k n=k*[m*gcd[no]]) = subst (_∣ n // 0) (≡-sym m=1) (∣-min (n // 0))
    where
        open ≡-Reasoning
        thing : NonZero (m * gcd n zero)
        thing = *-nonZero m (gcd n 0)

        km=1 : k * m ≡ 1
        km=1 = *-cancelʳ-≡ (k * m) 1 (gcd n zero) (
            (k * m) * gcd n zero    ≡⟨ *-assoc k m (gcd n 0) ⟩
            k * (m * gcd n zero)    ≡⟨ ≡-sym n=k*[m*gcd[no]] ⟩
            n                       ≡⟨ ≡-sym (gcd-identity .proj₂ n) ⟩
            gcd n 0                 ≡⟨ ≡-sym (*-identity .proj₁ (gcd n 0)) ⟩
            1 * (gcd n zero)        ∎)

        m=1 : m ≡ 1
        m=1 = m*n≡1⇒n≡1 k m km=1
*∣⇒∣// m n o@(suc o') m*gcd[no]∣n@(divides k n=k*[m*gcd[no]]) = divides k (
    n // o                          ≡⟨ //=/gcd n o ⟩
    n / gcd n o                     ≡⟨ cong (_/ gcd n o) n=k*[m*gcd[no]] ⟩
    k * (m * gcd n o) / gcd n o     ≡⟨ cong (_/ gcd n o) (≡-sym (*-assoc k m (gcd n o))) ⟩
    k * m * gcd n o / gcd n o       ≡⟨ m*n/n≡m (k * m) (gcd n o) ⟩
    k * m                           ∎)
    where
        open ≡-Reasoning
        instance
            gcd[no]-nonZero : NonZero (gcd n o)
            gcd[no]-nonZero = gcd-nonZeroʳ n o

-- tight, due to inverse proof //∣⇒∣*
∣*⇒//∣ : ∀ m n o → m ∣ o * gcd m n → m // n ∣ o
∣*⇒//∣ m n o m∣o*gcd[mn]@(divides k o*gcd[mn]=k*m) with gcd m n ≟ 0
... | no gcd[mn]≠0 =
    divides k (*-cancelʳ-≡ o (k * m // n) (gcd m n) (
    o * gcd m n             ≡⟨ o*gcd[mn]=k*m ⟩
    k * m                   ≡⟨ cong (k *_) (//-factor m n) ⟩
    k * (m // n * gcd m n)  ≡⟨ ≡-sym (*-assoc k (m // n) (gcd m n)) ⟩
    (k * m // n) * gcd m n  ∎))
    where
        open ≡-Reasoning
        instance
            gcd[mn]-nonZero : NonZero (gcd m n)
            gcd[mn]-nonZero = ≢-nonZero gcd[mn]≠0
... | yes gcd[mn]=0 = subst (_∣ o) (
    1       ≡⟨⟩
    0 // 0  ≡⟨ cong (_// 0) (≡-sym (gcd-zero-proj₁ m n gcd[mn]=0)) ⟩
    m // 0  ≡⟨ cong (m //_) (≡-sym (gcd-zero-proj₂ m n gcd[mn]=0)) ⟩
    m // n ∎) (∣-min o)
    where open ≡-Reasoning

-- tbh, these two are less useful as strategies.
-- I'm mostly using them to demonstrate that the above two are tight.
∣//⇒*∣ : ∀ m n o → m ∣ n // o → m * gcd n o ∣ n
∣//⇒*∣ m n o m∣n//o@(divides k n//o=k*m) = divides k (
    n                   ≡⟨ //-factor n o ⟩
    n // o * gcd n o    ≡⟨ cong (_* gcd n o) n//o=k*m ⟩
    k * m * gcd n o     ≡⟨ *-assoc k m (gcd n o) ⟩
    k * (m * gcd n o)   ∎)
    where open ≡-Reasoning

//∣⇒∣* : ∀ m n o → m // n ∣ o → m ∣ o * gcd m n
//∣⇒∣* m n o m//n∣o@(divides k o=k*m//n) = divides k (
    o * gcd m n             ≡⟨ cong (_* gcd m n) o=k*m//n ⟩
    (k * m // n) * gcd m n  ≡⟨ *-assoc k (m // n) (gcd m n) ⟩
    k * (m // n * gcd m n)  ≡⟨ ≡-sym (cong (k *_) (//-factor m n)) ⟩
    k * m                   ∎)
    where open ≡-Reasoning

-- tight on valid inputs, due to inverse *=-via-//
-- However, if n and o are 0, then we have 0 = 0, so the output reduces to m = 1
=//-via-* : ∀ m n o .{{_ : NonZero (gcd n o)}} → m * gcd n o ≡ n → m ≡ n // o
=//-via-* m n o *gcd= = ∣-antisym (*∣⇒∣// m n o (∣-reflexive *gcd=)) (∣*⇒//∣ n o m (∣-reflexive (≡-sym *gcd=)))

*=-via-// : ∀ m n o → m ≡ n // o → m * gcd n o ≡ n
*=-via-// m n o m=n//o = ∣-antisym (∣//⇒*∣ m n o (∣-reflexive m=n//o)) (//∣⇒∣* n o m (∣-reflexive (≡-sym m=n//o)))

gcd-*-foil : ∀ m n o p → gcd m n * gcd o p ≡ gcd (gcd (m * o) (n * o)) (gcd (m * p) (n * p))
gcd-*-foil m n o p =
    gcd m n * gcd o p                                   ≡⟨ *-distrib-gcd .proj₁ (gcd m n) o p ⟩
    gcd (gcd m n * o) (gcd m n * p)                     ≡⟨ cong₂ gcd (*-distrib-gcd .proj₂ o m n) (*-distrib-gcd .proj₂ p m n) ⟩
    gcd (gcd (m * o) (n * o)) (gcd (m * p) (n * p))     ∎
    where open ≡-Reasoning

gcd-sym : {α : Level} → (P Q : ℕ → Set α) → (∀ m n → P (gcd m n) → Q m) → ∀ m n → P (gcd m n) → Q n
gcd-sym P Q P⇒Q m n P[gcd] = P⇒Q n m (subst P (gcd-comm m n) P[gcd])

m//n∣m : ∀ m n → m // n ∣ m
m//n∣m m n = divides (gcd m n) (≡-trans (//-factor m n) (*-comm (m // n) (gcd m n)))

gcd-∣-*ˡ : ∀ m n o p → gcd m n ∣ gcd (o * m) (p * n)
gcd-∣-*ˡ m n o p = gcd-glb (gcd m n) (o * m) (p * n)
    (∣-trans (gcd-∣₁ m n) (divides o ≡-refl))
    (∣-trans (gcd-∣₂ m n) (divides p ≡-refl))

gcd-∣-*ʳ : ∀ m n o p → gcd m n ∣ gcd (m * o) (n * p)
gcd-∣-*ʳ m n o p = subst (gcd m n ∣_) {gcd (o * m) (p * n)} {gcd (m * o) (n * p)} (cong₂ gcd (*-comm o m) (*-comm p n)) (gcd-∣-*ˡ m n o p)

-- Extract m from n; extract the leftover from o
gcd-distribˡ₁-* : ∀ m n o → gcd m (n * o) ≡ gcd m n * gcd (m // n) o
gcd-distribˡ₁-* m n o = ≡-sym (
    gcd m n * gcd (m // n) o                                    ≡⟨ gcd-*-foil m n (m // n) o ⟩
    gcd (gcd (m * m // n) (n * m // n)) (gcd (m * o) (n * o))   ≡⟨ ∣-antisym
        (gcd-glb _ m (n * o)
            (∣-trans (gcd-∣₁ (gcd (m * m // n) (n * m // n)) (gcd (m * o) (n * o))) (∣-reflexive (
                gcd (m * m // n) (n * m // n)   ≡⟨ ≡-sym (*-distrib-gcd .proj₂ (m // n) m n) ⟩
                gcd m n * m // n                ≡⟨ *-comm (gcd m n) (m // n) ⟩
                m // n * gcd m n                ≡⟨ ≡-sym (//-factor m n) ⟩
                m                               ∎)))
            (∣-trans (gcd-∣₂ (gcd (m * m // n) (n * m // n)) (gcd (m * o) (n * o))) (gcd-∣₂ (m * o) (n * o))))
        (gcd-glb _ (gcd (m * m // n) (n * m // n)) (gcd (m * o) (n * o))
            (gcd-glb _ (m * m // n) (n * m // n) (∣-trans (gcd-∣₁ m (n * o)) (m∣m*n (m // n))) (∣-trans (gcd-∣₁ m (n * o)) (∣-trans (m∣m//n*n m n) (∣-reflexive (*-comm (m // n) n)))))
            (gcd-glb _ (m * o) (n * o) (∣-trans (gcd-∣₁ m (n * o)) (m∣m*n o)) (gcd-∣₂ m (n * o)))) ⟩
    gcd m (n * o)                                               ∎)
    where open ≡-Reasoning

gcd-distribˡ₂-* : ∀ m n o → gcd m (n * o) ≡ gcd (m // o) n * gcd m o
gcd-distribˡ₂-* m n o =
    gcd m (n * o)               ≡⟨ cong (gcd m) (*-comm n o) ⟩
    gcd m (o * n)               ≡⟨ gcd-distribˡ₁-* m o n ⟩
    gcd m o * gcd (m // o) n    ≡⟨ *-comm (gcd m o) (gcd (m // o) n) ⟩
    gcd (m // o) n * gcd m o    ∎
    where open ≡-Reasoning

gcd-distribʳ₁-* : ∀ m n o → gcd (n * o) m ≡ gcd n m * gcd o (m // n)
gcd-distribʳ₁-* m n o =
    gcd (n * o) m               ≡⟨ gcd-comm (n * o) m ⟩
    gcd m (n * o)               ≡⟨ gcd-distribˡ₁-* m n o ⟩
    gcd m n * gcd (m // n) o    ≡⟨ cong₂ _*_ (gcd-comm m n) (gcd-comm (m // n) o) ⟩
    gcd n m * gcd o (m // n)    ∎
    where open ≡-Reasoning

gcd-distribʳ₂-* : ∀ m n o → gcd (n * o) m ≡ gcd n (m // o) * gcd o m
gcd-distribʳ₂-* m n o =
    gcd (n * o) m               ≡⟨ cong (λ q → gcd q m) (*-comm n o) ⟩
    gcd (o * n) m               ≡⟨ gcd-distribʳ₁-* m o n ⟩
    gcd o m * gcd n (m // o)    ≡⟨ *-comm (gcd o m) (gcd n (m // o)) ⟩
    gcd n (m // o) * gcd o m    ∎
    where open ≡-Reasoning

-- If o = 0, then the equation collapses to 1 = m
*-//-assoc' : ∀ m n o .{{_ : NonZero o}} → gcd (m * n) o ≡ gcd n o → (m * n) // o ≡ m * (n // o)
*-//-assoc' m n o@(suc o') gcd= =
    (m * n) // o ≡⟨ //=/gcd (m * n) o ⟩
    (m * n) / gcd (m * n) o ≡⟨ /-congʳ {m = m * n} gcd= ⟩
    (m * n) / gcd n o ≡⟨ *-/-assoc m {n} {gcd n o} (gcd-∣₁ n o) ⟩
    m * (n / gcd n o) ≡⟨ cong (m *_) (≡-sym (//=/gcd n o)) ⟩
    m * n // o ∎
    where
        open ≡-Reasoning
        instance
            gcd[no]-nonZero : NonZero (gcd n o)
            gcd[no]-nonZero = gcd-nonZeroʳ n o

            gcd[mn,o]-nonZero : NonZero (gcd (m * n) o)
            gcd[mn,o]-nonZero = gcd-nonZeroʳ (m * n) o

*-//-assoc : ∀ m n o .{{_ : NonZero o}} → o ∣ n → (m * n) // o ≡ m * (n // o)
*-//-assoc m n o@(suc o') o∣n = *-//-assoc' m n o (≡-trans (∣⇒gcd=id₂ {m * n} {o} (∣-trans o∣n (n∣m*n m {n}))) (≡-sym (∣⇒gcd=id₂ o∣n)))

m//n//o=m//[n*o] : ∀ m n o → m // n // o ≡ m // (n * o)
m//n//o=m//[n*o] zero zero zero = ≡-refl
m//n//o=m//[n*o] zero n@(suc n') o@(suc o') = ≡-refl
m//n//o=m//[n*o] zero zero o@(suc o') =
    zero // zero // o   ≡⟨⟩
    1 // o              ≡⟨ 1//n=1 o ⟩
    1                   ≡⟨⟩
    zero // zero        ≡⟨⟩
    zero // (zero * o)  ∎
    where open ≡-Reasoning
m//n//o=m//[n*o] zero n@(suc n') zero =
    zero // n // zero   ≡⟨⟩
    zero // zero        ≡⟨ cong (zero //_) (≡-sym (*-zero .proj₂ n)) ⟩
    zero // (n * zero)  ∎
    where open ≡-Reasoning
m//n//o=m//[n*o] m@(suc m') n o =
    m // n // o                     ≡⟨ //=/gcd (m // n) o ⟩
    m // n / gcd (m // n) o         ≡⟨ /-congˡ {gcd (m // n) o} {m // n} {m / gcd m n} (//=/gcd m n) ⟩
    m / gcd m n / gcd (m // n) o    ≡⟨ m/n/o≡m/[n*o] m (gcd m n) (gcd (m // n) o) ⟩
    m / (gcd m n * gcd (m // n) o)  ≡⟨ /-congʳ {gcd m n * gcd (m // n) o} {gcd m (n * o)} {m} (≡-sym (gcd-distribˡ₁-* m n o)) ⟩
    m / gcd m (n * o)               ≡⟨ ≡-sym (//=/gcd m (n * o)) ⟩
    m // (n * o)                    ∎
    where
        open ≡-Reasoning
        instance
            m//n-nonZero : NonZero (m // n)
            m//n-nonZero = //-nonZero m n

            gcd[mn]-nonZero : NonZero (gcd m n)
            gcd[mn]-nonZero = gcd-nonZeroˡ m n

            gcd[m//n,o]-nonZero : NonZero (gcd (m // n) o)
            gcd[m//n,o]-nonZero = gcd-nonZeroˡ (m // n) o

            thing-nonZero : NonZero (gcd m n * gcd (m // n) o)
            thing-nonZero = *-nonZero (gcd m n) (gcd (m // n) o)

            gcd[m,n*o]-nonZero : NonZero (gcd m (n * o))
            gcd[m,n*o]-nonZero = gcd-nonZeroˡ m (n * o)

m//n//o=m//o//n : ∀ m n o → m // n // o ≡ m // o // n
m//n//o=m//o//n m n o =
    m // n // o     ≡⟨ m//n//o=m//[n*o] m n o ⟩
    m // (n * o)    ≡⟨ cong (m //_) (*-comm n o) ⟩
    m // (o * n)    ≡⟨ ≡-sym (m//n//o=m//[n*o] m o n) ⟩
    m // o // n     ∎
    where open ≡-Reasoning

//-factor-cancelʳ : ∀ m n o .{{_ : NonZero m}} → (n * m) // (o * m) ≡ n // o
//-factor-cancelʳ m n zero =
    (n * m) // (zero * m)   ≡⟨⟩
    (n * m) // zero         ≡⟨ //0=1 (n * m) ⟩
    1                       ≡⟨ ≡-sym (//0=1 n) ⟩
    n // zero               ∎
    where open ≡-Reasoning
//-factor-cancelʳ m n o@(suc o') =
    (n * m) // (o * m)              ≡⟨ //=/gcd (n * m) (o * m) ⟩
    (n * m) / gcd (n * m) (o * m)   ≡⟨ /-congʳ {m = n * m} (≡-sym (*-distrib-gcd .proj₂ m n o)) ⟩
    (n * m) / (gcd n o * m)         ≡⟨ *-/-exchange {n} {m} {gcd n o} {m} (gcd-∣₁ n o) ∣-refl ⟩
    (n / gcd n o) * (m / m)         ≡⟨ cong₂ _*_ (≡-sym (//=/gcd n o)) (n/n≡1 m) ⟩
    n // o * 1                      ≡⟨ *-identity .proj₂ (n // o) ⟩
    n // o                          ∎
    where
        open ≡-Reasoning
        instance
            gcd[no]-nonZero : NonZero (gcd n o)
            gcd[no]-nonZero = gcd-nonZeroʳ n o

            gcd-*-nonZero : NonZero (gcd n o * m)
            gcd-*-nonZero = *-nonZero (gcd n o) m

            gcd-nonZero : NonZero (gcd (n * m) (o * m))
            gcd-nonZero = subst NonZero (*-distrib-gcd .proj₂ m n o) gcd-*-nonZero

//-factor-cancelˡ : ∀ m n o .{{_ : NonZero m}} → (m * n) // (m * o) ≡ n // o
//-factor-cancelˡ m n o = subst (_≡ n // o) (cong₂ _//_ (*-comm n m) (*-comm o m)) (//-factor-cancelʳ m n o)

//-factor-cancel : (∀ m n o .{{_ : NonZero m}} → (m * n) // (m * o) ≡ n // o) × (∀ m n o .{{_ : NonZero m}} → (n * m) // (o * m) ≡ n // o)
//-factor-cancel = //-factor-cancelˡ , //-factor-cancelʳ

//-distribʳ₂-* : ∀ m n o .{{_ : NonZero m}} .{{_ : NonZero n}} → (m * n) // o ≡ m // (o // n) * (n // o)
//-distribʳ₂-* m@(suc m') n@(suc n') o =
    (m * n) // o                            ≡⟨ //=/gcd (m * n) o ⟩
    m * n / gcd (m * n) o                   ≡⟨ /-congʳ {m = m * n} (
        gcd (m * n) o               ≡⟨ gcd-comm (m * n) o ⟩
        gcd o (m * n)               ≡⟨ gcd-distribˡ₂-* o m n ⟩
        gcd (o // n) m * gcd o n    ∎) ⟩
    m * n / (gcd (o // n) m * gcd o n)      ≡⟨ *-/-exchange {m} {n} {gcd (o // n) m} {gcd o n} (gcd-∣₂ (o // n) m) (gcd-∣₂ o n) ⟩
    (m / gcd (o // n) m) * (n / gcd o n)    ≡⟨ cong₂ _*_ (≡-sym (//=/gcd' m (o // n))) (≡-sym (//=/gcd' n o)) ⟩
    m // (o // n) * n // o                  ∎
    where
        open ≡-Reasoning
        instance
            gcd[m*n,o]-nonZero : NonZero (gcd (m * n) o)
            gcd[m*n,o]-nonZero = gcd-nonZeroˡ (m * n) o

            gcd[no]-nonZero : NonZero (gcd o n)
            gcd[no]-nonZero = gcd-nonZeroʳ o n

            gcd[o//n,m]-nonZero : NonZero (gcd (o // n) m)
            gcd[o//n,m]-nonZero = gcd-nonZeroʳ (o // n) m

            gcd[o//n,m]*gcd[on]-nonZero : NonZero (gcd (o // n) m * gcd o n)
            gcd[o//n,m]*gcd[on]-nonZero = *-nonZero (gcd (o // n) m) (gcd o n)

//-distribʳ₂'-* : ∀ m n o .{{_ : NonZero o}} → (m * n) // o ≡ m // (o // n) * (n // o)
//-distribʳ₂'-* zero n o@(suc o') =
    (zero * n) // o             ≡⟨⟩
    zero // o                   ≡⟨ 0//=0 o ⟩
    zero                        ≡⟨⟩
    zero * n // o               ≡⟨ ≡-sym (cong (_* n // o) (0//=0 (o // n) {{//-nonZero o n}})) ⟩
    zero // (o // n) * n // o   ∎
    where open ≡-Reasoning
//-distribʳ₂'-* m@(suc m') zero o@(suc o') =
    (m * zero) // o                 ≡⟨ cong (_// o) (*-zero .proj₂ m) ⟩
    zero // o                       ≡⟨⟩
    zero                            ≡⟨ ≡-sym (*-zero .proj₂ (m // (o // zero))) ⟩
    m // (o // zero) * zero         ≡⟨⟩
    m // (o // zero) * zero // o    ∎
    where open ≡-Reasoning
//-distribʳ₂'-* m@(suc m') n@(suc n') o = //-distribʳ₂-* m n o

//-distribʳ₁-* : ∀ m n o .{{_ : NonZero m}} .{{_ : NonZero n}} → (m * n) // o ≡ m // o * n // (o // m)
//-distribʳ₁-* m n o =
    (m * n) // o            ≡⟨ cong (_// o) (*-comm m n) ⟩
    (n * m) // o            ≡⟨ //-distribʳ₂-* n m o ⟩
    n // (o // m) * m // o  ≡⟨ *-comm (n // (o // m)) (m // o) ⟩
    m // o * n // (o // m)  ∎
    where open ≡-Reasoning

//-distribʳ₁'-* : ∀ m n o .{{_ : NonZero o}} → (m * n) // o ≡ m // o * n // (o // m)
//-distribʳ₁'-* m n o =
    (m * n) // o            ≡⟨ cong (_// o) (*-comm m n) ⟩
    (n * m) // o            ≡⟨ //-distribʳ₂'-* n m o ⟩
    n // (o // m) * m // o  ≡⟨ *-comm (n // (o // m)) (m // o) ⟩
    m // o * n // (o // m)  ∎
    where open ≡-Reasoning


//-monoˡ-∣ : ∀ m {n o} → n ∣ o → n // m ∣ o // m
//-monoˡ-∣ m {n} {o} n∣o = ∣*⇒//∣ n m (o // m) (subst (n ∣_) (≡-sym (*-distrib-gcd .proj₁ (o // m) n m)) (gcd-glb n (o // m * n) (o // m * m)
    (divides (o // m) ≡-refl)
    (∣-trans n∣o (m∣m//n*n o m))))

//-monoʳ-∣ : ∀ m {n o} → o ∣ n → m // n ∣ m // o
//-monoʳ-∣ m {n} {o} o∣n = ∣*⇒//∣ m n (m // o) (subst (_∣ m // o * gcd m n) (≡-sym (//-factor m o)) (*-monoʳ-∣ (m // o) (gcd-glb (gcd m o) m n (gcd-∣₁ m o) (∣-trans (gcd-∣₂ m o) o∣n))))

//-mono-∣ : ∀ {m n o p} → m ∣ o → p ∣ n → m // n ∣ o // p
//-mono-∣ {m} {n} {o} {p} m∣o p∣n = ∣-trans {j = o // n} (//-monoˡ-∣ n m∣o) (//-monoʳ-∣ o p∣n)

-- // o ≡ m // (o // n) * (n // o)
-- //-distribʳ₁-* m n o =
--     (m * n) // o            ≡⟨ {!   !} ⟩
--     m // (o // n) * n // o  ∎
--     where open ≡-Reasoning

-- //-distribʳ-gcd : _//_ DistributesOverʳ gcd
-- //-distribʳ-gcd m n o = ∣-antisym
--     (gcd-glb (gcd n o // m) (n // m) (o // m) (//-monoˡ-∣ {gcd n o} {n} m (gcd-∣₁ n o)) (//-monoˡ-∣ {gcd n o} {o} m (gcd-∣₂ n o)))
--     (*∣⇒∣// (gcd (n // m) (o // m)) (gcd n o) m (gcd-glb (gcd (n // m) (o // m) * gcd (gcd n o) m) n o (thing n o) (subst (_∣ o) (cong₂ _*_ (gcd-comm (o // m) (n // m)) (cong (λ q → gcd q m) (gcd-comm o n))) (thing o n))))
--     where
--         instance
--             gcd-blob-nonZero : NonZero (gcd (gcd n o) m)
--             gcd-blob-nonZero = {!   !}

--         thing : ∀ n o → gcd (n // m) (o // m) * gcd (gcd n o) m ∣ n
--         thing n o = {! gcd-*-foil (n // m) (o // m) (gcd n o) m  !}
--             -- begin
--             -- gcd (n // m) (o // m) * gcd (gcd n o) m ∣⟨ {!   !} ⟩
--             -- gcd (n // m) o * gcd (gcd n m) o ≡⟨ {! ≡-sym (gcd-distribʳ₁-* (o // m) (n // m) (gcd n m))   !} ⟩
--             -- gcd (n // m) o * gcd (gcd n m) o * o ∣⟨ {!   !} ⟩
--             -- n ∎
--             where open ∣-Reasoning
--         open ≡-Reasoning

gcd-//-assoc : ∀ m n o .{{_ : NonZero (gcd n o)}} → gcd (m * gcd n o) n // o ≡ gcd m (n // o)
gcd-//-assoc m n o {{gcd[no]-nonZero}} =
    ≡-sym (=//-via-* (gcd m (n // o)) (gcd (m * gcd n o) n) o {{subst NonZero (≡-sym thing) gcd[no]-nonZero}} (
        subst (gcd m (n // o) * gcd (gcd (m * gcd n o) n) o ≡_) (≡-sym thing') (
            subst (λ q → gcd m (n // o) * q ≡ gcd (m * o) n) (≡-sym thing) (
                ≡-trans
                    (cong (gcd m (n // o) *_) (gcd-comm n o))
                    (≡-sym (gcd-distribʳ₂-* n m o))
            )
        )
    ))
    where
        open ≡-Reasoning

        thing' : gcd (m * gcd n o) n ≡ gcd (m * o) n
        thing' =
            gcd (m * gcd n o) n             ≡⟨ cong (λ q → gcd q n) (*-distrib-gcd .proj₁ m n o) ⟩
            gcd (gcd (m * n) (m * o)) n     ≡⟨ gcd-assoc (m * n) (m * o) n ⟩
            gcd (m * n) (gcd (m * o) n)     ≡⟨ ∣⇒gcd=id₂ {m * n} {gcd (m * o) n} (∣-trans (gcd-∣₂ (m * o) n) (divides m ≡-refl)) ⟩
            gcd (m * o) n                   ∎

        thing : gcd (gcd (m * gcd n o) n) o ≡ gcd n o
        thing =
            gcd (gcd (m * gcd n o) n) o     ≡⟨ gcd-assoc (m * gcd n o) n o ⟩
            gcd (m * gcd n o) (gcd n o)     ≡⟨ ∣⇒gcd=id₂ {m * gcd n o} {gcd n o} (divides m ≡-refl) ⟩
            gcd n o                         ∎

-- //-distribʳ-gcd : ∀ m n o → gcd n o // m ≡ gcd (n // m) (o // m) -- _//_ DistributesOverʳ gcd
-- //-distribʳ-gcd m n o = ≡-sym (=//-via-* (gcd (n // m) (o // m)) (gcd n o) m (≡-trans (gcd-*-foil (n // m) (o // m) (gcd n o) m) (∣-antisym
--     (gcd-glb thing n o {!   !} {!   !})
--     {! gcd-//-assoc (n // m) o m   !})))
--     where
--         thing = gcd (gcd (n // m * gcd n o) (o // m * gcd n o)) (gcd (n // m * m) (o // m * m))
--         -- if n ∣ m then n // m * m ∣ n
--         -- if m ∣ n then o // m * gcd n o ∣ o
--         -- but like, if m is bigger, it'll still divide o
--         instance
--             gcd-blob-nonZero : NonZero (gcd (gcd n o) m)
--             gcd-blob-nonZero = {!   !}

    -- gcd n o // m                    ≡⟨ //=//gcd (gcd n o) m ⟩
    -- gcd n o // (gcd (gcd n o) m)    ≡⟨ {! //gcd₁  !} ⟩
    -- gcd (n // m) (o // m) ∎
    -- where open ≡-Reasoning
    -- ≡-sym (=//-via-* (gcd (n // m) (o // m)) (gcd n o) m {{{!   !}}} (≡-trans (gcd-*-foil (n // m) (o // m) (gcd n o) m) {!   !}))
-- //-distribʳ-gcd m n o = ∣-antisym
--     (gcd-glb (gcd n o // m) (n // m) (o // m) (//-monoˡ-∣ {gcd n o} {n} m (gcd-∣₁ n o)) (//-monoˡ-∣ {gcd n o} {o} m (gcd-∣₂ n o)))
--     (*∣⇒∣// (gcd (n // m) (o // m)) (gcd n o) m (gcd-glb (gcd (n // m) (o // m) * gcd (gcd n o) m) n o (thing n o) (subst (_∣ o) (cong₂ _*_ (gcd-comm (o // m) (n // m)) (cong (λ q → gcd q m) (gcd-comm o n))) (thing o n))))
--     where
--         instance
--             gcd-blob-nonZero : NonZero (gcd (gcd n o) m)
--             gcd-blob-nonZero = {!   !}

--         thing : ∀ n o → gcd (n // m) (o // m) * gcd (gcd n o) m ∣ n
--         thing n o = {! gcd-*-foil (n // m) (o // m) (gcd n o) m  !}
--             -- begin
--             -- gcd (n // m) (o // m) * gcd (gcd n o) m ∣⟨ {!   !} ⟩
--             -- gcd (n // m) o * gcd (gcd n m) o ≡⟨ {! ≡-sym (gcd-distribʳ₁-* (o // m) (n // m) (gcd n m))   !} ⟩
--             -- gcd (n // m) o * gcd (gcd n m) o * o ∣⟨ {!   !} ⟩
--             -- n ∎
--             where open ∣-Reasoning
--         open ≡-Reasoning


---------------
--- Coprime ---
---------------

GCDCoprime : ℕ → ℕ → Set
GCDCoprime m n = gcd m n ≡ 1

coprime⇒m//n=m : ∀ m n → GCDCoprime m n → m // n ≡ m
coprime⇒m//n=m m n gcd=1 =
    m // n          ≡⟨ //=/gcd m n ⟩
    m / gcd m n ≡⟨ /-congʳ {m = m} gcd=1 ⟩
    m / 1 ≡⟨ n/1≡n m ⟩
    m ∎
    where
        open ≡-Reasoning
        instance
            gcd-nonZero : NonZero (gcd m n)
            gcd-nonZero = >-nonZero (≤-reflexive (≡-sym gcd=1))

coprime⇒gcd-*-cancelʳ₁ : ∀ m n o → GCDCoprime m n → gcd m (n * o) ≡ gcd m o
coprime⇒gcd-*-cancelʳ₁ m n o gcd= =
    gcd m (n * o)               ≡⟨ gcd-distribˡ₁-* m n o ⟩
    gcd m n * gcd (m // n) o    ≡⟨ cong₂ _*_ gcd= (cong (λ q → gcd q o) (coprime⇒m//n=m m n gcd=)) ⟩
    1 * gcd m o                 ≡⟨ *-identity .proj₁ (gcd m o) ⟩
    gcd m o                     ∎
    where open ≡-Reasoning

coprime-delete₁ : ∀ m n o → GCDCoprime m n → m ∣ n * o → m ∣ o
coprime-delete₁ m n o gcd= m∣n*o = gcd=id₁⇒∣ m o gcd[mo]=m
    where
        gcd[mo]=m : gcd m o ≡ m
        gcd[mo]=m =
            gcd m o         ≡⟨ ≡-sym (coprime⇒gcd-*-cancelʳ₁ m n o gcd=) ⟩
            gcd m (n * o)   ≡⟨ ∣⇒gcd=id₁ m∣n*o ⟩
            m               ∎
            where open ≡-Reasoning

coprime-delete₂ : ∀ m n o → GCDCoprime m o → m ∣ n * o → m ∣ n
coprime-delete₂ m n o gcd= m∣n*o = coprime-delete₁ m o n gcd= (subst (m ∣_) (*-comm n o) m∣n*o)


-- {-
--     n * o = k * m
--     but m and n are coprime (gcd m n = 1)

--     maybe I do want that gcd-*

--     regardless,
-- -}
-- -- gcd m n * o ≡ gcd (m * o) (n * o)
-- gcd-distribʳ-coprime-* : ∀ m n o → GCDCoprime n o → gcd (n * o) m ≡ gcd n m * gcd o m
-- gcd-distribʳ-coprime-* m n o gcd[no]=1 =
--     gcd (n * o) m ≡⟨ {!  !} ⟩ -- gcd-distribʳ₂-* m n o
--     {!   !}     ≡⟨ cong (λ q → gcd n m * gcd o q) {! coprime⇒m//n=m m n   !} ⟩
--     gcd n m * gcd o m ∎
--     where open ≡-Reasoning

    -- gcd (n * o) m                   ≡⟨ cong (gcd (n * o)) (≡-sym (∣⇒gcd=id₁ (divides m ≡-refl))) ⟩
    -- gcd (n * o) (gcd m (m * m))     ≡⟨ ≡-sym (gcd-assoc (n * o) m (m * m)) ⟩
    -- gcd (gcd (n * o) m) (m * m)     ≡⟨ cong (λ q → gcd (gcd (n * o) q) (m * m)) {m} {gcd (m * o) (n * m)} (
    --     m                       ≡⟨ ≡-sym (*-identity .proj₁ m) ⟩
    --     1 * m                   ≡⟨ cong (_* m) (≡-sym gcd[no]=1) ⟩
    --     gcd n o * m             ≡⟨ *-distrib-gcd .proj₂ m n o ⟩
    --     gcd (n * m) (o * m)     ≡⟨ gcd-comm (n * m) (o * m) ⟩
    --     gcd (o * m) (n * m)     ≡⟨ cong (λ q → gcd q (n * m)) (*-comm o m) ⟩
    --     gcd (m * o) (n * m)     ∎) ⟩
    -- gcd (gcd (n * o) (gcd (m * o) (n * m))) (m * m)     ≡⟨ ≡-sym (assoc-middle (discrete-setoid ℕ) gcd (λ {i} {j} {o} → ≡-sym (gcd-assoc i j o)) (inj₁ λ { ≡-refl → ≡-refl }) {n * o} {m * o} {n * m} {m * m}) ⟩
    -- gcd (gcd (n * o) (m * o)) (gcd (n * m) (m * m))     ≡⟨ ≡-sym (gcd-*-foil n m o m) ⟩
    -- gcd n m * gcd o m       ∎

-- gcd-distribˡ-coprime-* : ∀ m n o → GCDCoprime n o → gcd m (n * o) ≡ gcd m n * gcd m o
-- gcd-distribˡ-coprime-* m n o no-coprime =
--     gcd m (n * o)       ≡⟨ gcd-comm m (n * o) ⟩
--     gcd (n * o) m       ≡⟨ gcd-distribʳ-coprime-* m n o no-coprime ⟩
--     gcd n m * gcd o m   ≡⟨ cong₂ _*_ (gcd-comm n m) (gcd-comm o m) ⟩
--     gcd m n * gcd m o   ∎



--     -- gcd (gcd (m * n) (1 * o)) (o * o)     ≡⟨ {!   !} ⟩
--     -- gcd (gcd (m * n) (gcd m n * o)) (o * o)     ≡⟨ {!   !} ⟩
--     -- gcd (gcd (m * n) (gcd (m * o) (n * o))) (o * o)     ≡⟨ {!   !} ⟩
--     -- ∣-antisym ()
--     -- {!  gcd-*-foil m o n o !}
--     -- gcd-*-foil m o n o
--     -- *-distrib-gcd .proj₂ o m n
-- -- coprime-* : ∀ m n o → GCDCoprime m o → gcd m n ≡ gcd m (n * o)
-- -- coprime-* m n o (gcdCoprime gcd[mo]=1) = gcd-induction-up P (λ i j (gcdCoprime gcd[io]=1 , gcd=) → gcdCoprime {! gcd=  !} , coprime-* j i o {!   !}) n m (gcdCoprime (
-- --     gcd (gcd n m) o     ≡⟨ gcd-assoc n m o ⟩
-- --     gcd n (gcd m o)     ≡⟨ cong (gcd n) gcd[mo]=1 ⟩
-- --     gcd n 1             ≡⟨ gcd-one .proj₂ n ⟩
-- --     1                   ∎) ,
-- --     ≡-refl) .proj₂
-- --     where
-- --         P : ℕ → ℕ → Set
-- --         P i j = GCDCoprime j o × gcd j i ≡ gcd j (i * o)

-- coprime-delete : ∀ m n o → GCDCoprime m n → m ∣ n * o → m ∣ o
-- coprime-delete m zero o (gcdCoprime gcd[mn]=1) _ = divides o (
--     o       ≡⟨ ≡-sym(*-identity .proj₂ o) ⟩
--     o * 1   ≡⟨ cong (o *_) (≡-sym m=1) ⟩
--     o * m   ∎)
--     where
--         m=1 : m ≡ 1
--         m=1 =
--             m           ≡⟨ ≡-sym (gcd-identity .proj₂ m) ⟩
--             gcd m 0     ≡⟨ gcd[mn]=1 ⟩
--             1           ∎
-- coprime-delete m n@(suc n') o (gcdCoprime gcd[mn]=1) m∣n*o@(divides k n*o=k*m) = {!   !}




-- gcd-gcd-factor : ∀ m n → gcd (m // n) (n // m) * gcd m n ∣ gcd m n
-- gcd-gcd-factor m n = gcd-glb (gcd (m // n) (n // m) * gcd m n) m n
--     (subst (gcd (m // n) (n // m) * gcd m n ∣_) (≡-sym (//-factor m n)) (*-monoˡ-∣ (gcd m n) (gcd-∣₁ (m // n) (n // m))))
--     (subst (gcd (m // n) (n // m) * gcd m n ∣_) (≡-sym (//-factor' m n)) ((*-monoˡ-∣ (gcd m n) (gcd-∣₂ (m // n) (n // m)))))

-- //-coprime : ∀ m n → GCDCoprime (m // n) (n // m)
-- //-coprime zero zero = gcdCoprime ≡-refl
-- //-coprime zero (suc n) = gcdCoprime ≡-refl
-- //-coprime m@(suc m') n with gcd (m // n) (n // m) ≟ 1
-- ... | yes gcd=1 = gcdCoprime gcd=1
-- ... | no gcd≠1 = ⊥-elim (helper' gcd≠1)
--     where
--         instance
--             gcd-nonZero : NonZero (gcd m n)
--             gcd-nonZero = gcd-nonZeroˡ m n

--         blob = gcd (m // n) (n // m)

--         helper : ∀ k → gcd (m // n) (n // m) ≡ k → k ≡ 1
--         helper zero gcd-gcd-div=0 = ⊥-irr-elim (sn≠0 m' (
--             m                   ≡⟨ //-factor m n ⟩
--             m // n * gcd m n    ≡⟨ cong (_* gcd m n) (gcd-zero-proj₁ (m // n) (n // m) gcd-gcd-div=0) ⟩
--             0 * gcd m n         ≡⟨⟩
--             0                   ∎))
--         helper (suc zero) _ = ≡-refl
--         helper k@(suc (suc k')) gcd-gcd-div=k = ⊥-irr-elim (<-irrefl ≡-refl (<-≤-trans gcd<blob blob≤gcd))
--             where
--                 gcd<blob : gcd m n < blob * gcd m n
--                 gcd<blob = m<n*m (gcd m n) blob (<-≤-trans (s≤s (s≤s z≤n)) (≤-reflexive (≡-sym gcd-gcd-div=k)))

--                 blob≤gcd : blob * gcd m n ≤ gcd m n
--                 blob≤gcd = ∣⇒≤ (gcd-gcd-factor m n)

--         helper' : ¬ ¬ (gcd (m // n) (n // m) ≡ 1)
--         helper' ¬gcd=1 with gcd (m // n) (n // m) | inspect (gcd (m // n)) (n // m)
--         ... | zero | [ eq ] = case helper zero eq of λ ()
--         ... | suc zero | [ eq ] = ¬gcd=1 ≡-refl
--         ... | suc (suc k) | [ eq ] = case helper (suc (suc k)) eq of λ ()


-- lcm : ℕ → ℕ → ℕ
-- lcm zero _ = zero
-- lcm (suc _) zero = zero
-- lcm m@(suc m') n@(suc n') = m * n / gcd m n
--     where
--         instance
--             gcd-nonZero : NonZero (gcd m n)
--             gcd-nonZero = gcd-nonZeroˡ m n

-- lcm-decomposition-helper : ∀ m n → ((divides p _) : gcd m n ∣ m) → ((divides q _) : gcd m n ∣ n) → lcm m n ≡ p * q * gcd m n
-- lcm-decomposition-helper zero zero (divides p _) (divides q _) = ≡-sym (*-zero .proj₂ (p * q))
-- lcm-decomposition-helper zero n@(suc n') gcd∣m@(divides p _) (divides q _) =
--     zero                    ≡⟨⟩
--     zero * q * gcd zero n   ≡⟨ cong (λ x → x * q * gcd zero n) (≡-sym (0-divisor gcd∣m)) ⟩
--     p * q * gcd zero n      ∎
-- lcm-decomposition-helper m@(suc m') zero (divides p _) gcd∣n@(divides q _) =
--     zero                    ≡⟨⟩
--     zero * gcd m zero       ≡⟨ cong (_* gcd m zero) (≡-sym (*-zero .proj₂ p)) ⟩
--     p * zero * gcd m zero   ≡⟨ cong (λ x → p * x * gcd m zero) (≡-sym (0-divisor gcd∣n)) ⟩
--     p * q * gcd m zero ∎
-- lcm-decomposition-helper m@(suc m') n@(suc n') (divides p m=p*gcd) (divides q n=q*gcd) =
--     m * n / gcd m n                             ≡⟨ cong (_/ gcd m n) (cong₂ _*_ m=p*gcd n=q*gcd) ⟩
--     (p * gcd m n) * (q * gcd m n) / gcd m n     ≡⟨ cong (_/ gcd m n) (≡-sym (*-assoc (p * gcd m n) q (gcd m n))) ⟩
--     ((p * gcd m n) * q) * gcd m n / gcd m n     ≡⟨  m*n/n≡m (p * gcd m n * q) (gcd m n) ⟩
--     p * gcd m n * q                             ≡⟨ m*n*o=m*o*n p (gcd m n) q ⟩
--     p * q * gcd m n                             ∎
--     where
--         instance
--             gcd-nonZero : NonZero (gcd m n)
--             gcd-nonZero = gcd-nonZeroˡ m n

-- lcm-decomposition : ∀ m n → lcm m n ≡ m // n * n // m * gcd m n
-- lcm-decomposition m n = lcm-decomposition-helper m n (gcd-∣₁ m n) (gcd-∣₂ m n)

-- lcm-factor₂ : ∀ m n → lcm m n ≡ m // n * n
-- lcm-factor₂ m n =
--     lcm m n                         ≡⟨ lcm-decomposition m n ⟩
--     m // n * n // m * gcd m n       ≡⟨ *-assoc (m // n) (n // m) (gcd m n) ⟩
--     m // n * (n // m * gcd m n)     ≡⟨ cong (m // n *_) (≡-sym (//-factor' m n)) ⟩
--     m // n * n                      ∎
--     where open ≡-Reasoning

-- lcm-∣₁ : ∀ m n → m ∣ lcm m n
-- lcm-∣₁ m n = divides (n // m) (
--     lcm m n                         ≡⟨ lcm=p*q*gcd ⟩
--     m // n * n // m * gcd m n       ≡⟨ cong (_* gcd m n) (*-comm (m // n) (n // m)) ⟩
--     n // m * m // n * gcd m n       ≡⟨ *-assoc (n // m) (m // n) (gcd m n) ⟩
--     n // m * (m // n * gcd m n)     ≡⟨ cong (n // m *_) (≡-sym (gcd-∣₁ m n ._∣_.equality)) ⟩
--     n // m * m                      ∎)
--     where lcm=p*q*gcd = lcm-decomposition m n

-- lcm-∣₂ : ∀ m n → n ∣ lcm m n
-- lcm-∣₂ m n = divides (m // n) (
--     lcm m n                         ≡⟨ lcm=p*q*gcd ⟩
--     m // n * n // m * gcd m n       ≡⟨ *-assoc (m // n) (n // m) (gcd m n) ⟩
--     m // n * (n // m * gcd m n)     ≡⟨ cong (m // n *_) (≡-sym (gcd-∣₂ m n ._∣_.equality)) ⟩
--     m // n * n                      ∎)
--     where lcm=p*q*gcd = lcm-decomposition m n

-- *-gcd-lcm-factor : ∀ m n → m * n ≡ gcd m n * lcm m n
-- *-gcd-lcm-factor m n =
--     m * n                                       ≡⟨ cong₂ _*_ (//-factor m n) (//-factor' m n) ⟩
--     (m // n * gcd m n) * (n // m * gcd m n)     ≡⟨ cong (_* (n // m * gcd m n)) (*-comm (m // n) (gcd m n)) ⟩
--     (gcd m n * m // n) * (n // m * gcd m n)     ≡⟨ assoc-middle (discrete-setoid ℕ) (Function.flip _*_) (λ {x} {y} {z} → *-assoc z y x) ((inj₁ λ { ≡-refl → ≡-refl })) {gcd m n} {n // m} {m // n} {gcd m n} ⟩
--     gcd m n * (m // n * n // m * gcd m n)       ≡⟨ cong (gcd m n *_) (≡-sym (lcm-decomposition m n)) ⟩
--     gcd m n * lcm m n                           ∎
--     where open ≡-Reasoning

-- gcd-distribˡ-lcm : gcd DistributesOverˡ lcm
-- gcd-distribˡ-lcm m n o =
--     gcd m (lcm n o)                     ≡⟨ cong (gcd m) (lcm-decomposition n o) ⟩
--     gcd m (n // o * o // n * gcd n o)   ≡⟨ cong (gcd m) (*-assoc (n // o) (o // n) (gcd n o)) ⟩
--     gcd m (n // o * (o // n * gcd n o)) ≡⟨ cong (λ q → gcd m (n // o * q)) (*-distrib-gcd .proj₁ (o // n) n o) ⟩
--     gcd m (n // o * gcd (o // n * n) (o // n * o)) ≡⟨ cong (gcd m) (*-distrib-gcd .proj₁ (n // o) (o // n * n) (o // n * o)) ⟩
--     gcd m (gcd (n // o * (o // n * n)) (n // o * (o // n * o))) ≡⟨ {!!} ⟩
--     gcd m n // gcd m o * gcd m o // gcd m n * gcd (gcd m n) (gcd m o)  ≡⟨ ≡-sym (lcm-decomposition (gcd m n) (gcd m o)) ⟩
--     lcm (gcd m n) (gcd m o)             ∎
--     where open ≡-Reasoning

-- gcd-distribʳ-lcm : gcd DistributesOverʳ lcm
-- gcd-distribʳ-lcm = {!   !}

-- gcd-distrib-lcm : gcd DistributesOver lcm
-- gcd-distrib-lcm = {!   !}

-- lcm-distribˡ-gcd : lcm DistributesOverˡ gcd
-- lcm-distribˡ-gcd = {!   !}

-- lcm-distribʳ-gcd : lcm DistributesOverʳ gcd
-- lcm-distribʳ-gcd = {!   !}

-- lcm-distrib-gcd : lcm DistributesOver gcd
-- lcm-distrib-gcd = {!   !}



-- {-
--     m = p * n
--     m = q * o

--     show gcd n o divides m

--     p * n
--     p * n // o * gcd n o

--     m =
--     q * o // n * gcd n o

--     thus

--     p * n // o = q * o // n
--     or else gcd n o = 0 (and thus n and o = 0)

--     but since gcd-div₁ and gcd-div₂ are coprime, all their factors are in the other number
--     so p = gcd-div₂
--     and q = gcd-div₁

-- -}
-- lcm-glb : ∀ m n o → n ∣ m → o ∣ m → lcm n o ∣ m
-- lcm-glb m zero o n∣m@(divides p m=p*n) o∣m@(divides q m=q*o) = divides 0 (∣-max' n∣m)
-- lcm-glb m n@(suc n') o n∣m@(divides p m=p*n) o∣m@(divides q m=q*o) = divides {!   !} (
--     m               ≡⟨ {!   !} ⟩
--     {!   !} * lcm n o ∎)
