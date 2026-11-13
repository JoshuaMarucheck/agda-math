open import Level using (Level) renaming (zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≢_; _≡_; inspect; cong; cong₂; subst; Reveal_·_is_; [_]) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open import Relation.Binary using (tri<; tri≈; tri>; Recomputable; Setoid; IsPartialOrder)
open import Relation.Nullary.Decidable using (Dec; yes; no; recompute)
open import Relation.Nullary.Negation using (¬_)
import Relation.Unary as Unary
import Relation.Nullary as Nullary
open import Data.Unit using (⊤; tt)
open import Data.Bool using (true; false)
open import Data.Nat using (ℕ; _+_; _∸_; _*_; _^_; _!; _≤_; _≥_; _<_; _>_; <-cmp; _<?_; _≤?_; _≤ᵇ_; _<ᵇ_; s≤s; z≤n; s≤s⁻¹; zero; suc; pred; NonZero; ≢-nonZero; >-nonZero; NonTrivial; _⊔_; _⊓_)
open import Data.Nat.Properties using (module ≤-Reasoning; <-irrefl; ≤-refl; <-trans; ≤-reflexive; <⇒≤; ≤⇒≤ᵇ; ≤ᵇ⇒≤; <ᵇ⇒<; <⇒<ᵇ; ≰⇒>; ≮⇒≥; +-assoc; +-comm; +-suc; +-cancel-≡; *-comm; *-assoc; *-identity; *-zero; *-distrib-∸; *-cancelˡ-≤; *-cancelʳ-≤; *-cancelʳ-<; ≤-isPartialOrder; m∸n≤m; _≟_; m+n∸n≡m; m+n∸m≡n; n∸n≡0; 0∸n≡0; m*n≢0⇒m≢0; m≤n+m; m≤m+n; m≤m*n; m≤n*m; m<m*n; m≤n⇒m⊔n≡n; m≥n⇒m⊔n≡m; ⊔-comm; 1≤n!; m⊓n≤m; m⊓n≤n; m≤m⊔n; m≤n⊔m)
open import Data.Nat.DivMod using (_/_; _%_; m≡m%n+[m/n]*n; m/n≡1+[m∸n]/n; [m+kn]%n≡m%n; m<n⇒m%n≡m; m%n%n≡m%n; m%n<n; m/n*n≤m; +-distrib-/-∣ˡ; m*n/n≡m; m/n*n≡m; m*n/m*o≡n/o; m%[n*o]/o≡m/o%n; m∣n⇒o%n%m≡o%m; m%n≡m∸m/n*n; m*n%n≡0; *-/-assoc; /-congˡ; /-congʳ; %-congˡ; %-congʳ; /-mono-≤)
open import Data.Nat.Divisibility using (divides; _∣_; n/m≡quotient; ∣-refl; ∣-trans)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; uncurry)
open import Data.Empty using (⊥; ⊥-elim)
open import Algebra.Definitions {A = ℕ} _≡_ using (_DistributesOver_; _DistributesOverʳ_; _DistributesOverˡ_)
open import Function using (Bijection; Injective; _∋_)

open import Plasmaduck.SetoidExperiment.SetoidMachinery using (discrete-setoid; SetoidFunction₂; from-discrete-cong₂)
open import Plasmaduck.Util.TypeChange using (change-type)
open import Plasmaduck.Util.Case using (case_of_)
open import Plasmaduck.Data.Empty using (≢-recompute; ⊥-irr-elim)
open import Plasmaduck.Data.Bool using (form-T-false)
open import Plasmaduck.Data.Product using (Σ≡; ×≡)
open import Plasmaduck.Data.Squash using (Squash; squash)
open import Plasmaduck.Data.FakeFin using (FakeFin; realize; falsify)
open import Plasmaduck.Relation.Order using (IsPartialOrder-flip)
open import Plasmaduck.Relation.Equivalence using (irrelevant-cong; ≡-isEquivalence)
open import Plasmaduck.Algebra.Lattice.Semilattice using (MeetSemilattice)
open import Plasmaduck.Relation.OrderHelpers using (WeakTri; cmp₁; cmp₂; cmp₃)



module Plasmaduck.Data.Nat where

open import Plasmaduck.Data.Nat.IrrelevantLe public


variable
    m n o p : ℕ
    c ℓ ℓ₁ : Level

*-nonZero : ∀ m n .{{_ : NonZero m}} .{{_ : NonZero n}} → NonZero (m * n)
*-nonZero (suc m) (suc n) = record { nonZero = tt }

*-factor₁-nonZero : ∀ m n .{{_ : NonZero (m * n)}} → NonZero m
*-factor₁-nonZero (suc m) n = record { nonZero = tt }

*-factor₂-nonZero : ∀ m n .{{_ : NonZero (m * n)}} → NonZero n
*-factor₂-nonZero m n {{mn-nonZero}} = *-factor₁-nonZero n m {{subst NonZero (*-comm m n) mn-nonZero}}

*-factor-nonZero : (∀ m n .{{_ : NonZero (m * n)}} → NonZero m) × (∀ m n .{{_ : NonZero (m * n)}} → NonZero n)
*-factor-nonZero = *-factor₁-nonZero , *-factor₂-nonZero

¬NonZero⇒is-zero : ¬ NonZero n → n ≡ 0
¬NonZero⇒is-zero {n = n} ¬nonZero with n ≟ 0
... | yes n=0 = n=0
... | no n≠0 = ⊥-elim (¬nonZero (≢-nonZero n≠0))

≤-recompute : Recomputable _≤_
≤-recompute {x} {y} = recompute (x ≤? y)

-- Look at how cheap this is!
NonZero-recompute : Nullary.Recomputable (NonZero n)
NonZero-recompute {zero} ()
NonZero-recompute {suc n} _ = record { nonZero = tt }

NonTrivial-recompute : Nullary.Recomputable (NonTrivial n)
NonTrivial-recompute {zero} ()
NonTrivial-recompute {suc zero} ()
NonTrivial-recompute {suc (suc n)} _ = record { nonTrivial = tt }

≠0∧≠1⇒nonTrivial : ∀ {n} → .(n ≢ 0) → .(n ≢ 1) → NonTrivial n
≠0∧≠1⇒nonTrivial {zero} n≠0 n≠1 = ⊥-irr-elim (n≠0 ≡-refl)
≠0∧≠1⇒nonTrivial {suc zero} n≠0 n≠1 = ⊥-irr-elim (n≠1 ≡-refl)
≠0∧≠1⇒nonTrivial {suc (suc n)} n≠0 n≠1 = record { nonTrivial = tt }

m≤1⇒m*n≤n : ∀ m n → .(m ≤ 1) → m * n ≤ n
m≤1⇒m*n≤n zero n m≤1 = z≤n
m≤1⇒m*n≤n (suc zero) n m≤1 = ≤-reflexive (+-comm n zero)
m≤1⇒m*n≤n (suc (suc m)) n m≤1 = ⊥-irr-elim (case s≤s⁻¹ m≤1 of λ ())

NonTrivial-divisor : ∀ m n .{{_ : NonTrivial m}} → .(m < m * n) → NonTrivial n
NonTrivial-divisor m zero m<m*n = ⊥-irr-elim (case <-≤-trans m<m*n (≤-reflexive (*-zero .proj₂ m)) of λ ())
NonTrivial-divisor m (suc zero) m<m*n = ⊥-irr-elim (<-irrefl {m} ≡-refl (<-≤-trans m<m*n (≤-reflexive (*-identity .proj₂ m))))
NonTrivial-divisor m (suc (suc n)) m<m*n = record { nonTrivial = tt }

nonTrivial⇒pred-nonZero : ∀ n .{{_ : NonTrivial n}} → NonZero (pred n)
nonTrivial⇒pred-nonZero (suc (suc _)) = record { nonZero = tt }

nonZero⇒suc-nonTrivial : ∀ n .{{_ : NonZero n}} → NonTrivial (suc n)
nonZero⇒suc-nonTrivial (suc _) = record { nonTrivial = tt }

≤-cmp : (m n : ℕ) → m ≤ n ⊎ m > n
≤-cmp m n with <-cmp m n
... | tri< m<n _ _ = inj₁ (<⇒≤ m<n)
... | tri≈ _ m=n _ = inj₁ (≤-reflexive m=n)
... | tri> _ _ m>n = inj₂ m>n

≤⇒≡∨< : ∀ {m n} → .(m ≤ n) → m ≡ n ⊎ m < n
≤⇒≡∨< {m} {n} m≤n with <-cmp m n
... | tri< m<n _ _ = inj₂ m<n
... | tri≈ _ m=n _ = inj₁ m=n
... | tri> _ _ m>n = ⊥-irr-elim (<-irrefl ≡-refl (≤-<-trans m≤n m>n))

⊔≥₁ : ∀ m n → m ⊔ n ≥ m
⊔≥₁ m n with ≤-cmp m n
... | inj₁ m≤n = ≤-trans m≤n (≤-reflexive (≡-sym (m≤n⇒m⊔n≡n m≤n)))
... | inj₂ m>n = ≤-reflexive (≡-sym (m≥n⇒m⊔n≡m (<⇒≤ m>n)))

⊔≥₂ : ∀ m n → m ⊔ n ≥ n
⊔≥₂ m n = ≤-trans (⊔≥₁ n m) (≤-reflexive (⊔-comm n m))

max : ℕ → ℕ → ℕ
max m n with m ≤? n
... | yes _ = n
... | no _ = m

n≤n : n ≤ n
n≤n = ≤-refl

n<sn : n < suc n
n<sn = n≤n

n≤sn : n ≤ suc n
n≤sn {n = zero} = z≤n
n≤sn {n = suc n'} = s≤s n≤sn

m>0⇒m=sn : .(m > 0) → Σ ℕ λ n → m ≡ suc n
m>0⇒m=sn {m = suc m} m>0 = m , ≡-refl

m∸n>0⇒n<m : m ∸ n > 0 → n < m
m∸n>0⇒n<m {suc m} {zero} m∸n>0 = m∸n>0
m∸n>0⇒n<m {suc m} {suc n} m∸n>0 = s≤s (m∸n>0⇒n<m m∸n>0)

m<n*m : ∀ m n .{{_ : NonZero m}} → .(1 < n) → m < n * m
m<n*m m n 1<n = <-≤-trans (m<m*n m n 1<n) (≤-reflexive (*-comm m n))

m≢0⇒m=sn : .(m ≢ 0) → Σ ℕ λ n → m ≡ suc n
m≢0⇒m=sn {m = zero} m≠0 = ⊥-elim ((≢-recompute m≠0) ≡-refl)
m≢0⇒m=sn {m = suc m} _ = m , ≡-refl

sn≠0 : ∀ n → suc n ≢ 0
sn≠0 n ()

m<n⇒m≢n : .(m > 0) → m ≢ 0
m<n⇒m≢n {0} 0>0 ≡-refl = case (≤-recompute 0>0) of λ ()

m≤n⇒m≤pn : .(m ≤ n) → pred m ≤ n
m≤n⇒m≤pn {m = zero} {n = n} m≤n = z≤n
m≤n⇒m≤pn {m = m@(suc m')} {n = n} m≤n = ≤-trans n≤sn m≤n

m<n⇒n∸m-nonZero : .(m < n) → NonZero (n ∸ m)
m<n⇒n∸m-nonZero m<n = >-nonZero (m<n⇒0<n∸m m<n)

m<o∧n<p⇒s[m+o]<n+p : .(m < o) → .(n < p) → suc (m + n) < o + p
m<o∧n<p⇒s[m+o]<n+p {m = m} {n = n} m<o n<p = ≤-trans (≤-reflexive (cong suc (≡-sym (+-suc m n)))) (+-mono-≤ m<o n<p)

∸-cancelˡ-< : ∀ {m n o} → n ∸ m < o ∸ m → n < o
∸-cancelˡ-< {zero} {n} {o} n<o = n<o
∸-cancelˡ-< {suc m} {zero} {suc o} n∸m<o∸m = s≤s z≤n
∸-cancelˡ-< {suc m} {suc n} {suc o} n∸m<o∸m = s≤s (∸-cancelˡ-< {m} {n} {o} n∸m<o∸m)

<→≤ : m < n → m ≤ n
<→≤ (s≤s m-1<n-1) = ≤-trans m-1<n-1 n≤sn

≤≥⇒≡ : .(m ≤ n) → .(m ≥ n) → m ≡ n
≤≥⇒≡ {m} {n} m≤n m≥n with <-cmp m n
... | tri< m<n _ _ = ⊥-elim (<-irrefl ≡-refl (<-≤-trans m<n (≤-recompute m≥n)))
... | tri≈ _ m≡n _ = m≡n
... | tri> _ _ m>n = ⊥-elim (<-irrefl ≡-refl (<-≤-trans m>n (≤-recompute m≤n)))

≤→<≡ : .(m ≤ n) → m < n ⊎ m ≡ n
≤→<≡ {m = m} {n = n} m≤n with <-cmp m n
... | tri< m<n _ _ = inj₁ m<n
... | tri≈ _ m≡n _ = inj₂ m≡n
... | tri> _ _ m>n = ⊥-elim (<-irrefl ≡-refl (<-≤-trans m>n (≤-recompute m≤n)))

<≡→≤ : m < n ⊎ m ≡ n → m ≤ n
<≡→≤ (inj₁ m<n) = <→≤ m<n
<≡→≤ (inj₂ m≡n) = ≤-reflexive m≡n

≤-+-split : ∀ m n o p → .(m + n ≤ o + p) → WeakTri (m < o) (m ≡ o × n ≡ p) (n < p)
≤-+-split m n o p m+n≤o+p with ≤-cmp o m | ≤-cmp p n
... | inj₂ m<o | _ = cmp₁ m<o
... | inj₁ m≥o | inj₂ n<p = cmp₃ n<p
... | inj₁ m≥o | inj₁ n≥p = cmp₂ (≤-antisym (begin
        m           ≡⟨ ≡-sym (m+n∸n≡m m n) ⟩
        m + n ∸ n   ≤⟨ ∸-mono m+n≤o+p n≥p ⟩
        o + p ∸ p   ≡⟨ m+n∸n≡m o p ⟩
        o           ∎) m≥o ,
    ≤-antisym (begin
        n           ≡⟨ ≡-sym (m+n∸m≡n m n) ⟩
        m + n ∸ m   ≤⟨ ∸-mono m+n≤o+p m≥o ⟩
        o + p ∸ o   ≡⟨ m+n∸m≡n o p ⟩
        p           ∎) n≥p)
    where open ≤-Reasoning

-- not tight
≤-+-split' : ∀ m n o p → .(m + n ≤ o + p) → (m ≤ o) ⊎ (n ≤ p)
≤-+-split' m n o p m+n≤o+p with ≤-+-split m n o p m+n≤o+p
... | cmp₁ m<o = inj₁ (<⇒≤ m<o)
... | cmp₂ (m=o , _) = inj₁ (≤-reflexive m=o)
... | cmp₃ n<p = inj₂ (<⇒≤ n<p)

<-+-split : ∀ m n o p → .(m + n < o + p) → m < o ⊎ n < p
<-+-split m n o p m+n<o+p with ≤-cmp o m
... | inj₂ m<o = inj₁ m<o
... | inj₁ m≥o = inj₂ (begin
    suc n               ≡⟨ ≡-sym (m+n∸m≡n m (suc n)) ⟩
    m + suc n ∸ m       ≡⟨ cong (_∸ m) (+-suc m n) ⟩
    suc (m + n) ∸ m     ≤⟨ ∸-mono m+n<o+p m≥o ⟩
    o + p ∸ o           ≡⟨ m+n∸m≡n o p ⟩
    p                   ∎)
    where open ≤-Reasoning

≤-+-split₃ : ∀ m n o p q r → .(m + n + o ≤ p + q + r) → (m ≡ p × n ≡ q × o ≡ r) ⊎ WeakTri (m < p) (n < q) (o < r)
≤-+-split₃ m n o p q r ≤-thing with ≤-+-split (m + n) o (p + q) r ≤-thing
... | cmp₃ o<r = inj₂ (cmp₃ o<r)
... | cmp₁ m+n<p+q with <-+-split m n p q m+n<p+q
...     | inj₁ m<p = inj₂ (cmp₁ m<p)
...     | inj₂ n<q = inj₂ (cmp₂ n<q)
≤-+-split₃ m n o p q r ≤-thing
    | cmp₂ (m+n=p+q , o=r) with ≤-+-split m n p q (≤-reflexive m+n=p+q)
...     | cmp₁ m<p = inj₂ (cmp₁ m<p)
...     | cmp₂ (m=p , n=q) = inj₁ (m=p , n=q , o=r)
...     | cmp₃ o<r = inj₂ (cmp₂ o<r)

<-+-split₃ : ∀ m n o p q r → .(m + n + o < p + q + r) → WeakTri (m < p) (n < q) (o < r)
<-+-split₃ m n o p q r <-thing with <-+-split (m + n) o (p + q) r <-thing
... | inj₂ o<r = cmp₃ o<r
... | inj₁ m+n<p+q with <-+-split m n p q m+n<p+q
...     | inj₁ m<p = cmp₁ m<p
...     | inj₂ n<q = cmp₂ n<q


max≥fst : max m n ≥ m
max≥fst {m} {n} with m ≤? n
... | yes m≤n = m≤n
... | no _ = n≤n

max≥snd : max m n ≥ n
max≥snd {m} {n} with m ≤? n
... | yes _ = n≤n
... | no ¬m≤n with <-cmp m n
...     | tri< m<n _ _ = ⊥-elim (¬m≤n (<→≤ m<n))
...     | tri≈ _ m≡n _ = ≤-reflexive (≡-sym m≡n)
...     | tri> _ _ m>n = ≤-trans n≤sn m>n

s≡s⁻¹ : suc m ≡ suc n → m ≡ n
s≡s⁻¹ ≡-refl = ≡-refl

∸-suc-≤ : (m n : ℕ) → (suc m ∸ n) ≤ suc (m ∸ n)
∸-suc-≤ m zero = ≤-refl
∸-suc-≤ zero (suc n) = ≤-trans (≤-reflexive (0∸n≡0 n)) z≤n
∸-suc-≤ (suc m) (suc n) = ∸-suc-≤ m n

m∸n<m : ∀ m n .{{_ : NonZero m}} .{{_ : NonZero n}} → m ∸ n < m
m∸n<m (suc m) (suc n) = s≤s (m∸n≤m m n)

m∸n≤o⇒m≤o+n : ∀ m n o → m ∸ n ≤ o → m ≤ o + n
m∸n≤o⇒m≤o+n m zero o m≤o = ≤-trans m≤o (≤-reflexive (+-comm 0 o))
m∸n≤o⇒m≤o+n zero (suc n) o m∸n≤o = z≤n
m∸n≤o⇒m≤o+n (suc m) (suc n) o m∸n≤o = ≤-trans (+-mono-≤ {1} ≤-refl (m∸n≤o⇒m≤o+n m n o m∸n≤o)) (≤-reflexive (≡-sym (+-suc o n)))

m+n+o=m+o+n : ∀ m n o → m + n + o ≡ m + o + n
m+n+o=m+o+n m n o =
    m + n + o       ≡⟨ +-assoc m n o ⟩
    m + (n + o)     ≡⟨ cong (m +_) (+-comm n o) ⟩
    m + (o + n)     ≡⟨ ≡-sym (+-assoc m o n) ⟩
    m + o + n       ∎
    where open ≡-Reasoning

m=n+o⇒m∸o=n : ∀ m n o → m ≡ n + o → m ∸ o ≡ n
m=n+o⇒m∸o=n m n o m=n+o =
    m ∸ o       ≡⟨ cong (_∸ o) m=n+o ⟩
    n + o ∸ o   ≡⟨ m+n∸n≡m n o ⟩
    n           ∎
    where open ≡-Reasoning

m∸n+n≡m⊔n : ∀ m n → m ∸ n + n ≡ m ⊔ n
m∸n+n≡m⊔n m n with ≤-cmp n m
... | inj₁ n≤m =
    m ∸ n + n   ≡⟨ m∸n+n≡m n≤m ⟩
    m           ≡⟨ ≡-sym (m≥n⇒m⊔n≡m n≤m) ⟩
    m ⊔ n       ∎
    where open ≡-Reasoning
... | inj₂ n>m =
    m ∸ n + n   ≡⟨ cong (_+ n) (m≤n⇒m∸n≡0 (<⇒≤ n>m)) ⟩
    0 + n       ≡⟨⟩
    n           ≡⟨ ≡-sym (m≤n⇒m⊔n≡n (<⇒≤ n>m)) ⟩
    m ⊔ n       ∎
    where open ≡-Reasoning

+-∸-telescope : (m n o : ℕ) → .(m ≥ n) → .(n ≥ o) → (m ∸ n) + (n ∸ o) ≡ m ∸ o
+-∸-telescope m n o m≥n n≥o =
    (m ∸ n) + (n ∸ o)   ≡⟨ ≡-sym (+-∸-assoc (m ∸ n) {n} {o} n≥o) ⟩
    (m ∸ n + n) ∸ o     ≡⟨ cong (_∸ o) (m∸n+n≡m {m} {n} m≥n) ⟩
    m ∸ o               ∎
    where open ≡-Reasoning

m∸[n∸o]=m+o∸n : ∀ m n o → .(o ≤ n) → m ∸ (n ∸ o) ≡ (m + o) ∸ n
m∸[n∸o]=m+o∸n zero n o o≤n = ≡-trans (0∸n≡0 (n ∸ o)) (≡-sym (m≤n⇒m∸n≡0 {o} {n} o≤n))
m∸[n∸o]=m+o∸n (suc m) n zero o≤n = cong (_∸ n) (+-comm 0 (suc m))
m∸[n∸o]=m+o∸n (suc m) (suc n) (suc o) o≤n = ≡-trans (m∸[n∸o]=m+o∸n (suc m) n o (s≤s⁻¹ o≤n)) (cong (_∸ n) (≡-sym (+-suc m o)))

m∸n∸o≡m∸[n+o] : (m n o : ℕ) → m ∸ n ∸ o ≡ m ∸ (n + o)
m∸n∸o≡m∸[n+o] _ zero _ = ≡-refl
m∸n∸o≡m∸[n+o] zero (suc n') zero = ≡-refl
m∸n∸o≡m∸[n+o] zero (suc n') (suc o') = ≡-refl
m∸n∸o≡m∸[n+o] (suc m') (suc n') zero = cong (λ x → m' ∸ x) (+-comm 0 n')
m∸n∸o≡m∸[n+o] (suc m') (suc n') (suc o') = m∸n∸o≡m∸[n+o] m' n' (suc o')

m+[n∸o]=m∸o+n : ∀ m n o → .(o ≤ m) → .(o ≤ n) → m + (n ∸ o) ≡ (m ∸ o) + n
m+[n∸o]=m∸o+n m n zero o≤m o≤n = ≡-refl
m+[n∸o]=m∸o+n m@(suc m') n@(suc n') o@(suc o') o≤m o≤n =
    suc (m' + (n ∸ suc o'))     ≡⟨ ≡-sym (+-suc m' (n ∸ suc o')) ⟩
    m' + suc (n ∸ suc o')       ≡⟨ cong (m' +_) (∸-suc n' o' (s≤s⁻¹ o≤n)) ⟩
    m' + (n ∸ o')               ≡⟨ m+[n∸o]=m∸o+n m' n o' (s≤s⁻¹ o≤m) (≤-trans n≤sn o≤n) ⟩
    m' ∸ o' + n                 ∎
    where open ≡-Reasoning

m∸sn∸o≡m∸n∸so : (m n o : ℕ) → m ∸ suc n ∸ o ≡ m ∸ n ∸ suc o
m∸sn∸o≡m∸n∸so m n o =
    m ∸ suc n ∸ o   ≡⟨ m∸n∸o≡m∸[n+o] m (suc n) o ⟩
    m ∸ (suc n + o) ≡⟨ ≡-sym (cong (λ x → m ∸ x) (+-suc n o)) ⟩
    m ∸ (n + suc o) ≡⟨ ≡-sym (m∸n∸o≡m∸[n+o] m n (suc o)) ⟩
    m ∸ n ∸ suc o   ∎
    where open ≡-Reasoning

m∸n∸o≡m∸o∸n : (m n o : ℕ) → m ∸ n ∸ o ≡ m ∸ o ∸ n
m∸n∸o≡m∸o∸n m n o =
    m ∸ n ∸ o   ≡⟨ m∸n∸o≡m∸[n+o] m n o ⟩
    m ∸ (n + o) ≡⟨ cong (λ a → m ∸ a) (+-comm n o) ⟩
    m ∸ (o + n) ≡⟨ ≡-sym (m∸n∸o≡m∸[n+o] m o n) ⟩
    m ∸ o ∸ n   ∎
    where open ≡-Reasoning

sm∸n≡so→m∸n≡o : (m n : ℕ) → {o : ℕ} → suc m ∸ n ≡ suc o → m ∸ n ≡ o
sm∸n≡so→m∸n≡o m n {o} sm-n=so =
    m ∸ n                   ≡⟨⟩
    (suc m ∸ suc zero) ∸ n  ≡⟨ m∸n∸o≡m∸o∸n (suc m) (suc zero) n ⟩
    (suc m ∸ n) ∸ suc zero  ≡⟨ cong (λ x → x ∸ suc zero) sm-n=so ⟩
    (suc o) ∸ suc zero      ≡⟨⟩
    o ∎
    where open ≡-Reasoning

[n∸m]∸[o∸m]=n∸o : ∀ m n o → .(m ≤ o) → n ∸ m ∸ (o ∸ m) ≡ n ∸ o
[n∸m]∸[o∸m]=n∸o m n o m≤o =
    n ∸ m ∸ (o ∸ m)     ≡⟨ m∸n∸o≡m∸[n+o] n m (o ∸ m) ⟩
    n ∸ (m + (o ∸ m))   ≡⟨ cong (n ∸_) (m+[n∸m]≡n {m} {o} m≤o) ⟩
    n ∸ o               ∎
    where open ≡-Reasoning

m≢0→m≡sn : .(m ≢ 0) → Σ ℕ λ n → m ≡ suc n
m≢0→m≡sn {m = zero} z≢z = ⊥-elim ((≢-recompute z≢z) ≡-refl)
m≢0→m≡sn {m = suc m'} _ = m' , ≡-refl

m≡spm : .(m ≢ 0) → m ≡ suc (pred m)
m≡spm {m = m} m≢0 with m≢0→m≡sn m≢0
m≡spm {m = m} m≢0 | m' , m≡sm' =
    m                   ≡⟨ m≡sm' ⟩
    suc m'              ≡⟨⟩
    suc (suc m' ∸ 1)    ≡⟨ cong (λ x → suc (x ∸ 1)) (≡-sym m≡sm') ⟩
    suc (m ∸ 1)         ∎
    where open ≡-Reasoning

n=spn : .{{NonZero n}} → n ≡ suc (pred n)
n=spn {suc n} = ≡-refl

n≤spn : ∀ n → n ≤ suc (pred n)
n≤spn zero = z≤n
n≤spn (suc n) = ≤-refl

m/n/o=m/[n*o] : ∀ m n o  .{{_ : NonZero n}} .{{_ : NonZero o}} .{{_ : NonZero (n * o)}} →
    n * o ∣ m →
    m / n / o ≡ m / (n * o)
m/n/o=m/[n*o] m n o n*o∣m@(divides k m=k*[n*o]) =
    m / n / o                   ≡⟨ /-congˡ {o} (/-congˡ {n} (
        m               ≡⟨ m=k*[n*o] ⟩
        k * (n * o)     ≡⟨ cong (k *_) (*-comm n o) ⟩
        k * (o * n)     ≡⟨ ≡-sym (*-assoc k o n) ⟩
        k * o * n       ∎)) ⟩
    (k * o * n) / n / o         ≡⟨ /-congˡ {o} (m*n/n≡m (k * o) n) ⟩
    (k * o) / o                 ≡⟨ m*n/n≡m k o ⟩
    k                           ≡⟨ ≡-sym (m*n/n≡m k (n * o)) ⟩
    (k * (n * o)) / (n * o)     ≡⟨ /-congˡ {n * o} (≡-sym m=k*[n*o]) ⟩
    m / (n * o)                 ∎
    where open ≡-Reasoning

monotonic⇒injective : (f : ℕ → ℕ) → .(∀ {m n} → m < n → f m < f n) → Injective _≡_ _≡_ f
monotonic⇒injective f f-monotonic {m} {n} fm=fn with <-cmp m n
... | tri< m<n ¬m=n ¬m>n = ⊥-irr-elim (<-irrefl fm=fn (f-monotonic m<n))
... | tri≈ ¬m<n m=n ¬m>n = m=n
... | tri> ¬m<n ¬m=n m>n = ⊥-irr-elim (<-irrefl (≡-sym fm=fn) (f-monotonic m>n))

-- m<s[m/n]*n : ∀ m n .{{_ : NonZero n}} → m < suc (m / n) * n
-- m<s[m/n]*n m n@(suc n') = begin
--     suc m                       ≡⟨ cong suc (m≡m%n+[m/n]*n m n) ⟩
--     suc (m % n + m / n * n)     ≡⟨⟩
--     suc (m % n) + m / n * n     ≤⟨ +-mono-≤ {suc (m % n)} {n} {m / n * n} (m%n<n m n) ≤-refl ⟩
--     n + m / n * n               ≡⟨⟩
--     suc (m / n) * n             ∎
--     where open ≤-Reasoning

[m+n]/n=1+m/n : ∀ m n → .{{_ : NonZero n}} → (m + n) / n ≡ 1 + m / n
[m+n]/n=1+m/n m n =
    (m + n) / n             ≡⟨ m/n≡1+[m∸n]/n {m + n} {n} (+-mono-≤ {0} {m} {n} {n} z≤n n≤n) ⟩
    1 + (m + n ∸ n) / n     ≡⟨ cong (λ q → 1 + q / n) (m+n∸n≡m m n) ⟩
    1 + m / n               ∎
    where open ≡-Reasoning

[m*n+i]/n=i : {m n i : ℕ} → .{{_ : NonZero n}} → .(i < n) → (m * n + i) / n ≡ m
[m*n+i]/n=i {m} {n@(suc n')} {i} i<n =
    (m * n + i) / n     ≡⟨ +-distrib-/-∣ˡ {m * n} i {n} (divides m ≡-refl) ⟩
    m * n / n + i / n   ≡⟨ cong (_+ i / n) (m*n/n≡m m n) ⟩
    m + i / n           ≡⟨ cong (m +_) ((m<n⇒m/n≡0 {i} {n} i<n)) ⟩
    m + zero            ≡⟨ +-comm m zero ⟩
    m                   ∎
    where open ≡-Reasoning

m=n*o⇒m/n=o : ∀ m n o .{{_ : NonZero n}} → m ≡ n * o → m / n ≡ o
m=n*o⇒m/n=o m n o m=n*o = n/m≡quotient {n} {m} (divides o (≡-trans m=n*o (*-comm n o)))

*-mono-∣ : ∀ {m n o p} → m ∣ o → n ∣ p → m * n ∣ o * p
*-mono-∣ {m} {n} {o} {p} m∣o@(divides i o=i*m) n∣p@(divides j p=j*n) = divides (i * j) (
    o * p               ≡⟨ cong₂ _*_ o=i*m p=j*n ⟩
    (i * m) * (j * n)   ≡⟨ *-assoc i m (j * n) ⟩
    i * (m * (j * n))   ≡⟨ cong (i *_) (≡-sym (*-assoc m j n)) ⟩
    i * ((m * j) * n)   ≡⟨ cong (i *_) (cong (_* n) (*-comm m j)) ⟩
    i * ((j * m) * n)   ≡⟨ cong (i *_) (*-assoc j m n) ⟩
    i * (j * (m * n))   ≡⟨ ≡-sym (*-assoc i j (m * n)) ⟩
    i * j * (m * n)     ∎)
    where open ≡-Reasoning


quotient-nonZero : {m n : ℕ} → .{{_ : NonZero m}} → .{{_ : NonZero n}} → n ∣ m → NonZero (m / n)
quotient-nonZero m@{suc m'} {n} {{m-nonZero}} {{n-nonZero}} (divides q m=q*n) = change-type (cong NonZero q=m/n) q-nonZero
    where
        q=m/n : q ≡ m / n
        q=m/n = ≡-trans (≡-sym (m*n/n≡m q n)) (/-congˡ (≡-sym m=q*n))

        instance
            q*n-nonZero : NonZero (q * n)
            q*n-nonZero = change-type (cong NonZero m=q*n) (record { nonZero = tt })

        q-nonZero : NonZero q
        q-nonZero = m*n≢0⇒m≢0 q {n}

/-distribʳ-% : (m n o : ℕ) → .{{_ : NonZero n}} .{{_ : NonZero o}} →
    (o ∣ n) →
    .{{_ : NonZero (n / o)}} →
    m % n / o ≡ (m / o) % (n / o)
/-distribʳ-% m n o {{n-nonZero}} o∣n@(divides q n=q*o) =
    m % n / o           ≡⟨ /-congˡ (%-congʳ n=q*o) ⟩
    m % (q * o) / o     ≡⟨ m%[n*o]/o≡m/o%n m q o ⟩
    (m / o) % q         ≡⟨ %-congʳ {q} {n / o} {m / o} q=n/o ⟩
    ((m / o) % (n / o)) ∎
    where
        open ≡-Reasoning

        q=n/o : q ≡ n / o
        q=n/o = ≡-trans (≡-sym (m*n/n≡m q o)) (/-congˡ (≡-sym n=q*o))

        instance
            q*o-nonZero : NonZero (q * o)
            q*o-nonZero = NonZero-recompute (change-type (cong NonZero n=q*o) n-nonZero)

            q-nonZero : NonZero q
            q-nonZero = m*n≢0⇒m≢0 q {o}

            q*o/o-nonZero : NonZero (q * o / o)
            q*o/o-nonZero = change-type (cong NonZero (≡-sym (m*n/n≡m q o))) q-nonZero

            n/o-nonZero : NonZero (n / o)
            n/o-nonZero = change-type (cong NonZero q=n/o) q-nonZero

[m+kn]/n≡k+m/n : ∀ m k n .{{_ : NonZero n}} → (m + k * n) / n ≡ k + m / n
[m+kn]/n≡k+m/n m zero n = cong (_/ n) (+-comm m 0)
[m+kn]/n≡k+m/n m k@(suc k') n =
    (m + k * n) / n                 ≡⟨ m/n≡1+[m∸n]/n {m + k * n} {n} (≤-trans (m≤m+n n (k' * n)) (m≤n+m (k * n) m)) ⟩
    1 + (m + k * n ∸ n) / n         ≡⟨ cong (λ q → 1 + q / n) (+-∸-assoc m {k * n} {n} (m≤m+n n (k' * n))) ⟩
    1 + (m + (k * n ∸ n)) / n       ≡⟨ cong (λ q → 1 + (m + (k * n ∸ q)) / n) (≡-sym (*-identity .proj₁ n)) ⟩
    1 + (m + (k * n ∸ 1 * n)) / n   ≡⟨ cong (λ q → 1 + (m + q) / n) (≡-sym (*-distrib-∸ .proj₂ n k 1)) ⟩
    1 + (m + (k ∸ 1) * n) / n       ≡⟨⟩
    1 + (m + k' * n) / n            ≡⟨ cong suc ([m+kn]/n≡k+m/n m k' n) ⟩
    1 + (k' + m / n)                ≡⟨ +-assoc 1 k' (m / n) ⟩
    (1 + k') + m / n                ≡⟨⟩
    k + m / n                       ∎
    where open ≡-Reasoning

[kn+m]/n≡k+m/n : ∀ k n m .{{_ : NonZero n}} → (k * n + m) / n ≡ k + m / n
[kn+m]/n≡k+m/n k n m =
    (k * n + m) / n     ≡⟨ cong (_/ n) (+-comm (k * n) m) ⟩
    (m + k * n) / n     ≡⟨ [m+kn]/n≡k+m/n m k n ⟩
    k + m / n           ∎
    where open ≡-Reasoning

m∣n⇒m≤n : ∀ m n .{{_ : NonZero m}} .{{_ : NonZero n}} → m ∣ n → m ≤ n
m∣n⇒m≤n m n {{_}} {{n-nonZero}} (divides k n=k*m) = ≤-trans (m≤n*m m k) (≤-reflexive (≡-sym n=k*m))
    where
        instance
            k-nonZero : NonZero k
            k-nonZero = m*n≢0⇒m≢0 k {m} {{change-type (cong NonZero n=k*m) n-nonZero}}

m*n≤o⇒m*n≤o/n*n : ∀ m n o .{{_ : NonZero n}} → m * n ≤ o → m * n ≤ o / n * n
m*n≤o⇒m*n≤o/n*n m n o m*n≤o with ≤-cmp (m * n) (o / n * n)
... | inj₁ pf = pf
... | inj₂ m*n>o/n*n = ⊥-elim (<-irrefl ≡-refl (≤-<-trans m≤o/n m>o/n))
    where
        m>o/n : m > o / n
        m>o/n = *-cancelʳ-< n (o / n) m m*n>o/n*n

        m≤o/n : m ≤ o / n
        m≤o/n = begin
            m           ≡⟨ ≡-sym (m*n/n≡m m n) ⟩
            m * n / n   ≤⟨ /-mono-≤ {n} {n} {m * n} {o} m*n≤o ≤-refl ⟩
            o / n       ∎
            where open ≤-Reasoning

missing-part-< : ∀ m n o p → .(m < o) → o ∣ p → .(n * o < p) → m + n * o < p
missing-part-< m n o@(suc o') p@(suc p') m<o n∣p@(divides k p=k*o) n*o<p = begin
    suc m + n * o   ≤⟨ +-mono-≤ {suc m} {o} m<o ≤-refl ⟩
    o + n * o       ≡⟨⟩
    (suc n) * o     ≤⟨ *-mono-≤ {suc n} {k} {o} (*-cancelʳ-< o n k (<-≤-trans n*o<p (≤-reflexive p=k*o))) ≤-refl ⟩
    k * o           ≡⟨ ≡-sym p=k*o ⟩
    p               ∎
    where open ≤-Reasoning

[m∸kn]%n≡m%n : ∀ m k n .{{_ : NonZero n}} → .(m ≥ k * n) → (m ∸ k * n) % n ≡ m % n
[m∸kn]%n≡m%n m k n m≥kn =
    (m ∸ k * n) % n             ≡⟨ ≡-sym ([m+kn]%n≡m%n (m ∸ k * n) k n) ⟩
    (m ∸ k * n + k * n) % n     ≡⟨ cong (_% n) (m∸n+n≡m m≥kn) ⟩
    m % n                       ∎
    where open ≡-Reasoning

[m∸n]%n≡m%n : ∀ m n .{{_ : NonZero n}} → .(m ≥ n) → (m ∸ n) % n ≡ m % n
[m∸n]%n≡m%n m n m≥n =
    (m ∸ n) % n         ≡⟨ cong (λ q → (m ∸ q) % n) (≡-sym (*-identity .proj₁ n)) ⟩
    (m ∸ 1 * n) % n     ≡⟨ [m∸kn]%n≡m%n m 1 n (≤-trans (≤-reflexive (*-identity .proj₁ n)) m≥n) ⟩
    m % n               ∎
    where open ≡-Reasoning

m%n%o=m%n : (m n o : ℕ) → .{{_ : NonZero n}} → .{{_ : NonZero o}} →
    n ≤ o →
    m % n % o ≡ m % n
m%n%o=m%n m n o n≤o = m<n⇒m%n≡m {o} {m % n} (<-≤-trans (m%n<n m n) n≤o)

m%n%o=m%o : (m n o : ℕ) → .{{_ : NonZero n}} → .{{_ : NonZero o}} →
    o ∣ n →
    m % n % o ≡ m % o
m%n%o=m%o m n o (divides k n=k*o) =
    m % n % o                   ≡⟨ %-congˡ {o} (m%n≡m∸m/n*n m n) ⟩
    (m ∸ m / n * n) % o         ≡⟨ cong (λ q → (m ∸ q) % o) thing ⟩
    (m ∸ m / n * k * o) % o     ≡⟨ [m∸kn]%n≡m%n m (m / n * k) o (≤-trans (≤-reflexive (≡-sym thing)) (m/n*n≤m m n)) ⟩
    m % o                       ∎
    where
        open ≡-Reasoning
        thing : m / n * n ≡ m / n * k * o
        thing =
            m / n * n           ≡⟨ cong (m / n *_) n=k*o ⟩
            m / n * (k * o)     ≡⟨ ≡-sym (*-assoc (m / n) k o) ⟩
            m / n * k * o       ∎

*-distribʳ-% : ∀ m n o .{{_ : NonZero o}} .{{_ : NonZero (m * o)}} → m * (n % o) ≡ (m * n) % (m * o)
*-distribʳ-% m n o =
    m * (n % o)                             ≡⟨ cong (m *_) (m%n≡m∸m/n*n n o) ⟩
    m * (n ∸ n / o * o)                     ≡⟨ *-distrib-∸ .proj₁ m n (n / o * o) ⟩
    m * n ∸ m * (n / o * o)                 ≡⟨ cong (m * n ∸_) (*-comm m (n / o * o)) ⟩
    m * n ∸ (n / o * o) * m                 ≡⟨ cong (m * n ∸_) (*-assoc (n / o) o m) ⟩
    m * n ∸ (n / o) * (o * m)               ≡⟨ cong (λ q → m * n ∸ (n / o) * q) (*-comm o m) ⟩
    m * n ∸ (n / o) * (m * o)               ≡⟨ cong (λ q → m * n ∸ q * (m * o)) (≡-sym (m*n/m*o≡n/o m n o)) ⟩
    m * n ∸ (m * n) / (m * o) * (m * o)     ≡⟨ ≡-sym (m%n≡m∸m/n*n (m * n) (m * o)) ⟩
    (m * n) % (m * o)                       ∎
    where open ≡-Reasoning

*-distribˡ-% : ∀ m n o .{{_ : NonZero o}} .{{_ : NonZero (o * m)}} → (n % o) * m ≡ (n * m) % (o * m)
*-distribˡ-% m n o {{_}} {{o*m-nonZero}} =
    (n % o) * m         ≡⟨ *-comm (n % o) m ⟩
    m * (n % o)         ≡⟨ *-distribʳ-% m n o ⟩
    (m * n) % (m * o)   ≡⟨ cong (_% (m * o)) (*-comm m n) ⟩
    (n * m) % (m * o)   ≡⟨ %-congʳ {o = n * m} (*-comm m o) ⟩
    (n * m) % (o * m)   ∎
    where
        open ≡-Reasoning
        instance
            m*o-nonZero : NonZero (m * o)
            m*o-nonZero = NonZero-recompute (subst NonZero (*-comm o m) o*m-nonZero)

%-/*-commute : ∀ m n o .{{_ : NonZero n}} .{{_ : NonZero o}} → n ∣ o → m / n * n % o ≡ m % o / n * n
%-/*-commute m n o@(suc o') (divides k o=k*n) =
    m / n * n % o               ≡⟨ %-congʳ {o} {k * n} {m / n * n} o=k*n ⟩
    m / n * n % (k * n)         ≡⟨ ≡-sym (*-distribˡ-% n (m / n) k) ⟩
    m / n % k * n               ≡⟨ cong (_* n) (≡-sym (m%[n*o]/o≡m/o%n m k n)) ⟩
    m % (k * n) / n * n         ≡⟨ cong (λ q → q / n * n) (%-congʳ (≡-sym o=k*n)) ⟩
    m % o / n * n ∎
    where
        open ≡-Reasoning
        instance
            kn-nonZero : NonZero (k * n)
            kn-nonZero = subst NonZero {o} o=k*n _

            k-nonZero : NonZero k
            k-nonZero = *-factor₁-nonZero k n

            k/n*n-nonZero : NonZero (k * n / n)
            k/n*n-nonZero = change-type (cong NonZero (≡-trans (≡-sym (m*n/n≡m k n)) ≡-refl)) (m*n≢0⇒m≢0 k)

{-
    Intuition:
    Consider a digit in a multi-base numeral

    Lower sig ---> Higher sig
    Base:   3   5   8   7   13
    Num:    1   2   3   4   5

    So this would be the number 1 + 2 * (3) + 3 * (5 * 3) + 4 * (8 * 5 * 3) + 5 * (7 * 8 * 5 * 3)

    Consider the goal of extracting a digit from this number. In particular, suppose we want the third digit (so the 3).

    One way to do it is:
    divide by the lower base (3 * 5)
    giving us the number
    Base:   8   7   13
    Num:    3   4   5
    and the modulo by the digit base 8, giving us 3

    but alternatively, we could crop off the higher digits first, moduloing by (3 * 5 * 8 * 7), giving us the number
    Base:   3   5   8   7
    Num:    1   2   3   4
    and then divide by (3 * 5)
    Base:   8   7
    Num:    3   4
    and then modulo again to get 3.

    note the smaller modulo and divide both divide the big initial modulo. I think that is key to how this works.
-}
[[m%n]/o]%p=[m/o]%p : {m n o p : ℕ} → .{{_ : NonZero n}} .{{_ : NonZero o}} .{{_ : NonZero p}} →
    o * p ∣ n →
    ((m % n) / o) % p ≡ (m / o) % p
[[m%n]/o]%p=[m/o]%p {m} {n} {o} {p} o*p∣n@(divides q n=q*[o*p]) =
    m % n / o % p           ≡⟨ %-congˡ (/-distribʳ-% m n o o∣n) ⟩
    (m / o) % (n / o) % p   ≡⟨ m∣n⇒o%n%m≡o%m p (n / o) (m / o) p∣n/o ⟩
    m / o % p               ∎
    where
        open ≡-Reasoning

        n=q*p*o : n ≡ q * p * o
        n=q*p*o =
            n               ≡⟨ n=q*[o*p] ⟩
            q * (o * p)     ≡⟨ cong (q *_) (*-comm o p) ⟩
            q * (p * o)     ≡⟨ ≡-sym (*-assoc q p o) ⟩
            (q * p) * o     ∎

        o∣n : o ∣ n
        o∣n = divides (q * p) n=q*p*o

        p∣n/o : p ∣ n / o
        p∣n/o = divides q (
            n / o           ≡⟨ /-congˡ n=q*p*o ⟩
            q * p * o / o   ≡⟨ m*n/n≡m (q * p) o ⟩
            q * p           ∎)
        instance
            n/o-nonZero : NonZero (n / o)
            n/o-nonZero = quotient-nonZero o∣n

≃-mod-respʳ-flip-∣ : ∀ {m n} o p .{{_ : NonZero m}} .{{_ : NonZero n}} → m ∣ n → o % n ≡ p % n → o % m ≡ p % m
≃-mod-respʳ-flip-∣ {m} {n} o p m∣n o%n=p%n =
    o % m       ≡⟨ ≡-sym (m%n%o=m%o o n m m∣n) ⟩
    o % n % m   ≡⟨ %-congˡ {m} o%n=p%n ⟩
    p % n % m   ≡⟨ m%n%o=m%o p n m m∣n ⟩
    p % m       ∎
    where open ≡-Reasoning

0%n=0 : ∀ n → .{{_ : NonZero n}} → 0 % n ≡ 0
0%n=0 (suc n) = ≡-refl

m+m*n=m*sn : (m n : ℕ) → m + m * n ≡ m * suc n
m+m*n=m*sn m n =
    m + m * n   ≡⟨ cong (m +_) (*-comm m n) ⟩
    m + n * m   ≡⟨⟩
    suc n * m   ≡⟨ *-comm (suc n) m ⟩
    m * suc n   ∎
    where open ≡-Reasoning

m*n*o=m*o*n : (m n o : ℕ) → m * n * o ≡ m * o * n
m*n*o=m*o*n m n o =
    (m * n) * o ≡⟨ *-assoc m n o ⟩
    m * (n * o) ≡⟨ cong (m *_) (*-comm n o) ⟩
    m * (o * n) ≡⟨ ≡-sym (*-assoc m o n) ⟩
    (m * o) * n ∎
    where open ≡-Reasoning

m≠0∧n≠0⇒m*n≠0 : ∀ m n → .{{NonZero m}} → .{{NonZero n}} → NonZero (m * n)
m≠0∧n≠0⇒m*n≠0 (suc m) (suc n) = record { nonZero = tt }

m∣n⇒n%m≡0 : ∀ {n m} .{{_ : NonZero m}} → m ∣ n → n % m ≡ 0
m∣n⇒n%m≡0 {n} {m} (divides k n=k*m) =
    n % m       ≡⟨ cong (_% m) n=k*m ⟩
    k * m % m   ≡⟨ m*n%n≡0 k m ⟩
    0           ∎
    where open ≡-Reasoning

sn%n=1 : ∀ n .{{_ : NonTrivial n}} .{{_ : NonZero n}} → suc n % n ≡ 1
sn%n=1 n@(suc (suc n'')) =
    suc n % n ≡⟨ %-congˡ {n} {suc n} {1 + 1 * n} (≡-sym (+-comm (suc n) 0)) ⟩
    (1 + 1 * n) % n ≡⟨ [m+kn]%n≡m%n 1 1 n ⟩
    1 ∎
    where open ≡-Reasoning

%-cong : ∀ {m n o p} .{{_ : NonZero o}} .{{_ : NonZero p}} → m ≡ n → o ≡ p → m % o ≡ n % p
%-cong ≡-refl ≡-refl = ≡-refl

*-/-exchange :
    ∀ {m n o p} .{{_ : NonZero o}} .{{_ : NonZero p}} .{{_ : NonZero (o * p)}} →
    o ∣ m → p ∣ n →
    (m * n) / (o * p) ≡ (m / o) * (n / p)
*-/-exchange {m} {n} {o} {p} o∣m p∣n =
    (m * n) / (o * p)   ≡⟨ /-congʳ {m = m * n} (*-comm o p) ⟩
    (m * n) / (p * o)   ≡⟨ ≡-sym (m/n/o=m/[n*o] (m * n) p o (subst (_∣ m * n) (*-comm o p) (*-mono-∣ o∣m p∣n))) ⟩
    (m * n) / p / o     ≡⟨ /-congˡ {o} (*-/-assoc m {n} {p} p∣n) ⟩
    m * (n / p) / o     ≡⟨ /-congˡ {o} (*-comm m (n / p)) ⟩
    (n / p) * m / o     ≡⟨ *-/-assoc (n / p) {m} {o} o∣m ⟩
    (n / p) * (m / o)   ≡⟨ *-comm (n / p) (m / o) ⟩
    (m / o) * (n / p)   ∎
    where
        open ≡-Reasoning
        instance
            po-nonZero : NonZero (p * o)
            po-nonZero = *-nonZero p o

module _
    (P : ℕ → Set ℓ)
    where

    inductive-step-type : Set ℓ
    inductive-step-type = ∀ n → P n → P (suc n)

    module _
        (IH : inductive-step-type)
        where

        induction : P 0 → ∀ n → P n
        induction P[0] zero = P[0]
        induction P[0] (suc n) = IH n (induction P[0] n)

        +-induction : ∀ m n → P m → P (n + m)
        +-induction m zero P[m] = P[m]
        +-induction m (suc n) P[m] = IH (n + m) (+-induction m n P[m])

        ≤-induction : ∀ {m n : ℕ} → m ≤ n → P m → P n
        ≤-induction {m = m} {n} m≤n P[m] = change-type (cong P (m∸n+n≡m m≤n)) (+-induction m (n ∸ m) P[m])


≤-proofs-equal : {pf₁ pf₂ : m ≤ n} → pf₁ ≡ pf₂
≤-proofs-equal {pf₁ = z≤n} {z≤n} = ≡-refl
≤-proofs-equal {pf₁ = s≤s pf₁} {s≤s pf₂} = cong s≤s ≤-proofs-equal

decide-range' : {ℓ : Level} (P : ℕ → Set ℓ) → Unary.Decidable P →
    (m n : ℕ) →
    Dec (Σ ℕ λ o → m ≤ o × o < n + m × P o)
decide-range' P P-dec m zero = no λ (i , m≤i , i<m , _) → <-irrefl ≡-refl (≤-<-trans m≤i i<m)
decide-range' P P-dec m (suc n) with P-dec (n + m)
... | yes P[n+m] = yes (n + m , m≤n+m m n , n<sn , P[n+m])
... | no ¬P[n+m] with decide-range' P P-dec m n
...     | yes (i , m≤i , i<n+m , P[i]) = yes (i , m≤i , <-trans i<n+m n<sn , P[i])
...     | no ¬range = no λ thing@(i , m≤i , i<s[n+m] , P[i]) → case ≤-cmp (n + m) i of λ { (inj₁ n+m≤i) → ¬P[n+m] (subst P (≤-antisym {i} {n + m} (s≤s⁻¹ i<s[n+m]) n+m≤i) P[i]); (inj₂ n+m>i) → ¬range (i , m≤i , n+m>i , P[i]) }

decide-range : {ℓ : Level} (P : ℕ → Set ℓ) → Unary.Decidable P →
    (m n : ℕ) →
    Dec (Σ ℕ λ o → m ≤ o × o < n × P o)
decide-range P P-dec m n with m ≤? n
... | no ¬m≤n = no λ (i , m≤i , i<n , _) → ¬m≤n (<⇒≤ (≤-<-trans m≤i i<n))
... | yes m≤n = subst (λ q → Dec (Σ ℕ λ o → m ≤ o × o < q × P o)) (m∸n+n≡m {n} {m} m≤n) (decide-range' P P-dec m (n ∸ m))

+n-injective : ∀ n → Injective _≡_ _≡_ (_+ n)
+n-injective n {i} {j} i+n=j+n = +-cancel-≡ .proj₂ n i j i+n=j+n

n+-injective : ∀ n → Injective _≡_ _≡_ (n +_)
n+-injective n {i} {j} n+i=n+j = +-cancel-≡ .proj₁ n i j n+i=n+j

n≤n! : ∀ n → n ≤ n !
n≤n! zero = z≤n
n≤n! n@(suc n') = begin
    n           ≤⟨ m≤m*n n (n' !) ⟩
    n * n' !    ≡⟨⟩
    n !         ∎
    where
        open ≤-Reasoning
        instance
            n'!-nonZero : NonZero (n' !)
            n'!-nonZero = >-nonZero (1≤n! n')

n<n! : ∀ n → .(n ≢ 1) → .(n ≢ 2) → n < n !
n<n! zero n≠1 n≠2 = s≤s z≤n
n<n! (suc zero) n≠1 n≠2 = ⊥-irr-elim (n≠1 ≡-refl)
n<n! (suc (suc zero)) n≠1 n≠2 = ⊥-irr-elim (n≠2 ≡-refl)
n<n! n@(suc n'@(suc n''@(suc n'''))) n≠1 n≠2 = begin
    suc n                       ≤⟨ m<m*n n 2 (s≤s (s≤s z≤n)) ⟩
    n * 2                       ≤⟨ *-monoʳ-≤ n {2} {n' * 1} (s≤s (s≤s z≤n)) ⟩
    n * (n' * 1)                ≤⟨ *-monoʳ-≤ n {n' * 1} {n' * (n'' * 1)} (*-monoʳ-≤ n' {1} {n'' * 1} (m≤n*m 1 n'')) ⟩
    n * (n' * (n'' * 1))        ≤⟨ *-monoʳ-≤ n (*-monoʳ-≤ n' (*-monoʳ-≤ n'' (1≤n! n'''))) ⟩
    n * (n' * (n'' * n''' !))   ≡⟨⟩
    n !                         ∎
    where open ≤-Reasoning

<≤-find : ∀ m n → m < n → Σ ℕ λ o → m < o × o ≤ n
<≤-find m n m<n = suc m , n<sn , m<n

⊓-selective : ∀ m n → m ⊓ n ≡ m ⊎ m ⊓ n ≡ n
⊓-selective zero n = inj₁ ≡-refl
⊓-selective (suc m) zero = inj₂ ≡-refl
⊓-selective (suc m) (suc n) with ⊓-selective m n
... | inj₁ m⊓n=m = inj₁ (cong suc m⊓n=m)
... | inj₂ m⊓n=n = inj₂ (cong suc m⊓n=n)

⊓-glb : (m n o : ℕ) → m ≤ n → m ≤ o → m ≤ n ⊓ o
⊓-glb m n o m≤n m≤o with ⊓-selective n o
... | inj₁ n⊓o=n = ≤-trans m≤n (≤-reflexive (≡-sym n⊓o=n))
... | inj₂ n⊓o=o = ≤-trans m≤o (≤-reflexive (≡-sym n⊓o=o))

⊔-selective : ∀ m n → m ⊔ n ≡ m ⊎ m ⊔ n ≡ n
⊔-selective zero n = inj₂ ≡-refl
⊔-selective (suc m) zero = inj₁ ≡-refl
⊔-selective (suc m) (suc n) with ⊔-selective m n
... | inj₁ m⊔n=m = inj₁ (cong suc m⊔n=m)
... | inj₂ m⊔n=n = inj₂ (cong suc m⊔n=n)

⊔-lub : ∀ m n o → n ≤ m → o ≤ m → n ⊔ o ≤ m
⊔-lub m n o n≤m o≤m with ⊔-selective n o
... | inj₁ n⊔o=n = ≤-trans (≤-reflexive n⊔o=n) n≤m
... | inj₂ n⊔o=o = ≤-trans (≤-reflexive n⊔o=o) o≤m

≤-⊓-semilattice : MeetSemilattice lzero lzero lzero
≤-⊓-semilattice = record {
    rawSemilattice = record {
        A = ℕ;
        _≈_ = _≡_;
        _≤_ = _≤_;
        _⊓_ = _⊓_;
        ≤-isPartialOrder = ≤-isPartialOrder;
        ⊓-cong = from-discrete-cong₂ (discrete-setoid ℕ) _⊓_
        };
    isSemilattice = record {
        ⊓≤₁ = m⊓n≤m;
        ⊓≤₂ = m⊓n≤n;
        ⊓-glb = ⊓-glb
        }
    }

≥-isPartialOrder : IsPartialOrder _≡_ _≥_
≥-isPartialOrder = IsPartialOrder-flip _≡_ ≡-isEquivalence _≤_ ≤-isPartialOrder

≥-⊔-semilattice : MeetSemilattice lzero lzero lzero
≥-⊔-semilattice = record {
    rawSemilattice = record {
        A = ℕ;
        _≈_ = _≡_;
        _≤_ = _≥_;
        _⊓_ = _⊔_;
        ≤-isPartialOrder = ≥-isPartialOrder;
        ⊓-cong = from-discrete-cong₂ (discrete-setoid ℕ) _⊔_
        };
    isSemilattice = record {
        ⊓≤₁ = m≤m⊔n;
        ⊓≤₂ = m≤n⊔m;
        ⊓-glb = ⊔-lub
        }
    }

^-nonZero : ∀ m n .{{_ : NonZero m}} → NonZero (m ^ n)
^-nonZero m zero = record { nonZero = tt }
^-nonZero m (suc n) = *-nonZero m (m ^ n)
    where instance m^n-nonZero = ^-nonZero m n

¬≤ᵇ⇒> : (m ≤ᵇ n) ≡ false → m > n
¬≤ᵇ⇒> ¬m≤ᵇn = ≰⇒> λ m≤n → form-T-false ¬m≤ᵇn (≤⇒≤ᵇ m≤n)

¬<ᵇ⇒≥ : (m <ᵇ n) ≡ false → m ≥ n
¬<ᵇ⇒≥ ¬m<ᵇn = ≮⇒≥ λ m<n → form-T-false ¬m<ᵇn (<⇒<ᵇ m<n)
