open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; cong₂; subst) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open import Relation.Binary using (Setoid; Rel; Reflexive; Symmetric; Transitive; IsEquivalence; Decidable)
open import Relation.Nullary using (Dec; yes; no)
open import Function using (Congruent; Bijective; Injective; Surjective)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Nat using (ℕ; suc; zero; _+_; _∸_; _*_; _/_; _%_; _^_; NonZero; _≤_; _≥_; _<_; _>_; _≤?_)
open import Data.Nat.Properties using (+-∸-comm; +-∸-assoc; ∸-+-assoc; *-distrib-∸; n∸n≡0; m+n∸m≡n; m+n∸n≡m; m≤m+n; m≤n+m; m<m+n; m<n⇒0<n∸m; ≤-reflexive; ≤-refl; ≤-trans; ≤-<-trans; <-≤-trans; <⇒≤; module ≤-Reasoning)
    renaming (+-assoc to +-assocℕ; +-comm to +-commℕ; +-identity to +-identityℕ;
    *-identity to *-identityℕ; *-assoc to *-assocℕ; *-comm to *-commℕ; *-zero to *-zeroℕ; *-distrib-+ to *-distribℕ-+)
open import Data.Nat.DivMod using ([m+kn]%n≡m%n; [m+n]%n≡m%n; %-congˡ; %-congʳ; %-distribˡ-+; %-distribˡ-*; m/n*n≡m; m≡m%n+[m/n]*n; m%n<n; m%n≤n; m%n≤m; m<n⇒m%n≡m; m%n%n≡m%n)
open import Data.Nat.Divisibility using (_∣_; divides)
open import Data.Fin using (Fin; toℕ; fromℕ<) renaming (zero to zero-fin; suc to suc-fin)
open import Data.Fin.Properties using (toℕ-fromℕ<; fromℕ<-toℕ; fromℕ<-cong; toℕ<n)

open import Plasmaduck.SetoidExperiment.SetoidMachinery using (SetoidFunction₂; _which-is-cong₂_; _←₂_; SetoidFunction; _which-is-cong_; discrete-setoid; from-discrete-cong)
open import Plasmaduck.Counting.Counting using (IsFinite; HasSize)
open import Plasmaduck.Data.PropositionalEquality using (≡-isEquivalence)
open import Plasmaduck.Data.Nat using (m∸n+n≡m; ≤-cmp; m+[n∸o]=m∸o+n; [m∸kn]%n≡m%n; +-mono-≤; ∸-mono; m+[n∸m]≡n; ∸-suc)
open import Plasmaduck.Function.Properties using (Congruent₂; RightInverse; LeftInverse)
open import Plasmaduck.Function.InjectionSurjection using (both-inv→bijective)
open import Plasmaduck.Algebra.Group.Defs using (AbelianGroup)



module Plasmaduck.Number.NatModSetoid (mod : ℕ) .{{_ : NonZero mod}} where

infix 4 _≃_
_≃_ : Rel ℕ lzero
m ≃ n = m % mod ≡ n % mod

≃-reflexive : _≡_ Relation.Binary.⇒ _≃_
≃-reflexive ≡-refl = ≡-refl

≃-refl : Reflexive _≃_
≃-refl = ≡-refl

≃-sym : Symmetric _≃_
≃-sym = ≡-sym

≃-trans : Transitive _≃_
≃-trans = ≡-trans

≃-isEquivalence : IsEquivalence _≃_
≃-isEquivalence = record {
    refl = ≃-refl;
    sym = ≃-sym;
    trans = ≃-trans
    }

ℕ/[_]ℕ : Setoid lzero lzero
ℕ/[_]ℕ = record {
    Carrier = ℕ;
    _≈_ = _≃_;
    isEquivalence = ≃-isEquivalence
    }
NatModSetoid = ℕ/[_]ℕ

≃⇒mod∣∸ : ∀ {m n} → n ≃ m → mod ∣ m ∸ n
≃⇒mod∣∸ {m} {n} n≃m = divides (m / mod ∸ n / mod) (
    m ∸ n                                                   ≡⟨ cong₂ _∸_ (m≡m%n+[m/n]*n m mod) (m≡m%n+[m/n]*n n mod) ⟩
    m % mod + m / mod * mod ∸ (n % mod + n / mod * mod)     ≡⟨ cong (_∸ (n % mod + n / mod * mod)) (+-commℕ (m % mod) (m / mod * mod)) ⟩
    m / mod * mod + m % mod ∸ (n % mod + n / mod * mod)     ≡⟨ ≡-sym (∸-+-assoc (m / mod * mod + m % mod) (n % mod) (n / mod * mod)) ⟩
    m / mod * mod + m % mod ∸ n % mod ∸ n / mod * mod       ≡⟨ cong (_∸ n / mod * mod) (+-∸-assoc (m / mod * mod) {m % mod} {n % mod} (≤-reflexive n≃m)) ⟩
    m / mod * mod + (m % mod ∸ n % mod) ∸ n / mod * mod     ≡⟨ cong (λ q → m / mod * mod + (m % mod ∸ q) ∸ n / mod * mod) n≃m ⟩
    m / mod * mod + (m % mod ∸ m % mod) ∸ n / mod * mod     ≡⟨ cong (λ q → m / mod * mod + q ∸ n / mod * mod) (n∸n≡0 (m % mod)) ⟩
    m / mod * mod + 0 ∸ n / mod * mod                       ≡⟨ cong (_∸ n / mod * mod) (+-identityℕ .proj₂ (m / mod * mod)) ⟩
    m / mod * mod ∸ n / mod * mod                           ≡⟨ ≡-sym (*-distrib-∸ .proj₂ mod (m / mod) (n / mod)) ⟩
    (m / mod ∸ n / mod) * mod                               ∎)
    where open ≡-Reasoning

_≲_ : Rel ℕ lzero
m ≲ n = Σ ℕ λ k → n ≡ k * mod + m

≲-refl : Reflexive _≲_
≲-refl = 0 , ≡-refl

≲-trans : Transitive _≲_
≲-trans {m} {n} {o} (i , n=i*mod+m) (j , o=j*mod+n) = j + i , (
    o                           ≡⟨ o=j*mod+n ⟩
    j * mod + n                 ≡⟨ cong (j * mod +_) n=i*mod+m ⟩
    j * mod + (i * mod + m)     ≡⟨ ≡-sym (+-assocℕ (j * mod) (i * mod) m) ⟩
    j * mod + i * mod + m       ≡⟨ cong (_+ m) (≡-sym (*-distribℕ-+ .proj₂ mod j i)) ⟩
    (j + i) * mod + m           ∎)
    where open ≡-Reasoning

≲⇒≃ : _≲_ Relation.Binary.⇒ _≃_
≲⇒≃ {m} {n} (k , n=k*mod+m) =
    m % mod                 ≡⟨ ≡-sym ([m+kn]%n≡m%n m k mod) ⟩
    (m + k * mod) % mod     ≡⟨ %-congˡ {mod} (+-commℕ m (k * mod)) ⟩
    (k * mod + m) % mod     ≡⟨ %-congˡ {mod} (≡-sym n=k*mod+m) ⟩
    n % mod                 ∎
    where open ≡-Reasoning

-- i'm so sorry lmao
≲⇒≤ : _≲_ Relation.Binary.⇒ _≤_
≲⇒≤ {m} {n} (k , n=k*mod+m) = ≤-trans (m≤n+m m (k * mod)) (≤-reflexive (≡-sym n=k*mod+m))

≃×≤⇒≲ : ∀ {m n} → m ≃ n → .(m ≤ n) → m ≲ n
≃×≤⇒≲ {m} {n} m≃n m≤n = (n ∸ m) / mod , (
    n                           ≡⟨ ≡-sym (m∸n+n≡m {n} {m} m≤n) ⟩
    n ∸ m + m                   ≡⟨ cong (_+ m) (≡-sym (m/n*n≡m {n ∸ m} {mod} (≃⇒mod∣∸ {n} {m} m≃n))) ⟩
    (n ∸ m) / mod * mod + m     ∎)
    where open ≡-Reasoning

-- A maybe easier version of this relation to use
_≃′_ : Rel ℕ lzero
m ≃′ n = m ≲ n ⊎ n ≲ m

≃′⇒≃ : _≃′_ Relation.Binary.⇒ _≃_
≃′⇒≃ {m} {n} (inj₁ m≲n) = ≲⇒≃ m≲n
≃′⇒≃ {m} {n} (inj₂ n≲m) = ≃-sym (≲⇒≃ n≲m)

≃⇒≃′ : _≃_ Relation.Binary.⇒ _≃′_
≃⇒≃′ {m} {n} m≃n with ≤-cmp m n
... | inj₁ m≤n = inj₁ (≃×≤⇒≲ m≃n m≤n)
... | inj₂ n<m = inj₂ (≃×≤⇒≲ (≃-sym m≃n) (<⇒≤ n<m))



-----------------------
--- Relation to Fin ---
-----------------------

toℕ-cong : Congruent (_≡_ {A = Fin mod}) _≃_ toℕ
toℕ-cong = from-discrete-cong {A = Fin mod} NatModSetoid toℕ

toℕ-bijective : Bijective (_≡_ {A = Fin mod}) _≃_ toℕ
toℕ-bijective = both-inv→bijective (discrete-setoid (Fin mod)) NatModSetoid (toℕ which-is-cong toℕ-cong) ((cycle which-is-cong cycle-cong) , cycle-inject , inject-cycle)
    where
        -- inverse of toℕ : Fin mod → ℕ
        cycle : ℕ → Fin mod
        cycle i = fromℕ< {i % mod} (m%n<n i mod)

        inject : Fin mod → ℕ
        inject = toℕ

        open ≡-Reasoning

        cycle-cong : Congruent _≃_ _≡_ cycle
        cycle-cong {i} {j} i≃j =
            cycle i                         ≡⟨⟩
            fromℕ< {i % mod} (m%n<n i mod)  ≡⟨ fromℕ<-cong (i % mod) (j % mod) {mod} i≃j (m%n<n i mod) (m%n<n j mod) ⟩
            fromℕ< {j % mod} (m%n<n j mod)  ≡⟨⟩
            cycle j                         ∎

        cycle-inject : RightInverse _≃_ _≡_ cycle inject
        cycle-inject {i} =
            cycle (inject i)            ≡⟨⟩
            fromℕ< {toℕ i % mod} _      ≡⟨ fromℕ<-cong (toℕ i % mod) (toℕ i) {mod} (m<n⇒m%n≡m {mod} {toℕ i} (toℕ<n i)) _ (toℕ<n i) ⟩
            fromℕ< {toℕ i} (toℕ<n i)    ≡⟨ fromℕ<-toℕ i (toℕ<n i) ⟩
            i                           ∎
            where
                i<mod : toℕ i < mod
                i<mod = toℕ<n i

        inject-cycle : LeftInverse _≃_ _≡_ cycle inject
        inject-cycle {n} =
            inject (cycle n) % mod          ≡⟨⟩
            toℕ (fromℕ< {n % mod} _) % mod  ≡⟨ %-congˡ (toℕ-fromℕ< {n % mod} {mod} (m%n<n n mod)) ⟩
            n % mod % mod                   ≡⟨ m%n%n≡m%n n mod ⟩
            n % mod                         ∎

size-mod : HasSize NatModSetoid mod
size-mod = record {
    to = toℕ;
    cong = toℕ-cong;
    bijective = toℕ-bijective
    }


---------------------------
--- Some nice functions ---
---------------------------
{-
    Note that _+_, _*_, and _^_ all work with this setoid
-}

neg : ℕ → ℕ
neg m = mod ∸ m % mod

infixl 6 _-_
_-_ : ℕ → ℕ → ℕ
m - n = m + neg n


---------------------
--- Setoid things ---
---------------------

+-cong : Congruent₂ _≃_ _≃_ _≃_ _+_
+-cong {m} {n} {o} {p} m≃n o≃p =
    (m + o) % mod               ≡⟨ %-distribˡ-+ m o mod ⟩
    (m % mod + o % mod) % mod   ≡⟨ %-congˡ {mod} (cong₂ _+_ m≃n o≃p) ⟩
    (n % mod + p % mod) % mod   ≡⟨ ≡-sym (%-distribˡ-+ n p mod) ⟩
    (n + p) % mod               ∎
    where open ≡-Reasoning

+-func : SetoidFunction₂ NatModSetoid NatModSetoid NatModSetoid
+-func = record {
    func = _+_;
    respects = +-cong
    }

*-cong : Congruent₂ _≃_ _≃_ _≃_ _*_
*-cong {m} {n} {o} {p} m≃n o≃p =
    m * o % mod                 ≡⟨ %-distribˡ-* m o mod ⟩
    m % mod * (o % mod) % mod   ≡⟨ %-congˡ {mod} (cong₂ _*_  m≃n o≃p) ⟩
    n % mod * (p % mod) % mod   ≡⟨ ≡-sym (%-distribˡ-* n p mod) ⟩
    n * p % mod                 ∎
    where open ≡-Reasoning

*-func : SetoidFunction₂ NatModSetoid NatModSetoid NatModSetoid
*-func = record {
    func = _*_;
    respects = *-cong
    }

neg-cong : Congruent _≃_ _≃_ neg
neg-cong {m} {n} m≃n =
    (mod ∸ m % mod) % mod   ≡⟨ cong (λ q → (mod ∸ q) % mod) m≃n ⟩
    (mod ∸ n % mod) % mod   ∎
    where open ≡-Reasoning

neg-func : SetoidFunction NatModSetoid NatModSetoid
neg-func = record {
    func = neg;
    respects = neg-cong
    }

minus-cong : Congruent₂ _≃_ _≃_ _≃_ _-_
minus-cong ≃₁ ≃₂ = +-cong ≃₁ (neg-cong ≃₂)

minus-func : SetoidFunction₂ NatModSetoid NatModSetoid NatModSetoid
minus-func = record {
    func = _-_;
    respects = minus-cong
    }

^-cong : Congruent₂ _≃_ _≡_ _≃_ _^_
^-cong {m₁} {m₂} {zero} m₁≃m₂ ≡-refl = ≃-refl
^-cong {m₁} {m₂} {suc n} m₁≃m₂ ≡-refl = *-cong m₁≃m₂ (^-cong {y₁ = n} m₁≃m₂ ≡-refl)

^-func : SetoidFunction₂ NatModSetoid (discrete-setoid ℕ) NatModSetoid
^-func = record {
    func = _^_;
    respects = ^-cong
    }


----------------
--- Theorems ---
----------------

open import Algebra.Definitions {A = ℕ} _≃_ hiding (Cancellative; LeftCancellative; RightCancellative)
open import Algebra.Definitions using (Cancellative; LeftCancellative; RightCancellative)
open import Algebra.Consequences.Setoid NatModSetoid
  using (comm∧cancelʳ⇒cancelˡ; comm∧distrʳ⇒distrˡ; comm∧distrˡ⇒distrʳ
        ; comm⇒sym[distribˡ])

minus-is-∸ : ∀ {m n} → .(m ≥ n) → m - n ≃ m ∸ n
minus-is-∸ {m} {n} m≥n =
    (m - n) % mod                           ≡⟨⟩
    (m + (mod ∸ n % mod)) % mod             ≡⟨ %-congˡ {mod} (m+[n∸o]=m∸o+n m mod (n % mod) (≤-trans (m%n≤m n mod) m≥n) (m%n≤n n mod)) ⟩
    (m ∸ n % mod + mod) % mod               ≡⟨ [m+n]%n≡m%n (m ∸ n % mod) mod ⟩
    (m ∸ n % mod) % mod                     ≡⟨ ≡-sym ([m∸kn]%n≡m%n (m ∸ n % mod) (n / mod) mod thing) ⟩
    (m ∸ n % mod ∸ n / mod * mod) % mod     ≡⟨ %-congˡ {mod} (∸-+-assoc m (n % mod) (n / mod * mod)) ⟩
    (m ∸ (n % mod + n / mod * mod)) % mod   ≡⟨ %-congˡ {mod} (cong (m ∸_) (≡-sym (m≡m%n+[m/n]*n n mod))) ⟩
    (m ∸ n) % mod                           ∎
    where
        thing : m ∸ n % mod ≥ n / mod * mod
        thing = begin
            n / mod * mod                       ≡⟨ ≡-sym (m+n∸m≡n (n % mod) (n / mod * mod)) ⟩
            n % mod + n / mod * mod ∸ n % mod   ≡⟨ cong (_∸ n % mod) (≡-sym (m≡m%n+[m/n]*n n mod)) ⟩
            n ∸ n % mod                         ≤⟨ ∸-mono {o = n % mod} m≥n ≤-refl ⟩
            m ∸ n % mod                         ∎
            where open ≤-Reasoning
        open ≡-Reasoning

∸-partial-cong : ∀ {m n o p} → .(m ≥ o) → .(n ≥ p) → m ≃ n → o ≃ p → m ∸ o ≃ n ∸ p
∸-partial-cong {m} {n} {o} {p} m≥o n≤p m≃n o≃p = begin
    m ∸ o ≈⟨ ≃-sym (minus-is-∸ m≥o) ⟩
    m - o ≈⟨ minus-cong m≃n o≃p ⟩
    n - p ≈⟨ minus-is-∸ n≤p ⟩
    n ∸ p ∎
    where open import Relation.Binary.Reasoning.Setoid NatModSetoid

+-comm : Commutative _+_
+-comm m n = %-congˡ {mod} (+-commℕ m n)

+-assoc : Associative _+_
+-assoc m n o = %-congˡ {mod} (+-assocℕ m n o)

*-comm : Commutative _*_
*-comm m n = %-congˡ {mod} (*-commℕ m n)

*-assoc : Associative _*_
*-assoc m n o = %-congˡ {mod} (*-assocℕ m n o)

*-zero : Zero 0 _*_
*-zero = (λ x → ≡-refl) , (λ x → *-comm x 0)

m-m≃0 : ∀ m → m - m ≃ 0
m-m≃0 m = ≃-trans (minus-is-∸ {m} ≤-refl) (≃-reflexive (n∸n≡0 m))

minus-reverse : ∀ m n → m - n ≃ neg n + m
minus-reverse m n = +-comm m (neg n)

+-group : AbelianGroup lzero lzero
+-group = record {
    rawGroup = record {
        CarrierSetoid = NatModSetoid;
        op = +-func;
        inverse = neg-func;
        id = 0
        };
    isAbelianGroup = record {
        isGroup = record {
            id-is-left-id = λ {x} → ≡-refl;
            inv-is-left-inv = λ {x} → ≃-trans (≃-sym (minus-reverse x x)) (m-m≃0 x);
            assoc = λ {m} {n} {o} → ≃-sym (+-assoc m n o)
            };
        abelian = λ {m} {n} → +-comm m n
        }
    }

open AbelianGroup +-group using () renaming (
    identity to +-identity;
    inv-is-involution to neg-involutive;
    ∙-cancel to +-cancel-≃;
    inv-flip-distributes to neg-flip-distributes;
    inv-flips-∸ to neg-flips-∸;
    m∙n∸n=m to m+n-n≃m;
    m∙n∸m=n to m+n-m≃n;
    m∸n∙n=m to m-n+n≃m;
    m∙n∙o=m∙o∙n to m+n+o≃m+o+n;
    ∙-∸-assoc to +-minus-assoc
    ) public

*-identity : Identity 1 _*_
*-identity = (λ x → +-identity .proj₂ {x}) , (λ x → ≃-trans (*-comm x 1) (+-identity .proj₂ {x}))

m%mod≃m : ∀ m → m % mod ≃ m
m%mod≃m m = m%n%n≡m%n m mod


minus-bound : ∀ m n → .(m < n) → .(n ≤ mod) → m + (mod ∸ n) < mod
minus-bound m n m<n n≤mod = begin
    suc (m + (mod ∸ n))     ≡⟨ cong suc (+-commℕ m (mod ∸ n)) ⟩
    suc (mod ∸ n + m)       ≡⟨ cong (_+ m) (∸-suc mod n n≤mod) ⟩
    suc mod ∸ n + m         ≤⟨ +-mono-≤ {o = m} (∸-mono {suc mod} {o = n} {p = suc m} ≤-refl m<n) ≤-refl ⟩
    suc mod ∸ suc m + m     ≡⟨⟩
    mod ∸ m + m             ≡⟨ m∸n+n≡m {mod} {m} (<⇒≤ (<-≤-trans m<n n≤mod)) ⟩
    mod                     ∎
    where open ≤-Reasoning

small-minus : ∀ m n → .(m < n) → (n < mod) → (m - n) % mod ≡ m + (mod ∸ n)
small-minus m n m<n n<mod = ≡-sym (
    m + (mod ∸ n)                   ≡⟨ ≡-sym (m<n⇒m%n≡m {mod} {m + (mod ∸ n)} (minus-bound m n m<n (<⇒≤ n<mod))) ⟩
    (m + (mod ∸ n)) % mod           ≡⟨ cong (λ q → (m + (mod ∸ q)) % mod) {n} {n % mod} (≡-sym (m<n⇒m%n≡m n<mod)) ⟩
    (m + (mod ∸ n % mod)) % mod     ≡⟨⟩
    (m - n) % mod                   ∎)
    where open ≡-Reasoning

minus-wrap₁ : ∀ m n → .(m < n) → (n < mod) → (m - n) % mod > m
minus-wrap₁ m n m<n n<mod = begin
    suc m                           ≤⟨ m<m+n m {mod ∸ n} (m<n⇒0<n∸m n<mod) ⟩
    m + (mod ∸ n)                   ≡⟨ ≡-sym (small-minus m n m<n n<mod) ⟩
    (m - n) % mod                   ∎
    where open ≤-Reasoning

minus-wrap₂ : ∀ m n → .(m < n) → (n < mod) → n + (m - n) % mod ≥ mod
minus-wrap₂ m n m<n n<mod = begin
    mod                     ≤⟨ m≤m+n mod m ⟩
    mod + m                 ≡⟨ cong (_+ m) (≡-sym (m+[n∸m]≡n {n} {mod} (<⇒≤ n<mod))) ⟩
    n + (mod ∸ n) + m       ≡⟨ +-assocℕ n (mod ∸ n) m ⟩
    n + (mod ∸ n + m)       ≡⟨ cong (n +_) (+-commℕ (mod ∸ n) m) ⟩
    n + (m + (mod ∸ n))     ≡⟨ cong (n +_) (≡-sym (small-minus m n m<n n<mod)) ⟩
    n + (m - n) % mod       ∎
    where open ≤-Reasoning
