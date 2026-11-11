open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; subst; cong) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open import Relation.Nullary using (¬_; Dec; yes; no)
import Relation.Unary as Unary
open import Relation.Binary as Binary using (Setoid)
open import Function using (_∘_; Surjection; Bijection; Injective; Surjective)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (tt)
open import Data.Product using (Σ; _×_; _,_; _,′_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Fin using (Fin; toℕ; fromℕ<) renaming (zero to fin-zero; suc to fin-suc)
open import Data.Fin.Properties using (toℕ<n; toℕ-fromℕ<; fromℕ<-toℕ; fromℕ<-cong; toℕ-injective)
open import Data.Nat using (ℕ; zero; suc; pred; _+_; _∸_; _*_; _≤_; _≥_; _<_; _>_; _≤?_; _<?_; _!; s≤s; s≤s⁻¹; _≟_; NonZero; nonZero; ≢-nonZero; ≢-nonZero⁻¹; >-nonZero⁻¹; NonTrivial; n>1⇒nonTrivial; nonTrivial⇒nonZero; nonTrivial⇒n>1)
open import Data.Nat.Properties using (+-suc; suc-injective; *-comm; +-cancel-≡; +-mono-≤; ∸-mono; m≤m+n; ≤-reflexive; ≤-refl; ≤-trans; <-trans; <-≤-trans; ≤-<-trans; <-irrefl; <⇒≤; n<1⇒n≡0; ≤∧≢⇒<; m<m*n; m≤n+m; _!≢0; module ≤-Reasoning)
open import Data.Nat.Divisibility using (_∣_; divides; _∣?_; quotient>1)

open import Plasmaduck.SetoidExperiment.SetoidMachinery using (property-subset-setoid; discrete-setoid; from-discrete-cong)
open import Plasmaduck.Data.Nat.Divisibility using (∣-dec; ∣-reflexive; ∣-refl; ∣-trans; m≤n⇒¬m∣1+n!)
open import Plasmaduck.Data.Nat using (n<sn; n=spn; NonTrivial-divisor; nonTrivial⇒pred-nonZero; nonZero⇒suc-nonTrivial; ≠0∧≠1⇒nonTrivial; m∣n⇒m≤n; m<n*m; n≤sn; ≤-cmp; decide-range; n≤n!; n<n!; <≤-find; ∸-suc; m∸n+n≡m)
open import Plasmaduck.Util.Case using (case_of_)
open import Plasmaduck.Util.Negation using (¬¬-lift; dec⇒¬¬-flatten)
open import Plasmaduck.Counting.Counting using (any'; fin-setoid)
open import Plasmaduck.Function.Surjectionish using (Surjectionish)
open import Plasmaduck.Function.InjectionSurjection using (bijection→surjection)
open import Plasmaduck.Relation.Defs using (CongruentProperty)
open import Plasmaduck.Property.Defs using (any-type)
open import Plasmaduck.Data.Nat.GCD using (gcd; _//_; gcd-distribˡ₁-*; //-factor; gcd-nonZero⁻¹; gcd-zero-proj₁; gcd-∣₁; gcd≤₁; gcd=id₁⇒∣; gcd=id₂⇒∣; coprime-delete₁; coprime-delete₂; GCDCoprime)



module Plasmaduck.Data.Nat.Primality where

module _ (n : ℕ) where
    record Composite : Set where
        field
            i j : ℕ
            {{i-nonTrivial}} : NonTrivial i
            {{j-nonTrivial}} : NonTrivial j
            factors : n ≡ i * j

        i< : i < n
        i< = <-≤-trans (m<m*n i j {{nonTrivial⇒nonZero i}} (nonTrivial⇒n>1 j)) (≤-reflexive (≡-sym factors))

        j< : j < n
        j< = <-≤-trans (m<n*m j i {{nonTrivial⇒nonZero j}} (nonTrivial⇒n>1 i)) (≤-reflexive (≡-sym factors))

        i∣ : i ∣ n
        i∣ = divides j (≡-trans factors (*-comm i j))

        j∣ : j ∣ n
        j∣ = divides i factors

    Trivial : Set
    Trivial = n ≤ 1

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

¬Trivial∧NonTrivial : ∀ {n} → Trivial n → NonTrivial n → ⊥
¬Trivial∧NonTrivial {n} n≤1 nonTrivial = <-irrefl ≡-refl (≤-<-trans n≤1 (nonTrivial⇒n>1 n {{nonTrivial}}))

Trivial? : ∀ n → Trivial n ⊎ NonTrivial n
Trivial? n with ≤-cmp n 1
... | inj₁ n≤1 = inj₁ n≤1
... | inj₂ n>1 = inj₂ (n>1⇒nonTrivial n>1)

Rough? : Binary.Decidable _Rough_
Rough? m n with m HasDivisorLessThan? n
... | yes divisor = no (¬¬-lift divisor)
... | no rough = yes rough

Irreducible? : Unary.Decidable Irreducible
Irreducible? n with 1 <? n | n HasDivisorLessThan? n
... | no 1≮n | _ = no λ n-irreducible → 1≮n (nonTrivial⇒n>1 _ {{n-irreducible .proj₁}})
... | yes 1<n | yes n-divisor = no λ n-irreducible → Irreducible⇒Rough n-irreducible n-divisor
... | yes 1<n | no n-rough = yes (Rough⇒Irreducible {n} {{n>1⇒nonTrivial 1<n}} n-rough)

Composite? : Unary.Decidable Composite
Composite? n with n HasDivisorLessThan? n
... | no ¬divisor = no (¬divisor ∘ Composite⇒HasDivisor)
... | yes divisor = yes (HasDivisor⇒Composite divisor)

Irreducible∨Composite : ∀ n → Irreducible n ⊎ Composite n ⊎ Trivial n
Irreducible∨Composite n with Composite? n | Trivial? n
... | yes composite | _ = inj₂ (inj₁ composite)
... | no ¬composite | inj₁ trivial = inj₂ (inj₂ trivial)
... | no ¬composite | inj₂ nonTrivial = inj₁ (nonTrivial , ¬composite)

Prime⇒¬Composite : ∀ {n} → Prime n → ¬ (Composite n)
Prime⇒¬Composite {n@(suc n')} n-prime n-composite = case (n-prime .proj₂ i j (∣-reflexive factors)) of λ {
    (inj₁ n∣i) → <-irrefl ≡-refl (≤-<-trans (m∣n⇒m≤n n i n∣i) i<);
    (inj₂ n∣j) → <-irrefl ≡-refl (≤-<-trans (m∣n⇒m≤n n j n∣j) j<)
    }
    where
        open Composite n-composite
        instance
            i-nonZero : NonZero i
            i-nonZero = nonTrivial⇒nonZero i

            j-nonZero : NonZero j
            j-nonZero = nonTrivial⇒nonZero j

Prime⇒NonTrivial : ∀ {n} → Prime n → NonTrivial n
Prime⇒NonTrivial = proj₁

Prime⇒Irreducible : ∀ {n} → Prime n → Irreducible n
Prime⇒Irreducible n-prime = Prime⇒NonTrivial n-prime , Prime⇒¬Composite n-prime

Irreducible⇒gcd=1,n : ∀ {n} → Irreducible n → ∀ i → gcd n i ≡ 1 ⊎ gcd n i ≡ n
Irreducible⇒gcd=1,n {n@(suc (suc n''))} n-irr i with gcd n i ≟ 1 | gcd n i ≟ n
... | yes a | _ = inj₁ a
... | no _ | yes a = inj₂ a
... | no gcd[ni]≠1 | no gcd[ni]≠n = ⊥-elim (n-irr .proj₂ (record {
    i = n // i;
    j = gcd n i;
    i-nonTrivial = n>1⇒nonTrivial (quotient>1 {gcd n i} {n} (gcd-∣₁ n i) (≤∧≢⇒< (gcd≤₁ n i) gcd[ni]≠n));
    factors = //-factor n i
    }))
    where
        instance
            gcd-nonTrivial : NonTrivial (gcd n i)
            gcd-nonTrivial = ≠0∧≠1⇒nonTrivial (λ gcd=0 → ≢-nonZero⁻¹ n (gcd-zero-proj₁ n i gcd=0)) gcd[ni]≠1

            gcd-nonZero : NonZero (gcd n i)
            gcd-nonZero = nonTrivial⇒nonZero (gcd n i)

Irreducible⇒coprime-∨-divides : ∀ {n} → Irreducible n → ∀ i → GCDCoprime n i ⊎ n ∣ i
Irreducible⇒coprime-∨-divides {n} n-irr i with Irreducible⇒gcd=1,n n-irr i
... | inj₁ gcd[ni]=1 = inj₁ gcd[ni]=1
... | inj₂ gcd[ni]=n = inj₂ (gcd=id₁⇒∣ n i gcd[ni]=n)

Irreducible⇒Prime : ∀ {n} → Irreducible n → Prime n
Irreducible⇒Prime {n} n-irr = Irreducible⇒NonTrivial n-irr , λ x y n∣x*y → case (Irreducible⇒coprime-∨-divides n-irr x) of λ {
    (inj₁ nx-coprime) → inj₂ (coprime-delete₁ n x y nx-coprime n∣x*y);
    (inj₂ n∣x) → inj₁ n∣x
    }

Prime? : Unary.Decidable Prime
Prime? n with Irreducible? n
... | no ¬irr = no (¬irr ∘ Prime⇒Irreducible)
... | yes irr = yes (Irreducible⇒Prime irr)

Prime∨Composite : ∀ n → Prime n ⊎ Composite n ⊎ Trivial n
Prime∨Composite n with Composite? n | Trivial? n
... | yes composite | _ = inj₂ (inj₁ composite)
... | no ¬composite | inj₁ trivial = inj₂ (inj₂ trivial)
... | no ¬composite | inj₂ nonTrivial = inj₁ (Irreducible⇒Prime (nonTrivial , ¬composite))

¬Prime⇒Composite : ∀ {n} .{{_ : NonTrivial n}} → ¬ (Prime n) → Composite n
¬Prime⇒Composite {n} non-prime with Prime∨Composite n
... | inj₁ prime = ⊥-elim (non-prime prime)
... | inj₂ (inj₁ composite) = composite
... | inj₂ (inj₂ trivial) = ⊥-elim (<-irrefl ≡-refl (<-≤-trans (nonTrivial⇒n>1 n) trivial))


module PrimeGeneration where
    module Lemmas where

        TargetRange : ℕ → ℕ → Set
        TargetRange n i = n < i × i ≤ n !

        InRange? : (n i : ℕ) → Dec (TargetRange n i)
        InRange? n i with n <? i | i ≤? n !
        ... | no ¬a | _ = no λ z → ¬a (z .proj₁)
        ... | yes a | no ¬a = no λ z → ¬a (z .proj₂)
        ... | yes a | yes a₁ = yes (a , a₁)

        TargetRangeNonEmpty : (n : ℕ) → n ≢ 1 → n ≢ 2 → Σ ℕ (TargetRange n)
        TargetRangeNonEmpty zero n≠1 n≠2 = 1 , s≤s _≤_.z≤n , s≤s _≤_.z≤n
        TargetRangeNonEmpty (suc zero) n≠1 n≠2 = ⊥-elim (n≠1 ≡-refl)
        TargetRangeNonEmpty (suc (suc zero)) n≠1 n≠2 = ⊥-elim (n≠2 ≡-refl)
        TargetRangeNonEmpty n@(suc (suc (suc n'''))) n≠1 n≠2 = <≤-find n (n !) (n<n! n (λ ()) λ ())

        {-
            There is no maximum prime.
            Proof:

            AFSOC there is a max prime n.
            n! + 1 is not divisible by anything ≤ n.
            Since n is the max prime, it is not divisible by anything from n to n! (since those would be divisible by primes)
            Then n! + 1 is not divisible by any prime less than it, so it must itself be prime.
        -}
        prime-exists-theorem : ∀ n → (∀ i → TargetRange n i → Composite i) → Prime (1 + n !)
        prime-exists-theorem n all-composite = Irreducible⇒Prime (nonZero⇒suc-nonTrivial (n !) {{n !≢0}} , 1+n!-¬Composite)
            where
                not-divisible-≤n : ∀ {m} .{{_ : NonTrivial m}} → m ≤ n → ¬ m ∣ 1 + n !
                not-divisible-≤n m≤n = m≤n⇒¬m∣1+n! m≤n

                >n-divisor-step : ∀ {m} .{{_ : NonTrivial m}} → n < m → m ≤ n ! → m ∣ 1 + n ! → Σ ℕ λ m' → m' < m × NonTrivial m' × m' ∣ 1 + n !
                >n-divisor-step {m} n<m m≤n! m∣1+n! = m-composite .Composite.i , Composite.i< m-composite , Composite.i-nonTrivial m-composite , ∣-trans (Composite.i∣ m-composite) m∣1+n!
                    where
                        m-composite = all-composite m (n<m , m≤n!)

                >n-divisor-force : ∀ m o .{{_ : NonTrivial m}} → m ≤ o → m ≤ n ! →  m ∣ 1 + n ! → Σ ℕ λ m' → m' ≤ n × NonTrivial m' × m' ∣ 1 + n !
                >n-divisor-force m@(suc m'@(suc _)) o@(suc o') m≤o m≤n! m∣1+n! with ≤-cmp m n
                ... | inj₂ m>n = >n-divisor-force p o'  (s≤s⁻¹ (<-≤-trans p<m m≤o)) (≤-trans (<⇒≤ p<m) m≤n!) p∣1+n!
                    where
                        p-step = >n-divisor-step m>n m≤n! m∣1+n!

                        p : ℕ
                        p = p-step .proj₁

                        p<m : p < m
                        p<m = p-step. proj₂ .proj₁

                        instance
                            p-nonTrivial : NonTrivial p
                            p-nonTrivial = p-step .proj₂ .proj₂ .proj₁

                        p∣1+n! : p ∣ 1 + n !
                        p∣1+n! = p-step .proj₂ .proj₂ .proj₂

                ... | inj₁ m≤n = m , m≤n , record { nonTrivial = tt } , m∣1+n!

                not-divisible->n : ∀ m .{{_ : NonTrivial m}} → m ≤ n ! → ¬ m ∣ 1 + n !
                not-divisible->n m m≤n! m∣1+n! = not-divisible-≤n p≤n p∣1+n!
                    where
                        p-step = >n-divisor-force m m ≤-refl m≤n! m∣1+n!

                        p : ℕ
                        p = p-step .proj₁

                        p≤n : p ≤ n
                        p≤n = p-step .proj₂ .proj₁

                        instance
                            p-nonTrivial : NonTrivial p
                            p-nonTrivial = p-step .proj₂ .proj₂ .proj₁

                        p∣1+n! : p ∣ suc (n !)
                        p∣1+n! = p-step .proj₂ .proj₂ .proj₂

                1+n!-¬Composite : ¬ (Composite (suc (n !)))
                1+n!-¬Composite 1+n!-composite = not-divisible->n (1+n!-composite .Composite.i) (s≤s⁻¹ (Composite.i< 1+n!-composite)) (Composite.i∣ 1+n!-composite)

        module _ (n : ℕ) where
            target-fin-bij : Bijection (fin-setoid (n ! ∸ n)) (property-subset-setoid (discrete-setoid ℕ) (TargetRange n))
            target-fin-bij = record {
                to = f-func;
                cong = from-discrete-cong B-setoid f-func;
                bijective = f-inj , f-surj
                }
                where
                    A = fin-setoid (n ! ∸ n) .Setoid.Carrier
                    B-setoid = property-subset-setoid (discrete-setoid ℕ) (TargetRange n)
                    B = B-setoid .Setoid.Carrier

                    f : A → ℕ
                    f i = suc (toℕ i) + n

                    f-in-range : (i : A) → TargetRange n (f i)
                    f-in-range i = (begin
                            suc n               ≤⟨ m≤n+m (suc n) (toℕ i) ⟩
                            toℕ i + suc n       ≡⟨ +-suc (toℕ i) n ⟩
                            suc (toℕ i) + n     ≡⟨⟩
                            f i                 ∎
                        ) , (begin
                            f i                 ≡⟨⟩
                            suc (toℕ i) + n     ≤⟨ +-mono-≤ {suc (toℕ i)} {n ! ∸ n} {n} {n} (toℕ<n i) ≤-refl ⟩
                            n ! ∸ n + n         ≡⟨ m∸n+n≡m {n ! } {n} (n≤n! n) ⟩
                            n !                 ∎
                        )
                        where open ≤-Reasoning

                    f-func : A → B
                    f-func i = f i , f-in-range i

                    f-inj : Injective _≡_ (_≡_ Function.on proj₁) f-func
                    f-inj {i} {j} fi=fj = toℕ-injective (+-cancel-≡ .proj₂ n (toℕ i) (toℕ j) (suc-injective fi=fj))

                    f-surj : Surjective _≡_ (_≡_ Function.on proj₁) f-func
                    f-surj (m , m-in-range) = fromℕ< {m ∸ suc n} pf , λ { ≡-refl →
                        f-func (fromℕ< {m ∸ suc n} pf) .proj₁   ≡⟨⟩
                        suc (toℕ (fromℕ< {m ∸ suc n} pf)) + n   ≡⟨ cong suc (cong (_+ n) (toℕ-fromℕ< {m ∸ suc n} pf)) ⟩
                        suc (m ∸ suc n) + n                     ≡⟨ cong (_+ n) (∸-suc m (suc n) (m-in-range .proj₁)) ⟩
                        m ∸ n + n                               ≡⟨ m∸n+n≡m {m} {n} (<⇒≤ (m-in-range .proj₁)) ⟩
                        m                                       ∎ }
                        where
                            pf : m ∸ suc n < n ! ∸ n
                            pf = begin
                                suc (m ∸ suc n)     ≡⟨ ∸-suc m (suc n) (m-in-range .proj₁) ⟩
                                m ∸ n               ≤⟨ ∸-mono {m} {n ! } {n} {n} (m-in-range .proj₂) ≤-refl ⟩
                                n ! ∸ n             ∎
                                where open ≤-Reasoning
                            open ≡-Reasoning

            surj : Surjectionish (fin-setoid (n ! ∸ n)) (property-subset-setoid (discrete-setoid ℕ) (TargetRange n))
            surj = inj₁ (bijection→surjection target-fin-bij)

            any-primes-before-n!? : Dec (any-type {A = Σ ℕ (TargetRange n)} (Prime ∘ proj₁))
            any-primes-before-n!? = any' {A-setoid = property-subset-setoid (discrete-setoid ℕ) (TargetRange n)} surj (Prime ∘ proj₁) (λ { ≡-refl p → p }) (Prime? ∘ proj₁)

            find-prime : ℕ
            find-prime with any-primes-before-n!?
            ... | no no-primes = 1 + n !
            ... | yes ((p , p-in-range) , Prime[p]) = p

            find-prime-is-prime' : .{{_ : NonZero n}} → Prime find-prime
            find-prime-is-prime' with any-primes-before-n!?
            ... | no no-primes = prime-exists-theorem n λ i i-in-range → ¬Prime⇒Composite {{n>1⇒nonTrivial (≤-<-trans (>-nonZero⁻¹ n) (i-in-range .proj₁))}} λ P[i] → no-primes ((i , i-in-range) , P[i])
            ... | yes ((p , p-in-range) , Prime[p]) = Prime[p]

            2-is-prime : Prime 2
            2-is-prime = Irreducible⇒Prime (record { nonTrivial = tt } , λ composite → let open Composite composite in <-irrefl ≡-refl (<-≤-trans i< (nonTrivial⇒n>1 i)))

            find-prime-is-prime-zero : n ≡ 0 → Prime find-prime
            find-prime-is-prime-zero n=0 with any-primes-before-n!?
            ... | no no-primes = subst Prime {2} {suc (n !)} (cong suc (cong _! (≡-sym n=0))) 2-is-prime
            ... | yes ((p , p-in-range) , Prime[p]) = Prime[p]

            find-prime-is-prime : Prime find-prime
            find-prime-is-prime = case (n ≟ 0) of λ {
                (yes n=0) → find-prime-is-prime-zero n=0;
                (no n≠0) → find-prime-is-prime' {{≢-nonZero n≠0}}
                }

            find-prime-is-forward : n ≤ find-prime
            find-prime-is-forward with any-primes-before-n!?
            ... | no no-primes = ≤-trans (n≤n! n) n≤sn
            ... | yes ((p , p-in-range) , Prime[p]) = <⇒≤ (p-in-range .proj₁)

        contradict-prime-composite-trivial : ∀ n → Prime n → Composite n ⊎ Trivial n → ⊥
        contradict-prime-composite-trivial n Prime[n] (inj₁ Composite[n]) = Prime⇒Irreducible Prime[n] .proj₂ Composite[n]
        contradict-prime-composite-trivial n Prime[n] (inj₂ n≤1) = <-irrefl ≡-refl (<-≤-trans (nonTrivial⇒n>1 n {{Prime[n] .proj₁}}) n≤1)

    open Lemmas
    open import Plasmaduck.Counting.Generators Prime (λ n → Composite n ⊎ Trivial n) using (module ExistsToCeil)
    open ExistsToCeil Prime∨Composite find-prime find-prime-is-forward find-prime-is-prime using (module WithContradicition) renaming (
        gen to π;
        P[gen] to Prime[π];
        Q-middle-gen to Composite∨Trivial[π-skip];
        count to count-primes;
        restricted-gen to π-restricted
        ) public
    open WithContradicition contradict-prime-composite-trivial using () renaming (
        gen-count to π-count;
        count-gen to count-π;
        restricted-gen-bijective to π-restricted-bijective
        ) public
open PrimeGeneration public

module Thing where
    -- Success! But maybe don't use π for actual computation; it invokes factorials and searching for factors through all lesser ints.
    prime₀ : π 0 ≡ 2
    prime₀ = ≡-refl

    prime₁ : π 1 ≡ 3
    prime₁ = ≡-refl

    prime₂ : π 2 ≡ 5
    prime₂ = ≡-refl
