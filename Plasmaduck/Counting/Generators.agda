open import Level using (Level; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; ≢-sym; subst; cong) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open import Relation.Binary using (tri<; tri≈; tri>)
import Relation.Unary as Unary
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Function using (_∘_; Injective; Surjective; Bijective; Congruent)
open import Data.Empty using (⊥; ⊥-elim; ⊥-elim-irr)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Nat using (ℕ; zero; suc; pred; _≟_; _≤_; _<_; _≥_; _>_; s≤s; s≤s⁻¹; <-cmp; NonZero; >-nonZero⁻¹; ≢-nonZero; _+_; _∸_)
open import Data.Nat.Properties using (suc-injective; <-irrefl; ≤-refl; ≤-reflexive; ≤-antisym; ≤-<-trans; <-≤-trans; ≤-trans; <-trans; <⇒≤; ≮⇒≥; ≤∧≢⇒<; ∸-monoʳ-≤; ∸-monoˡ-≤; module ≤-Reasoning; m≤n+m; +-comm; +-assoc; +-suc; m+n∸n≡m)

open import Plasmaduck.SetoidExperiment.SetoidMachinery using (discrete-setoid; property-subset-setoid; _which-is-cong_; from-discrete-cong)
open import Plasmaduck.Data.Empty using (⊥-recompute)
open import Plasmaduck.Data.Sum using (⊎-force₁)
open import Plasmaduck.Data.Nat using (≤-cmp; m∸n+n≡m; m<n⇒n∸m-nonZero; monotonic⇒injective; n<sn; n≤sn; ∸-suc)
open import Plasmaduck.Function.Properties using (LeftInverse; RightInverse; Idempotent)
open import Plasmaduck.Function.InjectionSurjection using (both-inv→bijective)
-- open import Algebra.Definitions {A = ℕ} _≡_ using (Idempotent)
open import Plasmaduck.Util.Case using (case_of_; inspect-case_of_)
{-
    Functions that generate all nats with property P, in order
-}
module Plasmaduck.Counting.Generators {α β : Level} (P : ℕ → Set α) (Q : ℕ → Set β) where


-- P' only counts when ≥ m
module ClippedProperties (m : ℕ) where
    P' : ℕ → Set α
    P' n = P n × m ≤ n

    Q' : ℕ → Set β
    Q' n = Q n ⊎ m > n

    PQ'-dec : (∀ n → P n ⊎ Q n) → (∀ n → P' n ⊎ Q' n)
    PQ'-dec PQ-dec n with PQ-dec n | ≤-cmp m n
    ... | inj₂ Q[n] | _ = inj₂ (inj₁ Q[n])
    ... | inj₁ P[n] | inj₁ m≤n = inj₁ (P[n] , m≤n)
    ... | inj₁ P[n] | inj₂ m>n = inj₂ (inj₂ m>n)

    PQ'-contradict : (∀ n → P n → Q n → ⊥) → (∀ n → P' n → Q' n → ⊥)
    PQ'-contradict PQ'-contradict n (P[n] , m≤n) (inj₁ Q[n]) = PQ'-contradict n P[n] Q[n]
    PQ'-contradict PQ'-contradict n (P[n] , m≤n) (inj₂ m>n) = <-irrefl ≡-refl (≤-<-trans m≤n m>n)

-- This one is probably better for minimum search, since then it doesn't search all the items below m
module FlattenedProperties (m : ℕ) where
    P' : ℕ → Set α
    P' n = P (n + m)

    Q' : ℕ → Set β
    Q' n = Q (n + m)

    PQ'-dec : (∀ n → P n ⊎ Q n) → (∀ n → P' n ⊎ Q' n)
    PQ'-dec PQ-dec n = PQ-dec (n + m)

    PQ'-contradict : (∀ n → P n → Q n → ⊥) → (∀ n → P' n → Q' n → ⊥)
    PQ'-contradict PQ-contradict n P[n+] Q[n+] = PQ-contradict (n + m) P[n+] Q[n+]

module CeilToGenerator
    (ceil : ℕ → ℕ)
    (P[ceil] : ∀ m → P (ceil m))
    (Q-middle : ∀ m n → m ≤ n → n < ceil m → Q n)
    (ceil-forward : ∀ m → m ≤ ceil m)
    where

    -- The converses of these hold only if P and Q are contradictory
    ceil=⇒P : ∀ {n} → ceil n ≡ n → P n
    ceil=⇒P {n} ceil[n]=n = subst P ceil[n]=n (P[ceil] n)

    ceil>⇒Q : ∀ {n} → ceil n > n → Q n
    ceil>⇒Q {n} ceil[n]>n = Q-middle n n ≤-refl ceil[n]>n

    ceil≠⇒Q : ∀ {n} → ceil n ≢ n → Q n
    ceil≠⇒Q {n} ceil[n]≠n = ceil>⇒Q ceil-n>n
        where
            ceil-n>n : ceil n > n
            ceil-n>n = ≤∧≢⇒< (ceil-forward n) (≢-sym (ceil[n]≠n ))

    private
        -- Note that this module implies this
        PQ-dec : ∀ n → P n ⊎ Q n
        PQ-dec n with ceil n ≟ n
        ... | yes ceil-n=n = inj₁ (ceil=⇒P ceil-n=n)
        ... | no ceil-n≠n = inj₂ (ceil≠⇒Q ceil-n≠n)


    ----------------------------
    --- The actual functions ---
    ----------------------------

    next : ℕ → ℕ
    next = ceil ∘ suc

    gen-helper : ℕ → ℕ → ℕ
    gen-helper n zero = n
    gen-helper n (suc i) = gen-helper (next n) i

    -- The nth item with property P (where gen 0 is the first such item)
    gen : ℕ → ℕ
    gen n = gen-helper (ceil 0) n

    count-helper : ℕ → ℕ → ℕ
    count-helper acc zero = acc
    count-helper acc i@(suc i') with PQ-dec i'
    ... | inj₁ _ = count-helper (suc acc) i'
    ... | inj₂ _ = count-helper acc i'

    -- The number of items strictly less than n for which P holds
    count : ℕ → ℕ
    count = count-helper 0


    P[next] : (n : ℕ) → P (next n)
    P[next] = P[ceil] ∘ suc

    P[gen-helper] : (n : ℕ) (i : ℕ) → P n → P (gen-helper n i)
    P[gen-helper] n zero P[n] = P[n]
    P[gen-helper] n (suc i) P[n] = P[gen-helper] (next n) i (P[next] n)

    P[gen] : ∀ i → P (gen i)
    P[gen] i = P[gen-helper] (ceil 0) i (P[ceil] 0)

    -- This will eventually be proved bijective, under the condition that P and Q are contradictory
    restricted-gen : ℕ → Σ ℕ P
    restricted-gen n = gen n , P[gen] n


    ----------------
    --- Theorems ---
    ----------------

    private
        PQ-contradict-type : Set (α ⊔ β)
        PQ-contradict-type = ∀ n → P n → Q n → ⊥

    next-forward : ∀ m → m < next m
    next-forward = ceil-forward ∘ suc

    gen-helper-pop-next : (n : ℕ) (i : ℕ) → gen-helper n (suc i) ≡ next (gen-helper n i)
    gen-helper-pop-next n zero = ≡-refl
    gen-helper-pop-next n (suc i) = gen-helper-pop-next (next n) i

    gen-pop-next : (i : ℕ) → gen (suc i) ≡ next (gen i)
    gen-pop-next i = gen-helper-pop-next (ceil 0) i

    Q-middle-gen : ∀ n i → gen n < i → i < gen (suc n) → Q i
    Q-middle-gen n i gen[n]<i i<gen[sn] = Q-middle (suc (gen n)) i gen[n]<i (subst (i <_) (gen-pop-next n) i<gen[sn])

    Q-middle-next : ∀ m n → m < n → n < next m → Q n
    Q-middle-next m n m<n n<next[m] = Q-middle (suc m) n m<n n<next[m]

    gen-monotonic' : ∀ m n .{{_ : NonZero n}} → gen m < gen (n + m)
    gen-monotonic' m (suc zero) = subst (gen m <_) (≡-sym (gen-pop-next m)) (next-forward (gen m))
    gen-monotonic' m (suc (suc n)) = <-trans (gen-monotonic' m (suc n)) (subst (gen (suc (n + m)) <_) (≡-sym (gen-pop-next (suc (n + m)))) (next-forward (gen (suc (n + m)))))

    gen-monotonic : ∀ {m n} → .(m < n) → gen m < gen n
    gen-monotonic {m} {n} m<n = subst (λ q → gen m < gen q) {n ∸ m + m} {n} (m∸n+n≡m (<⇒≤ m<n)) (gen-monotonic' m (n ∸ m) {{m<n⇒n∸m-nonZero m<n}})

    gen-injective : Injective _≡_ _≡_ gen
    gen-injective = monotonic⇒injective gen λ m<n → gen-monotonic m<n

    count-helper-eq : ∀ acc i → count-helper acc i ≡ acc + count-helper 0 i
    count-helper-eq acc zero = +-comm 0 acc
    count-helper-eq acc i@(suc i') with PQ-dec i'
    ... | inj₂ _ = count-helper-eq acc i'
    ... | inj₁ _ =
        count-helper (suc acc) i'       ≡⟨ count-helper-eq (suc acc) i' ⟩
        suc acc + count-helper 0 i'     ≡⟨ ≡-sym (+-suc acc (count-helper 0 i')) ⟩
        acc + suc (count-helper 0 i')   ≡⟨ cong (acc +_) (≡-sym (count-helper-eq 1 i')) ⟩
        acc + count-helper 1 i'         ∎
        where open ≡-Reasoning

    count-weakly-monotonic' : ∀ m n → count m ≤ count (n + m)
    count-weakly-monotonic' m zero = ≤-refl
    count-weakly-monotonic' m (suc n) with PQ-dec (n + m)
    ... | inj₁ _ = ≤-trans (count-weakly-monotonic' m n) (≤-trans n≤sn (≤-reflexive (≡-sym (count-helper-eq 1 (n + m)))))
    ... | inj₂ _ = count-weakly-monotonic' m n

    count-weakly-monotonic : ∀ m n → .(m ≤ n) → count m ≤ count n
    count-weakly-monotonic m n m≤n = subst (λ q → count m ≤ count q) {n ∸ m + m} {n} (m∸n+n≡m m≤n) (count-weakly-monotonic' m (n ∸ m))

    module WithContradicition (PQ-contradict : PQ-contradict-type) where
        ceil-weakly-monotonic : ∀ m n → .(m ≤ n) → ceil m ≤ ceil n
        ceil-weakly-monotonic m n m≤n = ≮⇒≥ λ next-m>next-n → ⊥-recompute (PQ-contradict (ceil n) (P[ceil] n) (Q-middle m (ceil n) (≤-trans m≤n (ceil-forward n)) next-m>next-n))

        next-weakly-monotonic : ∀ m n → .(m ≤ n) → next m ≤ next n
        next-weakly-monotonic m n m≤n = ceil-weakly-monotonic (suc m) (suc n) (s≤s m≤n)

        P⇒ceil= : ∀ n → .(P n) → ceil n ≡ n
        P⇒ceil= n P[n] with ceil n ≟ n
        ... | yes ceil[n]=n = ceil[n]=n
        ... | no ceil[n]≠n = ⊥-elim-irr (PQ-contradict n P[n] (Q-middle n n ≤-refl (≤∧≢⇒< (ceil-forward n) (≢-sym (ceil[n]≠n)))))

        Q⇒ceil> : ∀ n → .(Q n) → ceil n > n
        Q⇒ceil> n Q[n] with ≤-cmp (ceil n) n
        ... | inj₂ ceil[n]>n = ceil[n]>n
        ... | inj₁ ceil[n]≤n = ⊥-elim-irr (PQ-contradict n (ceil=⇒P ceil[n]=n) Q[n])
            where
                ceil[n]=n : ceil n ≡ n
                ceil[n]=n = ≤-antisym ceil[n]≤n (ceil-forward n)

        Q⇒ceil[sn]=ceil[n] : ∀ n → .(Q n) → ceil (suc n) ≡ ceil n
        Q⇒ceil[sn]=ceil[n] n Q[n] with ceil (suc n) ≟ ceil n
        ... | yes a = a
        ... | no ceil-sn≠ceil-n = ⊥-elim-irr (PQ-contradict (ceil n) (P[ceil] n) (Q-middle (suc n) (ceil n) ceil-n≥sn ceil-n<ceil-sn))
            where
                ceil-n<ceil-sn : ceil n < ceil (suc n)
                ceil-n<ceil-sn = ≤∧≢⇒< (ceil-weakly-monotonic n (suc n) n≤sn) (≢-sym ceil-sn≠ceil-n)

                ceil-n≥sn : ceil n ≥ suc n
                ceil-n≥sn = Q⇒ceil> n Q[n]

        ceil-idempotent : Idempotent _≡_ ceil
        ceil-idempotent n = P⇒ceil= (ceil n) (P[ceil] n)

        -- count-force-P : ∀ m → .(P m) → count (suc m) ≡ suc (count m)
        -- count-force-P m P[m] with PQ-dec m
        -- ... | inj₁ _ = count-helper-eq 1 m
        -- ... | inj₂ Q[m] = ⊥-elim-irr (PQ-contradict m P[m] Q[m])

        -- count-force-Q : ∀ m → .(Q m) → count (suc m) ≡ count m
        -- count-force-Q m Q[m] with PQ-dec m
        -- ... | inj₁ P[m] = ⊥-elim-irr (PQ-contradict m P[m] Q[m])
        -- ... | inj₂ _ = ≡-refl


        count-gen-inv-near-0 : ∀ i → .(i ≤ gen 0) → count i ≡ 0
        count-gen-inv-near-0 zero _ = ≡-refl
        count-gen-inv-near-0 i@(suc i') i≤gen[0] with PQ-dec i'
        ... | inj₁ P[i'] = ⊥-elim-irr (PQ-contradict i' P[i'] (Q-middle 0 i' _≤_.z≤n i≤gen[0]))
        ... | inj₂ _ = count-gen-inv-near-0 i' (≤-trans n≤sn i≤gen[0])

        count-gen-inv-elsewhere : ∀ i j → gen i < j → j ≤ gen (suc i) → count j ≡ suc (count (gen i))
        count-gen-inv-elsewhere i zero ()
        count-gen-inv-elsewhere i j@(suc j') gen[i]<j j≤gen[si] with PQ-dec j' | j' ≟ gen i
        ... | inj₁ P[j'] | no ¬j'=gen[i] = ⊥-elim-irr (PQ-contradict j' P[j'] (Q-middle-gen i j' (≤∧≢⇒< (s≤s⁻¹ gen[i]<j) (≢-sym ¬j'=gen[i])) j≤gen[si]))
        ... | inj₁ P[j'] | yes ≡-refl = count-helper-eq 1 j'
        ... | inj₂ Q[j'] | no ¬j'=gen[i] = count-gen-inv-elsewhere i j' (≤∧≢⇒< (s≤s⁻¹ gen[i]<j) (≢-sym ¬j'=gen[i])) (≤-trans n≤sn j≤gen[si])
        ... | inj₂ Q[j'] | yes ≡-refl = ⊥-elim-irr (PQ-contradict j' (P[gen] i) Q[j'])

        count-gen : RightInverse _≡_ _≡_ count gen
        count-gen zero = count-gen-inv-near-0 (gen zero) ≤-refl
        count-gen (suc i) =
            count (gen (suc i))     ≡⟨ count-gen-inv-elsewhere i (gen (suc i)) ((gen-monotonic {i} n<sn)) ≤-refl ⟩
            suc (count (gen i))     ≡⟨ cong suc (count-gen i) ⟩
            suc i                   ∎
            where open ≡-Reasoning

        open import Plasmaduck.Counting.GeneralizedMinimum P Q using (Minimum; module FindMinimum; module IsMinimum)
        open FindMinimum PQ-dec using (find-minimum)
        open IsMinimum (λ {m} → PQ-contradict m) using (minimum-unique)


        gen-count : ∀ n → gen (count n) ≡ ceil n
        gen-count zero = ≡-refl
        gen-count n@(suc n') with PQ-dec n'
        ... | inj₁ P[n'] =
            gen (count-helper 1 n')     ≡⟨ cong gen (count-helper-eq 1 n') ⟩
            gen (suc (count n'))        ≡⟨ gen-pop-next (count n') ⟩
            next (gen (count n'))       ≡⟨ cong next (gen-count n') ⟩
            next (ceil n')              ≡⟨ cong next (P⇒ceil= n' P[n']) ⟩
            next n'                     ≡⟨⟩
            ceil (suc n')               ∎
            where open ≡-Reasoning
        ... | inj₂ Q[n'] =
            gen (count n')  ≡⟨ gen-count n' ⟩
            ceil n'         ≡⟨ ≡-sym (Q⇒ceil[sn]=ceil[n] n' Q[n']) ⟩
            ceil (suc n')   ∎
            where open ≡-Reasoning

        -- The above one is stronger, which is why it gets the main name.
        -- But this one is important to the bijection between ℕ and Σ ℕ P
        gen-count' : ∀ n → .(P n) → gen (count n) ≡ n
        gen-count' n P[n] =
            gen (count n)   ≡⟨ gen-count n ⟩
            ceil n          ≡⟨ P⇒ceil= n P[n] ⟩
            n               ∎
            where open ≡-Reasoning

        restricted-gen-bijective : Bijective _≡_ (_≡_ Function.on proj₁) restricted-gen
        restricted-gen-bijective = both-inv→bijective A B (restricted-gen which-is-cong from-discrete-cong B restricted-gen) ((partial-count which-is-cong λ { ≡-refl → ≡-refl }) , count-gen , λ (x , P[x]) → gen-count' x P[x])
            where
                A = discrete-setoid ℕ
                B = property-subset-setoid (discrete-setoid ℕ) P

                -- inverse
                partial-count : Σ ℕ P → ℕ
                partial-count = count ∘ proj₁

        restricted-gen-surjective : Surjective _≡_ (_≡_ Function.on proj₁) restricted-gen
        restricted-gen-surjective = restricted-gen-bijective .proj₂
    open WithContradicition public

-- Given you know one exists, find the next one
module ExistsToCeil
    (PQ-dec : ∀ n → P n ⊎ Q n)
    (exists : ℕ → ℕ)
    (exists-forward : ∀ n → n ≤ exists n)
    (P[exists] : ∀ n → P (exists n))
    where

    PQ-contradict-type : Set (α ⊔ β)
    PQ-contradict-type = ∀ n → P n → Q n → ⊥

    module _ (m : ℕ) where

        open FlattenedProperties m
        open import Plasmaduck.Counting.GeneralizedMinimum P' Q' using (module FindMinimum; module IsMinimum)
        open FindMinimum (PQ'-dec PQ-dec) using (find-minimum)

        ceil-min-value = find-minimum (exists m ∸ m , subst P (≡-sym (m∸n+n≡m (exists-forward m))) (P[exists] m))
        ceil-is-minimum = ceil-min-value .proj₂

        ceil : ℕ
        ceil = ceil-min-value .proj₁ + m

        P[ceil] : P ceil
        P[ceil] = ceil-is-minimum .proj₁

        Q-middle : ∀ n → .(m ≤ n) → n < ceil → Q n
        Q-middle n m≤n n<ceil = subst Q (m∸n+n≡m m≤n) (ceil-is-minimum .proj₂ (n ∸ m , (begin
            suc (n ∸ m)                     ≡⟨ ∸-suc n m m≤n ⟩
            suc n ∸ m                       ≤⟨ ∸-monoˡ-≤ {suc n} {ceil} m n<ceil ⟩
            ceil ∸ m                        ≡⟨⟩
            ceil-min-value .proj₁ + m ∸ m   ≡⟨ m+n∸n≡m (ceil-min-value .proj₁) (m) ⟩
            ceil-min-value .proj₁           ∎)))
            where open ≤-Reasoning

        ceil-forward : m ≤ ceil
        ceil-forward = m≤n+m m (ceil-min-value .proj₁)

    module _ where
        open import Plasmaduck.Counting.GeneralizedMinimum P Q using (Minimum; module FindMinimum)
        open FindMinimum PQ-dec using (find-minimum)

        min-value : Minimum
        min-value = find-minimum (exists 0 , P[exists] 0)

    open CeilToGenerator ceil P[ceil] (λ x y z → Q-middle x y z) ceil-forward public
