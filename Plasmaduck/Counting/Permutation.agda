open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; cong; cong-app; refl; sym; trans; inspect; [_])
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open import Relation.Binary using (Setoid; Rel; IsEquivalence; IsDecTotalOrder; tri<; tri≈; tri>)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Function using (_∘_; _∋_; id; Bijective; Bijection; Injective; Surjective)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (ℕ; _≤_; _<_; _>_; z≤n; s≤s; s≤s⁻¹; _∸_; _+_; NonZero; >-nonZero) renaming (zero to zeroℕ; suc to sucℕ; pred to predℕ; _≟_ to _≟ℕ_)
open import Data.Nat.Properties using (module ≤-Reasoning; <-cmp; suc-pred; ≤-reflexive; ≤-refl; ≤-trans; ≤-<-trans; <-≤-trans; <-trans; ≰⇒≥; <⇒≱; ≮⇒≥; <⇒≤; ≤-antisym; <-irrefl; +-mono-≤; +-mono-<; ∸-mono; +-suc; +-comm; +-assoc; m≤n+m; m∸n≤m; m≤m+n; m+n≤o⇒m≤o; m+n≤o⇒n≤o; m+n∸n≡m; m+[n∸m]≡n; +-∸-assoc; ∸-monoʳ-<; m∸[m∸n]≡n; m∸n+n≡m)
open import Data.Fin using (Fin; _≟_; _≤?_; _<?_; toℕ; fromℕ<) renaming (zero to zero-fin; suc to suc-fin; _<_ to _<-fin_; _≤_ to _≤-fin_; _≥_ to _≥-fin_)
open import Data.Fin.Properties using (toℕ-fromℕ<; fromℕ<-toℕ; fromℕ<-cong; toℕ<n; toℕ-injective; fromℕ<-injective) renaming (≤-isDecTotalOrder to ≤-fin-isDecTotalOrder)
open import Data.List using (List; foldl; _∷_; []; length; lookup; drop; _++_; reverse)
open import Data.List.Properties using (drop-drop; reverse-++)

open import Plasmaduck.SetoidExperiment.SetoidMachinery using (discrete-setoid; from-discrete-cong; SetoidFunction₂; _which-is-cong₂_; _←₂_; SetoidFunction; _which-is-cong_; _←_; property-subset-setoid)
open import Plasmaduck.Function.Properties using (module SingleOperator)
open import Plasmaduck.Util.Case using (case_of_)
open import Plasmaduck.Data.FakeFin using (FakeFin; realize; falsify)
open import Plasmaduck.Data.Squash using (Squash; squash)
open import Plasmaduck.Data.Nat using (≤-recompute; n≤n; n≤sn; n<sn; ≤→<≡; ∸-suc; m∸n∸o≡m∸[n+o])
open import Plasmaduck.Data.List using (drop-lookup)
open import Plasmaduck.Data.Product using (Σ≡; ×≡; uncurry; curry)
open import Plasmaduck.Util.TypeChange using (change-type-input-dependence-irrelevance)
open import Plasmaduck.Relation.Equivalence using (irrelevant-cong; irrelevant-cong₂)
open import Plasmaduck.Function.Bijection using (_∘-bijective_; id-bijective; bijective-is-functional)
open import Plasmaduck.Function using (_≈_; ≈-sym)



module Plasmaduck.Counting.Permutation where

variable
    a b c : Level
    m n : ℕ

fin-setoid : ℕ → Setoid lzero lzero
fin-setoid n = discrete-setoid (Fin n)

Permutation : ℕ → Set
Permutation n = Bijection (fin-setoid n) (fin-setoid n)

-- i hate proving things using with abstraction
swp-helper : (i j k : Fin n) → Dec (i ≡ k) → Dec (j ≡ k) → Fin n
swp-helper i j k (yes _) _ = j
swp-helper i j k (no _) (yes _) = i
swp-helper i j k (no _) (no _) = k

-- Given i and j, return a function that is the identity, except it swaps i and j.
swp : Fin n → Fin n → Fin n → Fin n
swp i j k = swp-helper i j k (i ≟ k) (j ≟ k)

module SwapLemmas where
    switch-lemma : (i j k : Fin n) → swp i j k ≡ swp j i k
    switch-lemma i j k with i ≟ k | j ≟ k
    ... | yes i=k | yes j=k = trans j=k (sym i=k)
    ... | yes i=k | no j≠k = refl
    ... | no i≠k | yes j=k = refl
    ... | no i≠k | no j≠k = refl

    match₁-lemma : (i k : Fin n) → swp i i k ≡ k
    match₁-lemma i k with i ≟ i | i ≟ k
    ... | yes i=i | yes i=k = i=k
    ... | yes i=i | no i≠k = refl
    ... | no i≠i | _ = ⊥-elim (i≠i refl)

    match₂-lemma : (i j : Fin n) → swp i j j ≡ i
    match₂-lemma i j with i ≟ j | j ≟ j
    ... | _ | no j≠j = ⊥-elim (j≠j refl)
    ... | yes i=j | yes j=j = sym i=j
    ... | no i≠j | yes j=j = refl

    matchₒ-lemma : (i j : Fin n) → swp i j i ≡ j
    matchₒ-lemma i j =
        swp i j i   ≡⟨ switch-lemma i j i ⟩
        swp j i i   ≡⟨ match₂-lemma j i ⟩
        j           ∎
        where open ≡-Reasoning

    no-then-id : (i j k : Fin n) → (i≠k : i ≢ k) (j≠k : j ≢ k) → swp i j k ≡ k
    no-then-id i j k i≠k j≠k with i ≟ k | j ≟ k
    ... | yes i=k | _ = ⊥-elim (i≠k i=k)
    ... | _ | yes j=k = ⊥-elim (j≠k j=k)
    ... | no _ | no _ = refl

    swp-involution : (i j k : Fin n) → swp i j (swp i j k) ≡ k
    swp-involution i j k with i ≟ k | j ≟ k
    ... | yes i=k | _ = trans (match₂-lemma i j) i=k
    ... | no i≠k | yes j=k = trans (matchₒ-lemma i j) j=k
    ... | no i≠k | no j≠k = no-then-id i j k i≠k j≠k

    low-swp-is-low : (i j k l : Fin n) → i ≤-fin l → j ≤-fin l → k ≤-fin l → swp i j k ≤-fin l
    low-swp-is-low i j k l i≤l j≤l k≤l with i ≟ k | j ≟ k
    ... | yes _ | _ = j≤l
    ... | no _ | yes _ = i≤l
    ... | no _ | no _ = k≤l

open SwapLemmas

swp-is-bijective : (i j : Fin n) → Bijective _≡_ _≡_ (swp i j)
swp-is-bijective i j = inj , surj
    where
        open ≡-Reasoning

        inj : Injective _≡_ _≡_ (swp i j)
        inj {k} {l} k'=l' with i ≟ k | j ≟ k | i ≟ l | j ≟ l
        ... | yes i=k | _ | yes i=l | _ = trans (sym i=k) i=l
        ... | yes i=k | _ | no i≠l | yes j=l = trans (trans (sym i=k) (sym k'=l')) j=l
        ... | yes i=k | _ | no i≠l | no j≠l = ⊥-elim (j≠l k'=l')
        ... | no i≠k | yes j=k | yes i=l | _ = trans (trans (sym j=k) (sym k'=l')) i=l
        ... | no i≠k | yes j=k | no _ | yes j=l = trans (sym j=k) j=l
        ... | no i≠k | yes j=k | no i≠l | no j≠l = ⊥-elim (i≠l k'=l')
        ... | no i≠k | no j≠k | yes i=l | _ = ⊥-elim (j≠k (sym k'=l'))
        ... | no i≠k | no j≠k | no i≠l | yes j=l = ⊥-elim (i≠k (sym k'=l'))
        ... | no _ | no _ | no _ | no _ = k'=l'

        surj : Surjective _≡_ _≡_ (swp i j)
        surj k with i ≟ k | j ≟ k
        ... | yes i=k | j≟k = j , λ { {z} refl →
            swp i z z   ≡⟨ match₂-lemma i z ⟩
            i           ≡⟨ i=k ⟩
            k           ∎ }
        ... | no i≠k | yes j=k = i , λ { {z} refl →
            swp z j z   ≡⟨ matchₒ-lemma z j ⟩
            j           ≡⟨ j=k ⟩
            k           ∎ }
        ... | no i≠k | no j≠k = k , λ { {z} refl → no-then-id i j k i≠k j≠k }

swap : Fin n → Fin n → Permutation n
swap {n} i j = record {
    to = swp i j;
    cong = from-discrete-cong (fin-setoid n) (swp i j);
    bijective = swp-is-bijective i j
    }


module Monotonicity where
    StrictlyMonotonicFin : (f : Fin m → Fin n) → Set
    StrictlyMonotonicFin {m = m} f = (∀ (i j : ℕ) → .(i<j : i < j) → .(j<m : j < m) → f (fromℕ< {i} (<-trans i<j j<m)) <-fin f (fromℕ< {j} j<m))

    private
        strictly-monotonic⇒is-not-lt : (f : Fin n → Fin n) → StrictlyMonotonicFin f →
            ∀ k → .(k<n : k < n) → ¬ toℕ (f (fromℕ< {k} k<n)) < k
        strictly-monotonic⇒is-not-lt f f-monotonic zeroℕ k<n = λ ()
        strictly-monotonic⇒is-not-lt {n = n} f f-monotonic k@(sucℕ k') k<n fk<k = strictly-monotonic⇒is-not-lt f f-monotonic k' k'<n (begin
            sucℕ (toℕ (f (fromℕ< {k'} k'<n)))   ≤⟨ f-monotonic k' k n<sn k<n ⟩
            (toℕ (f (fromℕ< {k} k<n)))          ≤⟨ s≤s⁻¹ fk<k ⟩
            k'                                  ∎)
            where
                open ≤-Reasoning
                k'<n : k' < n
                k'<n = ≤-trans n≤sn (≤-recompute k<n)

        strictly-monotonic⇒is-not-gt : (f : Fin n → Fin n) → StrictlyMonotonicFin f →
            ∀ k → .(k<n : k < n) → ¬ toℕ (f (fromℕ< {k} k<n)) > k
        strictly-monotonic⇒is-not-gt {n = n} f f-monotonic k k<n = λ fk>k → helper (predℕ n ∸ k) (≤-trans (s≤s (m∸n≤m (predℕ n) k)) (≤-reflexive spn=n)) (<-≤-trans (≤-<-trans (≤-reflexive (m∸[m∸n]≡n {predℕ n} {k} (reduce-≤n (≤-recompute k<n)))) fk>k) (≤-reflexive (irrelevant-cong (_< n) (λ q q<n → toℕ (f (fromℕ< {q} q<n))) {k} {predℕ n ∸ (predℕ n ∸ k)} {y = k<n} {z = ≤-<-trans (≤-reflexive (m∸[m∸n]≡n {predℕ n} {k} (reduce-≤n (≤-recompute k<n)))) k<n} (sym (m∸[m∸n]≡n {predℕ n} {k} (reduce-≤n (≤-recompute k<n)))))))
            where
                n-is-not-zero : NonZero n
                n-is-not-zero = >-nonZero (≤-<-trans z≤n (≤-recompute k<n))

                spn=n : sucℕ (predℕ n) ≡ n
                spn=n = suc-pred n {{n-is-not-zero}}

                pred-n<n : predℕ n < n
                pred-n<n = ≤-reflexive spn=n

                reduce-<n : {k : ℕ} → sucℕ k < n → k < predℕ n
                reduce-<n sk<n = s≤s⁻¹ (<-≤-trans sk<n (≤-reflexive (sym spn=n)))

                reduce-≤n : {k : ℕ} → sucℕ k ≤ n → k ≤ predℕ n
                reduce-≤n sk≤n = s≤s⁻¹ (≤-trans sk≤n (≤-reflexive (sym spn=n)))

                helper : ∀ k → .(k<n : k < n) → ¬ toℕ (f (fromℕ< {predℕ n ∸ k} (≤-<-trans (m∸n≤m (predℕ n) k) pred-n<n))) > predℕ n ∸ k
                helper zeroℕ k<n f[n∸1]>n∸1 = <⇒≱ (toℕ<n (f (fromℕ< {predℕ n} pred-n<n))) (≤-trans (≤-reflexive (sym spn=n)) f[n∸1]>n∸1)
                helper k@(sucℕ k') k<n thing = <⇒≱ thing (s≤s⁻¹ (begin
                    sucℕ (toℕ (f (fromℕ< {predℕ n ∸ k} (≤-<-trans (m∸n≤m (predℕ n) k) pred-n<n)))) ≤⟨ f-monotonic (predℕ n ∸ k) (predℕ n ∸ k') (∸-monoʳ-< {predℕ n} {k} {k'} n<sn (reduce-<n k<n)) (≤-<-trans (m∸n≤m (predℕ n) k') pred-n<n) ⟩
                    toℕ (f (fromℕ< {predℕ n ∸ k'} (≤-<-trans (m∸n≤m (predℕ n) k') pred-n<n))) ≤⟨ ≮⇒≥ (helper k' (≤-<-trans n≤sn k<n)) ⟩
                    predℕ n ∸ k'            ≡⟨ sym (∸-suc (predℕ n) k (reduce-<n k<n)) ⟩
                    sucℕ (predℕ n ∸ k) ∎))
                    where open ≤-Reasoning

    strictly-monotonic⇒is-id : (f : Fin n → Fin n) → StrictlyMonotonicFin f →
        ∀ k → .(k<n : k < n) → toℕ (f (fromℕ< {k} k<n)) ≡ k
    strictly-monotonic⇒is-id f f-monotonic k k<n with <-cmp (toℕ (f (fromℕ< {k} k<n))) k
    ... | tri< fk<k _ _ = ⊥-elim (strictly-monotonic⇒is-not-lt f f-monotonic k k<n fk<k)
    ... | tri≈ _ fk=k _ = fk=k
    ... | tri> _ _ fk>k = ⊥-elim (strictly-monotonic⇒is-not-gt f f-monotonic k k<n fk>k)


module SwapList where
    SwapList : ℕ → Set
    SwapList n = List (Fin n × Fin n)

    swap-with-things : (Fin n → Fin n) → SwapList n → Fin n → Fin n
    swap-with-things = foldl (λ acc (i , j) → swp i j ∘ acc)

    swap-with-list : SwapList n → Fin n → Fin n
    swap-with-list l k = swap-with-things id l k

    IsSwapDecomposition : (Fin n → Fin n) → SwapList n → Set
    IsSwapDecomposition p l = ∀ k → swap-with-list l k ≡ p k

    SwapDecomposition : (Fin n → Fin n) → Set
    SwapDecomposition {n} p = Σ (SwapList n) (IsSwapDecomposition p)

    swap-pop-func :
        (start : Fin m → Fin m)
        (l : SwapList m) →
        swap-with-things start l ≡ swap-with-things id l ∘ start
    swap-pop-func start [] = refl
    swap-pop-func start (ij@(i , j) ∷ l) =
        swap-with-things start (ij ∷ l)             ≡⟨⟩
        swap-with-things (swp i j ∘ start) l        ≡⟨ swap-pop-func (swp i j ∘ start) l ⟩
        (swap-with-things id l ∘ swp i j ∘ start)   ≡⟨ cong (_∘ start) (sym (swap-pop-func (swp i j) l)) ⟩
        (swap-with-things id (ij ∷ l) ∘ start)      ∎
        where open ≡-Reasoning

    swap-pop-initial :
        (start : Fin m → Fin m)
        (l : SwapList m) →
        (i j : Fin m) →
        swap-with-things start ((i , j) ∷ l) ≡ (swap-with-things id l ∘ swp i j ∘ start)
    swap-pop-initial start l i j = swap-pop-func (swp i j ∘ start) l

    ++-swap-split :
        (start : Fin m → Fin m)
        (l₁ l₂ : SwapList m) →
        swap-with-things start (l₁ ++ l₂) ≡ swap-with-list l₂ ∘ swap-with-things start l₁
    ++-swap-split start [] l₂ = swap-pop-func start l₂
    ++-swap-split start ((x , y) ∷ l₁) l₂ =
        swap-with-things start (((x , y) ∷ l₁) ++ l₂)               ≡⟨⟩
        swap-with-things (swp x y ∘ start) (l₁ ++ l₂)               ≡⟨ ++-swap-split (swp x y ∘ start) l₁ l₂ ⟩
        swap-with-list l₂ ∘ swap-with-things (swp x y ∘ start) l₁   ≡⟨⟩
        swap-with-list l₂ ∘ swap-with-things start ((x , y) ∷ l₁)   ∎
        where open ≡-Reasoning

    swap-with-list-reverse-is-right-inverse : (l : SwapList n) (k : Fin n) → (swap-with-list l ∘ swap-with-list (reverse l)) k ≡ k
    swap-with-list-reverse-is-right-inverse [] k = refl
    swap-with-list-reverse-is-right-inverse (x ∷ l) k =
        (swap-with-list (x ∷ l) ∘ swap-with-list (reverse (x ∷ l))) k                                           ≡⟨⟩
        (swap-with-list ((x ∷ []) ++ l) ∘ swap-with-list (reverse ((x ∷ []) ++ l))) k                           ≡⟨ cong (λ q → (swap-with-list ((x ∷ []) ++ l) ∘ swap-with-list q) k) (reverse-++ (x ∷ []) l) ⟩
        (swap-with-list ((x ∷ []) ++ l) ∘ swap-with-list (reverse l ++ (x ∷ []))) k                             ≡⟨ cong-app (cong (_∘ swap-with-list (reverse l ++ (x ∷ []))) (++-swap-split id (x ∷ []) l)) k ⟩
        (swap-with-list l ∘ swap-with-list (x ∷ []) ∘ swap-with-list (reverse l ++ (x ∷ []))) k                 ≡⟨ cong-app (cong ((swap-with-list l ∘ swap-with-list (x ∷ [])) ∘_) (++-swap-split id (reverse l) (x ∷ []))) k ⟩
        (swap-with-list l ∘ swap-with-list (x ∷ []) ∘ swap-with-list (x ∷ []) ∘ swap-with-list (reverse l)) k   ≡⟨ cong (swap-with-list l) (swp-involution (x .proj₁) (x .proj₂) (swap-with-list (reverse l) k)) ⟩
        (swap-with-list l ∘ swap-with-list (reverse l)) k                                                       ≡⟨ swap-with-list-reverse-is-right-inverse l k ⟩
        k                                                                                                  ∎
        where open ≡-Reasoning

    -- this is horrendous
    swap-with-list-bijective : (l : SwapList n) → Bijective _≡_ _≡_ (swap-with-list l)
    swap-with-list-bijective [] = id-bijective
    swap-with-list-bijective {n = n} ((i , j) ∷ l) =
        bijective-is-functional
            {A-setoid = discrete-setoid (Fin n)}
            {B-setoid = discrete-setoid (Fin n)}
            {f = record {func = f; respects = from-discrete-cong disc-n f}}
            {g = record {func = g; respects = from-discrete-cong disc-n g}}
            (cong-app (sym (swap-pop-initial id l i j)))
            (_∘-bijective_ {s₁ = disc-n} {s₂ = disc-n} {s₃ = disc-n}
                {g = swap-with-list l} (swap-with-list-bijective l)
                {f = swp i j} (swp-is-bijective i j)
            )
        where
            disc-n = discrete-setoid (Fin n)
            f = swap-with-list l ∘ swp i j
            g = swap-with-list ((i , j) ∷ l)


module Sorting {A : Set a} {_≈A_ : Rel A b} {_≤A_ : Rel A c} (≤A-decTotal : IsDecTotalOrder _≈A_ _≤A_) where
    open IsDecTotalOrder ≤A-decTotal using () renaming (
        _≤?_ to _≤A?_;
        _≟_ to _≟A_;
        reflexive to ≤A-reflexive;
        refl to ≤A-refl;
        trans to ≤A-trans;
        antisym to ≤A-antisym;
        isEquivalence to ≈A-isEquivalence
        )
    open IsEquivalence ≈A-isEquivalence using () renaming (
        reflexive to ≈A-reflexive;
        refl to ≈A-refl;
        sym to ≈A-sym;
        trans to ≈A-trans
        )
    open SwapList

    _≥A_ : Rel A c
    _≥A_ x y = y ≤A x

    module ≤A-Reasoning where
        open import Relation.Binary.Reasoning.Syntax

        open begin-syntax _≤A_ Function.id public
        open ≡-syntax _≤A_ ((λ a≡b b≤c → ≤A-trans (≤A-reflexive (≈A-reflexive a≡b)) b≤c)) public
        open ≈-syntax {R = _≈A_} _≤A_ _≤A_ (λ a≈b b≤c → ≤A-trans (≤A-reflexive a≈b) b≤c) public
        open ≤-syntax _≤A_ _≤A_ ≤A-trans public
        open end-syntax _≤A_ ≤A-refl public

    {-
        How am I modelling progress towards creating p?
        If I have a function, I can slowly move it towards id by imposing swaps.
        and then I will have something like (swap-with-list l) ∘ p = id
        then if i prove the lemma that (swap-with-list (reverse l)) is the right inverse of (swap-with-list l)
        then i can show that (swap-with-list (reverse l)) is equal to p.
    -}
    module _ (f : Fin m → A) where
        find-max-lower : (o : ℕ) → .(o < m) → Fin m
        find-max-lower zeroℕ z<m with ≤-recompute z<m
        ... | s≤s z≤n = zero-fin
        find-max-lower i@(sucℕ i') i<m with find-max-lower i' (≤-trans n≤sn i<m)
        ... | prev-max with f (fromℕ< {i} i<m) ≤A? f prev-max
        ...   | yes _ = prev-max
        ...   | no _ = fromℕ< {i} i<m

        find-max-lower-yields-low : {o : ℕ} → .(o<m : o < m) → toℕ (find-max-lower o o<m) ≤ o
        find-max-lower-yields-low {zeroℕ} o<m with ≤-recompute o<m
        ... | s≤s z≤n = ≤-refl
        find-max-lower-yields-low {i@(sucℕ i')} i<m with find-max-lower i' (≤-trans n≤sn i<m) | inspect {A = FakeFin m} {B = λ _ → Fin m} (λ {(q , squash q<m) → find-max-lower q q<m}) (i' , squash (≤-trans n≤sn i<m))
        ... | prev-max | [ prev-max= ] with f (fromℕ< {i} i<m) ≤A? f prev-max
        ...   | yes _ = begin
            toℕ prev-max                                ≤⟨ ≤-reflexive (cong toℕ (sym prev-max=)) ⟩
            toℕ (find-max-lower i' (≤-trans n≤sn i<m))  ≤⟨ find-max-lower-yields-low {i'} (≤-trans n≤sn i<m) ⟩
            i'                                          ≤⟨ n≤sn ⟩
            i                                           ∎
            where open ≤-Reasoning
        ...   | no _ = ≤-reflexive (
            toℕ (fromℕ< {i} i<m)    ≡⟨ toℕ-fromℕ< i<m ⟩
            i                       ∎)
            where open ≡-Reasoning

        find-max-lower-is-max : {i : Fin m} {j : ℕ} → .(i≤j : toℕ i ≤ j) → .(j<m : j < m) → f (find-max-lower j j<m) ≥A f i
        find-max-lower-is-max {zero-fin} {zeroℕ} i≤j j<m with ≤-recompute j<m
        ... | s≤s z≤n = ≤A-refl
        find-max-lower-is-max {i} {j@(sucℕ j')} i≤j j<m with toℕ i ≟ℕ j
        ... | yes toℕ-i=j with find-max-lower j' (≤-trans n≤sn j<m)
        ...     | prev-max with f (fromℕ< {j} j<m) ≤A? f prev-max
        ...     | yes pf =
            f i                                     ≡⟨ cong f (sym (fromℕ<-toℕ i (≤-<-trans i≤j j<m))) ⟩
            f (fromℕ< {toℕ i} (≤-<-trans i≤j j<m))  ≡⟨ irrelevant-cong (_< m) (λ q q<m → f (fromℕ< {q} q<m)) {y = ≤-<-trans i≤j j<m} {z = j<m} toℕ-i=j ⟩
            f (fromℕ< {j} j<m)                      ≤⟨ pf ⟩
            f prev-max                              ∎
            where open ≤A-Reasoning
        ...     | no _ = ≤A-reflexive (≈A-reflexive (cong f (trans (sym (fromℕ<-toℕ i (≤-<-trans i≤j j<m))) (irrelevant-cong (_< m) (λ q q<m → fromℕ< {q} q<m) {y = ≤-<-trans i≤j j<m} {z = j<m} toℕ-i=j))))
        find-max-lower-is-max {i} {j@(sucℕ j')} i≤j j<m | no i≠j with find-max-lower j' (≤-trans n≤sn j<m) | inspect {A = FakeFin m} {B = λ _ → Fin m} (λ {(q , squash q<m) → find-max-lower q q<m}) (j' , squash (≤-trans n≤sn j<m))
        ...     | prev-max | [ prev-max= ] with f (fromℕ< {j} j<m) ≤A? f prev-max
        ...     | yes _ = begin
            f i                                         ≤⟨ find-max-lower-is-max {i} {j'} (case ≤→<≡ i≤j of λ { (inj₁ (s≤s i≤j')) → i≤j'; (inj₂ i=j) → ⊥-elim (i≠j i=j) }) (≤-trans n≤sn j<m) ⟩
            f (find-max-lower j' (≤-trans n≤sn j<m))    ≡⟨ cong f prev-max= ⟩
            f prev-max                                  ∎
            where open ≤A-Reasoning
        ...     | no f[j]≰f[prev] = begin
            f i                                         ≤⟨ find-max-lower-is-max {i} {j'} (case ≤→<≡ i≤j of λ { (inj₁ (s≤s i≤j')) → i≤j'; (inj₂ i=j) → ⊥-elim (i≠j i=j) }) (≤-trans n≤sn j<m) ⟩
            f (find-max-lower j' (≤-trans n≤sn j<m))    ≡⟨ cong f prev-max= ⟩
            f prev-max                                  ≤⟨ (case (≤A-decTotal .IsDecTotalOrder.total (f prev-max) (f (fromℕ< {j} j<m))) of λ { (inj₁ pf) → pf; (inj₂ pf) → ⊥-elim (f[j]≰f[prev] pf) }) ⟩
            f (fromℕ< {j} j<m)                          ∎
            where open ≤A-Reasoning

    pair-at : (f : Fin m → A) → (o : ℕ) → .(o<m : o < m) → (l : SwapList m) → Fin m × Fin m
    pair-at f o o<m l = fromℕ< {o} o<m , find-max-lower (f ∘ swap-with-list l) o o<m

    -- finds the maximum item out of the items ≤ o (on function f ∘ swap-with-list l), swaps it to o, then recurses down.
    partial-decomposition : (f : Fin m → A) → (o : ℕ) → .(o < m) → SwapList m → SwapList m
    partial-decomposition f zeroℕ o<m l = l
    partial-decomposition f o@(sucℕ o') o<m l = partial-decomposition f o' (≤-trans n≤sn o<m) (pair-at f o o<m l ∷ l)

    partial-decomposition-length-lemma :
        (f : Fin m → A) → (o : ℕ) → .(o<m : o < m) → (l : SwapList m) →
        length (partial-decomposition f o o<m l) ≡ length l + o
    partial-decomposition-length-lemma f zeroℕ o<m l = sym (+-comm (length l) zeroℕ)
    partial-decomposition-length-lemma f o@(sucℕ o') o<m l =
        length (partial-decomposition f o o<m l)    ≡⟨ partial-decomposition-length-lemma f o' (≤-trans n≤sn o<m) ((fromℕ< {o} o<m , find-max-lower (f ∘ swap-with-list l) o o<m) ∷ l) ⟩
        (1 + length l) + o'                         ≡⟨ cong (_+ o') (+-comm 1 (length l)) ⟩
        (length l + 1) + o'                         ≡⟨ +-assoc (length l) 1 o' ⟩
        length l + (1 + o')                         ≡⟨⟩
        length l + o                                ∎
        where open ≡-Reasoning

    partial-decomposition-drop-lemma :
        (f : Fin m → A) → (o : ℕ) → .(o<m : o < m) → (l : SwapList m) →
        drop o (partial-decomposition f o o<m l) ≡ l
    partial-decomposition-drop-lemma f zeroℕ o<m l = refl
    partial-decomposition-drop-lemma f o@(sucℕ o') o<m l =
        drop (1 + o') (partial-decomposition f o o<m l)                                             ≡⟨ cong-app (cong drop (+-comm 1 o')) (partial-decomposition f o o<m l) ⟩
        drop (o' + 1) (partial-decomposition f o o<m l)                                             ≡⟨ sym (drop-drop o' 1 (partial-decomposition f o o<m l)) ⟩
        drop 1 (drop o' (partial-decomposition f o o<m l))                                          ≡⟨⟩
        drop 1 (drop o' (partial-decomposition f o' (≤-trans n≤sn o<m) (pair-at f o o<m l ∷ l)))    ≡⟨ cong (drop 1) (partial-decomposition-drop-lemma f o' (≤-trans n≤sn o<m) (pair-at f o o<m l ∷ l)) ⟩
        drop 1 (pair-at f o o<m l ∷ l)                                                              ≡⟨⟩
        l                                                                                           ∎
        where open ≡-Reasoning

    -- not tail-recursive; use for proofs
    -- only includes the first i entries
    partial-decomposition-range :
        (f : Fin m → A) → (o : ℕ) → .(o<m : o < m) → (l : SwapList m) →
        (i : ℕ) → .(i≤o : i ≤ o) →
        SwapList m
    partial-decomposition-range f o o<m l zeroℕ i≤o = l
    partial-decomposition-range f o o<m l i@(sucℕ i') i≤o with partial-decomposition-range f o o<m l i' (≤-trans n≤sn i≤o)
    ... | l' = pair-at f (sucℕ (o ∸ i)) (≤-<-trans (≤-reflexive (∸-suc o i i≤o)) (≤-<-trans (m∸n≤m o i') o<m)) l' ∷ l'

    partial-decomposition-range-length :
        (f : Fin m → A) → (o : ℕ) → .(o<m : o < m) → (l : SwapList m) →
        (i : ℕ) → .(i≤o : i ≤ o) →
        length (partial-decomposition-range f o o<m l i i≤o) ≡ length l + i
    partial-decomposition-range-length f o o<m l zeroℕ i≤o = sym (+-comm (length l) zeroℕ)
    partial-decomposition-range-length f o o<m l i@(sucℕ i') i≤o with partial-decomposition-range f o o<m l i' (≤-trans n≤sn i≤o) | partial-decomposition-range-length f o o<m l i' (≤-trans n≤sn i≤o)
    ... | l' | l'-length =
        sucℕ (length l')        ≡⟨ cong sucℕ l'-length ⟩
        sucℕ (length l + i')    ≡⟨ sym (+-suc (length l) i') ⟩
        length l + sucℕ i'      ∎
        where open ≡-Reasoning

    -- skip by i indices
    partial-decomposition-skip-lemma :
        (f : Fin m → A) → (o : ℕ) → .(o<m : o < m) → (l : SwapList m) →
        (i : ℕ) → .(i≤o : i ≤ o) →
        partial-decomposition f o o<m l ≡ partial-decomposition f (o ∸ i) (≤-<-trans (m∸n≤m o i) o<m) (partial-decomposition-range f o o<m l i i≤o)
    partial-decomposition-skip-lemma f o o<m l zeroℕ i≤o = refl
    partial-decomposition-skip-lemma {m = m} f o@(sucℕ o') o<m l i@(sucℕ i') i≤o with partial-decomposition-skip-lemma f o o<m l i' (≤-trans n≤sn i≤o)
    ... | l'≡ =
        partial-decomposition f o o<m l                                                                             ≡⟨ l'≡ ⟩
        partial-decomposition f (o ∸ i') o∸i'<m l'                                                                  ≡⟨ irrelevant-cong (_< m) (λ q q<m → partial-decomposition f q q<m l') {o ∸ i'} {sucℕ (o ∸ i)} (+-∸-assoc 1 {o'} {i'} i'≤o') ⟩
        partial-decomposition f (sucℕ (o ∸ i)) s[o'∸i']<m l'                                                        ≡⟨⟩
        partial-decomposition f (o ∸ i) (≤-<-trans n≤sn s[o'∸i']<m) (pair-at f (sucℕ (o ∸ i)) s[o'∸i']<m l' ∷ l')   ∎
        where
            open ≡-Reasoning
            l' = partial-decomposition-range f o o<m l i' (≤-trans n≤sn i≤o)

            -- Eventually irrelevant proofs
            i'≤o' : i' ≤ o'
            i'≤o' = s≤s⁻¹ (≤-recompute i≤o)

            o∸i'<m : o ∸ i' < m
            o∸i'<m = ≤-<-trans (m∸n≤m o i') (≤-recompute o<m)

            s[o'∸i']<m : sucℕ (o' ∸ i') < m
            s[o'∸i']<m = ≤-<-trans (≤-reflexive (∸-suc o' i' i'≤o')) o∸i'<m

    -- skip to index i
    partial-decomposition-skip-to-lemma :
        (f : Fin m → A) → (o : ℕ) → .(o<m : o < m) → (l : SwapList m) →
        (i : ℕ) → .(i≤o : i ≤ o) →
        partial-decomposition f o o<m l ≡ partial-decomposition f i (≤-<-trans i≤o o<m) (partial-decomposition-range f o o<m l (o ∸ i) (m∸n≤m o i))
    partial-decomposition-skip-to-lemma {m = m} f o o<m l i i≤o with partial-decomposition-skip-lemma f o o<m l (o ∸ i) (m∸n≤m o i)
    ... | l'≡ =
        partial-decomposition f o o<m l                     ≡⟨ l'≡ ⟩
        partial-decomposition f (o ∸ (o ∸ i)) o∸[o∸i]<m l'  ≡⟨ irrelevant-cong {A = ℕ} (_< m) (λ q q<m → partial-decomposition f q q<m l') {o ∸ (o ∸ i)} {i} (m∸[m∸n]≡n {o} {i} (≤-recompute i≤o)) ⟩
        partial-decomposition f i (≤-<-trans i≤o o<m) l'    ∎
        where
            open ≡-Reasoning
            l' = partial-decomposition-range f o o<m l (o ∸ i) (m∸n≤m o i)

            -- Eventually irrelevant proofs
            o∸[o∸i]≡i = m∸[m∸n]≡n {o} {i} (≤-recompute i≤o)

            i<m : i < m
            i<m = ≤-<-trans (≤-recompute i≤o) (≤-recompute o<m)

            o∸[o∸i]<m = ≤-<-trans (≤-reflexive o∸[o∸i]≡i) i<m

    partial-decomposition-is-range :
        (f : Fin m → A) → (o : ℕ) → .(o<m : o < m) → (l : SwapList m) →
        partial-decomposition f o o<m l ≡ partial-decomposition-range f o o<m l o n≤n
    partial-decomposition-is-range f o o<m l = partial-decomposition-skip-to-lemma f o o<m l 0 z≤n

    -- At position i in l, the indices being swapped are i and something less than i
    partial-decomposition-index-lemma :
        (f : Fin m → A) → (o : ℕ) → .(o<m : o < m) → (l : SwapList m) →
        (i : ℕ) → .(i<o : i < o) →
        Σ ℕ λ j → Σ (Squash (j ≤ sucℕ i)) λ { (squash j≤si) →
        lookup (partial-decomposition f o o<m l) (fromℕ< {i} (<-≤-trans (<-≤-trans i<o (m≤n+m o (length l))) (≤-reflexive (sym (partial-decomposition-length-lemma f o o<m l)))))
        ≡ (fromℕ< {sucℕ i} (≤-<-trans i<o o<m) , fromℕ< {j} (≤-<-trans (≤-trans j≤si i<o) o<m)) }
    partial-decomposition-index-lemma {m = m} f o o<m l i i<o = j , squash j≤si , lookup-correct
        where
            i<decompose-l : i < length (partial-decomposition f o o<m l)
            i<decompose-l = begin
                sucℕ i                                      ≤⟨ ≤-recompute i<o ⟩
                o                                           ≤⟨ m≤n+m o (length l) ⟩
                length l + o                                ≤⟨ ≤-reflexive (sym (partial-decomposition-length-lemma f o o<m l)) ⟩
                length (partial-decomposition f o o<m l)    ∎
                where open ≤-Reasoning

            l' : SwapList m
            l' = partial-decomposition-range f o o<m l (o ∸ sucℕ i) (m∸n≤m o (sucℕ i))

            j-fin : Fin m
            j-fin = pair-at f (sucℕ i) (≤-<-trans i<o o<m) l' .proj₂

            j : ℕ
            j = toℕ j-fin

            -- These are a bunch of proofs that shouldn't ever actually be computed. They're used in several irrelevant contexts,
            -- but to have them exist separately out here, they need to be real, apparently
            j≤si : j ≤ sucℕ i
            j≤si = begin
                j                                                                           ≤⟨ ≤-refl ⟩
                toℕ (find-max-lower (f ∘ swap-with-list l') (sucℕ i) (≤-<-trans i<o o<m))   ≤⟨ find-max-lower-yields-low (f ∘ swap-with-list l') {sucℕ i} (≤-<-trans i<o o<m) ⟩
                sucℕ i                                                                      ∎
                where open ≤-Reasoning

            si<m : sucℕ i < m
            si<m = ≤-<-trans (≤-recompute i<o) (≤-recompute o<m)

            i<m : i < m
            i<m = ≤-<-trans n≤sn si<m

            j<m : j < m
            j<m = ≤-<-trans j≤si si<m

            weird-len≡o : length (partial-decomposition f i i<m (pair-at f (sucℕ i) si<m l' ∷ l')) ≡ length l + o
            weird-len≡o =
                length (partial-decomposition f i i<m (pair-at f (sucℕ i) si<m l' ∷ l')) ≡⟨ partial-decomposition-length-lemma f i i<m (pair-at f (sucℕ i) si<m l' ∷ l') ⟩
                length (pair-at f (sucℕ i) si<m l' ∷ l') + i    ≡⟨⟩
                sucℕ (length l') + i                            ≡⟨ cong (λ q → sucℕ q + i) (partial-decomposition-range-length f o o<m l (o ∸ sucℕ i) (m∸n≤m o (sucℕ i))) ⟩
                sucℕ (length l + (o ∸ sucℕ i)) + i              ≡⟨ cong (_+ i) (sym (+-suc (length l) (o ∸ sucℕ i))) ⟩
                (length l + sucℕ (o ∸ sucℕ i)) + i              ≡⟨ cong (λ q → (length l + q) + i) (∸-suc o (sucℕ i) i<o) ⟩
                (length l + (o ∸ i)) + i                        ≡⟨ +-assoc (length l) (o ∸ i) i ⟩
                length l + ((o ∸ i) + i)                        ≡⟨ cong (length l +_) (m∸n+n≡m {o} {i} (<⇒≤ (≤-recompute i<o))) ⟩
                length l + o ∎
                where open ≡-Reasoning

            i<base-len : i < length (partial-decomposition f o o<m l)
            i<base-len = begin
                sucℕ i                                      ≤⟨ ≤-recompute i<o ⟩
                o                                           ≤⟨ m≤n+m o (length l) ⟩
                length l + o                                ≡⟨ sym (partial-decomposition-length-lemma f o o<m l) ⟩
                length (partial-decomposition f o o<m l)    ∎
                where open ≤-Reasoning

            i<weird-len : i < length (partial-decomposition f i i<m (pair-at f (sucℕ i) si<m l' ∷ l'))
            i<weird-len = begin
                sucℕ i                                                                      ≤⟨ m≤n+m (sucℕ i) (length l') ⟩
                length l' + sucℕ i                                                          ≡⟨ +-suc (length l') i ⟩
                sucℕ (length l') + i                                                        ≡⟨⟩
                length (pair-at f (sucℕ i) si<m l' ∷ l') + i                                ≡⟨ sym (partial-decomposition-length-lemma f i i<m (pair-at f (sucℕ i) si<m l' ∷ l')) ⟩
                length (partial-decomposition f i i<m (pair-at f (sucℕ i) si<m l' ∷ l'))    ∎
                where open ≤-Reasoning

            i+0<weird-len : i + 0 < length (partial-decomposition f i i<m (pair-at f (sucℕ i) si<m l' ∷ l'))
            i+0<weird-len = ≤-<-trans (≤-reflexive (+-comm i 0)) i<weird-len

            0<sub-len : 0 < length (pair-at f (sucℕ i) si<m l' ∷ l')
            0<sub-len = s≤s z≤n

            0<drop-len : 0 < length (drop i (partial-decomposition f i i<m (pair-at f (sucℕ i) si<m l' ∷ l')))
            0<drop-len = begin
                1                                                                                   ≤⟨ 0<sub-len ⟩
                length (pair-at f (sucℕ i) si<m l' ∷ l')                                            ≡⟨ cong length (sym (partial-decomposition-drop-lemma f i i<m (pair-at f (sucℕ i) si<m l' ∷ l'))) ⟩
                length (drop i (partial-decomposition f i i<m (pair-at f (sucℕ i) si<m l' ∷ l')))   ∎
                where open ≤-Reasoning

            lookup-correct =
                lookup (partial-decomposition f o o<m l) (fromℕ< {i} i<base-len)                                            ≡⟨ irrelevant-cong (λ q → i < length q) (λ q i< → lookup q (fromℕ< {i} i<)) {w = partial-decomposition f o o<m l} {x = partial-decomposition f (sucℕ i) si<m l'} {y = i<base-len} {z = i<weird-len} (partial-decomposition-skip-to-lemma f o o<m l (sucℕ i) i<o) ⟩
                lookup (partial-decomposition f (sucℕ i) si<m l') (fromℕ< {i} i<weird-len)                                  ≡⟨ irrelevant-cong (_< length (partial-decomposition f (sucℕ i) si<m l')) (λ q q< → lookup (partial-decomposition f (sucℕ i) si<m l') (fromℕ< {q} q<)) {i} {i + 0} {i<weird-len} {i+0<weird-len} (+-comm 0 i) ⟩
                lookup (partial-decomposition f (sucℕ i) si<m l') (fromℕ< {i + 0} i+0<weird-len)                            ≡⟨ drop-lookup (partial-decomposition f (sucℕ i) si<m l') i 0 i+0<weird-len ⟩
                lookup (drop i (partial-decomposition f (sucℕ i) si<m l')) (fromℕ< {0} 0<drop-len)                          ≡⟨⟩
                lookup (drop i (partial-decomposition f i i<m (pair-at f (sucℕ i) si<m l' ∷ l'))) (fromℕ< {0} 0<drop-len)   ≡⟨ irrelevant-cong (λ q → 0 < length q) (λ q 0< → lookup q (fromℕ< {0} 0<)) {w = drop i (partial-decomposition f i i<m (pair-at f (sucℕ i) si<m l' ∷ l'))} {x = pair-at f (sucℕ i) si<m l' ∷ l'} {y = 0<drop-len} {z = 0<sub-len} (partial-decomposition-drop-lemma f i i<m (pair-at f (sucℕ i) si<m l' ∷ l')) ⟩
                lookup (pair-at f (sucℕ i) si<m l' ∷ l') (fromℕ< {0} 0<sub-len)                                             ≡⟨⟩
                pair-at f (sucℕ i) si<m l'                                                                                  ≡⟨⟩
                fromℕ< {sucℕ i} si<m , j-fin                                                                                ≡⟨ ×≡ refl (sym (fromℕ<-toℕ j-fin (toℕ<n j-fin))) ⟩
                fromℕ< {sucℕ i} si<m , fromℕ< {j} j<m                                                                       ∎
                where open ≡-Reasoning

    +-range-split :
        (f : Fin m → A) → (o : ℕ) → .(o<m : o < m) → (l : SwapList m) →
        (i j : ℕ) → .(i+j≤o : i + j ≤ o) →
        partial-decomposition-range f o o<m l (i + j) i+j≤o ≡
        partial-decomposition-range f (o ∸ j) (≤-<-trans (m∸n≤m o j) o<m) (partial-decomposition-range f o o<m l j (m+n≤o⇒n≤o i i+j≤o)) i (≤-trans (≤-reflexive (sym (m+n∸n≡m i j))) (∸-mono {i + j} {o} {j} {j} i+j≤o n≤n))
    +-range-split f o o<m l zeroℕ j i+j≤o = refl
    +-range-split {m = m} f o o<m l i@(sucℕ i') j i+j≤o =
        partial-decomposition-range f o o<m l (i + j) i+j≤o                                                         ≡⟨⟩
        partial-decomposition-range f o o<m l (sucℕ (i' + j)) i+j≤o                                                 ≡⟨⟩
        xy ∷ partial-decomposition-range f o o<m l (i' + j) i'+j≤o                                                  ≡⟨ cong (xy ∷_) l'=l'' ⟩
        xy ∷ partial-decomposition-range f (o ∸ j) o∸j<m (partial-decomposition-range f o o<m l j j≤o) i' i'≤o∸j    ≡⟨ cong (_∷ partial-decomposition-range f (o ∸ j) o∸j<m (partial-decomposition-range f o o<m l j j≤o) i' i'≤o∸j) (×≡ x=x' y=y') ⟩
        xy' ∷ partial-decomposition-range f (o ∸ j) o∸j<m (partial-decomposition-range f o o<m l j j≤o) i' i'≤o∸j   ≡⟨⟩
        partial-decomposition-range f (o ∸ j) o∸j<m (partial-decomposition-range f o o<m l j j≤o) i i≤o∸j           ∎
        where
            open ≡-Reasoning

            i≤o : i ≤ o
            i≤o = m+n≤o⇒m≤o i (≤-recompute i+j≤o)

            j≤o : j ≤ o
            j≤o = m+n≤o⇒n≤o i (≤-recompute i+j≤o)

            i'+j≤o : i' + j ≤ o
            i'+j≤o = ≤-trans n≤sn (≤-recompute i+j≤o)

            i'≤o : i' ≤ o
            i'≤o = m+n≤o⇒m≤o i' i'+j≤o

            o∸j<m : o ∸ j < m
            o∸j<m = ≤-<-trans (m∸n≤m o j) (≤-recompute o<m)

            i≤o∸j : i ≤ o ∸ j
            i≤o∸j = ≤-trans (≤-reflexive (sym (m+n∸n≡m i j))) (∸-mono {i + j} {o} {j} {j} (≤-recompute i+j≤o) n≤n)

            i'≤o∸j : i' ≤ o ∸ j
            i'≤o∸j = ≤-trans n≤sn i≤o∸j

            s[o∸[i+j]]=s[o∸j∸i] : sucℕ (o ∸ (i + j)) ≡ sucℕ (o ∸ j ∸ i)
            s[o∸[i+j]]=s[o∸j∸i] = cong sucℕ (trans (cong (o ∸_) (+-comm i j)) (sym (m∸n∸o≡m∸[n+o] o j i)))

            s[o∸[i+j]]<m : sucℕ (o ∸ (i + j)) < m
            s[o∸[i+j]]<m = ≤-<-trans (≤-trans (≤-reflexive (∸-suc o (i + j) i+j≤o)) (m∸n≤m o (i' + j))) (≤-recompute o<m)

            s[o∸j∸i]<m : sucℕ (o ∸ j ∸ i) < m
            s[o∸j∸i]<m = ≤-<-trans (≤-reflexive (sym s[o∸[i+j]]=s[o∸j∸i])) s[o∸[i+j]]<m

            l' = partial-decomposition-range f o o<m l (i' + j) i'+j≤o
            xy = pair-at f (sucℕ (o ∸ (i + j))) (≤-<-trans (≤-reflexive (∸-suc o (i + j) i+j≤o)) (≤-<-trans (m∸n≤m o (i' + j)) o<m)) l'
            x = fromℕ< {sucℕ (o ∸ (i + j))} s[o∸[i+j]]<m
            y = find-max-lower (f ∘ swap-with-list l') (sucℕ (o ∸ (i + j))) s[o∸[i+j]]<m

            l'' = partial-decomposition-range f (o ∸ j) o∸j<m (partial-decomposition-range f o o<m l j j≤o) i' i'≤o∸j
            xy' = pair-at f (sucℕ (o ∸ j ∸ i)) s[o∸j∸i]<m l''
            x' = fromℕ< {sucℕ (o ∸ j ∸ i)} s[o∸j∸i]<m
            y' = find-max-lower (f ∘ swap-with-list l'') (sucℕ (o ∸ j ∸ i)) s[o∸j∸i]<m

            l'=l'' : l' ≡ l''
            l'=l'' =
                partial-decomposition-range f o o<m l (i' + j) i'+j≤o                                               ≡⟨ +-range-split f o o<m l i' j i'+j≤o ⟩
                partial-decomposition-range f (o ∸ j) o∸j<m (partial-decomposition-range f o o<m l j j≤o) i' i'≤o∸j ∎

            x=x' : x ≡ x'
            x=x' =
                fromℕ< {sucℕ (o ∸ (i + j))} s[o∸[i+j]]<m    ≡⟨ irrelevant-cong (_< m) (λ q q<m → fromℕ< {q} q<m) {y = s[o∸[i+j]]<m} {z = s[o∸j∸i]<m} s[o∸[i+j]]=s[o∸j∸i] ⟩
                fromℕ< {sucℕ (o ∸ j ∸ i)} s[o∸j∸i]<m        ∎

            y=y' : y ≡ y'
            y=y' =
                find-max-lower (f ∘ swap-with-list l') (sucℕ (o ∸ (i + j))) s[o∸[i+j]]<m    ≡⟨ cong (λ q → find-max-lower (f ∘ swap-with-list q) (sucℕ (o ∸ (i + j))) s[o∸[i+j]]<m) l'=l'' ⟩
                find-max-lower (f ∘ swap-with-list l'') (sucℕ (o ∸ (i + j))) s[o∸[i+j]]<m   ≡⟨ irrelevant-cong (_< m) (find-max-lower (f ∘ swap-with-list l'')) {y = s[o∸[i+j]]<m} {z = s[o∸j∸i]<m} s[o∸[i+j]]=s[o∸j∸i] ⟩
                find-max-lower (f ∘ swap-with-list l'') (sucℕ (o ∸ j ∸ i)) s[o∸j∸i]<m       ∎

    partial-decomposition-range-split-lemma :
        (f : Fin m → A) → (o : ℕ) → .(o<m : o < m) → (l : SwapList m) →
        (i : ℕ) → .(i≤o : i ≤ o) →
        swap-with-list (partial-decomposition-range f o o<m l i i≤o) ≡
        (swap-with-list l ∘ swap-with-list (partial-decomposition-range (f ∘ swap-with-list l) o o<m [] i i≤o))
    partial-decomposition-range-split-lemma f o o<m l zeroℕ i≤o = refl
    partial-decomposition-range-split-lemma {m = m} f o o<m l i@(sucℕ i') i≤o =
        swap-with-list (partial-decomposition-range f o o<m l i i≤o)                                            ≡⟨⟩
        swap-with-list (wz ∷ l')                                                                                ≡⟨ swap-pop-initial id l' w z  ⟩
        swap-with-list l' ∘ swp w z                                                                             ≡⟨ cong (_∘ swp w z) (partial-decomposition-range-split-lemma f o o<m l i' i'≤o) ⟩
        swap-with-list l ∘ swap-with-list l'' ∘ swp w z                                                         ≡⟨ cong (swap-with-list l ∘_) (sym (swap-pop-initial id (partial-decomposition-range (f ∘ swap-with-list l) o o<m [] i' i'≤o) w z)) ⟩
        swap-with-list l ∘ swap-with-list (wz ∷ l'')                                                            ≡⟨ cong (λ q → swap-with-list l ∘ swap-with-list ((w , q) ∷ l'')) z=z' ⟩
        swap-with-list l ∘ swap-with-list (wz' ∷ l'')                                                           ≡⟨⟩
        swap-with-list l ∘ swap-with-list (partial-decomposition-range (f ∘ swap-with-list l) o o<m [] i i≤o)   ∎
        where
            open ≡-Reasoning

            i'≤o : i' ≤ o
            i'≤o = ≤-trans n≤sn (≤-recompute i≤o)

            s[o∸i]<m : sucℕ (o ∸ i) < m
            s[o∸i]<m = ≤-<-trans (≤-trans (≤-reflexive (∸-suc o i i≤o))(m∸n≤m o i')) (≤-recompute o<m)

            l' = partial-decomposition-range f o o<m l i' i'≤o
            wz = pair-at f (sucℕ (o ∸ i)) s[o∸i]<m l'
            w = fromℕ< {sucℕ (o ∸ i)} s[o∸i]<m
            z = find-max-lower (f ∘ swap-with-list l') (sucℕ (o ∸ i)) s[o∸i]<m

            l'' = partial-decomposition-range (f ∘ swap-with-list l) o o<m [] i' i'≤o
            wz' = pair-at (f ∘ swap-with-list l) (sucℕ (o ∸ i)) s[o∸i]<m l''
            w' = fromℕ< {sucℕ (o ∸ i)} s[o∸i]<m
            z' = find-max-lower (f ∘ swap-with-list l ∘ swap-with-list l'') (sucℕ (o ∸ i)) s[o∸i]<m

            z=z' : z ≡ z'
            z=z' = cong (λ q → find-max-lower (f ∘ q) (sucℕ (o ∸ i)) s[o∸i]<m) {swap-with-list l'} {swap-with-list l ∘ swap-with-list l''} (partial-decomposition-range-split-lemma f o o<m l i' i'≤o)

    -- In the final sort, the any item above index i is completely determined by
    -- everything after the first i swaps in the list.
    -- This includes if j is outside of the sort entirely.
    partial-decomposition-swap-drop-lemma :
        (f : Fin m → A) → (o : ℕ) → .(o<m : o < m) → (l : SwapList m) →
        (i j : ℕ) → .(i<j : i < j) → .(i≤o : i ≤ o) .(j<m : j < m) →
        swap-with-list (partial-decomposition f o o<m l) (fromℕ< {j} j<m) ≡
        swap-with-list (partial-decomposition-range f o o<m l (o ∸ i) (m∸n≤m o i)) (fromℕ< {j} j<m)
    partial-decomposition-swap-drop-lemma f o o<m l zeroℕ j i<j i≤o j<m =
        swap-with-list (partial-decomposition f o o<m l) (fromℕ< {j} j<m)                 ≡⟨ cong (λ q → swap-with-list q (fromℕ< {j} j<m)) (partial-decomposition-is-range f o o<m l) ⟩
        swap-with-list (partial-decomposition-range f o o<m l o ≤-refl) (fromℕ< {j} j<m)  ∎
        where open ≡-Reasoning
    partial-decomposition-swap-drop-lemma {m = m} f o o<m l i@(sucℕ i') j i<j i≤o j<m =
        swap-with-list (partial-decomposition f o o<m l) (fromℕ< {j} j<m)                               ≡⟨ partial-decomposition-swap-drop-lemma f o o<m l i' j (≤-trans n≤sn i<j) (≤-trans n≤sn i≤o) j<m ⟩
        swap-with-list (partial-decomposition-range f o o<m l (o ∸ i') (m∸n≤m o i')) (fromℕ< {j} j<m)   ≡⟨ irrelevant-cong (_≤ o) (λ q q<m → swap-with-list (partial-decomposition-range f o o<m l q q<m) (fromℕ< {j} j<m)) {o ∸ i'} {sucℕ (o ∸ i)} {m∸n≤m o i'} {s[o∸i]≤o} (sym (∸-suc o i i≤o)) ⟩
        swap-with-list (partial-decomposition-range f o o<m l (sucℕ (o ∸ i)) s[o∸i]≤o) (fromℕ< {j} j<m) ≡⟨⟩
        swap-with-list (pair-at f (sucℕ (o ∸ sucℕ (o ∸ i))) thing<m l' ∷ l') (fromℕ< {j} j<m)           ≡⟨ irrelevant-cong (_< m) (λ q q<m → swap-with-list (pair-at f q q<m l' ∷ l') (fromℕ< {j} j<m)) {sucℕ (o ∸ sucℕ (o ∸ i))} {i} {thing<m} {i<m} thing≡i ⟩
        swap-with-list (pair-at f i i<m l' ∷ l') (fromℕ< {j} j<m)                                       ≡⟨ cong-app (uncurry (swap-pop-initial {m} id l') (pair-at f i i<m l')) (fromℕ< {j} j<m) ⟩
        (swap-with-list l' ∘ uncurry swp (pair-at f i i<m l')) (fromℕ< {j} j<m)                         ≡⟨ cong (swap-with-list l') swap-at-i-leaves-j ⟩
        swap-with-list l' (fromℕ< {j} j<m)                                                              ∎
        where
            open ≡-Reasoning
            l' = partial-decomposition-range f o o<m l (o ∸ i) (m∸n≤m o i)

            -- Eventually irrelevant proofs
            i<m : i < m
            i<m = <-trans (≤-recompute i<j) (≤-recompute j<m)

            s[o∸i]≤o : sucℕ (o ∸ sucℕ i') ≤ o
            s[o∸i]≤o = ≤-trans (≤-reflexive (∸-suc o i i≤o)) (m∸n≤m o i')

            thing≡i : sucℕ (o ∸ sucℕ (o ∸ i)) ≡ i
            thing≡i =
                sucℕ (o ∸ sucℕ (o ∸ i))     ≡⟨ ∸-suc o (sucℕ (o ∸ i)) s[o∸i]≤o ⟩
                o ∸ (o ∸ i)                 ≡⟨ m∸[m∸n]≡n {o} {i} (≤-recompute i≤o) ⟩
                i                           ∎

            thing<m : sucℕ (o ∸ sucℕ (o ∸ i)) < m
            thing<m = ≤-<-trans (≤-reflexive thing≡i) i<m

            -- and the core of the proof:
            swap-at-i-leaves-j : uncurry swp (pair-at f i i<m l') (fromℕ< {j} j<m) ≡ fromℕ< {j} j<m
            swap-at-i-leaves-j = no-then-id x y (fromℕ< {j} j<m) x≠j y≠j
                where
                    x = fromℕ< {i} i<m
                    y = find-max-lower (f ∘ swap-with-list l') i i<m

                    x≠j : x ≢ fromℕ< {j} j<m
                    x≠j i=j = <-irrefl {i} {j} (
                        i                       ≡⟨ sym (toℕ-fromℕ< {i} {m} i<m) ⟩
                        toℕ (fromℕ< {i} i<m)    ≡⟨ cong toℕ i=j ⟩
                        toℕ (fromℕ< {j} j<m)    ≡⟨ toℕ-fromℕ< {j} {m} j<m ⟩
                        j                       ∎
                        ) (≤-recompute i<j)

                    y≠j : y ≢ fromℕ< {j} j<m
                    y≠j y=j = <-irrefl {toℕ y} {j} (trans (cong toℕ y=j) (toℕ-fromℕ< j<m)) (≤-<-trans (find-max-lower-yields-low (f ∘ swap-with-list l') {i} i<m) (≤-recompute i<j))

    -- partial-decomposition has two core properties:
    -- anything below o stays below o
    -- anything above o is acted upon by identity
    -- this one does recomputation. Use as proof tool only!
    partial-decomposition-range-low-stays-low :
        (f : Fin m → A) → (o : ℕ) → .(o<m : o < m) →
        ∀ (i j : ℕ) → .(i≤o : i ≤ o) → .(j≤o : j ≤ o) →
        toℕ (swap-with-list (partial-decomposition-range f o o<m [] j j≤o) (fromℕ< {i} (≤-<-trans i≤o o<m))) ≤ o
    partial-decomposition-range-low-stays-low {m = m} f o o<m i zeroℕ i≤o j≤o = ≤-trans (≤-reflexive (toℕ-fromℕ< {i} {m} (≤-<-trans i≤o o<m))) (≤-recompute i≤o)
    partial-decomposition-range-low-stays-low {m = m} f o@(sucℕ o') o<m i j@(sucℕ j') i≤o j≤o = begin
        toℕ (swap-with-list (partial-decomposition-range f o o<m [] j j≤o) (fromℕ< {i} i<m))                                                                    ≡⟨⟩
        toℕ (swap-with-list (pair-at f (sucℕ (o ∸ j)) s[o'∸i']<m l' ∷ l') (fromℕ< {i} i<m))                                                                     ≡⟨ cong (λ q → toℕ (q (fromℕ< {i} i<m))) (swap-pop-initial id l' (fromℕ< {sucℕ (o ∸ j)} s[o'∸i']<m) (find-max-lower (f ∘ swap-with-list l') (sucℕ (o ∸ j)) s[o'∸i']<m)) ⟩
        toℕ ((swap-with-list l' ∘ swp (fromℕ< {sucℕ (o ∸ j)} s[o'∸i']<m) (find-max-lower (f ∘ swap-with-list l') (sucℕ (o ∸ j)) s[o'∸i']<m)) (fromℕ< {i} i<m))  ≡⟨⟩
        toℕ (swap-with-list l' new-i)                                                                                                                           ≡⟨ cong (λ q → toℕ (swap-with-list l' q)) (sym (fromℕ<-toℕ new-i (toℕ<n new-i))) ⟩
        toℕ (swap-with-list l' (fromℕ< {toℕ new-i} (toℕ<n new-i)))                                                                                              ≤⟨ partial-decomposition-range-low-stays-low f o o<m (toℕ new-i) j' new-i-low (≤-trans n≤sn j≤o) ⟩
        o                                                                                                                                                       ∎
        where
            open ≤-Reasoning
            l' = partial-decomposition-range f o o<m [] j' (≤-trans n≤sn j≤o)

            -- Hopefully irrelevant proofs
            i<m : i < m
            i<m = ≤-<-trans (≤-recompute i≤o) (≤-recompute o<m)

            j<m : j < m
            j<m = ≤-<-trans (≤-recompute j≤o) (≤-recompute o<m)

            s[o'∸i']<m : sucℕ (o' ∸ j') < m
            s[o'∸i']<m = ≤-<-trans (≤-trans (≤-reflexive (∸-suc o j j≤o)) (m∸n≤m o j')) (≤-recompute o<m)

            new-i = swp (fromℕ< {sucℕ (o ∸ j)} s[o'∸i']<m) (find-max-lower (f ∘ swap-with-list l') (sucℕ (o ∸ j)) s[o'∸i']<m) (fromℕ< {i} i<m)

            new-i-low : toℕ new-i ≤ o
            new-i-low = begin
                toℕ new-i               ≤⟨ low-swp-is-low (fromℕ< {sucℕ (o ∸ j)} s[o'∸i']<m) (find-max-lower (f ∘ swap-with-list l') (sucℕ (o ∸ j)) s[o'∸i']<m) (fromℕ< {i} i<m) (fromℕ< {o} o<m)
                    (begin
                        toℕ (fromℕ< {sucℕ (o ∸ j)} s[o'∸i']<m)  ≡⟨ toℕ-fromℕ< s[o'∸i']<m ⟩
                        sucℕ (o ∸ j)                            ≡⟨ ∸-suc o j j≤o ⟩
                        o ∸ j'                                  ≤⟨ m∸n≤m o j' ⟩
                        o                                       ≡⟨ sym (toℕ-fromℕ< o<m) ⟩
                        toℕ (fromℕ< {o} o<m)                    ∎)
                    (begin
                        toℕ (find-max-lower (f ∘ swap-with-list l') (sucℕ (o ∸ j)) s[o'∸i']<m)  ≤⟨ find-max-lower-yields-low (f ∘ swap-with-list l') s[o'∸i']<m ⟩
                        sucℕ (o ∸ j)                                                            ≡⟨ ∸-suc o j j≤o ⟩
                        o ∸ j'                                                                  ≤⟨ m∸n≤m o j' ⟩
                        o                                                                       ≡⟨ sym (toℕ-fromℕ< o<m) ⟩
                        toℕ (fromℕ< {o} o<m)                                                    ∎)
                    (begin
                        toℕ (fromℕ< {i} i<m)    ≡⟨ toℕ-fromℕ< i<m ⟩
                        i                       ≤⟨ ≤-recompute i≤o ⟩
                        o                       ≡⟨ sym (toℕ-fromℕ< o<m) ⟩
                        toℕ (fromℕ< {o} o<m)    ∎) ⟩
                toℕ (fromℕ< {o} o<m)    ≡⟨ toℕ-fromℕ< {o} o<m ⟩
                o                       ∎

    partial-decomposition-low-stays-low :
        (f : Fin m → A) → (o : ℕ) → .(o<m : o < m) →
        ∀ (i : ℕ) → .(i≤o : i ≤ o) →
        toℕ (swap-with-list (partial-decomposition f o o<m []) (fromℕ< {i} (≤-<-trans i≤o o<m))) ≤ o
    partial-decomposition-low-stays-low {m = m} f o o<m i i≤o = begin
        toℕ (swap-with-list (partial-decomposition f o o<m []) (fromℕ< {i} i<m))                ≡⟨ cong (λ q → toℕ (swap-with-list q (fromℕ< {i} i<m))) (partial-decomposition-is-range f o o<m []) ⟩
        toℕ (swap-with-list (partial-decomposition-range f o o<m [] o n≤n) (fromℕ< {i} i<m))    ≤⟨ partial-decomposition-range-low-stays-low f o o<m i o i≤o n≤n ⟩
        o                                                                                       ∎
        where
            open ≤-Reasoning
            i<m : i < m
            i<m = ≤-<-trans (≤-recompute i≤o) (≤-recompute o<m)

    partial-decomposition-monotonic-lemma :
        (f : Fin m → A) → (o : ℕ) → .(o<m : o < m) → (l : SwapList m) →
        ∀ (i j : ℕ) → .(i≤j : i ≤ j) → .(j≤o : j ≤ o) →
        ((f ∘ (swap-with-list (partial-decomposition f o o<m l))) (fromℕ< {i} (≤-<-trans (≤-trans i≤j j≤o) o<m))) ≤A
        ((f ∘ (swap-with-list (partial-decomposition f o o<m l))) (fromℕ< {j} (≤-<-trans j≤o o<m)))
    partial-decomposition-monotonic-lemma f o o<m l zeroℕ zeroℕ i≤j j≤o = ≤A-refl
    partial-decomposition-monotonic-lemma {m = m} f o@(sucℕ o') o<m l i j@(sucℕ j') i≤j j≤o = begin
        f (swap-with-list (partial-decomposition f o o<m l) (fromℕ< {i} i<m))                                                                                                                                                               ≡⟨ cong (λ q → f (swap-with-list q (fromℕ< {i} i<m))) (partial-decomposition-is-range f o o<m l) ⟩
        f (swap-with-list (partial-decomposition-range f o o<m l o n≤n) (fromℕ< {i} i<m))                                                                                                                                                   ≡⟨ irrelevant-cong (_≤ o) (λ q q≤o → f (swap-with-list (partial-decomposition-range f o o<m l q q≤o) (fromℕ< {i} i<m))) {o} {j + (o ∸ j)} {n≤n} {≤-reflexive (m+[n∸m]≡n j≤o)} (sym (m+[n∸m]≡n (≤-recompute j≤o))) ⟩
        f (swap-with-list (partial-decomposition-range f o o<m l (j + (o ∸ j)) (≤-reflexive (m+[n∸m]≡n j≤o))) (fromℕ< {i} i<m))                                                                                                             ≡⟨ cong (λ q → f (swap-with-list q (fromℕ< {i} i<m))) (+-range-split f o o<m l j (o ∸ j) (≤-reflexive (m+[n∸m]≡n j≤o))) ⟩
        f (swap-with-list (partial-decomposition-range f (o ∸ (o ∸ j)) (≤-<-trans (≤-reflexive (m∸[m∸n]≡n j≤o)) j<m) (partial-decomposition-range f o o<m l (o ∸ j) (m∸n≤m o j)) j (≤-reflexive (sym (m∸[m∸n]≡n j≤o)))) (fromℕ< {i} i<m))   ≡⟨ irrelevant-cong₂ (_< m) (j ≤_) (λ q q<m j≤q → f (swap-with-list (partial-decomposition-range f q q<m (partial-decomposition-range f o o<m l (o ∸ j) (m∸n≤m o j)) j j≤q) (fromℕ< {i} i<m))) {o ∸ (o ∸ j)} {j} {≤-<-trans (≤-reflexive (m∸[m∸n]≡n (≤-recompute j≤o))) j<m} {j<m} {≤-reflexive (sym (m∸[m∸n]≡n (≤-recompute j≤o)))} {n≤n} (m∸[m∸n]≡n (≤-recompute j≤o)) ⟩
        f (swap-with-list (partial-decomposition-range f j j<m (partial-decomposition-range f o o<m l (o ∸ j) (m∸n≤m o j)) j n≤n) (fromℕ< {i} i<m))                                                                                         ≡⟨ cong (λ q → f (q (fromℕ< {i} i<m))) (partial-decomposition-range-split-lemma f j j<m (partial-decomposition-range f o o<m l (o ∸ j) (m∸n≤m o j)) j n≤n) ⟩
        f ((swap-with-list l' ∘ swap-with-list (partial-decomposition-range (f ∘ swap-with-list (partial-decomposition-range f o o<m l (o ∸ j) (m∸n≤m o j))) j j<m [] j n≤n)) (fromℕ< {i} i<m))                                             ≤⟨ find-max-lower-is-max (f ∘ swap-with-list l') {swap-with-list (partial-decomposition-range (f ∘ swap-with-list (partial-decomposition-range f o o<m l (o ∸ j) (m∸n≤m o j))) j j<m [] j n≤n) (fromℕ< {i} i<m)} {j} (partial-decomposition-range-low-stays-low (f ∘ swap-with-list (partial-decomposition-range f o o<m l (o ∸ j) (m∸n≤m o j))) j j<m i j i≤j n≤n) j<m ⟩
        f (swap-with-list l' y)                                                                                             ≡⟨ cong (f ∘ swap-with-list l') (sym (matchₒ-lemma (fromℕ< {j} j<m) y)) ⟩
        f (swap-with-list l' (swp (fromℕ< {j} j<m) y (fromℕ< {j} j<m)))                                                     ≡⟨ cong (λ q → f (q (fromℕ< {j} j<m))) (sym (swap-pop-initial id l' (fromℕ< {j} j<m) y)) ⟩
        f (swap-with-list (pair-at f j j<m l' ∷ l') (fromℕ< {j} j<m))                                                       ≡⟨ irrelevant-cong (_< m) (λ q q<m → f (swap-with-list (pair-at f q q<m l' ∷ l') (fromℕ< {j} j<m))) {j} {sucℕ (o ∸ sucℕ (o ∸ j))} {j<m} {thing<m} (sym thing≡j) ⟩
        f (swap-with-list (pair-at f (sucℕ (o ∸ sucℕ (o ∸ j))) thing<m l' ∷ l') (fromℕ< {j} j<m))                           ≡⟨⟩
        f (swap-with-list (partial-decomposition-range f o o<m l (sucℕ (o' ∸ j')) (s≤s (m∸n≤m o' j'))) (fromℕ< {j} j<m))    ≡⟨ irrelevant-cong (_≤ o) (λ q q≤o → f (swap-with-list (partial-decomposition-range f o o<m l q q≤o) (fromℕ< {j} j<m))) {sucℕ (o' ∸ j')} {o ∸ j'} {s≤s (m∸n≤m o' j')} {m∸n≤m o j'} (∸-suc o' j' (s≤s⁻¹ j≤o)) ⟩
        f (swap-with-list (partial-decomposition-range f o o<m l (o ∸ j') (m∸n≤m o j')) (fromℕ< {j} j<m))                   ≡⟨ sym (cong f (partial-decomposition-swap-drop-lemma f o o<m l j' j n≤n (≤-trans n≤sn j≤o) j<m)) ⟩
        f (swap-with-list (partial-decomposition f o o<m l) (fromℕ< {j} j<m))                                               ∎
        where
            l' = partial-decomposition-range f o o<m l (o ∸ j) (≤-trans (m∸n≤m o' j') n≤sn)

            -- Eventually irrelevant proofs
            j<m : j < m
            j<m = ≤-<-trans (≤-recompute j≤o) (≤-recompute o<m)

            i<m : i < m
            i<m = ≤-<-trans (≤-recompute i≤j) j<m

            thing≡j : sucℕ (o ∸ sucℕ (o ∸ j)) ≡ j
            thing≡j =
                sucℕ (o ∸ sucℕ (o ∸ j))     ≡⟨ ∸-suc o (sucℕ (o ∸ j)) (s≤s (m∸n≤m o' j')) ⟩
                o ∸ (o ∸ j)                 ≡⟨ m∸[m∸n]≡n {o} {j} (≤-recompute j≤o) ⟩
                j                           ∎
                where open ≡-Reasoning

            thing<m : sucℕ (o ∸ sucℕ (o ∸ j)) < m
            thing<m = ≤-<-trans (≤-reflexive thing≡j) j<m

            -- the core swap's other position
            y = find-max-lower (f ∘ swap-with-list l') j j<m

            open ≤A-Reasoning


module _ {o' : ℕ} where
    o = sucℕ o'
    open Sorting (≤-fin-isDecTotalOrder {o})
    open SwapList
    open Monotonicity

    decompose-inverse : (p : Permutation o) → SwapList o
    decompose-inverse p = partial-decomposition (p .Bijection.to) o' n<sn []

    decompose-permutation : (p : Permutation o) → SwapList o
    decompose-permutation p = reverse (decompose-inverse p)

    -- This statement is stronger than the lemma in Sorting,
    -- since we're working with a surjective function,
    -- rather than an arbitrary one.
    partial-decomposition-strictly-monotonic-lemma :
        (p : Permutation o) →
        ∀ (i j : ℕ) → .(i<j : i < j) → .(j<o : j < o) →
        ((p .Bijection.to ∘ (swap-with-list (decompose-inverse p))) (fromℕ< {i} (<-trans i<j j<o))) <-fin
        ((p .Bijection.to ∘ (swap-with-list (decompose-inverse p))) (fromℕ< {j} j<o))
    partial-decomposition-strictly-monotonic-lemma p i j i<j j<o =
        case
            ≤→<≡ (partial-decomposition-monotonic-lemma (p .Bijection.to) o' n<sn [] i j (<⇒≤ i<j) (s≤s⁻¹ j<o))
        of λ {
            (inj₁ case<) → case<;
            (inj₂ case=) → ⊥-elim (<-irrefl (fromℕ<-injective i j (<-trans i<j j<o) j<o (swap-with-list-bijective (decompose-inverse p) .proj₁ (p .Bijection.bijective .proj₁ (toℕ-injective case=)))) (≤-recompute i<j))
        }

    decompose-inverse-is-right-inverse : (p : Permutation o) → ∀ k → (p .Bijection.to ∘ swap-with-list (decompose-inverse p)) k ≡ k
    decompose-inverse-is-right-inverse p k =
        thing                               ≡⟨ sym (fromℕ<-toℕ thing (toℕ<n thing)) ⟩
        fromℕ< {toℕ thing} (toℕ<n thing)    ≡⟨ irrelevant-cong (_< o) (λ q q<o → fromℕ< {q} q<o) {y = toℕ<n thing} {z = toℕ<n (thing')} (cong (λ q → toℕ (p .Bijection.to (swap-with-list (decompose-inverse p) q))) (sym (fromℕ<-toℕ  k (toℕ<n k)))) ⟩
        fromℕ< {toℕ thing'} (toℕ<n thing')  ≡⟨ irrelevant-cong (_< o) (λ q q<o → fromℕ< {q} q<o) {y = toℕ<n (thing')} {z = toℕ<n k} (strictly-monotonic⇒is-id (p .Bijection.to ∘ swap-with-list (decompose-inverse p)) (partial-decomposition-strictly-monotonic-lemma p) (toℕ k) (toℕ<n k)) ⟩
        fromℕ< {toℕ k} (toℕ<n k)            ≡⟨ fromℕ<-toℕ k (toℕ<n k) ⟩
        k                                   ∎
        where
            open ≡-Reasoning

            thing = p .Bijection.to (swap-with-list (decompose-inverse p) k)
            thing' = p .Bijection.to (swap-with-list (decompose-inverse p) (fromℕ< {toℕ k} (toℕ<n k)))

    is-permutation-decomposition : (p : Permutation o) → IsSwapDecomposition (p .Bijection.to) (decompose-permutation p)
    is-permutation-decomposition p k =
        swap-with-list (reverse l) k                                            ≡⟨ sym (decompose-inverse-is-right-inverse p (swap-with-list (reverse l) k)) ⟩
        (p .Bijection.to ∘ swap-with-list l ∘ swap-with-list (reverse l)) k     ≡⟨ cong (p .Bijection.to) (swap-with-list-reverse-is-right-inverse l k) ⟩
        p .Bijection.to k                                                       ∎
        where
            open ≡-Reasoning
            l = partial-decomposition (p .Bijection.to) o' n<sn []


-- -- Goal: show that every permutation can be decomposed into a sequence of swaps
-- module Decomposition where

--     StrictlyMonotonicUpperDomain : (Fin m → Fin n) → ℕ → Set
--     StrictlyMonotonicUpperDomain f i = ∀ j k → i ≤ toℕ j → j <-fin k → f j <-fin f k

--     WeaklyMonotonicUpperDomain : (Fin m → Fin n) → ℕ → Set
--     WeaklyMonotonicUpperDomain f i = ∀ j k → i ≤ toℕ j → j <-fin k → f j ≤-fin f k
