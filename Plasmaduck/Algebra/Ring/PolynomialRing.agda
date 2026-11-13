open import Level using (Level; _⊔_)
open import Relation.Binary.PropositionalEquality using (subst; _≡_; _≗_; module ≡-Reasoning) renaming (cong to ≡-cong; cong₂ to ≡-cong₂; refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Relation.Binary using (tri<; tri≈; tri>; Setoid; Rel; Decidable; IsEquivalence; Reflexive; Symmetric; Transitive; Trans; Irreflexive; Asymmetric; Antisymmetric)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Function using (_∘_; Congruent; Bijective)
open import Data.Empty using (⊥; ⊥-elim; ⊥-elim-irr)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Bool.Properties using (T?)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (ℕ; _>_; _<_; _≤_; _≥_; _≤?_; _<?_; _≤ᵇ_; _<ᵇ_; _≡ᵇ_; z≤n; s≤s; s≤s⁻¹) renaming (zero to zeroℕ; suc to sucℕ; pred to predℕ; _+_ to _+ℕ_; _∸_ to _∸ℕ_; _*_ to _*ℕ_; _/_ to _/ℕ_; _%_ to _%ℕ_; _^_ to _^ℕ_; _⊓_ to _⊓ℕ_; _⊔_ to _⊔ℕ_)
open import Data.Nat.Properties using (≤-refl; ≤-reflexive; ≤-trans; ≤-antisym; m≤n⇒m≤n+o; m≤o∸n⇒m+n≤o; <⇒≤; ≤⇒≤ᵇ; ≤ᵇ⇒≤; ≡⇒≡ᵇ; +-suc; ∸-mono; ∸-+-assoc; +-∸-assoc; m+n∸m≡n; m+n∸n≡m; n∸n≡0; m∸n≤m; ≰⇒>; ∸-monoˡ-≤; m≤m⊔n; m≤n⊔m; <-irrefl; <-cmp; +-mono-≤; *-mono-≤; n<1⇒n≡0; module ≤-Reasoning) renaming (+-comm to +ℕ-comm)
open import Data.Nat.DivMod using (%-congˡ; m%n<n; m<n*o⇒m/o<n; m≡m%n+[m/n]*n; [m+kn]%n≡m%n; m<n⇒m%n≡m; m<n⇒m/n≡0)
open import Relation.Binary.Reasoning.Syntax using (module ≤-syntax; module end-syntax)

open import Plasmaduck.SetoidExperiment.SetoidMachinery using (SetoidFunction₂; SetoidFunction; _which-is-cong_; discrete-setoid; from-discrete-cong)
open import Plasmaduck.Function.Properties using (Congruent₂; Associative; Commutative; LeftIdentity; RightIdentity; Identity; _DistributesOverˡ_; _DistributesOverʳ_; _DistributesOver_)
open import Plasmaduck.Function.InjectionSurjection using (both-inv→bijective)
open import Plasmaduck.Relation.Defs using (CongruentRel; CongruentProperty)
open import Plasmaduck.Relation.OrderHelpers using (WeakTri; cmp₁; cmp₂; cmp₃)
open import Plasmaduck.Data.Empty using (⊥-recompute)
open import Plasmaduck.Data.Squash using (Squash; squash; squash-≡)
open import Plasmaduck.Data.Bool using (if-force-true; if-force-false)
open import Plasmaduck.Data.Nat using (≤-recompute; ≥-⊔-semilattice; ≤-cmp; <-≤-trans; ≤-<-trans; n≤sn; n≤spn; ≤-+-split; <-+-split; <-+-split₃; [m+kn]/n≡k+m/n; m∸n+n≡m; m∸n≤o⇒m≤o+n; ∸-suc; m∸[m∸n]≡n; [n∸m]∸[o∸m]=n∸o; m+[n∸m]≡n; m<n⇒n∸m-nonZero; m∸n+n≡m⊔n; ⊔≥₁; ≤⇒<≡)
open import Plasmaduck.Data.FakeFin using (FakeFin)
open import Plasmaduck.Fold.Nat.Merge using (merge; merge-pop-first; merge-carrying-lemma; merge-merge; module MergeSubstitute; module MergeOnSetoid; module Reindex)
open import Plasmaduck.Fold.Nat.InfiniteReindexing using (_≺_; all-index-vectors; InfiniteVector; IsNonZero; HasOneTail; LesserInfiniteVector; LesserInfiniteVectorSetoid; module FiniteVectorBijections; module Cube)
open import Plasmaduck.Counting.Permutation.Defs using (swp)
open import Plasmaduck.Algebra.Ring.Defs using (Ring; RawRing; IsRing; IsCommutativeRing; CommutativeRing; opposite-ring)
open import Plasmaduck.Algebra.Group.Defs using (Group)
open import Plasmaduck.Util.Case using (case_of_)

open import Plasmaduck.Algebra.Ring.FormalPolynomialRing using (module RawFormalPolynomial; module FormalPolynomial; module CommutativeFormalPolynomial)



module Plasmaduck.Algebra.Ring.PolynomialRing where

variable
    c ℓ : Level

module Polynomial (ring : Ring c ℓ) where
    open Ring ring using (IsZero; NonZero; NonZero-cong; Carrier; S) renaming (
        zero to zeroR; one to oneR; _≈_ to _≈R_; _+_ to _+R_; -_ to -R_; _*_ to _*R_;
        +-op to +R-op;
        +-cong to +R-cong;
        +-assoc to +R-assoc;
        +-comm to +R-comm;
        +-identity to +R-identity;
        neg-cong to negR-cong;
        *-cong to *R-cong;
        *-assoc to *R-assoc;
        zero-is-*-strong-absorber to zeroR-is-*R-strong-absorber;
        zero-is-*-left-absorber to zeroR-is-*R-left-absorber;
        zero-is-*-right-absorber to zeroR-is-*R-right-absorber;
        one-is-*-left-id to oneR-is-*R-left-id;
        one-is-*-right-id to oneR-is-*R-right-id;
        zero-is-+-left-id to zeroR-is-+R-left-id;
        zero-is-+-right-id to zeroR-is-+R-right-id;
        neg-zero-is-zero to negR-zeroR-is-zeroR;
        *-+-distributive to *R-+R-distributive
        )
    open IsEquivalence (S .Setoid.isEquivalence)
    open RawFormalPolynomial (ring .Ring.rawRing) using (FormalPolynomial; FormalPolynomialSetoid) renaming (_≈_ to _≈'_; _+_ to _+'_; -_ to -'_; _∸_ to _∸'_; _*_ to _*'_; _*-alt_ to _*'-alt_; _*x^_ to _*x^'_; zero to zero'; one to one'; +-cong to +'-cong; ∸-cong to ∸'-cong; negate-cong to negate'-cong; *-cong to *'-cong; constant-polynomial to constant-polynomial')
    open FormalPolynomial ring using () renaming (
        *-flip to *'-flip;
        *-identity to *-identity';
        *-assoc to *-assoc';
        *-distrib-+ to *-distrib-+'
        )
    open MergeSubstitute S using (merge-local-substitute-generate; merge-substitute-generate; merge-substitute; merge-substitute-start; merge-substitute-op)
    open MergeOnSetoid S using (merge-pop-last; merge-distribute-theorem; merge-zipper-lemma)

    {-
        This one is clunkier to use conceptually,
        but is capable of expressing that
        a zero polynomial has lower degree
        than a constant polynomial.
    -}
    HasDegree< : FormalPolynomial → ℕ → Set ℓ
    HasDegree< p n = ∀ {m} → .(n ≤ m) → IsZero (p m)

    HasDegree≤ : FormalPolynomial → ℕ → Set ℓ
    HasDegree≤ p n = HasDegree< p (sucℕ n)

    -- not tight
    HasDegree<⇒HasDegree≤ : ∀ p m → HasDegree< p m → HasDegree≤ p (predℕ m)
    HasDegree<⇒HasDegree≤ p m p[≥m]=0 {i} i>pm = p[≥m]=0 {i} (≤-trans (n≤spn m) i>pm)

    HasDegree : FormalPolynomial → ℕ → Set ℓ
    HasDegree p n = NonZero (p n) × HasDegree≤ p n

    IsBoundedDegree : FormalPolynomial → Set ℓ
    IsBoundedDegree p = Σ ℕ (HasDegree< p)

    HasDegree<-cong : ∀ n → CongruentProperty FormalPolynomialSetoid (λ p → HasDegree< p n)
    HasDegree<-cong n {p} {q} p≈q p[≥n]=zero {m} n≤m = trans (sym (p≈q m)) (p[≥n]=zero n≤m)

    HasDegree-cong : ∀ n → CongruentProperty FormalPolynomialSetoid (λ p → HasDegree p n)
    HasDegree-cong n {p} {q} p≈q (p[n]-nonZero , p[>n]=zero) = NonZero-cong (p≈q n) p[n]-nonZero , λ {i} n<i → trans (sym (p≈q i)) (p[>n]=zero n<i)

    IsBoundedDegree-cong : CongruentProperty FormalPolynomialSetoid IsBoundedDegree
    IsBoundedDegree-cong {p} {q} p≈q (p-bound , p-high-zero) = p-bound , λ {i} pb≤i → trans (sym (p≈q i)) (p-high-zero pb≤i)

    Polynomial : Set (c ⊔ ℓ)
    Polynomial = Σ FormalPolynomial IsBoundedDegree

    get : (p : Polynomial) → ℕ → Carrier
    get p = p .proj₁

    infix 4 _≈_
    infixl 5 _+_ _∸_
    infixl 6 _*_ _*-alt_
    infix 7 -_

    _≈_ : Rel Polynomial ℓ
    (p , _) ≈ (q , _) = p ≈' q

    ≈-refl : Reflexive _≈_
    ≈-refl n = refl

    ≈-sym : Symmetric _≈_
    ≈-sym z n = sym (z n)

    ≈-trans : Transitive _≈_
    ≈-trans z z₁ n = trans (z n) (z₁ n)

    ≈-eq : IsEquivalence _≈_
    ≈-eq = record {
        refl = λ {x} → ≈-refl {x};
        sym = λ {x} {y} → ≈-sym {x} {y};
        trans = λ {x} {y} {z} → ≈-trans {x} {y} {z}
        }

    PolynomialSetoid : Setoid (c ⊔ ℓ) ℓ
    PolynomialSetoid = record { isEquivalence = ≈-eq }

    +-degree-bound : (p q : FormalPolynomial) {m n : ℕ} → (HasDegree< p m) → (HasDegree< q n) → HasDegree< (p +' q) (m ⊔ℕ n)
    +-degree-bound p q {m} {n} p[>m]=0 q[>n]=0 {o} m⊔n≤o = begin
        (p +' q) o      ≈⟨ refl ⟩
        p o +R q o      ≈⟨ +R-cong {p o} {zeroR} {q o} {zeroR} (p[>m]=0 (≤-trans (m≤m⊔n m n) m⊔n≤o)) (q[>n]=0 (≤-trans (m≤n⊔m m n) m⊔n≤o)) ⟩
        zeroR +R zeroR  ≈⟨ zeroR-is-+R-left-id zeroR ⟩
        zeroR           ∎
        where open import Relation.Binary.Reasoning.Setoid S

    _+_ : Polynomial → Polynomial → Polynomial
    (p , m , p[>m]=0) + (q , n , q[>n]=0) = p +' q , m ⊔ℕ n , +-degree-bound p q p[>m]=0 q[>n]=0

    neg-preserves-degree-bound : (p : FormalPolynomial) {m : ℕ} → (HasDegree< p m) → HasDegree< (-' p) m
    neg-preserves-degree-bound p p[>m]=0 {i} m≤i = begin
        -R p i      ≈⟨ negR-cong (p[>m]=0 m≤i) ⟩
        -R zeroR    ≈⟨ negR-zeroR-is-zeroR ⟩
        zeroR       ∎
        where open import Relation.Binary.Reasoning.Setoid S

    -_ : Polynomial → Polynomial
    -_ (p , m , p[>m]=0) = (λ i → -R p i) , m , neg-preserves-degree-bound p p[>m]=0

    _∸_ : Polynomial → Polynomial → Polynomial
    p ∸ q = p + - q

    *-degree-bound' : (p q : FormalPolynomial) {m n : ℕ} → (HasDegree≤ p m) → (HasDegree≤ q n) → HasDegree≤ (p *' q) (m +ℕ n)
    *-degree-bound' p q {m} {n} p[>m]=0 q[>n]=0 {i} m+n≤i = merge-carrying-lemma IsZero _+R_ (λ x y x-is-zero y-is-zero → begin
        x +R y          ≈⟨ +R-cong x-is-zero y-is-zero ⟩
        zeroR +R zeroR  ≈⟨ zeroR-is-+R-left-id zeroR ⟩
        zeroR           ∎
        ) zeroR (*-gen i) (sucℕ i) refl carry
        where
            *-gen : ℕ → ℕ → Carrier
            *-gen i j = p j *R q (i ∸ℕ j)

            split : ∀ j → (m < j) ⊎ (n < i ∸ℕ j)
            split j = <-+-split m n j (i ∸ℕ j) (≤-trans m+n≤i (≤-trans (⊔≥₁ i j) (≤-reflexive (≡-trans (≡-sym (m∸n+n≡m⊔n i j)) (+ℕ-comm (i ∸ℕ j) j)))))

            carry : (j : ℕ) → IsZero (*-gen i j)
            carry j = zeroR-is-*R-strong-absorber (case (split j) of λ {
                (inj₁ m<j) → inj₁ (p[>m]=0 m<j);
                (inj₂ n<i∸j) → inj₂ (q[>n]=0 n<i∸j)})

            open import Relation.Binary.Reasoning.Setoid S

    *-degree-bound : (p q : FormalPolynomial) {m n : ℕ} → (HasDegree< p m) → (HasDegree< q n) → HasDegree< (p *' q) (sucℕ (predℕ m +ℕ predℕ n))
    *-degree-bound p q {m} {n} p-bound q-bound = *-degree-bound' p q {predℕ m} {predℕ n} (HasDegree<⇒HasDegree≤ p m p-bound) (HasDegree<⇒HasDegree≤ q n q-bound)

    _*_ : Polynomial → Polynomial → Polynomial
    (p , m , p[>m]=0) * (q , n , q[>n]=0) = p *' q , sucℕ (predℕ m +ℕ predℕ n) , *-degree-bound p q p[>m]=0 q[>n]=0

    constant-polynomial'-degree-bound : ∀ x → HasDegree< (constant-polynomial' x) 1
    constant-polynomial'-degree-bound x {sucℕ i} 0<i = refl

    zero : Polynomial
    zero = zero' , zeroℕ , λ _ → refl

    one : Polynomial
    one = one' , sucℕ zeroℕ , λ { {sucℕ _} _ → refl }

    _*-alt_ : Polynomial → Polynomial → Polynomial
    p@(p' , p-bound , p-high-zero) *-alt q@(q' , q-bound , q-high-zero) = p' *'-alt q' , IsBoundedDegree-cong (*'-flip p' q') ((p * q) .proj₂)

    *x^'-degree-bound : ∀ p {m} → HasDegree< p m → ∀ n → HasDegree< (p *x^' n) (n +ℕ m)
    *x^'-degree-bound p {m} p[≥m]=0 n {o} n+m≤o with o <? n
    ... | yes o<n = refl
    ... | no ¬o<n = p[≥m]=0 (begin
        m               ≡⟨ ≡-sym (m+n∸m≡n n m) ⟩
        n +ℕ m ∸ℕ n   ≤⟨ ∸-mono {n +ℕ m} {o} {n} {n} n+m≤o ≤-refl ⟩
        o ∸ℕ n          ∎)
        where open ≤-Reasoning

    _*x^_ : Polynomial → ℕ → Polynomial
    (p , m , p[>m]=0) *x^ n = p *x^' n , n +ℕ m , *x^'-degree-bound p p[>m]=0 n

    record IsMonic (p : FormalPolynomial) : Set ℓ where
        field
            degree : ℕ
            monic : p degree ≈R oneR
            bounded : HasDegree≤ p degree

        polynomial : Polynomial
        polynomial = p , sucℕ degree , bounded

        has-degree : ¬ (zeroR ≈R oneR) → HasDegree p degree
        has-degree 0≉1 = (λ p[deg]=0 → 0≉1 (trans (sym p[deg]=0) monic)) , bounded

    record MonicPolynomial : Set (c ⊔ ℓ) where
        field
            poly : FormalPolynomial
            isMonic : IsMonic poly
        open IsMonic isMonic public


    -------------------------
    --- More Degree Stuff ---
    -------------------------

    HasDegree≥ : FormalPolynomial → ℕ → Set ℓ
    HasDegree≥ p m = Σ ℕ λ n → Squash (n ≥ m) × NonZero (p n)

    HasDegree> : FormalPolynomial → ℕ → Set ℓ
    HasDegree> p m = HasDegree≥ p (sucℕ m)

    HasDegree<-raise : ∀ p {m} → HasDegree< p m → ∀ {n} → .(m ≤ n) → HasDegree< p n
    HasDegree<-raise p {m} p[≥m]=0 {n} m≤n {i} i≥n = p[≥m]=0 {i} (≤-trans m≤n i≥n)

    HasDegree≥-lower : ∀ p {m} → HasDegree≥ p m → ∀ {n} → .(m ≥ n) → HasDegree≥ p n
    HasDegree≥-lower p {m} (k , squash k≥m , p[k]-nonZero) {n} m≥n = k , squash (≤-trans m≥n k≥m) , p[k]-nonZero

    HasDegree-fixed : ∀ p {m n} → .(HasDegree p m) → .(HasDegree p n) → m ≡ n
    HasDegree-fixed p {m} {n} deg[p]=m deg[p]=n with <-cmp m n
    ... | tri< m<n _ _ = ⊥-elim-irr (deg[p]=n .proj₁ (deg[p]=m .proj₂ m<n))
    ... | tri≈ _ m=n _ = m=n
    ... | tri> _ _ m>n = ⊥-elim-irr (deg[p]=m .proj₁ (deg[p]=n .proj₂ m>n))

    HasDegree⇒HasDegree≤ : ∀ p {n} → HasDegree p n → HasDegree≤ p n
    HasDegree⇒HasDegree≤ p deg[p]=n = deg[p]=n .proj₂

    HasDegree⇒HasDegree≥ : ∀ p {n} → HasDegree p n → HasDegree≥ p n
    HasDegree⇒HasDegree≥ p {n} deg[p]=n = n , squash ≤-refl , deg[p]=n .proj₁

    HasDegree≤≥⇒HasDegree : ∀ p {n} → HasDegree≤ p n → HasDegree≥ p n → HasDegree p n
    HasDegree≤≥⇒HasDegree p {n} p[>n]=0 (k , squash k≥n , p[k]-nonZero) with ≤⇒<≡ k≥n
    ... | inj₁ n<k = ⊥-elim (p[k]-nonZero (p[>n]=0 n<k))
    ... | inj₂ ≡-refl = p[k]-nonZero , p[>n]=0

    HasDegree<≥-degree-bind : ∀ p {m n} → HasDegree< p m → HasDegree≥ p n → n < m
    HasDegree<≥-degree-bind p {m} {n} p[≥m]=0 (k , squash k≥n , p[k]-nonZero) with ≤-cmp m k
    ... | inj₁ m≤k = ⊥-elim-irr (p[k]-nonZero (p[≥m]=0 m≤k))
    ... | inj₂ m>k = ≤-<-trans k≥n m>k

    HasDegree≤≥-degree-bind : ∀ p {m n} → HasDegree≤ p m → HasDegree≥ p n → n ≤ m
    HasDegree≤≥-degree-bind p {m} {n} deg[p]≤m deg[p]≥n = s≤s⁻¹ (HasDegree<≥-degree-bind p {sucℕ m} {n} deg[p]≤m deg[p]≥n)

    HasDegree<≥-contradict : ∀ p {n} → HasDegree< p n → HasDegree≥ p n → ⊥
    HasDegree<≥-contradict p {n} p[≥n]=0 (k , squash k≥n , p[k]-nonZero) = p[k]-nonZero (p[≥n]=0 {k} k≥n)

    HasDegree≤>-contradict : ∀ p {n} → HasDegree≤ p n → HasDegree> p n → ⊥
    HasDegree≤>-contradict p {n} p[>n]=0 (k , squash k>n , p[k]-nonZero) = p[k]-nonZero (p[>n]=0 {k} k>n)

    _≈deg_ : Rel FormalPolynomial ℓ
    p ≈deg q = Σ ℕ λ n → HasDegree p n × HasDegree q n

    _≤deg_ : Rel FormalPolynomial ℓ
    p ≤deg q = Σ ℕ λ n → HasDegree≤ p n × HasDegree≥ q n

    _<deg_ : Rel FormalPolynomial ℓ
    p <deg q = Σ ℕ λ n → HasDegree< p n × HasDegree≥ q n

    _>deg_ = Function.flip _<deg_
    _≥deg_ = Function.flip _≤deg_

    infix 2 _≈deg_ _≤deg_ _≥deg_ _<deg_ _>deg_

    <deg⇒≤deg : ∀ {p q} → p <deg q → p ≤deg q
    <deg⇒≤deg {p} {q} (n , deg[p]<n , deg[q]≥n) = n , HasDegree<-raise p deg[p]<n n≤sn , deg[q]≥n

    ≤>deg-contradict : ∀ {p q} → p ≤deg q → p >deg q → ⊥
    ≤>deg-contradict {p} {q} (m , deg[p]≤m , deg[q]≥m) (n , deg[q]<n , deg[p]≥n) = <-irrefl ≡-refl (≤-<-trans m≥n m<n)
        where
            m<n : m < n
            m<n = HasDegree<≥-degree-bind q deg[q]<n deg[q]≥m

            m≥n : m ≥ n
            m≥n = HasDegree≤≥-degree-bind p deg[p]≤m deg[p]≥n

    -- Oops, _≈deg_ is not reflexive because knowing p ≈deg p amounts to knowing the degree of p, which we can't do.
    -- (There are some formal polynomials without degrees, even!)

    ≈deg-sym : Symmetric _≈deg_
    ≈deg-sym (n , deg[p]=n , deg[q]=n) = n , deg[q]=n , deg[p]=n

    ≈deg-trans : Transitive _≈deg_
    ≈deg-trans {p} {q} {r} (m , deg[p]=m , deg[q]=m) (n , deg[q]=n , deg[r]=n) with HasDegree-fixed q deg[q]=m deg[q]=n
    ... | ≡-refl = m , deg[p]=m , deg[r]=n

    ≤deg-reflexive : _≈deg_ Relation.Binary.⇒ _≤deg_
    ≤deg-reflexive {p} {q} (n , deg[p]=n , deg[q]=n) = n , HasDegree⇒HasDegree≤ p deg[p]=n , HasDegree⇒HasDegree≥ q deg[q]=n

    ≤deg-trans : Transitive _≤deg_
    ≤deg-trans {p} {q} {r} (m , deg[p]≤m , deg[q]≥m) (n , deg[q]≤n , deg[r]≥n) = m , deg[p]≤m , HasDegree≥-lower r deg[r]≥n (HasDegree≤≥-degree-bind q deg[q]≤n deg[q]≥m)

    <deg-≤deg-trans : Trans _<deg_ _≤deg_ _<deg_
    <deg-≤deg-trans {p} {q} {r} (m , deg[p]<m , deg[q]≥m) (n , deg[q]≤n , deg[r]≥n) = n , HasDegree<-raise p deg[p]<m (HasDegree≤≥-degree-bind q deg[q]≤n deg[q]≥m) , deg[r]≥n

    ≤deg-<deg-trans : Trans _≤deg_ _<deg_ _<deg_
    ≤deg-<deg-trans {p} {q} {r} (m , deg[p]≤m , deg[q]≥m) (n , deg[q]<n , deg[r]≥n) = n , HasDegree<-raise p deg[p]≤m (HasDegree<≥-degree-bind q deg[q]<n deg[q]≥m) , deg[r]≥n

    <deg-irrefl : Irreflexive _≈deg_ _<deg_
    <deg-irrefl p-≈deg-q p-<deg-q = ≤>deg-contradict (≤deg-reflexive (≈deg-sym p-≈deg-q)) p-<deg-q

    <deg-asym : Asymmetric _<deg_
    <deg-asym p-<deg-q p->deg-q = ≤>deg-contradict (<deg⇒≤deg p-<deg-q) p->deg-q

    <deg-trans : Transitive _<deg_
    <deg-trans p-<deg-q = ≤deg-<deg-trans (<deg⇒≤deg p-<deg-q)

    -- --------------------------
    -- --- Decidability stuff ---
    -- --------------------------
    -- {-
    --     TODO, outside of the decidability module:
    --     - if HasDegree p n, then p is limited to n items
    --     - if HasDegree p n and HasDegree p m, then m = n
    --     - if minimal property below, then HasDegree p n
    -- -}
    -- private
    --     module _ (p : Polynomial) where
    --         P : ℕ → Set ℓ
    --         P i = ∀ j → i ≤ j → get p j ≈R zeroR

    -- module _ (≈R-dec : Decidable _≈R_) where
    --     {-
    --         If equality is decidable then:
    --         - there is a function determining degree
    --         - polynomial equality is decidable
    --         note that if you can tell the difference between two specific elements, then you can tell the difference between any two elements, I think.
    --     -}

    --     module _ (p : Polynomial) where
    --         open import Plasmaduck.Counting.GeneralizedMinimum (λ i → ∀ j → i ≤ j → get p j ≈R zeroR) (λ i → Σ ℕ λ j → ¬ (get p j ≈R zeroR)) using ()

    --         deg : Polynomial → ℕ
    --         deg = {!   !}

    --         deg-gets-degree : HasDegree p (deg p)
    --         deg-gets-degree = {!   !}

    --     ≈-dec : Decidable _≈_
    --     ≈-dec = {!   !}


    ------------------------------------
    --- Proving that it forms a ring ---
    ------------------------------------

    +-cong : Congruent₂ _≈_ _≈_ _≈_ _+_
    +-cong = +'-cong

    +-op : SetoidFunction₂ PolynomialSetoid PolynomialSetoid PolynomialSetoid
    +-op = record {
        func = _+_;
        respects = +'-cong
        }

    negate-cong : Congruent _≈_ _≈_ -_
    negate-cong = negate'-cong

    negate-op : SetoidFunction PolynomialSetoid PolynomialSetoid
    negate-op = record {
        func = -_;
        respects = negate'-cong
        }

    *-cong : Congruent₂ _≈_ _≈_ _≈_ _*_
    *-cong = *'-cong

    *-op : SetoidFunction₂ PolynomialSetoid PolynomialSetoid PolynomialSetoid
    *-op = record {
        func = _*_;
        respects = *'-cong
        }

    *-identity : Identity _≈_ _*_ one
    *-identity = *-identity' .proj₁ ∘ proj₁ , *-identity' .proj₂ ∘ proj₁

    *-assoc : Associative _≈_ _*_
    *-assoc p@(p' , _) q@(q' , _) r@(r' , _) = *-assoc' p' q' r'

    *-distrib-+ : _DistributesOver_ _≈_ _*_ _+_
    *-distrib-+ = (λ p q r → *-distrib-+' .proj₁ (p .proj₁) (q .proj₁) (r .proj₁)) , (λ p q r → *-distrib-+' .proj₂ (p .proj₁) (q .proj₁) (r .proj₁))

    PolynomialRawRing : RawRing (c ⊔ ℓ) ℓ
    PolynomialRawRing = record {
        S = PolynomialSetoid;
        +-op = +-op;
        +-inverse = negate-op;
        zero = zero;
        *-op = *-op;
        one = one
        }

    PolynomialIsRing : IsRing PolynomialRawRing
    PolynomialIsRing = record {
        +-isAbelianGroup = record {
            isGroup = record {
                id-is-left-id = λ x n → zeroR-is-+R-left-id (x .proj₁ n);
                inv-is-left-inv = λ x n → Ring.neg-is-+-left-inv ring (x .proj₁ n);
                assoc = λ x y z n → Ring.+-assoc ring (x .proj₁ n) (y .proj₁ n) (z .proj₁ n)
                };
            abelian = λ x y n → Ring.+-comm ring (x .proj₁ n) (y .proj₁ n)
            };
        one-is-*-id = *-identity;
        *-assoc = *-assoc;
        *-+-distributive = *-distrib-+
        }

    PolynomialRing : Ring (c ⊔ ℓ) ℓ
    PolynomialRing = record {
        rawRing = PolynomialRawRing;
        isRing = PolynomialIsRing
        }

    module _ (p@(p' , p-bound , high-p-zero) q@(q' , q-bound , high-q-zero) r@(r' , r-bound , high-r-zero) : Polynomial) where
        identity-lemma-helper : ∀ m n o → .(p-bound +ℕ q-bound +ℕ r-bound < sucℕ m +ℕ sucℕ n +ℕ sucℕ o) → WeakTri (p' m ≈R zeroR) (q' n ≈R zeroR) (r' o ≈R zeroR)
        identity-lemma-helper m n o bounded with <-+-split₃ p-bound q-bound r-bound (sucℕ m) (sucℕ n) (sucℕ o) bounded
        ... | cmp₁ pb<sm = cmp₁ (high-p-zero (s≤s⁻¹ pb<sm))
        ... | cmp₂ qb<sn = cmp₂ (high-q-zero (s≤s⁻¹ qb<sn))
        ... | cmp₃ rb<so = cmp₃ (high-r-zero (s≤s⁻¹ rb<so))

        identity-lemma : ∀ m n o → .(p-bound +ℕ q-bound +ℕ r-bound < sucℕ m +ℕ sucℕ n +ℕ sucℕ o) → (p' m *R q' n *R r' o) ≈R zeroR
        identity-lemma m n o bounded with identity-lemma-helper m n o bounded
        ... | cmp₁ pm=0 = zeroR-is-*R-strong-absorber (inj₁ (zeroR-is-*R-strong-absorber (inj₁ pm=0)))
        ... | cmp₂ qn=0 = zeroR-is-*R-strong-absorber (inj₁ (zeroR-is-*R-strong-absorber (inj₂ qn=0)))
        ... | cmp₃ ro=0 = zeroR-is-*R-strong-absorber (inj₂ ro=0)


module CommutativePolynomial (ring : CommutativeRing c ℓ) where
    open Polynomial (CommutativeRing.ring ring) public

    open CommutativeFormalPolynomial ring using () renaming (*-comm to *-comm')
    *-comm : Commutative _≈_ _*_
    *-comm (p' , _) (q' , _) = *-comm' p' q'

    PolynomialIsCommutativeRing : IsCommutativeRing PolynomialRawRing
    PolynomialIsCommutativeRing = record {
        +-isAbelianGroup = IsRing.+-isAbelianGroup PolynomialIsRing;
        one-is-*-left-id = *-identity .proj₁;
        *-assoc = *-assoc;
        *-+-left-distributive = *-distrib-+ .proj₁;
        *-comm = *-comm
        }

    PolynomialCommutativeRing : CommutativeRing (c ⊔ ℓ) ℓ
    PolynomialCommutativeRing = record {
        rawRing = PolynomialRawRing;
        isCommutativeRing = PolynomialIsCommutativeRing
        }
