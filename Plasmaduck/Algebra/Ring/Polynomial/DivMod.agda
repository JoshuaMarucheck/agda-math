open import Level using (Level; _⊔_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; subst; _≡_; _≗_; module ≡-Reasoning) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Relation.Binary using (Setoid; Rel; Decidable; IsEquivalence; Reflexive; Symmetric; Transitive)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Function using (_∘_; Congruent; Bijective)
open import Data.Empty using (⊥; ⊥-elim; ⊥-elim-irr)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (ℕ; _>_; _<_; _≤_; _≥_; _≤?_; _≤ᵇ_; _<ᵇ_; _≡ᵇ_; z≤n; s≤s; s≤s⁻¹; NonZero; >-nonZero; ≢-nonZero) renaming (zero to zeroℕ; suc to sucℕ; pred to predℕ; _+_ to _+ℕ_; _∸_ to _∸ℕ_; _*_ to _*ℕ_; _/_ to _/ℕ_; _%_ to _%ℕ_; _^_ to _^ℕ_; _⊓_ to _⊓ℕ_; _⊔_ to _⊔ℕ_)
open import Data.Nat.Properties using (≤-refl; ≤-reflexive; ≤-trans; ≤-antisym; m≤n⇒m≤n+o; m≤o∸n⇒m+n≤o; m<n⇒0<n∸m; <⇒≤; ≤⇒≤ᵇ; ≤ᵇ⇒≤; ≡⇒≡ᵇ; ∸-mono; ∸-+-assoc; +-∸-assoc; n∸n≡0; m∸n≤m; m≤n+m; ≰⇒>; ∸-monoˡ-≤; m≤m⊔n; m≤n⊔m; m≥n⇒m⊔n≡m; <-irrefl; +-mono-≤; *-mono-≤; n<1⇒n≡0; m+n∸n≡m; module ≤-Reasoning) renaming (+-comm to +ℕ-comm)
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
open import Plasmaduck.Data.Nat using (≤-recompute; ≥-⊔-semilattice; ≤-cmp; <-≤-trans; ≤-<-trans; n≤sn; ∸-suc-≤; <-+-split₃; [m+kn]/n≡k+m/n; m∸n+n≡m; m∸n≤o⇒m≤o+n; ∸-suc; m∸[m∸n]≡n; [n∸m]∸[o∸m]=n∸o; m+[n∸m]≡n; m<n⇒n∸m-nonZero; ≤→<≡; m∸[n∸o]=m+o∸n; m∸n>0⇒n<m; n=spn; n≤spn)
open import Plasmaduck.Data.FakeFin using (FakeFin)
open import Plasmaduck.Fold.Nat.Merge using (merge; merge-pop-first; merge-carrying-lemma; merge-merge; module MergeSubstitute; module MergeOnSetoid; module Reindex)
open import Plasmaduck.Fold.Nat.InfiniteReindexing using (_≺_; all-index-vectors; InfiniteVector; IsNonZero; HasOneTail; LesserInfiniteVector; LesserInfiniteVectorSetoid; module FiniteVectorBijections; module Cube)
open import Plasmaduck.Counting.Permutation.Defs using (swp)
open import Plasmaduck.Algebra.Ring.Defs using (Ring; RawRing; IsDecidableEqualityRawRing; IsRing; IsCommutativeRing; CommutativeRing; opposite-ring)
open import Plasmaduck.Algebra.Group.Defs using (Group)
open import Plasmaduck.Util.Case using (case_of_)

open import Plasmaduck.Algebra.Ring.FormalPolynomialRing using (module FormalPolynomial)
open import Plasmaduck.Algebra.Ring.PolynomialRing using (module Polynomial)



{-
    I lump all of this together because the polynomials must be bounded for modulus to be defined.
    I could maybe define division as a climbing thing if the *lowest* degree coefficient was 1,
    but that definition wouldn't align with this one at all,
    and would have no guarantee of converging to anything in the usual polynomial sense. (Also you can't really
    define a modulus on that sense of division.)
-}
module Plasmaduck.Algebra.Ring.Polynomial.DivMod {α ℓ : Level} (ring : Ring α ℓ) (dec : IsDecidableEqualityRawRing (Ring.rawRing ring)) where

open FormalPolynomial ring using (FormalPolynomial; FormalPolynomialSetoid; FormalPolynomialRing) renaming (_≈_ to _≈'_; _+_ to _+'_; _∸_ to _∸'_; -_ to -'_; _*_ to _*'_; _⋆_ to _⋆'_; _*x^_ to _*x^'_; one to one'; zero to zero'; constant-polynomial to constant-polynomial'; *x^-force≥ to *x^'-force≥;
    *-const-is-⋆ˡ to *-const-is-⋆ˡ';
    *-raised-one-is-*x^ˡ to *-raised-one-is-*x^ˡ';
    *-raised-one-is-*x^ʳ to *-raised-one-is-*x^ʳ';
    *-*x^-selectiveˡ to *-*x^-selectiveˡ';
    *-*x^-exchange to *-*x^-exchange';
    ⋆-*x^-assoc to ⋆-*x^-assoc';
    *x^-cong' to *x^'-cong'
    )
open Polynomial ring using (MonicPolynomial; Polynomial; HasDegree≤; HasDegree<; HasDegree<-cong;
    zero;
    *x^'-degree-bound;
    constant-polynomial'-degree-bound;
    HasDegree<-raise
    ) renaming (
    +-degree-bound to +'-degree-bound
    )
open Ring ring using (IsZero; IsNonzero; Carrier; S) renaming (
    zero to zeroR; one to oneR; _≈_ to _≈R_; _≉_ to _≉R_; _+_ to _+R_; -_ to -R_; _∸_ to _∸R_; _*_ to _*R_;
    +-op to +R-op;
    +-cong to +R-cong;
    +-assoc to +R-assoc;
    +-comm to +R-comm;
    +-identity to +R-identity;
    neg-cong to negR-cong;
    *-cong to *R-cong;
    *-assoc to *R-assoc;
    ∸-cong to ∸R-cong;
    zero-is-*-strong-absorber to zeroR-is-*R-strong-absorber;
    zero-is-*-left-absorber to zeroR-is-*R-left-absorber;
    zero-is-*-right-absorber to zeroR-is-*R-right-absorber;
    one-is-*-left-id to oneR-is-*R-left-id;
    one-is-*-right-id to oneR-is-*R-right-id;
    zero-is-+-left-id to zeroR-is-+R-left-id;
    zero-is-+-right-id to zeroR-is-+R-right-id;
    neg-zero-is-zero to negR-zeroR-is-zeroR;
    *-+-distributive to *R-+R-distributive;
    neg-is-+-left-inv to neg-is-+R-left-inv;
    neg-is-+-right-inv to neg-is-+R-right-inv
    )
open IsEquivalence (Setoid.isEquivalence S)
open Ring FormalPolynomialRing using () renaming (
    ≈-refl to ≈'-refl;
    ≈-sym to ≈'-sym;
    ≈-trans to ≈'-trans;
    +-op to +'-op;
    +-cong to +'-cong;
    +-assoc to +'-assoc;
    +-comm to +'-comm;
    +-identity to +'-identity;
    neg-cong to neg'-cong;
    *-cong to *'-cong;
    *-assoc to *'-assoc;
    ∸-cong to ∸'-cong;
    zero-is-*-strong-absorber to zero'-is-*'-strong-absorber;
    zero-is-*-left-absorber to zero'-is-*'-left-absorber;
    zero-is-*-right-absorber to zero'-is-*'-right-absorber;
    one-is-*-left-id to one'-is-*'-left-id;
    one-is-*-right-id to one'-is-*'-right-id;
    zero-is-+-left-id to zero'-is-+'-left-id;
    zero-is-+-right-id to zero'-is-+'-right-id;
    neg-zero-is-zero to neg'-zero'-is-zero';
    *-+-distributive to *'-+'-distributive;
    neg-is-+-left-inv to neg-is-+'-left-inv;
    neg-is-+-right-inv to neg-is-+'-right-inv
    )

module Modulus (d : MonicPolynomial) where
    private
        modulus-degree : ℕ
        modulus-degree = MonicPolynomial.degree d

        d-poly : Polynomial
        d-poly = MonicPolynomial.polynomial d

        d-poly' : FormalPolynomial
        d-poly' = MonicPolynomial.poly d

    deg : Polynomial → ℕ
    deg (_ , d , _) = predℕ d

    leading-coeff : Polynomial → Carrier
    leading-coeff (p , d , _) = p (predℕ d)

    -- First goal: reduce the degree of the dividend by 1
    module _
        (p@(p' , m , p'[≥m]=0) : Polynomial)
        .(m≥mod-deg : deg p ≥ modulus-degree)
        where
        private
            m' = predℕ m

        /-poke : FormalPolynomial
        /-poke = constant-polynomial' (leading-coeff p) *x^' (deg p ∸ℕ modulus-degree)

        %-poke : FormalPolynomial
        %-poke = p' ∸' (leading-coeff p ⋆' d-poly' *x^' (deg p ∸ℕ modulus-degree))

        %-poke[m]-zero : IsZero (%-poke m')
        %-poke[m]-zero = begin
            %-poke m'                                                               ≈⟨ refl ⟩
            (p' ∸' (leading-coeff p ⋆' d-poly' *x^' (deg p ∸ℕ modulus-degree))) m'  ≈⟨ refl ⟩
            p' m' ∸R ((leading-coeff p ⋆' d-poly' *x^' (m' ∸ℕ modulus-degree)) m')  ≈⟨ ∸R-cong refl (reflexive (*x^'-force≥ (leading-coeff p ⋆' d-poly') {m' ∸ℕ modulus-degree} {m'} (m∸n≤m m' modulus-degree))) ⟩
            p' m' ∸R (leading-coeff p ⋆' d-poly') (m' ∸ℕ (m' ∸ℕ modulus-degree))    ≈⟨ ∸R-cong refl (reflexive (cong (leading-coeff p ⋆' d-poly') (m∸[m∸n]≡n m≥mod-deg))) ⟩
            p' m' ∸R (leading-coeff p ⋆' d-poly') modulus-degree                    ≈⟨ refl ⟩
            p' m' ∸R leading-coeff p *R d-poly' modulus-degree                      ≈⟨ ∸R-cong refl (*R-cong refl (MonicPolynomial.monic d)) ⟩
            p' m' ∸R leading-coeff p *R oneR                                        ≈⟨ ∸R-cong {p' m'} refl (oneR-is-*R-right-id (leading-coeff p)) ⟩
            p' m' ∸R leading-coeff p                                                ≈⟨ neg-is-+R-right-inv (p' m') ⟩
            zeroR                                                                   ∎
            where open import Relation.Binary.Reasoning.Setoid S

        /-poke-degree : HasDegree≤ /-poke (deg p ∸ℕ modulus-degree)
        /-poke-degree =  subst (HasDegree< /-poke) (+ℕ-comm (deg p ∸ℕ modulus-degree) 1) (*x^'-degree-bound (constant-polynomial' (leading-coeff p)) (constant-polynomial'-degree-bound (leading-coeff p)) (deg p ∸ℕ modulus-degree))

        %-poke-degree : HasDegree< %-poke m'
        %-poke-degree {i} m'≤i with ≤→<≡ m'≤i
        ... | inj₂ ≡-refl = %-poke[m]-zero
        ... | inj₁ m'<i = begin
            %-poke i                                                                ≈⟨ refl ⟩
            p' i ∸R (leading-coeff p ⋆' d-poly' *x^' (deg p ∸ℕ modulus-degree)) i   ≈⟨ ∸R-cong (p'[≥m]=0 m≤i) refl ⟩
            zeroR ∸R (leading-coeff p ⋆' d-poly' *x^' (deg p ∸ℕ modulus-degree)) i  ≈⟨ zeroR-is-+R-left-id (-R (leading-coeff p ⋆' d-poly' *x^' (deg p ∸ℕ modulus-degree)) i) ⟩
            -R (leading-coeff p ⋆' d-poly' *x^' (deg p ∸ℕ modulus-degree)) i        ≈⟨ negR-cong (reflexive (*x^'-force≥ (leading-coeff p ⋆' d-poly') {m' ∸ℕ modulus-degree} {i} (≤-trans (m∸n≤m m' modulus-degree) m'≤i))) ⟩
            -R (leading-coeff p ⋆' d-poly') (i ∸ℕ (m' ∸ℕ modulus-degree ))          ≈⟨ refl ⟩
            -R (leading-coeff p *R d-poly' (i ∸ℕ (m' ∸ℕ modulus-degree )))          ≈⟨ negR-cong (*R-cong refl (MonicPolynomial.bounded d {i ∸ℕ (m' ∸ℕ modulus-degree )} thing)) ⟩
            -R (leading-coeff p *R zeroR)                                           ≈⟨ negR-cong (zeroR-is-*R-right-absorber (leading-coeff p)) ⟩
            -R zeroR                                                                ≈⟨ negR-zeroR-is-zeroR ⟩
            zeroR                                                                   ∎
            where
                m≤i : m ≤ i
                m≤i = ≤-trans (n≤spn m) m'<i

                thing : modulus-degree < i ∸ℕ (m' ∸ℕ modulus-degree)
                thing = begin
                    sucℕ modulus-degree             ≡⟨⟩
                    1 +ℕ modulus-degree             ≤⟨ +-mono-≤ {1} {i ∸ℕ m'} {u = modulus-degree} (m<n⇒0<n∸m m'<i) ≤-refl ⟩
                    i ∸ℕ m' +ℕ modulus-degree       ≡⟨ +ℕ-comm (i ∸ℕ m') modulus-degree ⟩
                    modulus-degree +ℕ (i ∸ℕ m')     ≡⟨ ≡-sym (+-∸-assoc modulus-degree (<⇒≤ m'<i)) ⟩
                    modulus-degree +ℕ i ∸ℕ m'       ≡⟨ cong (_∸ℕ m') (+ℕ-comm modulus-degree i) ⟩
                    i +ℕ modulus-degree ∸ℕ m'       ≡⟨ ≡-sym (m∸[n∸o]=m+o∸n i m' modulus-degree m≥mod-deg) ⟩
                    i ∸ℕ (m' ∸ℕ modulus-degree)     ∎
                    where open ≤-Reasoning
                open import Relation.Binary.Reasoning.Setoid S

        p≈p%d+p/d*d-poke : p' ≈' %-poke +' /-poke *' d-poly'
        p≈p%d+p/d*d-poke = begin
            p'                                                                  ≈⟨ ≈'-sym (zero'-is-+'-right-id p') ⟩
            p' +' zero'                                                         ≈⟨ +'-cong {p'} ≈'-refl (≈'-sym (neg-is-+'-left-inv (c ⋆' d-poly' *x^' dp∸m))) ⟩
            p' +' (-' (c ⋆' d-poly' *x^' dp∸m) +' (c ⋆' d-poly' *x^' dp∸m))     ≈⟨ ≈'-sym (+'-assoc p' (-' (c ⋆' d-poly' *x^' dp∸m)) (c ⋆' d-poly' *x^' dp∸m)) ⟩
            p' ∸' (c ⋆' d-poly' *x^' dp∸m) +' (c ⋆' d-poly' *x^' dp∸m)          ≈⟨ +'-cong {p' ∸' (c ⋆' d-poly' *x^' dp∸m)} ≈'-refl thing ⟩
            p' ∸' (c ⋆' d-poly' *x^' dp∸m) +' /-poke *' d-poly'                 ≈⟨ ≈'-refl ⟩
            %-poke +' /-poke *' d-poly'                                         ∎
            where
                open import Relation.Binary.Reasoning.Setoid FormalPolynomialSetoid

                dp∸m : ℕ
                dp∸m = deg p ∸ℕ modulus-degree

                c = leading-coeff p

                thing : (c ⋆' d-poly' *x^' dp∸m) ≈' /-poke *' d-poly'
                thing = begin
                    c ⋆' d-poly' *x^' dp∸m                          ≈⟨ *x^'-cong' dp∸m (≈'-sym (*-const-is-⋆ˡ' c d-poly')) ⟩
                    (constant-polynomial' c *' d-poly') *x^' dp∸m   ≈⟨ *-*x^-selectiveˡ' (constant-polynomial' c) d-poly' dp∸m ⟩
                    constant-polynomial' c *x^' dp∸m *' d-poly'     ≈⟨ ≈'-refl ⟩
                    /-poke *' d-poly'                               ∎

    %-helper : (p : FormalPolynomial) → {n : ℕ} → (HasDegree< p (n +ℕ modulus-degree)) → FormalPolynomial
    %-helper p {zeroℕ} p-bound = p
    %-helper p n@{sucℕ n'} p-bound = %-helper step {n'} (%-poke-degree poly poly-deg-bound)
        where
            poly : Polynomial
            poly = (p , n +ℕ modulus-degree , p-bound)

            poly-deg-bound = m≤n+m modulus-degree n'

            step : FormalPolynomial
            step = %-poke poly poly-deg-bound

    /-helper' : (acc p : FormalPolynomial) → {n : ℕ} → (HasDegree< p (n +ℕ modulus-degree)) → FormalPolynomial
    /-helper' acc p {zeroℕ} p-bound = acc
    /-helper' acc p n@{sucℕ n'} p-bound = /-helper' (dividend-piece +' acc) step (%-poke-degree poly poly-deg-bound)
        where
            poly : Polynomial
            poly = (p , n +ℕ modulus-degree , p-bound)

            poly-deg-bound = m≤n+m modulus-degree n'

            step : FormalPolynomial
            step = %-poke poly poly-deg-bound

            dividend-piece : FormalPolynomial
            dividend-piece = /-poke poly poly-deg-bound

    /-helper : (p : FormalPolynomial) → {n : ℕ} → (HasDegree< p (n +ℕ modulus-degree)) → FormalPolynomial
    /-helper = /-helper' zero'

    /-helper'-acc-cong :
        (acc₁ acc₂ p : FormalPolynomial) → {n : ℕ} → (p-bound : HasDegree< p (n +ℕ modulus-degree)) →
        acc₁ ≈' acc₂ →
        /-helper' acc₁ p p-bound ≈' /-helper' acc₂ p p-bound
    /-helper'-acc-cong acc₁ acc₂ p {zeroℕ} p-bound acc₁≈acc₂ = acc₁≈acc₂
    /-helper'-acc-cong acc₁ acc₂ p n@{sucℕ n'} p-bound acc₁≈acc₂ = /-helper'-acc-cong (dividend-piece +' acc₁) (dividend-piece +' acc₂) step (%-poke-degree poly poly-deg-bound) (+'-cong {dividend-piece} ≈'-refl acc₁≈acc₂)
        where
            poly : Polynomial
            poly = (p , n +ℕ modulus-degree , p-bound)

            poly-deg-bound = m≤n+m modulus-degree n'

            step : FormalPolynomial
            step = %-poke poly poly-deg-bound

            dividend-piece : FormalPolynomial
            dividend-piece = /-poke poly poly-deg-bound

    /-helper'-extract-acc :
        (acc p : FormalPolynomial) → {n : ℕ} → (p-bound : HasDegree< p (n +ℕ modulus-degree)) →
        /-helper' acc p p-bound ≈' acc +' /-helper p p-bound
    /-helper'-extract-acc acc p {zeroℕ} p-bound = begin
        acc             ≈⟨ ≈'-sym (zero'-is-+'-right-id acc) ⟩
        acc +' zero'    ∎
        where open import Relation.Binary.Reasoning.Setoid FormalPolynomialSetoid
    /-helper'-extract-acc acc p n@{sucℕ n'} p-bound = begin
        /-helper' (dividend-piece +' acc) step %-poke-deg           ≈⟨ /-helper'-extract-acc (dividend-piece +' acc) step %-poke-deg ⟩
        dividend-piece +' acc +' /-helper' zero' step %-poke-deg    ≈⟨ +'-cong {u = /-helper' zero' step %-poke-deg} (+'-comm dividend-piece acc) ≈'-refl ⟩
        acc +' dividend-piece +' /-helper' zero' step %-poke-deg    ≈⟨ +'-assoc acc dividend-piece (/-helper step %-poke-deg) ⟩
        acc +' (dividend-piece +' /-helper' zero' step %-poke-deg)  ≈⟨ +'-cong {acc} ≈'-refl (≈'-sym (/-helper'-extract-acc dividend-piece step %-poke-deg)) ⟩
        acc +' /-helper' dividend-piece step %-poke-deg             ≈⟨ +'-cong {acc} ≈'-refl (/-helper'-acc-cong dividend-piece (dividend-piece +' zero') step %-poke-deg (≈'-sym (zero'-is-+'-right-id dividend-piece))) ⟩
        acc +' /-helper' (dividend-piece +' zero') step %-poke-deg  ∎
        where
            open import Relation.Binary.Reasoning.Setoid FormalPolynomialSetoid
            poly : Polynomial
            poly = (p , n +ℕ modulus-degree , p-bound)

            poly-deg-bound = m≤n+m modulus-degree n'

            %-poke-deg = %-poke-degree poly poly-deg-bound

            step : FormalPolynomial
            step = %-poke poly poly-deg-bound

            dividend-piece : FormalPolynomial
            dividend-piece = /-poke poly poly-deg-bound

    %-helper-degree-bound :
        (p : FormalPolynomial) → {n : ℕ} → (p-bound : HasDegree< p (n +ℕ modulus-degree)) →
        HasDegree< (%-helper p p-bound) modulus-degree
    %-helper-degree-bound p {zeroℕ} p[≥mod-deg]=0 = p[≥mod-deg]=0
    %-helper-degree-bound p n@{sucℕ n'} p-bound = %-helper-degree-bound step {n'} (%-poke-degree poly poly-deg-bound)
        where
            poly : Polynomial
            poly = (p , n +ℕ modulus-degree , p-bound)

            poly-deg-bound = m≤n+m modulus-degree n'

            step : FormalPolynomial
            step = %-poke poly poly-deg-bound

    /-helper-degree-bound :
        (p : FormalPolynomial) → {n : ℕ} → (p-bound : HasDegree< p (n +ℕ modulus-degree)) →
        HasDegree< (/-helper p p-bound) n
    /-helper-degree-bound p {zeroℕ} p-bound = λ .z → refl
    /-helper-degree-bound p n@{sucℕ n'} p-bound = HasDegree<-cong n {_} {/-helper p p-bound} (begin
        dividend-piece +' /-helper step %-poke-deg              ≈⟨ ≈'-sym (/-helper'-extract-acc dividend-piece step %-poke-deg) ⟩
        /-helper' dividend-piece step %-poke-deg                ≈⟨ /-helper'-acc-cong dividend-piece (dividend-piece +' zero') step %-poke-deg (≈'-sym (zero'-is-+'-right-id dividend-piece)) ⟩
        /-helper' (dividend-piece +' zero') step %-poke-deg     ≈⟨ ≈'-refl ⟩
        /-helper p p-bound                                      ∎) (subst (HasDegree< (dividend-piece +' /-helper step %-poke-deg)) thing (+'-degree-bound dividend-piece (/-helper step %-poke-deg) (/-poke-degree poly poly-deg-bound) (/-helper-degree-bound step %-poke-deg)))
        where

            poly : Polynomial
            poly = p , n +ℕ modulus-degree , p-bound

            poly-deg-bound = m≤n+m modulus-degree n'

            %-poke-deg = %-poke-degree poly poly-deg-bound

            step : FormalPolynomial
            step = %-poke poly poly-deg-bound

            dividend-piece : FormalPolynomial
            dividend-piece = /-poke poly poly-deg-bound

            thing : sucℕ (deg poly ∸ℕ modulus-degree) ⊔ℕ n' ≡ n
            thing =
                sucℕ (deg poly ∸ℕ modulus-degree) ⊔ℕ n'                 ≡⟨⟩
                sucℕ (n' +ℕ modulus-degree ∸ℕ modulus-degree) ⊔ℕ n'     ≡⟨ cong (λ q → sucℕ q ⊔ℕ n') (m+n∸n≡m n' modulus-degree) ⟩
                sucℕ n' ⊔ℕ n'                                           ≡⟨ m≥n⇒m⊔n≡m n≤sn ⟩
                n                                                       ∎
                where open ≡-Reasoning

            open import Relation.Binary.Reasoning.Setoid FormalPolynomialSetoid

    p≈p%d+p/d*d-helper :
        (p : FormalPolynomial) → {n : ℕ} → (p-bound : HasDegree< p (n +ℕ modulus-degree)) →
        p ≈' %-helper p p-bound +' /-helper p p-bound *' d-poly'
    p≈p%d+p/d*d-helper p {zeroℕ} p-bound = begin
        p                       ≈⟨ ≈'-sym (zero'-is-+'-right-id p) ⟩
        p +' zero'              ≈⟨ +'-cong {p} ≈'-refl (≈'-sym (zero'-is-*'-left-absorber d-poly')) ⟩
        p +' zero' *' d-poly'   ∎
        where open import Relation.Binary.Reasoning.Setoid FormalPolynomialSetoid
    p≈p%d+p/d*d-helper p n@{sucℕ n'} p-bound = begin
        p                                                                                                       ≈⟨ p≈p%d+p/d*d-poke (p , n +ℕ modulus-degree , p-bound) (m≤n+m modulus-degree n') ⟩
        step +' dividend-piece *' d-poly'                                                                       ≈⟨ +'-cong {u = dividend-piece *' d-poly'} (p≈p%d+p/d*d-helper step {n'} %-poke-deg) ≈'-refl ⟩
        (%-helper step {n'} %-poke-deg +' /-helper step %-poke-deg *' d-poly') +' dividend-piece *' d-poly'     ≈⟨ +'-assoc (%-helper step {n'} %-poke-deg) (/-helper step %-poke-deg *' d-poly') (dividend-piece *' d-poly') ⟩
        %-helper step {n'} %-poke-deg +' (/-helper step %-poke-deg *' d-poly' +' dividend-piece *' d-poly')     ≈⟨ +'-cong {%-helper step {n'} %-poke-deg} ≈'-refl (≈'-sym (*'-+'-distributive .proj₂ d-poly' (/-helper step %-poke-deg) dividend-piece)) ⟩
        %-helper step {n'} %-poke-deg +' (/-helper step %-poke-deg +' dividend-piece) *' d-poly'                ≈⟨ +'-cong {%-helper step {n'} %-poke-deg} ≈'-refl (*'-cong {u = d-poly'} (begin
            /-helper step %-poke-deg +' dividend-piece              ≈⟨ +'-comm (/-helper step %-poke-deg) dividend-piece ⟩
            dividend-piece +' /-helper step %-poke-deg              ≈⟨ ≈'-sym (/-helper'-extract-acc dividend-piece step %-poke-deg) ⟩
            /-helper' dividend-piece step %-poke-deg                ≈⟨ /-helper'-acc-cong dividend-piece (dividend-piece +' zero') step %-poke-deg (≈'-sym (zero'-is-+'-right-id dividend-piece)) ⟩
            /-helper' (dividend-piece +' zero') step %-poke-deg     ∎
            ) ≈'-refl) ⟩
        %-helper step {n'} %-poke-deg +' /-helper' (dividend-piece +' zero') step %-poke-deg *' d-poly'         ∎
        where
            open import Relation.Binary.Reasoning.Setoid FormalPolynomialSetoid

            poly : Polynomial
            poly = (p , n +ℕ modulus-degree , p-bound)

            poly-deg-bound = m≤n+m modulus-degree n'
            %-poke-deg = %-poke-degree poly poly-deg-bound

            step : FormalPolynomial
            step = %-poke poly poly-deg-bound

            dividend-piece : FormalPolynomial
            dividend-piece = /-poke poly poly-deg-bound

module _ (p@(p' , m , p'-bound-at-m) : Polynomial) (q : MonicPolynomial) where
    private
        m' = predℕ m

        modulus-degree : ℕ
        modulus-degree = MonicPolynomial.degree q

        d-poly : Polynomial
        d-poly = MonicPolynomial.polynomial q

        d-poly' : FormalPolynomial
        d-poly' = MonicPolynomial.poly q

        p'-bound-at-m-twist : .(modulus-degree ≤ m) → HasDegree< p' (m ∸ℕ modulus-degree +ℕ modulus-degree)
        p'-bound-at-m-twist mod-deg≤m = subst (HasDegree< p') (≡-sym (m∸n+n≡m {m} {modulus-degree} mod-deg≤m)) p'-bound-at-m

    open Modulus q

    _/'_ : FormalPolynomial
    _/'_ with ≤-cmp m modulus-degree
    ... | inj₁ m≤mod-deg = zero'
    ... | inj₂ m>mod-deg = /-helper p' (p'-bound-at-m-twist (<⇒≤ m>mod-deg))

    /'-degree-bound : HasDegree< _/'_ (m ∸ℕ modulus-degree)
    /'-degree-bound with ≤-cmp m modulus-degree
    ... | inj₁ m≤mod-deg = λ .z → refl
    ... | inj₂ m>mod-deg = /-helper-degree-bound p' {m ∸ℕ modulus-degree} (p'-bound-at-m-twist (<⇒≤ m>mod-deg))

    _/_ : Polynomial
    _/_ = _/'_ , m ∸ℕ modulus-degree , /'-degree-bound

    _%'_ : FormalPolynomial
    _%'_ with ≤-cmp m modulus-degree
    ... | inj₁ m≤mod-deg = p'
    ... | inj₂ m>mod-deg = %-helper p' (p'-bound-at-m-twist (<⇒≤ m>mod-deg))

    %'-degree-bound : HasDegree< _%'_ modulus-degree
    %'-degree-bound with ≤-cmp m modulus-degree
    ... | inj₁ m≤mod-deg = HasDegree<-raise p' p'-bound-at-m m≤mod-deg
    ... | inj₂ m>mod-deg = %-helper-degree-bound p' (p'-bound-at-m-twist (<⇒≤ m>mod-deg))

    _%_ : Polynomial
    _%_ = _%'_ , modulus-degree , %'-degree-bound

    p≈p%q+p/q*q : p' ≈' _%'_ +' _/'_ *' d-poly'
    p≈p%q+p/q*q with ≤-cmp m modulus-degree
    ... | inj₂ m>mod-deg = p≈p%d+p/d*d-helper p' (p'-bound-at-m-twist (<⇒≤ m>mod-deg))
    ... | inj₁ m≤mod-deg = begin
        p'                      ≈⟨ ≈'-sym (zero'-is-+'-right-id p') ⟩
        p' +' zero'             ≈⟨ +'-cong {p'} ≈'-refl (≈'-sym (zero'-is-*'-left-absorber d-poly')) ⟩
        p' +' zero' *' d-poly'  ∎
        where open import Relation.Binary.Reasoning.Setoid FormalPolynomialSetoid
