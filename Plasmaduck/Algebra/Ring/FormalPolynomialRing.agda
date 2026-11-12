open import Level using (Level; _⊔_)
open import Relation.Binary.PropositionalEquality using (subst; _≡_; _≗_; module ≡-Reasoning) renaming (cong to ≡-cong; cong₂ to ≡-cong₂; refl to ≡-refl; sym to ≡-sym)
open import Relation.Binary using (Setoid; Rel; Decidable; IsEquivalence; Reflexive; Symmetric; Transitive)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Function using (_∘_; Congruent; Bijective)
open import Data.Empty using (⊥; ⊥-elim; ⊥-elim-irr)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (ℕ; _>_; _<_; _≤_; _≥_; _≤?_; _≤ᵇ_; _≡ᵇ_; z≤n; s≤s; s≤s⁻¹; NonZero; >-nonZero) renaming (zero to zeroℕ; suc to sucℕ; pred to predℕ; _+_ to _+ℕ_; _∸_ to _∸ℕ_; _*_ to _*ℕ_; _/_ to _/ℕ_; _%_ to _%ℕ_; _^_ to _^ℕ_; _⊓_ to _⊓ℕ_; _⊔_ to _⊔ℕ_)
open import Data.Nat.Properties using (≤-refl; ≤-reflexive; ≤-trans; ≤-antisym; m≤n⇒m≤n+o; m≤o∸n⇒m+n≤o; ≤⇒≤ᵇ; ≤ᵇ⇒≤; ≡⇒≡ᵇ; ∸-mono; ∸-+-assoc; +-∸-assoc; n∸n≡0; m∸n≤m; ≰⇒>; ∸-monoˡ-≤; m≤m⊔n; m≤n⊔m; <-irrefl; +-mono-≤; *-mono-≤; n<1⇒n≡0; module ≤-Reasoning) renaming (+-comm to +ℕ-comm)
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
open import Plasmaduck.Data.Nat using (≤-recompute; ≥-⊔-semilattice; ≤-cmp; <-≤-trans; ≤-<-trans; n≤sn; <-+-split₃; [m+kn]/n≡k+m/n; m∸n+n≡m; m∸n≤o⇒m≤o+n; ∸-suc; m∸[m∸n]≡n; [n∸m]∸[o∸m]=n∸o; m+[n∸m]≡n; m<n⇒n∸m-nonZero)
open import Plasmaduck.Data.FakeFin using (FakeFin)
open import Plasmaduck.Fold.Nat.Merge using (merge; merge-pop-first; merge-carrying-lemma; merge-merge; module MergeSubstitute; module MergeOnSetoid; module Reindex)
open import Plasmaduck.Fold.Nat.InfiniteReindexing using (_≺_; all-index-vectors; InfiniteVector; IsNonZero; HasOneTail; LesserInfiniteVector; LesserInfiniteVectorSetoid; module FiniteVectorBijections; module Cube)
open import Plasmaduck.Counting.Permutation.Defs using (swp)
open import Plasmaduck.Algebra.Ring.Defs using (Ring; RawRing; IsRing; IsCommutativeRing; CommutativeRing; opposite-ring)
open import Plasmaduck.Algebra.Group.Defs using (Group)
open import Plasmaduck.Util.Case using (case_of_)




{-
    Decisions to make for representation:
    do I force it to be decidable whether an element is zero or not?
    - if yes:
      - i can do addition and cancel and reduce the polynomial to its smallest representation
      - this would let me make degree a function, by just taking the length of the list
    - if no:
      - it'll be a setoid, where two polynomials are equal if the extra elements on one are zero (and their agreeing elements match, of course)
      - degree will be a provable property, not a function
-}
module Plasmaduck.Algebra.Ring.FormalPolynomialRing where

variable
    c ℓ : Level

module RawFormalPolynomial (ring : RawRing c ℓ) where
    open RawRing ring using (IsZero; IsNonzero; Carrier; S; neg-cong) renaming (zero to zeroR; one to oneR; _≈_ to _≈R_; _+_ to _+R_; -_ to -R_; _*_ to _*R_; +-cong to +R-cong; *-cong to *R-cong)
    open import Relation.Binary.Reasoning.Setoid S
    open IsEquivalence (S .Setoid.isEquivalence)

    open MergeSubstitute S using (merge-local-substitute-generate; merge-substitute-generate)
    open MergeOnSetoid S using (merge-pop-last)


    FormalPolynomial : Set c
    FormalPolynomial = ℕ → Carrier

    _≈_ : Rel FormalPolynomial ℓ
    p ≈ q = ∀ n → p n ≈R q n

    ≈-refl : Reflexive _≈_
    ≈-refl n = refl

    ≈-sym : Symmetric _≈_
    ≈-sym z n = sym (z n)

    ≈-trans : Transitive _≈_
    ≈-trans z z₁ n = trans (z n) (z₁ n)

    ≈-eq : IsEquivalence _≈_
    ≈-eq = record {
        refl = ≈-refl;
        sym = ≈-sym;
        trans = ≈-trans
        }

    FormalPolynomialSetoid : Setoid c ℓ
    FormalPolynomialSetoid = record { isEquivalence = ≈-eq }

    infix 4 _≈_
    infixl 5 _+_ _∸_
    infixl 6 _*_ _*-alt_
    infix 7 -_

    _+_ : FormalPolynomial → FormalPolynomial → FormalPolynomial
    _+_ p q o = p o +R q o

    -_ : FormalPolynomial → FormalPolynomial
    -_ p i = -R (p i)

    _∸_ : FormalPolynomial → FormalPolynomial → FormalPolynomial
    p ∸ q = p + - q

    _*_ : FormalPolynomial → FormalPolynomial → FormalPolynomial
    _*_ p q i = merge _+R_ zeroR (λ j → (p j *R q (i ∸ℕ j))) (sucℕ i)

    _*-alt_ : FormalPolynomial → FormalPolynomial → FormalPolynomial
    _*-alt_ p q i = merge _+R_ zeroR (λ j → (p (i ∸ℕ j) *R q j)) (sucℕ i)

    zero : FormalPolynomial
    zero _ = zeroR

    one : FormalPolynomial
    one zeroℕ = oneR
    one (sucℕ _) = zeroR

    one-force-nonZero : ∀ i → {{_ : NonZero i}} → one i ≡ zeroR
    one-force-nonZero (sucℕ i) = ≡-refl


    ------------------------------------
    --- Proving that it forms a ring ---
    ------------------------------------

    +-cong : Congruent₂ _≈_ _≈_ _≈_ _+_
    +-cong p≈ q≈ i = +R-cong (p≈ i) (q≈ i)

    +-op : SetoidFunction₂ FormalPolynomialSetoid FormalPolynomialSetoid FormalPolynomialSetoid
    +-op = record {
        func = _+_;
        respects = λ p q i → +R-cong (p i) (q i)
        }

    negate-cong : Congruent _≈_ _≈_ -_
    negate-cong = λ p i → neg-cong (p i)

    negate-op : SetoidFunction FormalPolynomialSetoid FormalPolynomialSetoid
    negate-op = record {
        func = -_;
        respects = λ p i → neg-cong (p i)
        }

    ∸-cong : Congruent₂ _≈_ _≈_ _≈_ _∸_
    ∸-cong p≈ q≈ = +-cong p≈ (negate-cong q≈)

    ∸-op : SetoidFunction₂ FormalPolynomialSetoid FormalPolynomialSetoid FormalPolynomialSetoid
    ∸-op = record {
        func = _∸_;
        respects = ∸-cong
        }

    *-cong : Congruent₂ _≈_ _≈_ _≈_ _*_
    *-cong {p₁} {p₂} {q₁} {q₂} p₁≈p₂ q₁≈q₂ i = merge-substitute-generate _+R_ +R-cong zeroR (λ j → (p₁ j *R q₁ (i ∸ℕ j))) (λ j → (p₂ j *R q₂ (i ∸ℕ j))) (λ j → *R-cong (p₁≈p₂ j) (q₁≈q₂ (i ∸ℕ j))) (sucℕ i)

    *-op : SetoidFunction₂ FormalPolynomialSetoid FormalPolynomialSetoid FormalPolynomialSetoid
    *-op = record {
        func = _*_;
        respects = *-cong
        }

module LeftFormalPolynomialLemmas (ring : Ring c ℓ) where
    open Ring ring using (IsZero; IsNonzero; Carrier; S) renaming (
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
    open MergeSubstitute S using (merge-local-substitute-generate; merge-substitute-generate; merge-substitute; merge-substitute-start; merge-substitute-op)
    open MergeOnSetoid S using (merge-pop-last; merge-distribute-theorem; merge-zipper-lemma)
    open RawFormalPolynomial (ring .Ring.rawRing) using (FormalPolynomial; FormalPolynomialSetoid; _≈_; _+_; _∸_; _*_; _*-alt_; zero; one; one-force-nonZero; +-cong; ∸-cong; negate-cong; *-cong)

    *-flip : ∀ p q → p * q ≈ p *-alt q
    *-flip p q i = begin
        (p * q) i                                           ≈⟨ refl ⟩
        merge _+R_ zeroR (λ j → (p j *R q (i ∸ℕ j))) i*     ≈⟨ merge-local-substitute-generate _+R_ +R-cong zeroR _ _ i* (λ j j<i* → reflexive (≡-cong (λ k → p k *R q (i ∸ℕ k)) (≡-sym (m<n⇒m%n≡m j<i*)))) ⟩
        merge _+R_ zeroR (gen ∘ inject) i*                  ≈⟨ reindex' S +R-op gen-func +R-assoc +R-comm i* inject inject-bijective-binding shuffle shuffle-bijective zeroR ⟩
        merge _+R_ zeroR (gen ∘ shuffle ∘ inject) i*        ≈⟨ merge-local-substitute-generate _+R_ +R-cong zeroR _ _ i* (λ j j<i* → begin
            gen (shuffle (inject j))            ≈⟨ reflexive (≡-cong (λ k → p (i ∸ℕ k) *R q (i ∸ℕ (i ∸ℕ k))) (m<n⇒m%n≡m j<i*)) ⟩
            p (i ∸ℕ j) *R q (i ∸ℕ (i ∸ℕ j))     ≈⟨ reflexive (≡-cong (λ k → p (i ∸ℕ j) *R q k) (m∸[m∸n]≡n {i} {j} (s≤s⁻¹ j<i*))) ⟩
            p (i ∸ℕ j) *R q j                   ∎) ⟩
        merge _+R_ zeroR (λ j → p (i ∸ℕ j) *R q j) i*       ≈⟨ refl ⟩
        (p *-alt q) i                                       ∎
        where
            i* = sucℕ i
            open import Relation.Binary.Reasoning.Setoid S

            IndexSetoid = discrete-setoid (FakeFin i*)
            Index = FakeFin i*

            open Reindex IndexSetoid using (BijectiveBinding; reindex'; bind'; unbind; unbind'; bind'-unbind'; unbind'-force<)

            inject : ℕ → FakeFin i*
            inject j = j %ℕ i* , squash (m%n<n j i*)

            bound-inject-func : SetoidFunction IndexSetoid IndexSetoid
            bound-inject-func = (bind' i* inject) which-is-cong from-discrete-cong IndexSetoid (bind' i* inject)

            inject-bijective-binding : BijectiveBinding i* inject
            inject-bijective-binding = both-inv→bijective IndexSetoid IndexSetoid bound-inject-func ((Function.id which-is-cong from-discrete-cong IndexSetoid Function.id) , (λ x → squash-≡ (inv x)) , (λ x → squash-≡ (inv x)))
                where
                    inv : ((j , _) : FakeFin i*) → inject j .proj₁ ≡ j
                    inv (j , squash j<i*) = m<n⇒m%n≡m (≤-recompute j<i*)

            shuffle : Index → Index
            shuffle (j , _) = i ∸ℕ j , squash (s≤s (m∸n≤m i j))

            shuffle-func : SetoidFunction IndexSetoid IndexSetoid
            shuffle-func = shuffle which-is-cong from-discrete-cong IndexSetoid shuffle

            shuffle-bijective : Bijective _≡_ _≡_ shuffle
            shuffle-bijective = both-inv→bijective IndexSetoid IndexSetoid shuffle-func (shuffle-func , inv , inv)
                where
                    inv : Plasmaduck.Function.Properties.LeftInverse _≡_ _≡_ shuffle shuffle
                    inv (j , squash j<i*) = squash-≡ (m∸[m∸n]≡n {i} {j} (s≤s⁻¹ j<i*))

            gen : FakeFin i* → Carrier
            gen (j , _) = p j *R q (i ∸ℕ j)

            gen-cong : Congruent _≡_ _≈R_ gen
            gen-cong = from-discrete-cong S gen

            gen-func : SetoidFunction IndexSetoid S
            gen-func = gen which-is-cong gen-cong


    private
        one-is-*-left-id-trace : (p : FormalPolynomial) → (m n' : ℕ) → merge _+R_ zeroR (λ j → one j *R p (m ∸ℕ j)) (sucℕ n') ≈R p m
        one-is-*-left-id-trace p m zeroℕ = begin
            merge _+R_ zeroR gen 1                              ≈⟨ refl ⟩
            merge _+R_ ((one 0 *R p (m ∸ℕ 0)) +R zeroR) gen 0   ≈⟨ refl ⟩
            merge _+R_ ((one 0 *R p m) +R zeroR) gen 0          ≈⟨ refl ⟩
            one 0 *R p m +R zeroR                               ≈⟨ refl ⟩
            oneR *R p m +R zeroR                                ≈⟨ zeroR-is-+R-right-id (oneR *R p m) ⟩
            oneR *R p m                                         ≈⟨ oneR-is-*R-left-id (p m) ⟩
            p m                                                 ∎
                where
                    open import Relation.Binary.Reasoning.Setoid S
                    gen = λ j → one j *R p (m ∸ℕ j)
        one-is-*-left-id-trace p m n'@(sucℕ n'') = begin
            merge _+R_ zeroR gen n                                  ≈⟨ refl ⟩
            merge _+R_ ((one n' *R p (m ∸ℕ n')) +R zeroR) gen n'    ≈⟨ refl ⟩
            merge _+R_ ((zeroR *R p (m ∸ℕ n')) +R zeroR) gen n'     ≈⟨ merge-substitute-start _+R_ +R-cong ((zeroR *R p (m ∸ℕ n')) +R zeroR) (zeroR +R zeroR) (+R-cong (zeroR-is-*R-left-absorber (p (m ∸ℕ sucℕ n''))) (refl {zeroR})) gen n' ⟩
            merge _+R_ (zeroR +R zeroR) gen n'                      ≈⟨ merge-substitute-start _+R_ +R-cong (zeroR +R zeroR) zeroR (zeroR-is-+R-left-id zeroR) gen n' ⟩
            merge _+R_ zeroR gen n'                                 ≈⟨ one-is-*-left-id-trace p m n'' ⟩
            p m                                                     ∎
                where
                    open import Relation.Binary.Reasoning.Setoid S
                    n = sucℕ n'
                    gen = λ j → one j *R p (m ∸ℕ j)

        is-zero⇒left-identity : ∀ {x} → IsZero x → LeftIdentity _≈R_ _+R_ x
        is-zero⇒left-identity {x} x≈0 y = begin
            x +R y      ≈⟨ +R-cong x≈0 refl ⟩
            zeroR +R y  ≈⟨ zeroR-is-+R-left-id y ⟩
            y           ∎
            where open import Relation.Binary.Reasoning.Setoid S

    one-is-*-left-id : LeftIdentity _≈_ _*_ one
    one-is-*-left-id p n = one-is-*-left-id-trace p n n

    *-assoc : Associative _≈_ _*_
    *-assoc p q r i = sym (begin
        (p * (q * r)) i                                                                                         ≈⟨ refl ⟩
        merge _+R_ zeroR (λ j → (p j *R merge _+R_ zeroR (λ k → (q k *R r (i ∸ℕ j ∸ℕ k))) (sucℕ (i ∸ℕ j)))) i*  ≈⟨ merge-local-substitute-generate _+R_ +R-cong zeroR _ _ i* (λ j j<i* → begin
            p j *R merge _+R_ zeroR (λ k → q k *R r (i ∸ℕ j ∸ℕ k)) (sucℕ (i ∸ℕ j))                      ≈⟨ merge-distribute-theorem +R-op (p j *R_) (*R-+R-distributive .proj₁ (p j)) zeroR (λ k → (q k *R r (i ∸ℕ j ∸ℕ k))) (sucℕ (i ∸ℕ j)) ⟩
            merge _+R_ (p j *R zeroR) (_*R_ (p j) ∘ (λ k → q k *R r (i ∸ℕ j ∸ℕ k))) (sucℕ (i ∸ℕ j))     ≈⟨ refl ⟩
            merge _+R_ (p j *R zeroR) (λ k → p j *R (q k *R r (i ∸ℕ j ∸ℕ k))) (sucℕ (i ∸ℕ j))           ≈⟨ merge-substitute-start _+R_ +R-cong (p j *R zeroR) zeroR (zeroR-is-*R-right-absorber (p j)) (λ k → p j *R (q k *R r (i ∸ℕ j ∸ℕ k))) (sucℕ (i ∸ℕ j)) ⟩
            merge _+R_ zeroR (λ k → p j *R (q k *R r (i ∸ℕ j ∸ℕ k))) (sucℕ (i ∸ℕ j))                    ≈⟨ merge-substitute-generate _+R_ +R-cong zeroR (λ k → p j *R (q k *R r (i ∸ℕ j ∸ℕ k))) (λ k → p j *R q k *R r (i ∸ℕ j ∸ℕ k)) (λ k → sym (*R-assoc (p j) (q k) (r (i ∸ℕ j ∸ℕ k)))) (sucℕ (i ∸ℕ j)) ⟩
            merge _+R_ zeroR (λ k → p j *R q k *R r (i ∸ℕ j ∸ℕ k)) (sucℕ (i ∸ℕ j))                      ≈⟨ merge-local-substitute-generate _+R_ +R-cong zeroR (λ k → p j *R q k *R r (i ∸ℕ j ∸ℕ k)) (gen' j) (sucℕ (i ∸ℕ j)) (λ k k<s[i∸j] → reflexive (≡-sym (if-force-true (F j k) (p j *R q k *R r (i ∸ℕ j ∸ℕ k)) zeroR (≤⇒≤ᵇ {j +ℕ k} {i} (≤-trans (≤-reflexive (+ℕ-comm j k)) (m≤o∸n⇒m+n≤o k {j} {i} (s≤s⁻¹ j<i*) (s≤s⁻¹ k<s[i∸j]))))))) ⟩
            merge _+R_ zeroR (λ k → gen' j k) (sucℕ (i ∸ℕ j))                                           ∎
            ) ⟩
        merge _+R_ zeroR (λ j → (merge _+R_ zeroR (λ k → gen' j k) (sucℕ (i ∸ℕ j)))) i*                         ≈⟨ merge-merge S +R-op +R-assoc {zeroR} +R-identity gen' i* (λ j → sucℕ (i ∸ℕ j)) i* (λ j _ → s≤s (m∸n≤m i j)) identity-thing₁ ⟩
        merge _+R_ zeroR (λ j → gen' (j /ℕ i*) (j %ℕ i*)) (i* *ℕ i*)                                            ≈⟨ merge-local-substitute-generate _+R_ +R-cong zeroR _ _ (i* *ℕ i*) (λ j j<i*² → thing₃ j j<i*²) ⟩
        merge _+R_ zeroR (gen ∘ unbind' zeroVec f-func) (i* *ℕ i*)                                              ≈⟨ reindex' S +R-op gen-func +R-assoc +R-comm (i* *ℕ i*) (unbind' zeroVec f-func) f-bind shuffle-func shuffle-bijective zeroR ⟩
        merge _+R_ zeroR (gen ∘ shuffle-func ∘ unbind' zeroVec f-func) (i* *ℕ i*)                               ≈⟨ merge-local-substitute-generate _+R_ +R-cong zeroR _ _ (i* *ℕ i*) (λ j j<i*² → thing₄ j j<i*²) ⟩
        merge _+R_ zeroR (λ j → gen' (j %ℕ i*) ((j /ℕ i*) -mod (j %ℕ i*))) (i* *ℕ i*)                           ≈⟨ sym (merge-merge S +R-op +R-assoc {zeroR} +R-identity (λ j k → gen' k (j -mod k)) i* sucℕ i* (λ j j<si → ≤-recompute j<si) identity-thing₂) ⟩
        merge _+R_ zeroR (λ j → merge _+R_ zeroR (λ k → gen' k (j -mod k)) (sucℕ j)) i*                         ≈⟨ merge-local-substitute-generate _+R_ +R-cong zeroR _ _ i* (λ j j<i* → begin
            merge _+R_ zeroR (λ k → gen' k (j -mod k)) (sucℕ j)                                 ≈⟨ merge-local-substitute-generate _+R_ +R-cong zeroR _ _ (sucℕ j) (λ k k<sj → begin
                gen' k (j -mod k)                               ≈⟨ reflexive (≡-cong (gen' k) (-mod-is-∸ j k (s≤s⁻¹ k<sj) j<i*)) ⟩
                gen' k (j ∸ℕ k)                                 ≈⟨ reflexive (if-force-true (F k (j ∸ℕ k)) (p k *R q (j ∸ℕ k) *R r (i ∸ℕ k ∸ℕ (j ∸ℕ k))) zeroR (≤⇒≤ᵇ {k +ℕ (j ∸ℕ k)} {i} (≤-trans (≤-reflexive (m+[n∸m]≡n {k} {j} (s≤s⁻¹ k<sj))) (s≤s⁻¹ j<i*)))) ⟩
                p k *R q (j ∸ℕ k) *R r (i ∸ℕ k ∸ℕ (j ∸ℕ k))     ≈⟨ reflexive (≡-cong (λ o → p k *R q (j ∸ℕ k) *R r o) ([n∸m]∸[o∸m]=n∸o k i j (s≤s⁻¹ k<sj))) ⟩
                p k *R q (j ∸ℕ k) *R r (i ∸ℕ j)                 ∎) ⟩
            merge _+R_ zeroR (λ k → p k *R q (j ∸ℕ k) *R r (i ∸ℕ j)) (sucℕ j)                   ≈⟨ merge-substitute-start _+R_ +R-cong zeroR (zeroR *R r (i ∸ℕ j)) (sym (zeroR-is-*R-left-absorber (r (i ∸ℕ j)))) (λ k → p k *R q (j ∸ℕ k) *R r (i ∸ℕ j)) (sucℕ j) ⟩
            merge _+R_ (zeroR *R r (i ∸ℕ j)) (λ k → p k *R q (j ∸ℕ k) *R r (i ∸ℕ j)) (sucℕ j)   ≈⟨ sym (merge-distribute-theorem +R-op (_*R r (i ∸ℕ j)) (*R-+R-distributive .proj₂ (r (i ∸ℕ j))) zeroR (λ k → p k *R q (j ∸ℕ k)) (sucℕ j)) ⟩
            merge _+R_ zeroR (λ k → p k *R q (j ∸ℕ k)) (sucℕ j) *R r (i ∸ℕ j)                   ∎) ⟩
        merge _+R_ zeroR (λ j → merge _+R_ zeroR (λ k → (p k *R q (j ∸ℕ k))) (sucℕ j) *R r (i ∸ℕ j)) i*         ≈⟨ refl ⟩
        ((p * q) * r) i                                                                                         ∎)
        where
            i* = sucℕ i

            open Cube 2 i* using (basesVec; basesVec-IsNonZero; basesVec-HasOneTail; all-index-vectors-lesser)
            open import Plasmaduck.Number.NatModSetoid i* using (NatModSetoid; _≃_; m%mod≃m; m+n-m≃n; +-minus-assoc; minus-wrap₂; minus-is-∸) renaming (
                _-_ to _∸mod_;
                +-cong to +-cong-≃;
                minus-cong to ∸mod-cong-≃
                )

            _-mod_ : ℕ → ℕ → ℕ
            _-mod_ m n = (m ∸mod n) %ℕ i*

            -mod-is-∸ : (j k : ℕ) → .(j ≥ k) → (j < i*) → j -mod k ≡ j ∸ℕ k
            -mod-is-∸ j k j≥k j<i* =
                j -mod k        ≡⟨ minus-is-∸ j≥k ⟩
                (j ∸ℕ k) %ℕ i*  ≡⟨ m<n⇒m%n≡m {i*} {j ∸ℕ k} (≤-<-trans (m∸n≤m j k) j<i*) ⟩
                j ∸ℕ k          ∎
                where open ≡-Reasoning

            F : ℕ → ℕ → Bool
            F m n = m +ℕ n ≤ᵇ i

            Index = LesserInfiniteVector basesVec
            IndexSetoid = LesserInfiniteVectorSetoid basesVec

            zeroVec : Index
            zeroVec = (λ _ → 0) , (λ {
                zeroℕ → s≤s z≤n
              ; (sucℕ zeroℕ) → s≤s z≤n
              ; (sucℕ (sucℕ i)) → s≤s z≤n })

            open Reindex IndexSetoid using (BijectiveBinding; reindex'; bind'; unbind; unbind'; bind'-unbind'; unbind'-force<)

            gen' : ℕ → ℕ → Carrier
            gen' m n = if (F m n) then (p m *R q n *R r (i ∸ℕ m ∸ℕ n)) else zeroR

            identity-thing₁ : (j k : ℕ) → .(j < i*) → .(sucℕ (i ∸ℕ j) ≤ k) → .(k < i*) → LeftIdentity _≈R_ _+R_ (gen' j k)
            identity-thing₁ j k j<i* i∸j<k k<i* = is-zero⇒left-identity (reflexive (if-force-false (j +ℕ k ≤ᵇ i) (p j *R q k *R r (i ∸ℕ j ∸ℕ k)) zeroR λ j+k≤ᵇi → ⊥-recompute (<-irrefl ≡-refl (<-≤-trans (≤-trans (m∸n≤o⇒m≤o+n i* j k (≤-trans (≤-reflexive (≡-sym (∸-suc i j (s≤s⁻¹ j<i*)))) i∸j<k)) (≤-reflexive (+ℕ-comm k j))) (≤ᵇ⇒≤ (j +ℕ k) i j+k≤ᵇi)))))

            identity-thing₂ : (j k : ℕ) → .(j < i*) → .(sucℕ j ≤ k) → .(k < i*) → LeftIdentity _≈R_ _+R_ (gen' k (j -mod k))
            identity-thing₂ j k j<i* j<k k<i* = is-zero⇒left-identity (reflexive (if-force-false (k +ℕ (j -mod k) ≤ᵇ i) (p k *R q (j -mod k) *R r (i ∸ℕ k ∸ℕ (j -mod k))) zeroR λ k+[j∸k]≤ᵇi → ⊥-recompute (<-irrefl ≡-refl (<-≤-trans thing (≤ᵇ⇒≤ (k +ℕ (j -mod k)) i k+[j∸k]≤ᵇi)))))
                where
                    thing : k +ℕ (j -mod k) > i
                    thing = begin
                        sucℕ i                  ≤⟨ minus-wrap₂ j k j<k (≤-recompute k<i*) ⟩
                        k +ℕ (j ∸mod k) %ℕ i*   ≡⟨⟩
                        k +ℕ (j -mod k)         ∎
                        where open ≤-Reasoning

            gen : Index → Carrier
            gen (I , _) = gen' (I 0) (I 1)

            gen-cong : Congruent (Setoid._≈_ IndexSetoid) (Setoid._≈_ S) gen
            gen-cong {(u , u≺bases)} {v , v≺bases} u≈v = reflexive (≡-cong₂ gen' {u 0} {v 0} {u 1} {v 1} (u≈v 0) (u≈v 1))

            gen-func : SetoidFunction IndexSetoid S
            gen-func = gen which-is-cong λ {x} {y} → gen-cong {x} {y}

            f : ℕ → InfiniteVector
            f j 0 = j /ℕ i*
            f j 1 = j %ℕ i*
            f j _ = 0

            f-inv : InfiniteVector → ℕ
            f-inv u = u 1 +ℕ u 0 *ℕ i*

            f-inv< : ∀ u → u ≺ basesVec → f-inv u < i* *ℕ i*
            f-inv< u u≺bases = begin
                sucℕ (u 1 +ℕ u 0 *ℕ i*)     ≤⟨ +-mono-≤ {sucℕ (u 1)} {i*} {u 0 *ℕ i*} {i *ℕ i*} (u≺bases 1) (*-mono-≤ {u 0} {i} {i*} (s≤s⁻¹ (u≺bases 0)) ≤-refl) ⟩
                sucℕ (i +ℕ i *ℕ i*)         ≡⟨⟩
                i* *ℕ i*                    ∎
                where open ≤-Reasoning

            f-func : FakeFin (i* *ℕ i*) → Index
            f-func (j , squash j<i**i*) = f j , λ {
                0 → m<n*o⇒m/o<n {j} {i*} {i*} (≤-recompute j<i**i*);
                1 → m%n<n j i*;
                (sucℕ (sucℕ _)) → s≤s z≤n}

            thing₃ : ∀ j → .(j < i* *ℕ i*) → gen' (j /ℕ i*) (j %ℕ i*) ≈R gen (unbind' zeroVec f-func j)
            thing₃ j j<i*² = begin
                gen' (j /ℕ i*) (j %ℕ i*)            ≈⟨ refl ⟩
                gen (f-func (j , squash j<i*²))     ≈⟨ reflexive (≡-cong gen (≡-sym (unbind'-force< zeroVec f-func (j , squash j<i*²)))) ⟩
                gen (unbind' zeroVec f-func j)      ∎
                where open import Relation.Binary.Reasoning.Setoid S

            f-inv-func : Index → FakeFin (i* *ℕ i*)
            f-inv-func (u , u≺bases) = f-inv u , squash (f-inv< u u≺bases)

            f-finv : ∀ u → u ≺ basesVec → (f ∘ f-inv) u ≗ u
            f-finv u u≺bases 0 =
                (f ∘ f-inv) u 0             ≡⟨⟩
                (u 1 +ℕ u 0 *ℕ i*) /ℕ i*    ≡⟨ [m+kn]/n≡k+m/n (u 1) (u 0) i* ⟩
                u 0 +ℕ u 1 /ℕ i*            ≡⟨ ≡-cong (u 0 +ℕ_) (m<n⇒m/n≡0 {u 1} {i*} (u≺bases 1)) ⟩
                u 0 +ℕ 0                    ≡⟨ +ℕ-comm (u 0) 0 ⟩
                u 0                         ∎
                where open ≡-Reasoning
            f-finv u u≺bases 1 =
                (f ∘ f-inv) u 1             ≡⟨⟩
                (u 1 +ℕ u 0 *ℕ i*) %ℕ i*    ≡⟨ [m+kn]%n≡m%n (u 1) (u 0) i* ⟩
                u 1 %ℕ i*                   ≡⟨ m<n⇒m%n≡m {i*} {u 1} (u≺bases 1) ⟩
                u 1                         ∎
                where open ≡-Reasoning
            f-finv u u≺bases n@(sucℕ (sucℕ n'')) = ≤-antisym z≤n (s≤s⁻¹ (u≺bases n))
                where open ≡-Reasoning

            finv-f : ∀ m → (f-inv ∘ f) m ≡ m
            finv-f m = ≡-sym (m≡m%n+[m/n]*n m i*)

            f-bind : BijectiveBinding (i* *ℕ i*) (unbind' zeroVec f-func)
            f-bind = both-inv→bijective (discrete-setoid (FakeFin (i* *ℕ i*))) IndexSetoid (bind' (i* *ℕ i*) (unbind' zeroVec f-func) which-is-cong from-discrete-cong IndexSetoid (bind' (i* *ℕ i*) (unbind' zeroVec f-func))) ((f-inv-func which-is-cong λ {x@(u , _)} {y@(v , _)} u~v → squash-≡ (≡-cong₂ _+ℕ_ (u~v 1) (≡-cong (_*ℕ i*) (u~v 0)))) , (λ x@(j , j<i*²) →
                f-inv-func (unbind' zeroVec f-func j)   ≡⟨ ≡-cong f-inv-func (unbind'-force< zeroVec f-func x) ⟩
                f-inv-func (f-func x)                   ≡⟨ squash-≡ (finv-f j) ⟩
                x ∎
                    ) , (λ x@(u , u≺bases) i →
                (unbind' zeroVec f-func (f-inv u)) .proj₁ i     ≡⟨ ≡-cong (λ q → q .proj₁ i) (unbind'-force< zeroVec f-func (f-inv-func x)) ⟩
                f-func (f-inv-func x) .proj₁ i                  ≡⟨ f-finv u u≺bases i ⟩
                u i                                             ∎))
                where open ≡-Reasoning

            _~_ = IndexSetoid .Setoid._≈_

            shuffle : InfiniteVector → InfiniteVector
            shuffle u 0 = u 1
            shuffle u 1 = u 0 -mod u 1
            shuffle u _ = 0

            shuffle≺ : (u : InfiniteVector) → u ≺ basesVec → shuffle u ≺ basesVec
            shuffle≺ u u≺bases 0 = u≺bases 1
            shuffle≺ u u≺bases 1 = m%n<n (u 0 ∸mod u 1) i*
            shuffle≺ u u≺bases (sucℕ (sucℕ _)) = s≤s z≤n

            shuffle-func : Index → Index
            shuffle-func (u , u≺bases) = shuffle u , shuffle≺ u u≺bases

            thing₄ : (j : ℕ) → .(j < i* *ℕ i*) → gen (shuffle-func (unbind' zeroVec f-func j)) ≈R gen' (j %ℕ i*) ((j /ℕ i*) -mod (j %ℕ i*))
            thing₄ j j<i*² = begin
                gen (shuffle-func (unbind' zeroVec f-func j))   ≈⟨ reflexive (≡-cong (gen ∘ shuffle-func) (unbind'-force< zeroVec f-func (j , squash j<i*²))) ⟩
                gen (shuffle-func (f-func (j , squash j<i*²)))  ≈⟨ refl ⟩
                gen' (j %ℕ i*) ((j /ℕ i*) -mod (j %ℕ i*))       ∎
                where open import Relation.Binary.Reasoning.Setoid S

            shuffle-func-cong : Congruent _~_ _~_ shuffle-func
            shuffle-func-cong x~y (sucℕ (sucℕ _)) = ≡-refl
            shuffle-func-cong x~y 0 = x~y 1
            shuffle-func-cong {x@(u , u≺bases)} {y@(v , v≺bases)} x~y 1 =
                shuffle u 1     ≡⟨⟩
                u 0 -mod u 1    ≡⟨ ≡-cong₂ _-mod_ (x~y 0) (x~y 1) ⟩
                v 0 -mod v 1    ≡⟨⟩
                shuffle v 1     ∎
                where open ≡-Reasoning

            shuffle-inv : InfiniteVector → InfiniteVector
            shuffle-inv u 0 = (u 0 +ℕ u 1) %ℕ i*
            shuffle-inv u 1 = u 0
            shuffle-inv u _ = 0

            shuffle-left-inv : (u : InfiniteVector) → u ≺ basesVec → shuffle-inv (shuffle u) ≗ u
            shuffle-left-inv u u≺bases n@(sucℕ (sucℕ _)) = ≡-sym (n<1⇒n≡0 (u≺bases n))
            shuffle-left-inv u u≺bases 1 = ≡-refl
            shuffle-left-inv u u≺bases 0 =
                shuffle-inv (shuffle u) 0               ≡⟨⟩
                (shuffle u 0 +ℕ shuffle u 1) %ℕ i*      ≡⟨⟩
                (u 1 +ℕ (u 0 -mod u 1)) %ℕ i*           ≡⟨⟩
                (u 1 +ℕ (u 0 ∸mod u 1) %ℕ i*) %ℕ i*     ≡⟨ thing ⟩
                u 0 %ℕ i*                               ≡⟨ m<n⇒m%n≡m {i*} {u 0} (u≺bases 0) ⟩
                u 0                                     ∎
                where
                    thing : u 1 +ℕ (u 0 ∸mod u 1) %ℕ i* ≃ u 0
                    thing = begin
                        u 1 +ℕ (u 0 ∸mod u 1) %ℕ i*     ≈⟨ +-cong-≃ {u 1} {u 1} {(u 0 ∸mod u 1) %ℕ i*} {u 0 ∸mod u 1} ≡-refl (m%mod≃m (u 0 ∸mod u 1)) ⟩
                        u 1 +ℕ (u 0 ∸mod u 1)           ≈⟨ ≡-sym (+-minus-assoc (u 1) (u 0) (u 1)) ⟩
                        u 1 +ℕ u 0 ∸mod u 1             ≈⟨ m+n-m≃n (u 1) (u 0) ⟩
                        u 0                             ∎
                        where open import Relation.Binary.Reasoning.Setoid NatModSetoid
                    open ≡-Reasoning

            shuffle-right-inv : (u : InfiniteVector) → u ≺ basesVec → shuffle (shuffle-inv u) ≗ u
            shuffle-right-inv u u≺bases n@(sucℕ (sucℕ _)) = ≡-sym (n<1⇒n≡0 (u≺bases n))
            shuffle-right-inv u u≺bases 0 = ≡-refl
            shuffle-right-inv u u≺bases 1 =
                shuffle (shuffle-inv u) 1               ≡⟨⟩
                shuffle-inv u 0 -mod shuffle-inv u 1    ≡⟨⟩
                ((u 0 +ℕ u 1) %ℕ i*) -mod u 0           ≡⟨ thing ⟩
                u 1 %ℕ i*                               ≡⟨ m<n⇒m%n≡m (u≺bases 1) ⟩
                u 1                                     ∎
                where
                    thing : ((u 0 +ℕ u 1) %ℕ i*) ∸mod u 0 ≃ u 1
                    thing = begin
                        ((u 0 +ℕ u 1) %ℕ i*) ∸mod u 0   ≈⟨ ∸mod-cong-≃ {(u 0 +ℕ u 1) %ℕ i*} {u 0 +ℕ u 1} {u 0} {u 0} (m%mod≃m (u 0 +ℕ u 1)) ≡-refl ⟩
                        (u 0 +ℕ u 1) ∸mod u 0           ≈⟨ m+n-m≃n (u 0) (u 1) ⟩
                        u 1                             ∎
                        where open import Relation.Binary.Reasoning.Setoid NatModSetoid
                    open ≡-Reasoning

            shuffle-inv≺ : (u : InfiniteVector) → u ≺ basesVec → shuffle-inv u ≺ basesVec
            shuffle-inv≺ u u≺bases 0 = m%n<n (u 0 +ℕ u 1) i*
            shuffle-inv≺ u u≺bases 1 = u≺bases 0
            shuffle-inv≺ u u≺bases (sucℕ (sucℕ _)) = s≤s z≤n

            shuffle-inv-func : Index → Index
            shuffle-inv-func (u , u≺bases) = shuffle-inv u , shuffle-inv≺ u u≺bases

            shuffle-inv-func-cong : Congruent _~_ _~_ shuffle-inv-func
            shuffle-inv-func-cong x~y (sucℕ (sucℕ _)) = ≡-refl
            shuffle-inv-func-cong x~y 1 = x~y 0
            shuffle-inv-func-cong {x@(u , u≺bases)} {y@(v , v≺bases)} x~y 0 =
                shuffle-inv u 0     ≡⟨⟩
                (u 0 +ℕ u 1) %ℕ i*  ≡⟨ %-congˡ {i*} (≡-cong₂ _+ℕ_ (x~y 0) (x~y 1)) ⟩
                (v 0 +ℕ v 1) %ℕ i*  ≡⟨⟩
                shuffle-inv v 0     ∎
                where open ≡-Reasoning

            shuffle-bijective : Bijective (IndexSetoid .Setoid._≈_) (IndexSetoid .Setoid._≈_) shuffle-func
            shuffle-bijective = both-inv→bijective IndexSetoid IndexSetoid (shuffle-func which-is-cong λ {x} {y} → shuffle-func-cong {x} {y}) ((shuffle-inv-func which-is-cong λ {x} {y} → shuffle-inv-func-cong {x} {y}) , (λ x@(u , u≺bases) i →
                shuffle-inv (shuffle u) i   ≡⟨ shuffle-left-inv u u≺bases i ⟩
                u i                         ∎
                    ) , (λ x@(u , u≺bases) i →
                shuffle (shuffle-inv u) i   ≡⟨ shuffle-right-inv u u≺bases i ⟩
                u i                         ∎))
                where open ≡-Reasoning

            g : ℕ → InfiniteVector
            g = shuffle ∘ f

            open import Relation.Binary.Reasoning.Setoid S

    *-+-left-distributive : _DistributesOverˡ_ _≈_ _*_ _+_
    *-+-left-distributive p q r i = begin
        (p * (q + r)) i                                                                                                     ≈⟨ refl ⟩
        merge _+R_ zeroR (λ j → (p j *R (q (i ∸ℕ j) +R r (i ∸ℕ j)))) (sucℕ i)                                               ≈⟨ merge-substitute-generate _+R_ +R-cong zeroR _ _ (λ j → *R-+R-distributive .proj₁ (p j) (q (i ∸ℕ j)) (r (i ∸ℕ j))) (sucℕ i) ⟩
        merge _+R_ zeroR (λ j → (p j *R q (i ∸ℕ j)) +R (p j *R r (i ∸ℕ j))) (sucℕ i)                                        ≈⟨ sym (merge-zipper-lemma +R-op +R-assoc +R-comm +R-identity (λ j → (p j *R q (i ∸ℕ j))) (λ j → (p j *R r (i ∸ℕ j))) (sucℕ i)) ⟩
        (merge _+R_ zeroR (λ j → (p j *R q (i ∸ℕ j))) (sucℕ i)) +R (merge _+R_ zeroR (λ j → (p j *R r (i ∸ℕ j))) (sucℕ i))  ≈⟨ refl ⟩
        ((p * q) + (p * r)) i                                                                                               ∎
        where
            open import Relation.Binary.Reasoning.Setoid S

module FormalPolynomial (ring : Ring c ℓ) where
    open Ring ring using (IsZero; IsNonzero; Carrier; S) renaming (
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

    open MergeSubstitute S using (merge-local-substitute-generate; merge-substitute-generate; merge-substitute; merge-substitute-start; merge-substitute-op)
    open MergeOnSetoid S using (merge-pop-last; merge-distribute-theorem; merge-zipper-lemma)

    module Flip where
        open LeftFormalPolynomialLemmas (opposite-ring ring) using (*-+-left-distributive; one-is-*-left-id)
        open RawFormalPolynomial (opposite-ring ring .Ring.rawRing) using () renaming (one to one-flip; _*_ to _*-flip_; _*-alt_ to _*-alt-flip_; _+_ to _+-flip_)
        open LeftFormalPolynomialLemmas ring using () renaming (*-flip to *-flip-to-alt)
        open RawFormalPolynomial (ring .Ring.rawRing) using (FormalPolynomial; FormalPolynomialSetoid; _≈_; _+_; _∸_; _*_; _*-alt_; zero; one; one-force-nonZero; +-cong; ∸-cong; negate-cong; *-cong; ≈-refl)

        +-is-flip-+-flipped : ∀ p q → p + q ≈ q +-flip p
        +-is-flip-+-flipped p q i = refl

        *-is-flip-*-flipped : ∀ p q → p * q ≈ q *-flip p
        *-is-flip-*-flipped p q i = begin
            (p * q) i                                                               ≈⟨ *-flip-to-alt p q i ⟩
            (p *-alt q) i                                                           ≈⟨ refl ⟩
            merge _+R_ zeroR (λ j → p (i ∸ℕ j) *R q j) (sucℕ i)                     ≈⟨ merge-substitute-op _+R_ (Function.flip _+R_) (λ {w} {x} {y} {z} w≈x y≈z → begin
                w +R y  ≈⟨ +R-cong w≈x y≈z ⟩
                x +R z  ≈⟨ +R-comm x z ⟩
                z +R x  ∎
                ) zeroR (λ j → p (i ∸ℕ j) *R q j) (sucℕ i) ⟩
            merge (Function.flip _+R_) zeroR (λ j → p (i ∸ℕ j) *R q j) (sucℕ i)     ≈⟨ refl ⟩
            (q *-flip p) i                                                          ∎
            where open import Relation.Binary.Reasoning.Setoid S

        one-is-flip-one-flipped : one ≈ one-flip
        one-is-flip-one-flipped zeroℕ = refl
        one-is-flip-one-flipped (sucℕ _) = refl

        one-is-*-right-id : RightIdentity _≈_ _*_ one
        one-is-*-right-id p n = begin
            (p * one) n             ≈⟨ refl ⟩
            (p * one) n             ≈⟨ *-cong {p} ≈-refl one-is-flip-one-flipped n ⟩
            (p * one-flip) n        ≈⟨ *-is-flip-*-flipped p one-flip n ⟩
            (one-flip *-flip p) n   ≈⟨ one-is-*-left-id p n ⟩
            p n                     ∎
            where open import Relation.Binary.Reasoning.Setoid S

        *-+-right-distributive : _DistributesOverʳ_ _≈_ _*_ _+_
        *-+-right-distributive p q r i = begin
            ((q + r) * p) i                     ≈⟨ *-is-flip-*-flipped (q + r) p i ⟩
            (p *-flip (r +-flip q)) i           ≈⟨ *-+-left-distributive p r q i ⟩
            (p *-flip r +-flip p *-flip q) i    ≈⟨ sym (+R-cong (*-is-flip-*-flipped q p i) (*-is-flip-*-flipped r p i)) ⟩
            (q * p + r * p) i                   ∎
            where open import Relation.Binary.Reasoning.Setoid S

    open Flip using (one-is-*-right-id; *-+-right-distributive) public
    open LeftFormalPolynomialLemmas ring public
    open RawFormalPolynomial (ring .Ring.rawRing) public

    FormalPolynomialRawRing : RawRing c ℓ
    FormalPolynomialRawRing = record {
        S = FormalPolynomialSetoid;
        +-op = +-op;
        +-inverse = negate-op;
        zero = zero;
        *-op = *-op;
        one = one
        }

    *-distrib-+ : _DistributesOver_ _≈_ _*_ _+_
    *-distrib-+ = *-+-left-distributive , *-+-right-distributive

    *-identity : Identity _≈_ _*_ one
    *-identity = one-is-*-left-id , one-is-*-right-id

    FormalPolynomialIsRing : IsRing FormalPolynomialRawRing
    FormalPolynomialIsRing = record {
        +-isAbelianGroup = record {
            isGroup = record {
                id-is-left-id = λ x n → zeroR-is-+R-left-id (x n);
                inv-is-left-inv = λ x n → Ring.neg-is-+-left-inv ring (x n);
                assoc = λ x y z n → Ring.+-assoc ring (x n) (y n) (z n)
                };
            abelian = λ x y n → Ring.+-comm ring (x n) (y n)
            };
        one-is-*-id = *-identity;
        *-assoc = *-assoc;
        *-+-distributive = *-distrib-+
        }

    FormalPolynomialRing : Ring c ℓ
    FormalPolynomialRing = record {
        rawRing = FormalPolynomialRawRing;
        isRing = FormalPolynomialIsRing
        }


module CommutativeFormalPolynomial (ring : CommutativeRing c ℓ) where
    open CommutativeRing ring using (IsZero; IsNonzero; Carrier; S) renaming (
        zero to zeroR; one to oneR; _≈_ to _≈R_; _+_ to _+R_; -_ to -R_; _*_ to _*R_;
        +-op to +R-op;
        +-cong to +R-cong;
        +-assoc to +R-assoc;
        +-comm to +R-comm;
        +-identity to +R-identity;
        neg-cong to negR-cong;
        *-cong to *R-cong;
        *-assoc to *R-assoc;
        *-comm to *R-comm;
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

    open MergeSubstitute S using (merge-local-substitute-generate; merge-substitute-generate; merge-substitute; merge-substitute-start; merge-substitute-op)
    open MergeOnSetoid S using (merge-pop-last; merge-distribute-theorem; merge-zipper-lemma)

    open FormalPolynomial (CommutativeRing.ring ring) public


    *-comm : Commutative _≈_ _*_
    *-comm p q i = begin
        (p * q) i                                           ≈⟨ *-flip p q i ⟩
        (p *-alt q) i                                       ≈⟨ refl ⟩
        merge _+R_ zeroR (λ j → (p (i ∸ℕ j) *R q j)) i*     ≈⟨ merge-substitute-generate _+R_ +R-cong zeroR _ _ (λ j → *R-comm (p (i ∸ℕ j)) (q j)) i* ⟩
        merge _+R_ zeroR (λ j → (q j *R p (i ∸ℕ j))) i*     ≈⟨ refl ⟩
        (q * p) i                                           ∎
        where
            i* = sucℕ i
            open import Relation.Binary.Reasoning.Setoid S

    FormalPolynomialIsCommutativeRing : IsCommutativeRing FormalPolynomialRawRing
    FormalPolynomialIsCommutativeRing = record {
        +-isAbelianGroup = IsRing.+-isAbelianGroup FormalPolynomialIsRing;
        one-is-*-left-id = one-is-*-left-id;
        *-assoc = *-assoc;
        *-+-left-distributive = *-+-left-distributive;
        *-comm = *-comm
        }

    FormalPolynomialCommutativeRing : CommutativeRing c ℓ
    FormalPolynomialCommutativeRing = record {
        rawRing = FormalPolynomialRawRing;
        isCommutativeRing = FormalPolynomialIsCommutativeRing
        }
