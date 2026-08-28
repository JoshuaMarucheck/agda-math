open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_) renaming (cong to ≡-cong; refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Relation.Binary using (Setoid; Rel; Decidable; IsEquivalence; Reflexive; Transitive)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Function using (Congruent)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (ℕ; _<_; _>_; _≤_; _≥_; _<?_; _≤?_; s≤s; <-cmp) renaming (zero to zeroℕ; suc to sucℕ; _+_ to _+ℕ_; _*_ to _*ℕ_; _∸_ to _∸ℕ_)
open import Data.Nat.Properties using (≤-refl; ≤-reflexive; ≤-trans; m≤n⇒m≤n+o; ∸-+-assoc; +-∸-assoc; ≰⇒>; ∸-monoˡ-≤; ≤-irrelevant) renaming (+-identity to +ℕ-identity; +-comm to +ℕ-comm)
open import Relation.Binary.Reasoning.Syntax using (module ≤-syntax; module end-syntax)

open import Plasmaduck.Data.Nat using (≤-recompute) renaming (max to maxℕ; max≥fst to maxℕ≥fst; max≥snd to maxℕ≥snd)
open import Plasmaduck.Fold.BoundedNat.Foldl using () renaming (fold to foldℕ; fold-carrying-theorem to foldℕ-carrying-theorem)
open import Plasmaduck.Algebra.Ring.Defs using (Ring; RawRing; IsRing; IsCommutativeRing; CommutativeRing)
open import Plasmaduck.SetoidExperiment.SetoidMachinery using (SetoidFunction₂; _which-is-cong₂_; _←₂_; SetoidFunction; _←_; property-subset-setoid)
open import Plasmaduck.Algebra.Group.Defs using (RawGroup; IsGroup; IsAbelianGroup; Group)
open import Plasmaduck.Function.Properties using (Associative; Commutative; Identity; Distributive; LeftAbsorber; RightAbsorber; Absorber; Congruent₂)
open import Plasmaduck.Relation.Defs using (CongruentRel)
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
module Plasmaduck.Algebra.Ring.PolynomialRing where

variable
    c ℓ : Level


module RawPolynomial (ring : Ring c ℓ) where
    open Ring ring using (IsZero; IsNonzero; Carrier; S; neg-cong; zero-is-*-absorber; zero-is-*-strong-absorber; zero-is-+-left-id; neg-zero-is-zero) renaming (zero to zeroR; one to oneR; _≈_ to _≈R_; _+_ to _+R_; -_ to -R_; _*_ to _*R_; +-cong to +R-cong)
    open import Relation.Binary.Reasoning.Setoid S
    open IsEquivalence (S .Setoid.isEquivalence)

    FormalPolynomial : Set c
    FormalPolynomial = ℕ → Carrier

    HasDegree≤ : FormalPolynomial → ℕ → Set ℓ
    HasDegree≤ p n = ∀ {m} → .(n ≤ m) → IsZero (p m)

    HasDegree : FormalPolynomial → ℕ → Set ℓ
    HasDegree p n = IsNonzero (p n) × HasDegree≤ p n

    _≈_ : Rel FormalPolynomial ℓ
    p ≈ q = ∀ n → p n ≈R q n

    ≈-eq : IsEquivalence _≈_
    ≈-eq = record {
        refl = λ {x} n → refl;
        sym = λ {x} {y} z n → sym (z n);
        trans = λ {i} {j} {k} z z₁ n → trans (z n) (z₁ n)
        }

    FormalPolynomialSetoid : Setoid c ℓ
    FormalPolynomialSetoid = record { isEquivalence = ≈-eq }

    _+_ : FormalPolynomial → FormalPolynomial → FormalPolynomial
    _+_ p q o = p o +R q o

    -_ : FormalPolynomial → FormalPolynomial
    -_ p i = -R (p i)

    _*_ : FormalPolynomial → FormalPolynomial → FormalPolynomial
    _*_ p q i = foldℕ (sucℕ i) (λ s j _ → s +R (p j *R q (i ∸ℕ j))) zeroR

    zero : FormalPolynomial
    zero _ = zeroR

    one : FormalPolynomial
    one zeroℕ = oneR
    one (sucℕ _) = zeroR

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
    --     module _ (p : FormalPolynomial) where
    --         P : ℕ → Set ℓ
    --         P i = ∀ j → i ≤ j → p j ≈R zeroR

    -- module _ (≈R-dec : Decidable _≈R_) where
    --     {-
    --         If equality is decidable then:
    --         - there is a function determining degree
    --         - polynomial equality is decidable
    --         note that if you can tell the difference between two specific elements, then you can tell the difference between any two elements, I think.
    --     -}

    --     module _ (p : FormalPolynomial) where
    --         open import Plasmaduck.Counting.GeneralizedMinimum (λ i → ∀ j → i ≤ j → p j ≈R zeroR) (λ i → Σ ℕ λ j → ¬ (p j ≈R zeroR)) using ()

    --         deg : FormalPolynomial → ℕ
    --         deg = {!   !}

    --         deg-gets-degree : HasDegree p (deg p)
    --         deg-gets-degree = {!   !}

    --     ≈-dec : Decidable _≈_
    --     ≈-dec = {!   !}


    ------------------------------------
    --- Proving that it forms a ring ---
    ------------------------------------

    +-cong : Congruent₂ _≈_ _≈_ _≈_ _+_
    +-cong p≈ q≈ i = +R-cong (p≈ i) (q≈ i)

    -- +-op : SetoidFunction₂ PolynomialSetoid PolynomialSetoid PolynomialSetoid
    -- +-op = record {
    --     func = _+_;
    --     respects = λ p q i → +R-cong (p i) (q i)
    --     }

    negate-cong : Congruent _≈_ _≈_ -_
    negate-cong = λ p i → neg-cong (p i)

    -- negate-op : SetoidFunction PolynomialSetoid PolynomialSetoid
    -- negate-op = record {
    --     func = -_;
    --     respects = λ p i → neg-cong (p i)
    --     }

    *-cong : Congruent₂ _≈_ _≈_ _≈_ _*_
    *-cong {p₁} {p₂} {q₁} {q₂} p₁≈p₂ q₁≈q₂ i = begin
        foldℕ (sucℕ i) (λ s j _ → s +R (p₁ j *R q₁ (i ∸ℕ j))) zeroR     ≈⟨ {!   !} ⟩
        foldℕ (sucℕ i) (λ s j _ → s +R (p₂ j *R q₂ (i ∸ℕ j))) zeroR     ∎

    -- -- *-op : SetoidFunction₂ PolynomialSetoid PolynomialSetoid PolynomialSetoid
    -- -- *-op = record {
    -- --     func = _*_;
    -- --     respects = {!   !}
    -- --     }




module Polynomial (ring : Ring c ℓ) where
    open Ring ring using (IsZero; IsNonzero; Carrier; S; neg-cong; zero-is-*-absorber; zero-is-*-strong-absorber; zero-is-+-left-id; neg-zero-is-zero) renaming (zero to zeroR; one to oneR; _≈_ to _≈R_; _+_ to _+R_; -_ to -R_; _*_ to _*R_; +-cong to +R-cong)
    open import Relation.Binary.Reasoning.Setoid S
    open IsEquivalence (S .Setoid.isEquivalence)
    open RawPolynomial ring



    record IsBoundedDegree (p : FormalPolynomial) : Set ℓ where
        field
            n : ℕ
            degree≤n : HasDegree≤ p n

    Polynomial : Set (c ⊔ ℓ)
    Polynomial = Σ FormalPolynomial IsBoundedDegree

    get : (p : Polynomial) → ℕ → Carrier
    get p = p .proj₁

    -- _≈_ : Rel Polynomial ℓ
    -- p ≈ q = ∀ n → get p n ≈R get q n

    -- ≈-eq : IsEquivalence _≈_
    -- ≈-eq = record {
    --     refl = λ {x} n → refl;
    --     sym = λ {x} {y} z n → sym (z n);
    --     trans = λ {i} {j} {k} z z₁ n → trans (z n) (z₁ n)
    --     }

    -- PolynomialSetoid : Setoid (c ⊔ ℓ) ℓ
    -- PolynomialSetoid = record { isEquivalence = ≈-eq }

    -- _+_ : Polynomial → Polynomial → Polynomial
    -- (p , m , p[≥m]=0) + (q , n , q[≥n]=0) = (λ o → p o +R q o) , maxℕ m n , λ {o} [max-m-n≤o] → begin
    --     p o +R q o      ≈⟨ +R-cong (p[≥m]=0 (≤-trans maxℕ≥fst (≤-recompute [max-m-n≤o]))) (q[≥n]=0 (≤-trans (maxℕ≥snd {m = m} {n = n}) (≤-recompute [max-m-n≤o]))) ⟩
    --     zeroR +R zeroR    ≈⟨ Ring.zero-is-+-right-id ring ⟩
    --     zeroR            ∎

    -- -_ : Polynomial → Polynomial
    -- -_ (p , m , p[≥m]=0) = (λ i → -R p i) , m , λ {i} pf → begin
    --     -R p i   ≈⟨ neg-cong (p[≥m]=0 pf) ⟩
    --     -R zeroR  ≈⟨ neg-zero-is-zero ⟩
    --     zeroR    ∎

    -- _*_ : Polynomial → Polynomial → Polynomial
    -- (p , m , p[≥m]=0) * (q , n , q[>n]=0) = pure-r , bound , bound-pf
    --     where
    --         -- sum over products of powers adding to i
    --         pure-r : ℕ → Carrier
    --         pure-r i = foldℕ (sucℕ i) (λ s j _ → s +R (p j *R q (i ∸ℕ j))) zeroR

    --         bound = m +ℕ n ∸ℕ 1

    --         split : ∀ {o} → .(bound ≤ o) → ∀ j → (m ≤ j) ⊎ (n ≤ o ∸ℕ j)
    --         split {o} bound-o j with m ≤? j
    --         ... | yes m≤j = inj₁ m≤j
    --         ... | no m≰j = inj₂ (
    --             n                       ≤⟨ m≤n⇒m≤n+o (m ∸ℕ (1 +ℕ j)) ≤-refl ⟩
    --             n +ℕ (m ∸ℕ (1 +ℕ j))    ≤⟨ ≤-reflexive (≡-sym (+-∸-assoc n {m} {1 +ℕ j} (≰⇒> m≰j))) ⟩
    --             (n +ℕ m) ∸ℕ (1 +ℕ j)    ≤⟨ ≤-reflexive (≡-sym (∸-+-assoc (n +ℕ m) 1 j)) ⟩
    --             ((n +ℕ m) ∸ℕ 1) ∸ℕ j    ≤⟨ ≤-reflexive (≡-cong (λ q → q ∸ℕ 1 ∸ℕ j) (+ℕ-comm n m)) ⟩
    --             ((m +ℕ n) ∸ℕ 1) ∸ℕ j    ≤⟨ ≤-refl ⟩
    --             (m +ℕ n ∸ℕ 1) ∸ℕ j      ≤⟨ ∸-monoˡ-≤ j (≤-recompute bound-o) ⟩
    --             o ∸ℕ j                  ∎')
    --             where
    --                 open ≤-syntax {R = _≤_} _≤_ _≤_ ≤-trans
    --                 open end-syntax _≤_ ≤-refl using () renaming (_∎ to _∎')

    --         carry : ∀ {o} → .(bound ≤ o) → (s : Carrier) (j : ℕ) → IsZero s → IsZero (s +R p j *R q (o ∸ℕ j))
    --         carry {o} bound-o s j s≈zero = begin
    --             s +R p j *R q (o ∸ℕ j)      ≈⟨ +R-cong s≈zero refl ⟩
    --             zeroR +R p j *R q (o ∸ℕ j)   ≈⟨ zero-is-+-left-id ⟩
    --             p j *R q (o ∸ℕ j)           ≈⟨ zero-is-*-strong-absorber (case (split bound-o j) of λ {(inj₁ m≤j) → inj₁ (p[≥m]=0 m≤j); (inj₂ n≤o∸j) → inj₂ (q[>n]=0 n≤o∸j)}) ⟩
    --             zeroR                        ∎

    --         bound-pf : ∀ {i} → .(bound ≤ i) → IsZero (pure-r i)
    --         bound-pf {i} bound-i = foldℕ-carrying-theorem (sucℕ i) (λ s j _ → s +R (p j *R q (i ∸ℕ j))) zeroR IsZero (λ x i _ → carry bound-i x i) refl

    -- zero : Polynomial
    -- zero = (λ _ → zeroR) , zeroℕ , λ _ → refl

    -- one : Polynomial
    -- one = (λ {zeroℕ → oneR; (sucℕ _) → zeroR}) , sucℕ zeroℕ , λ { {sucℕ _} _ → refl }


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


    -- ------------------------------------
    -- --- Proving that it forms a ring ---
    -- ------------------------------------

    -- +-cong : Congruent₂ _≈_ _≈_ _≈_ _+_
    -- +-cong = λ p q i → +R-cong (p i) (q i)

    -- +-op : SetoidFunction₂ PolynomialSetoid PolynomialSetoid PolynomialSetoid
    -- +-op = record {
    --     func = _+_;
    --     respects = λ p q i → +R-cong (p i) (q i)
    --     }

    -- negate-cong : Congruent _≈_ _≈_ -_
    -- negate-cong = λ p i → neg-cong (p i)

    -- negate-op : SetoidFunction PolynomialSetoid PolynomialSetoid
    -- negate-op = record {
    --     func = -_;
    --     respects = λ p i → neg-cong (p i)
    --     }

    -- *-cong : Congruent₂ _≈_ _≈_ _≈_ _*_
    -- *-cong {p₁'@(p₁ , m₁ , p₁[≥m₁]=0)} {p₂'@(p₂ , m₂ , p₂[≥m₂]=0)} {q₁'@(q₁ , n₁ , q₁[≥n₁]=0)} {q₂'@(q₂ , n₂ , q₂[≥n₂]=0)} p₁≈p₂ q₁≈q₂ i = begin
    --     (p₁' * q₁') .proj₁ i                                            ≈⟨ refl ⟩
    --     foldℕ (sucℕ i) (λ s j _ → s +R (p₁ j *R q₁ (i ∸ℕ j))) zeroR     ≈⟨ {!   !} ⟩
    --     foldℕ (sucℕ i) (λ s j _ → s +R (p₂ j *R q₂ (i ∸ℕ j))) zeroR     ≈⟨ refl ⟩
    --     (p₂' * q₂') .proj₁ i                                            ∎

    -- *-op : SetoidFunction₂ PolynomialSetoid PolynomialSetoid PolynomialSetoid
    -- *-op = record {
    --     func = _*_;
    --     respects = {!   !}
    --     }

    -- PolynomialRawRing : RawRing (c ⊔ ℓ) ℓ
    -- PolynomialRawRing = record {
    --     S = PolynomialSetoid;
    --     +-op = +-op;
    --     +-inverse = negate-op;
    --     zero = zero;
    --     *-op = *-op;
    --     one = one
    --     }

    -- PolynomialIsCommutativeRing : IsCommutativeRing PolynomialRawRing
    -- PolynomialIsCommutativeRing = record {
    --     +-isAbelianGroup = record {
    --         isGroup = record {
    --             id-is-left-id = λ {x} n → zero-is-+-left-id;
    --             inv-is-left-inv = λ {x} n → Ring.neg-is-+-left-inv ring;
    --             assoc = λ {x} {y} {z} n → Ring.+-assoc ring
    --             };
    --         abelian = λ {x} {y} n → Ring.+-comm ring
    --         };
    --     one-is-*-left-id = λ {p} n → {!   !};
    --     *-assoc = {!   !};
    --     *-+-left-distributive = {!   !};
    --     *-comm = {!   !}
    --     }

    -- PolynomialCommutativeRing : CommutativeRing (c ⊔ ℓ) ℓ
    -- PolynomialCommutativeRing = record {
    --     rawRing = PolynomialRawRing;
    --     isCommutativeRing = PolynomialIsCommutativeRing
    --     }

    -- PolynomialIsRing : IsRing PolynomialRawRing
    -- PolynomialIsRing = IsCommutativeRing.isRing PolynomialIsCommutativeRing

    -- PolynomialRing : Ring (c ⊔ ℓ) ℓ
    -- PolynomialRing = CommutativeRing.ring PolynomialCommutativeRing