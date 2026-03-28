open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≢_; _≡_; inspect; cong; Reveal_·_is_; [_]) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary using (Rel; IsEquivalence; Decidable)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Function using (_∋_; _∘_; id; typeOf; Bijective; Injective; Surjective; Congruent; Bijection; Injection; Surjection)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; _∸_; _+_; _*_; _≤_; _≥_; _<_; _>_; _<?_; <-cmp; s≤s; z≤n; s≤s⁻¹) renaming (zero to zero-ℕ; suc to suc-ℕ)
open import Data.Nat.Properties using (+-comm; <-trans; ≤-trans; ≤-<-trans; <-≤-trans; ≤-reflexive; ≤-refl; m+[n∸m]≡n; +-cancelˡ-<; +-monoʳ-<; ∸-monoˡ-<; m≤n+m; m≤m+n; +-suc; n∸n≡0; <-irrefl)
open import Data.Fin using (Fin; zero; suc; _↑ˡ_; _↑ʳ_; splitAt; join; combine; fromℕ<; toℕ) renaming (_<_ to _<-fin_; _≤_ to _≤-fin_; reduce≥ to reduce≥-fin)
open import Data.Fin.Properties using (join-splitAt; splitAt-join; splitAt-↑ˡ; splitAt-↑ʳ; splitAt⁻¹-↑ʳ; combine-injective; combine-surjective; toℕ<n; toℕ-fromℕ<; fromℕ<-toℕ; fromℕ<-cong; toℕ-↑ʳ)

open import Plasmaduck.SetoidExperiment.SetoidMachinery using (discrete-setoid; property-subset-setoid; from-discrete-cong; ⊎-setoid; ×-setoid; maybe-setoid; rel₁; rel₂; SetoidFunction; _which-is-cong_)
open import Plasmaduck.Function.Bijection using (invert-bijection; _∘-bijection_)
open import Plasmaduck.Number.Fin using (fin-≡-dec; _↑ˡ-inverted_; splitAt-≥; fromℕ<-cong₂)
open import Plasmaduck.Number.Nat using (n<sn; n≤n; n≤sn; ≤→<≡; <→≤; s≡s⁻¹; sm∸n≡so→m∸n≡o; ∸-suc)
open import Plasmaduck.Util.TypeChange using (change-type; change-type-trans; change-type-trans'; change-type-proof-irrelevance; change-type-input-dependence-irrelevance; change-type-output-dependence-commute; change-type-bijective'; cong₂-dependent)
open import Plasmaduck.Util.Case using (case_of_)
open import Plasmaduck.Function.InjectionSurjection using (both-inv→bijective; LeftInverse; RightInverse; bijection→surjection; _∘-surjection_)
open import Plasmaduck.Counting.Counting using (HasSize)
open import Plasmaduck.Counting.DeleteOne using (delete-one-bijection)

open import Plasmaduck.Counting.Counting using (HasSize; AtMostSize; IsFinite; IsWeaklyFinite; subset-of-finite-is-upper-bounded)
open import Plasmaduck.Counting.Pigeonhole using (pigeonhole-principle-fin; any-zero-eq)
open import Plasmaduck.Property.Defs using (DecidableProperty; CongruentProperty)
open import Plasmaduck.Relation.Decidable using (decidable-push)


module Plasmaduck.Counting.Strengthening where

variable
    a b c ℓ ℓ₁ : Level


module _ (A-setoid : Setoid c ℓ) where
    private
        A = A-setoid .Setoid.Carrier
        _~_ = A-setoid .Setoid._≈_
        open IsEquivalence (A-setoid .Setoid.isEquivalence) using (refl; sym; trans)

        reflexive : {x y : A} → x ≡ y → x ~ y
        reflexive {x = x} {.x} ≡-refl = refl


    any-eq : Decidable _~_ → {m : ℕ} → (f : Fin m → A) → Dec (Σ (Fin m) λ x → Σ (Fin m) λ y → x ≢ y × f x ~ f y)
    any-eq _~?_ {m = zero-ℕ} f = no λ { (() , _) }
    any-eq _~?_ {m = suc-ℕ zero-ℕ} f = no λ { (zero , zero , z≢z , _) → ⊥-elim (z≢z ≡-refl) }
    any-eq _~?_ {m = m@(suc-ℕ m')} f = sol
        where
            zero-match-type : Set ℓ
            zero-match-type = Σ (Fin m') λ i → f zero ~ f (suc i)

            zero-dec : Dec zero-match-type
            zero-dec = any-zero-eq A-setoid _~?_ f

            recursive-call : Dec (Σ (Fin m') λ x → Σ (Fin m') λ y → x ≢ y × f (suc x) ~ f (suc y))
            recursive-call = any-eq _~?_ {m = m'} (f ∘ suc)

            sol : Dec (Σ (Fin m) λ x → Σ (Fin m) λ y → x ≢ y × f x ~ f y)
            sol with zero-dec
            ... | no no-zero-match with any-eq _~?_ {m = m'} (f ∘ suc)
            ...     | yes (x , y , x≢y , fsx~fsy) = yes (suc x , suc y , (λ { ≡-refl → x≢y ≡-refl}) , fsx~fsy)
            ...     | no pf = no λ {
                    (zero , zero , z≢z , _) → z≢z ≡-refl;
                    (zero , suc y , _ , fzero~fsy) → no-zero-match (y , fzero~fsy);
                    (suc x , zero , _ , fsx~fzero) → no-zero-match (x , sym fsx~fzero);
                    (suc x , suc y , sx≢sy , fsx~fsy) → pf (x , y , (λ x≡y → sx≢sy (cong suc x≡y)) , fsx~fsy)
                    }
            sol | yes (x , fz~fsi) = yes (zero , suc x , (λ ()) , fz~fsi)


module _ {A-setoid : Setoid c ℓ} (_~?_ : Decidable (A-setoid .Setoid._≈_)) where
    private
        A = A-setoid .Setoid.Carrier
        _~_ = A-setoid .Setoid._≈_
        open IsEquivalence (A-setoid .Setoid.isEquivalence) using (refl; sym; trans)


    strengthen-core : {n : ℕ} → AtMostSize A-setoid n → Σ ℕ λ m → HasSize A-setoid m × m ≤ n
    strengthen-core (inj₂ ¬A) = zero-ℕ , record {
        to = λ ();
        cong = λ {};
        bijective = (λ {}) , ⊥-elim ∘ ¬A
        } , z≤n
    strengthen-core {zero-ℕ} (inj₁ n-surjection) = zero-ℕ , record {
        to = n-surjection .Surjection.to;
        cong = λ {};
        bijective = (λ {}) , n-surjection .Surjection.surjective
        } , z≤n
    strengthen-core {n = n@(suc-ℕ n')} (inj₁ n-surjection) with any-eq A-setoid _~?_ (n-surjection .Surjection.to)
    ... | no pf = n , record {
        to = to;
        cong = from-discrete-cong A-setoid to;
        bijective = injective , n-surjection .Surjection.surjective
        } , ≤-refl
        where
            to : (Fin n) → A
            to = n-surjection .Surjection.to

            injective : Injective _≡_ _~_ to
            injective {x = x} {y} fx~fy with fin-≡-dec x y
            ... | yes x≡y = x≡y
            ... | no x≢y = ⊥-elim (pf (x , y , x≢y , fx~fy))
    ... | yes (x , y , x≢y , fx~fy) with strengthen-core {n = n'} (inj₁ surjection)
        where
            old-to : (Fin n) → A
            old-to = n-surjection .Surjection.to

            n-without-y-setoid = property-subset-setoid (discrete-setoid (Fin n)) λ i → i ≢ y

            to' : (Σ (Fin n) λ i → i ≢ y) → A
            to' = old-to ∘ proj₁

            to'-cong : Congruent (n-without-y-setoid .Setoid._≈_) _~_ to'
            to'-cong = n-surjection .Surjection.cong

            to'-surjective : Surjective (n-without-y-setoid .Setoid._≈_) _~_ to'
            to'-surjective z with n-surjection .Surjection.surjective z
            ... | old-x , refl→to-old-x~z with fin-≡-dec old-x y
            ...     | no old-x≢y = (old-x , old-x≢y) , λ { ≡-refl → refl→to-old-x~z ≡-refl }
            ...     | yes old-x≡y = (x , x≢y) , λ { ≡-refl → trans (trans fx~fy (sym (n-surjection .Surjection.cong old-x≡y))) (refl→to-old-x~z ≡-refl) }

            to'-surjection : Surjection n-without-y-setoid A-setoid
            to'-surjection = record {
                to = to';
                cong = n-surjection .Surjection.cong;
                surjective = to'-surjective
                }

            del-bij : Bijection n-without-y-setoid (discrete-setoid (Fin n'))
            del-bij = delete-one-bijection y

            surjection : Surjection (discrete-setoid (Fin n')) A-setoid
            surjection = to'-surjection ∘-surjection bijection→surjection (invert-bijection del-bij)
    ...         | m , A-size-m , m≤n' = m , A-size-m , ≤-trans m≤n' n≤sn

    strengthen : IsWeaklyFinite A-setoid → IsFinite A-setoid
    strengthen (_ , A-size-upper-bound) with strengthen-core A-size-upper-bound
    ... | m , A-size-m , _ = m , A-size-m

module _
    {A-setoid : Setoid a ℓ}
    (_~?_ : Decidable (A-setoid .Setoid._≈_))
    {P : A-setoid .Setoid.Carrier → Set ℓ₁}
    (P-cong : CongruentProperty A-setoid P)
    (P-dec : DecidableProperty P)
    where

    subset-of-finite-is-finite' :
        {n : ℕ} → HasSize A-setoid n →
        Σ ℕ λ m → HasSize (property-subset-setoid A-setoid P) m × m ≤ n
    subset-of-finite-is-finite' A-size-n = strengthen-core (decidable-push A-setoid _~?_) (subset-of-finite-is-upper-bounded P-cong P-dec A-size-n) --

    subset-of-finite-is-finite :
        IsFinite A-setoid →
        IsFinite (property-subset-setoid A-setoid P)
    subset-of-finite-is-finite (_ , A-size) with subset-of-finite-is-finite' A-size
    ... | (m , A-with-P-size-m , _) = m , A-with-P-size-m
