open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≢_; _≡_; inspect; cong; Reveal_·_is_; [_]) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary using (Rel; IsEquivalence)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Function using (_∋_; _∘_; id; typeOf; Bijective; Injective; Surjective; Congruent; Bijection; Injection)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; _∸_; _+_; _*_; _≤_; _≥_; _<_; _>_; _<?_; <-cmp; s≤s; z≤n; s≤s⁻¹) renaming (zero to zero-ℕ; suc to suc-ℕ)
open import Data.Nat.Properties using (+-comm; <-trans; ≤-trans; ≤-<-trans; <-≤-trans; ≤-reflexive; ≤-refl; m+[n∸m]≡n; +-cancelˡ-<; +-monoʳ-<; ∸-monoˡ-<; m≤n+m; m≤m+n; +-suc; n∸n≡0; <-irrefl)
open import Data.Fin using (Fin; zero; suc; _↑ˡ_; _↑ʳ_; splitAt; join; combine; fromℕ<; toℕ) renaming (_<_ to _<-fin_; _≤_ to _≤-fin_; reduce≥ to reduce≥-fin)
open import Data.Fin.Properties using (join-splitAt; splitAt-join; splitAt-↑ˡ; splitAt-↑ʳ; splitAt⁻¹-↑ʳ; combine-injective; combine-surjective; toℕ<n; toℕ-fromℕ<; fromℕ<-toℕ; fromℕ<-cong; toℕ-↑ʳ)

open import Plasmaduck.SetoidExperiment.SetoidMachinery using (discrete-setoid; property-subset-setoid; from-discrete-cong; ⊎-setoid; ×-setoid; maybe-setoid; rel₁; rel₂)
open import Plasmaduck.Function.Bijection using (invert-bijection; _∘-bijection_)
open import Plasmaduck.Number.Fin using (fin-≡-dec; _↑ˡ-inverted_; splitAt-≥; fromℕ<-cong₂)
open import Plasmaduck.Number.Nat using (n<sn; n≤n; n≤sn; ≤→<≡; <→≤; s≡s⁻¹; sm∸n≡so→m∸n≡o; ∸-suc)
open import Plasmaduck.Util.TypeChange using (change-type; change-type-trans; change-type-trans'; change-type-proof-irrelevance; change-type-input-dependence-irrelevance; change-type-output-dependence-commute; change-type-bijective'; cong₂-dependent)
open import Plasmaduck.Util.Case using (case_of_)
open import Plasmaduck.Function.InjectionSurjection using (both-inv→bijective; LeftInverse; RightInverse)
open import Plasmaduck.Counting.Counting using (HasSize)
open import Plasmaduck.Counting.DeleteOne using (delete-one-bijection)


module Plasmaduck.Counting.Pigeonhole where

variable
    a b c ℓ ℓ₁ ℓ₂ : Level


pigeonhole-principle-fin : {m n : ℕ} → m > n → (f : Fin m → Fin n) → Σ (Fin m) λ i → Σ (Fin m) λ j → i ≢ j × f i ≡ f j
pigeonhole-principle-fin {zero-ℕ} {zero-ℕ} ()
pigeonhole-principle-fin {suc-ℕ _} {zero-ℕ} _ f with f zero
...                                                | ()
pigeonhole-principle-fin {suc-ℕ zero-ℕ} {suc-ℕ _} (s≤s ())
pigeonhole-principle-fin {m@(suc-ℕ m'@(suc-ℕ m''))} {n@(suc-ℕ n')} n<m f =
    case fz≡?fi of λ {
    (yes (i , fz≡fsi)) → zero , suc i , (λ ()) , fz≡fsi;
    (no no-zero-match) → get-sol-for-no-case no-zero-match
        }
    where
        hunt : (j : ℕ) .(j<m' : j < m') → Dec (Σ (Fin m') λ i → toℕ i ≤ j × f zero ≡ f (suc i))
        hunt j j<m'          with fin-≡-dec (f zero) (f (fromℕ< {m = suc-ℕ j} {n = m} (s≤s j<m')))
        ...                  | yes f0≡fsj = yes (fromℕ< {m = j} {n = m'} j<m' , ≤-reflexive (toℕ-fromℕ< j<m') , f0≡fsj)
        hunt zero-ℕ z<m'     | no f0≢f1 = no λ { (zero , z≤n , f0≡f1) → f0≢f1 f0≡f1 }
        hunt j@(suc-ℕ j') sj'<m' | no f0≢fsj with hunt j' (<-trans (s≤s⁻¹ sj'<m') n<sn)
        ...                               | yes (k , k≤j' , f0≡fsk) = yes (k , ≤-trans k≤j' n≤sn , f0≡fsk)
        ...                               | no pf' = no λ { (k , k≤j , f0≡fsk) → case ≤→<≡ k≤j of λ {
            (inj₁ k<j) → pf' (k , s≤s⁻¹ k<j , f0≡fsk);
            (inj₂ k≡j) → f0≢fsj (≡-trans f0≡fsk (cong (f ∘ suc) (≡-trans (≡-sym (fromℕ<-toℕ k (≤-<-trans k≤j sj'<m'))) (fromℕ<-cong (toℕ k) j k≡j (≤-<-trans k≤j sj'<m') sj'<m'))))
            }}

        zero-match-type : Set
        zero-match-type = Σ (Fin m') λ i → f zero ≡ f (suc i)

        fz≡?fi : Dec zero-match-type
        fz≡?fi with hunt m'' n<sn
        ...       | yes (i , _ , fz≡fsi) = yes (i , fz≡fsi)
        ...       | no no-zero-match = no λ { (i , fz≡fsi) → no-zero-match (i , s≤s⁻¹ (toℕ<n i) , fz≡fsi) }

        module NoZeroMatch (no-zero-match : ¬ zero-match-type) where

            disc-fin : ℕ → Setoid lzero lzero
            disc-fin = discrete-setoid ∘ Fin

            full-bijection : Bijection (property-subset-setoid (disc-fin n) (λ i → i ≢ f zero)) (disc-fin n')
            full-bijection = delete-one-bijection (f zero)

            f' : Fin m' → Fin n'
            f' i = full-bijection .Bijection.to (f (suc i) , λ fsi≡fz → no-zero-match (i , ≡-sym fsi≡fz))

            sol : Σ (Fin m) λ p → Σ (Fin m) λ q → p ≢ q × f p ≡ f q
            sol with pigeonhole-principle-fin (s≤s⁻¹ n<m) f'
            ... | (i' , j' , i'≢j' , f'i'≡f'j') = suc i' , suc j' , (λ { ≡-refl → i'≢j' ≡-refl }) , ((full-bijection .Bijection.bijective .proj₁) f'i'≡f'j')
                where
                    bij-inv : (x : Fin n') → Σ (Fin n) λ i → i ≢ f zero
                    bij-inv = proj₁ ∘ (full-bijection .Bijection.bijective .proj₂)

                    back : Fin n' → Fin n
                    back = proj₁ ∘ bij-inv

        open NoZeroMatch renaming (sol to get-sol-for-no-case)

module _ {m n : ℕ} (m>n : m > n) {A-setoid : Setoid a ℓ₁} (A-size-m : HasSize A-setoid m) {B-setoid : Setoid b ℓ₂} (B-size-n : HasSize B-setoid n) (f : A-setoid .Setoid.Carrier → B-setoid .Setoid.Carrier) where
    private
        A = A-setoid .Setoid.Carrier
        B = B-setoid .Setoid.Carrier

        _~_ = A-setoid .Setoid._≈_
        _≈_ = B-setoid .Setoid._≈_

        open Bijection using (to)

        f' : Fin m → Fin n
        f' = ((invert-bijection B-size-n) .to) ∘ f ∘ (A-size-m .to)

    pigeonhole-principle : Σ A λ x → Σ A λ y → (¬ x ~ y) × (f x ≈ f y)
    pigeonhole-principle with pigeonhole-principle-fin m>n f'
    ... | (i , j , i≢j , f'i≡f'j) = A-size-m .to i , A-size-m .to j , i≢j ∘ (A-size-m .Bijection.bijective .proj₁) , (invert-bijection B-size-n) .Bijection.bijective .proj₁ f'i≡f'j
