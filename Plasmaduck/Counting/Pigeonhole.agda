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

            flatten-subtraction : {i : ℕ} → (n' ≤ i) → Fin (toℕ (f zero) + (i ∸ toℕ (f zero))) ≡ Fin i
            flatten-subtraction {i = i} n≤i = cong Fin (m+[n∸m]≡n {m = toℕ (f zero)} {n = i} (≤-trans (s≤s⁻¹ (toℕ<n (f zero))) n≤i ))

            f0 : ℕ
            f0 = toℕ (f zero)

            twist : ℕ → ℕ
            twist i = f0 + (i ∸ f0)

            twist-id : {i : ℕ} → f0 ≤ i → twist i ≡ i
            twist-id {i = i} f0≤i = m+[n∸m]≡n {m = f0} {n = i} f0≤i

            fin-twist : {i : ℕ} → f0 ≤ i → Fin i → Fin (twist i)
            fin-twist f0≤i x = change-type (cong Fin (≡-sym (twist-id f0≤i))) x

            disc-fin : ℕ → Setoid lzero lzero
            disc-fin = discrete-setoid ∘ Fin

            twist-bij : {i : ℕ} → f0 ≤ i → Bijection (disc-fin i) (disc-fin (twist i))
            twist-bij {i = i} f0≤i = record {
                to = fin-twist f0≤i;
                cong = from-discrete-cong (disc-fin (twist i)) (fin-twist f0≤i);
                bijective = change-type-bijective' (cong Fin (≡-sym (twist-id f0≤i)))
                }

            split-bij : {i : ℕ} → f0 ≤ i → Bijection (disc-fin (twist i)) (discrete-setoid (Fin f0 ⊎ Fin (i ∸ f0)))
            split-bij {i = i} f0≤i = record {
                to = to;
                cong = to-cong;
                bijective = both-inv→bijective A B to to-cong (inv , inv-cong , (λ {x} → join-splitAt f0 (i ∸ f0) x) , λ {y} → splitAt-join f0 (i ∸ f0) y)
                }
                where
                    A = (disc-fin (twist i))
                    B = (discrete-setoid (Fin f0 ⊎ Fin (i ∸ f0)))
                    to = splitAt f0 {n = i ∸ f0}
                    to-cong = from-discrete-cong B to

                    inv = join f0 (i ∸ f0)
                    inv-cong = from-discrete-cong A inv

            n∸f0-spin : {i : ℕ} → f0 ≤ i → suc-ℕ (i ∸ f0) ≡ suc-ℕ i ∸ f0
            n∸f0-spin {i = i} f0≤i = ∸-suc i f0 f0≤i

            f0-⊎-n∸f0≡f0-⊎-s[n'∸f0] : {i : ℕ} → f0 ≤ i → (Fin f0 ⊎ (Fin (suc-ℕ i ∸ f0))) ≡ (Fin f0 ⊎ (Fin (suc-ℕ (i ∸ f0))))
            f0-⊎-n∸f0≡f0-⊎-s[n'∸f0] f0≤i = cong (Fin f0 ⊎_) (cong Fin (≡-sym (n∸f0-spin f0≤i)))

            spin-bij : {i : ℕ} → f0 ≤ i → Bijection (discrete-setoid (Fin f0 ⊎ (Fin (suc-ℕ i ∸ f0)))) (discrete-setoid (Fin f0 ⊎ (Fin (suc-ℕ (i ∸ f0)))))
            spin-bij {i = i} f0≤i = record {
                to = to;
                cong = to-cong;
                bijective = both-inv→bijective A-setoid B-setoid to to-cong (inv , inv-cong , is-left-inv , is-right-inv)
                }
                where

                    A = Fin f0 ⊎ (Fin (suc-ℕ i ∸ f0))
                    B = Fin f0 ⊎ (Fin (suc-ℕ (i ∸ f0)))
                    A-setoid = discrete-setoid A
                    B-setoid = discrete-setoid B

                    to : A → B
                    to = change-type (f0-⊎-n∸f0≡f0-⊎-s[n'∸f0] f0≤i)

                    to-cong : Congruent _≡_ _≡_ to
                    to-cong = from-discrete-cong B-setoid to

                    inv : B → A
                    inv = change-type (≡-sym (f0-⊎-n∸f0≡f0-⊎-s[n'∸f0] f0≤i))

                    inv-cong : Congruent _≡_ _≡_ inv
                    inv-cong = from-discrete-cong A-setoid inv

                    is-left-inv : LeftInverse A-setoid B-setoid to to-cong inv
                    is-left-inv = change-type-trans' (f0-⊎-n∸f0≡f0-⊎-s[n'∸f0] f0≤i) (≡-sym (f0-⊎-n∸f0≡f0-⊎-s[n'∸f0] f0≤i)) ≡-refl

                    is-right-inv : RightInverse A-setoid B-setoid to to-cong inv
                    is-right-inv = change-type-trans' (≡-sym (f0-⊎-n∸f0≡f0-⊎-s[n'∸f0] f0≤i)) (f0-⊎-n∸f0≡f0-⊎-s[n'∸f0] f0≤i) ≡-refl

            half : {i : ℕ} → f0 ≤ i → Bijection (disc-fin (suc-ℕ i)) (discrete-setoid (Fin f0 ⊎ (Fin (suc-ℕ (i ∸ f0)))))
            half f0≤i = (spin-bij f0≤i) ∘-bijection (split-bij (≤-trans f0≤i n≤sn)) ∘-bijection (twist-bij (≤-trans f0≤i n≤sn))

            f0≤n' : f0 ≤ n'
            f0≤n' = s≤s⁻¹ (toℕ<n (f zero))

            f0≤n : f0 ≤ n
            f0≤n = ≤-trans f0≤n' n≤sn

            first-half : Bijection (disc-fin n) (discrete-setoid (Fin f0 ⊎ (Fin (suc-ℕ (n' ∸ f0)))))
            first-half = half f0≤n'

            first-half-fz : first-half .Bijection.to (f zero) ≡ inj₂ zero
            first-half-fz = ((spin-bij f0≤n' .Bijection.to) ∘ splitAt f0 {n = n ∸ f0} ∘ (fin-twist {i = n} f0≤n)) (f zero) ≡ inj₂ zero ∋
                ((spin-bij f0≤n' .Bijection.to) ∘ splitAt f0 {n = n ∸ f0} ∘ (fin-twist {i = n} f0≤n)) (f zero)
                    ≡⟨ cong (spin-bij f0≤n' .Bijection.to) (
                        splitAt f0 (fin-twist f0≤n (f zero))
                            ≡⟨ splitAt-≥ {m = f0} (fin-twist f0≤n (f zero)) (≤-reflexive (≡-sym twist-f0≡f0)) ⟩
                        inj₂ (fromℕ< {m = toℕ (fin-twist f0≤n (f zero)) ∸ f0} {n = n ∸ f0} (∸-monoˡ-< {m = toℕ (fin-twist f0≤n (f zero))} {n = f0} {o = n} (<-≤-trans (toℕ<n (fin-twist f0≤n (f zero))) (≤-reflexive (twist-id f0≤n))) (≤-reflexive (≡-sym twist-f0≡f0))))
                            ≡⟨ cong inj₂ (fromℕ<-cong (toℕ (fin-twist f0≤n (f zero)) ∸ f0) 0 twist-f0∸f0≡0 (≤-<-trans (≤-reflexive twist-f0∸f0≡0) (<-≤-trans (s≤s z≤n) (≤-reflexive (n∸f0-spin f0≤n')))) (<-≤-trans (s≤s z≤n) (≤-reflexive (n∸f0-spin f0≤n')))) ⟩
                        inj₂ (fromℕ< {m = 0} {n = n ∸ f0} (<-≤-trans (s≤s z≤n) (≤-reflexive (n∸f0-spin f0≤n'))))
                            ≡⟨ cong inj₂ (≡-trans (≡-sym (change-type-trans' (cong Fin (≡-sym (n∸f0-spin f0≤n'))) (cong Fin (n∸f0-spin f0≤n')) ≡-refl)) (cong (change-type (cong Fin (n∸f0-spin f0≤n'))) (fromℕ<-cong₂ 0 0 (n ∸ f0) (suc-ℕ (n' ∸ f0)) ≡-refl (≡-sym (n∸f0-spin f0≤n')) (<-≤-trans (s≤s z≤n) (≤-reflexive (n∸f0-spin f0≤n'))) (s≤s z≤n)))) ⟩
                        inj₂ (change-type (cong Fin (n∸f0-spin f0≤n')) zero)
                            ≡⟨ ≡-trans (change-type-output-dependence-commute {a = lzero} {b = lzero} {c = lzero} {A = ℕ} Fin (λ _ i → Fin f0 ⊎ typeOf i) inj₂ (n∸f0-spin f0≤n') zero) (change-type-proof-irrelevance (cong₂-dependent Fin (λ z i → Fin f0 ⊎ typeOf i) (n∸f0-spin f0≤n') ≡-refl) (≡-sym (f0-⊎-n∸f0≡f0-⊎-s[n'∸f0] f0≤n'))) ⟩
                        change-type (≡-sym (f0-⊎-n∸f0≡f0-⊎-s[n'∸f0] f0≤n')) (inj₂ zero)
                            ∎
                    ) ⟩
                (spin-bij f0≤n' .Bijection.to) (change-type (≡-sym (f0-⊎-n∸f0≡f0-⊎-s[n'∸f0] f0≤n')) (inj₂ zero)) ≡⟨ change-type-trans' (≡-sym (f0-⊎-n∸f0≡f0-⊎-s[n'∸f0] f0≤n')) (f0-⊎-n∸f0≡f0-⊎-s[n'∸f0] f0≤n') ≡-refl ⟩
                inj₂ zero ∎
                where
                    open ≡-Reasoning

                    twist-f0≡f0 : toℕ (fin-twist f0≤n (f zero)) ≡ f0
                    twist-f0≡f0 = change-type-input-dependence-irrelevance Fin toℕ (≡-sym (twist-id f0≤n)) (f zero)

                    twist-f0∸f0≡0 : toℕ (fin-twist f0≤n (f zero)) ∸ f0 ≡ 0
                    twist-f0∸f0≡0 = ≡-trans (cong (_∸ f0) twist-f0≡f0) (n∸n≡0 (toℕ (f zero)))

            first-half-mod : Bijection (property-subset-setoid (discrete-setoid (Fin n)) (λ i → i ≢ f zero)) (⊎-setoid (discrete-setoid (Fin f0)) (property-subset-setoid (discrete-setoid (Fin (suc-ℕ (n' ∸ f0)))) (λ x → x ≢ zero)))
            first-half-mod = record {
                to = to;
                cong = to-cong;
                bijective = injective , surjective
                }
                where
                    open ≡-Reasoning
                    A-setoid = property-subset-setoid (discrete-setoid (Fin n)) (λ i → i ≢ f zero)
                    B-setoid = ⊎-setoid (discrete-setoid (Fin f0)) (property-subset-setoid (discrete-setoid (Fin (suc-ℕ (n' ∸ f0)))) (λ x → x ≢ zero))
                    A = A-setoid .Setoid.Carrier
                    B = B-setoid .Setoid.Carrier

                    _~_ : Rel A lzero
                    _~_ = A-setoid .Setoid._≈_
                    _≈_ : Rel B lzero
                    _≈_ = B-setoid .Setoid._≈_

                    old-to : Fin n → Fin f0 ⊎ Fin (suc-ℕ (n' ∸ f0))
                    old-to = first-half .Bijection.to

                    old-injective : Injective _≡_ _≡_ old-to
                    old-injective = first-half .Bijection.bijective .proj₁

                    old-surjective : Surjective _≡_ _≡_ old-to
                    old-surjective = first-half .Bijection.bijective .proj₂

                    to : A → B
                    to (i , i≢fz) with first-half .Bijection.to i | inspect (first-half .Bijection.to) i
                    ... | inj₁ x | _ = inj₁ x
                    ... | inj₂ zero | [ to-i≡z₂ ] = ⊥-elim (i≢fz (old-injective (≡-trans to-i≡z₂ (≡-sym first-half-fz))))
                    ... | inj₂ (suc x) | _  = inj₂ ((suc x) , λ ())

                    to-cong : Congruent _~_ _≈_ to
                    to-cong {i , i≢fz} {.i , j≢fz} ≡-refl with first-half .Bijection.to i | inspect (first-half .Bijection.to) i
                    ... | inj₁ x | _ = rel₁ ≡-refl
                    ... | inj₂ zero | [ to-i≡z₂ ] = ⊥-elim (i≢fz (old-injective (≡-trans to-i≡z₂ (≡-sym first-half-fz))))
                    ... | inj₂ (suc x) | _  = rel₂ ≡-refl

                    injective : Injective _~_ _≈_ to
                    injective {i , i≢fz} {j , j≢fz} to-i≈to-j with first-half .Bijection.to i | inspect (first-half .Bijection.to) i | first-half .Bijection.to j | inspect (first-half .Bijection.to) j | to-i≈to-j
                    ... | inj₁ p | [ old-to-i≡p ] | inj₁ .p | [ old-to-j≡p ] | rel₁ ≡-refl = old-injective {i} {j} (≡-trans old-to-i≡p (≡-sym old-to-j≡p))
                    ... | inj₂ zero | [ old-to-i≡z₂ ] | _ | _ | _ = ⊥-elim (i≢fz (old-injective (≡-trans old-to-i≡z₂ (≡-sym first-half-fz))))
                    ... | _ | _ | inj₂ zero | [ old-to-j≡z₂ ] | _ = ⊥-elim (j≢fz (old-injective ((≡-trans old-to-j≡z₂ (≡-sym first-half-fz)))))
                    ... | inj₂ (suc p) | [ old-to-i≡p ] | inj₂ (suc q) | [ old-to-j≡q ] | rel₂ sp≡sq = old-injective {i} {j} (
                        old-to i        ≡⟨ old-to-i≡p ⟩
                        inj₂ (suc p)    ≡⟨ cong inj₂ sp≡sq ⟩
                        inj₂ (suc q)    ≡⟨ ≡-sym old-to-j≡q ⟩
                        old-to j        ∎
                        )

                    inj₂-cancel : {A : Set a} {n : ℕ} → (x y : Fin n) → inj₂ {A = A} x ≡ inj₂ {A = A} y → x ≡ y
                    inj₂-cancel x .x ≡-refl = ≡-refl

                    inj₁-cancel : {A : Set a} {n : ℕ} → (x y : Fin n) → inj₁ {B = A} x ≡ inj₁ {B = A} y → x ≡ y
                    inj₁-cancel x .x ≡-refl = ≡-refl

                    surjective : Surjective _~_ _≈_ to
                    surjective (inj₁ x) with old-surjective (inj₁ x)
                    ... | i , pf = (i , λ i≡fz → case (
                        inj₁ x          ≡⟨ ≡-sym (pf ≡-refl) ⟩
                        old-to i        ≡⟨ cong old-to i≡fz ⟩
                        old-to (f zero) ≡⟨ first-half-fz ⟩
                        inj₂ zero       ∎
                        ) of λ ()) , thing
                        where
                            thing : ∀ {z} → z ~ (i , λ i≡fz → case (
                                inj₁ x          ≡⟨ ≡-sym (pf ≡-refl) ⟩
                                old-to i        ≡⟨ cong old-to i≡fz ⟩
                                old-to (f zero) ≡⟨ first-half-fz ⟩
                                inj₂ zero       ∎
                                ) of λ ()) → to z ≈ inj₁ x
                            thing {.i , i≢fz} ≡-refl with first-half .Bijection.to i | inspect (first-half .Bijection.to) i
                            ... | inj₁ y | [ to-i≡y₁ ] = rel₁ (inj₁-cancel y x (≡-trans (≡-sym to-i≡y₁) (pf ≡-refl)))
                            ... | inj₂ zero | [ to-i≡z₂ ] = ⊥-elim (i≢fz (old-injective (≡-trans to-i≡z₂ (≡-sym first-half-fz))))
                            ... | inj₂ (suc y) | [ to-i≡y₂ ] = ⊥-elim (case (≡-trans (≡-sym to-i≡y₂) (pf ≡-refl)) of λ ())
                    surjective (inj₂ (x , x≢z)) with old-surjective (inj₂ x)
                    ... | i , pf = (i , λ i≡fz → x≢z (inj₂-cancel x zero (
                        inj₂ x ≡⟨ ≡-sym (pf ≡-refl) ⟩
                        old-to i ≡⟨ cong old-to i≡fz ⟩
                        old-to (f zero) ≡⟨ first-half-fz ⟩
                        inj₂ zero ∎
                        ))) , thing
                        where
                            thing : ∀ {z} → z ~ (i , λ i≡fz → x≢z (inj₂-cancel x zero (
                                inj₂ x ≡⟨ ≡-sym (pf ≡-refl) ⟩
                                old-to i ≡⟨ cong old-to i≡fz ⟩
                                old-to (f zero) ≡⟨ first-half-fz ⟩
                                inj₂ zero ∎
                                ))) → to z ≈ (inj₂ (x , x≢z))
                            thing {.i , i≢fz} ≡-refl with first-half .Bijection.to i | inspect (first-half .Bijection.to) i
                            ... | inj₁ y | [ to-i≡y₁ ] = ⊥-elim (case ≡-trans (≡-sym to-i≡y₁) (pf ≡-refl) of λ ())
                            ... | inj₂ zero | [ to-i≡z₂ ] = ⊥-elim (i≢fz (old-injective (≡-trans to-i≡z₂ (≡-sym first-half-fz))))
                            ... | inj₂ (suc y) | [ to-i≡y₂ ] = rel₂ (inj₂-cancel (suc y) x (≡-trans (≡-sym to-i≡y₂) (pf ≡-refl)))

            oops-property-bij : Bijection (⊎-setoid (discrete-setoid (Fin f0)) (property-subset-setoid (discrete-setoid (Fin (suc-ℕ (n' ∸ f0)))) (λ x → x ≢ zero))) (discrete-setoid (Fin f0 ⊎ Σ (Fin (suc-ℕ (n' ∸ f0))) λ x → x ≢ zero))
            oops-property-bij = record {
                to = id;
                cong = to-cong;
                bijective = both-inv→bijective A-setoid B-setoid to to-cong (inv , inv-cong , is-left-inv , is-right-inv)
                }
                where
                    A-setoid = ⊎-setoid (discrete-setoid (Fin f0)) (property-subset-setoid (discrete-setoid (Fin (suc-ℕ (n' ∸ f0)))) (λ x → x ≢ zero))
                    B-setoid = discrete-setoid (Fin f0 ⊎ Σ (Fin (suc-ℕ (n' ∸ f0))) λ x → x ≢ zero)
                    A = A-setoid .Setoid.Carrier
                    B = B-setoid .Setoid.Carrier

                    _~_ = A-setoid .Setoid._≈_
                    _≈_ = B-setoid .Setoid._≈_

                    to : A → B
                    to = id

                    to-cong : Congruent _~_ _≈_ to
                    to-cong (rel₁ ≡-refl) = ≡-refl
                    to-cong (rel₂ ≡-refl) = ≡-refl

                    inv : B → A
                    inv = id

                    inv-cong : Congruent _≈_ _~_ inv
                    inv-cong ≡-refl = A-setoid .Setoid.isEquivalence .IsEquivalence.refl

                    is-left-inv : LeftInverse A-setoid B-setoid to to-cong inv
                    is-left-inv = A-setoid .Setoid.isEquivalence .IsEquivalence.refl

                    is-right-inv : RightInverse A-setoid B-setoid to to-cong inv
                    is-right-inv = B-setoid .Setoid.isEquivalence .IsEquivalence.refl

            del-bij : Bijection (discrete-setoid (Fin f0 ⊎ Fin (n' ∸ f0))) (discrete-setoid (Fin f0 ⊎ Σ (Fin (suc-ℕ (n' ∸ f0))) λ x → x ≢ zero))
            del-bij = record {
                to = to;
                cong = to-cong;
                bijective = both-inv→bijective A-setoid B-setoid to to-cong (inv , inv-cong , is-left-inv , is-right-inv)
                }
                where
                    A = Fin f0 ⊎ Fin (n' ∸ f0)
                    B = Fin f0 ⊎ Σ (Fin (suc-ℕ (n' ∸ f0))) λ x → x ≢ zero
                    A-setoid = discrete-setoid A
                    B-setoid = discrete-setoid B
                    to : A → B
                    to (inj₁ x) = inj₁ x
                    to (inj₂ x) = inj₂ ((suc x) , λ ())

                    to-cong : Congruent _≡_ _≡_ to
                    to-cong = from-discrete-cong B-setoid to

                    inv : B → A
                    inv (inj₁ x) = inj₁ x
                    inv (inj₂ (zero , z≠z)) = ⊥-elim (z≠z ≡-refl)
                    inv (inj₂ (suc x , _)) = inj₂ x

                    inv-cong : Congruent _≡_ _≡_ inv
                    inv-cong = from-discrete-cong A-setoid inv

                    is-left-inv : LeftInverse A-setoid B-setoid to to-cong inv
                    is-left-inv {inj₁ x} = ≡-refl
                    is-left-inv {inj₂ x} = ≡-refl

                    is-right-inv : RightInverse A-setoid B-setoid to to-cong inv
                    is-right-inv {inj₁ x} = ≡-refl
                    is-right-inv {inj₂ (zero , z≠z)} = ⊥-elim (z≠z ≡-refl)
                    is-right-inv {inj₂ (suc x , _)} = ≡-refl

            full-bijection : Bijection (property-subset-setoid (disc-fin n) (λ i → i ≢ f zero)) (disc-fin n')
            full-bijection = (invert-bijection (twist-bij f0≤n')) ∘-bijection (invert-bijection (split-bij f0≤n')) ∘-bijection (invert-bijection del-bij) ∘-bijection oops-property-bij ∘-bijection first-half-mod

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
