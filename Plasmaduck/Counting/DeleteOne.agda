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



module Plasmaduck.Counting.DeleteOne where

variable
    a : Level

delete-one-bijection : {n : ℕ} → (i : Fin (suc-ℕ n)) → Bijection (property-subset-setoid (discrete-setoid (Fin (suc-ℕ n))) λ j → j ≢ i) (discrete-setoid (Fin n))
delete-one-bijection {n = n'} q = full-bijection
    where
        n = suc-ℕ n'

        qℕ : ℕ
        qℕ = toℕ q

        twist : ℕ → ℕ
        twist i = qℕ + (i ∸ qℕ)

        twist-id : {i : ℕ} → qℕ ≤ i → twist i ≡ i
        twist-id {i = i} qℕ≤i = m+[n∸m]≡n {m = qℕ} {n = i} qℕ≤i

        fin-twist : {i : ℕ} → qℕ ≤ i → Fin i → Fin (twist i)
        fin-twist qℕ≤i x = change-type (cong Fin (≡-sym (twist-id qℕ≤i))) x

        disc-fin : ℕ → Setoid lzero lzero
        disc-fin = discrete-setoid ∘ Fin

        twist-bij : {i : ℕ} → qℕ ≤ i → Bijection (disc-fin i) (disc-fin (twist i))
        twist-bij {i = i} qℕ≤i = record {
            to = fin-twist qℕ≤i;
            cong = from-discrete-cong (disc-fin (twist i)) (fin-twist qℕ≤i);
            bijective = change-type-bijective' (cong Fin (≡-sym (twist-id qℕ≤i)))
            }

        split-bij : {i : ℕ} → qℕ ≤ i → Bijection (disc-fin (twist i)) (discrete-setoid (Fin qℕ ⊎ Fin (i ∸ qℕ)))
        split-bij {i = i} qℕ≤i = record {
            to = to;
            cong = to-cong;
            bijective = both-inv→bijective A B to to-cong (inv , inv-cong , (λ {x} → join-splitAt qℕ (i ∸ qℕ) x) , λ {y} → splitAt-join qℕ (i ∸ qℕ) y)
            }
            where
                A = (disc-fin (twist i))
                B = (discrete-setoid (Fin qℕ ⊎ Fin (i ∸ qℕ)))
                to = splitAt qℕ {n = i ∸ qℕ}
                to-cong = from-discrete-cong B to

                inv = join qℕ (i ∸ qℕ)
                inv-cong = from-discrete-cong A inv

        n∸qℕ-spin : {i : ℕ} → qℕ ≤ i → suc-ℕ (i ∸ qℕ) ≡ suc-ℕ i ∸ qℕ
        n∸qℕ-spin {i = i} qℕ≤i = ∸-suc i qℕ qℕ≤i

        qℕ-⊎-n∸qℕ≡qℕ-⊎-s[n'∸qℕ] : {i : ℕ} → qℕ ≤ i → (Fin qℕ ⊎ (Fin (suc-ℕ i ∸ qℕ))) ≡ (Fin qℕ ⊎ (Fin (suc-ℕ (i ∸ qℕ))))
        qℕ-⊎-n∸qℕ≡qℕ-⊎-s[n'∸qℕ] qℕ≤i = cong (Fin qℕ ⊎_) (cong Fin (≡-sym (n∸qℕ-spin qℕ≤i)))

        spin-bij : {i : ℕ} → qℕ ≤ i → Bijection (discrete-setoid (Fin qℕ ⊎ (Fin (suc-ℕ i ∸ qℕ)))) (discrete-setoid (Fin qℕ ⊎ (Fin (suc-ℕ (i ∸ qℕ)))))
        spin-bij {i = i} qℕ≤i = record {
            to = to;
            cong = to-cong;
            bijective = both-inv→bijective A-setoid B-setoid to to-cong (inv , inv-cong , is-left-inv , is-right-inv)
            }
            where

                A = Fin qℕ ⊎ (Fin (suc-ℕ i ∸ qℕ))
                B = Fin qℕ ⊎ (Fin (suc-ℕ (i ∸ qℕ)))
                A-setoid = discrete-setoid A
                B-setoid = discrete-setoid B

                to : A → B
                to = change-type (qℕ-⊎-n∸qℕ≡qℕ-⊎-s[n'∸qℕ] qℕ≤i)

                to-cong : Congruent _≡_ _≡_ to
                to-cong = from-discrete-cong B-setoid to

                inv : B → A
                inv = change-type (≡-sym (qℕ-⊎-n∸qℕ≡qℕ-⊎-s[n'∸qℕ] qℕ≤i))

                inv-cong : Congruent _≡_ _≡_ inv
                inv-cong = from-discrete-cong A-setoid inv

                is-left-inv : LeftInverse A-setoid B-setoid to to-cong inv
                is-left-inv = change-type-trans' (qℕ-⊎-n∸qℕ≡qℕ-⊎-s[n'∸qℕ] qℕ≤i) (≡-sym (qℕ-⊎-n∸qℕ≡qℕ-⊎-s[n'∸qℕ] qℕ≤i)) ≡-refl

                is-right-inv : RightInverse A-setoid B-setoid to to-cong inv
                is-right-inv = change-type-trans' (≡-sym (qℕ-⊎-n∸qℕ≡qℕ-⊎-s[n'∸qℕ] qℕ≤i)) (qℕ-⊎-n∸qℕ≡qℕ-⊎-s[n'∸qℕ] qℕ≤i) ≡-refl

        half : {i : ℕ} → qℕ ≤ i → Bijection (disc-fin (suc-ℕ i)) (discrete-setoid (Fin qℕ ⊎ (Fin (suc-ℕ (i ∸ qℕ)))))
        half qℕ≤i = (spin-bij qℕ≤i) ∘-bijection (split-bij (≤-trans qℕ≤i n≤sn)) ∘-bijection (twist-bij (≤-trans qℕ≤i n≤sn))

        qℕ≤n' : qℕ ≤ n'
        qℕ≤n' = s≤s⁻¹ (toℕ<n q)

        qℕ≤n : qℕ ≤ n
        qℕ≤n = ≤-trans qℕ≤n' n≤sn

        first-half : Bijection (disc-fin n) (discrete-setoid (Fin qℕ ⊎ (Fin (suc-ℕ (n' ∸ qℕ)))))
        first-half = half qℕ≤n'

        first-half-fz : first-half .Bijection.to q ≡ inj₂ zero
        first-half-fz = ((spin-bij qℕ≤n' .Bijection.to) ∘ splitAt qℕ {n = n ∸ qℕ} ∘ (fin-twist {i = n} qℕ≤n)) q ≡ inj₂ zero ∋
            ((spin-bij qℕ≤n' .Bijection.to) ∘ splitAt qℕ {n = n ∸ qℕ} ∘ (fin-twist {i = n} qℕ≤n)) q
                ≡⟨ cong (spin-bij qℕ≤n' .Bijection.to) (
                    splitAt qℕ (fin-twist qℕ≤n q)
                        ≡⟨ splitAt-≥ {m = qℕ} (fin-twist qℕ≤n q) (≤-reflexive (≡-sym twist-qℕ≡qℕ)) ⟩
                    inj₂ (fromℕ< {m = toℕ (fin-twist qℕ≤n q) ∸ qℕ} {n = n ∸ qℕ} (∸-monoˡ-< {m = toℕ (fin-twist qℕ≤n q)} {n = qℕ} {o = n} (<-≤-trans (toℕ<n (fin-twist qℕ≤n q)) (≤-reflexive (twist-id qℕ≤n))) (≤-reflexive (≡-sym twist-qℕ≡qℕ))))
                        ≡⟨ cong inj₂ (fromℕ<-cong (toℕ (fin-twist qℕ≤n q) ∸ qℕ) 0 twist-qℕ∸qℕ≡0 (≤-<-trans (≤-reflexive twist-qℕ∸qℕ≡0) (<-≤-trans (s≤s z≤n) (≤-reflexive (n∸qℕ-spin qℕ≤n')))) (<-≤-trans (s≤s z≤n) (≤-reflexive (n∸qℕ-spin qℕ≤n')))) ⟩
                    inj₂ (fromℕ< {m = 0} {n = n ∸ qℕ} (<-≤-trans (s≤s z≤n) (≤-reflexive (n∸qℕ-spin qℕ≤n'))))
                        ≡⟨ cong inj₂ (≡-trans (≡-sym (change-type-trans' (cong Fin (≡-sym (n∸qℕ-spin qℕ≤n'))) (cong Fin (n∸qℕ-spin qℕ≤n')) ≡-refl)) (cong (change-type (cong Fin (n∸qℕ-spin qℕ≤n'))) (fromℕ<-cong₂ 0 0 (n ∸ qℕ) (suc-ℕ (n' ∸ qℕ)) ≡-refl (≡-sym (n∸qℕ-spin qℕ≤n')) (<-≤-trans (s≤s z≤n) (≤-reflexive (n∸qℕ-spin qℕ≤n'))) (s≤s z≤n)))) ⟩
                    inj₂ (change-type (cong Fin (n∸qℕ-spin qℕ≤n')) zero)
                        ≡⟨ ≡-trans (change-type-output-dependence-commute {a = lzero} {b = lzero} {c = lzero} {A = ℕ} Fin (λ _ i → Fin qℕ ⊎ typeOf i) inj₂ (n∸qℕ-spin qℕ≤n') zero) (change-type-proof-irrelevance (cong₂-dependent Fin (λ z i → Fin qℕ ⊎ typeOf i) (n∸qℕ-spin qℕ≤n') ≡-refl) (≡-sym (qℕ-⊎-n∸qℕ≡qℕ-⊎-s[n'∸qℕ] qℕ≤n'))) ⟩
                    change-type (≡-sym (qℕ-⊎-n∸qℕ≡qℕ-⊎-s[n'∸qℕ] qℕ≤n')) (inj₂ zero)
                        ∎
                ) ⟩
            (spin-bij qℕ≤n' .Bijection.to) (change-type (≡-sym (qℕ-⊎-n∸qℕ≡qℕ-⊎-s[n'∸qℕ] qℕ≤n')) (inj₂ zero)) ≡⟨ change-type-trans' (≡-sym (qℕ-⊎-n∸qℕ≡qℕ-⊎-s[n'∸qℕ] qℕ≤n')) (qℕ-⊎-n∸qℕ≡qℕ-⊎-s[n'∸qℕ] qℕ≤n') ≡-refl ⟩
            inj₂ zero ∎
            where
                open ≡-Reasoning

                twist-qℕ≡qℕ : toℕ (fin-twist qℕ≤n q) ≡ qℕ
                twist-qℕ≡qℕ = change-type-input-dependence-irrelevance Fin toℕ (≡-sym (twist-id qℕ≤n)) q

                twist-qℕ∸qℕ≡0 : toℕ (fin-twist qℕ≤n q) ∸ qℕ ≡ 0
                twist-qℕ∸qℕ≡0 = ≡-trans (cong (_∸ qℕ) twist-qℕ≡qℕ) (n∸n≡0 qℕ)

        first-half-mod : Bijection (property-subset-setoid (discrete-setoid (Fin n)) (λ i → i ≢ q)) (⊎-setoid (discrete-setoid (Fin qℕ)) (property-subset-setoid (discrete-setoid (Fin (suc-ℕ (n' ∸ qℕ)))) (λ x → x ≢ zero)))
        first-half-mod = record {
            to = to;
            cong = to-cong;
            bijective = injective , surjective
            }
            where
                open ≡-Reasoning
                A-setoid = property-subset-setoid (discrete-setoid (Fin n)) (λ i → i ≢ q)
                B-setoid = ⊎-setoid (discrete-setoid (Fin qℕ)) (property-subset-setoid (discrete-setoid (Fin (suc-ℕ (n' ∸ qℕ)))) (λ x → x ≢ zero))
                A = A-setoid .Setoid.Carrier
                B = B-setoid .Setoid.Carrier

                _~_ : Rel A lzero
                _~_ = A-setoid .Setoid._≈_
                _≈_ : Rel B lzero
                _≈_ = B-setoid .Setoid._≈_

                old-to : Fin n → Fin qℕ ⊎ Fin (suc-ℕ (n' ∸ qℕ))
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
                    old-to q ≡⟨ first-half-fz ⟩
                    inj₂ zero       ∎
                    ) of λ ()) , thing
                    where
                        thing : ∀ {z} → z ~ (i , λ i≡fz → case (
                            inj₁ x          ≡⟨ ≡-sym (pf ≡-refl) ⟩
                            old-to i        ≡⟨ cong old-to i≡fz ⟩
                            old-to q ≡⟨ first-half-fz ⟩
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
                    old-to q ≡⟨ first-half-fz ⟩
                    inj₂ zero ∎
                    ))) , thing
                    where
                        thing : ∀ {z} → z ~ (i , λ i≡fz → x≢z (inj₂-cancel x zero (
                            inj₂ x ≡⟨ ≡-sym (pf ≡-refl) ⟩
                            old-to i ≡⟨ cong old-to i≡fz ⟩
                            old-to q ≡⟨ first-half-fz ⟩
                            inj₂ zero ∎
                            ))) → to z ≈ (inj₂ (x , x≢z))
                        thing {.i , i≢fz} ≡-refl with first-half .Bijection.to i | inspect (first-half .Bijection.to) i
                        ... | inj₁ y | [ to-i≡y₁ ] = ⊥-elim (case ≡-trans (≡-sym to-i≡y₁) (pf ≡-refl) of λ ())
                        ... | inj₂ zero | [ to-i≡z₂ ] = ⊥-elim (i≢fz (old-injective (≡-trans to-i≡z₂ (≡-sym first-half-fz))))
                        ... | inj₂ (suc y) | [ to-i≡y₂ ] = rel₂ (inj₂-cancel (suc y) x (≡-trans (≡-sym to-i≡y₂) (pf ≡-refl)))

        oops-property-bij : Bijection (⊎-setoid (discrete-setoid (Fin qℕ)) (property-subset-setoid (discrete-setoid (Fin (suc-ℕ (n' ∸ qℕ)))) (λ x → x ≢ zero))) (discrete-setoid (Fin qℕ ⊎ Σ (Fin (suc-ℕ (n' ∸ qℕ))) λ x → x ≢ zero))
        oops-property-bij = record {
            to = id;
            cong = to-cong;
            bijective = both-inv→bijective A-setoid B-setoid to to-cong (inv , inv-cong , is-left-inv , is-right-inv)
            }
            where
                A-setoid = ⊎-setoid (discrete-setoid (Fin qℕ)) (property-subset-setoid (discrete-setoid (Fin (suc-ℕ (n' ∸ qℕ)))) (λ x → x ≢ zero))
                B-setoid = discrete-setoid (Fin qℕ ⊎ Σ (Fin (suc-ℕ (n' ∸ qℕ))) λ x → x ≢ zero)
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

        del-bij : Bijection (discrete-setoid (Fin qℕ ⊎ Fin (n' ∸ qℕ))) (discrete-setoid (Fin qℕ ⊎ Σ (Fin (suc-ℕ (n' ∸ qℕ))) λ x → x ≢ zero))
        del-bij = record {
            to = to;
            cong = to-cong;
            bijective = both-inv→bijective A-setoid B-setoid to to-cong (inv , inv-cong , is-left-inv , is-right-inv)
            }
            where
                A = Fin qℕ ⊎ Fin (n' ∸ qℕ)
                B = Fin qℕ ⊎ Σ (Fin (suc-ℕ (n' ∸ qℕ))) λ x → x ≢ zero
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

        full-bijection : Bijection (property-subset-setoid (disc-fin n) (λ i → i ≢ q)) (disc-fin n')
        full-bijection = (invert-bijection (twist-bij qℕ≤n')) ∘-bijection (invert-bijection (split-bij qℕ≤n')) ∘-bijection (invert-bijection del-bij) ∘-bijection oops-property-bij ∘-bijection first-half-mod
