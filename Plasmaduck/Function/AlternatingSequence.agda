open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≢_; _≡_; inspect; cong; Reveal_·_is_; [_]) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Data.Nat using (ℕ; suc; zero; _+_; _∸_; _<_; _≤_; z≤n; s≤s; s≤s⁻¹)
open import Data.Nat.Properties using (m∸n+n≡m; _≟_; ≤-total; ≤-trans)
open import Data.Vec using (Vec; _∷_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Function using (_∘_; _on_; flip; id; Injective; Surjective; Bijection; Congruent)
open import Relation.Binary using (TotalOrder; DecTotalOrder; IsTotalOrder; IsStrictTotalOrder; Reflexive; Irreflexive; Symmetric; Asymmetric; Transitive; Trans; Rel; IsEquivalence; _Respects₂_; _Respectsˡ_; _Respectsʳ_; Decidable; IsStrictPartialOrder; Trichotomous; Tri; tri<; tri≈; tri>; IsDecStrictPartialOrder)
open import Relation.Binary.Bundles using (Setoid)

open import Plasmaduck.Util.Case using (case_of_)
open import Plasmaduck.Util.TypeChange using (change-type)
open import Plasmaduck.SetoidExperiment.SetoidMachinery using (SetoidFunction; discrete-setoid; property-subset-setoid)
open import Plasmaduck.Property.Defs using (DecidableProperty)
open import Plasmaduck.Relation.Decidable using (decidable-push)
open import Plasmaduck.Number.Nat using (+-induction; ≤-induction; n≤n; n≤sn; ≤→<≡)
open import Plasmaduck.Counting.Counting using (any; fin-nat-bijection)
open import Plasmaduck.Function.Sequence using (module Repeat)


-- Trying to figure out a necessary and sufficient condition for turning two opposing surjections into a bijection
-- Though tbh, I think loops are more an injection thing, so I guess I started down that path? Oops.
-- See file CollidingSequence.agda for surjections to bijection.
module Plasmaduck.Function.AlternatingSequence where

variable
    a b c d ℓ ℓ₁ ℓ₂ ℓ₃ : Level

open Setoid using (Carrier; _≈_)
open SetoidFunction using (func; respects)

module _
    {A-setoid : Setoid a ℓ₁}
    (f-func : SetoidFunction A-setoid A-setoid)
    (x : A-setoid .Carrier)
    where
    -- x is the starting point

    private
        A = A-setoid .Carrier
        _~_ = A-setoid ._≈_
        f = f-func .func
        f-respects = f-func .respects

        open IsEquivalence (A-setoid .Setoid.isEquivalence) using (reflexive; refl; sym; trans)
        open import Relation.Binary.Reasoning.Setoid A-setoid
        open Repeat f-func using (repeat; repeat-f)

    LoopsAt : Rel ℕ ℓ₁
    LoopsAt m n = repeat x m ~ repeat x n × m ≢ n

    loops-at-sym : Symmetric LoopsAt
    loops-at-sym {m} {n} (loop-at-mn , m≢n) = sym loop-at-mn , m≢n ∘ ≡-sym

    loops-at-irrefl : Irreflexive _≡_ LoopsAt
    loops-at-irrefl ≡-refl (_ , m≢m) = m≢m ≡-refl

    loops-at-suc : (m n : ℕ) → LoopsAt m n → LoopsAt (suc m) (suc n)
    loops-at-suc m n (loops-at-mn , m≢n) = (begin
        repeat x (suc m)    ≈⟨ reflexive (≡-sym (repeat-f x m)) ⟩
        f (repeat x m)      ≈⟨ f-respects loops-at-mn ⟩
        f (repeat x n)      ≈⟨ reflexive (repeat-f x n) ⟩
        repeat x (suc n)    ∎) , λ { ≡-refl → m≢n ≡-refl }

    -- oops this one is not decidable
    LoopStartingAt : ℕ → Set ℓ₁
    LoopStartingAt m = Σ ℕ (LoopsAt m)

    loops-starting-at-suc : (m : ℕ) → LoopStartingAt m → LoopStartingAt (suc m)
    loops-starting-at-suc m (n , loops-at-mn) = suc n , loops-at-suc m n loops-at-mn

    loops-starting-at-+ : (m n : ℕ) → LoopStartingAt m → LoopStartingAt (n + m)
    loops-starting-at-+ = +-induction LoopStartingAt loops-starting-at-suc

    loops-starting-at-≤ : {m n : ℕ} → m ≤ n → LoopStartingAt m → LoopStartingAt n
    loops-starting-at-≤ = ≤-induction LoopStartingAt loops-starting-at-suc

    LoopEndAt : ℕ → Set ℓ₁
    LoopEndAt n = Σ ℕ λ i → i ≤ n × LoopsAt i n

    loop-end-at-suc : (m : ℕ) → LoopEndAt m → LoopEndAt (suc m)
    loop-end-at-suc m (n , n≤m , loop-at-nm) = suc n , s≤s n≤m , loops-at-suc n m loop-at-nm

    loop-end-at-≤ : {m n : ℕ} → m ≤ n → LoopEndAt m → LoopEndAt n
    loop-end-at-≤ = ≤-induction LoopEndAt loop-end-at-suc

    -- Apparently this is the same as LoopEndAt above
    LoopsBelow : ℕ → Set ℓ₁
    LoopsBelow n = Σ ℕ λ i → i ≤ n × Σ ℕ λ j → j ≤ n × LoopsAt i j

    loop-end-at→loops-below : (n : ℕ) → LoopEndAt n → LoopsBelow n
    loop-end-at→loops-below n (m , m≤n , loop-at-mn) = m , m≤n , n , n≤n , loop-at-mn

    loops-below→loop-end-at : (n : ℕ) → LoopsBelow n → LoopEndAt n
    loops-below→loop-end-at n (i , i≤n , j , j≤n , loop-at-ij) with ≤-total i j
    ... | inj₁ i≤j = loop-end-at-≤ j≤n (i , i≤j , loop-at-ij)
    ... | inj₂ j≤i = loop-end-at-≤ i≤n (j , j≤i , loops-at-sym loop-at-ij)

    module _
        (_~?_ : Decidable _~_)
        where

        loops-at-dec : Decidable LoopsAt
        loops-at-dec m n with repeat x m ~? repeat x n | m ≟ n
        ... | yes loop-at-mn | no m≠n = yes (loop-at-mn , m≠n)
        ... | no no-loop-at-mn | _ = no (no-loop-at-mn ∘ proj₁)
        ... | _ | yes m=n = no λ (_ , m≠n) → m≠n m=n

        loop-end-at-dec : DecidableProperty LoopEndAt
        loop-end-at-dec zero = no λ { (zero , z≤n , _ , z≢z) → z≢z ≡-refl }
        loop-end-at-dec m@(suc m') with any {A-setoid = property-subset-setoid (discrete-setoid ℕ) (_< m)} (m , fin-nat-bijection m) (LoopsAt m ∘ proj₁) (λ { ≡-refl → id }) (loops-at-dec m ∘ proj₁)
        ... | yes ((i , i<m) , loop-at-mi) = yes (i , ≤-trans n≤sn i<m , loops-at-sym loop-at-mi)
        ... | no pf = no λ { ((i , i≤m , loop-at-im@(_ , i≢m))) → pf ((i , (case ≤→<≡ i≤m of λ { (inj₁ i<m) → i<m; (inj₂ i≡m) → ⊥-elim (i≢m i≡m) })) , loops-at-sym loop-at-im) }

        loops-below-dec : DecidableProperty LoopsBelow
        loops-below-dec m with loop-end-at-dec m
        ... | yes pf = yes (loop-end-at→loops-below m pf)
        ... | no pf = no (pf ∘ loops-below→loop-end-at m)


    -- In theory, there is a tail and a loop, moving into the loop.
