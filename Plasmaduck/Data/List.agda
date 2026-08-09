open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; cong; cong-app; refl; sym; trans; inspect; [_])
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open import Data.Nat using (ℕ; _+_; _∸_; _≤_; _<_; s≤s⁻¹) renaming (zero to zeroℕ; suc to sucℕ)
open import Data.Nat.Properties using (≤-reflexive; ≤-refl; ≤-trans; +-comm; +-∸-assoc; ∸-mono; m≤n⇒m∸n≡0; module ≤-Reasoning)
open import Data.Fin using (Fin; fromℕ<; toℕ)
open import Data.List using (List; _∷_; []; length; lookup; drop)
open import Data.List.Properties using (length-drop)

open import Plasmaduck.Data.Nat using (n≤sn)



module Plasmaduck.Data.List where

variable
    a b c : Level
    A : Set a

open ≤-Reasoning using (begin_; step-≤) renaming (_∎ to _≤∎)

drop-lookup : (l : List A) (m n : ℕ) → .(m+n<|l| : m + n < length l) → lookup l (fromℕ< {m + n} m+n<|l|) ≡ lookup (drop m l) (fromℕ< {n} (begin
    sucℕ n              ≤⟨ ≤-reflexive (+-comm zeroℕ (sucℕ n)) ⟩
    sucℕ n + zeroℕ      ≤⟨ ≤-reflexive (sym (cong (sucℕ n +_) (m≤n⇒m∸n≡0 {m = m} ≤-refl))) ⟩
    sucℕ n + (m ∸ m)    ≤⟨ ≤-reflexive (sym (+-∸-assoc (sucℕ n) {m} {m} ≤-refl)) ⟩
    (sucℕ n + m) ∸ m    ≤⟨ ≤-refl ⟩
    sucℕ (n + m) ∸ m    ≤⟨ ≤-reflexive (cong (λ q → sucℕ q ∸ m) (+-comm n m)) ⟩
    sucℕ (m + n) ∸ m    ≤⟨ ∸-mono {sucℕ (m + n)} {length l} {m} {m} m+n<|l| ≤-refl ⟩
    length l ∸ m        ≤⟨ ≤-reflexive (sym (length-drop m l)) ⟩
    length (drop m l)   ≤∎))
drop-lookup l zeroℕ n m+n<|l| = refl
drop-lookup (x ∷ l) m@(sucℕ m') n m+n<|l| =
    lookup (x ∷ l) (fromℕ< {m + n} m+n<|l|)     ≡⟨⟩
    lookup l (fromℕ< {m' + n} (s≤s⁻¹ m+n<|l|))  ≡⟨ drop-lookup l m' n (s≤s⁻¹ m+n<|l|) ⟩
    lookup (drop m' l) (fromℕ< {n} _)           ≡⟨⟩
    lookup (drop m (x ∷ l)) (fromℕ< {n} _)      ∎
    where open ≡-Reasoning