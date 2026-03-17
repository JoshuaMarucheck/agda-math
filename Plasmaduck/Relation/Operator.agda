open import Level using (Level; _⊔_; Lift; lift; Setω) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; inspect; cong; Reveal_·_is_; [_]) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Binary.Bundles using (Setoid)
open import Function using (_∘_; flip; id; Bijective; Injective; Surjective; Congruent; Bijection; Injection; Surjection)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Nat using (ℕ; _+_) renaming (zero to zero-ℕ; suc to suc-ℕ)
open import Data.Fin using (Fin) renaming (zero to zero-Fin; suc to suc-Fin)
open import Data.Vec using (Vec; lookup; []; _∷_; _∷ʳ_; _++_)
open import Relation.Binary using (Reflexive; Symmetric; Transitive; IsDecPreorder; Irreflexive; Trans; Rel; IsEquivalence; _Respects₂_; _Respectsˡ_; _Respectsʳ_; Decidable; IsStrictPartialOrder; Trichotomous; Tri; tri<; tri≈; tri>; Asymmetric; IsDecStrictPartialOrder)

open import Plasmaduck.Util.Case using (case_of_)
open import Plasmaduck.Relation.Equivalence using (≡-isEquivalence; all-respects-≡)
open import Plasmaduck.Relation.Order using (Comparable; ComparableAt; show-total-order)
open import Plasmaduck.Relation.OrderHelpers using (WeakTri; cmp₁; cmp₂; cmp₃; _Extends_)
open import Plasmaduck.Relation.RelationVector using (RelTree; leaf; branch; branch-type; trans-branch; map-branch; trans-flatten-branch; lift-rel-to-branch; flatten-branches; pop-first; pop-last)
open import Plasmaduck.Function.Function using (_↔_)
open import Plasmaduck.Counting.Counting using (AtLeastSize)



module Plasmaduck.Relation.Operator {a ℓ : Level} (A-setoid : Setoid a ℓ) where

open Setoid using (Carrier)

A : Set a
A = A-setoid .Carrier

_≈_ : Rel A ℓ
_≈_ = A-setoid .Setoid._≈_

≈-eq : IsEquivalence _≈_
≈-eq = A-setoid .Setoid.isEquivalence

open IsEquivalence ≈-eq renaming (refl to ≈-refl; sym to ≈-sym; trans to ≈-trans)
open IsEquivalence using (refl; sym; trans)

variable
    ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ : Level



-- Reflexive wrt the ambient equality relation
Refl : Rel A ℓ₂ → Set (a ⊔ ℓ ⊔ ℓ₂)
Refl _~_ = ∀ {x y} → x ≈ y → x ~ y

SameRel : Rel A ℓ₂ → Rel A ℓ₃ → Set (a ⊔ ℓ₂ ⊔ ℓ₃)
SameRel _#_ _#'_ = (_#'_ Extends _#_) × (_#_ Extends _#'_)

-- Congruent wrt the ambient equality relation, which is necessary for some of the proofs
CongruentRel : Rel A ℓ₂ → Set (a ⊔ ℓ ⊔ ℓ₂)
CongruentRel _~_ = ∀ {x₁ x₂ y₁ y₂ : A} → (x₁ ≈ x₂) → (y₁ ≈ y₂) → (x₁ ~ y₁) → (x₂ ~ y₂)


SameRel-refl : {_#_ : Rel A ℓ₁} → SameRel _#_ _#_
SameRel-refl = id , id

SameRel-sym : {_#_ : Rel A ℓ₁} {_#'_ : Rel A ℓ₂} → SameRel _#_ _#'_ → SameRel _#'_ _#_
SameRel-sym (#→#' , #'→#) = #'→# , #→#'

SameRel-trans : {_#_ : Rel A ℓ₁} {_#'_ : Rel A ℓ₂} {_#''_ : Rel A ℓ₃} → SameRel _#_ _#'_ → SameRel _#'_ _#''_ → SameRel _#_ _#''_
SameRel-trans {#} {#'} {#''} (#→#' , #'→#) (#'→#'' , #''→#') = #'→#'' ∘ #→#' , #'→# ∘ #''→#'

-- Weaker than the above for sym and trans. Use the above if the relation levels are not all the same.
SameRel-eq : IsEquivalence (SameRel {ℓ₂ = ℓ₂} {ℓ₃ = ℓ₂})
SameRel-eq = record {
    refl = SameRel-refl;
    sym = SameRel-sym;
    trans = SameRel-trans
    }


-------------------------------
--- Properties of Operators ---
-------------------------------

-- Sometimes, the operators are polymorphic over level. This makes the below definitions exotic sometimes,
-- since operators usually need to be able to change the level of the set the relation is over.

-- Proof that the operator finds the minimal relation
-- (that is, a minimum of things are related (in the partial order of orders on A))
-- such that the property holds.
MinimalOperator :
    (ℓ₂ : Level) →
    (property : Rel A ℓ₃ → Set ℓ₅) →
    (operator : Rel A ℓ₂ → Rel A ℓ₃) →
    Set (a ⊔ lsuc ℓ₂ ⊔ lsuc ℓ₃ ⊔ ℓ₅)
MinimalOperator {ℓ₃ = ℓ₃} ℓ₂ property operator = (_#_ : Rel A ℓ₂) → (_#'_ : Rel A ℓ₃) → _#'_ Extends _#_ → property _#'_ → _#'_ Extends (operator _#_)

OperatorPreserves :
    (property : Rel A ℓ₁ → Set ℓ₅) →
    (operator : Rel A ℓ₁ → Rel A ℓ₁) →
    Set (a ⊔ lsuc ℓ₁ ⊔ ℓ₅)
OperatorPreserves {ℓ₁ = ℓ₁} property operator = (_#_ : Rel A ℓ₁) → property _#_ → property (operator _#_)

ExtensiveOperator :
    (ℓ₂ : Level) →
    (operator : Rel A ℓ₂ → Rel A ℓ₃) →
    Set (a ⊔ lsuc ℓ₂ ⊔ ℓ₃)
ExtensiveOperator ℓ₂ operator = (_#_ : Rel A ℓ₂) → operator _#_ Extends _#_

IdempotentOperator :
    (ℓ₂ : Level) →
    (operator : Rel A ℓ₂ → Rel A ℓ₂) →
    Set (a ⊔ lsuc ℓ₂)
IdempotentOperator ℓ₂ operator = (_#_ : Rel A ℓ₂) → SameRel (operator (operator _#_)) (operator _#_)

CommutativeOperators :
    (ℓ₂ : Level) →
    (operator₁ operator₂ : Rel A ℓ₂ → Rel A ℓ₂) →
    Set (a ⊔ ℓ ⊔ lsuc ℓ₂)
CommutativeOperators ℓ₂ op₁ op₂ = {_#_ : Rel A ℓ₂} → (CongruentRel _#_) → SameRel (op₁ (op₂ _#_)) (op₂ (op₁ _#_))

TransferrableProperty :
    (ℓ₂ : Level) →
    (property : Rel A ℓ₂ → Set ℓ₅) →
    Set (a ⊔ ℓ₅ ⊔ lsuc ℓ₂)
TransferrableProperty ℓ₂ property = {_#_ _#'_ : Rel A ℓ₂} → SameRel _#_ _#'_ → property _#_ → property _#'_

SameRelCongruentOperator' :
    (ℓ₂ ℓ₄ : Level) →
    {l : Level → Level} →
    (operator : {b : Level} → Rel A b → Rel A (l b)) →
    Set (a ⊔ lsuc ℓ₂ ⊔ lsuc ℓ₄ ⊔ l ℓ₂ ⊔ l ℓ₄)
SameRelCongruentOperator' ℓ₂ ℓ₄ op = {_#_ : Rel A ℓ₂} {_#'_ : Rel A ℓ₄} → SameRel _#_ _#'_ → (op _#'_) Extends (op _#_)

SameRelCongruentOperator :
    (ℓ₂ ℓ₄ : Level) →
    {l : Level → Level} →
    (operator : {b : Level} → Rel A b → Rel A (l b)) →
    Set (a ⊔ lsuc ℓ₂ ⊔ lsuc ℓ₄ ⊔ l ℓ₂ ⊔ l ℓ₄)
SameRelCongruentOperator ℓ₂ ℓ₄ op = {_#_ : Rel A ℓ₂} {_#'_ : Rel A ℓ₄} → SameRel _#_ _#'_ → SameRel (op _#_) (op _#'_)

prove-rel-congruence :
    {l : Level → Level} →
    (operator : {b : Level} → Rel A b → Rel A (l b)) →
    ({ℓ₂ ℓ₄ : Level} → SameRelCongruentOperator' ℓ₂ ℓ₄ operator) →
    ({ℓ₂ ℓ₄ : Level} → SameRelCongruentOperator ℓ₂ ℓ₄ operator)
prove-rel-congruence op op-rel-cong #-same-rel-#' = op-rel-cong #-same-rel-#' , op-rel-cong (SameRel-sym #-same-rel-#')


-------------------------
--- Congruent Closure ---
-------------------------

congruent-closure : Rel A ℓ₂ → Rel A (a ⊔ ℓ ⊔ ℓ₂)
congruent-closure _#_ x y = Σ A λ x₁ → Σ A λ y₁ → x₁ ≈ x × y₁ ≈ y × x₁ # y₁

congruent-closure-is-congruent : (_#_ : Rel A ℓ₂) → CongruentRel (congruent-closure _#_)
congruent-closure-is-congruent _#_ {x₀} {x₂} {y₀} {y₂} x₀≈x₂ y₀≈y₂ (x₁ , y₁ , x₁≈x₀ , y₁≈y₀ , x₁#y₁) = x₁ , y₁ , ≈-trans x₁≈x₀ x₀≈x₂ , ≈-trans y₁≈y₀ y₀≈y₂ , x₁#y₁

congruent-closure-is-minimal : MinimalOperator ℓ₂ CongruentRel congruent-closure
congruent-closure-is-minimal _#_ _#'_ #'-extends-# #'-cong (x₁ , y₁ , x₁≈x , y₁≈y , x₁#y₁)  = #'-cong x₁≈x y₁≈y (#'-extends-# x₁#y₁)

congruent-closure-is-extensive : ExtensiveOperator ℓ₂ congruent-closure
congruent-closure-is-extensive _#_ {x} {y} x#y = x , y , ≈-refl , ≈-refl , x#y

congruent-closure-is-idempotent : IdempotentOperator (a ⊔ ℓ ⊔ ℓ₂) congruent-closure
congruent-closure-is-idempotent _#_ = (λ {
        {x} {y} (x₁ , y₁ , x₁≈x , y₁≈y , x₁#congy₁) → congruent-closure-is-congruent _#_ x₁≈x y₁≈y x₁#congy₁
    }) , congruent-closure-is-extensive (congruent-closure _#_)

congruent-closure-is-rel-congruent : SameRelCongruentOperator (a ⊔ ℓ₁) (a ⊔ ℓ₂) congruent-closure
congruent-closure-is-rel-congruent = prove-rel-congruence congruent-closure λ { (#→#' , #'→#) {x} {y} (x' , y' , x'≈x , y'≈y , x'#y') → x' , y' , x'≈x , y'≈y , #→#' x'#y' }

congruence-transferrable : TransferrableProperty ℓ₂ CongruentRel
congruence-transferrable (#→#' , #'→#) #-cong {x₁} {x₂} {y₁} {y₂} x₁≈x₂ y₁≈y₂ x₁#'y₁ = #→#' (#-cong x₁≈x₂ y₁≈y₂ (#'→# x₁#'y₁))


-------------------------
--- Reflexive Closure ---
-------------------------

reflexive-closure : Rel A ℓ₂ → Rel A (ℓ ⊔ ℓ₂)
reflexive-closure _#_ x y = x # y ⊎ x ≈ y

reflexive-closure-is-reflexive : (_#_ : Rel A ℓ₂) → Refl (reflexive-closure _#_)
reflexive-closure-is-reflexive _#_ {x} {y} x≈y = inj₂ x≈y

reflexive-closure-is-minimal : MinimalOperator ℓ₂ Refl reflexive-closure
reflexive-closure-is-minimal _#_ _#'_ #'-extends-# #'-refl {x} {y} (inj₁ x#y) = #'-extends-# x#y
reflexive-closure-is-minimal _#_ _#'_ #'-extends-# #'-refl {x} {y} (inj₂ x≈y) = #'-refl x≈y

reflexive-closure-is-extensive : ExtensiveOperator ℓ₂ reflexive-closure
reflexive-closure-is-extensive _#_ = inj₁

reflexive-closure-is-idempotent : IdempotentOperator (ℓ ⊔ ℓ₂) reflexive-closure
reflexive-closure-is-idempotent _#_ = (λ {x} {y} → λ {(inj₁ rel) → rel ; (inj₂ x≈y) → inj₂ x≈y }) , inj₁

reflexive-closure-is-rel-congruent : SameRelCongruentOperator (a ⊔ ℓ₂) (a ⊔ ℓ₃) reflexive-closure
reflexive-closure-is-rel-congruent = prove-rel-congruence reflexive-closure λ { (#→#' , #'→#) {x} {y} → λ {
    (inj₁ x#y) → inj₁ (#→#' x#y);
    (inj₂ x≈y) → inj₂ x≈y
    }}

reflexivity-transferrable : TransferrableProperty ℓ₂ Refl
reflexivity-transferrable (#→#' , #'→#) #-refl {x} {y} x≈y = #→#' (#-refl x≈y)


-------------------------
--- Symmetric Closure ---
-------------------------

symmetric-closure : Rel A ℓ₂ → Rel A ℓ₂
symmetric-closure _#_ x y = x # y ⊎ y # x

symmetric-closure-is-symmetric : (_#_ : Rel A ℓ₂) → Symmetric (symmetric-closure _#_)
symmetric-closure-is-symmetric _#_ {x} {y} (inj₁ x#y) = inj₂ x#y
symmetric-closure-is-symmetric _#_ {x} {y} (inj₂ y#x) = inj₁ y#x

symmetric-closure-is-minimal : MinimalOperator ℓ₂ Symmetric symmetric-closure
symmetric-closure-is-minimal _#_ _#'_ #'-extends-# #'-sym {x} {y} (inj₁ x#y) = #'-extends-# x#y
symmetric-closure-is-minimal _#_ _#'_ #'-extends-# #'-sym {x} {y} (inj₂ y#x) = #'-sym (#'-extends-# y#x)

symmetric-closure-is-extensive : ExtensiveOperator ℓ₂ symmetric-closure
symmetric-closure-is-extensive _#_ = inj₁

symmetric-closure-is-idempotent : IdempotentOperator ℓ₂ symmetric-closure
symmetric-closure-is-idempotent _#_ = (λ {x} {y} → λ {
    (inj₁ rel) → rel;
    (inj₂ (inj₁ y#x)) → inj₂ y#x;
    (inj₂ (inj₂ x#y)) → inj₁ x#y }) , inj₁

symmetric-closure-is-rel-congruent : SameRelCongruentOperator (a ⊔ ℓ₂) (a ⊔ ℓ₃) symmetric-closure
symmetric-closure-is-rel-congruent = prove-rel-congruence symmetric-closure λ { (#→#' , #'→#) → λ {
    (inj₁ x#y) → inj₁ (#→#' x#y);
    (inj₂ y#x) → inj₂ (#→#' y#x)
    }}

symmetry-transferrable : TransferrableProperty ℓ₂ Symmetric
symmetry-transferrable (#→#' , #'→#) #-sym {x} {y} x#'y = #→#' (#-sym (#'→# x#'y))


--------------------------
--- Transitive Closure ---
--------------------------

transitive-closure : Rel A ℓ₂ → Rel A (a ⊔ ℓ₂)
transitive-closure = branch-type

transitive-closure-is-transitive : (_#_ : Rel A ℓ₂) → Transitive (transitive-closure _#_)
transitive-closure-is-transitive _#_ = trans-branch _#_

transitive-closure-is-minimal : MinimalOperator ℓ₂ Transitive transitive-closure
transitive-closure-is-minimal _#_ _#'_ #'-extends-# #'-trans {x} {y} x↔y = trans-flatten-branch _#'_ #'-trans (map-branch id #'-extends-# x↔y)

transitive-closure-is-extensive : ExtensiveOperator ℓ₂ transitive-closure
transitive-closure-is-extensive = lift-rel-to-branch

transitive-closure-is-idempotent : IdempotentOperator (a ⊔ ℓ₂) transitive-closure
transitive-closure-is-idempotent _#_ = flatten-branches , lift-rel-to-branch (transitive-closure _#_)

transitive-closure-is-rel-congruent : SameRelCongruentOperator (a ⊔ ℓ₂) (a ⊔ ℓ₃) transitive-closure
transitive-closure-is-rel-congruent = prove-rel-congruence transitive-closure λ { (#→#' , #'→#) x#↔y → map-branch id #→#' x#↔y }

transitivity-transferrable : TransferrableProperty ℓ₂ Transitive
transitivity-transferrable (#→#' , #'→#) #-trans {x} {y} {z} x#'y y#'z = #→#' (#-trans (#'→# x#'y) (#'→# y#'z))


------------------------
--- Joint properties ---
------------------------

refl-sym-commute : CommutativeOperators (ℓ ⊔ ℓ₂) reflexive-closure symmetric-closure
refl-sym-commute {_#_ = _#_} #-cong = (λ {
    (inj₁ (inj₁ x#y)) → inj₁ (inj₁ x#y);
    (inj₁ (inj₂ y#x)) → inj₂ (inj₁ y#x);
    (inj₂ x≈y) → inj₁ (inj₂ x≈y)
    }) , (λ {
    (inj₁ (inj₁ x#y)) → inj₁ (inj₁ x#y);
    (inj₁ (inj₂ x≈y)) → inj₂ x≈y;
    (inj₂ (inj₁ y#x)) → inj₁ (inj₂ y#x);
    (inj₂ (inj₂ y≈x)) → inj₂ (≈-eq .sym y≈x)
    })

squeeze-reflexive-branch :
    {_#_ : Rel A ℓ₁} →
    (CongruentRel _#_) →
    {x y : A} →
    transitive-closure (reflexive-closure _#_) x y →
    reflexive-closure (transitive-closure _#_) x y
squeeze-reflexive-tree :
    {_#_ : Rel A ℓ₁} →
    (CongruentRel _#_) →
    {x y : A} →
    RelTree (reflexive-closure _#_) x y →
    reflexive-closure (transitive-closure _#_) x y
squeeze-reflexive-branch #-cong {x = w} {z} (x , y , wTx , _ , yTz) with squeeze-reflexive-tree #-cong wTx | squeeze-reflexive-tree #-cong yTz
squeeze-reflexive-branch #-cong {x = w} {z} (x , y , _ , inj₁ x#y , _) | inj₁ wBx | inj₁ yBz = inj₁ (x , y , branch wBx , x#y , branch yBz)
squeeze-reflexive-branch #-cong {x = w} {z} (x , y , _ , inj₁ x#y , _) | inj₁ wBx | inj₂ y≈z = inj₁ (x , z , branch wBx , #-cong (≈-eq .refl) y≈z x#y , leaf z)
squeeze-reflexive-branch #-cong {x = w} {z} (x , y , _ , inj₁ x#y , _) | inj₂ w≈x | inj₁ yBz = inj₁ (w , y , leaf w , #-cong (sym ≈-eq w≈x) (refl ≈-eq) x#y , branch yBz)
squeeze-reflexive-branch #-cong {x = w} {z} (x , y , _ , inj₁ x#y , _) | inj₂ w≈x | inj₂ y≈z = inj₁ (w , z , leaf w , #-cong (sym ≈-eq w≈x) y≈z x#y , leaf z)
squeeze-reflexive-branch {_#_ = _#_} #-cong {x = w} {z} (x , y , _ , inj₂ x≈y , _) | inj₁ wBx | inj₁ yBz with pop-first _#_ yBz
...                                                                                                         | q , y#q , qTz = inj₁ (x , q , branch wBx , #-cong (sym ≈-eq x≈y) (refl ≈-eq) y#q , qTz)
squeeze-reflexive-branch {_#_ = _#_} #-cong {x = w} {z} (x , y , _ , inj₂ x≈y , _) | inj₁ wBx | inj₂ y≈z with pop-last _#_ wBx
...                                                                                                         | q , wTq , q#x = inj₁ (q , z , wTq , #-cong (refl ≈-eq) (trans ≈-eq x≈y y≈z) q#x , leaf z)
squeeze-reflexive-branch {_#_ = _#_} #-cong {x = w} {z} (x , y , _ , inj₂ x≈y , _) | inj₂ w≈x | inj₁ yBz with pop-first _#_ yBz
...                                                                                                         | q , y#q , qTz = inj₁ (w , q , leaf w , #-cong (sym ≈-eq (trans ≈-eq w≈x x≈y)) (refl ≈-eq) y#q , qTz)
squeeze-reflexive-branch #-cong {x = w} {z} (x , y , _ , inj₂ x≈y , _) | inj₂ w≈x | inj₂ y≈z = inj₂ (trans ≈-eq (trans ≈-eq w≈x x≈y) y≈z)
squeeze-reflexive-tree #-cong (leaf x) = inj₂ (≈-eq .refl)
squeeze-reflexive-tree #-cong (branch b) = squeeze-reflexive-branch #-cong b

refl-trans-commute : CommutativeOperators (a ⊔ ℓ ⊔ ℓ₂) reflexive-closure transitive-closure
refl-trans-commute {_#_ = _#_} #-cong = (λ {
    (inj₁ xBy) → map-branch id inj₁ xBy;
    (inj₂ x≈y) → lift-rel-to-branch (reflexive-closure _#_) (inj₂ x≈y)
    }) , squeeze-reflexive-branch #-cong

{-
    Symmetric and transitive closure are not commutative, as long as A has at least 3 distinct things in it.
    Consider the relation _<_ on {a, b, c} with a < b and a < c.
    Transitive closure of symmetric closure of _<_ would make everything related to everything.
    Symmetric closure of transitive closure would not relate a and c, though all other relations would hold.
    In particular, Symmetric closure of transitive closure is not transitive, and thus symmetric closure does not necessarily preserve transitivity.
-}

sym-not-trans-preserving' : AtLeastSize A-setoid 3 → (ℓ₁ : Level) → Σ (Rel A (a ⊔ ℓ ⊔ ℓ₁)) λ _#_ → CongruentRel _#_ × Transitive _#_ × ¬ Transitive (symmetric-closure _#_)
sym-not-trans-preserving' inj ℓ₁ = _<_ , congruent-closure-is-congruent _<-base_ , <-trans , ¬-~-trans
    where
        f : Fin 3 → A
        f = inj .Injection.to

        f-inj : Injective _≡_ _≈_ f
        f-inj = inj .Injection.injective


        i = f zero-Fin
        j = f (suc-Fin zero-Fin)
        k = f (suc-Fin (suc-Fin zero-Fin))

        data _<-base_ : Rel A ℓ₁ where
            i<j : i <-base j
            i<k : i <-base k

        _<_ : Rel A (a ⊔ ℓ ⊔ ℓ₁)
        _<_ = congruent-closure _<-base_

        ¬j< : ∀ x → ¬ j < x
        ¬j< x (.i , .j , i≈j , j≈x , i<j) with f-inj i≈j
        ... | ()
        ¬j< x (.i , .k , i≈j , k≈x , i<k) with f-inj i≈j
        ... | ()

        ¬k< : ∀ x → ¬ k < x
        ¬k< x (.i , .j , i≈k , j≈x , i<j) with f-inj i≈k
        ... | ()
        ¬k< x (.i , .k , i≈k , k≈x , i<k) with f-inj i≈k
        ... | ()

        <-trans : Transitive _<_
        <-trans {x} {y} {z} (.i , .j , i≈x , j≈y , i<j) (.i , .j , i≈y , j≈z , i<j) = case f-inj (≈-trans i≈y (≈-sym j≈y)) of λ ()
        <-trans {x} {y} {z} (.i , .j , i≈x , j≈y , i<j) (.i , .k , i≈y , k≈z , i<k) = case f-inj (≈-trans i≈y (≈-sym j≈y)) of λ ()
        <-trans {x} {y} {z} (.i , .k , i≈x , k≈y , i<k) (.i , .j , i≈y , j≈z , i<j) = case f-inj (≈-trans i≈y (≈-sym k≈y)) of λ ()
        <-trans {x} {y} {z} (.i , .k , i≈x , k≈y , i<k) (.i , .k , i≈y , k≈z , i<k) = case f-inj (≈-trans i≈y (≈-sym k≈y)) of λ ()

        _~_ : Rel A (a ⊔ ℓ ⊔ ℓ₁)
        _~_ = symmetric-closure _<_

        j~i : j ~ i
        j~i = inj₂ (i , j , ≈-refl , ≈-refl , i<j)

        i~k : i ~ k
        i~k = inj₁ (i , k , ≈-refl , ≈-refl , i<k)

        j≁k : ¬ j ~ k
        j≁k (inj₁ (.i , .j , i≈j , _ , i<j)) = case f-inj i≈j of λ ()
        j≁k (inj₁ (.i , .k , i≈j , _ , i<k)) = case f-inj i≈j of λ ()
        j≁k (inj₂ (.i , .j , i≈k , _ , i<j)) = case f-inj i≈k of λ ()
        j≁k (inj₂ (.i , .k , i≈k , _ , i<k)) = case f-inj i≈k of λ ()

        ¬-~-trans : ¬ Transitive _~_
        ¬-~-trans ~-trans = j≁k (~-trans j~i i~k)

sym-not-trans-preserving : AtLeastSize A-setoid 3 → (ℓ₁ : Level) → ¬ (OperatorPreserves {ℓ₁ = a ⊔ ℓ ⊔ ℓ₁} Transitive symmetric-closure)
sym-not-trans-preserving inj ℓ₁ preserving with sym-not-trans-preserving' inj ℓ₁
...                                           |  _<_ , _ , <-trans , ¬-~-trans = ¬-~-trans (preserving _<_ <-trans)

not-sym-trans-commute' : AtLeastSize A-setoid 3 → (ℓ₁ : Level) → Σ (Rel A (a ⊔ ℓ ⊔ ℓ₁)) λ _#_ → CongruentRel _#_ × ¬ SameRel (symmetric-closure (transitive-closure _#_)) (transitive-closure (symmetric-closure _#_))
not-sym-trans-commute' inj ℓ₁ =
    let
        _<_ , <-cong , <-trans , ¬-~-trans = sym-not-trans-preserving' inj ℓ₁
        _~_ : Rel A (a ⊔ ℓ ⊔ ℓ₁)
        _~_ = symmetric-closure _<_

        <-is-transitive-closure-< : SameRel (transitive-closure _<_) _<_
        <-is-transitive-closure-< =  transitive-closure-is-minimal _<_ _<_ id <-trans , transitive-closure-is-extensive _<_

        sym-trans-<-is-~ : SameRel (symmetric-closure (transitive-closure _<_)) _~_
        sym-trans-<-is-~ = symmetric-closure-is-rel-congruent {ℓ₂ = ℓ ⊔ ℓ₁} {ℓ₃ = ℓ ⊔ ℓ₁} (<-is-transitive-closure-<)

    in _<_ , <-cong , λ sym-trans-comm-same-rel → let
        ~-trans' : Transitive (symmetric-closure (transitive-closure _<_))
        ~-trans' = transitivity-transferrable {ℓ₂ = a ⊔ ℓ ⊔ ℓ₁} (SameRel-eq .sym sym-trans-comm-same-rel) (transitive-closure-is-transitive _~_)

        ~-trans : Transitive _~_
        ~-trans = transitivity-transferrable sym-trans-<-is-~ ~-trans'
    in ¬-~-trans ~-trans

not-sym-trans-commute : AtLeastSize A-setoid 3 → ¬ CommutativeOperators (a ⊔ ℓ ⊔ ℓ₂) symmetric-closure transitive-closure
not-sym-trans-commute {ℓ₂ = ℓ₂} inj comm with not-sym-trans-commute' inj (ℓ ⊔ ℓ₂)
... | _<_ , <-cong , sym-trans-<-≢-trans-sym-< = sym-trans-<-≢-trans-sym-< (comm <-cong)
