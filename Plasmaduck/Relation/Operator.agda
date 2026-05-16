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
open import Plasmaduck.Counting.Counting using (AtLeastSize)
open import Plasmaduck.Relation.Defs using (module BasicDefs)



module Plasmaduck.Relation.Operator {a ℓ : Level} (A-setoid : Setoid a ℓ) where

open BasicDefs A-setoid using (CongruentRel)
open Setoid using (Carrier)

A : Set a
A = A-setoid .Carrier

_≈_ : Rel A ℓ
_≈_ = A-setoid .Setoid._≈_

≈-eq : IsEquivalence _≈_
≈-eq = A-setoid .Setoid.isEquivalence

open IsEquivalence ≈-eq renaming (refl to ≈-refl; sym to ≈-sym; trans to ≈-trans)
open IsEquivalence using (refl; sym; trans)

open import Plasmaduck.Relation.OperatorDefs A using (SameRel; SameRel-refl; SameRel-sym; SameRel-trans; SameRel-eq)

variable
    ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ : Level


-------------------------------
--- Properties of Operators ---
-------------------------------


{-
    Worth considering: what if instead of operators, we just had properties?

    A property is a set of relations. This may or may not have a minimum.
    Examples:
    - Reflexivity
    - Transitivity
    - Extends relation _#_ (for some relation _#_)
    - Relates a < b
    - Does not relate a < b
    - Every element relates to something

    Then, if the property is upward-closed so talking of minimal elements makes sense,
    We can ask if it has a minimum.

    But for example, the reflexive-closure operator below finds the
    minimum Reflexive relation that extends some relation _#_.
    Note the two properties here:
    - Reflexive
    - extends _#_
    It took the minimum of the second property and returned the minimum of their intersection.


    Also consider: two properties without a minimum may intersect and have a minimum. For example:
    let the set have 5 things {a, b, c, d, e}
    Let there be 3 relations {_#_, _#'_, _#''_}
    where
    a # b
    b # c
    b #' c
    c #' d
    c #'' d
    d #'' e
    and these are the only things that hold of these relations. Consider the two properties:
    - extends _#_ or extends _#'_
    - extends _#'_ or extends _#''_

    The first has two minimal relations (_#_ and _#'_), and since the two are not comparable, it has no minimum.
    Likewise for the second property. However, for their intersection,
    it either extends _#_ or _#'_, so in particular, it relates b ^ c
    it also either extends _#'_ or _#''_, so in particular, it relates c ^ d
    which means it extends _#'_. So since _#'_ is a valid item in this set of relations, it must be the minimum.

-}

-- Sometimes, the operators are polymorphic over level. This makes the below definitions exotic sometimes,
-- since operators usually need to be able to change the level of the set the relation is over.

-- Proof that the operator finds the minimal relation
-- (that is, a minimum of things are related (in the partial order of orders on A))
-- such that the property holds.
MinimalOperator :
    (ℓ₂ ℓ₃ : Level) →
    {lₚ : Level → Level} → (property : {ℓ' : Level} → Rel A ℓ' → Set (lₚ ℓ')) →
    {lₒ : Level → Level} → (operator : {ℓ' : Level} → Rel A ℓ' → Rel A (lₒ ℓ')) →
    Set (a ⊔ lsuc ℓ₂ ⊔ lsuc ℓ₃ ⊔ lₚ ℓ₃ ⊔ lₒ ℓ₂)
MinimalOperator ℓ₂ ℓ₃ property operator = (_#_ : Rel A ℓ₂) → (_#'_ : Rel A ℓ₃) → _#'_ Extends _#_ → property _#'_ → _#'_ Extends (operator _#_)

OperatorPreserves :
    (ℓ₁ : Level)
    {lₚ : Level → Level} → (property : {ℓ' : Level} → Rel A ℓ' → Set (lₚ ℓ')) →
    {lₒ : Level → Level} → (operator : {ℓ' : Level} → Rel A ℓ' → Rel A (lₒ ℓ')) →
    Set (a ⊔ lsuc ℓ₁ ⊔ lₚ ℓ₁ ⊔ lₚ (lₒ ℓ₁))
OperatorPreserves ℓ₁ property operator = (_#_ : Rel A ℓ₁) → property _#_ → property (operator _#_)

OperatorPreserves₂ :
    (ℓ₁ ℓ₂ : Level)
    {lₚ : Level → Level} → (property : {ℓ' : Level} → Rel A ℓ' → Set (lₚ ℓ')) →
    {lₒ : Level → Level → Level} → (operator : {ℓ' ℓ'' : Level} → Rel A ℓ' → Rel A ℓ'' → Rel A (lₒ ℓ' ℓ'')) →
    Set (a ⊔ lsuc ℓ₁ ⊔ lsuc ℓ₂ ⊔ lₚ ℓ₁ ⊔ lₚ ℓ₂ ⊔ lₚ (lₒ ℓ₁ ℓ₂))
OperatorPreserves₂ ℓ₁ ℓ₂ property operator = {_#_ : Rel A ℓ₁} → property _#_ → {_~_ : Rel A ℓ₂} → property _~_ → property (operator _#_ _~_)

ExtensiveOperator :
    (ℓ₂ : Level) →
    {lₒ : Level → Level} → (operator : {ℓ' : Level} → Rel A ℓ' → Rel A (lₒ ℓ')) →
    Set (a ⊔ lsuc ℓ₂ ⊔ lₒ ℓ₂)
ExtensiveOperator ℓ₂ operator = (_#_ : Rel A ℓ₂) → operator _#_ Extends _#_

IdempotentOperator :
    (ℓ₂ : Level) →
    {lₒ : Level → Level} → (operator : {ℓ' : Level} → Rel A ℓ' → Rel A (lₒ ℓ')) →
    Set (a ⊔ lsuc ℓ₂ ⊔ lₒ ℓ₂ ⊔ lₒ (lₒ ℓ₂))
IdempotentOperator ℓ₂ operator = (_#_ : Rel A ℓ₂) → SameRel (operator (operator _#_)) (operator _#_)

CommutativeOperators :
    (ℓ₂ : Level) →
    {l₁ : Level → Level} → (operator : {ℓ' : Level} → Rel A ℓ' → Rel A (l₁ ℓ')) →
    {l₂ : Level → Level} → (operator : {ℓ' : Level} → Rel A ℓ' → Rel A (l₂ ℓ')) →
    Set (a ⊔ ℓ ⊔ lsuc ℓ₂ ⊔ l₁ (l₂ ℓ₂) ⊔ l₂ (l₁ ℓ₂))
CommutativeOperators ℓ₂ op₁ op₂ = {_#_ : Rel A ℓ₂} → (CongruentRel _#_) → SameRel (op₁ (op₂ _#_)) (op₂ (op₁ _#_))

TransferrableProperty :
    (ℓ₂ ℓ₃ : Level) →
    {lₚ : Level → Level} → (property : {ℓ' : Level} → Rel A ℓ' → Set (lₚ ℓ')) →
    Set (a ⊔ lsuc ℓ₂ ⊔ lsuc ℓ₃ ⊔ lₚ ℓ₂ ⊔ lₚ ℓ₃)
TransferrableProperty ℓ₂ ℓ₃ property = {_#_ : Rel A ℓ₂} {_#'_ : Rel A ℓ₃} → SameRel _#_ _#'_ → property _#_ → property _#'_

SameRelCongruentOperator' :
    (ℓ₂ ℓ₄ : Level) →
    {l : Level → Level} → (operator : {b : Level} → Rel A b → Rel A (l b)) →
    Set (a ⊔ lsuc ℓ₂ ⊔ lsuc ℓ₄ ⊔ l ℓ₂ ⊔ l ℓ₄)
SameRelCongruentOperator' ℓ₂ ℓ₄ op = {_#_ : Rel A ℓ₂} {_#'_ : Rel A ℓ₄} → SameRel _#_ _#'_ → (op _#'_) Extends (op _#_)

SameRelCongruentOperator :
    (ℓ₂ ℓ₄ : Level) →
    {l : Level → Level} → (operator : {b : Level} → Rel A b → Rel A (l b)) →
    Set (a ⊔ lsuc ℓ₂ ⊔ lsuc ℓ₄ ⊔ l ℓ₂ ⊔ l ℓ₄)
SameRelCongruentOperator ℓ₂ ℓ₄ op = {_#_ : Rel A ℓ₂} {_#'_ : Rel A ℓ₄} → SameRel _#_ _#'_ → SameRel (op _#_) (op _#'_)

prove-rel-congruence :
    {l : Level → Level} → (operator : {b : Level} → Rel A b → Rel A (l b)) →
    ({ℓ₂ ℓ₄ : Level} → SameRelCongruentOperator' ℓ₂ ℓ₄ operator) →
    ({ℓ₂ ℓ₄ : Level} → SameRelCongruentOperator ℓ₂ ℓ₄ operator)
prove-rel-congruence op op-rel-cong #-same-rel-#' = op-rel-cong #-same-rel-#' , op-rel-cong (SameRel-sym #-same-rel-#')


------------
--- Lift ---
------------

lift-rel : (ℓ₃ : Level) → Rel A ℓ₂ → Rel A (ℓ₂ ⊔ ℓ₃)
lift-rel ℓ₃ _#_ x y = Lift ℓ₃ (x # y)

lift-rel-same-rel : (ℓ₃ : Level) → (_#_ : Rel A ℓ₂) → SameRel _#_ (lift-rel ℓ₃ _#_)
lift-rel-same-rel ℓ₃ _#_ = lift , Lift.lower


-------------------------
--- Congruent Closure ---
-------------------------

congruent-closure : Rel A ℓ₂ → Rel A (a ⊔ ℓ ⊔ ℓ₂)
congruent-closure _#_ x y = Σ A λ x₁ → Σ A λ y₁ → x₁ ≈ x × y₁ ≈ y × x₁ # y₁

congruent-closure-is-congruent : (_#_ : Rel A ℓ₂) → CongruentRel (congruent-closure _#_)
congruent-closure-is-congruent _#_ {x₀} {x₂} {y₀} {y₂} x₀≈x₂ y₀≈y₂ (x₁ , y₁ , x₁≈x₀ , y₁≈y₀ , x₁#y₁) = x₁ , y₁ , ≈-trans x₁≈x₀ x₀≈x₂ , ≈-trans y₁≈y₀ y₀≈y₂ , x₁#y₁

congruent-closure-is-minimal : MinimalOperator ℓ₂ ℓ₃ CongruentRel congruent-closure
congruent-closure-is-minimal _#_ _#'_ #'-extends-# #'-cong (x₁ , y₁ , x₁≈x , y₁≈y , x₁#y₁)  = #'-cong x₁≈x y₁≈y (#'-extends-# x₁#y₁)

congruent-closure-is-extensive : ExtensiveOperator ℓ₂ congruent-closure
congruent-closure-is-extensive _#_ {x} {y} x#y = x , y , ≈-refl , ≈-refl , x#y

congruent-closure-is-idempotent : IdempotentOperator (a ⊔ ℓ ⊔ ℓ₂) congruent-closure
congruent-closure-is-idempotent _#_ = (λ {
        {x} {y} (x₁ , y₁ , x₁≈x , y₁≈y , x₁#congy₁) → congruent-closure-is-congruent _#_ x₁≈x y₁≈y x₁#congy₁
    }) , congruent-closure-is-extensive (congruent-closure _#_)

congruent-closure-is-rel-congruent : SameRelCongruentOperator (a ⊔ ℓ₁) (a ⊔ ℓ₂) congruent-closure
congruent-closure-is-rel-congruent = prove-rel-congruence congruent-closure λ { (#→#' , #'→#) {x} {y} (x' , y' , x'≈x , y'≈y , x'#y') → x' , y' , x'≈x , y'≈y , #→#' x'#y' }

congruence-transferrable : TransferrableProperty ℓ₂ ℓ₃ CongruentRel
congruence-transferrable (#→#' , #'→#) #-cong {x₁} {x₂} {y₁} {y₂} x₁≈x₂ y₁≈y₂ x₁#'y₁ = #→#' (#-cong x₁≈x₂ y₁≈y₂ (#'→# x₁#'y₁))


-------------------------
--- Reflexive Closure ---
-------------------------

reflexive-closure : Rel A ℓ₂ → Rel A (a ⊔ ℓ₂)
reflexive-closure _#_ x y = x # y ⊎ x ≡ y

reflexive-closure-is-reflexive : (_#_ : Rel A ℓ₂) → Reflexive (reflexive-closure _#_)
reflexive-closure-is-reflexive _#_ {x} = inj₂ ≡-refl

reflexive-closure-is-minimal : MinimalOperator ℓ₂ ℓ₃ Reflexive reflexive-closure
reflexive-closure-is-minimal _#_ _#'_ #'-extends-# #'-refl {x} {y} (inj₁ x#y) = #'-extends-# x#y
reflexive-closure-is-minimal _#_ _#'_ #'-extends-# #'-refl {x} {y} (inj₂ ≡-refl) = #'-refl

reflexive-closure-is-extensive : ExtensiveOperator ℓ₂ reflexive-closure
reflexive-closure-is-extensive _#_ = inj₁

reflexive-closure-is-idempotent : IdempotentOperator (a ⊔ ℓ₂) reflexive-closure
reflexive-closure-is-idempotent _#_ = (λ {x} {y} → λ {(inj₁ rel) → rel ; (inj₂ x≈y) → inj₂ x≈y }) , inj₁

reflexive-closure-is-rel-congruent : SameRelCongruentOperator (a ⊔ ℓ₂) (a ⊔ ℓ₃) reflexive-closure
reflexive-closure-is-rel-congruent = prove-rel-congruence reflexive-closure λ { (#→#' , #'→#) {x} {y} → λ {
    (inj₁ x#y) → inj₁ (#→#' x#y);
    (inj₂ x≈y) → inj₂ x≈y
    }}

reflexivity-transferrable : TransferrableProperty ℓ₂ ℓ₃ Reflexive
reflexivity-transferrable (#→#' , #'→#) #-refl {x} = #→#' #-refl


-------------------------
--- Symmetric Closure ---
-------------------------

symmetric-closure : Rel A ℓ₂ → Rel A ℓ₂
symmetric-closure _#_ x y = x # y ⊎ y # x

symmetric-closure-is-symmetric : (_#_ : Rel A ℓ₂) → Symmetric (symmetric-closure _#_)
symmetric-closure-is-symmetric _#_ {x} {y} (inj₁ x#y) = inj₂ x#y
symmetric-closure-is-symmetric _#_ {x} {y} (inj₂ y#x) = inj₁ y#x

symmetric-closure-is-minimal : MinimalOperator ℓ₂ ℓ₃ Symmetric symmetric-closure
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

symmetry-transferrable : TransferrableProperty ℓ₂ ℓ₃ Symmetric
symmetry-transferrable (#→#' , #'→#) #-sym {x} {y} x#'y = #→#' (#-sym (#'→# x#'y))


--------------------------
--- Transitive Closure ---
--------------------------

transitive-closure : Rel A ℓ₂ → Rel A (a ⊔ ℓ₂)
transitive-closure = branch-type

transitive-closure-is-transitive : (_#_ : Rel A ℓ₂) → Transitive (transitive-closure _#_)
transitive-closure-is-transitive _#_ = trans-branch _#_

transitive-closure-is-minimal : MinimalOperator ℓ₂ ℓ₃ Transitive transitive-closure
transitive-closure-is-minimal _#_ _#'_ #'-extends-# #'-trans {x} {y} x↔y = trans-flatten-branch _#'_ #'-trans (map-branch id #'-extends-# x↔y)

transitive-closure-is-extensive : ExtensiveOperator ℓ₂ transitive-closure
transitive-closure-is-extensive = lift-rel-to-branch

transitive-closure-is-idempotent : IdempotentOperator (a ⊔ ℓ₂) transitive-closure
transitive-closure-is-idempotent _#_ = flatten-branches , lift-rel-to-branch (transitive-closure _#_)

transitive-closure-is-rel-congruent : SameRelCongruentOperator (a ⊔ ℓ₂) (a ⊔ ℓ₃) transitive-closure
transitive-closure-is-rel-congruent = prove-rel-congruence transitive-closure λ { (#→#' , #'→#) x#↔y → map-branch id #→#' x#↔y }

transitivity-transferrable : TransferrableProperty ℓ₂ ℓ₃ Transitive
transitivity-transferrable (#→#' , #'→#) #-trans {x} {y} {z} x#'y y#'z = #→#' (#-trans (#'→# x#'y) (#'→# y#'z))

-- Keep in mind this use of minimality
transitive-closure-fold : (_#_ : Rel A ℓ₂) → (_#'_ : Rel A ℓ₃) → _#'_ Extends _#_ → Transitive _#'_ → ∀ {x y : A} → transitive-closure _#_ x y → x #' y
transitive-closure-fold = transitive-closure-is-minimal


------------------------
--- Joint properties ---
------------------------

refl-sym-commute : CommutativeOperators (a ⊔ ℓ₂) reflexive-closure symmetric-closure
refl-sym-commute {_#_ = _#_} #-cong = (λ {
    (inj₁ (inj₁ x#y)) → inj₁ (inj₁ x#y);
    (inj₁ (inj₂ y#x)) → inj₂ (inj₁ y#x);
    (inj₂ x≡y) → inj₁ (inj₂ x≡y)
    }) , (λ {
    (inj₁ (inj₁ x#y)) → inj₁ (inj₁ x#y);
    (inj₁ (inj₂ x≡y)) → inj₂ x≡y;
    (inj₂ (inj₁ y#x)) → inj₁ (inj₂ y#x);
    (inj₂ (inj₂ y≡x)) → inj₂ (≡-sym y≡x)
    })

squeeze-reflexive-branch :
    {_#_ : Rel A ℓ₁} →
    {x y : A} →
    transitive-closure (reflexive-closure _#_) x y →
    reflexive-closure (transitive-closure _#_) x y
squeeze-reflexive-tree :
    {_#_ : Rel A ℓ₁} →
    {x y : A} →
    RelTree (reflexive-closure _#_) x y →
    reflexive-closure (transitive-closure _#_) x y
squeeze-reflexive-branch {x = w} {z} (x , y , wTx , _ , yTz) with squeeze-reflexive-tree wTx | squeeze-reflexive-tree yTz
squeeze-reflexive-branch {x = w} {z} (x , y , _ , inj₁ x#y , _) | inj₁ wBx | inj₁ yBz = inj₁ (x , y , branch wBx , x#y , branch yBz)
squeeze-reflexive-branch {x = w} {z} (x , y , _ , inj₁ x#y , _) | inj₁ wBx | inj₂ y≡z rewrite y≡z = inj₁ (x , z , branch wBx , x#y , leaf z)
squeeze-reflexive-branch {x = w} {z} (x , y , _ , inj₁ x#y , _) | inj₂ w≡x | inj₁ yBz rewrite ≡-sym w≡x = inj₁ (w , y , leaf w , x#y , branch yBz)
squeeze-reflexive-branch {x = w} {z} (x , y , _ , inj₁ x#y , _) | inj₂ w≡x | inj₂ y≡z rewrite y≡z rewrite ≡-sym w≡x = inj₁ (w , z , leaf w , x#y , leaf z)
squeeze-reflexive-branch {_#_ = _#_} {x = w} {z} (x , y , _ , inj₂ x≡y , _) | inj₁ wBx | inj₁ yBz with pop-first _#_ yBz
...                                                                                                         | q , y#q , qTz rewrite ≡-sym x≡y = inj₁ (x , q , branch wBx , y#q , qTz)
squeeze-reflexive-branch {_#_ = _#_} {x = w} {z} (x , y , _ , inj₂ x≡y , _) | inj₁ wBx | inj₂ y≡z with pop-last _#_ wBx
...                                                                                                         | q , wTq , q#x rewrite ≡-trans x≡y y≡z = inj₁ (q , z , wTq , q#x , leaf z)
squeeze-reflexive-branch {_#_ = _#_} {x = w} {z} (x , y , _ , inj₂ x≡y , _) | inj₂ w≡x | inj₁ yBz with pop-first _#_ yBz
...                                                                                                         | q , y#q , qTz rewrite (≡-sym (≡-trans w≡x x≡y)) = inj₁ (w , q , leaf w , y#q , qTz)
squeeze-reflexive-branch {x = w} {z} (x , y , _ , inj₂ x≡y , _) | inj₂ w≡x | inj₂ y≡z = inj₂ (≡-trans (≡-trans w≡x x≡y) y≡z)
squeeze-reflexive-tree (leaf x) = inj₂ ≡-refl
squeeze-reflexive-tree (branch b) = squeeze-reflexive-branch b

refl-trans-commute : CommutativeOperators (a ⊔ ℓ ⊔ ℓ₂) reflexive-closure transitive-closure
refl-trans-commute {_#_ = _#_} #-cong = (λ {
    (inj₁ xBy) → map-branch id inj₁ xBy;
    (inj₂ x≈y) → lift-rel-to-branch (reflexive-closure _#_) (inj₂ x≈y)
    }) , squeeze-reflexive-branch

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

sym-not-trans-preserving : AtLeastSize A-setoid 3 → (ℓ₁ : Level) → ¬ (OperatorPreserves (a ⊔ ℓ ⊔ ℓ₁) Transitive symmetric-closure)
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



---------------------------------------
--- Reflexive Transitive properties ---
---------------------------------------
-- Since apparently this is a thing that comes up sometimes

reflexive-transitive-closure : Rel A ℓ₂ → Rel A (a ⊔ ℓ₂)
reflexive-transitive-closure = reflexive-closure ∘ transitive-closure

reflexive-transitive-closure-is-transitive : (_#_ : Rel A ℓ₂) → Transitive (reflexive-transitive-closure _#_)
reflexive-transitive-closure-is-transitive _#_ (inj₁ i~j) (inj₁ j~k) = inj₁ (trans-branch _#_ i~j j~k)
reflexive-transitive-closure-is-transitive _#_ (inj₁ i~j) (inj₂ ≡-refl) = inj₁ i~j
reflexive-transitive-closure-is-transitive _#_ (inj₂ ≡-refl) (inj₁ j~k) = inj₁ j~k
reflexive-transitive-closure-is-transitive _#_ (inj₂ ≡-refl) (inj₂ ≡-refl) = inj₂ ≡-refl

reflexive-transitive-closure-is-reflexive : (_#_ : Rel A ℓ₂) → Reflexive (reflexive-transitive-closure _#_)
reflexive-transitive-closure-is-reflexive _#_ = reflexive-closure-is-reflexive (transitive-closure _#_)

reflexive-transitive-closure-is-minimal : MinimalOperator ℓ₂ ℓ₃ (λ _#_ → Reflexive _#_ × Transitive _#_) reflexive-transitive-closure
reflexive-transitive-closure-is-minimal _#_ _#'_ #'-extends-# (#'-refl , #'-trans) (inj₁ x↔y) = transitive-closure-is-minimal _#_ _#'_ #'-extends-# #'-trans x↔y
reflexive-transitive-closure-is-minimal _#_ _#'_ #'-extends-# (#'-refl , #'-trans) (inj₂ ≡-refl) = reflexive-closure-is-minimal (transitive-closure _#_) _#'_ (transitive-closure-is-minimal _#_ _#'_ #'-extends-# #'-trans) #'-refl (inj₂ ≡-refl)

reflexive-transitive-closure-is-extensive : ExtensiveOperator ℓ₂ reflexive-transitive-closure
reflexive-transitive-closure-is-extensive _#_ = reflexive-closure-is-extensive (transitive-closure _#_) ∘ (transitive-closure-is-extensive _#_)

-- reflexive-transitive-closure-is-idempotent : IdempotentOperator (a ⊔ ℓ₂) reflexive-transitive-closure
-- reflexive-transitive-closure-is-idempotent _#_ = (λ {
--     (inj₁ (w , z , x↔w , (inj₁ w#↔z) , z↔y)) → {!   !};
--     (inj₁ (w , z , x↔w , (inj₂ ≡-refl) , z↔y)) → ?
--     (inj₂ ≡-refl) → inj₂ ≡-refl
--     }) , λ x#↔y → inj₁ (transitive-closure-is-extensive (reflexive-transitive-closure _#_) x#↔y)

-- reflexive-transitive-closure-is-rel-congruent : SameRelCongruentOperator (a ⊔ ℓ₂) (a ⊔ ℓ₃) reflexive-transitive-closure
-- reflexive-transitive-closure-is-rel-congruent = prove-rel-congruence reflexive-transitive-closure λ { (#→#' , #'→#) x#↔y → {!   !} }


---------------
--- Product ---
---------------

×-rel : Rel A ℓ₁ → Rel A ℓ₂ → Rel A (ℓ₁ ⊔ ℓ₂)
×-rel _#_ _~_ x y = x # y × x ~ y

×-rel-preserves-congruence : OperatorPreserves₂ ℓ₁ ℓ₂ CongruentRel ×-rel
×-rel-preserves-congruence #-cong ~-cong x₁≈x₂ y₁≈y₂ (x₁#y₁ , x₁~y₁) = #-cong x₁≈x₂ y₁≈y₂ x₁#y₁ , ~-cong x₁≈x₂ y₁≈y₂ x₁~y₁

×-rel-preserves-reflexivity : OperatorPreserves₂ ℓ₁ ℓ₂ Reflexive ×-rel
×-rel-preserves-reflexivity #-refl ~-refl = #-refl , ~-refl

×-rel-preserves-symmetry : OperatorPreserves₂ ℓ₁ ℓ₂ Symmetric ×-rel
×-rel-preserves-symmetry #-sym ~-sym (x#y , x~y) = #-sym x#y , ~-sym x~y

×-rel-preserves-transitivity : OperatorPreserves₂ ℓ₁ ℓ₂ Transitive ×-rel
×-rel-preserves-transitivity #-trans ~-trans (x#y , x~y) (y#z , y~z) = #-trans x#y y#z , ~-trans x~y y~z

×-rel-preserves-equivalence : OperatorPreserves₂ ℓ₁ ℓ₂ IsEquivalence ×-rel
×-rel-preserves-equivalence #-eq ~-eq = record {
    refl = λ {x} → ×-rel-preserves-reflexivity (#-refl {x}) (~-refl {x}) {x};
    sym = λ {x} {y} → ×-rel-preserves-symmetry #-sym ~-sym {x} {y};
    trans = λ {x} {y} {z} → ×-rel-preserves-transitivity #-trans ~-trans {x} {y} {z}
    }
    where
        open IsEquivalence #-eq renaming (refl to #-refl; sym to #-sym; trans to #-trans)
        open IsEquivalence ~-eq renaming (refl to ~-refl; sym to ~-sym; trans to ~-trans)


-------------------------------------
--- Some Transferrable Properties ---
-------------------------------------

{-
    Note that above, we prove that CongruentRel, Reflexive, Symmetric, Transitive are transferrable properties.
-}
IsEquivalence-transferrable : TransferrableProperty ℓ₂ ℓ₃ IsEquivalence
IsEquivalence-transferrable {_#_ = _#_} {_$_} ($-extends-# , #-extends-$) #-eq = record {
    refl = λ {x} → $-extends-# (refl #-eq);
    sym = λ {x} {y} x$y → $-extends-# (sym #-eq (#-extends-$ x$y));
    trans = λ {i} {j} {k} i$j j$k → $-extends-# (trans #-eq (#-extends-$ i$j) (#-extends-$ j$k))
    }

Decidable-transferrable : TransferrableProperty ℓ₂ ℓ₃ Decidable
Decidable-transferrable {_#_ = _#_} {_$_} ($-extends-# , #-extends-$) #-dec x y with #-dec x y
... | yes x#y = yes ($-extends-# x#y)
... | no ¬x#y = no (¬x#y ∘ #-extends-$)

Irreflexive-transferrable : TransferrableProperty ℓ₂ ℓ₃ (Irreflexive _≈_)
Irreflexive-transferrable {_#_ = _#_} {_$_} ($-extends-# , #-extends-$) #-irrefl = λ z z₁ → #-irrefl z (#-extends-$ z₁)

Respectsʳ-transferrable : TransferrableProperty ℓ₂ ℓ₃ (_Respectsʳ _≈_)
Respectsʳ-transferrable {_#_ = _#_} {_$_} ($-extends-# , #-extends-$) #-respʳ = λ z z₁ → $-extends-# (#-respʳ z (#-extends-$ z₁))

Respectsˡ-transferrable : TransferrableProperty ℓ₂ ℓ₃ (_Respectsˡ _≈_)
Respectsˡ-transferrable {_#_ = _#_} {_$_} ($-extends-# , #-extends-$) #-respˡ = λ z z₁ → $-extends-# (#-respˡ z (#-extends-$ z₁))

Respects₂-transferrable : TransferrableProperty ℓ₂ ℓ₃ (_Respects₂ _≈_)
Respects₂-transferrable {_#_ = _#_} {_$_} $-same-rel-# #-resp₂ = Respectsʳ-transferrable $-same-rel-# (#-resp₂ .proj₁) , Respectsˡ-transferrable $-same-rel-# (#-resp₂ .proj₂)

IsStrictPartialOrder-transferrable : TransferrableProperty ℓ₂ ℓ₃ (IsStrictPartialOrder _≈_)
IsStrictPartialOrder-transferrable {_#_ = _#_} {_$_} $-same-rel-# #-strict-partial = record {
    isEquivalence = #-strict-partial .IsStrictPartialOrder.isEquivalence;
    irrefl = Irreflexive-transferrable $-same-rel-# (IsStrictPartialOrder.irrefl #-strict-partial);
    trans = transitivity-transferrable $-same-rel-# (IsStrictPartialOrder.trans #-strict-partial);
    <-resp-≈ = Respects₂-transferrable $-same-rel-# (IsStrictPartialOrder.<-resp-≈ #-strict-partial)
    }

IsDecStrictPartialOrder-transferrable : TransferrableProperty ℓ₂ ℓ₃ (IsDecStrictPartialOrder _≈_)
IsDecStrictPartialOrder-transferrable {_#_ = _#_} {_$_} $-same-rel-# #-dec-strict-partial = record {
    isStrictPartialOrder = IsStrictPartialOrder-transferrable $-same-rel-# (#-dec-strict-partial .IsDecStrictPartialOrder.isStrictPartialOrder);
    _≟_ = IsDecStrictPartialOrder._≟_ #-dec-strict-partial;
    _<?_ = Decidable-transferrable $-same-rel-# (IsDecStrictPartialOrder._<?_ #-dec-strict-partial)
    }
