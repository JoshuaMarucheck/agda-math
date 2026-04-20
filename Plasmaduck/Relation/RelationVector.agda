open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; inspect; cong; Reveal_·_is_; [_]; refl; sym; trans)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; z≤n; s≤s; s≤s⁻¹) renaming (zero to zero-ℕ; suc to suc-ℕ)
open import Data.Nat.Properties using (+-suc)
open import Data.Fin using (Fin; zero; suc; toℕ) renaming (_<_ to _<-fin_)
open import Data.Vec using (Vec; []; _∷_; head; tail; lookup)
open import Relation.Binary using (Rel; Transitive)
open import Function using (flip)



module Plasmaduck.Relation.RelationVector where

variable
    a b c ℓ ℓ₁ ℓ₂ : Level


module RelationVector {A : Set a} (_~_ : Rel A ℓ) where
    data PairwiseRelationVector : {n : ℕ} → Vec A n → Set (a ⊔ ℓ) where
        empty : (v : Vec A 0) → PairwiseRelationVector v
        single : (v : Vec A 1) → PairwiseRelationVector v
        head-pair : {n : ℕ} → (vec : Vec A (suc-ℕ (suc-ℕ n))) → head vec ~ head (tail vec) → PairwiseRelationVector {n = suc-ℕ n} (tail vec) → PairwiseRelationVector vec

    module _ (~-trans : Transitive _~_) where
        lookup-trans : {n : ℕ} {vec : Vec A n} → PairwiseRelationVector vec → (i j : Fin n) → i <-fin j → lookup vec i ~ lookup vec j
        lookup-trans {n = 0} _ ()
        lookup-trans {n = 1} _ zero zero ()
        lookup-trans {n = suc-ℕ (suc-ℕ n'')} (head-pair (x ∷ y ∷ xs) x~y rel-vec) i zero ()
        lookup-trans {n = suc-ℕ (suc-ℕ n'')} (head-pair (x ∷ y ∷ xs) x~y rel-vec) zero (suc zero) i<j = x~y
        lookup-trans {n = suc-ℕ (suc-ℕ n'')} (head-pair (x ∷ y ∷ xs) x~y rel-vec) zero (suc (suc j'')) i<j = ~-trans x~y (lookup-trans rel-vec zero (suc j'') (s≤s z≤n))
        lookup-trans {n = suc-ℕ (suc-ℕ n'')} (head-pair (x ∷ y ∷ xs) x~y rel-vec) (suc i') (suc j') i<j = lookup-trans rel-vec i' j' (s≤s⁻¹ i<j)



module RelationTree {A : Set a} (_~_ : Rel A ℓ) where

    branch-type : (w z : A) → Set (a ⊔ ℓ)
    data RelTree : (x y : A) → Set (a ⊔ ℓ) where
        leaf : (x : A) → RelTree x x
        branch : {w z : A} → branch-type w z → RelTree w z
    branch-type w z = Σ A λ x → Σ A λ y → RelTree w x × x ~ y × RelTree y z

    lift-rel-to-branch : {x y : A} → x ~ y → branch-type x y
    lift-rel-to-branch {x} {y} x~y = x , y , leaf x , x~y , leaf y


    pop-first : {x y : A} → branch-type x y → Σ A λ z → x ~ z × RelTree z y
    pop-first {x = w} {z} (w , y , leaf w , w~y , y↔z) = y , w~y , y↔z
    pop-first {x = w} {z} (x , y , branch b , x~y , y↔z) with pop-first b
    ...                                                     | (q , w~q , q↔x) = q , w~q , branch (x , y , q↔x , x~y , y↔z)

    append-first-tree : {x y z : A} → x ~ y → RelTree y z → branch-type x z
    append-first-tree {x = x} {y} {z} x~y (y↔z) = x , y , leaf x , x~y , y↔z

    append-first-branch : {x y z : A} → x ~ y → branch-type y z → branch-type x z
    append-first-branch {x = v} {w} {z} v~w b = append-first-tree v~w (branch b)

    append-first : {x y z : A} → x ~ y × RelTree y z → branch-type x z
    append-first (x~y , yTz) = append-first-tree x~y yTz


    pop-last : {x y : A} → branch-type x y → Σ A λ z → RelTree x z × z ~ y
    pop-last {x = w} {z} (x , z , w↔x , x~z , leaf z) = x , w↔x , x~z
    pop-last {x = w} {z} (x , y , w↔x , x~y , branch b) with pop-last b
    ...                                                     | (q , y↔q , q~z) = q , branch (x , y , w↔x , x~y , y↔q) , q~z

    append-last-tree : {x y z : A} → RelTree x y → y ~ z → branch-type x z
    append-last-tree {x = x} {y} {z} x↔y y~z = y , z , x↔y , y~z , leaf z

    append-last-branch : {x y z : A} → branch-type x y → y ~ z → branch-type x z
    append-last-branch {x = v} {y} {z} b y~z = append-last-tree (branch b) y~z

    append-last : {x y z : A} → RelTree x y × y ~ z → branch-type x z
    append-last (xTy , y~z) = append-last-tree xTy y~z


    trans-branch : {x y z : A} → branch-type x y → branch-type y z → branch-type x z
    trans-branch {y = y} b₁ b₂ with pop-first b₂
    ...                           | (y₂ , y~y₂ , y₂↔z) = y , y₂ , branch b₁ , y~y₂ , y₂↔z

    trans-tree : {x y z : A} → RelTree x y → RelTree y z → RelTree x z
    trans-tree (leaf x) (leaf x) = leaf x
    trans-tree (leaf x) (branch b₂) = branch b₂
    trans-tree (branch b₁) (leaf x) = branch b₁
    trans-tree (branch b₁) (branch b₂) = branch (trans-branch b₁ b₂)

    trans-flatten-branch : Transitive _~_ → {w z : A} → branch-type w z → w ~ z
    trans-flatten-branch ~-trans {w} {z} (w , z , leaf w , w~z , leaf z) = w~z
    trans-flatten-branch ~-trans {w} {z} (w , y , leaf w , w~y , branch yBz) = ~-trans w~y (trans-flatten-branch ~-trans yBz)
    trans-flatten-branch ~-trans {w} {z} (x , y , branch wBx , x~z , leaf z) = ~-trans (trans-flatten-branch ~-trans wBx) x~z
    trans-flatten-branch ~-trans {w} {z} (x , y , branch wBx , x~y , branch yBz) = ~-trans (~-trans (trans-flatten-branch ~-trans wBx) x~y) (trans-flatten-branch ~-trans yBz)


open RelationTree public

map-branch :
    {A : Set a} {_~_ : Rel A ℓ₁} {B : Set b} {_#_ : Rel B ℓ₂} →
    (f : A → B) →
    (map-rel : {x y : A} → x ~ y → f x # f y) →
    {w z : A} → branch-type _~_ w z →
    branch-type _#_ (f w) (f z)
map-tree :
    {A : Set a} {_~_ : Rel A ℓ₁} {B : Set b} {_#_ : Rel B ℓ₂} →
    (f : A → B) →
    (map-rel : {x y : A} → x ~ y → f x # f y) →
    {w z : A} → RelTree _~_ w z →
    RelTree _#_ (f w) (f z)
map-branch f map-rel {w} {z} (x , y , b₁ , x~y , b₂) = f x , f y , map-tree f map-rel b₁ , map-rel x~y , map-tree f map-rel b₂
map-tree f map-rel {x} {x} (leaf x) = leaf (f x)
map-tree f map-rel {x} {y} (branch xBy) = branch (map-branch f map-rel xBy)


flatten-branches :
    {A : Set a} {_~_ : Rel A ℓ₁} →
    {w z : A} →
    branch-type (branch-type _~_) w z →
    branch-type _~_ w z
flatten-trees :
    {A : Set a} {_~_ : Rel A ℓ₁} →
    {w z : A} →
    RelTree (branch-type _~_) w z →
    RelTree _~_ w z

flatten-branches {_~_ = _~_} {w = w} {z} (x , y , wTx , xBy , yTz) with pop-first _~_ xBy
...                                                                   | (x₁ , x~x₁ , x₁By) = x , x₁ , flatten-trees wTx , x~x₁ , trans-tree _~_ x₁By (flatten-trees yTz)
flatten-trees (leaf x) = leaf x
flatten-trees (branch b) = branch (flatten-branches b)

flip-branch :
    {A : Set a} {_~_ : Rel A ℓ₁} →
    {x y : A} →
    branch-type _~_ x y →
    branch-type (flip _~_) y x
flip-tree :
    {A : Set a} {_~_ : Rel A ℓ₁} →
    {x y : A} →
    RelTree _~_ x y →
    RelTree (flip _~_) y x
flip-branch {x = w} {z} (x , y , wTx , x~y , yTz) = y , x , flip-tree yTz , x~y , flip-tree wTx
flip-tree (leaf x) = leaf x
flip-tree (branch b) = branch (flip-branch b)
