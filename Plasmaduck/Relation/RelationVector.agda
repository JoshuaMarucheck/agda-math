open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; inspect; cong; Reveal_·_is_; [_]) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open import Data.Empty using (⊥-elim)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; z≤n; s≤s; s≤s⁻¹) renaming (zero to zero-ℕ; suc to suc-ℕ)
open import Data.Nat.Properties using (+-suc)
open import Data.Fin using (Fin; zero; suc; toℕ) renaming (_<_ to _<-fin_)
-- open import Data.Vec using (Vec; []; _∷_; head; tail; lookup)
open import Relation.Binary using (Rel; REL; Transitive; IsEquivalence)
open import Function using (flip; _∘_)

open import Plasmaduck.SetoidExperiment.SetoidMachinery using (equality→setoid)
open import Plasmaduck.Function.Properties using (Congruent₂)



module Plasmaduck.Relation.RelationVector where

variable
    a b c ℓ ℓ₁ ℓ₂ : Level


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

    append-first : {x y z : A} → x ~ y → RelTree y z → branch-type x z
    append-first {x = x} {y} {z} x~y (y↔z) = x , y , leaf x , x~y , y↔z

    append-first-branch : {x y z : A} → x ~ y → branch-type y z → branch-type x z
    append-first-branch {x = v} {w} {z} v~w b = append-first v~w (branch b)

    append-first-tree : {x y z : A} → x ~ y → RelTree y z → RelTree x z
    append-first-tree x~y yTz = branch (append-first x~y yTz)


    pop-last : {x y : A} → branch-type x y → Σ A λ z → RelTree x z × z ~ y
    pop-last {x = w} {z} (x , z , w↔x , x~z , leaf z) = x , w↔x , x~z
    pop-last {x = w} {z} (x , y , w↔x , x~y , branch b) with pop-last b
    ...                                                     | (q , y↔q , q~z) = q , branch (x , y , w↔x , x~y , y↔q) , q~z

    append-last : {x y z : A} → RelTree x y → y ~ z → branch-type x z
    append-last {x = x} {y} {z} x↔y y~z = y , z , x↔y , y~z , leaf z

    append-last-branch : {x y z : A} → branch-type x y → y ~ z → branch-type x z
    append-last-branch {x = v} {y} {z} b y~z = append-last (branch b) y~z

    append-last-tree : {x y z : A} → RelTree x y → y ~ z → RelTree x z
    append-last-tree xTy y~z = branch (append-last xTy y~z)


    trans-branch : {x y z : A} → branch-type x y → branch-type y z → branch-type x z
    trans-branch {y = y} b₁ b₂ with pop-first b₂
    ...                           | (y₂ , y~y₂ , y₂↔z) = y , y₂ , branch b₁ , y~y₂ , y₂↔z

    trans-tree : {x y z : A} → RelTree x y → RelTree y z → RelTree x z
    trans-tree (leaf x) (leaf x) = leaf x
    trans-tree (leaf x) (branch b₂) = branch b₂
    trans-tree (branch b₁) (leaf x) = branch b₁
    trans-tree (branch b₁) (branch b₂) = branch (trans-branch b₁ b₂)

    -- Fold, via tree
    trans-flatten-branch : Transitive _~_ → {w z : A} → branch-type w z → w ~ z
    trans-flatten-branch ~-trans {w} {z} (w , z , leaf w , w~z , leaf z) = w~z
    trans-flatten-branch ~-trans {w} {z} (w , y , leaf w , w~y , branch yBz) = ~-trans w~y (trans-flatten-branch ~-trans yBz)
    trans-flatten-branch ~-trans {w} {z} (x , y , branch wBx , x~z , leaf z) = ~-trans (trans-flatten-branch ~-trans wBx) x~z
    trans-flatten-branch ~-trans {w} {z} (x , y , branch wBx , x~y , branch yBz) = ~-trans (~-trans (trans-flatten-branch ~-trans wBx) x~y) (trans-flatten-branch ~-trans yBz)


open RelationTree public



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



-- For similar cases as RelationTree above,
-- but for when you want pop-first to be done via deconstruction
-- (and thus be able to recurse on it)
module RelationList {A : Set a} (_~_ : Rel A ℓ) where
    data PairwiseRelationList : (x y : A) → Set (a ⊔ ℓ)
    PairwiseRelationListCons : (x y : A) → Set (a ⊔ ℓ)
    PairwiseRelationListCons x z = Σ A λ y → x ~ y × PairwiseRelationList y z
    data PairwiseRelationList where
        init : (x : A) → PairwiseRelationList x x
        cons : {x y : A} → PairwiseRelationListCons x y → PairwiseRelationList x y

    pattern [] = init _
    -- _∷_ : {x y z : A} → x ~ y → PairwiseRelationList y z → PairwiseRelationList x z
    pattern _∷_ x y = cons (_ , x , y)
    infixr 6 _∷_

    -- To get a PairwiseRelationListCons
    -- _∷_ : {x y z : A} → x ~ y → PairwiseRelationList y z → PairwiseRelationListCons x z
    pattern _∷'_ x y = (_ , x , y)
    infixr 6 _∷'_

    module _ (~-trans : Transitive _~_) where

        foldl' : {x y z : A} → x ~ y → PairwiseRelationList y z → x ~ z
        foldl' x~y (init _) = x~y
        foldl' {x = w} {x} w~x (cons (y , x~y , y*z)) = foldl' (~-trans w~x x~y) y*z

        foldl : {x y : A} → PairwiseRelationListCons x y → x ~ y
        foldl (z , x~z , z*y) = foldl' x~z z*y

open RelationList public

module _ {A : Set a} {_~_ : Rel A ℓ} where
    flip-concat :
        {x y z : A} →
        PairwiseRelationList (flip _~_) z y →
        PairwiseRelationList _~_ z x →
        PairwiseRelationList _~_ y x
    flip-concat (init _) y-*x = y-*x
    flip-concat (cons (w , z~w , w*y)) z-*x = flip-concat w*y (cons (_ , z~w , z-*x))

    flip-list :
        {x y : A} →
        PairwiseRelationList (flip _~_) x y →
        PairwiseRelationList _~_ y x
    flip-list l = flip-concat l (init _)

    head :
        {x y : A} →
        PairwiseRelationListCons _~_ x y →
        Σ A λ z → x ~ z
    head (z , x~z , _) = (z , x~z)

    head' :
        {x y : A} →
        PairwiseRelationList _~_ x y →
        Maybe (Σ A λ z → x ~ z)
    head' (init _) = nothing
    head' {x = x} {y} (cons (z , x~z , z*y)) = just (z , x~z)



module RelationListProofTools {A : Set a} {_~_ : Rel A ℓ} where
    -- Generally not computationally efficient; use as proof tool only
    last' :
        {x y : A} →
        PairwiseRelationList _~_ x y →
        Maybe (Σ A λ z → z ~ y)
    last' {x = x} {.x} (init x) = nothing
    last' {x = x} {y} (cons (.y , x~y , (init y))) = just (x , x~y)
    last' {x = x} {y} (cons (z , x~z , l@(cons _))) = last' l

    last'-cons-is-just :
        {x z : A} →
        (x*z : PairwiseRelationListCons _~_ x z) →
        Σ A λ y → Σ (y ~ z) λ y~z → last' (cons x*z) ≡ just (y , y~z)
    last'-cons-is-just {x = x} {z} (.z , x~z , (init .z)) = x , x~z , ≡-refl
    last'-cons-is-just {x = x} {z} (y , y~z , (cons y*z)) = last'-cons-is-just y*z


    last :
        {x y : A} →
        PairwiseRelationListCons _~_ x y →
        Σ A λ z → z ~ y
    last {x = x} {y} x*y with last' (cons x*y) | .(last'-cons-is-just x*y)
    ... | just thing | _ = thing
    ... | nothing | ()

    length :
        {x y : A} →
        PairwiseRelationList _~_ x y →
        ℕ
    length (init x) = 0
    length (cons (_ , _ , l)) = suc-ℕ (length l)

    last-drops-cons :
        {x y z : A} →
        (x~y : x ~ y) →
        (y*z : PairwiseRelationListCons _~_ y z) →
        last (y , x~y , cons y*z) ≡ last y*z
    last-drops-cons x~y y*z = ≡-refl

    cons-last :
        {x y z : A} →
        (x*y : PairwiseRelationList _~_ x y) →
        (y~z : y ~ z) →
        PairwiseRelationListCons _~_ x z
    cons-last (init _) y~z = _ , y~z , init _
    cons-last (cons (w , x~w , w*y)) y~z = w , x~w , cons (cons-last w*y y~z)

    cons-last' :
        {x y z : A} →
        (x*y : PairwiseRelationList _~_ x y) →
        (y~z : y ~ z) →
        PairwiseRelationList _~_ x z
    cons-last' l y~z = cons (cons-last l y~z)

    cons-cons-last-commute :
        {w x y z : A} →
        (w~x : w ~ x) →
        (x*y : PairwiseRelationList _~_ x y) →
        (y~z : y ~ z) →
        cons-last' (cons (x , w~x , x*y)) y~z ≡ cons (x , w~x , (cons-last' x*y y~z))
    cons-cons-last-commute w~x x*y y~z = ≡-refl

    last-cons-last-lemma :
        {x y z : A} →
        (x*y : PairwiseRelationList _~_ x y) →
        (y~z : y ~ z) →
        last (cons-last x*y y~z) ≡ (_ , y~z)
    last-cons-last-lemma (init x) y~z = ≡-refl
    last-cons-last-lemma {x = x} {y} {z} (cons (w , x~w , w*y)) y~z = last-cons-last-lemma w*y y~z

    length-cons-last-lemma :
        {x y z : A} →
        (x*y : PairwiseRelationList _~_ x y) →
        (y~z : y ~ z) →
        length (cons-last' x*y y~z) ≡ suc-ℕ (length x*y)
    length-cons-last-lemma (init x) y~z = ≡-refl
    length-cons-last-lemma x*y@(cons (w , x~w , w*y)) y~z =
        length (cons-last' (cons (w , x~w , w*y)) y~z)  ≡⟨⟩
        length (cons (w , x~w , (cons-last' w*y y~z)))  ≡⟨⟩
        suc-ℕ (length (cons-last' w*y y~z))             ≡⟨ cong suc-ℕ (length-cons-last-lemma w*y y~z) ⟩
        suc-ℕ (suc-ℕ (length w*y))                      ≡⟨⟩
        suc-ℕ (length x*y)                              ∎
        where open ≡-Reasoning

    data same-path : {x y : A} → REL (RelTree _~_ x y) (PairwiseRelationList _~_ x y) (a ⊔ ℓ) where
        init-step : {x : A} → same-path (leaf x) (init x)
        cons-step : {x z : A} → (b : branch-type _~_ x z) → let (y , x~y , y*z) = pop-first _~_ b in (l : PairwiseRelationList _~_ y z) → same-path y*z l → same-path (branch b) (cons (y , x~y , l))

open RelationListProofTools

cons-flip-concat :
    {A : Set a} {_~_ : Rel A ℓ}
    {w x y z : A} →
    (w~x : w ~ x) →
    (y*x : PairwiseRelationList (flip _~_) y x) →
    (y*z : PairwiseRelationList _~_ y z) →
    flip-concat (cons-last' y*x w~x) y*z ≡
    cons (x , w~x , (flip-concat y*x y*z))
cons-flip-concat w~x (init _) y*z = ≡-refl
cons-flip-concat w~x (cons (v , y~v , v*x)) y*z = cons-flip-concat w~x v*x (cons (_ , y~v , y*z))

cons-last-flip-concat :
    {A : Set a} {_~_ : Rel A ℓ}
    {w x y z : A} →
    (x*w : PairwiseRelationList (flip _~_) x w) →
    (x*y : PairwiseRelationList _~_ x y) →
    (y~z : y ~ z) →
    flip-concat x*w (cons-last' x*y y~z) ≡
    cons-last' (flip-concat x*w x*y) y~z
cons-last-flip-concat (init _) x*y y~z = ≡-refl
cons-last-flip-concat {A = A} {_~_} {w} {x} {y} {z} x*w@(cons (v , v~x , w*v)) x*y y~z =
    flip-concat (cons (v , v~x , w*v)) (cons-last' x*y y~z)     ≡⟨⟩
    flip-concat w*v (cons (x , v~x , (cons-last' x*y y~z)))     ≡⟨⟩
    flip-concat w*v (cons-last' (cons (x , v~x , x*y)) y~z)     ≡⟨ cons-last-flip-concat w*v (cons (x , v~x , x*y)) y~z ⟩
    cons-last' (flip-concat w*v (cons (x , v~x , x*y))) y~z     ≡⟨⟩
    cons-last' (flip-concat x*w x*y) y~z                        ∎
    where open ≡-Reasoning

flip-list-involution :
    {A : Set a} {_~_ : Rel A ℓ}
    {x y : A} →
    (l : PairwiseRelationList _~_ x y) →
    flip-list (flip-list l) ≡ l
flip-list-involution (init x) = ≡-refl
flip-list-involution (cons (z , x~z , z*y)) =
    flip-list (flip-list (cons (z , x~z , z*y)))                            ≡⟨⟩
    flip-concat (flip-concat (cons (z , x~z , z*y)) (init _)) (init _)      ≡⟨⟩
    flip-concat (flip-concat z*y (cons-last' (init _) x~z)) (init _)        ≡⟨ cong flip-list (cons-last-flip-concat z*y (init _) x~z) ⟩
    flip-concat (cons-last' (flip-concat z*y (init _)) x~z) (init _)        ≡⟨ cons-flip-concat x~z (flip-concat z*y (init _)) (init _) ⟩
    cons (z , x~z , (flip-concat ((flip-concat z*y (init _))) (init _)))    ≡⟨⟩
    cons (z , x~z , (flip-list (flip-list z*y)))                            ≡⟨ cong (λ q → cons (z , x~z , q)) (flip-list-involution z*y) ⟩
    cons (z , x~z , z*y)                                                    ∎
    where open ≡-Reasoning

_++_ :
    {A : Set a} {_~_ : Rel A ℓ}
    {x y z : A} →
    PairwiseRelationList _~_ x y →
    PairwiseRelationList _~_ y z →
    PairwiseRelationList _~_ x z
_++_ x*y y*z = flip-concat (flip-list x*y) y*z
infixr 5 _++_

tree→list :
    {A : Set a} {_~_ : Rel A ℓ}
    {x y : A} →
    RelTree _~_ x y →
    PairwiseRelationList _~_ x y
tree→list (leaf x) = init x
tree→list {x = x} {y} (branch (w , z , x*w , w~z , z*y)) = (tree→list x*w) ++ cons (z , w~z , (tree→list z*y))

list→tree :
    {A : Set a} {_~_ : Rel A ℓ}
    {x y : A} →
    PairwiseRelationList _~_ x y →
    RelTree _~_ x y
list→tree (init x) = leaf x
list→tree {x = x} {y} (cons (z , x~z , l)) = branch (x , z , leaf x , x~z , list→tree l)


++-left-cons-make :
    {A : Set a} {_~_ : Rel A ℓ}
    {x y z : A} →
    (xy : PairwiseRelationListCons _~_ x y) →
    (yz : PairwiseRelationList _~_ y z) →
    PairwiseRelationListCons _~_ x z
++-left-cons-make {x = w} {y} {z} (x , w~x , xy) yz = x , w~x , xy ++ yz

_++'_ :
    {A : Set a} {_~_ : Rel A ℓ}
    {x y z : A} →
    PairwiseRelationListCons _~_ x y →
    PairwiseRelationListCons _~_ y z →
    PairwiseRelationListCons _~_ x z
_++'_ {x = w} {y} {z} (x , w~x , x*y) y*z = x , w~x , x*y ++ cons y*z
infixr 5 _++'_

++-right-cons-make :
    {A : Set a} {_~_ : Rel A ℓ}
    {x y z : A} →
    (xy : PairwiseRelationList _~_ x y) →
    (yz : PairwiseRelationListCons _~_ y z) →
    PairwiseRelationListCons _~_ x z
++-right-cons-make (init _) y*z = y*z
++-right-cons-make (cons x*y) y*z = x*y ++' y*z

++-left-cons :
    {A : Set a} {_~_ : Rel A ℓ}
    {x y z : A} →
    (xy : PairwiseRelationListCons _~_ x y) →
    (yz : PairwiseRelationList _~_ y z) →
    (cons xy) ++ yz ≡ cons (++-left-cons-make xy yz)
++-left-cons (_ ∷' []) y*z = ≡-refl
++-left-cons {x = w} {y} {z} (x , w~x , x*y@(cons (v , x~v , v*y))) y*z =
    cons (x , w~x , x*y) ++ y*z                                     ≡⟨⟩
    flip-concat (flip-concat (cons (x , w~x , x*y)) (init _)) y*z   ≡⟨ cong (λ q → flip-concat q y*z) (cons-last-flip-concat x*y (init _) w~x) ⟩
    flip-concat (cons-last' (flip-concat x*y (init _)) w~x) y*z     ≡⟨ cons-flip-concat w~x (flip-list x*y) y*z ⟩
    cons (x , w~x , x*y ++ y*z)                                     ∎
    where open ≡-Reasoning

++-right-cons :
    {A : Set a} {_~_ : Rel A ℓ}
    {x y z : A} →
    (xy : PairwiseRelationList _~_ x y) →
    (yz : PairwiseRelationListCons _~_ y z) →
    xy ++ (cons yz) ≡ cons (++-right-cons-make xy yz)
++-right-cons (init _) y*z = ≡-refl
++-right-cons {x = v} {x} {z} (cons vx) (y , x~y , y*z) = ++-left-cons vx (cons (y , x~y , y*z))

++-assoc :
    {A : Set a} {_~_ : Rel A ℓ}
    {w x y z : A} →
    (wx : PairwiseRelationList _~_ w x) →
    (xy : PairwiseRelationList _~_ x y) →
    (yz : PairwiseRelationList _~_ y z) →
    wx ++ (xy ++ yz) ≡ (wx ++ xy) ++ yz
++-assoc (init _) xy yz = ≡-refl
++-assoc {_~_ = _~_} {w} {x} {y} {z} (cons (v , w~v , vx)) xy yz =
    cons (v , w~v , vx) ++ (xy ++ yz)   ≡⟨ ++-left-cons (w~v ∷' vx) (xy ++ yz) ⟩
    cons (v , w~v , vx ++ (xy ++ yz))   ≡⟨ cong (λ q → cons (v , w~v , q)) (++-assoc vx xy yz) ⟩
    cons (v , w~v , (vx ++ xy) ++ yz)   ≡⟨ ≡-sym (++-left-cons (w~v ∷' (vx ++ xy)) yz) ⟩
    cons (v , w~v , vx ++ xy) ++ yz     ≡⟨ cong (_++ yz) (≡-sym (++-left-cons (w~v ∷' vx) xy)) ⟩
    (cons (v , w~v , vx) ++ xy) ++ yz   ∎
    where open ≡-Reasoning


++-++' :
    {A : Set a} {_~_ : Rel A ℓ}
    {x y z : A} →
    (xy : PairwiseRelationListCons _~_ x y) →
    (yz : PairwiseRelationListCons _~_ y z) →
    cons (xy ++' yz) ≡ cons xy ++ cons yz
++-++' {x = w} {y} {z} xy yz = ≡-sym (++-left-cons xy (cons yz))

++-right-empty :
    {A : Set a} {_~_ : Rel A ℓ}
    {x y : A} →
    (xy : PairwiseRelationList _~_ x y) →
    xy ++ [] ≡ xy
++-right-empty [] = ≡-refl
++-right-empty (x~z ∷ z*y) =
    (x~z ∷ z*y) ++ []   ≡⟨ ++-left-cons (x~z ∷' z*y) [] ⟩
    x~z ∷ (z*y ++ [])   ≡⟨ cong (x~z ∷_) (++-right-empty z*y) ⟩
    x~z ∷ z*y           ∎
    where open ≡-Reasoning

branch→cons :
    {A : Set a} {_~_ : Rel A ℓ}
    {x y : A} →
    branch-type _~_ x y →
    PairwiseRelationListCons _~_ x y
branch→cons {x = x} {y} (w , z , x*w , w~z , z*y) = ++-right-cons-make (tree→list x*w) (z , w~z , (tree→list z*y))

cons→branch :
    {A : Set a} {_~_ : Rel A ℓ}
    {x y : A} →
    PairwiseRelationListCons _~_ x y →
    branch-type _~_ x y
cons→branch {x = x} {y} (z , x~z , z*y) = (x , z , leaf x , x~z , list→tree z*y)

tree→list-branch→cons-same :
    {A : Set a} {_~_ : Rel A ℓ}
    {x y : A} →
    (xy : branch-type _~_ x y) →
    tree→list (branch xy) ≡ cons (branch→cons xy)
tree→list-branch→cons-same {w} {z} b@(x , y , w*x , x~y , y*z) = ++-right-cons (tree→list w*x) (y , x~y , tree→list y*z)

-- Note this implies that list→tree is injective and tree→list is surjective
-- The surjective function (with SetoidExperiment/On.agda) implies a setoid on trees where
-- two trees are equal if they generate the same list.
list-is-onto-tree :
    {A : Set a} {_~_ : Rel A ℓ}
    {x y : A} →
    (l : PairwiseRelationList _~_ x y) →
    tree→list (list→tree l) ≡ l
list-is-onto-tree (init _) = ≡-refl
list-is-onto-tree {_~_ = _~_} {x = x} {z} (cons (y , x~y , y*z)) =
    tree→list (list→tree (cons (y , x~y , y*z)))            ≡⟨⟩
    tree→list (append-first-tree _~_ x~y (list→tree y*z))   ≡⟨⟩
    cons (y , x~y , tree→list (list→tree y*z))              ≡⟨ cong (λ q → cons (y , x~y , q)) (list-is-onto-tree y*z) ⟩
    cons (y , x~y , y*z)                                    ∎
    where open ≡-Reasoning

-- Theorems about equivalence between morphisms, essentially
module Flattening
    {A : Set a} {_~_ : Rel A ℓ}
    (~-trans : Transitive _~_)
    (≈-rel : {x y : A} → Rel (x ~ y) ℓ₁)
    (≈-eq : ∀ {x y} → IsEquivalence (≈-rel {x} {y}))
    (~-trans-assoc : ∀ {w x y z : A} {w~x : w ~ x} {x~y : x ~ y} {y~z : y ~ z} → ≈-rel (~-trans w~x (~-trans x~y y~z)) (~-trans (~-trans w~x x~y) y~z))
    (~-trans-cong : ∀ {x y z} → Congruent₂ (≈-rel {x} {y}) (≈-rel {y} {z}) (≈-rel {x} {z}) ~-trans)
    where
    private
        _→~←_ = ~-trans
        infixr 5 _→~←_

        _≈_ = ≈-rel
        infix 1 _≈_

        module _ {x y : A} where
            open IsEquivalence (≈-eq {x} {y}) public
            open import Relation.Binary.Reasoning.Setoid (equality→setoid (≈-eq {x} {y})) public

    fold : {x y : A} → PairwiseRelationListCons _~_ x y → x ~ y
    fold = foldl _~_ _→~←_

    flatten : {x y : A} → branch-type _~_ x y → x ~ y
    flatten = trans-flatten-branch _~_ _→~←_

    foldl-pop :
        {x y z : A} →
        (x~y : x ~ y)
        (y*z : PairwiseRelationListCons _~_ y z) →
        fold (x~y ∷' cons y*z) ≈ x~y →~← fold y*z
    foldl-pop {x = w} {x} {z} w~x (y , x~z , init .z) = refl
    foldl-pop {x = v} {w} {z} v~w (x , w~x , cons x*z) = begin
        fold (w , v~w , cons (x , w~x , cons x*z))  ≈⟨ refl ⟩
        fold (x , v~w →~← w~x , cons x*z)           ≈⟨ foldl-pop (~-trans v~w w~x) x*z ⟩
        (v~w →~← w~x) →~← fold x*z                  ≈⟨ sym ~-trans-assoc ⟩
        v~w →~← (w~x →~← fold x*z)                  ≈⟨ ~-trans-cong refl (sym (foldl-pop w~x x*z)) ⟩
        v~w →~← fold (x , w~x , cons x*z)           ∎

    -- foldl-pop-last :

    foldl-pop-trans :
        {w x y z : A} →
        (w~x : w ~ x)
        (x~y : x ~ y)
        (y*z : PairwiseRelationList _~_ y z) →
        fold ((w~x →~← x~y) ∷' y*z) ≈ w~x →~← (fold (x~y ∷' y*z))
    foldl-pop-trans w~x x~y (init _) = refl
    foldl-pop-trans {w} {x} {y} {z} w~x x~y (cons y*z) = begin
        fold (y , w~x →~← x~y , cons y*z)   ≈⟨ foldl-pop (w~x →~← x~y) y*z ⟩
        (w~x →~← x~y) →~← fold y*z          ≈⟨ sym ~-trans-assoc ⟩
        w~x →~← (x~y →~← fold y*z)          ≈⟨ ~-trans-cong refl (sym (foldl-pop x~y y*z)) ⟩
        w~x →~← fold (y , x~y , cons y*z)   ∎

    foldl-cong :
        {x y z : A} →
        {x~y₁ x~y₂ : x ~ y} →
        (same-xy : x~y₁ ≈ x~y₂)
        (y*z : PairwiseRelationList _~_ y z) →
        fold (x~y₁ ∷' y*z) ≈ fold (x~y₂ ∷' y*z)
    foldl-cong {x~y₁ = x~y₁} {x~y₂} same-xy (init _) = same-xy
    foldl-cong {x} {y} {z} {x~y₁} {x~y₂} same-xy (cons y*z@(w , y~w , w*z)) = begin
        fold (y , x~y₁ , cons y*z)  ≈⟨ foldl-pop x~y₁ y*z ⟩
        x~y₁ →~← fold y*z           ≈⟨ ~-trans-cong same-xy refl ⟩
        x~y₂ →~← fold y*z           ≈⟨ sym (foldl-pop x~y₂ y*z) ⟩
        fold (y , x~y₂ , cons y*z)  ∎

    foldl-++' :
        {x y z : A} →
        (x*y : PairwiseRelationListCons _~_ x y) →
        (y*z : PairwiseRelationListCons _~_ y z) →
        fold (x*y ++' y*z) ≈ (fold x*y) →~← (fold y*z)
    foldl-++' {x = v} {x} {z} (.x , v~x , []) (y , x~y , init _) = refl
    foldl-++' {x = v} {x} {z} (.x , v~x , []) (y , x~y , cons y*z@(y' , y~y' , y'*z)) = begin
        fold ((x , v~x , init x) ++' (y , x~y , cons y*z))      ≈⟨ refl ⟩
        fold (_ , ~-trans (~-trans v~x x~y) y~y' , y'*z)        ≈⟨ foldl-cong (sym ~-trans-assoc) y'*z ⟩
        fold (_ , ~-trans v~x (~-trans x~y y~y') , y'*z)        ≈⟨ foldl-pop-trans v~x _ y'*z ⟩
        ~-trans v~x (fold (_ , ~-trans x~y y~y' , y'*z))        ≈⟨ refl ⟩
        fold (x , v~x , init x) →~← fold (y , x~y , cons y*z)   ∎
    foldl-++' {x = v} {x} {z} (w , v~w , cons w*x) (y , x~y , y*z) = begin
        fold (v~w ∷' cons w*x ++' x~y ∷' y*z)           ≈⟨ refl ⟩
        fold (v~w ∷' (cons w*x ++ x~y ∷ y*z))           ≈⟨ reflexive (cong (λ q → fold (v~w ∷' q)) (≡-sym (++-++' w*x (x~y ∷' y*z)))) ⟩
        fold (v~w ∷' cons (w*x ++' x~y ∷' y*z))         ≈⟨ foldl-pop v~w (w*x ++' x~y ∷' y*z) ⟩
        v~w →~← fold (w*x ++' x~y ∷' y*z)               ≈⟨ ~-trans-cong refl (foldl-++' w*x (x~y ∷' y*z)) ⟩
        v~w →~← (fold w*x →~← fold (x~y ∷' y*z))        ≈⟨ ~-trans-assoc ⟩
        (v~w →~← fold w*x) →~← fold (x~y ∷' y*z)        ≈⟨ ~-trans-cong (sym (foldl-pop v~w w*x)) refl ⟩
        fold (v~w ∷' cons w*x) →~← fold (x~y ∷' y*z)    ∎

    foldl-flatten-same :
        {x y : A} →
        (b : branch-type _~_ x y) →
        fold (branch→cons b) ≈ flatten b
    foldl-flatten-same {w} {z} (x , y , leaf _ , x~y , leaf _) = refl
    foldl-flatten-same {x} {z} (x , y , leaf _ , x~y , branch yz) = begin
        fold (branch→cons (x , y , leaf x , x~y , branch yz))                               ≈⟨ refl ⟩
        fold (++-right-cons-make (tree→list (leaf x)) (y , x~y , tree→list (branch yz)))    ≈⟨ refl ⟩
        fold (++-right-cons-make (init x) (y , x~y , tree→list (branch yz)))                ≈⟨ refl ⟩
        fold (x~y ∷' (tree→list (branch yz)))                                               ≈⟨ reflexive (cong (λ q → fold (x~y ∷' q)) (tree→list-branch→cons-same yz)) ⟩
        fold (x~y ∷' cons (branch→cons yz))                                                 ≈⟨ foldl-pop x~y (branch→cons yz) ⟩
        ~-trans x~y (fold (branch→cons yz))                                                 ≈⟨ ~-trans-cong refl (foldl-flatten-same yz) ⟩
        ~-trans x~y (flatten yz)                                                            ≈⟨ refl ⟩
        flatten (x , y , leaf x , x~y , branch yz)                                          ∎
    foldl-flatten-same {w} {y} (x , y , branch wx , x~y , leaf _) = begin
        fold (branch→cons (x , y , branch wx , x~y , leaf y))                               ≈⟨ refl ⟩
        fold (++-right-cons-make (tree→list (branch wx)) (y , x~y , tree→list (leaf y)))    ≈⟨ refl ⟩
        fold (++-right-cons-make (tree→list (branch wx)) (y , x~y , init y))                ≈⟨ reflexive (cong (λ q → fold (++-right-cons-make q (y , x~y , init y))) (tree→list-branch→cons-same wx)) ⟩
        fold (++-right-cons-make (cons (branch→cons wx)) (y , x~y , init y))                ≈⟨ refl ⟩
        fold (branch→cons wx ++' (y , x~y , init y))                                        ≈⟨ foldl-++' (branch→cons wx) (x~y ∷' []) ⟩
        ~-trans (fold (branch→cons wx)) x~y                                                 ≈⟨ ~-trans-cong (foldl-flatten-same wx) refl ⟩
        ~-trans (flatten wx) x~y                                                            ≈⟨ refl ⟩
        flatten (x , y , branch wx , x~y , leaf y)                                          ∎
    foldl-flatten-same {w} {z} (x , y , branch wx , x~y , branch yz) = begin
        fold (branch→cons (x , y , branch wx , x~y , branch yz))                                ≈⟨ refl ⟩
        fold (++-right-cons-make (tree→list (branch wx)) (y , x~y , tree→list (branch yz)))     ≈⟨ reflexive (cong (λ q → fold (++-right-cons-make q (y , x~y , tree→list (branch yz)))) (tree→list-branch→cons-same wx)) ⟩
        fold (++-right-cons-make (cons (branch→cons wx)) (y , x~y , tree→list (branch yz)))     ≈⟨ reflexive ((cong (λ q → fold (++-right-cons-make (cons (branch→cons wx)) (y , x~y , q))) (tree→list-branch→cons-same yz))) ⟩
        fold (++-right-cons-make (cons (branch→cons wx)) (y , x~y , cons (branch→cons yz)))     ≈⟨ refl ⟩
        fold (branch→cons wx ++' (y , x~y , cons (branch→cons yz)))                             ≈⟨ foldl-++' (branch→cons wx) (y , x~y , cons (branch→cons yz)) ⟩
        fold (branch→cons wx) →~← fold (y , x~y , cons (branch→cons yz))                        ≈⟨ ~-trans-cong refl (foldl-pop x~y (branch→cons yz)) ⟩
        fold (branch→cons wx) →~← (x~y →~← fold (branch→cons yz))                               ≈⟨ ~-trans-assoc ⟩
        ((fold (branch→cons wx)) →~← x~y) →~← fold (branch→cons yz)                             ≈⟨ ~-trans-cong (~-trans-cong (foldl-flatten-same wx) refl) (foldl-flatten-same yz) ⟩
        ((flatten wx) →~← x~y) →~← flatten yz                                                   ≈⟨ refl ⟩
        flatten (x , y , branch wx , x~y , branch yz)                                           ∎


-- Mapping
module Mapping
    {A : Set a} {_~_ : Rel A ℓ₁} {B : Set b} {_#_ : Rel B ℓ₂}
    (f : A → B)
    (map-rel : {x y : A} → x ~ y → f x # f y)
    where

    map-branch :
        {w z : A} → branch-type _~_ w z →
        branch-type _#_ (f w) (f z)
    map-tree :
        {w z : A} → RelTree _~_ w z →
        RelTree _#_ (f w) (f z)
    map-branch {w} {z} (x , y , b₁ , x~y , b₂) = f x , f y , map-tree b₁ , map-rel x~y , map-tree b₂
    map-tree {x} {x} (leaf x) = leaf (f x)
    map-tree {x} {y} (branch xBy) = branch (map-branch xBy)

    -- This is kind of a type of folding, isn't it?
    map-cons :
        {w z : A} → PairwiseRelationListCons _~_ w z →
        PairwiseRelationListCons _#_ (f w) (f z)
    map-list :
        {w z : A} → PairwiseRelationList _~_ w z →
        PairwiseRelationList _#_ (f w) (f z)
    map-cons (x , w~x , x*z) = (map-rel w~x) ∷' map-list x*z
    map-list (init x) = init (f x)
    map-list (cons x) = cons (map-cons x)

    map-list-++ :
        {x y z : A} →
        (xy : PairwiseRelationList _~_ x y) →
        (yz : PairwiseRelationList _~_ y z) →
        map-list (xy ++ yz) ≡ map-list xy ++ map-list yz
    map-list-++ (init _) yz = ≡-refl
    map-list-++ {x = w} (cons (x , w~x , xy)) yz =
        map-list ((w~x ∷ xy) ++ yz)                 ≡⟨ cong map-list (++-left-cons (w~x ∷' xy) yz) ⟩
        map-list (w~x ∷ (xy ++ yz))                 ≡⟨⟩
        map-rel w~x ∷ (map-list (xy ++ yz))         ≡⟨ cong (map-rel w~x ∷_) (map-list-++ xy yz) ⟩
        map-rel w~x ∷ (map-list xy ++ map-list yz)  ≡⟨ ≡-sym (++-left-cons (map-rel w~x ∷' map-list xy) (map-list yz)) ⟩
        (map-rel w~x ∷ map-list xy) ++ map-list yz  ≡⟨⟩
        map-list (w~x ∷ xy) ++ map-list yz          ∎
        where open ≡-Reasoning

    map-++-left-cons :
        {x y z : A} →
        (xy : PairwiseRelationListCons _~_ x y) →
        (yz : PairwiseRelationList _~_ y z) →
        map-cons (++-left-cons-make xy yz) ≡ ++-left-cons-make (map-cons xy) (map-list yz)
    map-++-left-cons {x = w} (w~x ∷' xy) yz =
        map-cons (++-left-cons-make (w~x ∷' xy) yz)                     ≡⟨⟩
        map-cons (w~x ∷' (xy ++ yz))                                    ≡⟨⟩
        map-rel w~x ∷' (map-list (xy ++ yz))                            ≡⟨ cong (map-rel w~x ∷'_) (map-list-++ xy yz) ⟩
        map-rel w~x ∷' (map-list xy ++ map-list yz)                     ≡⟨⟩
        ++-left-cons-make (map-rel w~x ∷' map-list xy) (map-list yz)    ≡⟨⟩
        ++-left-cons-make (map-cons (w~x ∷' xy)) (map-list yz)          ∎
        where open ≡-Reasoning

    map-cons-++' :
        {x y z : A} →
        (xy : PairwiseRelationListCons _~_ x y) →
        (yz : PairwiseRelationListCons _~_ y z) →
        map-cons (xy ++' yz) ≡ map-cons xy ++' map-cons yz
    map-cons-++' {x = w} xy yz = map-++-left-cons xy (cons yz)

    map-cons-on :
        {w z : A} → PairwiseRelationListCons _~_ w z →
        PairwiseRelationListCons (_#_ Function.on f) w z
    map-list-on :
        {w z : A} → PairwiseRelationList _~_ w z →
        PairwiseRelationList (_#_ Function.on f) w z
    map-cons-on (x , w~x , x*z) = (map-rel w~x) ∷' map-list-on x*z
    map-list-on (init x) = init x
    map-list-on (cons x) = cons (map-cons-on x)

    tree→list-mapping-commutes : {x y : A} (tree : RelTree _~_ x y) →
        tree→list (map-tree tree) ≡ map-list (tree→list tree)
    tree→list-mapping-commutes (leaf x) = ≡-refl
    tree→list-mapping-commutes {x = w} {z} (branch (x , y , w*x , x~y , y*z)) =
        tree→list (map-tree (branch (x , y , w*x , x~y , y*z)))                     ≡⟨⟩
        tree→list (branch (f x , f y , map-tree w*x , map-rel x~y , map-tree y*z))  ≡⟨⟩
        tree→list (map-tree w*x) ++ map-rel x~y ∷ tree→list (map-tree y*z)          ≡⟨ cong (λ q → tree→list (map-tree w*x) ++ map-rel x~y ∷ q) (tree→list-mapping-commutes y*z) ⟩
        tree→list (map-tree w*x) ++ map-rel x~y ∷ map-list (tree→list y*z)          ≡⟨ cong (λ q → q ++ map-rel x~y ∷ map-list (tree→list y*z)) (tree→list-mapping-commutes w*x) ⟩
        map-list (tree→list w*x) ++ map-rel x~y ∷ map-list (tree→list y*z)          ≡⟨ ≡-sym (map-list-++ (tree→list w*x) (x~y ∷ tree→list y*z)) ⟩
        map-list ((tree→list w*x) ++ x~y ∷ (tree→list y*z))                         ≡⟨⟩
        map-list (tree→list (branch (x , y , w*x , x~y , y*z)))                     ∎
        where open ≡-Reasoning

    list→tree-mapping-commutes : {x y : A} (l : PairwiseRelationList _~_ x y) →
        list→tree (map-list l) ≡ map-tree (list→tree l)
    list→tree-mapping-commutes [] = ≡-refl
    list→tree-mapping-commutes {x = x} {z} (cons (y , x~y , yz)) =
        list→tree (map-list (x~y ∷ yz))                                         ≡⟨ ≡-refl ⟩
        list→tree (map-rel x~y ∷ map-list yz)                                   ≡⟨ ≡-refl ⟩
        branch (f x , f y , leaf (f x) , map-rel x~y , list→tree (map-list yz)) ≡⟨ cong (λ q → branch (f x , f y , leaf (f x) , map-rel x~y , q)) (list→tree-mapping-commutes yz) ⟩
        branch (f x , f y , leaf (f x) , map-rel x~y , map-tree (list→tree yz)) ≡⟨ ≡-refl ⟩
        map-tree (branch (x , y , leaf x , x~y , list→tree yz))                 ≡⟨ ≡-refl ⟩
        map-tree (list→tree (x~y ∷ yz))                                         ∎
        where open ≡-Reasoning
open Mapping public
