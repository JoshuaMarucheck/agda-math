open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; cong; cong-app; inspect; [_]) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open import Relation.Binary using (Setoid; Rel; tri<; tri≈; tri>; Reflexive; Symmetric; Transitive; IsEquivalence)
open import Function using (_∘_; _∋_; flip)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Nat using (ℕ; _+_; _∸_; _≤_; _<_; s≤s⁻¹; s≤s; z≤n; _⊓_; <-cmp) renaming (zero to zeroℕ; suc to sucℕ)
open import Data.Nat.Properties using (≤-reflexive; ≤-refl; ≤-trans; ≤-<-trans; <-≤-trans; <-irrefl; <⇒≤; +-suc; +-comm; +-∸-assoc; ∸-mono; m≤n⇒m∸n≡0; m+n≤o⇒m≤o; m+n≤o⇒n≤o; m+[n∸m]≡n; +-mono-≤-<; +-mono-<-≤; +-mono-≤; m≤n⇒m⊓n≡m; n∸n≡0; module ≤-Reasoning)
open import Data.Fin using (Fin; fromℕ<; toℕ) renaming (_≤_ to _≤-fin_; zero to zero-fin; suc to suc-fin)
open import Data.Fin.Properties using (toℕ<n)
open import Data.List using (List; _∷_; []; _++_; _∷ʳ_; length; lookup; drop; take; tabulate; foldl; map; concat; zipWith; reverse; reverseAcc)
open import Data.List.Properties using (length-drop; length-take; length-tabulate; tabulate-cong; concat-++; foldl-cong; foldl-++; reverse-++; reverse-involutive; length-map; ++-assoc; length-++)
open import Data.List.Relation.Unary.All using (All)
open import Data.List.Relation.Unary.Any using ()

open import Plasmaduck.SetoidExperiment.SetoidMachinery using (discrete-setoid; SetoidFunction; SetoidFunctionEquality; _←_)
open import Plasmaduck.Util.TypeChange using (change-type; change-type-proof-irrelevance; change-type-input-dependence-irrelevance; change-type-output-dependence-commute; cong₂-dependent)
open import Plasmaduck.Util.Case using (case_of_)
open import Plasmaduck.Data.Nat using (n≤n; n≤sn; s≡s⁻¹; m>0⇒m=sn; m<o∧n<p⇒s[m+o]<n+p; ≤-recompute)
open import Plasmaduck.Relation.Equivalence using (irrelevant-cong)
open import Plasmaduck.Function.Properties using (Congruent₂; LeftCongruent; RightCongruent; EssentiallyIdentical)



module Plasmaduck.Data.List where

variable
    a b c α β γ ℓ : Level


All-++ :
    {A : Set a}
    {P : A → Set b}
    {l l' : List A}
    (l-all : All P l)
    (l'-all : All P l') →
    All P (l ++ l')
All-++ {l = []} l-all l'-all = l'-all
All-++ {l = x ∷ l} (px All.∷ l-all) l'-all = px All.∷ All-++ {l = l} l-all l'-all

All-concat :
    {A : Set a}
    {P : A → Set b}
    {l : List (List A)}
    (l-all : All (λ q → All P q) l) →
    All P (concat l)
All-concat {l = []} All.[] = All.[]
All-concat {l = [] ∷ xss} (All.[] All.∷ xss-all) = All-concat xss-all
All-concat {l = (x ∷ xs) ∷ xss} ((px All.∷ xs-all) All.∷ xss-all) = px All.∷ All-concat (xs-all All.∷ xss-all)

All-map :
    {A : Set a}
    {B : Set b}
    (f : A → B)
    (P : A → Set α)
    (Q : B → Set β) →
    (∀ x → P x → Q (f x)) →
    {l : List A} →
    (All P l) →
    All Q (map f l)
All-map f P Q P⇒Q∘f {[]} All.[] = All.[]
All-map f P Q P⇒Q∘f {x ∷ l} (px All.∷ l-all) = P⇒Q∘f x px All.∷ All-map f P Q P⇒Q∘f l-all

-----------------------
--- liat and unsnoc ---
-----------------------
-- for tail and uncons, but reversed
-- i've defined my own versions of these because the standard library just takes a list and returns a Maybe,
-- and i think i can do better than that.

unsnoc :
    {A : Set a}
    (x : A)
    (l : List A) →
    A
unsnoc x [] = x
unsnoc x (y ∷ l) = unsnoc y l

liat :
    {A : Set a}
    (x : A)
    (l : List A) →
    List A
liat x [] = []
liat x (y ∷ l) = x ∷ liat y l

liat∷ʳunsnoc :
    {A : Set a}
    (x : A)
    (l : List A) →
    liat x l ∷ʳ unsnoc x l ≡ x ∷ l
liat∷ʳunsnoc x [] = ≡-refl
liat∷ʳunsnoc x (y ∷ l) =
    liat x (y ∷ l) ∷ʳ unsnoc x (y ∷ l)  ≡⟨⟩
    x ∷ liat y l ∷ʳ unsnoc y l          ≡⟨ cong (x ∷_) (liat∷ʳunsnoc y l) ⟩
    x ∷ y ∷ l                           ∎
    where open ≡-Reasoning

length-liat :
    {A : Set a}
    (x : A)
    (l : List A) →
    length (liat x l) ≡ length l
length-liat x [] = ≡-refl
length-liat x (y ∷ l) = cong sucℕ (length-liat y l)

All-liat :
    {A : Set a}
    {P : A → Set ℓ}
    {x : A}
    {l : List A} →
    All P (x ∷ l) →
    All P (liat x l)
All-liat {x = x} {[]} (px All.∷ All.[]) = All.[]
All-liat {x = x} {y ∷ l} (px All.∷ All-yl) = px All.∷ All-liat All-yl

All-get-unsnoc :
    {A : Set a}
    {P : A → Set ℓ}
    {x : A}
    {l : List A} →
    All P (x ∷ l) →
    P (unsnoc x l)
All-get-unsnoc {x = x} {[]} (px All.∷ All.[]) = px
All-get-unsnoc {x = x} {y ∷ l} (px All.∷ All-yl) = All-get-unsnoc All-yl


------------------------------------------------
--- Lists of pairs and permuting index order ---
------------------------------------------------





module ListSetoid (A-setoid : Setoid c ℓ) where
    open Setoid A-setoid using (_≈_; refl; sym; trans) renaming (
        Carrier to A
        )

    _≈ZipList_ : Rel (List A) (lsuc ℓ)
    _≈ZipList_ l₁ l₂ = All Function.id (zipWith _≈_ l₁ l₂)

    _≈List_ : Rel (List A) (lsuc ℓ)
    _≈List_  l₁ l₂ = length l₁ ≡ length l₂ × l₁ ≈ZipList l₂


    ≈ZipList-refl : Reflexive _≈ZipList_
    ≈ZipList-refl {[]} = All.[]
    ≈ZipList-refl {x ∷ l} = All._∷_ refl ≈ZipList-refl

    ≈ZipList-sym : Symmetric _≈ZipList_
    ≈ZipList-sym {[]} {[]} l₁≈l₂ = All.[]
    ≈ZipList-sym {[]} {x ∷ l₂} l₁≈l₂ = All.[]
    ≈ZipList-sym {x ∷ l₁} {[]} l₁≈l₂ = All.[]
    ≈ZipList-sym {x ∷ l₁} {y ∷ l₂} (All._∷_ x~y l₁≈l₂) = All._∷_ (sym x~y) (≈ZipList-sym l₁≈l₂)


    ≈List-refl : Reflexive _≈List_
    ≈List-refl {l} = ≡-refl , ≈ZipList-refl

    ≈List-sym : Symmetric _≈List_
    ≈List-sym {l₁} {l₂} (length= , same-list) = ≡-sym length= , ≈ZipList-sym same-list

    ≈List-trans : Transitive _≈List_
    ≈List-trans {[]} {[]} {[]} _ _ = ≡-refl , All.[]
    ≈List-trans {[]} {[]} {x ∷ l₃} _ ()
    ≈List-trans {[]} {x ∷ l₂} {[]} () _
    ≈List-trans {[]} {x ∷ l₂} {x₁ ∷ l₃} () _
    ≈List-trans {x ∷ l₁} {[]} {[]} () _
    ≈List-trans {x ∷ l₁} {[]} {x₁ ∷ l₃} () _
    ≈List-trans {x ∷ l₁} {x₁ ∷ l₂} {[]} _ ()
    ≈List-trans {x ∷ l₁} {y ∷ l₂} {z ∷ l₃} (len₁=len₂ , All._∷_ x~y l₁≈l₂) (len₂=len₃ , All._∷_ y~z l₂≈l₃) = ≡-trans len₁=len₂ len₂=len₃ , All._∷_ (trans x~y y~z) (≈List-trans {l₁} {l₂} {l₃} (s≡s⁻¹ len₁=len₂ , l₁≈l₂) (s≡s⁻¹ len₂=len₃ , l₂≈l₃) .proj₂)

    ≈List-eq : IsEquivalence _≈List_
    ≈List-eq = record {
        refl = ≈List-refl;
        sym = ≈List-sym;
        trans = ≈List-trans
        }

    ListSetoid : Setoid c (lsuc ℓ)
    ListSetoid = record {
        Carrier = List A;
        _≈_ = _≈List_;
        isEquivalence = ≈List-eq
        }

open ListSetoid using (ListSetoid) public


module FoldlOnSetoid (A-setoid : Setoid a α) (B-setoid : Setoid b β) where
    open Setoid A-setoid using () renaming (
        Carrier to A;
        _≈_ to _≈A_;
        refl to ≈A-refl;
        sym to ≈A-sym
        )

    open Setoid B-setoid using () renaming (
        Carrier to B;
        _≈_ to _≈B_;
        refl to ≈B-refl;
        sym to ≈B-sym
        )

    open ListSetoid B-setoid using (_≈List_; ≈List-refl)

    map-substitute :
        (f g : A → B) →
        EssentiallyIdentical _≈A_ _≈B_ f g →
        (l l' : List A) →
        (ListSetoid._≈List_ A-setoid l l') →
        map f l ≈List map g l
    map-substitute f g f~g [] [] (≡-refl , All.[]) = ≡-refl , All.[]
    map-substitute f g f~g [] (x ∷ l') ()
    map-substitute f g f~g (x ∷ l) [] ()
    map-substitute f g f~g (x ∷ l) (x' ∷ l') (len=len' , x~x' All.∷ l~l') = cong sucℕ (
        length (map f l)    ≡⟨ length-map f l ⟩
        length l            ≡⟨ ≡-sym (length-map g l) ⟩
        length (map g l)    ∎
        ) , f~g ≈A-refl All.∷ map-substitute f g f~g l l' (s≡s⁻¹ len=len' , l~l') .proj₂
        where open ≡-Reasoning

    foldl-substitute :
        {_∙_ _∙'_ : A → B → A} →
        (∀ {x₁ x₂ : A} {y₁ y₂ : B} → x₁ ≈A x₂ → y₁ ≈B y₂ → x₁ ∙ y₁ ≈A x₂ ∙' y₂) →
        {start start' : A} →
        (start ≈A start') →
        (l l' : List B) →
        (l ≈List l') →
        foldl _∙_ start l ≈A foldl _∙'_ start' l'
    foldl-substitute {_∙_ = _∙_} {_∙'_} ∙-cong {start} {start'} start-cong [] [] (_ , All.[]) = start-cong
    foldl-substitute {_∙_ = _∙_} {_∙'_} ∙-cong {start} {start'} start-cong (x ∷ l) (x' ∷ l') (len=len' , All._∷_ x~x' l~l') = foldl-substitute ∙-cong {start ∙ x} {start' ∙' x'} (∙-cong start-cong x~x') l l' (s≡s⁻¹ len=len' , l~l')

    foldl-substitute-op :
        {_∙_ _∙'_ : A → B → A} →
        (∀ {x₁ x₂ : A} {y₁ y₂ : B} → x₁ ≈A x₂ → y₁ ≈B y₂ → x₁ ∙ y₁ ≈A x₂ ∙' y₂) →
        {start : A} →
        (l : List B) →
        foldl _∙_ start l ≈A foldl _∙'_ start l
    foldl-substitute-op ∙-cong {start} l = foldl-substitute ∙-cong {start} ≈A-refl l l ≈List-refl

    foldl-substitute-start :
        {_∙_ : A → B → A} →
        LeftCongruent _≈A_ _≈B_ _≈A_ _∙_ →
        {start start' : A} →
        (start ≈A start') →
        (l : List B) →
        foldl _∙_ start l ≈A foldl _∙_ start' l
    foldl-substitute-start ∙-left-cong {start} {start'} start-cong [] = start-cong
    foldl-substitute-start {_∙_ = _∙_} ∙-left-cong {start} {start'} start-cong (x ∷ l) = foldl-substitute-start ∙-left-cong {start ∙ x} {start' ∙ x} (∙-left-cong start-cong) l

    foldl-substitute-list :
        {_∙_ : A → B → A} →
        Congruent₂ _≈A_ _≈B_ _≈A_ _∙_ →
        {start : A} →
        (l l' : List B) →
        (l ≈List l') →
        foldl _∙_ start l ≈A foldl _∙_ start l'
    foldl-substitute-list ∙-cong l l' l-cong = foldl-substitute ∙-cong ≈A-refl l l' l-cong

-- For foldl using a binary operator on a single setoid
module MergeOnSetoid (B-setoid : Setoid c ℓ) where
    open import Plasmaduck.Function.Properties using (module SingleOperator)
    open SingleOperator B-setoid using (Associative; Identity)

    open Setoid B-setoid using () renaming (
        Carrier to B;
        _≈_ to _≈_;
        reflexive to ≈-reflexive;
        refl to ≈-refl;
        sym to ≈-sym;
        trans to ≈-trans
        )
    open ListSetoid B-setoid using (_≈List_; ≈List-refl; ≈ZipList-refl)
    open FoldlOnSetoid B-setoid B-setoid using (foldl-substitute; foldl-substitute-start; foldl-substitute-list)

    foldl-pop :
        {_*_ : B → B → B} →
        Associative _*_ →
        RightCongruent _≈_ _≈_ _≈_ _*_ →
        (start x : B) → (xs : List B) →
        foldl _*_ start (x ∷ xs) ≈ start * foldl _*_ x xs
    foldl-pop {_*_} *-assoc *-right-cong i j [] = ≈-refl
    foldl-pop {_*_} *-assoc *-right-cong i j (x ∷ xs) = begin
        foldl _*_ (i * j) (x ∷ xs)  ≈⟨ ≈-refl ⟩
        foldl _*_ ((i * j) * x) xs  ≈⟨ foldl-pop {_*_} *-assoc *-right-cong (i * j) x xs ⟩
        (i * j) * foldl _*_ x xs    ≈⟨ ≈-sym (*-assoc {i} {j} {foldl _*_ x xs}) ⟩
        i * (j * foldl _*_ x xs)    ≈⟨ *-right-cong {i} (≈-sym (foldl-pop {_*_} *-assoc *-right-cong j x xs)) ⟩
        i * (foldl _*_ (j * x) xs)  ≈⟨ ≈-refl ⟩
        i * foldl _*_ j (x ∷ xs)    ∎
        where open import Relation.Binary.Reasoning.Setoid B-setoid

    merge-pop-first :
        {_*_ : B → B → B} →
        Congruent₂ _≈_ _≈_ _≈_ _*_ →
        {id : B} →
        Identity _*_ id →
        Associative _*_ →
        (x : B) → (xs : List B) →
        foldl _*_ id (x ∷ xs) ≈ x * foldl _*_ id xs
    merge-pop-first {_*_} *-cong {id} *-id *-assoc x xs = begin
        foldl _*_ id (x ∷ xs)   ≈⟨ ≈-refl ⟩
        foldl _*_ (id * x) xs   ≈⟨ foldl-substitute-start {_*_} (λ z → *-cong z ≈-refl) {id * x} {x * id} (≈-trans (*-id .proj₁) (≈-sym (*-id .proj₂))) xs ⟩
        foldl _*_ (x * id) xs   ≈⟨ foldl-pop {_*_} *-assoc (*-cong ≈-refl) x id xs ⟩
        x * foldl _*_ id xs     ∎
        where open import Relation.Binary.Reasoning.Setoid B-setoid

    foldl-concat' :
        {_*_ : B → B → B} →
        (*-cong : Congruent₂ _≈_ _≈_ _≈_ _*_) →
        {id : B} →
        (*-id : Identity _*_ id) →
        (*-assoc : Associative _*_) →
        (start : B) →
        (xss : List (List B)) →
        foldl _*_ start (map (foldl _*_ id) xss) ≈ foldl _*_ start (concat xss)
    foldl-concat' {_*_} *-cong {id} *-id *-assoc start [] = ≈-refl
    foldl-concat' {_*_} *-cong {id} *-id *-assoc start ([] ∷ xss) = begin
        foldl _*_ start (map (foldl _*_ id) ([] ∷ xss))     ≈⟨ ≈-refl ⟩
        foldl _*_ start (id ∷ map (foldl _*_ id) xss)       ≈⟨ ≈-refl ⟩
        foldl _*_ (start * id) (map (foldl _*_ id) xss)     ≈⟨ foldl-substitute-start (λ z → *-cong z ≈-refl) (*-id .proj₂) (map (foldl _*_ id) xss) ⟩
        foldl _*_ start (map (foldl _*_ id) xss)            ≈⟨ foldl-concat' *-cong *-id *-assoc start xss ⟩
        foldl _*_ start (concat xss)                        ≈⟨ ≈-refl ⟩
        foldl _*_ start (concat ([] ∷ xss))                 ∎
        where open import Relation.Binary.Reasoning.Setoid B-setoid hiding (start)
    foldl-concat' {_*_} *-cong {id} *-id *-assoc start ((x ∷ xs) ∷ xss) = begin
        foldl _*_ start (map (foldl _*_ id) ((x ∷ xs) ∷ xss))               ≈⟨ ≈-refl ⟩
        foldl _*_ start ((foldl _*_ id (x ∷ xs)) ∷ map (foldl _*_ id) xss)  ≈⟨ ≈-refl ⟩
        foldl _*_ start ((foldl _*_ (id * x) xs) ∷ map (foldl _*_ id) xss)  ≈⟨ foldl-substitute-list *-cong ((foldl _*_ (id * x) xs) ∷ map (foldl _*_ id) xss) ((foldl _*_ (x * id) xs) ∷ map (foldl _*_ id) xss) (≡-refl , All._∷_ (foldl-substitute-start (λ z → *-cong z ≈-refl) (≈-trans (*-id .proj₁) (≈-sym (*-id .proj₂))) xs) ≈ZipList-refl) ⟩
        foldl _*_ start ((foldl _*_ (x * id) xs) ∷ map (foldl _*_ id) xss)  ≈⟨ foldl-substitute-list *-cong ((foldl _*_ (x * id) xs) ∷ map (foldl _*_ id) xss) ((x * foldl _*_ id xs) ∷ map (foldl _*_ id) xss) (≡-refl , All._∷_ (foldl-pop {_*_} *-assoc (λ {x₁} {y} {z} → *-cong ≈-refl) x id xs) ≈ZipList-refl) ⟩
        foldl _*_ start ((x * foldl _*_ id xs) ∷ map (foldl _*_ id) xss)    ≈⟨ ≈-refl ⟩
        foldl _*_ (start * (x * foldl _*_ id xs)) (map (foldl _*_ id) xss)  ≈⟨ foldl-substitute-start (λ z → *-cong z ≈-refl) *-assoc (map (foldl _*_ id) xss) ⟩
        foldl _*_ ((start * x) * foldl _*_ id xs) (map (foldl _*_ id) xss)  ≈⟨ ≈-refl ⟩
        foldl _*_ (start * x) (foldl _*_ id xs ∷ map (foldl _*_ id) xss)    ≈⟨ ≈-refl ⟩
        foldl _*_ (start * x) (map (foldl _*_ id) (xs ∷ xss))               ≈⟨ foldl-concat' *-cong *-id *-assoc (start * x) (xs ∷ xss) ⟩
        foldl _*_ (start * x) (concat (xs ∷ xss))                           ≈⟨ ≈-refl ⟩
        foldl _*_ start (concat ((x ∷ xs) ∷ xss))                           ∎
        where open import Relation.Binary.Reasoning.Setoid B-setoid hiding (start)

    foldl-concat :
        {_*_ : B → B → B} →
        (*-cong : Congruent₂ _≈_ _≈_ _≈_ _*_) →
        {id : B} →
        (*-id : Identity _*_ id) →
        (*-assoc : Associative _*_) →
        (xss : List (List B)) →
        foldl _*_ id (map (foldl _*_ id) xss) ≈ foldl _*_ id (concat xss)
    foldl-concat *-cong {id} *-id *-assoc xss = foldl-concat' *-cong *-id *-assoc id xss

    foldl-reverse :
        {_*_ : B → B → B} →
        Congruent₂ _≈_ _≈_ _≈_ _*_ →
        {id : B} →
        Identity _*_ id →
        Associative _*_ →
        (xs : List B) →
        foldl (flip _*_) id (reverse xs) ≈ foldl _*_ id xs
    foldl-reverse {_*_} *-cong {id} *-id *-assoc [] = ≈-refl
    foldl-reverse {_*_} *-cong {id} *-id *-assoc (x ∷ xs) = begin
        foldl (flip _*_) id (reverse (x ∷ xs))                          ≈⟨ ≈-reflexive (cong (foldl (flip _*_) id) (reverse-++ (x ∷ []) xs)) ⟩
        foldl (flip _*_) id (reverse xs ++ x ∷ [])                      ≈⟨ ≈-reflexive (foldl-++ (flip _*_) id (reverse xs) (x ∷ [])) ⟩
        foldl (flip _*_) (foldl (flip _*_) id (reverse xs)) (x ∷ [])    ≈⟨ foldl-substitute-start {flip _*_} (*-cong ≈-refl) (foldl-reverse *-cong *-id *-assoc xs) (x ∷ []) ⟩
        foldl (flip _*_) (foldl _*_ id xs) (x ∷ [])                     ≈⟨ ≈-refl ⟩
        x * foldl _*_ id xs                                             ≈⟨ ≈-sym (merge-pop-first {_*_} *-cong {id} *-id *-assoc x xs) ⟩
        foldl _*_ id (x ∷ xs)                                           ∎
        where open import Relation.Binary.Reasoning.Setoid B-setoid

    foldl-reverse' :
        {_*_ : B → B → B} →
        Congruent₂ _≈_ _≈_ _≈_ _*_ →
        {id : B} →
        Identity _*_ id →
        Associative _*_ →
        (xs : List B) →
        foldl (flip _*_) id xs ≈ foldl _*_ id (reverse xs)
    foldl-reverse' {_*_} *-cong {id} *-id *-assoc xs = begin
        foldl (flip _*_) id xs                      ≈⟨ ≈-reflexive (cong (foldl (flip _*_) id) (≡-sym (reverse-involutive xs))) ⟩
        foldl (flip _*_) id (reverse (reverse xs))  ≈⟨ foldl-reverse *-cong *-id *-assoc (reverse xs) ⟩
        foldl _*_ id (reverse xs)                   ∎
        where open import Relation.Binary.Reasoning.Setoid B-setoid

module _
    (A-setoid : Setoid a α)
    (B-setoid : Setoid b β)
    (C-setoid : Setoid c γ)
    where
    open Setoid A-setoid using () renaming (
        Carrier to A;
        _≈_ to _≈A_;
        refl to ≈A-refl
        )
    open Setoid B-setoid using () renaming (
        Carrier to B;
        _≈_ to _≈B_;
        refl to ≈B-refl
        )
    open Setoid C-setoid using () renaming (
        Carrier to C;
        _≈_ to _≈C_;
        refl to ≈C-refl
        )

    foldl-map-cong :
        {_*_ : A → B → A} →
        Congruent₂ _≈A_ _≈B_ _≈A_ _*_ →
        (start : A) →
        (f g : C → B) →
        (f≈g : EssentiallyIdentical _≈C_ _≈B_ f g) →
        (l : List C) →
        foldl _*_ start (map f l) ≈A
        foldl _*_ start (map g l)
    foldl-map-cong {_*_} *-cong start f g f≈g [] = ≈A-refl
    foldl-map-cong {_*_} *-cong start f g f≈g (x ∷ l) = begin
        foldl _*_ start (map f (x ∷ l))     ≈⟨ ≈A-refl ⟩
        foldl _*_ (start * f x) (map f l)   ≈⟨ FoldlOnSetoid.foldl-substitute A-setoid B-setoid {_*_} {_*_} *-cong {start * f x} {start * g x} (*-cong ≈A-refl (f≈g ≈C-refl)) (map f l) (map g l) (FoldlOnSetoid.map-substitute C-setoid B-setoid f g f≈g l l (ListSetoid.≈List-refl C-setoid)) ⟩
        foldl _*_ (start * g x) (map g l)   ≈⟨ ≈A-refl ⟩
        foldl _*_ start (map g (x ∷ l))     ∎
        where open import Relation.Binary.Reasoning.Setoid A-setoid hiding (start)


------------------------------------------------
-- And now for something completely different --
------------------------------------------------

module _ where
    open ≤-Reasoning using (begin_; step-≤) renaming (_∎ to _≤∎)

    drop-lookup : {A : Set a} (l : List A) (m n : ℕ) → .(m+n<|l| : m + n < length l) → lookup l (fromℕ< {m + n} m+n<|l|) ≡ lookup (drop m l) (fromℕ< {n} (begin
        sucℕ n              ≤⟨ ≤-reflexive (+-comm zeroℕ (sucℕ n)) ⟩
        sucℕ n + zeroℕ      ≤⟨ ≤-reflexive (≡-sym (cong (sucℕ n +_) (m≤n⇒m∸n≡0 {m = m} ≤-refl))) ⟩
        sucℕ n + (m ∸ m)    ≤⟨ ≤-reflexive (≡-sym (+-∸-assoc (sucℕ n) {m} {m} ≤-refl)) ⟩
        (sucℕ n + m) ∸ m    ≤⟨ ≤-refl ⟩
        sucℕ (n + m) ∸ m    ≤⟨ ≤-reflexive (cong (λ q → sucℕ q ∸ m) (+-comm n m)) ⟩
        sucℕ (m + n) ∸ m    ≤⟨ ∸-mono {sucℕ (m + n)} {length l} {m} {m} m+n<|l| ≤-refl ⟩
        length l ∸ m        ≤⟨ ≤-reflexive (≡-sym (length-drop m l)) ⟩
        length (drop m l)   ≤∎))
    drop-lookup l zeroℕ n m+n<|l| = ≡-refl
    drop-lookup (x ∷ l) m@(sucℕ m') n m+n<|l| =
        lookup (x ∷ l) (fromℕ< {m + n} m+n<|l|)     ≡⟨⟩
        lookup l (fromℕ< {m' + n} (s≤s⁻¹ m+n<|l|))  ≡⟨ drop-lookup l m' n (s≤s⁻¹ m+n<|l|) ⟩
        lookup (drop m' l) (fromℕ< {n} _)           ≡⟨⟩
        lookup (drop m (x ∷ l)) (fromℕ< {n} _)      ∎
        where open ≡-Reasoning

≡-by-lookup : {A : Set a} {l₁ l₂ : List A} → (same-length : length l₁ ≡ length l₂) → (∀ (i : Fin (length l₁)) → lookup l₁ i ≡ lookup l₂ (change-type (cong Fin same-length) i)) → l₁ ≡ l₂
≡-by-lookup {l₁ = []} {[]} same-length same-lookup = ≡-refl
≡-by-lookup {l₁ = x ∷ l₁} {x₁ ∷ l₂} same-length same-lookup =
    x ∷ l₁                                                              ≡⟨ cong (x ∷_) l₁=l₂ ⟩
    x ∷ l₂                                                              ≡⟨ cong (_∷ l₂) (same-lookup (fromℕ< {0} (s≤s z≤n))) ⟩
    lookup (x₁ ∷ l₂) (change-type (cong Fin same-length) zero-fin) ∷ l₂ ≡⟨ cong (λ q → lookup (x₁ ∷ l₂) q ∷ l₂) (change-type-proof-irrelevance (cong Fin same-length) (cong (λ x₂ → Fin (sucℕ (length x₂))) l₁=l₂)) ⟩
    lookup (x₁ ∷ l₂) (change-type (cong (λ x₂ → Fin (sucℕ (length x₂))) l₁=l₂) zero-fin) ∷ l₂ ≡⟨ cong (_∷ l₂) (change-type-input-dependence-irrelevance (Fin ∘ sucℕ ∘ length) (λ {q} i → lookup (x₁ ∷ q) i) {l₁} {l₂} l₁=l₂ zero-fin) ⟩
    lookup (x₁ ∷ l₂) zero-fin ∷ l₂                                      ≡⟨⟩
    x₁ ∷ l₂                                                             ∎
    where
        open ≡-Reasoning
        l₁=l₂ : l₁ ≡ l₂
        l₁=l₂ = ≡-by-lookup {l₁ = l₁} {l₂} (s≡s⁻¹ same-length) λ i →
            lookup l₁ i                                                                                                             ≡⟨ same-lookup (suc-fin i) ⟩
            lookup (x₁ ∷ l₂) (change-type (cong Fin same-length) (suc-fin i))                                                       ≡⟨ cong (lookup (x₁ ∷ l₂)) (change-type-proof-irrelevance (cong Fin same-length) (cong₂-dependent Fin (λ i₁ _ → Fin (sucℕ i₁)) (s≡s⁻¹ same-length) ≡-refl)) ⟩
            lookup (x₁ ∷ l₂) (change-type (cong₂-dependent Fin (λ i₁ _ → Fin (sucℕ i₁)) (s≡s⁻¹ same-length) ≡-refl) (suc-fin i))    ≡⟨ cong (lookup (x₁ ∷ l₂)) (≡-sym (change-type-output-dependence-commute Fin (λ i _ → Fin (sucℕ i)) (λ i → suc-fin i) (s≡s⁻¹ same-length) i)) ⟩
            lookup (x₁ ∷ l₂) (suc-fin (change-type (cong Fin (s≡s⁻¹ same-length)) i))                                               ≡⟨⟩
            lookup l₂ (change-type (cong Fin (s≡s⁻¹ same-length)) i)                                                                ∎

module TabulateFunc where
    variable
        A : Set a

    tabulate-func : {n : ℕ} (i j : ℕ) → .(j + i ≤ n) → (f : Fin n → A) →
        Fin j → A
    tabulate-func {n = n} i j j+i≤n f k = f (fromℕ< {toℕ k + i} (begin
        sucℕ (toℕ k + i)    ≡⟨⟩
        sucℕ (toℕ k) + i    ≤⟨ +-mono-≤ (toℕ<n k) n≤n ⟩
        j + i               ≤⟨ j+i≤n ⟩
        n ∎))
        where open ≤-Reasoning

    -- Starting with i, including j items
    tabulate-range : {n : ℕ} (i j : ℕ) → .(j + i ≤ n) → (f : Fin n → A) → List A
    tabulate-range {n = n} i j j+i≤n f = tabulate {n = j} (tabulate-func i j j+i≤n f)
        where open ≤-Reasoning

    tabulate-func-suc : {n : ℕ} (i j' : ℕ) → .(j+i≤n : sucℕ j' + i ≤ n) → (f : Fin n → A) →
        ∀ (k : Fin j') → (tabulate-func i (sucℕ j') j+i≤n f ∘ suc-fin) k ≡ (tabulate-func (sucℕ i) j' (≤-trans (≤-reflexive (+-suc j' i)) j+i≤n) f) k
    tabulate-func-suc {n = n} i j' j+i≤n f k =
        f (fromℕ< {toℕ (suc-fin k) + i} _)  ≡⟨ cong f (irrelevant-cong (_< n) (λ q q<n → fromℕ< {q} q<n) {y = sk+i<n} {z = ≤-<-trans (≤-reflexive (+-suc (toℕ k) i)) sk+i<n} (≡-sym (+-suc (toℕ k) i))) ⟩
        f (fromℕ< {toℕ k + sucℕ i} _)       ∎
        where
            sk+i<n : sucℕ (toℕ k) + i < n
            sk+i<n = begin
                sucℕ (sucℕ (toℕ k) + i)     ≡⟨⟩
                sucℕ (sucℕ (toℕ k)) + i     ≤⟨ +-mono-≤ (s≤s (toℕ<n k)) (n≤n {i}) ⟩
                sucℕ j' + i                 ≤⟨ ≤-recompute j+i≤n ⟩
                n                           ∎
                where open ≤-Reasoning
            open ≡-Reasoning

    tabulate-range-pop : {n : ℕ} (i j' : ℕ) → .(j+i≤n : sucℕ j' + i ≤ n) → (f : Fin n → A) →
        tabulate-range i (sucℕ j') j+i≤n f ≡ f (fromℕ< {i} (m+n≤o⇒n≤o j' {sucℕ i} {n} (≤-trans (≤-reflexive (+-suc j' i)) j+i≤n))) ∷ tabulate-range (sucℕ i) j' (≤-trans (≤-reflexive (+-suc j' i)) j+i≤n) f
    tabulate-range-pop {n = n} i j' j+i≤n f =
        tabulate-range i (sucℕ j') j+i≤n f                                              ≡⟨⟩
        tabulate (tabulate-func i (sucℕ j') j+i≤n f)                                    ≡⟨⟩
        f (fromℕ< {i} i<n) ∷ tabulate (tabulate-func i (sucℕ j') j+i≤n f ∘ suc-fin)     ≡⟨ cong (f (fromℕ< {i} i<n) ∷_) (tabulate-cong (tabulate-func-suc i j' j+i≤n f)) ⟩
        f (fromℕ< {i} i<n) ∷ tabulate (tabulate-func (sucℕ i) j' j'+si≤n f)             ≡⟨⟩
        f (fromℕ< {i} i<n) ∷ tabulate-range (sucℕ i) j' j'+si≤n f                       ∎
        where
            open ≡-Reasoning

            j'+si≤n : j' + sucℕ i ≤ n
            j'+si≤n = ≤-trans (≤-reflexive (+-suc j' i)) (≤-recompute j+i≤n)

            i<n : i < n
            i<n = m+n≤o⇒n≤o j' {sucℕ i} {n} j'+si≤n

            i+0<n : i + 0 < n
            i+0<n = ≤-<-trans (≤-reflexive (+-comm i 0)) i<n

    tabulate-range-length : {n : ℕ} (i j : ℕ) → .(j+i≤n : j + i ≤ n) → (f : Fin n → A) →
        length (tabulate-range i j j+i≤n f) ≡ j
    tabulate-range-length {n = n} i j j+i≤n f = length-tabulate (tabulate-func i j j+i≤n f)

    tabulate-range-lookup : {n : ℕ} (i j : ℕ) → .(j+i≤n : j + i ≤ n) → (f : Fin n → A) →
        (k : Fin (length (tabulate-range i j j+i≤n f))) →
        lookup (tabulate-range i j j+i≤n f) k ≡ f (fromℕ< {toℕ k + i} (<-≤-trans (+-mono-<-≤ (<-≤-trans (toℕ<n k) (≤-reflexive (tabulate-range-length i j j+i≤n f))) (n≤n {i})) j+i≤n))
    tabulate-range-lookup {n = n} i (sucℕ j') j+i≤n f zero-fin = ≡-refl
        where open ≡-Reasoning
    tabulate-range-lookup {n = n} i j@(sucℕ j') j+i≤n f k@(suc-fin k') =
        lookup (tabulate-range i j j+i≤n f) k                                                               ≡⟨⟩
        lookup (tabulate (tabulate-func i j j+i≤n f)) k                                                     ≡⟨⟩
        lookup (tabulate (tabulate-func i j j+i≤n f ∘ suc-fin)) k'                                          ≡⟨ cong₂-dependent (Fin ∘ length) lookup (tabulate-cong {f = tabulate-func i j j+i≤n f ∘ suc-fin} {g = tabulate-func (sucℕ i) j' sj+i'≤n f} (tabulate-func-suc i j' j+i≤n f)) (change-type-proof-irrelevance _ _ {k'}) ⟩
        lookup (tabulate (tabulate-func (sucℕ i) j' sj+i'≤n f)) (change-type (cong Fin same-length) k')     ≡⟨⟩
        lookup (tabulate-range (sucℕ i) j' sj+i'≤n f) (change-type (cong Fin same-length) k')               ≡⟨ tabulate-range-lookup (sucℕ i) j' sj+i'≤n f (change-type (cong Fin same-length) k') ⟩
        f (fromℕ< {toℕ (change-type (cong Fin same-length) k') + sucℕ i} thing<n)                           ≡⟨ cong f (irrelevant-cong (_< n) (λ q q<n → fromℕ< {q} q<n) {y = thing<n} {z = k+i<n} thing=) ⟩
        f (fromℕ< {toℕ k + i} k+i<n)                                                                        ∎
        where
            sj+i'≤n : j' + sucℕ i ≤ n
            sj+i'≤n = ≤-trans (≤-reflexive (+-suc j' i)) (≤-recompute j+i≤n)

            old-func = tabulate-func i j j+i≤n f
            new-func = tabulate-func (sucℕ i) j' sj+i'≤n f

            same-length : length (tabulate (old-func ∘ suc-fin)) ≡ length (tabulate new-func)
            same-length = ≡-trans (length-tabulate (old-func ∘ suc-fin)) (≡-sym (length-tabulate new-func))

            thing= : toℕ (change-type (cong Fin same-length) k') + sucℕ i ≡ toℕ k + i
            thing= =
                toℕ (change-type (cong Fin same-length) k') + sucℕ i    ≡⟨ cong (λ q → q + sucℕ i) (change-type-input-dependence-irrelevance Fin toℕ same-length k') ⟩
                toℕ k' + sucℕ i                                         ≡⟨ +-suc (toℕ k') i ⟩
                toℕ k + i                                               ∎
                where open ≡-Reasoning

            k<j : toℕ k < j
            k<j = <-≤-trans (toℕ<n k) (≤-reflexive (tabulate-range-length i j j+i≤n f))

            k+i<n : toℕ k + i < n
            k+i<n = begin
                sucℕ (toℕ k) + i            ≤⟨ +-mono-≤ k<j n≤n ⟩
                j + i                       ≤⟨ ≤-recompute j+i≤n ⟩
                n ∎
                where open ≤-Reasoning

            thing<n : toℕ (change-type (cong Fin same-length) k') + sucℕ i < n
            thing<n = ≤-<-trans (≤-reflexive thing=) k+i<n

            open ≡-Reasoning

open FoldlOnSetoid public
open MergeOnSetoid public
