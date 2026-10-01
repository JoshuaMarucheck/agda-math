open import Level using (Level; _⊔_; Lift; lift; lower) renaming (zero to lzero; suc to lsuc)
open import Relation.Binary.PropositionalEquality using (_≡_; inspect; [_]) renaming (refl to ≡-refl)
open import Relation.Binary using (Rel; Decidable; Reflexive; Irreflexive; Transitive; IsStrictPartialOrder)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Function using (_∘_)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing; Is-just; to-witness; Is-nothing)
open import Data.Maybe.Relation.Unary.Any using (Any)
open import Data.Product using (Σ; _×_; _,_; proj₁ ;proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; s≤s) renaming (_⊔_ to _⊔ℕ_)
open import Data.Nat.Properties using (≤-trans; <-≤-trans; ≤-<-trans; <⇒≤; <-irrefl)
open import Data.List using (List; _∷_; [])

open import Plasmaduck.Property.Defs using (DecidableProperty; CongruentProperty)
open import Plasmaduck.Relation.Equivalence using (≡-isEquivalence)
open import Plasmaduck.Data.Nat using (n<sn; n≤sn; ⊔≥₂; ⊔≥₁)
open import Plasmaduck.Relation.RelationVector using (PairwiseRelationList)
open import Plasmaduck.Util.Case using (case_of_; inspect-case_of_)



{-
    The ascending chain condition is: for a partial order ≤,
    for any sequence of elements that monotonically increases in ≤,
    the sequence will eventually hit a maximum element.
    Proving so constructively means finding an index where it maxes out, which is impossible to do constructively in general,
    since I can give you a sequence of non-maximal element that are all equal to each other, and not knowing the sequence,
    you can never say if it will go up later.

    Thus, better, I think, is to take the strict version of the relation and say that no infinite sequences of that exist.


    Even stronger would be to give an upper bound on how long the sequence can be (given, say, the first element),
    but that would not be classically equivalent:
    Consider the rake order with elements ∙ ⊎ {ℕ × ℕ | first item smaller}. Let _<_ be the minimal (strict partial order) relation extending:
        ∙ < (0 , n) for all n
        (m , n) < (suc m , n) for all m,n
    Then every ascending sequence is finite (and can be bounded in length if you look at the second element),
    but you cannot bound the sequence length just from knowing it starts with ∙.

    I mean, the idea is that the order is well-founded (but with the order flipped). Our well-ordered set can be based on
    any well-founded datatype.

    -- Importantly, the length may not be bounded by a primitive recursive function.



    Possible representations:
    - Every coinductive generator of the appropriate type terminates (or terminates at (or by) a specific natural number)
    - Every List of elements cannot be extended indefinitely, if each pair is related by _<_
    - Every infinite sequence of A has a pair of elements not related by _<_ (thus by Plasmaduck.Counting.GeneralizedMinimum, has a minimum such pair)
-}
module Plasmaduck.Relation.AscendingChainCondition where

module AscendingChains
    {ℓ α β : Level} {A : Set ℓ} {_≈_ : Rel A α} {_≺_ : Rel A β}
    (≺-isStrictPartialOrder : IsStrictPartialOrder _≈_ _≺_)
    where

    _maybe-≺_ : Rel (Maybe A) β
    _maybe-≺_ (just x) (just y) = x ≺ y
    _maybe-≺_ (just x) nothing = Lift _ ⊤
    _maybe-≺_ nothing _ = Lift _ ⊤

    variable
        γ : Level

    -- Essentially a (possibly terminating) coinductive generator (though it guaranteed has one element)
    record AscendingChainDescriptor (γ : Level) : Set (ℓ ⊔ β ⊔ lsuc γ) where
        field
            Context : Set γ
            hd : Context → A
            tl : (ctx : Context) → Maybe (Σ Context λ ctx' → hd ctx ≺ hd ctx')

        nxt : Context → Maybe Context
        nxt ctx = Data.Maybe.map proj₁ (tl ctx)

    record AscendingChain (γ : Level) : Set (ℓ ⊔ β ⊔ lsuc γ) where
        field
            descriptor : AscendingChainDescriptor γ

        open AscendingChainDescriptor descriptor using (Context) public
        open AscendingChainDescriptor descriptor using (hd; tl; nxt)
        open Data.Maybe using (map; _>>=_)

        field
            ctx : Maybe Context

        head : Maybe A
        head = map hd ctx

        next-ctx : Maybe Context
        next-ctx = ctx >>= nxt

        next-head : Maybe A
        next-head = map hd next-ctx

        -- head≺next-head : head maybe-≺ next-head
        -- head≺next-head = inspect-case ctx of λ {
        --     (just c , eq) → {!   !};
        --     (nothing , eq) → {!   !}
        --     }
        -- head≺next-head with head | next-head | inspect (map hd) ctx | inspect (map hd) next-ctx
        -- ... | just x | just y | [ eq ] | [ eq₁ ] = {!   !}
        -- ... | just x | nothing | _ | _ = lift tt
        -- ... | nothing | just y | _ | _ = lift tt
        -- ... | nothing | nothing | _ | _ = lift tt -- (ctx Data.Maybe.>>= (Data.Maybe.map proj₁ ∘ tl))

        with-ctx : Maybe Context → AscendingChain γ
        with-ctx ctx' = record { descriptor = descriptor; ctx = ctx' }

        -- if this chain is empty,
        -- it feels a bit silly to say that there is a next chain.
        next-chain : Maybe (AscendingChain γ)
        next-chain = ctx >>= (just ∘ with-ctx ∘ nxt)

        next-is-just : Is-just ctx → Is-just next-chain
        next-is-just ctx-is-just with ctx
        ... | just _ = Any.just tt

        head-is-just : Is-just ctx → Is-just head
        head-is-just ctx-is-just with ctx
        ... | just _ = Any.just tt

        next-chain' : AscendingChain γ
        next-chain' = with-ctx next-ctx

    lift-descriptor : (β : Level) → AscendingChainDescriptor α → AscendingChainDescriptor (α ⊔ β)
    lift-descriptor β descriptor = record {
        Context = Lift β (descriptor .AscendingChainDescriptor.Context);
        hd = hd ∘ lower;
        tl = λ ctx → Data.Maybe.map (λ (ctx' , hd≺hd') → lift ctx' , hd≺hd') (tl (lower ctx))
        }
        where open AscendingChainDescriptor descriptor

    lift-chain : (β : Level) → AscendingChain α → AscendingChain (α ⊔ β)
    lift-chain β chain = record {
        descriptor = lift-descriptor β descriptor;
        ctx = Data.Maybe.map lift ctx
        }
        where open AscendingChain chain

    open AscendingChainDescriptor hiding (Context)
    open AscendingChain

    AscendingChainLength : AscendingChain γ → ℕ → Set γ
    AscendingChainLength chain zero = Is-nothing (ctx chain)
    AscendingChainLength chain (suc i) = Σ (Is-just (ctx chain)) λ is-just → AscendingChainLength (next-chain' chain) i

    AscendingChainIsFinite : AscendingChain γ → Set γ
    AscendingChainIsFinite chain = Σ ℕ (AscendingChainLength chain)

    AscendingChainCondition : (γ : Level) → Set (ℓ ⊔ β ⊔ lsuc γ)
    AscendingChainCondition γ = ∀ (chain : AscendingChain γ) → AscendingChainIsFinite chain


    -- fin-to-list : {chain : AscendingChain γ} → {i : ℕ} → AscendingChainLength chain i → List A
    -- fin-to-list {chain = chain} {zero} len = []
    -- fin-to-list {chain = chain} {suc i} (is-just , len') = (to-witness {m = head chain} (head-is-just chain is-just)) ∷ fin-to-list {chain = next-chain' chain} {i} len'

    ChainList : Set (ℓ ⊔ β)
    ChainList = Σ A λ x → Σ A λ y → PairwiseRelationList _≺_ x y

    -- fin-to-list : {chain : AscendingChain γ} → {i : ℕ} → AscendingChainLength chain (suc i) → ChainList
    -- fin-to-list {chain = chain} {zero} (is-just , len) = x , x , PairwiseRelationList.init {_~_ = _≺_} x
    --     where
    --         x : A
    --         x = to-witness {m = head chain} (head-is-just chain is-just)
    -- fin-to-list {chain = chain} {suc i} (is-just , len) = x , z , PairwiseRelationList.cons (y , {!  head-is-just chain is-just  !} , prev-chain) -- (to-witness {m = head chain} (head-is-just chain is-just)) ∷ fin-to-list {chain = next-chain' chain} {i} len'
    --     where
    --         x : A
    --         x = to-witness {m = head chain} (head-is-just chain is-just)

    --         y : A
    --         y = fin-to-list len .proj₁

    --         z : A
    --         z = fin-to-list len .proj₂ .proj₁

    --         prev-chain : PairwiseRelationList _≺_ y z
    --         prev-chain = fin-to-list len .proj₂ .proj₂

    from-list : ChainList → AscendingChain (ℓ ⊔ β)
    from-list (x , y , l) = record {
        descriptor = record {
            Context = Σ A λ z → PairwiseRelationList _≺_ z y;
            hd = proj₁;
            tl = λ { (hd' , PairwiseRelationList.init .hd') → nothing
                   ; (hd' , PairwiseRelationList.cons (z , hd'≺z , tl')) → just ((z , tl') , hd'≺z) }
            };
        ctx = just (x , l)
        }

    module Consequences (acc : AscendingChainCondition γ) where

        -- to-list : AscendingChain γ → List A
        -- to-list chain = fin-to-list {chain = chain} (acc chain .proj₂)

        -- to-list : AscendingChain γ → ChainList
        -- to-list chain = {!    !}
        -- from-list : List A → AscendingChain ?

--     _⊀_ : Rel A β
--     x ⊀ y = ¬ x ≺ y

--     AscendingChainCondition : Set (ℓ ⊔ β)
--     AscendingChainCondition = ∀ (f : ℕ → A) → Σ ℕ λ i → f i ⊀ f (suc i)

--     private
--         ≺-at-i : (ℕ → A) → ℕ → Set β
--         ≺-at-i f i = f i ≺ f (suc i)

--         ⊀-at-i : (ℕ → A) → ℕ → Set β
--         ⊀-at-i f i = f i ⊀ f (suc i)


--     decide-chain : Decidable _≺_ → (f : ℕ → A) → DecidableProperty (≺-at-i f)
--     decide-chain ≺-dec f i = ≺-dec (f i) (f (suc i))

--     private
--         module _ (f : ℕ → A) where
--             open import Plasmaduck.Counting.GeneralizedMinimum (¬_ ∘ (≺-at-i f)) (≺-at-i f) using (module FindMinimum; module IsMinimum) public
--             open IsMinimum (λ x⊀y x≺y → x⊀y x≺y) using () public

--     -- Things that result due to the ascending chain condition
--     module Consequences (acc : AscendingChainCondition) (f : ℕ → A) where
--         private
--             ≺-at-i' = ≺-at-i f
--         module _ (≺-dec-at-i : DecidableProperty ≺-at-i') where
--             private
--                 PQ-dec : ∀ i → ¬ (≺-at-i' i) ⊎ ≺-at-i' i
--                 PQ-dec i with ≺-dec-at-i i
--                 ... | no ¬a = inj₁ ¬a
--                 ... | yes a = inj₂ a
--                 open FindMinimum f PQ-dec using (find-minimum) public

--             chain-end : ℕ
--             chain-end = find-minimum (acc f) .proj₁

--             chain-end-is-end : f chain-end ⊀ f (suc chain-end)
--             chain-end-is-end = find-minimum (acc f) .proj₂ .proj₁

--             chain-is-chain : ∀ i → i < chain-end → f i ≺ f (suc i)
--             chain-is-chain i i<end = find-minimum (acc f) .proj₂ .proj₂ (i , i<end)


--         -- open Minimum ≺-at-i using (module FindMinimum) public
--     open Consequences public
--     module _ (≺-dec : Decidable _≺_) where
--         module _ (f : ℕ → A) where
--             -- open FindMinimum f (decide-chain f ≺-dec) public

module DescendingChains
    {ℓ α β : Level} {A : Set ℓ} {_≈_ : Rel A α} {_≻_ : Rel A β}
    (≻-isStrictPartialOrder : IsStrictPartialOrder _≈_ _≻_)
    where
    open AscendingChains ≻-isStrictPartialOrder using (
        ) renaming (
            AscendingChainDescriptor to DescendingChainDescriptor;
            AscendingChain to DescendingChain;
            AscendingChainIsFinite to DescendingChainIsFinite;
            AscendingChainLength to DescendingChainLength;
            AscendingChainCondition to DescendingChainCondition
        ) public

open AscendingChains public
open DescendingChains public



private
    {-
        Demonstrating that inductive types always have an order obeying the descending chain condition.
        I don't think I can show this for inductive types in general, but creating a specific order can always be done
        in this general way.
    -}
    data Thing : Set where
        start : Thing
        thing-suc : Thing → Thing
        thing-suc' : Thing → Thing → Thing

    data _is-child_ : Rel Thing lzero where
        suc~ : (x : Thing) → x is-child thing-suc x
        suc'~₁ : (x y : Thing) → x is-child thing-suc' x y
        suc'~₂ : (x y : Thing) → y is-child thing-suc' x y

    height : Thing → ℕ
    height start = 0
    height (thing-suc x) = suc (height x)
    height (thing-suc' x y) = suc (height x ⊔ℕ height y)

    open import Plasmaduck.Relation.RelationVector using (PairwiseRelationList; PairwiseRelationListCons; _++'_; init; cons)
    open import Plasmaduck.SetoidExperiment.SetoidMachinery using (discrete-setoid)

    _~_ : Rel Thing lzero
    _~_ = PairwiseRelationListCons _is-child_

    is-child⇒<height : ∀ {x y} → x is-child y → height x < height y
    is-child⇒<height (suc~ x) = n<sn
    is-child⇒<height (suc'~₁ x y) = s≤s (⊔≥₁ (height x) (height y))
    is-child⇒<height (suc'~₂ x y) = s≤s (⊔≥₂ (height x) (height y))

    ~⇒<height : ∀ {x y} → x ~ y → height x < height y
    ~⇒<height {x} {z} (y , x-is-child-y , cons y~z) = <-≤-trans (is-child⇒<height x-is-child-y) (<⇒≤ (~⇒<height y~z))
    ~⇒<height {x} (y , x-is-child-y , init z) = is-child⇒<height x-is-child-y

    ~-trans : Transitive _~_
    ~-trans = _++'_

    ~-irrefl : Irreflexive _≡_ _~_
    ~-irrefl {x} ≡-refl x~x = <-irrefl ≡-refl (~⇒<height x~x)

    ~-isStrictPartialOrder : IsStrictPartialOrder _≡_ _~_
    ~-isStrictPartialOrder = record {
        isEquivalence = ≡-isEquivalence;
        irrefl = ~-irrefl;
        trans = ~-trans;
        <-resp-≈ = (λ { ≡-refl z → z }) , (λ { ≡-refl z → z })
        }
