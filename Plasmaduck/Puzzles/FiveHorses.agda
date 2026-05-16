open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; inspect; cong; Reveal_·_is_; [_]; refl; sym; trans)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Function using (_∘_; flip; Bijection)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (ℕ; _+_; _≤_; _≥_) renaming (zero to zero-ℕ; suc to suc-ℕ)
open import Data.Nat.Properties using (+-comm)
open import Data.Fin using (Fin; zero; suc; _↑ˡ_) renaming (_<_ to _<-fin_)
open import Data.Vec using (Vec; lookup; head; drop; []; _∷_; length)
open import Relation.Binary using (TotalOrder; DecTotalOrder; IsTotalOrder; IsStrictTotalOrder; Irreflexive; Transitive; Rel; IsEquivalence; _Respects₂_; Decidable; IsStrictPartialOrder; Trichotomous; Tri; tri<; tri≈; tri>; Asymmetric; IsDecStrictPartialOrder; DecStrictPartialOrder)

open import Plasmaduck.SetoidExperiment.SetoidMachinery using (equality→setoid; discrete-setoid)
open import Plasmaduck.Util.Case using (case_of_)
open import Plasmaduck.Relation.Equivalence using (≡-isEquivalence; all-respects-≡)
open import Plasmaduck.Relation.Order using (show-total-order; Total)
open import Plasmaduck.Relation.OrderHelpers using (WeakTri; cmp₁; cmp₂; cmp₃; _Extends_)
open import Plasmaduck.Util.TypeChange using (change-type)
open import Plasmaduck.Data.Fin using (fin-≡-dec; _∸-fin_; _↑ˡ-inverted_)
open import Plasmaduck.Counting.DiscreteCounting using (SubsetHasSize)
open import Plasmaduck.Relation.Order using (ComparableAt; show-total-order)
open import Plasmaduck.AdversarialGames.AdversarialGames using (module Types)
open import Plasmaduck.Relation.DecStrictPartialOrder using (module MassRelExtension)



module Plasmaduck.Puzzles.FiveHorses where

variable
    ℓ ℓ₂ : Level


module FiveHorsesPuzzle (ℓ₃ : Level) (horses : ℕ) (race-size : ℕ) (goal-pred : ℕ) where
    {-
        There is an unknown total order. Really, there are many total orders, and the goal is to run tests that constrain it to knowing the top so many items.
        There is a render function, which takes some races and tells you what the order of horses are. It's guaranteed to be consistent, meaning there is at least one total order which creates this ordering.
          In particular, the directed graph has no cycles (where there's an edge from A to B if B is faster than A).
        A strategy function takes a list of horses and their rendering and returns another race to add to the rendering.
    -}

    goal = suc-ℕ goal-pred

    Horse : Set
    Horse = Fin horses

    HorseSubset : Set (lsuc ℓ₃)
    HorseSubset = Horse → Set ℓ₃

    SizedHorseSubset : ℕ → Set (lsuc ℓ₃)
    SizedHorseSubset n = Σ HorseSubset (λ s → SubsetHasSize s n)

    subset-get : {n : ℕ} → SizedHorseSubset n → Fin n → Horse
    subset-get (P , bij) i = bij .Bijection.to i .proj₁

    subset-get-in-subset : {n : ℕ} → (subset : SizedHorseSubset n) → (i : Fin n) → subset .proj₁ (subset-get subset i)
    subset-get-in-subset (P , bij) i = bij .Bijection.to i .proj₂

    in-subset→has-index : {n : ℕ} → (subset : SizedHorseSubset n) → (h : Horse) → subset .proj₁ h → Σ (Fin n) (λ i → subset-get subset i ≡ h)
    in-subset→has-index (P , bij) h P[h] = case (bij .Bijection.bijective .proj₂ (h , P[h])) of λ (i , pf) → i , pf refl

    Race : Set (lsuc ℓ₃)
    Race = SizedHorseSubset race-size

    Races : (n : ℕ) → Set (lsuc ℓ₃)
    Races n = Vec Race n

    horse-≡-dec : Decidable (_≡_ {A = Horse})
    horse-≡-dec = fin-≡-dec

    make-horse-order :
        {ℓ₂ : Level} →
        (_<_ : Rel Horse ℓ₂) →
        (<-irrefl : Irreflexive _≡_ _<_) →
        (<-trans : Transitive _<_) →
        (<-cmp : Total _≡_ _<_) →
        IsStrictTotalOrder _≡_ _<_
    make-horse-order {ℓ₂} _<_ <-irrefl <-trans <-cmp = show-total-order {S = Horse} _≡_ ≡-isEquivalence _<_ <-irrefl <-trans <-cmp (all-respects-≡ _<_)

    -- HorseOrder : {ℓ₂ : Level} → Set (lsuc ℓ₂)
    -- HorseOrder {ℓ₂} = Rel Horse ℓ₂

    -- While we are solving the problem, not every horse is comparable. However, horse comparison is a strict partial order, and horses in the same race are comparable.
    record IsComparableRace {_<_ : Rel Horse ℓ} (isDecStrictPartialOrder : IsDecStrictPartialOrder _≡_ _<_) (race : Race) : Set ℓ where
        _>_ = flip _<_

        _<'_ : Rel (Fin race-size) ℓ
        _<'_ i j = subset-get race i < subset-get race j

        _≡'_ : Rel (Fin race-size) lzero
        _≡'_ i j = subset-get race i ≡ subset-get race j

        _>'_ : Rel (Fin race-size) ℓ
        _>'_ i j = subset-get race i > subset-get race j

        private
            <-irrefl : Irreflexive _≡_ _<_
            <-irrefl = isDecStrictPartialOrder .IsDecStrictPartialOrder.isStrictPartialOrder .IsStrictPartialOrder.irrefl

            <-trans : Transitive _<_
            <-trans = isDecStrictPartialOrder .IsDecStrictPartialOrder.isStrictPartialOrder .IsStrictPartialOrder.trans

            <-asym : Asymmetric _<_
            <-asym x<y y<x = <-irrefl refl (<-trans x<y y<x)
            -- <-asym = {! isDecStrictPartialOrder .IsDecStrictPartialOrder.isStrictPartialOrder  .IsStrictPartialOrder.asym !}
        field
            comparable : (i j : Fin race-size) → WeakTri (i <' j) (i ≡' j) (i >' j)

        tri-comparable : (i j : Fin race-size) → Tri (i <' j) (i ≡' j) (i >' j)
        tri-comparable i j with comparable i j
        tri-comparable i j | cmp₁ i<'j = tri< i<'j (λ i≡'j → <-irrefl i≡'j i<'j) (<-asym i<'j)
        tri-comparable i j | cmp₂ i≡'j = tri≈ (<-irrefl i≡'j) i≡'j (<-irrefl (sym i≡'j))
        tri-comparable i j | cmp₃ i>'j = tri> (<-asym i>'j) (λ i≡'j → <-irrefl (sym i≡'j) i>'j) i>'j


    record IsHorseOrder {_<_ : Rel Horse ℓ} (isDecStrictPartialOrder : IsDecStrictPartialOrder _≡_ _<_) {n : ℕ} (races : Races n) : Set ℓ where
        field
            compare-race : (i : Fin n) → IsComparableRace isDecStrictPartialOrder (lookup races i)

    record KnownGoal {_<_ : Rel Horse ℓ} (isDecStrictPartialOrder : IsDecStrictPartialOrder _≡_ _<_) : Set (ℓ ⊔ lsuc ℓ₃) where
        _>_ = flip _<_

        field
            is-top-horse : Horse → Set ℓ₃

        top-horse-subset : Set ℓ₃
        top-horse-subset = Σ Horse is-top-horse

        field
            top-horses-count : SubsetHasSize is-top-horse goal
            top-horses-ordered : ∀ (x y : top-horse-subset) → ComparableAt _≡_ _<_ (x .proj₁) (y .proj₁)
            known-maximal : (h : Horse) → is-top-horse h ⊎ ∀ ((h' , _) : top-horse-subset) → h < h'

    -- A strategy on relations of level ℓ
    Strategy : (ℓ : Level) → Set (lsuc ℓ ⊔ lsuc ℓ₃)
    Strategy ℓ =
        {_<_ : Rel Horse ℓ} →
        {isDecStrictPartialOrder : IsDecStrictPartialOrder _≡_ _<_} →
        {n : ℕ} →
        {races : Races n} →
        IsHorseOrder isDecStrictPartialOrder races →
        Race ⊎ KnownGoal isDecStrictPartialOrder

    empty-order : Rel Horse lzero
    empty-order x y = ⊥

    empty-order-is-dec-strict-partial-order : IsDecStrictPartialOrder _≡_ empty-order
    empty-order-is-dec-strict-partial-order = record {
        isStrictPartialOrder = record {
            isEquivalence = ≡-isEquivalence;
            irrefl = λ _ ();
            trans = λ ();
            <-resp-≈ = (λ _ ()) , (λ _ ())
            };
        _≟_ = horse-≡-dec;
        _<?_ = λ _ _ → no λ ()
        }

    module _ (race : Race) where
        open MassRelExtension (discrete-setoid Horse) (race .proj₂) using (extend-dec-strict-partial; extend-imposes-pairwise-cmp; extend-extends) renaming (_<'_ to extend-rel-with-race) public

    module _ {ℓ : Level} where
        open import Plasmaduck.Relation.DecStrictPartialOrder.Trees {ℓ₂ = ℓ} {A = Horse} {_≈_ = _≡_} using (GlobalTopN)
        open import Plasmaduck.Relation.Operator (discrete-setoid Horse) using (lift-rel; lift-rel-same-rel; IsDecStrictPartialOrder-transferrable)

        open Types
            (Σ (Rel Horse ℓ) λ _<_ → IsDecStrictPartialOrder _≡_ _<_)   -- State
            (λ _ → Race)                                                -- Moveset
            (λ (rel , _) → rel ≡ lift-rel ℓ empty-order)                -- start-condition
            (λ _ → ⊤)                                                   -- continue-condition
            (λ (rel , is-valid-rel) → GlobalTopN is-valid-rel goal)     -- stop-condition
            (λ (rel₂ , rel₂-valid) ((rel₁ , _) , race) → rel₂ Extends rel₁ × IsComparableRace rel₂-valid race) -- is-possible-next-state
            (((lift-rel ℓ empty-order) , IsDecStrictPartialOrder-transferrable {_#_ = empty-order} (lift-rel-same-rel ℓ empty-order) empty-order-is-dec-strict-partial-order) , refl) -- start-exists
            (λ (rel , is-valid-rel) → inj₂ (tt , λ race → (extend-rel-with-race race is-valid-rel , extend-dec-strict-partial race is-valid-rel) , extend-extends race is-valid-rel , record { comparable = λ i j → extend-imposes-pairwise-cmp race is-valid-rel (race .proj₂ .Bijection.to i , race .proj₂ .Bijection.to j)})) -- continuation-exists
            using ()

    {-
        Essentially, the set of all of these for a given strategy is a model for the adversarially generated puzzle.
        Each order represents the information the strategy knows, and thus the information you must abide to.
        However, you are allowed to change anything the strategy does not know yet.
        Each time the strategy picks a race, you must provide a new order consistent with previous orders and the new race.
        However, you do not need to give the strategy anything more, and in fact there will be many such sequences which do not give more.

        The partial sequence represents an incomplete game. You have declared an order in response to the strategy's latest race selection.
        This is the info that is prepared to be handed to the strategy, which can either declare a new race or declare that it knows the answer.
    -}
    record PossiblePartialSequence {ℓ ℓ₂ : Level} (strategy : Strategy ℓ) : Set (lsuc ℓ ⊔ lsuc ℓ₃) where
        field
            n-pred : ℕ

        n = suc-ℕ n-pred

        field
            races : Races n  -- The races are ordered from latest to earliest, that is, the head is the latest race

            orders : Vec (Σ (Rel Horse ℓ) λ _<_ → IsDecStrictPartialOrder _≡_ _<_) n                                        -- The corresponding orders after each race
            -- orders-extend : vec-pairwise-rel orders λ {(rel₁ , isOrder₁) (rel₂ , isOrder₂) → rel₁ Extends rel₂}             -- The later orders extend the earlier orders
            -- orders-hold : (i : Fin n) →
        -- orders-hold' : (i : Fin n) → IsHorseOrder (proj₂ (lookup orders i)) (vec-drop i races)                           -- Each order orders all races at and before itself
        -- orders-hold' = ?
        -- field
        --     respects-strategy : (i : Fin n-pred) → strategy (orders-hold (suc i)) ≡ inj₁ (lookup races (i ↑ˡ-inverted 1))   -- Each race is generated by strategy and the ordering on all races before it

-- --     -- This represents a completed game between the strategy and the adversary.
-- --     record PossibleSequence {ℓ : Level} (strategy : Strategy ℓ) : Set (lsuc ℓ) where
-- --         field
-- --             possiblePartialSequence : PossiblePartialSequence strategy

-- --         open PossiblePartialSequence possiblePartialSequence public

-- --         field
-- --             known-goal : KnownGoal (proj₂ (head orders))

-- --         score : ℕ
-- --         score = n  -- which is the same as length races

-- --     StrategyHasUpperBound : {ℓ : Level} (strategy : Strategy ℓ) (n : ℕ) → Set (lsuc ℓ)
-- --     StrategyHasUpperBound strategy n = ∀ (seq : PossibleSequence strategy) → PossibleSequence.score seq ≤ n

-- --     ProblemHasLowerBound : (ℓ : Level) (n : ℕ) → Set (lsuc ℓ)
-- --     ProblemHasLowerBound ℓ n = ∀ (str : Strategy ℓ) → Σ (PossibleSequence str) λ seq → PossibleSequence.score seq ≥ n

-- --     Solution : (ℓ : Level) (n : ℕ) → Set (lsuc ℓ)
-- --     Solution ℓ n = ProblemHasLowerBound ℓ n × Σ (Strategy ℓ) λ str → StrategyHasUpperBound str n


-- -- module Solving-25-5-3 where
-- --     open FiveHorsesPuzzle 25 5 3

-- --     {-
-- --         I want to see if I can walk through all of the solutions I had before.
-- --         That means I want to do a bunch of lower bound proofs:
-- --         - 3 via information theory (Finding the top three horses requires log_2 (25 * 24 * 23) bits. Each race gives log_2 (5P3 = 60) bits. It thus requires strictly more than 2 races, and thus at least 3.)
-- --         - 5 via All Horses Must Be Raced
-- --         - 6 via graph connectedness (all horses must be connected for the top horse to be known)
-- --         - 7 via fancy graph manipulation:
-- --             AFSOC we can do it in 6. Propose such a strategy.
-- --             Suppose each race just adds 4 directed edges, in order from slowest to fastest horse. This still allows all horses in the race to be compared.
-- --             Then the final graph is a tree (since we did it in 6 and connected all the nodes (else we would have uncomparable segments, which lead to failure as in the 6 case above))
-- --             Note that at every step, in every connected component, the fastest horse of that component is known.
-- --                 This is because at the end we know which horse is fastest.
-- --                 This fastest horse is comparable to all other horses.
-- --                 If a connected component has multiple uncomparable fastest horses, then in the final graph, all of those horses have paths to the fastest horse
-- --                 But those paths to the overall fastest horse, combined with the fact that they were already connected, means there's a loop
-- --                 and as we've seen, this graph must be a tree at the end.
-- --             Since the fastest horse is known, for any selected connected component, the fastest horse is raced.
-- --             Since there are no loops, *only* the fastest horse is raced.
-- --             Now consider: we know which horse is second-fastest. Second-fastest horse is comparable to all horses.
-- --             If the fastest horse had two children in the tree, then we would not know which horse was second-fastest.
-- --             Thus, fastest horse has only one child in the tree.
-- --             But this means that fastest horse was only ever involved in one race!
-- --                 Since if it was involved in two races, it would have two separate children
-- --             Thus, fastest horse must have only been involved in the *last* race
-- --                 Since if it was involved in an earlier race, it would be fastest in its connected component and thus required to race again eventually in the process of connecting all the components.
-- --             So consider: fastest horse was only ever raced in the last race. In the last race, there were 5 connected components left, and their fastest horses were raced. Fastest horse has no children at this stage. This means another horse in the last race has children (since there are 20 other unaccounted horses which are nonetheless attached to these 5)
-- --             Since the fastest horse has not been compared with any other horse, strategy does not yet know that it is fastest horse. In fact, from strategy's perspective, any of these 5 could be fastest horse.
-- --             Consider yourself as the adversary looking at this setup. Instead of making fastest horse a horse without children, pick a horse with children to be fastest. This is a valid response to the strategy.
-- --             Then there is a known fastest horse, and it has 1 child it brought with it (not in the last 5) and 1 child from the last 5. That means this horse has at least two separate children.
-- --             As before, these children are uncomparable; we do not know which is second-fastest.
-- --                 In particular, there is a partial order which does not compare the two children, yet one of them must be second-fastest. Thus, strategy cannot claim to know which child is second fastest.
-- --             This contradicts the assertion that the goal is known after only 6 moves.
-- --     -}

-- --     solution : Solution lzero 7
-- --     solution = {!   !}
