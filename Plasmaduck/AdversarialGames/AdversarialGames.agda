open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; inspect; cong; Reveal_·_is_; [_]) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Relation.Nullary.Negation using (¬_)
open import Function using (_∘_; flip)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (ℕ; _+_; _≤_; _≥_) renaming (zero to zero-ℕ; suc to suc-ℕ)
open import Data.Nat.Properties using (≤-refl; ≤-trans; <-irrefl)
open import Data.Fin using (Fin) renaming (zero to zero-fin; suc to suc-fin)
open import Data.Vec using (Vec; lookup; []; _∷_; reverse)
open import Relation.Binary using (Setoid; REL; Rel; IsEquivalence)

open import Plasmaduck.Relation.Vector using (VectorSetoid; VectorSetoid')
open import Plasmaduck.SetoidExperiment.SetoidMachinery using (SetoidFunction)
open import Plasmaduck.SetoidExperiment.On using (setoid-on)
open import Plasmaduck.Data.Nat using (n≤sn)
open import Plasmaduck.Data.Product using (Σ≡)
open import Plasmaduck.Util.Case using (case_of_)
open import Plasmaduck.Util.TypeChange using (change-type; change-type-flatten)



module Plasmaduck.AdversarialGames.AdversarialGames where

open Setoid using (Carrier)

variable
    a b c ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ : Level

{-
    What things even exist?

    There is state.
    There is a stop condition (which can have a score associated with it maybe?)
    There are moves which can be taken from a state.
    There is a strategy, which, given a state, picks a move. One move can be to stop, if the stop condition if fulfilled.
    There is the adversary (which will probably not actually be modelled; we assume the adversary plays optimally, or maybe stochastically).
    - The adversary takes the state and the move made by the strategy and returns the new state that occurs after the adversary makes their move. Or maybe it catalogues the possible states that could occur.
    - In particular, there is a relation, which states that a state is a valid endpoint after a given state-move pair. The relation must have at least one valid output; ideally, the output is of known size.
    - Do we also want to let the adversary stop the game? Or maybe the game stops automatically when the stop condition is fulfilled? But then we have to prove that the stop condition is not fulfilled at each step...
    There is a partial game, which is a sequence of states and moves.
    There is a full game, which is a partial game that ends on a stop state.
    - The full game has an associated score, maybe? and a number of turns it took.


    We could also frame it differently. We could have the set of possible end states, which gets restricted as the game is played.
    The stop condition would then be that there is only one possible end state.
-}

module Types
    (State : Set a)
    (Moveset : State → Set c)
    (start-condition : State → Set ℓ₃)
    (continue-condition : State → Set ℓ₄)
    (stop-condition : State → Set ℓ₁)
    (is-possible-next-state : REL State (Σ State Moveset) ℓ₂)
    (start-exists : Σ State start-condition)
    (continuation-exists : (s₁ : State) → stop-condition s₁ ⊎ (continue-condition s₁ × (∀ (m : Moveset s₁) → Σ State λ s₂ → is-possible-next-state s₂ (s₁ , m))))
    where

    module NoStrategy where
        -- A valid partially played game
        data PartialGame : ℕ → Set (a ⊔ c ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄)
        current-state : {n : ℕ} → PartialGame n → State
        data PartialGame where
            game-start : (s : State) → start-condition s → PartialGame 0
            next-move : {n : ℕ} → (game : PartialGame n) → continue-condition (current-state game) → (move : Moveset (current-state game)) → (s : State) → is-possible-next-state s (current-state game , move) → PartialGame (suc-ℕ n)
        current-state (game-start s _) = s
        current-state (next-move game _ _ s _) = s

        record FullGame (n : ℕ) : Set (a ⊔ c ⊔ ℓ₁ ⊔ ℓ₃ ⊔ ℓ₂ ⊔ ℓ₄) where
            field
                partial-game : PartialGame n
                is-complete : stop-condition (current-state partial-game)


    {-
        A strategy with memory. It is allowed to not declare a move at any time.
        However, if it fails to make a move in some actual game,
        it is not a valid strategy (see IsValidStrategy below).
    -}
    record PartialStrategy (ℓ₆ : Level) : Set (a ⊔ c ⊔ lsuc ℓ₆) where
        field
            Data : Set ℓ₆                                                           -- The memory set
            starting-data : Data                                                    -- The memory it starts the game with
            partial-strategy : ((s , _) : State × Data) → Maybe (Moveset s × Data)  -- The move it makes (and the memory update) at a given state

    module GameWithStrategy {ℓ₆ : Level} (strategy' : PartialStrategy ℓ₆) where
        Data = strategy' .PartialStrategy.Data
        starting-data = strategy' .PartialStrategy.starting-data
        partial-strategy = strategy' .PartialStrategy.partial-strategy

        GameState = State × Data

        -- s₂ can follow from s₁ under the given strategy
        -- Note that nothing follows from any point where the strategy declares no move.
        is-next-state : Rel GameState (ℓ₂ ⊔ ℓ₆)
        is-next-state (s₂ , d₂) (s₁ , d₁) with partial-strategy (s₁ , d₁)
        ... | just (m₁ , d₂') = d₂ ≡ d₂' × is-possible-next-state s₂ (s₁ , m₁)
        ... | nothing = Lift _ ⊥

        -- ... what a horrible lemma
        -just-forces-is-next-state : ((s₂ , d₂) g@(s₁ , _) : GameState) → ((m₁ , d₂') : Moveset s₁ × Data) → partial-strategy g ≡ just (m₁ , d₂') → is-next-state (s₂ , d₂) g ≡ (d₂ ≡ d₂' × is-possible-next-state s₂ (s₁ , m₁))
        -just-forces-is-next-state (s₂ , d₂) (s₁ , d₁) (m₁ , d₂') partial≡ with partial-strategy (s₁ , d₁)
        ... | just (m₁' , d₂'') = case partial≡ of λ { ≡-refl → ≡-refl }
        ... | nothing = case partial≡ of λ ()

        -is-next-state-forces-is-possible-next-state : {s₂ s₁ : GameState} → is-next-state s₂ s₁ → Σ (Moveset (s₁ .proj₁)) λ m → is-possible-next-state (s₂ .proj₁) (s₁ .proj₁ , m)
        -is-next-state-forces-is-possible-next-state {s₂ = s₂} {s₁} s₂-follows-s₁ with partial-strategy s₁
        -is-next-state-forces-is-possible-next-state {s₂ = s₂} {s₁} s₂-follows-s₁ | just (m , d) = m , s₂-follows-s₁ .proj₂
        -is-next-state-forces-is-possible-next-state () | nothing

        -- PartialGame n is a partially played game in which n moves have been made by the given strategy.
        -- Note that the game starts with an initial state before any moves are made,
        --   hence the number of states is 1+n, and there is always at least one state.
        data PartialGame : ℕ → Set (a ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄ ⊔ ℓ₆)
        current-state : {n : ℕ} → PartialGame n → GameState
        data PartialGame where
            game-start : (s : State) → start-condition s → PartialGame 0
            next-move : {n : ℕ} → (game : PartialGame n) → continue-condition (current-state game .proj₁) → (s : GameState) → is-next-state s (current-state game) → PartialGame (suc-ℕ n)
        current-state (game-start s _) = s , starting-data
        current-state (next-move game _ s _) = s

        started-game-exists : PartialGame 0
        started-game-exists = game-start (start-exists .proj₁) (start-exists .proj₂)

        -- For all possible games that this strategy could actually play, it makes a move.
        -- That is, the strategy doesn't have to generate a move if it can prove that
        --   it would never get into that position in the first place.
        -- Also note it does not have to generate a move if it can show that the game is in a stop condition.
        IsValidStrategy : Set _
        IsValidStrategy = {n : ℕ} → (game : PartialGame n) → stop-condition (current-state game .proj₁) ⊎ Σ (Moveset (current-state game .proj₁) × Data) λ move → partial-strategy (current-state game) ≡ just move

        get-state-from-game : {n : ℕ} → PartialGame n → Fin (suc-ℕ n) → GameState
        get-state-from-game game zero-fin = current-state game
        get-state-from-game (next-move game _ s _) (suc-fin i) = get-state-from-game game i

        game-to-state-vector : {n : ℕ} → PartialGame n → Vec State (suc-ℕ n)
        game-to-state-vector {n = zero-ℕ} (game-start s _) = s ∷ []
        game-to-state-vector {n = suc-ℕ n} (next-move game _ s _) = (proj₁ s) ∷ (game-to-state-vector game)

        game-prod-to-vector-prod : Σ ℕ PartialGame → Σ ℕ (Vec State)
        game-prod-to-vector-prod (n , game) = suc-ℕ n , game-to-state-vector game

        get-lookup : {n : ℕ} → (game : PartialGame n) → (i : Fin (suc-ℕ n)) → proj₁ (get-state-from-game game i) ≡ lookup (game-to-state-vector game) i
        get-lookup (game-start s _) zero-fin = ≡-refl
        get-lookup current-game@(next-move game _ s _) zero-fin = ≡-refl
        get-lookup (next-move game _ s _) (suc-fin i) = get-lookup game i

        record FullGame (n : ℕ) : Set (a ⊔ ℓ₁ ⊔ ℓ₃ ⊔ ℓ₂ ⊔ ℓ₄ ⊔ ℓ₆) where
            field
                partial-game : PartialGame n
                is-complete : stop-condition (proj₁ (current-state partial-game))

        module _ {_~_ : Rel State ℓ₅} (isEquivalence : IsEquivalence _~_) where
            StateSetoid : Setoid a ℓ₅
            StateSetoid = record {
                Carrier = State;
                _≈_ = _~_;
                isEquivalence = isEquivalence
                }

            n-PartialGameSetoid : ℕ → Setoid (a ⊔ ℓ₃ ⊔ ℓ₄ ⊔ ℓ₂ ⊔ ℓ₆) (a ⊔ ℓ₅)
            n-PartialGameSetoid n = setoid-on (VectorSetoid StateSetoid (suc-ℕ n)) (game-to-state-vector {n = n})

            PartialGameSetoid : Setoid (a ⊔ ℓ₃ ⊔ ℓ₄ ⊔ ℓ₂ ⊔ ℓ₆) (a ⊔ ℓ₅)
            PartialGameSetoid = setoid-on (VectorSetoid' StateSetoid) game-prod-to-vector-prod

            n-FullGameSetoid : ℕ → Setoid (a ⊔ ℓ₃ ⊔ ℓ₄ ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₆) (a ⊔ ℓ₅)
            n-FullGameSetoid n = setoid-on (VectorSetoid StateSetoid (suc-ℕ n)) (game-to-state-vector ∘ FullGame.partial-game)

            FullGameSetoid : Setoid (a ⊔ ℓ₃ ⊔ ℓ₄ ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₆) (a ⊔ ℓ₅)
            FullGameSetoid = setoid-on {A = Σ ℕ FullGame} (VectorSetoid' StateSetoid) (λ (n , game) → game-prod-to-vector-prod (n , FullGame.partial-game game))


        Strategy-takes-≥-n-moves : (n : ℕ) → Set _
        Strategy-takes-≥-n-moves n = {m : ℕ} → FullGame m → m ≥ n

        -- If a strategy can ever get stuck in a loop, it cannot be upper-bounded.
        Strategy-takes-≤-n-moves : (n : ℕ) → Set _
        Strategy-takes-≤-n-moves n = {m : ℕ} → PartialGame m → m ≤ n


        -- Continuing a game forward
        data _extends-game_ : Rel (Σ ℕ PartialGame) (a ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄ ⊔ ℓ₆) where
            same-game : (g : Σ ℕ PartialGame) → g extends-game g
            move-made : ((m , g₁) g₂' : Σ ℕ PartialGame) → (m , g₁) extends-game g₂' →
                {continue : continue-condition (current-state g₁ .proj₁)} →
                {s : GameState} →
                {is-next : is-next-state s (current-state g₁)} →
                (suc-ℕ m , next-move g₁ continue s is-next) extends-game g₂'

        extended-game-is-longer : {g₁@(m , _) g₂@(n , _) : Σ ℕ PartialGame} → g₁ extends-game g₂ → m ≥ n
        extended-game-is-longer (same-game _) = ≤-refl
        extended-game-is-longer {g₁ = m , g₁} {g₂ = n , g₂} (move-made _ _ g₁-extends-g₂) = ≤-trans (extended-game-is-longer g₁-extends-g₂) n≤sn


        open NoStrategy using () renaming (PartialGame to NoStrategyPartialGame; FullGame to NoStrategyFullGame; game-start to game-start-no-strategy; next-move to next-move-no-strategy)
        remove-strategy-partial : {n : ℕ} → PartialGame n → NoStrategyPartialGame n
        remove-strategy-current-state : {n : ℕ} → (game : PartialGame n) → current-state game .proj₁ ≡ NoStrategy.current-state (remove-strategy-partial game)
        remove-strategy-partial (game-start s pf) = game-start-no-strategy s pf
        remove-strategy-partial (next-move game pf₁ s pf₂) with -is-next-state-forces-is-possible-next-state pf₂
        ... | (m , possible-with-m) = next-move-no-strategy (remove-strategy-partial game) (change-type (cong continue-condition (remove-strategy-current-state game)) pf₁) (change-type (cong Moveset (remove-strategy-current-state game)) m) (s .proj₁) (change-type (cong (is-possible-next-state (s .proj₁)) (Σ≡ (remove-strategy-current-state game) (((≡-sym (change-type-flatten (cong Moveset (remove-strategy-current-state game)) (cong Moveset (≡-sym (remove-strategy-current-state game))) {x = m})))))) possible-with-m)
        remove-strategy-current-state (game-start s pf) = ≡-refl
        remove-strategy-current-state (next-move game pf₁ s pf₂) = ≡-refl

        remove-strategy-full : {n : ℕ} → FullGame n → NoStrategyFullGame n
        remove-strategy-full (record {partial-game = game; is-complete = pf}) = record {partial-game = remove-strategy-partial game; is-complete = change-type (cong stop-condition (remove-strategy-current-state game)) pf}

    open GameWithStrategy using (IsValidStrategy)

    ValidStrategy : (ℓ₆ : Level) → Set _
    ValidStrategy ℓ₆ = Σ (PartialStrategy ℓ₆) IsValidStrategy

    module GameWithValidStrategy {ℓ₆ : Level} ((strategy , is-valid-strategy) : ValidStrategy ℓ₆) where
        open GameWithStrategy strategy public

        step-game : {n : ℕ} → PartialGame n → FullGame n ⊎ PartialGame (suc-ℕ n)
        step-game game with is-valid-strategy game
        ... | inj₁ stop = inj₁ record {partial-game = game; is-complete = stop}
        ... | inj₂ ((m , d) , moves-pf) with continuation-exists (current-state game .proj₁)
        ...     | inj₁ stop' = inj₁ record {partial-game = game; is-complete = stop'}           -- The strategy is allowed to keep going (if any continuation exists), but we cut it off here. The longer game is still a valid game for the purposes of bounding the strategy's overall performance.
        ...     | inj₂ (continue-pf , all-moves-continue) with all-moves-continue m
        ...         | s' , is-valid-continuation with partial-strategy (current-state game) | inspect partial-strategy (current-state game)
        ...             | just x | [ thing ] = inj₂ (next-move game continue-pf (s' , d) (change-type (≡-sym (-just-forces-is-next-state (s' , d) (current-state game) x thing)) (case moves-pf of λ { ≡-refl → ≡-refl , is-valid-continuation })))

        upper-bound→finished-game : {n : ℕ} → Strategy-takes-≤-n-moves n → Σ ℕ FullGame
        upper-bound→finished-game {n = n} ≤-n-moves with helper (suc-ℕ n)
            where
                helper : (i : ℕ) → PartialGame i ⊎ Σ ℕ FullGame
                helper zero-ℕ = inj₁ started-game-exists
                helper (suc-ℕ i) with helper i
                ... | inj₂ full-game = inj₂ full-game
                ... | inj₁ partial-game with step-game partial-game
                ...     | inj₁ full-game = inj₂ (i , full-game)
                ...     | inj₂ partial-game' = inj₁ partial-game'
        ... | inj₂ full-game = full-game
        ... | inj₁ partial-game = ⊥-elim (<-irrefl ≡-refl (≤-n-moves partial-game))

    open GameWithValidStrategy using (Strategy-takes-≥-n-moves; Strategy-takes-≤-n-moves)



    -- For problems where the question is "how few moves can you guarantee a solution in?"
    lower-bound-moves-via-strategy : (ℓ₆ : Level) → ℕ → Set _
    lower-bound-moves-via-strategy ℓ₆ n = ∀ (strategy : ValidStrategy ℓ₆) → Strategy-takes-≥-n-moves strategy n

    lower-bound-moves : (ℓ₆ : Level) → ℕ → Set _
    lower-bound-moves ℓ₆ n = ∀ {m : ℕ} (_ : NoStrategyFullGame m) → m ≥ n
        where open NoStrategy using () renaming (FullGame to NoStrategyFullGame)

    upper-bound-moves : (ℓ₆ : Level) → ℕ → Set _
    upper-bound-moves ℓ₆ n = Σ (ValidStrategy ℓ₆) λ strategy → Strategy-takes-≤-n-moves strategy n

    minimally-solvable-in-n-moves : (ℓ₆ ℓ₇ : Level) → ℕ → Set _
    minimally-solvable-in-n-moves ℓ₆ ℓ₇ n = lower-bound-moves ℓ₆ n × upper-bound-moves ℓ₇ n
