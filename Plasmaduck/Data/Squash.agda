open import Level using (Level)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; refl; sym; trans; Reveal_·_is_; [_])
open import Relation.Nullary using (Irrelevant)
open import Function using (_∘_)

open import Plasmaduck.Util.TypeChange using (change-type)



module Plasmaduck.Data.Squash where

variable
    a b α β ℓ : Level

-- shamelessly copied from the wiki: https://agda.readthedocs.io/en/latest/language/irrelevance.html
record Squash (A : Set α) : Set α where
    constructor squash
    field
        .unsquash : A

squash-irrelevant : ∀ {A : Set ℓ} → Irrelevant (Squash A)
squash-irrelevant (squash p₁) (squash p₂) = refl

squash-change-type : ∀ {A : Set α} {B : A → Set β} → {x y : A} → (x=y : x ≡ y) {Bx=By : Squash (B y) ≡ Squash (B x)} → {p : Squash (B x)} {q : Squash (B y)} →
    p ≡ change-type Bx=By q
squash-change-type refl {refl} {squash _} {squash _} = refl

squash-function : {A : Set a} {B : .A → Set b}
    (f : .(x : A) → B x) → ((squash x) : Squash A) → B x
squash-function f (squash x) = f x

unsquash-function : {A : Set a} {B : .A → Set b}
    (f : ((squash x) : Squash A) → B x) → .(x : A) → B x
unsquash-function f x = f (squash x)

irrelevant-inspect : ∀ {A : Set a} {B : .A → Set b}
          (f : .(x : A) → B x) .(x : A) → Reveal_·_is_ {B = squash-function B} (squash-function f) (squash x) (f x)
irrelevant-inspect f x = [ refl ]
