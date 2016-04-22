module Logic.Core where

open import Prelude renaming (¬_ to ~_)
import Data.Vec.N-ary as N-ary
open N-ary

infixl 4 _∨_
infixl 5 _∧_
infixl 6 ¬_
infix 7 #_

-- propositions are indexed by the number of free variables

data Prop (n : ℕ) : Set where
  #_ : (v : Fin n) → Prop n
  _∧_ : (P : Prop n) → (Q : Prop n) → Prop n
  _∨_ : (P : Prop n) → (Q : Prop n) → Prop n
  ¬_ : (P : Prop n) → Prop n
  tt : Prop n
  ff : Prop n

module _ {n} where
  infixr 3 _⇒_
  infix 3 _⇔_

  -- implication and equivalence can be defined in terms of the more basic
  -- operations

  _⇒_ : Prop n → Prop n → Prop n
  A ⇒ B = ¬ A ∨ B

  _⇔_ : Prop n → Prop n → Prop n
  A ⇔ B = (A ⇒ B) ∧ (B ⇒ A)

  intros : N-ary n (Prop n) (Prop n) → Prop n
  intros f = f $ⁿ tabulate {n = n} #_

  -- a proposition can be folded by providing functions to put in place of each
  -- operation

  foldP : ∀ {ℓ}{A : Set ℓ}
          → (var : Fin n → A)
          → (and : A → A → A)
          → (or  : A → A → A)
          → (neg : A → A)
          → (truth : A)
          → (falsehood : A)
          → Prop n → A
  foldP var and or neg truth falsehood = rec
    where
      rec : _ → _
      rec (# v) = var v
      rec (P ∧ Q) = and (rec P) (rec Q)
      rec (P ∨ Q) = or (rec P) (rec Q)
      rec (¬ P) = neg (rec P)
      rec tt = truth
      rec ff = falsehood

  -- Convert a proposition in classical logic into a proposition in the universe
  -- of Agda types. Note that this changes the meaning of the proposition in
  -- many cases, since Agda types are constructive whereas propositional logic is
  -- classical.

  private
    N-indexed : ∀ {a b c}{A : Set a}{B : Set b}{C : Set c} n → (B → C) → N-ary n A B → N-ary n A C
    N-indexed zero P f = P f
    N-indexed (suc n) P f x = N-indexed n P (f x)

    N-indexed₂ : ∀ {a b c}{A : Set a}{B : Set b}{C : Set c} n → (B → B → C) → N-ary n A B → N-ary n A B → N-ary n A C
    N-indexed₂ zero P f g = P f g
    N-indexed₂ (suc n) P f g x = N-indexed₂ n P (f x) (g x)

  reify : Prop n → N-ary n Set Set
  reify = foldP (curryⁿ ∘ indexVec)
                (N-indexed₂ n _×_)
                (N-indexed₂ n _⊎_)
                (N-indexed n ~_)
                (curryⁿ {n} (const ⊤))
                (curryⁿ {n} (const ⊥))

  -- evaluate a proposition with the variables taking the provided values

  eval : Vec Bool n → Prop n → Bool
  eval env = foldP (flip indexVec env) _&&_ _||_ not true false
