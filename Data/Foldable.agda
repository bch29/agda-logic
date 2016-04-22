--
-- This module defines 'Foldable' containers, which must also have a cons
-- operation and must satisfy a few laws when folding and consing interacts.

module Data.Foldable where

open import Prelude hiding (refl; sym)

record FoldableOps {ℓ c p}
                   (T : Set ℓ → Set ℓ)
                   (_►_ : ∀ {A : Set ℓ} → A → T A → T A)
                   (empty : ∀ {A : Set ℓ} → T A)
                   (monoid : Monoid c p)
       : Set (lsuc ℓ ⊔ c ⊔ p) where

  open Monoid monoid renaming (Carrier to M)

  field
    foldMap : ∀ {A : Set ℓ} → (A → M) → T A → M

    ►-∙ : ∀ {A : Set ℓ} (f : A → M) (x : A) (xs : T A) → foldMap f (x ► xs) ≈ f x ∙ foldMap f xs
    empty-ε : ∀ {A : Set ℓ} (f : A → M) → foldMap f empty ≈ ε

  open EqReasoning (mkSetoid isEquivalence)

  ►-∙₂ : ∀ {A : Set ℓ} (f : A → M) (x y : A) (xs : T A) → foldMap f (x ► (y ► xs)) ≈ f x ∙ f y ∙ foldMap f xs
  ►-∙₂ f x y xs = begin
    foldMap f (x ► (y ► xs))     ≈⟨ ►-∙ _ _ _ ⟩
    f x ∙ foldMap f (y ► xs)     ≈⟨ ∙-cong refl (►-∙ _ _ _) ⟩
    f x ∙ (f y ∙ foldMap f xs)   ≈⟨ sym $ assoc _ _ _ ⟩
    f x ∙ f y ∙ foldMap f xs     ∎

record Foldable ℓ c p : Set (lsuc (ℓ ⊔ c ⊔ p)) where
  infixr 5 _►_
  field
    T : Set ℓ → Set ℓ
    empty : ∀ {A : Set ℓ} → T A
    _►_ : ∀ {A : Set ℓ} → A → T A → T A

    -- folding can happen in any monoid
    ops : (monoid : Monoid c p) → FoldableOps T _►_ empty monoid

  open module Ops monoid = FoldableOps (ops monoid) public

-- Lists are the prime example of something that's 'Foldable'.

module ListFoldable where
  module _ {c p} (monoid : Monoid c p) where
    open Monoid monoid renaming (Carrier to M)

    ops : FoldableOps {lzero}{c}{p} List _∷_ [] monoid
    ops = record
      { foldMap = λ f → foldr _∙_ ε ∘ map f
      ; ►-∙ = λ _ _ _ → refl
      ; empty-ε = λ _ → refl
      }

  foldable : ∀ {c p} → Foldable lzero c p
  foldable = record
    { T = List
    ; _►_ = _∷_
    ; empty = []
    ; ops = ops
    }
