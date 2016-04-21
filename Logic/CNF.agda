module Logic.CNF where

open import Prelude renaming (¬_ to ~_) hiding (_+_; _*_; refl; sym; trans)

open import Logic.Core
open import Logic.Properties
open import Logic.Properties.Equivalence using (module ≃-Reasoning)

open import Algebra

import Logic.SemiringProperties as SP
open SP public using () renaming (SNF to CNF)
open SP

module _ {n} where
  ba = booleanAlgebra n
  open BooleanAlgebra ba hiding (_∨_; _∧_; ¬_; ⊤; ⊥; _≈_)
  open import Algebra.Properties.BooleanAlgebra ba
  open ≃-Reasoning {n}
  semiring = CommutativeSemiring.semiring (∧-∨-commutativeSemiring)
  open Semiring semiring using () renaming (+-identity to ∧-identity; *-identity to ∨-identity)
  open CNF semiring public renaming (⟦_⟧ to ⟦_⟧NNF; ⟦_⟧N to ⟦_⟧CNF)

--------------------------------------------------------------------------------
--  NNF
--------------------------------------------------------------------------------

  NNF = Tree (Prop n)

  -- convert a proposition into the canonical NNF type

  prop→nnf : Prop n → NNF
  prop→nnf (# v) = atom $ # v
  prop→nnf (A ∧ B) = prop→nnf A |+| prop→nnf B
  prop→nnf (A ∨ B) = prop→nnf A |*| prop→nnf B
  prop→nnf tt = atom tt
  prop→nnf ff = atom ff

  prop→nnf (¬ # v) = atom $ ¬ # v
  prop→nnf (¬ (¬ A)) = prop→nnf A
  prop→nnf (¬ tt) = atom ff
  prop→nnf (¬ ff) = atom tt

  prop→nnf (¬ (A ∧ B)) = prop→nnf (¬ A) |*| prop→nnf (¬ B)
  prop→nnf (¬ (A ∨ B)) = prop→nnf (¬ A) |+| prop→nnf (¬ B)

  -- convert a proposition into NNF, keeping its type as 'Prop'

  nnfProp : Prop n → Prop n
  nnfProp A = ⟦ prop→nnf A ⟧NNF

  -- conversion to NNF retains meaning exactly

  nnf-correct : ∀ A → A ≃ nnfProp A
  nnf-correct (# v) = refl
  nnf-correct (A ∧ B) = ∧-cong (nnf-correct A) (nnf-correct B)
  nnf-correct (A ∨ B) = ∨-cong (nnf-correct A) (nnf-correct B)
  nnf-correct tt = refl
  nnf-correct ff = refl

  nnf-correct (¬ # v) = refl
  nnf-correct (¬ (¬ A)) = trans (¬-involutive _) (nnf-correct A)
  nnf-correct (¬ tt) = ¬⊤=⊥
  nnf-correct (¬ ff) = ¬⊥=⊤

  nnf-correct (¬ (A ∧ B)) = begin
    ¬ (A ∧ B)                          ≃⟨ deMorgan₁ _ _ ⟩
    (¬ A ∨ ¬ B)                        ≃⟨ ∨-cong (nnf-correct (¬ A)) (nnf-correct (¬ B)) ⟩
    (nnfProp (¬ A) ∨ nnfProp (¬ B))    ∎

  nnf-correct (¬ (A ∨ B)) = begin
    ¬ (A ∨ B)                          ≃⟨ deMorgan₂ _ _ ⟩
    (¬ A ∧ ¬ B)                        ≃⟨ ∧-cong (nnf-correct (¬ A)) (nnf-correct (¬ B)) ⟩
    (nnfProp (¬ A) ∧ nnfProp (¬ B))    ∎

--------------------------------------------------------------------------------
--  Since semantic execution of a CNF under our particular semiring creates a
--  few superfluous 'tt' and 'ff's on the left of conjunctions and disjunctions
--  respectively, we would like a (proven correct) way of cleaning up the
--  output.
--------------------------------------------------------------------------------

  private
    clean : Prop n → Prop n

    clean (# v) = # v
    clean (¬ A) = ¬ clean A
    clean tt = tt
    clean ff = ff

    clean (tt ∧ B) = clean B
    clean (# v ∧ B) = # v ∧ clean B
    clean ((A ∧ A₁) ∧ B) = clean (A ∧ A₁) ∧ clean B
    clean ((A ∨ A₁) ∧ B) = clean (A ∨ A₁) ∧ clean B
    clean (¬ A ∧ B) = clean (¬ A) ∧ clean B
    clean (ff ∧ B) = ff ∧ clean B

    clean (ff ∨ B) = clean B
    clean (# v ∨ B) = # v ∨ clean B
    clean (A ∧ A₁ ∨ B) = clean (A ∧ A₁) ∨ clean B
    clean ((A ∨ A₁) ∨ B) = clean (A ∨ A₁) ∨ clean B
    clean (¬ A ∨ B) = clean (¬ A) ∨ clean B
    clean (tt ∨ B) = tt ∨ clean B

    clean-correct : ∀ A → clean A ≃ A

    clean-correct (# v) = refl
    clean-correct (¬ A) = ¬-cong (clean-correct A)
    clean-correct tt = refl
    clean-correct ff = refl

    clean-correct (tt ∧ B) = begin
      clean B  ≃⟨ clean-correct B ⟩
            B  ≃⟨ sym $ fst ∧-identity _ ⟩
      (tt ∧ B) ∎
    clean-correct (# v ∧ B) = ∧-cong refl (clean-correct B)
    clean-correct ((A ∧ A₁) ∧ B) = ∧-cong (clean-correct (A ∧ A₁)) (clean-correct B)
    clean-correct ((A ∨ A₁) ∧ B) = ∧-cong (clean-correct (A ∨ A₁)) (clean-correct B)
    clean-correct (¬ A ∧ B) = ∧-cong (clean-correct (¬ A)) (clean-correct B)
    clean-correct (ff ∧ B) = ∧-cong refl (clean-correct B)

    clean-correct (ff ∨ B) = begin
      clean B  ≃⟨ clean-correct B ⟩
            B  ≃⟨ sym $ fst ∨-identity _ ⟩
      (ff ∨ B) ∎
    clean-correct (# v ∨ B) = ∨-cong refl (clean-correct B)
    clean-correct (A ∧ A₁ ∨ B) = ∨-cong (clean-correct (A ∧ A₁)) (clean-correct B)
    clean-correct ((A ∨ A₁) ∨ B) = ∨-cong (clean-correct (A ∨ A₁)) (clean-correct B)
    clean-correct (¬ A ∨ B) = ∨-cong (clean-correct (¬ A)) (clean-correct B)
    clean-correct (tt ∨ B) = ∨-cong refl (clean-correct B)

--------------------------------------------------------------------------------
--  CNF
--------------------------------------------------------------------------------

  -- convert a proposition into the canonical CNF type

  prop→cnf : Prop n → CNF (Prop n)
  prop→cnf = tree→snf ∘ prop→nnf

  -- convert a proposition into CNF, keeping its type as 'Prop'

  cnfProp : Prop n → Prop n
  cnfProp = clean ∘ ⟦_⟧CNF ∘ prop→cnf

  -- conversion to CNF retains meaning exactly

  cnf-correct : ∀ A → cnfProp A ≃ A
  cnf-correct A = begin
    cnfProp A          ≃⟨ clean-correct _ ⟩
    ⟦ prop→cnf A ⟧CNF  ≃⟨ sym (tree→snf-correct (prop→nnf A)) ⟩
    nnfProp A          ≃⟨ sym $ nnf-correct A ⟩
    A                  ∎
