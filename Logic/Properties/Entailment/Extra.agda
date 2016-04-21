
-- This module contains extra properties of entailment which are derived from
-- equivalence (and thus can't be in 'Logic.Properties.Entailment' because they
-- would cause cyclic dependencies).

open import Prelude hiding (refl; trans; sym) renaming (¬_ to ~_)

module Logic.Properties.Entailment.Extra {n : ℕ} where

open import Logic.Core

open import Relation.Binary hiding (_⇒_)

open import Data.Bool.Properties using (booleanAlgebra)
open import Algebra.Properties.BooleanAlgebra booleanAlgebra

open import Logic.Properties.Entailment {n}
import Logic.Properties.Equivalence {n} as ≃
open ≃ using (_≃_; ≃left; ≃right)

private
  infixr 5 _=>_

  _=>_ : Bool → Bool → Bool
  x => y = not x || y

  &&elim : ∀ x y → IsTrue ((x && y) => x)
  &&elim false false = tt
  &&elim false true = tt
  &&elim true false = tt
  &&elim true true = tt

  ||intro : ∀ x y → IsTrue (x => (x || y))
  ||intro false false = tt
  ||intro false true = tt
  ||intro true false = tt
  ||intro true true = tt

∧-elim₁ : ∀ A B → A ∧ B ⊨ A
∧-elim₁ A B = fromBoolImpl₂ (λ A B → A ∧ B) (λ A B → A)
                            (λ A _ _ → &&elim (eval _ A) _) _ _

∨-intro₁ : ∀ A B → A ⊨ A ∨ B
∨-intro₁ A B = fromBoolImpl₂ (λ A B → A) (λ A B → A ∨ B)
                             (λ A _ _ → ||intro (eval _ A) _) _ _

open ⊨-Reasoning

∧-comm : ∀ A B → A ∧ B ⊨ B ∧ A
∧-comm _ _ = ≃left $ ≃.∧-comm _ _

∨-comm : ∀ A B → A ∨ B ⊨ B ∨ A
∨-comm _ _ = ≃left $ ≃.∨-comm _ _

∧-elim₂ : ∀ A B → A ∧ B ⊨ B
∧-elim₂ A B = begin
  A ∧ B    ⊨⟨ ∧-comm _ _ ⟩
  B ∧ A    ⊨⟨ ∧-elim₁ _ _ ⟩
  B        ∎

∨-intro₂ : ∀ A B → B ⊨ A ∨ B
∨-intro₂ A B = begin
  B        ⊨⟨ ∨-intro₁ _ _ ⟩
  (B ∨ A)  ⊨⟨ ∨-comm _ _ ⟩
  (A ∨ B)  ∎

∧-cong : ∀ {A A′ B B′} → A ⊨ A′ → B ⊨ B′ → A ∧ B ⊨ A′ ∧ B′
∧-cong {A}{A′}{B}{B′} aa bb = begin
  (A  ∧ B)     ⊨⟨ ∧-cong₁ aa ⟩
  (A′ ∧ B)     ⊨⟨ ∧-comm _ _ ⟩
  (B  ∧ A′)    ⊨⟨ ∧-cong₁ bb ⟩
  (B′ ∧ A′)    ⊨⟨ ∧-comm _ _ ⟩
  (A′ ∧ B′)    ∎

∨-cong : ∀ {A A′ B B′} → A ⊨ A′ → B ⊨ B′ → A ∨ B ⊨ A′ ∨ B′
∨-cong {A}{A′}{B}{B′} aa bb = begin
  (A  ∨ B)     ⊨⟨ ∨-cong₁ aa ⟩
  (A′ ∨ B)     ⊨⟨ ∨-comm _ _ ⟩
  (B  ∨ A′)    ⊨⟨ ∨-cong₁ bb ⟩
  (B′ ∨ A′)    ⊨⟨ ∨-comm _ _ ⟩
  (A′ ∨ B′)    ∎
