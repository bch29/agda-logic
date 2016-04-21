module Logic where

open import Prelude renaming (¬_ to ~_)

open import Logic.Core public
open import Logic.Properties public
open import Logic.CNF public

private
  example₁ : Prop 2
  example₁ = intros (λ P Q → ((P ⇒ Q) ⇒ P) ⇒ P)

  -- ⊨-example₁ : ⊨ example₁
  -- ⊨-example₁ = from-yes (BruteForce.⊨? example₁)

  example₂ : Prop 3
  example₂ = intros (λ P Q R -> ((P ∧ Q) ∨ R) ∧ ¬ (P ∨ R))

  example₃ : Prop 3
  example₃ = cnfProp $ intros $ λ P Q R → (P ⇒ Q) ⇔ (P ⇒ R)

  -- ¬⊨-example₂ : ~ ⊨ example₂
  -- ¬⊨-example₂ = from-no (BruteForce.⊨? example₂)

test = cnfProp example₂
