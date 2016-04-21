module Logic.Properties where

open import Prelude renaming (¬_ to ~_)

open import Logic.Core
import Logic.Properties.Equivalence as Equiv

open Equiv public using (_≃_)
open Equiv
open import Logic.Properties.Entailment public using (_⊨_; ⊨_)

open import Algebra

booleanAlgebra : ∀ n → BooleanAlgebra _ _
booleanAlgebra n = record
  { Carrier = Prop n
  ; _≈_ = _≃_
  ; _∨_ = _∨_
  ; _∧_ = _∧_
  ; ¬_ = ¬_
  ; ⊤ = tt
  ; ⊥ = ff
  ; isBooleanAlgebra = record
    { isDistributiveLattice = record
      { isLattice = record
        { isEquivalence = isEquiv
        ; ∨-comm = ∨-comm
        ; ∨-assoc = ∨-assoc
        ; ∨-cong = ∨-cong
        ; ∧-comm = ∧-comm
        ; ∧-assoc = ∧-assoc
        ; ∧-cong = ∧-cong
        ; absorptive = absorptive
        }
      ; ∨-∧-distribʳ = ∨-∧-distribʳ
      }
    ; ∨-complementʳ = ∨-complementʳ
    ; ∧-complementʳ = ∧-complementʳ
    ; ¬-cong = ¬-cong
    }
  }
