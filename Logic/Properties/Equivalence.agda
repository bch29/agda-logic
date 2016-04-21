open import Prelude hiding (refl; trans; sym) renaming (¬_ to ~_)

module Logic.Properties.Equivalence {n : ℕ} where

open import Function using (_on_)
open import Logic.Core

import Logic.Properties.Entailment as ⊨
open ⊨ using (_⊨_)

open import Algebra using (BooleanAlgebra)
open import Data.Bool.Properties using (booleanAlgebra)
module BA = BooleanAlgebra booleanAlgebra

-- if two propositions entail each other, they are called logically equivalent

infix 1 _≃_

data _≃_ (P Q : Prop n) : Set where
  equiv : P ⊨ Q → Q ⊨ P → P ≃ Q

≃left : ∀ {P Q} → P ≃ Q → P ⊨ Q
≃left (equiv l _) = l

≃right : ∀ {P Q} → P ≃ Q → Q ⊨ P
≃right (equiv _ r) = r

open import Algebra.FunctionProperties _≃_
open import Relation.Binary

--------------------------------------------------------------------------------
--  ≃ is an equivalence relation
--------------------------------------------------------------------------------

refl : Reflexive _≃_
refl = equiv ⊨.refl ⊨.refl

sym : Symmetric _≃_
sym (equiv x y) = equiv y x

trans : Transitive _≃_
trans (equiv pq qp) (equiv qr rq) = equiv (⊨.trans pq qr) (⊨.trans rq qp)

instance
  isEquiv : IsEquivalence _≃_
  IsEquivalence.refl isEquiv = refl
  IsEquivalence.sym isEquiv = sym
  IsEquivalence.trans isEquiv = trans

setoid : Setoid lzero lzero
Setoid.Carrier setoid = Prop n
Setoid._≈_ setoid = _≃_
Setoid.isEquivalence setoid = isEquiv

module ≃-Reasoning = EqReasoning setoid
  renaming (_≈⟨_⟩_ to _≃⟨_⟩_)

--------------------------------------------------------------------------------
--  Translating boolean equalities into propositional equivalences
--------------------------------------------------------------------------------

open ≃-Reasoning

fromBoolEq₁ : {f g : Prop n → Prop n} →
              (∀ A env → eval env (f A) ≡ eval env (g A)) →
              (∀ A → f A ≃ g A)
fromBoolEq₁ {f}{g} beq _ =
  equiv (⊨.fromBoolEq₁ f g beq)
        (⊨.fromBoolEq₁ g f (λ A → ≡sym ∘ beq A))

fromBoolEq₂ : {f g : Prop n → Prop n → Prop n} →
              (∀ A B env → eval env (f A B) ≡ eval env (g A B)) →
              (∀ A B → f A B ≃ g A B)
fromBoolEq₂ {f}{g} beq _ _ =
  equiv (⊨.fromBoolEq₂ f g beq)
        (⊨.fromBoolEq₂ g f (λ A B → ≡sym ∘ beq A B))

fromBoolEq₃ : {f g : (A B C : Prop n) → Prop n} →
              (∀ A B C env → eval env (f A B C) ≡ eval env (g A B C)) →
              (∀ A B C → f A B C ≃ g A B C)
fromBoolEq₃ {f}{g} beq _ _ _ =
  equiv (⊨.fromBoolEq₃ f g beq _ _ _)
        (⊨.fromBoolEq₃ g f (λ A B C → ≡sym ∘ beq A B C) _ _ _)

--------------------------------------------------------------------------------
--  Congruence of ∧ and ∨ in their first argument. Used to prove full congruence
--  later using commutativity.
--------------------------------------------------------------------------------

private
  ∧-cong₁ : ∀ {A A′ B} → A ≃ A′ → A ∧ B ≃ A′ ∧ B
  ∧-cong₁ (equiv r l) = equiv (⊨.∧-cong₁ r) (⊨.∧-cong₁ l)

  ∨-cong₁ : ∀ {A A′ B} → A ≃ A′ → A ∨ B ≃ A′ ∨ B
  ∨-cong₁ (equiv r l) = equiv (⊨.∨-cong₁ r) (⊨.∨-cong₁ l)

--------------------------------------------------------------------------------
--  Proofs of each of the minimum conditions for our propositional logic to form
--  a boolean algebra
--------------------------------------------------------------------------------

∧-assoc : Associative _∧_
∧-assoc = fromBoolEq₃ (λ A _ _ _ → BA.∧-assoc (eval _ A) _ _)

∨-assoc : Associative _∨_
∨-assoc = fromBoolEq₃ (λ A _ _ _ → BA.∨-assoc (eval _ A) _ _)

∧-comm : Commutative _∧_
∧-comm = fromBoolEq₂ (λ A _ _ → BA.∧-comm (eval _ A) _)

∨-comm : Commutative _∨_
∨-comm = fromBoolEq₂ (λ A _ _ → BA.∨-comm (eval _ A) _)

∨-∧-distribʳ : _∨_ DistributesOverʳ _∧_
∨-∧-distribʳ = fromBoolEq₃ (λ _ B _ _ → BA.∨-∧-distribʳ _ (eval _ B) _)

¬-cong : ¬_ Preserves _≃_ ⟶ _≃_
¬-cong (equiv l r) = equiv (⊨.contra r) (⊨.contra l)

∨-absorbs-∧ : _∨_ Absorbs _∧_
∨-absorbs-∧ = fromBoolEq₂ (λ A _ _ → fst BA.absorptive (eval _ A) _)

∧-absorbs-∨ : _∧_ Absorbs _∨_
∧-absorbs-∨ = fromBoolEq₂ (λ A _ _ → snd BA.absorptive (eval _ A) _)

absorptive : Absorptive _∨_ _∧_
absorptive = ∨-absorbs-∧ , ∧-absorbs-∨

∧-complementʳ : RightInverse ff ¬_ _∧_
∧-complementʳ = fromBoolEq₁ (λ A _ → BA.∧-complementʳ (eval _ A))

∨-complementʳ : RightInverse tt ¬_ _∨_
∨-complementʳ = fromBoolEq₁ (λ A _ → BA.∨-complementʳ (eval _ A))

∧-cong : _∧_ Preserves₂ _≃_ ⟶ _≃_ ⟶ _≃_
∧-cong {A} {A′} {B} {B′} aa bb =
  begin
    (A  ∧ B)    ≃⟨ ∧-cong₁ aa ⟩
    (A′ ∧ B)    ≃⟨ ∧-comm _ _ ⟩
    (B  ∧ A′)   ≃⟨ ∧-cong₁ bb ⟩
    (B′ ∧ A′)   ≃⟨ ∧-comm _ _ ⟩
    (A′ ∧ B′)   ∎

∨-cong : _∨_ Preserves₂ _≃_ ⟶ _≃_ ⟶ _≃_
∨-cong {A}{A′}{B}{B′} aa bb =
  begin
    (A  ∨ B)    ≃⟨ ∨-cong₁ aa ⟩
    (A′ ∨ B)    ≃⟨ ∨-comm _ _ ⟩
    (B  ∨ A′)   ≃⟨ ∨-cong₁ bb ⟩
    (B′ ∨ A′)   ≃⟨ ∨-comm _ _ ⟩
    (A′ ∨ B′)   ∎
