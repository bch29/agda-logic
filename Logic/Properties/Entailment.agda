open import Prelude hiding (refl; trans; sym) renaming (¬_ to ~_)

module Logic.Properties.Entailment {n : ℕ} where

open import Logic.Core

open import Relation.Binary hiding (_⇒_)

open import Data.Bool.Properties using (booleanAlgebra)
open import Algebra.Properties.BooleanAlgebra booleanAlgebra

--------------------------------------------------------------------------------
--  The definition of entailment
--------------------------------------------------------------------------------

infix 4 ⊨_
infix 1 _⊨_

-- this type is inhabited if the proposition 'A' is true in the provided
-- environment

[_]⊨_ : Vec Bool n → Prop n → Set
[ env ]⊨ A = IsTrue (eval env A)

-- this type is inhabited if the truth of 'A' in the provided environment
-- implies the truth of 'B'

_[_]⊨_ : Prop n → Vec Bool n → Prop n → Set
A [ env ]⊨ B = [ env ]⊨ A → [ env ]⊨ B

-- 'A' is valid if it is true in all possible environments

⊨_ : Prop n → Set
⊨ A = ∀ env → [ env ]⊨ A

-- 'A' entails 'B' if, in all possible environments, the truth of 'A' implies
-- the truth of 'B'

data _⊨_ (A B : Prop n) : Set where
  entails : (∀ env → A [ env ]⊨ B) → A ⊨ B

run-⊨ : ∀ {A B} → A ⊨ B → (∀ env → A [ env ]⊨ B)
run-⊨ (entails f) = f

open import Algebra.FunctionProperties {A = Prop n} _≡_

--------------------------------------------------------------------------------
--  ⊨ is a preorder
--------------------------------------------------------------------------------

refl : Reflexive _⊨_
refl = entails (λ _ → id)

trans : Transitive _⊨_
trans (entails pq) (entails qr) = entails (λ env → qr env ∘ pq env)

isPreorder : IsPreorder _≡_ _⊨_
IsPreorder.isEquivalence isPreorder       = it
IsPreorder.reflexive     isPreorder ≡refl = refl
IsPreorder.trans         isPreorder       = trans

preorder : Preorder _ _ _
Preorder.Carrier    preorder = Prop n
Preorder._≈_        preorder = _≡_
Preorder._∼_        preorder = _⊨_
Preorder.isPreorder preorder = isPreorder

module ⊨-Reasoning = PreorderReasoning preorder
  renaming ( _∼⟨_⟩_ to _⊨⟨_⟩_
           ; _≈⟨_⟩_ to _≡⟨_⟩_
           ; _≈⟨⟩_  to _≡⟨⟩_)

--------------------------------------------------------------------------------
--  Entailment, implication and function arrows are all similar
--------------------------------------------------------------------------------

private
  ≡true→IsTrue : ∀ b → b ≡ true → IsTrue b
  ≡true→IsTrue .true ≡refl = tt

⇒→⊨ : ∀ {A B} → ⊨ (A ⇒ B) → A ⊨ B
⇒→⊨ {A}{B} A⇒B = entails go
  where go : ∀ env → A [ env ]⊨ B
        go env x with eval env A | A⇒B env
        go env () | false | impl
        go env x | true | impl = impl

⊨→⇒ : ∀ {A B} → A ⊨ B → ⊨ (A ⇒ B)
⊨→⇒ {A}{B} (entails ab) env with eval env A | inspect (eval env) A
⊨→⇒ (entails ab) env | false | _ = _
⊨→⇒ (entails ab) env | true | revealed eq = ab env (≡true→IsTrue _ eq)

→⊨ : ∀ {A B} → A ⊨ B → (⊨ A → ⊨ B)
→⊨ {A}{B} (entails ab) a env = ab env (a env)

private
  infixr 5 _=>_
           
  _=>_ : Bool → Bool → Bool
  x => y = not x || y

--------------------------------------------------------------------------------
--  Translating boolean properties into propositional ones
--------------------------------------------------------------------------------

fromBoolEq₁ : (f g : Prop n → Prop n) →
              (∀ A env → eval env (f A) ≡ eval env (g A)) →
              (∀ {A} → f A ⊨ g A)
fromBoolEq₁ f g beq {A} = entails go
  where go : ∀ env → f A [ env ]⊨ g A
        go env x rewrite beq A env = x

fromBoolEq₂ : (f g : Prop n → Prop n → Prop n) →
              (∀ A B env → eval env (f A B) ≡ eval env (g A B)) →
              (∀ {A B} → f A B ⊨ g A B)
fromBoolEq₂ f g beq {A}{B} = entails go
  where go : ∀ env → f A B [ env ]⊨ g A B
        go env x rewrite beq A B env = x

fromBoolEq₃ : (f g : (A B C : Prop n) → Prop n) →
              (∀ A B C env → eval env (f A B C) ≡ eval env (g A B C)) →
              (∀ A B C → f A B C ⊨ g A B C)
fromBoolEq₃ f g beq A B C = entails go
  where go : ∀ env → f A B C [ env ]⊨ g A B C
        go env x rewrite beq A B C env = x

fromBoolImpl₂ : (f g : (A B : Prop n) → Prop n) →
                (∀ A B env → IsTrue (eval env (f A B) =>
                                    eval env (g A B))) →
                (∀ A B → f A B ⊨ g A B)
fromBoolImpl₂ f g bi A B = ⇒→⊨ (bi A B)

fromBoolImpl₃ : (f g : (A B C : Prop n) → Prop n) →
                (∀ A B C env → IsTrue (eval env (f A B C) =>
                                      eval env (g A B C))) →
                (∀ A B C → f A B C ⊨ g A B C)
fromBoolImpl₃ f g bi A B C = ⇒→⊨ (bi A B C)

--------------------------------------------------------------------------------
--  We will need these properties of booleans
--------------------------------------------------------------------------------

private
  contraB : ∀ x y → x => y ≡ not y => not x
  contraB false false = ≡refl
  contraB false true = ≡refl
  contraB true false = ≡refl
  contraB true true = ≡refl

  &&congB : ∀ x x′ y → IsTrue $ (x => x′) => ((x && y) => (x′ && y))
  &&congB false false false = tt
  &&congB false false true = tt
  &&congB false true false = tt
  &&congB false true true = tt
  &&congB true false false = tt
  &&congB true false true = tt
  &&congB true true false = tt
  &&congB true true true = tt

  ||congB : ∀ x x′ y → IsTrue $ (x => x′) => ((x || y) => (x′ || y))
  ||congB false false false = tt
  ||congB false false true = tt
  ||congB false true false = tt
  ||congB false true true = tt
  ||congB true false false = tt
  ||congB true false true = tt
  ||congB true true false = tt
  ||congB true true true = tt

--------------------------------------------------------------------------------
--  Some miscellaneous properties of ⊨
--------------------------------------------------------------------------------

lift⊨ : ∀ {A B C D} → (A ⇒ B) ⊨ (C ⇒ D) → A ⊨ B → C ⊨ D
lift⊨ x = ⇒→⊨ ∘ →⊨ x ∘ ⊨→⇒

contra : ∀ {A B} → A ⊨ B → (¬ B) ⊨ (¬ A)
contra = lift⊨ $
  fromBoolEq₂ (λ A B → A ⇒ B) (λ A B → ¬ B ⇒ ¬ A)
              (λ A _ _ → contraB (eval _ A) _)

∧-cong₁ : ∀ {A A′ B} → A ⊨ A′ → (A ∧ B) ⊨ (A′ ∧ B)
∧-cong₁ = lift⊨ $
  fromBoolImpl₃ (λ A A′ _ → A ⇒ A′) (λ A A′ B → A ∧ B ⇒ A′ ∧ B)
                (λ A _ _ _ → &&congB (eval _ A) _ _) _ _ _

∨-cong₁ : ∀ {A A′ B} → A ⊨ A′ → (A ∨ B) ⊨ (A′ ∨ B)
∨-cong₁ = lift⊨ $
  fromBoolImpl₃ (λ A A′ _ → A ⇒ A′) (λ A A′ B → A ∨ B ⇒ A′ ∨ B)
                (λ A _ _ _ → ||congB (eval _ A) _ _) _ _ _
