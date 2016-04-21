
-- We can define a 'sequent calculus' for propositional logic, which can be used
-- to aid reasoning about entailment. This module is parametrised over some
-- choice of 'Foldable' container that satisfies a couple of laws as defined in
-- 'Data.Foldable'. A good choice is a list.

open import Prelude hiding (_,_) renaming (¬_ to ~_)
open import Data.Foldable

module Logic.Sequent {n : ℕ}(foldable : Foldable lzero lzero lzero) where

open import Logic.Core
open import Logic.Properties
open import Data.Container hiding (_⇒_)

open Foldable foldable

Env = T (Prop n)
infixr 1 _,_

_,_ = _►_
∅ = empty

infix 0 _==>_

-- TODO: find a nice way to allow arbitrary swapping of terms on either side of
-- the sequent; swapping the front two, as is currently possible, is not always
-- sufficient.

data _==>_ : Env → Env → Set where
  axiom : ∀ {Γ Δ A}
          → A , Γ ==> A , Δ

  ∧l : ∀ {Γ Δ A B}
       → A , B , Γ ==> Δ
       --------------------
       → (A ∧ B) , Γ ==> Δ

  ∧r : ∀ {Γ Δ A B}
       → Γ ==> A , Δ
       → Γ ==> B , Δ
       --------------------
       → Γ ==> (A ∧ B) , Δ

  ∨l : ∀ {Γ Δ A B}
       → A , Γ ==> Δ
       → B , Γ ==> Δ
       --------------------
       → A ∨ B , Γ ==> Δ

  ∨r : ∀ {Γ Δ A B}
       → Γ ==> A , B , Δ
       --------------------
       → Γ ==> (A ∨ B) , Δ

  ¬l : ∀ {Γ Δ A}
       → Γ ==> A , Δ
       -----------------
       → (¬ A) , Γ ==> Δ

  ¬r : ∀ {Γ Δ A}
       → A , Γ ==> Δ
       -----------------
       → Γ ==> (¬ A) , Δ

  swapl : ∀ {Γ Δ A B}
          → A , B , Γ ==> Δ
          -----------------
          → B , A , Γ ==> Δ

  swapr : ∀ {Γ Δ A B}
          → Γ ==> A , B , Δ
          -----------------
          → Γ ==> B , A , Δ

⇒r : ∀ {Γ Δ A B}
     → A , Γ ==> B , Δ
     -------------------
     → Γ ==> (A ⇒ B) , Δ
⇒r = ∨r ∘ ¬r

⇒l : ∀ {Γ Δ A B}
     → Γ ==> A , Δ
     → B , Γ ==> Δ
     -------------------
     → (A ⇒ B) , Γ ==> Δ
⇒l x y = ∨l (¬l x) y

open import Algebra using (BooleanAlgebra)
open import Algebra.Properties.BooleanAlgebra (booleanAlgebra n)
open BooleanAlgebra (booleanAlgebra n) using (∧-assoc; ∨-assoc)
open CommutativeSemiring (∨-∧-commutativeSemiring) using ()
  renaming ( +-identity to ∨-identity
           ; *-identity to ∧-identity)

private
  ∨-monoid = CommutativeSemiring.+-monoid ∨-∧-commutativeSemiring
  ∧-monoid = CommutativeSemiring.*-monoid ∨-∧-commutativeSemiring

  -- big AND = and together everything in the foldable container
  ⋀ = foldMap ∧-monoid id
  -- big OR = or together everything in the foldable container
  ⋁ = foldMap ∨-monoid id

module ⊨ where
  open import Logic.Properties.Entailment {n} public
  open import Logic.Properties.Entailment.Extra {n} public

open import Logic.Properties.Equivalence using (_≃_; ≃left; ≃right)
open ⊨.⊨-Reasoning

-- Our sequent calculus for propositional logic is sound. In other words,
-- given a sequent proof 'Γ ==> Δ', we can prove that the big AND of the left
-- entails the big OR of the right.

==>-sound : ∀ Γ Δ → Γ ==> Δ → ⋀ Γ ⊨ ⋁ Δ

==>-sound _ _ (axiom {Γ}{Δ}{A}) = begin
  ⋀ (A , Γ)      ⊨⟨ ≃left $ ►-∙ ∧-monoid _ _ _ ⟩
  (A ∧ ⋀ Γ)      ⊨⟨ ⊨.∧-elim₁ _ _ ⟩
  A              ⊨⟨ ⊨.∨-intro₁ _ _ ⟩
  (A ∨ ⋁ Δ)      ⊨⟨ ≃right $ ►-∙ ∨-monoid _ _ _ ⟩
  ⋁ (A , Δ)      ∎

==>-sound _ Δ (∧l {Γ}{_}{A}{B} seq) = begin
  ⋀ ((A ∧ B) , Γ)    ⊨⟨ ≃left $ ►-∙ ∧-monoid _ _ _ ⟩
  (A ∧ B) ∧ ⋀ Γ      ⊨⟨ ≃right $ ►-∙₂ ∧-monoid _ _ _ _ ⟩
  ⋀ (A , B , Γ)      ⊨⟨ ==>-sound _ _ seq ⟩
  ⋁ Δ                ∎

==>-sound Γ _ (∧r {_}{Δ}{A}{B} lseq rseq) = begin
  ⋀ Γ                    ⊨⟨ ≃right $ ∧-idempotent _ ⟩
  ⋀ Γ ∧ ⋀ Γ              ⊨⟨ ⊨.∧-cong (==>-sound _ _ lseq) (==>-sound _ _ rseq) ⟩
  ⋁ (A , Δ) ∧ ⋁ (B , Δ)  ⊨⟨ ⊨.∧-cong (≃left $ ►-∙ ∨-monoid _ _ _) (≃left $ ►-∙ ∨-monoid _ _ _) ⟩
  (A ∨ ⋁ Δ) ∧ (B ∨ ⋁ Δ)  ⊨⟨ ≃right $ snd ∨-∧-distrib _ _ _ ⟩
  ((A ∧ B) ∨ ⋁ Δ)        ⊨⟨ ≃right $ ►-∙ ∨-monoid _ _ _ ⟩
  ⋁ ((A ∧ B) , Δ)        ∎

==>-sound _ Δ (∨l {Γ}{_}{A}{B} lseq rseq) = begin
  ⋀ ((A ∨ B) , Γ)           ⊨⟨ ≃left $ ►-∙ ∧-monoid _ _ _ ⟩
  (A ∨ B) ∧ ⋀ Γ             ⊨⟨ ≃left $ snd ∧-∨-distrib _ _ _ ⟩
  ((A ∧ ⋀ Γ) ∨ (B ∧ ⋀ Γ))  ⊨⟨ ⊨.∨-cong (≃right $ ►-∙ ∧-monoid _ _ _) (≃right $ ►-∙ ∧-monoid _ _ _) ⟩
  (⋀ (A , Γ) ∨ ⋀ (B , Γ))  ⊨⟨ ⊨.∨-cong (==>-sound _ _ lseq) (==>-sound _ _ rseq) ⟩
  (⋁ Δ ∨ ⋁ Δ)              ⊨⟨ ≃left $ ∨-idempotent _ ⟩
  ⋁ Δ                       ∎

==>-sound Γ _ (∨r {_}{Δ}{A}{B} seq) = begin
  ⋀ Γ                ⊨⟨ ==>-sound _ _ seq ⟩
  ⋁ (A , B , Δ)      ⊨⟨ ≃left $ ►-∙₂ ∨-monoid _ _ _ _ ⟩
  ((A ∨ B) ∨ ⋁ Δ)    ⊨⟨ ≃right $ ►-∙ ∨-monoid _ _ _ ⟩
  ⋁ ((A ∨ B) , Δ)    ∎

==>-sound _ Δ (¬l {Γ}{_}{A} sequent) = begin
  ⋀ ((¬ A) , Γ)               ⊨⟨ ≃left $ ►-∙ ∧-monoid _ _ _ ⟩
  ¬ A ∧ ⋀ Γ                   ⊨⟨ ⊨.∧-cong ⊨.refl (==>-sound _ _ sequent) ⟩
  ¬ A ∧ ⋁ (A , Δ)             ⊨⟨ ⊨.∧-cong ⊨.refl (≃left $ ►-∙ ∨-monoid _ _ _) ⟩
  ¬ A ∧ (A ∨ ⋁ Δ)             ⊨⟨ ≃left $ fst ∧-∨-distrib _ _ _ ⟩
  ((¬ A ∧ A) ∨ (¬ A ∧ ⋁ Δ))   ⊨⟨ ⊨.∨-cong (≃left $ fst ∧-complement _) ⊨.refl ⟩
  (ff ∨ (¬ A ∧ ⋁ Δ))          ⊨⟨ ≃left $ fst ∨-identity _ ⟩
  ¬ A ∧ ⋁ Δ                   ⊨⟨ ⊨.∧-elim₂ _ _ ⟩
  ⋁ Δ                         ∎

==>-sound Γ _ (¬r {_}{Δ}{A} seq) = begin
  ⋀ Γ                         ⊨⟨ ⊨.∨-intro₂ _ _ ⟩
  (¬ A ∨ ⋀ Γ)                 ⊨⟨ ≃right $ fst ∧-identity _ ⟩
  tt ∧ (¬ A ∨ ⋀ Γ)            ⊨⟨ ⊨.∧-cong (≃right $ fst ∨-complement _) ⊨.refl ⟩
  (¬ A ∨ A) ∧ (¬ A ∨ ⋀ Γ)     ⊨⟨ ≃right $ fst ∨-∧-distrib _ _ _ ⟩
  (¬ A ∨ (A ∧ ⋀ Γ))           ⊨⟨ ⊨.∨-cong ⊨.refl (≃right $ ►-∙ ∧-monoid _ _ _) ⟩
  (¬ A ∨ ⋀ (A , Γ))           ⊨⟨ ⊨.∨-cong ⊨.refl (==>-sound _ _ seq) ⟩
  (¬ A ∨ ⋁ Δ)                 ⊨⟨ ≃right $ ►-∙ ∨-monoid _ _ _ ⟩
  ⋁ ((¬ A) , Δ)               ∎

==>-sound _ _ (swapl {Γ}{Δ}{A}{B} seq) = begin
  ⋀ (B , A , Γ)              ⊨⟨ ≃left $ ►-∙₂ ∧-monoid _ _ _ _ ⟩
  (B ∧ A) ∧ ⋀ Γ              ⊨⟨ ⊨.∧-cong (⊨.∧-comm _ _) ⊨.refl ⟩
  (A ∧ B) ∧ ⋀ Γ              ⊨⟨ ≃right $ ►-∙₂ ∧-monoid _ _ _ _ ⟩
  ⋀ (A , B , Γ)              ⊨⟨ ==>-sound _ _ seq ⟩
  ⋁ Δ                        ∎

==>-sound _ _ (swapr {Γ}{Δ}{A}{B} seq) = begin
  ⋀ Γ                       ⊨⟨ ==>-sound _ _ seq ⟩
  ⋁ (A , B , Δ)             ⊨⟨ ≃left $ ►-∙₂ ∨-monoid _ _ _ _ ⟩
  ((A ∨ B) ∨ ⋁ Δ)           ⊨⟨ ⊨.∨-cong (⊨.∨-comm _ _) ⊨.refl ⟩
  ((B ∨ A) ∨ ⋁ Δ)           ⊨⟨ ≃right $ ►-∙₂ ∨-monoid _ _ _ _ ⟩
  ⋁ (B , A , Δ)             ∎

module Reasoning where

  data TransChain : Env → Env → Env → Env → Set where
    simpl : ∀ {Γ Δ} → TransChain Γ Δ Γ Δ
    cons : ∀ {Γ Γ′ Γ′′ Δ Δ′ Δ′′} → (Γ ==> Δ → Γ′ ==> Δ′) → TransChain Γ′ Δ′ Γ′′ Δ′′ → TransChain Γ Δ Γ′′ Δ′′

  chain : ∀ {Γ Γ′ Δ Δ′} → TransChain Γ Δ Γ′ Δ′ → (Γ ==> Δ → Γ′ ==> Δ′)
  chain simpl = id
  chain (cons f c) = chain c ∘ f

  infix -2 begin>_

  begin>_ : ∀ {Γ Γ′ Δ Δ′ A} → TransChain (A , Γ) (A , Δ) Γ′ Δ′ → Γ′ ==> Δ′
  begin> chn = chain chn axiom

  infixr -1 _=>_⟨_⟩_

  _=>_⟨_⟩_ : ∀ Γ Δ {Γ′ Γ′′ Δ′ Δ′′} → (Γ ==> Δ → Γ′ ==> Δ′) → TransChain Γ′ Δ′ Γ′′ Δ′′ → TransChain Γ Δ Γ′′ Δ′′
  (_ => _ ⟨ f ⟩ c) = cons f c

  infix 0 _=>_∎>

  _=>_∎> : ∀ Γ Δ → TransChain Γ Δ Γ Δ
  _ => _ ∎> = simpl

  example : ∀ {P Q} → ∅ ==> (((P ⇒ Q) ⇒ P) ⇒ P) , ∅
  example {P}{Q} =
    begin>
      P , ∅             => P , ∅                    ⟨ ⇒l lhs ⟩
      ---------------------------------------------------------
      ((P ⇒ Q) ⇒ P) , ∅ => P , ∅                    ⟨ ⇒r ⟩
      ---------------------------------------------------------
      ∅                 => (((P ⇒ Q) ⇒ P) ⇒ P) , ∅  ∎>
    where
      lhs =
        begin>
          P , ∅ => P , Q , ∅         ⟨ swapr ⟩
          -------------------------------------
          P , ∅ => Q , P , ∅         ⟨ ⇒r ⟩
          -------------------------------------
          ∅     => (P ⇒ Q) , P , ∅   ∎>