{-

This module contains proofs of properties of monoids pertaining to list folds.

-}

open import Prelude hiding (foldl; foldr)

module Logic.MonoidProperties {a ℓ}(monoid : Monoid a ℓ) where

open Monoid monoid
  renaming ( Carrier to A
           ; refl to ≈refl
           ; sym to ≈sym)

instance equivalence = isEquivalence
open EqReasoning setoid

import Data.List as List

foldl = List.foldl _∙_
foldr = List.foldr _∙_

foldl₀ = foldl ε
foldr₀ = foldr ε

-- if you're left folding starting from some "z", you can pull it out to the
-- left and start from "ε" instead

foldl-pull-z : ∀ z xs → foldl z xs ≈ z ∙ foldl₀ xs
foldl-pull-z z [] = sym (snd identity _)
foldl-pull-z z (x ∷ xs) = begin
  foldl (z ∙ x) xs           ≈⟨ foldl-pull-z _ xs ⟩
  z ∙ x ∙ foldl ε xs         ≈⟨ assoc _ _ _ ⟩
  z ∙ (x ∙ foldl ε xs)       ≈⟨ ∙-cong ≈refl (∙-cong (sym $ fst identity _) ≈refl) ⟩
  z ∙ (ε ∙ x ∙ foldl ε xs)   ≈⟨ ∙-cong ≈refl (sym $ foldl-pull-z _ xs) ⟩
  z ∙ foldl (ε ∙ x) xs       ∎

-- if you're right folding starting from some "z", you can pull it out to the
-- right and start from "ε" instead

foldr-pull-z : ∀ z xs → foldr z xs ≈ foldr₀ xs ∙ z
foldr-pull-z z [] = sym (fst identity _)
foldr-pull-z z (x ∷ xs) = begin
  x ∙ foldr z xs       ≈⟨ ∙-cong refl (foldr-pull-z _ xs) ⟩
  x ∙ (foldr₀ xs ∙ z)  ≈⟨ sym (assoc _ _ _) ⟩
  x ∙ foldr₀ xs ∙ z    ∎

-- folding left preserves equivalence of the starting element

foldl-z-cong : ∀ a b xs → a ≈ b → foldl a xs ≈ foldl b xs
foldl-z-cong a b xs eq = begin
  foldl a xs      ≈⟨ foldl-pull-z _ xs ⟩
  a ∙ foldl ε xs  ≈⟨ ∙-cong eq ≈refl ⟩
  b ∙ foldl ε xs  ≈⟨ sym $ foldl-pull-z _ xs ⟩
  foldl b xs      ∎

-- _++_/_∙_ is homomorphic under foldl

foldl-++ : ∀ z xs ys → foldl z (xs ++ ys) ≈ foldl z xs ∙ foldl ε ys
foldl-++ z [] ys = begin
  foldl z ys       ≈⟨ foldl-pull-z _ ys ⟩
  z ∙ foldl ε ys   ∎
foldl-++ z (x ∷ xs) = foldl-++ (z ∙ x) xs

-- it doesn't matter which order you fold when your operation is associative

foldl₀≈foldr₀ : ∀ xs → foldl₀ xs ≈ foldr₀ xs
foldl₀≈foldr₀ [] = refl
foldl₀≈foldr₀ (x ∷ xs) = begin
  foldl (ε ∙ x) xs    ≈⟨ foldl-pull-z _ xs ⟩
  ε ∙ x ∙ foldl₀ xs   ≈⟨ ∙-cong (fst identity _) (foldl₀≈foldr₀ xs) ⟩
  x     ∙ foldr₀ xs   ∎

-- now that we've established that they're the same, we can call "foldl₀" =
-- "foldr₀" = "fold"

fold = foldl₀
