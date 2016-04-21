module Logic.SemiringProperties where

open import Prelude hiding (_+_; _*_)

infixl 4 _|*|_
infixl 3 _|+|_
infixr 4 _⊛_

-- A tree which represents a frozen computation in a semiring. May be evaluated
-- with respect to a specific semiring with "⟦_⟧", defined below.

data Tree {a}(A : Set a) : Set a where
  _|+|_ : Tree A → Tree A → Tree A
  _|*|_ : Tree A → Tree A → Tree A
  atom : A → Tree A

-- A tree can be converted to a "sum of products" normal form. This preserves
-- meaning with respect to any semiring (see below for proof). Note that
-- multiplication is necessarily on the inside, because multiplication
-- distributes over addition, but not, in general, vice versa.

SNF : ∀ {a} → Set a → Set a
SNF A = List (List A)

private
  distribute : ∀ {a}{A : Set a} → List A → SNF A → SNF A
  distribute x ys = map (x ++_) ys

private
  -- convolution AKA distributing the left sum over the right
  _⊛_ : ∀ {a}{A : Set a} → SNF A → SNF A → SNF A
  _⊛_ xs ys = concat (map (flip distribute ys) xs)

tree→snf : ∀ {a}{A : Set a} → Tree A → SNF A
tree→snf (l |+| r) = tree→snf l ++ tree→snf r
tree→snf (l |*| r) = tree→snf l ⊛ tree→snf r
tree→snf (atom x) = singleton (singleton x)

-- this module contains proofs of properties of SNF, culminating in the fact
-- that conversion to SNF preserves semantic meaning

module SNF {a ℓ}(semiring : Semiring a ℓ) where
  open Semiring semiring
    renaming ( Carrier to A
             ; sym to ≈sym
             ; trans to ≈trans
             ; refl to ≈refl
             ; zero to 0-annihilate )

  instance equivalence = isEquivalence

  open EqReasoning setoid
  open import Logic.MonoidProperties as MP
    hiding (foldl; foldr; foldl₀; foldr₀; fold)
  open import Data.List.Properties using (map-++-commute)

  open MP +-monoid using () renaming (fold to +-fold; foldl to +-foldl)
  open MP *-monoid using () renaming (fold to *-fold; foldl to *-foldl)

  -- evaluate a tree in this semiring

  ⟦_⟧ : Tree A → A
  ⟦ l |+| r ⟧ = ⟦ l ⟧ + ⟦ r ⟧
  ⟦ l |*| r ⟧ = ⟦ l ⟧ * ⟦ r ⟧
  ⟦ atom x ⟧ = x

  -- evaluate a normal form in this semiring

  ⟦_⟧N : SNF A → A
  ⟦_⟧N = +-fold ∘ map *-fold

  private
    -- _++_ in SNF is homomorphic with _+_ in the semiring

    ++-correct : ∀ xs ys
                 → ⟦ xs ++ ys ⟧N
                 ≈ ⟦ xs ⟧N + ⟦ ys ⟧N
    ++-correct xs ys = begin
      +-fold (map *-fold (xs ++ ys))             ≡⟨ cong +-fold (map-++-commute *-fold xs ys) ⟩
      +-fold (map *-fold xs ++ map *-fold ys)    ≈⟨ foldl-++ +-monoid _ (map *-fold xs) _ ⟩
      ⟦ xs ⟧N + ⟦ ys ⟧N                          ∎

    swap-0 : ∀ z → z + 0# ≈ 0# + z
    swap-0 z = begin
           z + 0#    ≈⟨ snd +-identity _ ⟩
           z         ≈⟨ ≈sym (fst +-identity _) ⟩
      0# + z         ∎

    distribute-correct : ∀ x ys → ⟦ distribute x ys ⟧N ≈ *-fold x * ⟦ ys ⟧N
    distribute-correct x [] = ≈sym $ snd 0-annihilate _
    distribute-correct x (y ∷ ys) = begin
      +-foldl _ (map *-fold (distribute x ys))     ≈⟨ foldl-pull-z +-monoid _ (map *-fold (distribute x ys)) ⟩
      0# + *-fold (x ++ y) + ⟦ distribute x ys ⟧N  ≈⟨ +-cong (fst +-identity _) ≈refl ⟩
           *-fold (x ++ y) + ⟦ distribute x ys ⟧N  ≈⟨ +-cong (foldl-++ *-monoid _ x y) (distribute-correct x ys) ⟩
      *-fold x * *-fold y  + *-fold x * ⟦ ys ⟧N    ≈⟨ ≈sym (fst distrib (*-fold x) (*-fold y) (⟦ ys ⟧N)) ⟩
      *-fold x * (      *-fold y  + ⟦ ys ⟧N)       ≈⟨ *-cong ≈refl (+-cong (≈sym $ fst +-identity _) ≈refl) ⟩
      *-fold x * ((0# + *-fold y) + ⟦ ys ⟧N)       ≈⟨ *-cong ≈refl (≈sym $ foldl-pull-z +-monoid _ (map *-fold ys)) ⟩
      *-fold x * ⟦ y ∷ ys ⟧N                       ∎

    -- _⊛_ in SNF is homomorphic with _*_ in the semiring

    ⊛-correct : ∀ xs ys → ⟦ xs ⊛ ys ⟧N ≈ ⟦ xs ⟧N * ⟦ ys ⟧N
    ⊛-correct [] ys = ≈sym (fst 0-annihilate _)
    ⊛-correct (x ∷ xs) ys = begin
      ⟦ distribute x ys ++ (xs ⊛ ys) ⟧N       ≈⟨ ++-correct (distribute x ys) (xs ⊛ ys) ⟩
      ⟦ distribute x ys ⟧N  + ⟦ xs ⊛ ys ⟧N    ≈⟨ +-cong (distribute-correct x ys) (⊛-correct xs ys) ⟩
      *-fold x * ⟦ ys ⟧N + ⟦ xs ⟧N * ⟦ ys ⟧N  ≈⟨ ≈sym (snd distrib _ _ _) ⟩
      (*-fold x        + ⟦ xs ⟧N) * ⟦ ys ⟧N   ≈⟨ *-cong (+-cong (≈sym $ fst +-identity _) ≈refl) ≈refl ⟩
      ((0# + *-fold x) + ⟦ xs ⟧N) * ⟦ ys ⟧N   ≈⟨ *-cong (≈sym $ foldl-pull-z +-monoid _ (map *-fold xs)) ≈refl ⟩
      ⟦ x ∷ xs ⟧N                 * ⟦ ys ⟧N   ∎

  -- converting a tree to SNF preserves its result when evaluated in the semiring

  tree→snf-correct : ∀ t → ⟦ t ⟧ ≈ ⟦ tree→snf t ⟧N
  tree→snf-correct (l |+| r) =
    let l-correct = tree→snf-correct l
        r-correct = tree→snf-correct r
    in begin
       ⟦          l ⟧  + ⟦          r ⟧     ≈⟨ +-cong l-correct r-correct ⟩
       ⟦ tree→snf l ⟧N + ⟦ tree→snf r ⟧N    ≈⟨ ≈sym (++-correct (tree→snf l) (tree→snf r)) ⟩
       ⟦ tree→snf l   ++   tree→snf r ⟧N    ∎
  tree→snf-correct (l |*| r) =
    let l-correct = tree→snf-correct l
        r-correct = tree→snf-correct r
    in begin
       ⟦          l ⟧  * ⟦          r ⟧     ≈⟨ *-cong l-correct r-correct ⟩
       ⟦ tree→snf l ⟧N * ⟦ tree→snf r ⟧N    ≈⟨ ≈sym (⊛-correct (tree→snf l) (tree→snf r)) ⟩
       ⟦ tree→snf l    ⊛   tree→snf r ⟧N    ∎
  tree→snf-correct (atom x) = begin
              x    ≈⟨ ≈sym (fst *-identity _) ⟩
         1# * x    ≈⟨ ≈sym (fst +-identity _) ⟩
    0# + 1# * x    ∎
