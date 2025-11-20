module InsertionSort where

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; _≤_; _≤ᵇ_; z≤n; s≤s)
open import Data.Bool using (Bool; true; false)

-- Insertion sort definition
insert : ℕ → List ℕ → List ℕ
insert x [] = x ∷ []
insert x (y ∷ ys) with x ≤ᵇ y
... | true  = x ∷ y ∷ ys
... | false = y ∷ (insert x ys)

insertionSort : List ℕ → List ℕ
insertionSort []       = []
insertionSort (x ∷ xs) = insert x (insertionSort xs)

-- Sorted List definition as a type
-- Via the propositions-as-types correspondence
data Sorted : List ℕ → Set where
  sorted-[]     : Sorted []
  sorted-single : (x : ℕ) → Sorted (x ∷ [])
  sorted-cons   : (x y : ℕ) (ys : List ℕ) → x ≤ y → Sorted (y ∷ ys) → Sorted (x ∷ y ∷ ys)

proof-empty : Sorted []
proof-empty = sorted-[]

proof-single : Sorted (3 ∷ [])
proof-single = sorted-single 3

proof-2-7 : Sorted (2 ∷ 7 ∷ [])
proof-2-7 = sorted-cons 2 7 []
                        (s≤s (s≤s z≤n))   -- Proof that 2 ≤ 7
                        (sorted-single 7) -- Proof that [7 ∷ []] is sorted

1≤3 : 1 ≤ 3
1≤3 = s≤s z≤n

3≤8 : 3 ≤ 8
3≤8 = s≤s (s≤s (s≤s z≤n))

proof-1-3-8 : Sorted (1 ∷ 3 ∷ 8 ∷ [])
proof-1-3-8 =
  sorted-cons 1 3 (8 ∷ [])
    1≤3                      -- Proof that 1 ≤ 3
    (sorted-cons 3 8 []      -- Proof that [3 ∷ 8 ∷ []] is sorted
      3≤8                    -- Proof that 3 ≤ 8
      (sorted-single 8))     -- Proof thath [8 ∷ []] is sorted

-- Lemma: Executing `insert` of x over a sorted list maintains sorting
insert-sorted : (x : ℕ) (xs : List ℕ) → Sorted xs → Sorted (insert x xs)
insert-sorted x [] sorted-[] = sorted-single x
--insert-sorted x  

insertionSort-sorted : (xs : List ℕ) → Sorted (insertionSort xs)
insertionSort-sorted []        = sorted-[]
insertionSort-sorted (x ∷ xs₁) =
  insert-sorted x (insertionSort xs₁) (insertionSort-sorted xs₁)  


-- Definition of Permutation
-- Based on stdlib implementation
-- https://agda.github.io/agda-stdlib/master/Data.List.Relation.Binary.Permutation.Declarative.html#1644
data _~_ : List ℕ → List ℕ → Set where
  perm-refl  : {xs : List ℕ} → xs ~ xs                                  -- Every list is a permutation of itself
  perm-swap  : {x y : ℕ} {xs : List ℕ} → (x ∷ y ∷ xs) ~ (y ∷ x ∷ xs)    -- Swapping two elements is a permutation
  perm-skip  : {x : ℕ} {xs ys : List ℕ} → xs ~ ys → (x ∷ xs) ~ (x ∷ ys) -- Adding an element to two permutated lists maintains the permutation
  perm-trans : {xs ys zs : List ℕ} → xs ~ ys → ys ~ zs → xs ~ zs        -- Transitivity of permutation

-- Examples
ex1 : (1 ∷ 2 ∷ 3 ∷ []) ~ (1 ∷ 2 ∷ 3 ∷ [])
ex1 = perm-refl

ex2 : (1 ∷ 2 ∷ []) ~ (2 ∷ 1 ∷ [])
ex2 = perm-swap

ex3 : (1 ∷ 2 ∷ 3 ∷ []) ~ (1 ∷ 3 ∷ 2 ∷ [])
ex3 = perm-skip perm-swap

ex4 : (1 ∷ 2 ∷ 3 ∷ []) ~ (3 ∷ 2 ∷ 1 ∷ [])
ex4 =
  perm-trans
    (perm-skip perm-swap)     -- [1 ∷ 2 ∷ 3] ~ [1 ∷ 3 ∷ 2]
    (perm-trans
      perm-swap               -- [1 ∷ 3 ∷ 2] ~ [3 ∷ 1 ∷ 2]
      (perm-skip perm-swap))  -- [3 ∷ 1 ∷ 2] ~ [3 ∷ 2 ∷ 1]
    

-- Lemma: Executing `insert` of an element x in xs is a permutation of x∷xs
insert-perm : (x : ℕ) (xs : List ℕ) → (x ∷ xs) ~ (insert x xs)
insert-perm x [] = perm-refl
insert-perm x (y ∷ ys) with x ≤ᵇ y
... | true = perm-refl              -- insert x (y ∷ ys) = x ∷ y ∷ ys
... | false =
  perm-trans
    perm-swap                       -- [x ∷ y ∷ ...] ~ [y ∷ x ∷ ...]
    (perm-skip (insert-perm x ys))  -- [y ∷ x ∷ ...] ~ [y ∷ (insert x ys)]


-- Main proof: Applying insertion sort produces a permutation
insertion-sort-perm : (xs : List ℕ) → xs ~ (insertionSort xs)
insertion-sort-perm []       = perm-refl
insertion-sort-perm (x ∷ xs₁) =
  perm-trans
    (perm-skip (insertion-sort-perm xs₁)) -- [x ∷ xs₁] ~ [x ∷ (insertionSort xs₁)] (H.I.) por perm-swap 
    (insert-perm x (insertionSort xs₁))   -- [x ∷ (insertionSort xs₁)] ~ (insert x (insertionSort xs₁))

