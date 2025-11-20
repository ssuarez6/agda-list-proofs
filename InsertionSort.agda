module InsertionSort where

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; _≤_; _≤ᵇ_; z≤n; s≤s; suc; zero)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt) public
open import Data.Nat.Properties using (≤-trans) public
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- Insertion sort definition
insert : ℕ → List ℕ → List ℕ
insert x [] = x ∷ []
insert x (y ∷ ys) with x ≤ᵇ y
... | true  = x ∷ y ∷ ys
... | false = y ∷ (insert x ys)

insertionSort : List ℕ → List ℕ
insertionSort []       = []
insertionSort (x ∷ xs) = insert x (insertionSort xs)


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

-- Product type
record _×_ (A B : Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B

open _×_

-- Less than all relation
_≤*_ : (x : ℕ) → (list : List ℕ) → Set
x ≤* [] = ⊤
x ≤* (y ∷ l) = (x ≤ y) × (x ≤* l)

-- Sorted as structural recursive function
sorted : (l : List ℕ) → Set
sorted [] = ⊤
sorted (x ∷ l) = (x ≤* l) × sorted l

-- Lemma: If x ≤ y and y ≤* zs then x ≤* zs
≤*-trans : ∀ {x y zs} → x ≤ y → y ≤* zs → x ≤* zs
≤*-trans {zs = []}     x≤y _             = tt
≤*-trans {zs = z ∷ zs} x≤y (y≤z , y≤*zs) = (≤-trans x≤y y≤z) , (≤*-trans x≤y y≤*zs)

-- Lemma: If z ≤ x and z ≤* ys then z ≤* (insert x ys)
≤*-insert : ∀ {x z ys} → z ≤ x → z ≤* ys → z ≤* (insert x ys)
≤*-insert {x} {z} {[]} z≤x _ = z≤x , tt
≤*-insert {x} {z} {y ∷ ys} z≤x (z≤y , z≤*ys) with x ≤ᵇ y
... | true  = z≤x , (z≤y , z≤*ys)               -- x is the new head
... | false = z≤y , (≤*-insert z≤x z≤*ys) -- y is still the head, recurse


-- Relation between decidable ≤ᵇ and type ≤
≤ᵇ-true→≤ : ∀ {x y} → (x ≤ᵇ y) ≡ true → x ≤ y
≤ᵇ-true→≤ {zero}  {y}     eq = z≤n
≤ᵇ-true→≤ {suc x} {zero}  () -- Impossible case: true ≡ false
≤ᵇ-true→≤ {suc x} {suc y} eq = s≤s (≤ᵇ-true→≤ eq)

≤ᵇ-false→≤ : ∀ {x y} → (x ≤ᵇ y) ≡ false → y ≤ x
≤ᵇ-false→≤ {zero}  {y}     () -- Impossible case: true ≡ false
≤ᵇ-false→≤ {suc x} {zero}  eq = z≤n
≤ᵇ-false→≤ {suc x} {suc y} eq = s≤s (≤ᵇ-false→≤ eq)

-- Lemma: Inserting an `x` over a sorted list maintains sorting
insert-sorted : (x : ℕ) (xs : List ℕ) → sorted xs → sorted (insert x xs)
insert-sorted x [] _ = tt , tt    -- base case: sorted [x] is (x≤*[] , sorted [])

insert-sorted x (y ∷ ys) (y≤*ys , s-ys) with x ≤ᵇ y
... | true =
  -- when x ≤ y the result is x ∷ y ∷ ys
  -- goal: x ≤* (y ∷ ys) × sorted (y ∷ ys)
  let
    x≤y = ≤ᵇ-true→≤ refl
    x≤*ys = ≤*-trans x≤y y≤*ys
  in
    (x≤y , x≤*ys) , (y≤*ys , s-ys)

... | false =
  -- when x > y the result is y ∷ insert x xs
  -- goal: y ≤* (insert x ys) × sorted (insert x ys)
  let
    y≤x = ≤ᵇ-false→≤ refl
    tail-srt = insert-sorted x ys s-ys
    head-≤* = ≤*-insert y≤x y≤*ys
  in
    head-≤* , tail-srt


insertionSort-sorted : (xs : List ℕ) → sorted (insertionSort xs)
insertionSort-sorted [] = tt
insertionSort-sorted (x ∷ xs₁) =
  insert-sorted x (insertionSort xs₁) (insertionSort-sorted xs₁)
