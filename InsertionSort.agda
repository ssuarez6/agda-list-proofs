module InsertionSort where

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; _≤_; _≤ᵇ_; z≤n; s≤s)
open import Data.Bool using (Bool; true; false)

insert : ℕ → List ℕ → List ℕ
insert x [] = x ∷ []
insert x (y ∷ ys) with x ≤ᵇ y
... | true  = x ∷ y ∷ ys
... | false = y ∷ (insert x ys)

insertionSort : List ℕ → List ℕ
insertionSort []       = []
insertionSort (x ∷ xs) = insert x (insertionSort xs)

-- Definición de Lista Ordernada
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
                        (s≤s (s≤s z≤n))   -- Prueba de que 2≤7
                        (sorted-single 7) -- Prueba de que (7 ∷ []) está ordenada

1≤3 : 1 ≤ 3
1≤3 = s≤s z≤n

3≤8 : 3 ≤ 8
3≤8 = s≤s (s≤s (s≤s z≤n))

proof-1-3-8 : Sorted (1 ∷ 3 ∷ 8 ∷ [])
proof-1-3-8 =
  sorted-cons 1 3 (8 ∷ [])
    1≤3                      -- Prueba de que 1≤3
    (sorted-cons 3 8 []      -- Prueba de que [3 ∷ 8 ∷ []] está ordenada
      3≤8                    -- Prueba de que 3≤8
      (sorted-single 8))     -- Prueba de que [8 ∷ []] está ordenada

5≤2 : 5 ≤ 2
5≤2 = ?

proof-5-2 : Sorted (5 ∷ 2 ∷ [])
proof-5-2 = sorted-cons 5 2 [] 5≤2 (sorted-single 2) 

-- Lema: Ejecutar insert de un elemento sobre una lista ordenada mantiene el orden
insert-sorted : (x : ℕ) (xs : List ℕ) → Sorted xs → Sorted (insert x xs)
insert-sorted x [] sorted-[] = sorted-single x
--insert-sorted x  

insertionSort-sorted : (xs : List ℕ) → Sorted (insertionSort xs)
insertionSort-sorted []        = sorted-[]
insertionSort-sorted (x ∷ xs₁) =
  insert-sorted x (insertionSort xs₁) (insertionSort-sorted xs₁)  


-- Definición de Permutación
data _~_ : List ℕ → List ℕ → Set where
  perm-refl  : {xs : List ℕ} → xs ~ xs                                  -- Toda lista es permutación de si misma
  perm-swap  : {x y : ℕ} {xs : List ℕ} → (x ∷ y ∷ xs) ~ (y ∷ x ∷ xs)    -- Intercambiar dos elementos da una permutación
  perm-skip  : {x : ℕ} {xs ys : List ℕ} → xs ~ ys → (x ∷ xs) ~ (x ∷ ys) -- Añadir un elemento a ambos lados mantiene la permutación
  perm-trans : {xs ys zs : List ℕ} → xs ~ ys → ys ~ zs → xs ~ zs        -- La permutación es transitiva

-- Ejemplos
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
    

-- Ubicar un elemento `x` al principio de una lista `xs`
-- es una permutación de `insert x xs`
insert-perm : (x : ℕ) (xs : List ℕ) → (x ∷ xs) ~ (insert x xs)
insert-perm x [] = perm-refl
insert-perm x (y ∷ ys) with x ≤ᵇ y
... | true = perm-refl              -- insert x (y ∷ ys) = x ∷ y ∷ ys
... | false =
  perm-trans
    perm-swap                       -- [x ∷ y ∷ ...] ~ [y ∷ x ∷ ...]
    (perm-skip (insert-perm x ys))  -- [y ∷ x ∷ ...] ~ [y ∷ (insert x ys)]


-- Toda lista es permutación de su versión ordenada (por insertion sort)
insertion-sort-perm : (xs : List ℕ) → xs ~ (insertionSort xs)
insertion-sort-perm []       = perm-refl
insertion-sort-perm (x ∷ xs₁) =
  perm-trans
    (perm-skip (insertion-sort-perm xs₁)) -- [x ∷ xs₁] ~ [x ∷ (insertionSort xs₁)] (H.I.) por perm-swap 
    (insert-perm x (insertionSort xs₁))   -- [x ∷ (insertionSort xs₁)] ~ (insert x (insertionSort xs₁))

