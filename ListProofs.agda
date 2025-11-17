module ListProofs where

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat

data ⊥ : Set where

-- symmetry
sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

-- congruence
cong : {A B : Set} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

-- transitivity
trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

data List (A : Set ) : Set  where
  [] : List A
  _::_ : A → List A → List A

consEq : (x : Nat) (xs : List Nat) → x :: xs ≡ x :: xs
consEq x xs = refl

-- negation defined as in intuitionistic logic
¬ : Set → Set
¬ P = P → ⊥

emptyNotEqCons : {A : Set} (x : A) (xs : List A) → ¬ ([] ≡ x :: xs)
emptyNotEqCons x xs ()

length : List Nat → Nat
length [] = 0
length (x :: xs) = suc (length xs)

-- List concatenation
_++_ : List Nat → List Nat → List Nat
[] ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

-- appending empty lists give the same list
appendNilLeft : (xs : List Nat) → [] ++ xs ≡ xs
appendNilLeft xs = refl

appendNilRight : (xs : List Nat) → xs ++ [] ≡ xs
appendNilRight [] = refl
appendNilRight (x :: xs) = cong (x ::_) (appendNilRight xs)

-- append is associative
appendAssoc : (xs ys zs : List Nat) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
appendAssoc [] ys zs = refl
appendAssoc (x :: xs) ys zs = cong (x ::_) (appendAssoc xs ys zs)

-- length of an append is the sum of the lengths
length-++ : (xs ys : List Nat) → (length xs) + (length ys) ≡ length (xs ++ ys)
length-++ [] ys = refl
length-++ (x :: xs) ys = cong suc (length-++ xs ys)

-- appending empty list does not increase the length
length-empty-++-l : (xs : List Nat) → length ([] ++ xs) ≡ length (xs)
length-empty-++-l _ = refl

-- appending empty list to the right does not increase length
length-empty-++-r : (xs : List Nat) → length (xs ++ []) ≡ length xs
length-empty-++-r [] = refl
length-empty-++-r (x :: xs) = cong suc (length-empty-++-r xs)

-- appending empty list on both sides does not affect length
append-empty-both : (xs : List Nat) → ([] ++ xs) ++ [] ≡ xs
append-empty-both xs = appendNilRight xs

snoc : List Nat → Nat → List Nat
snoc [] x        = x :: []
snoc (y :: ys) x = y :: (snoc ys x)

length-snoc : (xs : List Nat) (n : Nat) → length (snoc xs n) ≡ suc (length xs)
length-snoc [] n        = refl
length-snoc (x :: xs) n = cong suc (length-snoc xs n)

-- prepending

prepend : List Nat → Nat → List Nat
prepend xs n = n :: xs

-- prepending adds 1 to the length
length-prepend : (xs : List Nat) (n : Nat) → length (prepend xs n) ≡ suc (length xs)
length-prepend _ _ = refl 

-- reversing
reverse : List Nat → List Nat
reverse []        = []
reverse (x :: xs) = (reverse xs) ++ (x :: [])

+1≡suc : (n : Nat) → n + suc zero ≡ suc n
+1≡suc zero = refl
+1≡suc (suc n) = cong suc (+1≡suc n)

-- length of the reverse list is the same as the length of the list
reverse-length : (xs : List Nat) → length (reverse xs) ≡ length xs
reverse-length [] = refl
reverse-length (x :: xs) =
  let
    s₁ : length (reverse (x :: xs)) ≡ length (reverse xs ++ (x :: []))
    s₁ = refl -- definition of reverse

    s₂ : length (reverse xs ++ (x :: [])) ≡ length (reverse xs) + length (x :: [])
    s₂ = sym (length-++ (reverse xs) (x :: [])) -- using helper lemma

    s₃ : length (reverse xs) + length (x :: []) ≡ length (reverse xs) + 1
    s₃ = refl -- definition of length

    s₄ : length (reverse xs) + 1 ≡ suc (length (reverse xs))
    s₄ = +1≡suc (length (reverse xs)) -- using helper lemma

    s₅ : suc (length (reverse xs)) ≡ suc (length xs)
    s₅ = cong suc (reverse-length xs) -- congruency of adding one to the lengths
  in
    trans s₁ (trans s₂ (trans s₃ (trans s₄ s₅)))

-- appending empty list to the right gives the same list
lemma₁-reverse : (xs : List Nat) → (xs ++ []) ≡ xs
lemma₁-reverse []         = refl
lemma₁-reverse (x :: xs₁) = cong (x ::_) (lemma₁-reverse xs₁)

-- associativity of appending function
assoc-++ : (xs ys zs : List Nat) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
assoc-++ [] ys zs         = refl
assoc-++ (x :: xs₁) ys zs = cong (x ::_) (assoc-++ xs₁ ys zs)

-- distributivity of reversing
reverse-dist : (xs ys : List Nat) → reverse (xs ++ ys) ≡ (reverse ys) ++ (reverse xs)
reverse-dist [] ys         = sym (lemma₁-reverse (reverse ys))
reverse-dist (x :: xs₁) ys =
  let
    s₁ : reverse ((x :: xs₁) ++ ys) ≡ reverse (x :: (xs₁ ++ ys))
    s₁ = refl

    s₂ : reverse (x :: (xs₁ ++ ys)) ≡ reverse (xs₁ ++ ys) ++ (x :: [])
    s₂ = refl

    s₃ : reverse (xs₁ ++ ys) ++ (x :: []) ≡ ((reverse ys) ++ (reverse xs₁)) ++ (x :: [])
    s₃ = cong (_++ (x :: [])) (reverse-dist xs₁ ys)

    s₄ : ((reverse ys) ++ (reverse xs₁)) ++ (x :: []) ≡ (reverse ys) ++ ((reverse xs₁) ++ (x :: []))
    s₄ = assoc-++ (reverse ys) (reverse xs₁) (x :: [])

    s₅ : (reverse ys) ++ ((reverse xs₁) ++ (x :: [])) ≡ (reverse ys) ++ (reverse (x :: xs₁))
    s₅ = refl
  in
    trans s₁ (trans s₂ (trans s₃ (trans s₄ s₅)))
    

-- reversing twice gives the same list
reverse-reverse : (xs : List Nat) → reverse (reverse xs) ≡ xs
reverse-reverse [] = refl
reverse-reverse (x :: xs₁) =
  let
    s₁ : reverse (reverse (x :: xs₁)) ≡ reverse (reverse xs₁ ++ (x :: []))
    s₁ = refl

    s₂ : reverse (reverse xs₁ ++ (x :: [])) ≡ (reverse (x :: [])) ++ (reverse (reverse xs₁))
    s₂ = reverse-dist (reverse xs₁) (x :: [])

    s₃ : (reverse (x :: [])) ++ (reverse (reverse xs₁)) ≡ (x :: []) ++ xs₁
    s₃ = cong ((x :: []) ++_) (reverse-reverse xs₁)

    s₄ : (x :: []) ++ xs₁ ≡ x :: xs₁
    s₄ = refl
  in
    trans s₁ (trans s₂ (trans s₃ s₄))
