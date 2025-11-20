# Insertion Sort correctness proof in Agda

Developed by Andrés Felipe Puerta and Santiago Suárez Pérez

## Insertion Sort
Insertion sort is a O(n^2) algorithm that sorts lists.
Its simple implementation makes it easy to verify as well.

From Wikipedia:

"Insertion sort iterates, consuming one input element each repetition, and grows a sorted output list. At each iteration, insertion sort removes one element from the input data, finds the correct location within the sorted list, and inserts it there. It repeats until no input elements remain."

## Correctness proofs
In order to prove the correctness of the insertion sort algorithm we focused on two aspects:
1. Output must be in increasing order (or any order if generalized).
2. Output must be a permutation of its input.

We first defined the insertion sort algorithm itself, and then defined two datatypes expressing the properties of Sorted and Permutation (via the `~` operator).
This is possible because of the Curry-Howard correspondence (also known as propositions-as-types).

## Versions used:
* agda v2.7.0.1
* GNU Emacs 30.2 with agda2-mode
* GHC v9.10.1

## References
* https://en.wikipedia.org/wiki/Insertion_sort
* https://agda.github.io/agda-stdlib/master/Data.List.Relation.Binary.Permutation.Declarative.html#1644
* https://plfa.github.io/Lists/
* https://gemini.google.com/
