-- Reverse a list of integers
def myReverse (xs : List Int) : List Int :=
-- << CODE START >>
match xs with
| []       => []
| x :: xs' => myReverse xs' ++ [x]

/-
  Specification for `myReverse`:
  Reversing a list twice should yield the original list.
-/
def myReverse_spec (xs : List Int) : Prop :=
myReverse (myReverse xs) = xs

/-
  Lemma: Reversal of concatenated lists.
  For any lists `xs` and `ys`, the reversal of their concatenation equals the reversal
  of `ys` appended with the reversal of `xs`.
-/
theorem myReverse_append (xs ys : List Int) : myReverse (xs ++ ys) = myReverse ys ++ myReverse xs :=
by
  induction xs with
  | nil =>
      simp [List.append, myReverse]
  | cons a xs ih =>
      simp [List.append, myReverse]
      rw [ih]
      simp [List.append]
      -- Removed the extra `rfl` because the goal has already been solved.


/-
  Theorem: Double reversal property.
  For any list `xs`, reversing it twice yields the original list.
-/
theorem myReverse_double_inv : ∀ xs : List Int, myReverse (myReverse xs) = xs :=
by
  intro xs
  induction xs with
  | nil =>
      simp [myReverse]
  | cons a xs ih =>
      simp [myReverse]
      rw [myReverse_append]
      have h : myReverse [a] = [a] := by simp [myReverse]
      rw [h]
      simp [ih, List.append]

#eval myReverse [1, 2, 3] -- Output: [3, 2, 1]
#eval myReverse [] -- Output: []
#eval myReverse [1] -- Output: [1]
#eval myReverse [1, 2] -- Output: [2, 1]
