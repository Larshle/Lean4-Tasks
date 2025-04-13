partial def mergeSort (arr : List Int) : List Int :=
  -- << CODE START >>
  let rec merge (xs ys : List Int) : List Int :=
    match xs, ys with
    | [], _ => ys
    | _, [] => xs
    | x :: xt, y :: yt =>
      if x <= y then
        x :: merge xt (y :: yt)
      else
        y :: merge (x :: xt) yt

  let rec sort (l : List Int) : List Int :=
    match l with
    | [] => []
    | [x] => [x]
    | _ =>
      let half := l.length / 2
      let left := l.take half
      let right := l.drop half
      let leftSorted := sort left
      let rightSorted := sort right
      merge leftSorted rightSorted

  sort arr
  -- << CODE END >>

def count (x : Int) (l : List Int) : Nat :=
  match l with
  | []   => 0
  | h::t => if h = x then 1 + count x t else count x t

def mergeSort_spec (arr : List Int) (result : List Int) : Prop :=
  -- << SPEC START >>
  -- 1) Same length as the input
  (result.length = arr.length) ∧

  -- 2) The list is sorted in non-decreasing order
  (∀ i : Nat, i < result.length - 1 → result[i]! ≤ result[i+1]!) ∧

  -- 3) The output is a permutation of the input, i.e. same element frequencies
  (∀ x, count x arr = count x result)
  -- << SPEC END >>
