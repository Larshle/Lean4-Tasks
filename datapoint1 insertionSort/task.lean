import Lean


def isSorted : List Int → Prop
| []          => True
| [_]         => True  -- Use [_] so there is no "unused variable"
| x :: y :: t => (x <= y) ∧ isSorted (y :: t)

def isPermutation (l1 l2 : List Int) : Prop :=
  (l1.length = l2.length) ∧
  (∀ (x : Int), l1.count x = l2.count x)

def insertionSort (xs : List Int) : List Int :=
-- << CODE START >>
  let rec insert (x : Int) (ys : List Int) : List Int :=
    match ys with
    | []      => [x]
    | y :: ys' =>
      if x <= y then
        x :: y :: ys'
      else
        y :: insert x ys'

  let rec sort (arr : List Int) : List Int :=
    match arr with
    | [] => []
    | x :: xs => insert x (sort xs)

  sort xs
-- << CODE END >>

def insertionSort_spec_correct (xs : List Int) (result : List Int) : Prop :=
-- << SPEC START >>
  isSorted result ∧ isPermutation xs result
-- << SPEC END >>

#eval insertionSort [3, 1, 4, 1, 5, 9]
