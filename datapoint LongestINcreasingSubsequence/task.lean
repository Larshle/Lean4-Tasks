def strictlyIncreasing (xs : List Int) : Bool :=
  match xs with
  | [] => true
  | [_] => true         -- Replaced `[x] => true` with `[_] => true`
  | x :: y :: rest => (x < y) && strictlyIncreasing (y :: rest)

partial def isSubsequence (sub original : List Int) : Bool :=
  match sub, original with
  | [], _ => true
  | _, [] => false
  | s :: subT, o :: origT =>
    if s == o then isSubsequence subT origT
    else isSubsequence sub original.tail!

partial def longestIncreasingSubsequence (arr : List Int) : List Int :=
  -- << CODE START >>
  let rec buildDP (xs : List Int) (acc : List (List Int)) : List (List Int) :=
    match xs with
    | [] => acc
    | x :: tail =>
      let bestPrev :=
        acc.filter (fun lis => lis != [] && lis.getLast! < x)
           |>.foldl
               (fun best candidate =>
                 if candidate.length > best.length then candidate else best)
               []
      let newSubseq := bestPrev ++ [x]
      buildDP tail (acc ++ [newSubseq])

  let allSubs := buildDP arr []
  allSubs.foldl
    (fun best candidate =>
      if candidate.length > best.length then candidate else best)
    []
  -- << CODE END >>

def longestIncreasingSubsequence_spec (arr : List Int) (result : List Int) : Prop :=
  -- << SPEC START >>
  isSubsequence result arr = true ∧
  strictlyIncreasing result = true ∧
  ∀ candidate, strictlyIncreasing candidate = true →
    isSubsequence candidate arr = true →
    candidate.length ≤ result.length
  -- << SPEC END >>

