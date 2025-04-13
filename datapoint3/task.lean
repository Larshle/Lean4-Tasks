/--
  A helper to check if a list is strictly increasing.
--/
def strictlyIncreasing (xs : List Int) : Bool :=
  match xs with
  | [] => true
  | [_] => true         -- Replaced `[x] => true` with `[_] => true`
  | x :: y :: rest => (x < y) && strictlyIncreasing (y :: rest)

/--
  A helper to check if `sub` is a subsequence of `original`.
  i.e., can we obtain `sub` by removing zero or more elements
  from `original` without reordering the remaining elements?

  Marked as `partial def` to avoid the termination error;
  Lean is unsure it always decreases without a proof.
--/
partial def isSubsequence (sub original : List Int) : Bool :=
  match sub, original with
  | [], _ => true
  | _, [] => false
  | s :: subT, o :: origT =>
    if s == o then isSubsequence subT origT
    else isSubsequence sub original.tail!

partial def longestIncreasingSubsequence (arr : List Int) : List Int :=
  -- << CODE START >>
  -- We'll build a List of best subsequences for each tail.
  -- This is a naive O(n^2) approach:
  --
  -- buildDP xs = for each prefix of xs, store
  -- the LIS that ends at each position.
  --
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
  -- pick the subsequence with max length
  allSubs.foldl
    (fun best candidate =>
      if candidate.length > best.length then candidate else best)
    []
  -- << CODE END >>

/--
  Specification for the Longest Increasing Subsequence:
  1) The result is a subsequence of `arr`.
  2) The result is strictly increasing.
  3) No strictly increasing subsequence of `arr` is longer than the result.
--/
def longestIncreasingSubsequence_spec (arr : List Int) (result : List Int) : Prop :=
  -- << SPEC START >>
  isSubsequence result arr = true ∧
  strictlyIncreasing result = true ∧
  ∀ candidate, strictlyIncreasing candidate = true →
    isSubsequence candidate arr = true →
    candidate.length ≤ result.length
  -- << SPEC END >>

-- Optional quick checks:
#eval longestIncreasingSubsequence []                -- Expect []
#eval longestIncreasingSubsequence [3, 1, 2]         -- Expect [1, 2]
#eval longestIncreasingSubsequence [10, 9, 2, 5, 3, 7, 101, 18]  -- e.g. [2, 3, 7, 18]
