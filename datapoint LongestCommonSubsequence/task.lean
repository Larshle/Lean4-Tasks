partial def isSubsequenceList (sub original : List Char) : Bool :=
  match sub, original with
  | [], _ => true
  | _, [] => false
  | s :: st, o :: ot =>
    if s == o then
      isSubsequenceList st ot
    else
      isSubsequenceList sub ot

partial def isSubsequence (sub original : String) : Bool :=
  isSubsequenceList sub.data original.data

partial def LCSList (xs ys : List Char) : List Char :=
  match xs, ys with
  | [], _ => []
  | _, [] => []
  | x :: xt, y :: yt =>
    if x == y then
      x :: LCSList xt yt
    else
      let L1 := LCSList xs yt
      let L2 := LCSList xt ys
      if L1.length >= L2.length then L1 else L2

partial def longestCommonSubsequence (str1 : String) (str2 : String) : String :=
  -- << CODE START >>
  let lcsList := LCSList str1.data str2.data
  String.mk lcsList
  -- << CODE END >>

def longestCommonSubsequence_spec (str1 : String) (str2 : String) (result : String) : Prop :=
  -- << SPEC START >>
  (isSubsequence result str1 = true) ∧
  (isSubsequence result str2 = true) ∧
  ∀ candidate : String,
    isSubsequence candidate str1 = true →
    isSubsequence candidate str2 = true →
    candidate.length ≤ result.length
  -- << SPEC END >>
