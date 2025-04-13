def decodeRLE (lst : List (Char × Nat)) : String :=
  match lst with
  | [] => ""
  | (ch, cnt) :: tail =>
    let repeated := String.mk (List.replicate cnt ch)
    repeated ++ decodeRLE tail

def runLengthEncode (s : String) : List (Char × Nat) :=
  -- << CODE START >>
  let chars := s.data

  let rec encodeAux (acc : List (Char × Nat)) (rest : List Char) : List (Char × Nat) :=
    match rest with
    | [] => acc.reverse
    | h :: t =>
      match acc with
      | (ch, count) :: accTail =>
        if ch = h then
          encodeAux ((ch, count + 1) :: accTail) t
        else
          encodeAux ((h, 1) :: (ch, count) :: accTail) t
      | [] =>
        encodeAux ([(h, 1)]) t

  let encoded := encodeAux [] chars
  encoded
  -- << CODE END >>

def runLengthEncode_spec (s : String) (result : List (Char × Nat)) : Prop :=
  -- << SPEC START >>
  (∀ pair ∈ result, pair.snd > 0) ∧
  (∀ i : Nat, i < result.length - 1 → (result[i]!).fst ≠ (result[i+1]!).fst) ∧
  decodeRLE result = s
  -- << SPEC END >>
