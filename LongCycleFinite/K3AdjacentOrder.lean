import LongCycleFinite.K3Readout

/-! A linear scan of the adjacent dyadic intervals, checked against the root readout. -/

namespace LongCycleFinite.K3

def extraLinear : List Window → List Window → Bool
  | [], _ => true
  | p :: ps, q :: r :: rs =>
    q.right.less p.left && p.right.less r.left && extraLinear ps (r :: rs)
  | _, _ => false

def equalLinear : List Window → List Window → Bool
  | [], _ => true
  | p :: ps, q :: qs =>
    p.right.less q.left &&
      (match ps with | [] => true | r :: _ => q.right.less r.left) &&
      equalLinear ps qs
  | _, _ => false

private theorem extraLinear_at {old new : List Window} (h : extraLinear old new = true)
    (i : ℕ) (hi : i < old.length) :
    ((bracketAt new i).right.less (bracketAt old i).left &&
      (bracketAt old i).right.less (bracketAt new (i + 1)).left) = true := by
  induction old generalizing new i with
  | nil => simp at hi
  | cons p ps ih =>
    match new with
    | [] => simp [extraLinear] at h
    | [_] => simp [extraLinear] at h
    | q :: r :: rs =>
      obtain ⟨head, tail⟩ := Bool.and_eq_true_iff.mp h
      cases i with
      | zero => simpa [bracketAt] using head
      | succ i =>
        simpa [bracketAt, Nat.succ_eq_add_one] using
          ih tail i (by simpa using hi)

private theorem equalLinear_at {old new : List Window} (h : equalLinear old new = true)
    (i : ℕ) (hi : i < old.length) :
    ((bracketAt old i).right.less (bracketAt new i).left &&
      (if i + 1 < old.length then
        (bracketAt new i).right.less (bracketAt old (i + 1)).left else true)) = true := by
  induction old generalizing new i with
  | nil => simp at hi
  | cons p ps ih =>
    cases new with
    | nil => simp [equalLinear] at h
    | cons q qs =>
      obtain ⟨head, tail⟩ := Bool.and_eq_true_iff.mp h
      cases i with
      | zero =>
        cases ps with
        | nil => simpa [bracketAt] using head
        | cons s ss => simpa [bracketAt] using head
      | succ i =>
        simpa [bracketAt, Nat.succ_eq_add_one] using ih tail i (by simpa using hi)

def linearOrderAtOK (n : ℕ) (old new : RowCertificate) : Bool :=
  if n % 2 = 0 then extraLinear old.brackets new.brackets
  else equalLinear old.brackets new.brackets

theorem orderAtOK_of_linear {n : ℕ} {old new : RowCertificate}
    (h : linearOrderAtOK n old new = true) : orderAtOK n old new = true := by
  by_cases parity : n % 2 = 0
  · simp only [orderAtOK, if_pos parity, extraOrder, List.all_eq_true]
    intro i hi
    exact extraLinear_at (by simpa [linearOrderAtOK, parity] using h) i (List.mem_range.mp hi)
  · simp only [orderAtOK, if_neg parity, equalOrder, List.all_eq_true]
    intro i hi
    exact equalLinear_at (by simpa [linearOrderAtOK, parity] using h) i (List.mem_range.mp hi)

#print axioms orderAtOK_of_linear

end LongCycleFinite.K3
