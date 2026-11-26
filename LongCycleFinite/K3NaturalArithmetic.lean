import LongCycleFinite.Arithmetic

/-! Exact homogeneous Horner checking with unsigned positive and negative sums. -/

namespace LongCycleFinite.K3

private def unsignedHorner (m s : ℕ) : ℕ → List ℤ → ℕ × ℕ
  | _, [] => (0, 0)
  | n, a :: as =>
    let v := unsignedHorner m s (n-1) as
    let p := 2^(s*n)
    (a.toNat * p + m*v.2, (-a).toNat * p + m*v.1)

private theorem toNat_diff (a : ℤ) : ((a.toNat : ℤ) - (-a).toNat) = a := by
  omega

private theorem natAbs_of_nonpos (a : ℤ) (h : a ≤ 0) : (a.natAbs : ℤ) = -a := by
  omega

private theorem unsignedHorner_eq (x : Dyadic) (hx : x.numer ≤ 0) (cs : List ℤ) :
    let v := unsignedHorner x.numer.natAbs x.shift cs.length cs
    (v.1 : ℤ) - (v.2 : ℤ) = homogeneous x cs := by
  induction cs with
  | nil => rfl
  | cons a as ih =>
    let v := unsignedHorner x.numer.natAbs x.shift as.length as
    let p := (2 : ℕ) ^ (x.shift * (as.length + 1))
    change ((a.toNat * p + x.numer.natAbs * v.2 : ℕ) : ℤ) -
        (( (-a).toNat * p + x.numer.natAbs * v.1 : ℕ) : ℤ) =
      (a <<< (x.shift * (as.length + 1))) + x.numer * homogeneous x as
    rw [Int.shiftLeft_eq, ← ih]
    simp only [Nat.cast_add, Nat.cast_mul, natAbs_of_nonpos x.numer hx]
    change (a.toNat : ℤ) * (p : ℤ) + -x.numer * (v.2 : ℤ) -
        (( (-a).toNat : ℤ) * (p : ℤ) + -x.numer * (v.1 : ℤ)) =
      a * (p : ℤ) + x.numer * ((v.1 : ℤ) - v.2)
    conv_rhs => rw [← toNat_diff a]
    ring

def naturalSign (negative : Bool) (cs : List ℤ) (x : Dyadic) : Bool :=
  decide (x.numer ≤ 0) &&
    let v := unsignedHorner x.numer.natAbs x.shift cs.length cs
    if negative then decide (v.1 < v.2) else decide (v.2 < v.1)

/-- The unsigned Horner checker is equivalent to the exact integer checker
at the negative dyadic endpoints used by the root certificate. -/
theorem naturalSign_eq (negative : Bool) (cs : List ℤ) (x : Dyadic) (hx : x.numer ≤ 0) :
    naturalSign negative cs x = positiveAt negative cs x := by
  simp only [naturalSign, decide_eq_true hx, Bool.true_and, positiveAt, ← unsignedHorner_eq x hx cs]
  cases negative <;> simp [sub_neg]

theorem naturalSign_sound {negative : Bool} {cs : List ℤ} {x : Dyadic}
    (h : naturalSign negative cs x = true) :
    if negative then (ofCoeffs cs).eval x.value < 0 else 0 < (ofCoeffs cs).eval x.value := by
  have hx : x.numer ≤ 0 := of_decide_eq_true (Bool.and_eq_true_iff.mp h).1
  rw [naturalSign_eq negative cs x hx] at h
  exact (positiveAt_iff negative cs x).mp h

#print axioms naturalSign_eq
#print axioms naturalSign_sound

end LongCycleFinite.K3
