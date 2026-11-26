import LongCycleFinite.Assembly

namespace LongCycleFinite

open Polynomial

noncomputable section

def insertionStep (n : ℕ) (f : Polynomial ℝ) : Polynomial ℝ :=
  (1 + C (n : ℝ) * X) * f + X * (1 - X) * f.derivative

private theorem insertionStep_add (n : ℕ) (f g : Polynomial ℝ) :
    insertionStep n (f + g) = insertionStep n f + insertionStep n g := by
  simp only [insertionStep, derivative_add]
  ring

private theorem insertionStep_C_mul (n : ℕ) (a : ℝ) (f : Polynomial ℝ) :
    insertionStep n (C a * f) = C a * insertionStep n f := by
  simp only [insertionStep, derivative_C_mul]
  ring

private theorem X_mul_derivative_X_pow (j : ℕ) :
    (X : Polynomial ℝ) * derivative (X ^ j) = C (j : ℝ) * X ^ j := by
  cases j with
  | zero => simp
  | succ j =>
    rw [derivative_X_pow_succ, pow_succ']
    simp only [Nat.cast_succ]
    ring

private theorem insertionStep_basis (j d : ℕ) :
    insertionStep (2 * j + d + 1) ((X : Polynomial ℝ)^j * (1 + X)^d) =
      C ((j : ℝ) + 1) * (X^j * (1 + X)^(d + 1)) +
        C (2 * (d : ℝ)) * (X^(j + 1) * (1 + X)^(d - 1)) := by
  have h (e : ℕ) : (X : Polynomial ℝ) * derivative (X^j * (1 + X)^e) =
      C (j : ℝ) * (X^j * (1 + X)^e) + C (e : ℝ) * (X^(j + 1) * (1 + X)^(e - 1)) := by
    rw [derivative_mul, mul_add, ← mul_assoc X, X_mul_derivative_X_pow, derivative_pow,
      pow_succ X j]
    simp only [derivative_add, derivative_one, derivative_X, zero_add, mul_one]
    ring
  rw [insertionStep, show (X : Polynomial ℝ) * (1 - X) = (1 - X) * X by ring, mul_assoc, h]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_two, Nat.cast_one, map_add, map_mul, map_one,
    map_ofNat]
  cases d with
  | zero => simp; ring
  | succ d =>
    simp only [Nat.add_one_sub_one, Nat.cast_succ, map_add, map_one, pow_succ]
    ring

theorem expandGamma_addCoeffs (d : ℕ) (as bs : List ℤ) :
    expandGamma d (addCoeffs as bs) = expandGamma d as + expandGamma d bs := by
  induction as generalizing d bs with
  | nil => simp [addCoeffs, expandGamma]
  | cons a as ih =>
    cases bs with
    | nil => simp [addCoeffs, expandGamma]
    | cons b bs =>
      simp only [addCoeffs, expandGamma, Int.cast_add, map_add, ih]
      ring

end

/-- One gamma recurrence step, indexed by the original exponent `j` and the
remaining binomial power `d`. Zero at the upper endpoint is omitted. -/
def gammaAdvance : ℕ → ℕ → List ℤ → List ℤ
  | _, _, [] => []
  | d, j, a :: as =>
      ((j : ℤ) + 1) * a :: addCoeffs (if d = 0 then [] else [2 * (d : ℤ) * a])
        (gammaAdvance (d - 2) (j + 1) as)

theorem expandGamma_gammaAdvance (d j : ℕ) (cs : List ℤ) (h : 2 * (cs.length - 1) ≤ d) :
    expandGamma (d + 1) (gammaAdvance d j cs) * X^j =
      insertionStep (2 * j + d + 1) (expandGamma d cs * X^j) := by
  induction cs generalizing d j with
  | nil => simp [gammaAdvance, expandGamma, insertionStep]
  | cons a as ih =>
    have hhead : expandGamma d (a :: as) * X^j =
        C (a : ℝ) * (X^j * (1 + X)^d) + expandGamma (d - 2) as * X^(j + 1) := by
      rw [expandGamma, pow_succ]
      ring
    rw [hhead, insertionStep_add, insertionStep_C_mul, insertionStep_basis]
    have htail : insertionStep (2 * j + d + 1) (expandGamma (d - 2) as * X^(j + 1)) =
        expandGamma (d + 1 - 2) (gammaAdvance (d - 2) (j + 1) as) * X^(j + 1) := by
      cases as with
      | nil => simp [expandGamma, insertionStep, gammaAdvance]
      | cons b bs =>
        have hd : 2 ≤ d := by simp only [List.length_cons] at h; omega
        have hs : 2 * ((b :: bs).length - 1) ≤ d - 2 := by
          simp only [List.length_cons] at h ⊢
          omega
        rw [show 2 * j + d + 1 = 2 * (j + 1) + (d - 2) + 1 by omega,
          ← ih (d - 2) (j + 1) hs, show d - 2 + 1 = d + 1 - 2 by omega]
    rw [htail, gammaAdvance, expandGamma, expandGamma_addCoeffs,
      show d + 1 - 2 = d - 1 by omega]
    by_cases hz : d = 0
    · simp only [hz, if_pos, expandGamma, Int.cast_add, Int.cast_natCast, Int.cast_one,
        Int.cast_mul, map_mul, map_add, map_one, Nat.cast_zero, mul_zero, C_0, zero_mul,
        zero_add, add_zero, pow_succ]
      ring
    · simp only [if_neg hz, expandGamma, Int.cast_add, Int.cast_natCast, Int.cast_one,
        Int.cast_ofNat, Int.cast_mul, map_mul, map_add, map_one, mul_zero, add_zero, pow_succ]
      ring

theorem eulerian_of_gamma_step (d : ℕ) {a b : List ℤ} (hlen : 2 * (a.length - 1) ≤ d)
    (ha : expandGamma d a = LongCycles.eulerian (d + 1)) (hb : gammaAdvance d 0 a = b) :
    expandGamma (d + 1) b = LongCycles.eulerian (d + 2) := by
  subst b
  have hs := expandGamma_gammaAdvance d 0 a hlen
  simp only [pow_zero, mul_one, Nat.mul_zero, zero_add] at hs
  rw [hs, ha]
  exact (LongCycleBounds.longEulerian_succ (d + 1)).symm

theorem length_addCoeffs (as bs : List ℤ) : (addCoeffs as bs).length = max as.length bs.length := by
  induction as generalizing bs with
  | nil => simp [addCoeffs]
  | cons a as ih => cases bs <;> simp [addCoeffs, ih, Nat.succ_max_succ]

theorem length_mulCoeffs_le (as bs : List ℤ) (hb : 0 < bs.length) :
    (mulCoeffs as bs).length ≤ as.length + bs.length - 1 := by
  induction as with
  | nil => simp [mulCoeffs]
  | cons a as ih =>
    simp only [mulCoeffs, length_addCoeffs, scaleCoeffs, List.length_map, List.length_cons, max_le_iff]
    omega

theorem expandGamma_scaleCoeffs (n : ℕ) (a : ℤ) (as : List ℤ) :
    expandGamma n (scaleCoeffs a as) = C (a : ℝ) * expandGamma n as := by
  induction as generalizing n with
  | nil => simp [expandGamma, scaleCoeffs]
  | cons b bs ih =>
    change expandGamma n (a * b :: scaleCoeffs a bs) = _
    simp only [expandGamma, Int.cast_mul, map_mul, ih]
    ring

theorem expandGamma_square (d : ℕ) (as : List ℤ) (h : 2 * (as.length - 1) ≤ d) :
    expandGamma (2 * d) (mulCoeffs as as) = (expandGamma d as)^2 := by
  cases as with
  | nil => simp [expandGamma, mulCoeffs]
  | cons a as =>
    have hmul := length_mulCoeffs_le (a :: as) (a :: as) (by simp)
    have h' : 2 * ((mulCoeffs (a :: as) (a :: as)).length - 1) ≤ 2 * d := by omega
    apply Polynomial.eq_of_infinite_eval_eq
    refine (Set.Ioi_infinite (-1 : ℝ)).mono ?_
    intro t (ht : -1 < t)
    change (expandGamma (2 * d) (mulCoeffs (a :: as) (a :: as))).eval t = _
    rw [eval_expandGamma _ _ h' ht.ne', eval_pow, eval_expandGamma _ _ h ht.ne', ofCoeffs_mulCoeffs,
      eval_mul, show (1 + t)^(2*d) = ((1 + t)^d)^2 by rw [← pow_mul, Nat.mul_comm]]
    ring

def correctedGamma (k : ℕ) (a b : List ℤ) : List ℤ :=
  addCoeffs b (0 :: scaleCoeffs ((Nat.fast_choose (2*k) k / 2 : ℕ) : ℤ) (mulCoeffs a a))

theorem correctedGamma_expands (k : ℕ) (hk : 2 ≤ k) {a b : List ℤ}
    (hl : 2 * (a.length - 1) ≤ k - 2)
    (ha : expandGamma (k - 2) a = LongCycles.eulerian (k - 1))
    (hb : expandGamma (2 * k - 2) b = LongCycles.eulerian (2 * k - 1)) :
    expandGamma (2 * k - 2) (correctedGamma k a b) = firstQ k := by
  rw [correctedGamma, expandGamma_addCoeffs, hb, expandGamma, Int.cast_zero, C_0, zero_mul, zero_add,
    show 2 * k - 2 - 2 = 2 * (k - 2) by omega, expandGamma_scaleCoeffs,
    expandGamma_square _ _ hl, ha]
  unfold firstQ
  simp only [Int.cast_natCast, Nat.fast_choose, ← Nat.choose_eq_descFactorial_div_factorial]
  ring

theorem firstSplit_of_gamma_expansions {k : ℕ} (hk : 3 ≤ k) {p q : List ℤ} {outer : Dyadic}
    {ws : List Window} (hw : ws.length = k - 2) (hcheck : caseOK p q outer ws = true)
    (hp : expandGamma (2 * k - 3) p = firstP k) (hq : expandGamma (2 * k - 2) q = firstQ k) :
    LongCycles.WeakRealInterlacing (LongCycles.enumerator (2 * k - 1) k)
      (LongCycles.enumerator (2 * k) k) := by
  have hpart : (boundaryOK p q outer ws.length = true ∧ orderOK outer ws = true) ∧
      signsOK p q ws.length ws = true := by
    simpa only [caseOK, Bool.and_eq_true_iff] using hcheck
  have hb := hpart.1.1
  simp only [boundaryOK, Bool.and_eq_true_iff, decide_eq_true_eq] at hb
  obtain ⟨hpl, hql⟩ := hb.1.1.1
  have hs := expandGamma_interlacing hpl hql
    (caseOK_sound (show 0 < ws.length by omega) hcheck)
  rw [show ws.length + ws.length + 1 + 1 = 2 * k - 2 by omega,
    show ws.length + ws.length + 1 = 2 * k - 3 by omega, hp, hq] at hs
  obtain ⟨ha, hb⟩ := firstSplit_quotients k (by omega)
  rw [ha, hb]
  exact weak_mul_X_of_strict hs

#print axioms expandGamma_gammaAdvance
#print axioms eulerian_of_gamma_step
#print axioms correctedGamma_expands
#print axioms firstSplit_of_gamma_expansions

end LongCycleFinite
