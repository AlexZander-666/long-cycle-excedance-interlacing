import LongCycleBounds.MarkedInsertion

/-! A uniform conversion from a scaled row gap to the original sign inequality. -/
noncomputable section
namespace LongCycleBounds.MarkedTwo
open Real

def rowScale (r x : ℝ) (j : ℕ) : ℝ := r^(j+1)/((1-time x)*j.factorial)

theorem rowScale_pos {r : ℝ} (hr : 0<r) (x : ℝ) (j : ℕ) : 0<rowScale r x j := by
  have hp : 0<1-time x := by dsimp [time];linarith [exp_pos (-x)]
  exact div_pos (pow_pos hr _) (mul_pos hp (by positivity))

theorem scaledRow_normalized (u x r : ℝ) (j : ℕ) :
    scaledRow u (time x) r j=rowScale r x j*normalizedRow u j x := by
  have hp : 1-time x≠0 := by dsimp [time];linarith [exp_pos (-x)]
  simp only [scaledRow,normalizedRow,rowScale,pow_succ (1-time x)]
  field_simp

theorem scaled_insertion (u x r : ℝ) (m : ℕ) :
    let Y := scaledRow u (time x) r
    Y (m+3) + rowScale r x (m+3)*deriv (normalizedRow u (m+2)) x =
      (alpha u x*r^2*Y (m+1) + beta u x*r^3*Y m)/((m:ℝ)+3) := by
  dsimp only
  simp only [scaledRow_normalized,(normalizedRow_hasDerivAt u x m).deriv]
  have hp : 1-time x≠0 := by dsimp [time];linarith [exp_pos (-x)]
  unfold rowScale
  rw [Nat.factorial_succ (m+2),Nat.cast_mul,Nat.factorial_succ (m+1),Nat.cast_mul,
    Nat.factorial_succ m,Nat.cast_mul]
  simp only [Nat.cast_succ,pow_succ]
  field_simp
  ring

/-- The antecedent is the common analytic target in all three x-regions;
the conclusion concerns the actual derangement enumerators. -/
theorem sign_of_scaled_gap (u x r : ℝ) (hr : 0<r) (m : ℕ)
    (gap : |(alpha u x*r^2*scaledRow u (time x) r (m+1)+
      beta u x*r^3*scaledRow u (time x) r m)/((m:ℝ)+3)| <
      |scaledRow u (time x) r (m+3)|) :
    0<normalizedRow u (m+3) x * (-deriv (normalizedRow u (m+2)) x) := by
  rw [←scaled_insertion,scaledRow_normalized] at gap
  let Y := normalizedRow u (m+3) x
  let D := deriv (normalizedRow u (m+2)) x
  let S := rowScale r x (m+3)
  have pos : 0<S := rowScale_pos hr _ _
  change |S*Y+S*D| < |S*Y| at gap
  rw [←mul_add,abs_mul,abs_mul,abs_of_pos pos] at gap
  have h : |Y+D| < |Y| := (mul_lt_mul_iff_right₀ pos).mp gap
  have square := (sq_lt_sq).2 h
  change 0<Y*(-D)
  nlinarith [sq_nonneg D]

#print axioms scaled_insertion
#print axioms sign_of_scaled_gap
end LongCycleBounds.MarkedTwo
