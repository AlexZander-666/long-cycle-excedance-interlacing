import LongCycleBounds.FixedFourCoefficients

/-! Factored true insertion moments at the fourth-degree tilt. -/
noncomputable section
namespace LongCycleBounds.FiveCutoff
open Real Polynomial LongCycles Band FixedCutoff

def height (r : ℝ) := r/(1+r)^2
def imbalance (r : ℝ) := (1-r)/(1+r)

private theorem e2 : eulerian 2 = 1+X := by
  rw [show 2 = 1+1 by decide, longEulerian_succ, longEulerian_one]
  simp

private theorem e3 : eulerian 3 = 1+C (4:ℝ)*X+X^2 := by
  change eulerian (2+1) = _
  rw [longEulerian_succ,e2]
  simp [C_ofNat]
  ring

private theorem e4 : eulerian 4 = 1+C (11:ℝ)*X+C (11:ℝ)*X^2+X^3 := by
  change eulerian (3+1) = _
  rw [longEulerian_succ,e3]
  simp [C_ofNat]
  ring

theorem moment_forms (x : ℝ) :
    let r := exp (-x)
    let h := height r
    let v := imbalance r
    cycleMoment 2 x = -h ∧ cycleMoment 3 x = -h*v ∧
      cycleMoment 4 x = -h*(1-6*h) ∧ cycleMoment 5 x = -h*v*(1-12*h) := by
  dsimp only
  have nz : 1+exp (-x) ≠ 0 := by positivity
  constructor
  · simp [cycleMoment, moment, height, longEulerian_one, neg_div]
  constructor
  · simp [cycleMoment, moment, height, imbalance, e2]
    field_simp
    ring
  constructor
  · simp [cycleMoment, moment, height, e3]
    field_simp
    ring
  · simp [cycleMoment, moment, height, imbalance, e4]
    field_simp
    ring

theorem shape_bounds {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    0 ≤ height r ∧ height r ≤ r ∧ height r ≤ 1/4 ∧
      0 ≤ imbalance r ∧ imbalance r ≤ 1 ∧
      4*height r=1-(imbalance r)^2 := by
  have den : 0 < 1+r := by linarith
  unfold height imbalance
  refine ⟨by positivity, div_le_self h0 (one_le_pow₀ (by linarith : 1 ≤ 1+r)),
    ?_, div_nonneg (by linarith) den.le, (div_le_one₀ den).mpr (by linarith), ?_⟩
  · rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [sq_nonneg (1-r)]
  · field_simp
    ring

theorem fifth_shape_bound {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    |imbalance r*(1-12*height r)| ≤ 1 := by
  obtain ⟨_,_,_,v0,v1,relation⟩ := shape_bounds h0 h1
  let v := imbalance r
  have eq : imbalance r*(1-12*height r)=3*v^3-2*v := by
    dsimp [v]
    nlinarith only [congrArg (fun t : ℝ ↦ imbalance r*t) relation]
  rw [eq,abs_le]
  constructor
  · by_cases small : v ≤ 1/3
    · nlinarith only [small,pow_nonneg (show 0 ≤ v from v0) 3]
    · nlinarith only [sq_nonneg (1-v),mul_nonneg (sq_nonneg v) (show 0 ≤ 3*v-1 by linarith)]
  · nlinarith only [mul_nonneg (show 0 ≤ 1-v by linarith only [show v ≤ 1 from v1])
      (show 0 ≤ 3*v^2+3*v+1 by nlinarith only [sq_nonneg v, show 0 ≤ v from v0])]

#print axioms moment_forms
#print axioms shape_bounds
#print axioms fifth_shape_bound
end LongCycleBounds.FiveCutoff
