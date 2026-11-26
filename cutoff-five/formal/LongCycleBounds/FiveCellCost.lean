import LongCycleBounds.FiveCellDrift
import LongCycleFinite.K5CompactCert.ExpBounds

/-! Certified bounds for the true finite tilt at the adjustable radius. -/
noncomputable section
namespace LongCycleBounds.FiveCutoff
open Real Finset FixedCutoff PoleBridge Band LongCycleFinite.K5CompactCert

theorem cell_tilt_caps {c : Cell} (hc : c.Valid) {x : ℝ} (xa : (c.a:ℝ) ≤ x)
    (xb : x ≤ (c.b:ℝ)) {w : ℕ → ℝ} (w1 : w 1 = 0) (unit : ∀ i, w i ∈ Set.Icc (0:ℝ) 1) :
    |tiltCoefficient w 1 x| ≤ (c.b1:ℝ) ∧ |tiltCoefficient w 2 x| ≤ (c.b2:ℝ) ∧
    |tiltCoefficient w 3 x| ≤ (c.b3:ℝ) ∧ |tiltCoefficient w 4 x| ≤ (c.b4:ℝ) := by
  obtain ⟨hx,_,_,_⟩ := cell_radii hc.1 xa xb
  obtain ⟨rLo,rHi⟩ := Cell.r_bounds hc xa xb
  obtain ⟨m2,m3,m4,_⟩ := cell_moment_caps hc.1 hx rLo rHi
  let r := exp (-x)
  have rp : 0 < r := exp_pos _
  have hp : 0 < (c.rHi:ℝ) := rp.trans_le rHi
  have h1 : r/(1+r) ≤ (c.rHi:ℝ)/(1+c.rHi) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  have coef (a : ℕ) (M : ℝ) (hm : |cycleMoment a x| ≤ M) :
      |tiltCoefficient w a x| ≤ M / a.factorial := by
    have diff : |w a-1| ≤ 1 := abs_le.mpr ⟨by linarith [(unit a).1],by linarith [(unit a).2]⟩
    rw [tiltCoefficient,abs_div,abs_mul,abs_of_pos (by positivity : (0:ℝ)<a.factorial)]
    exact div_le_div_of_nonneg_right ((mul_le_of_le_one_left (abs_nonneg _) diff).trans hm) (by positivity)
  have a2 := coef 2 _ m2
  have a3 := coef 3 _ m3
  have a4 := coef 4 _ m4
  norm_num [Nat.factorial] at a2 a3 a4
  refine ⟨?_,a2.trans (by exact_mod_cast roundUp_ge (c.m2/2)),
    a3.trans (by exact_mod_cast roundUp_ge (c.m3/6)),a4.trans (by exact_mod_cast roundUp_ge (c.m4/24))⟩
  have eq : tiltCoefficient w 1 x = r/(1+r) := (FixedFour.tilt_forms w w1 x).1
  rw [eq,abs_of_pos (by positivity)]
  exact h1.trans (by exact_mod_cast roundUp_ge (c.rHi/(1+c.rHi)))

theorem cell_cost {c : Cell} (hc : c.Valid) {x : ℝ} (xa : (c.a:ℝ) ≤ x)
    (xb : x ≤ (c.b:ℝ)) {w : ℕ → ℝ} (w1 : w 1=0) (unit : ∀ i, w i ∈ Set.Icc (0:ℝ) 1) :
    cost (fun a ↦ tiltCoefficient w a x) ((c.lambda:ℝ)*radius x) 4 ≤ (c.cost:ℝ) := by
  obtain ⟨_,hρ,_,_⟩ := cell_radii hc.1 xa xb
  obtain ⟨a1,a2,a3,a4⟩ := cell_tilt_caps hc xa xb w1 unit
  have lam := hc.1.2.2.2.2.2.2.2.2.1
  have l1 : (1:ℝ) < c.lambda := by exact_mod_cast lam
  have l0 : (0:ℝ) ≤ c.lambda := by linarith
  have rr : (c.lambda:ℝ)*radius x ≤ (c.radius:ℝ) := by
    simpa [Cell.radius,mul_comm] using mul_le_mul_of_nonneg_left hρ l0
  have rp := mul_nonneg l0 (radius_pos x).le
  have term (i : ℕ) (M : ℝ) (h : |tiltCoefficient w i x| ≤ M) :
      |tiltCoefficient w i x| * ((c.lambda:ℝ)*radius x)^i ≤ M*(c.radius:ℝ)^i :=
    mul_le_mul h (pow_le_pow_left₀ rp rr _) (pow_nonneg rp _) ((abs_nonneg _).trans h)
  have one := term 1 _ a1
  have two := term 2 _ a2
  have three := term 3 _ a3
  have four := term 4 _ a4
  apply le_trans _ (show (c.computedCost:ℝ) ≤ c.cost by exact_mod_cast hc.2.1.2.2.2.2.2.2.2.2.1)
  simp only [cost,sum_range_succ,sum_range_zero,zero_add,Nat.reduceAdd,pow_one,
    Cell.computedCost,Rat.cast_add,Rat.cast_mul,Rat.cast_pow]
  simp only [pow_one] at one
  linarith only [one,two,three,four]

#print axioms cell_tilt_caps
#print axioms cell_cost
end LongCycleBounds.FiveCutoff
