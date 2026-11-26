import LongCycleBounds.AdjustableProfileError
import LongCycleFinite.K5CompactCert.Checks

/-! The certificate multiplier selects the physical radius R = λρ(x).
The rounded tabulated radius upper-bounds ρ(x) in the tilt costs only. -/
noncomputable section
namespace LongCycleBounds.FiveCutoff
open Real PoleBridge LongCycleFinite.K5CompactCert

theorem pi_enclosure : (piLo : ℝ) ≤ π ∧ π ≤ (piHi : ℝ) := by
  norm_num [piLo,piHi]
  constructor <;> linarith [pi_gt_d6,pi_lt_d6]

theorem cell_radii {c : Cell} (hc : c.Geometry) {x : ℝ} (xa : (c.a : ℝ) ≤ x)
    (xb : x ≤ (c.b : ℝ)) :
    0 ≤ x ∧ radius x ≤ (c.rho : ℝ) ∧ radius x < (c.lambda : ℝ)*radius x ∧
      (c.lambda : ℝ)*radius x ≤ ‖PoleBridge.den x 3‖ := by
  obtain ⟨_,ae,_,_,_,_,rp,rbound,lam1,lam3,radiusTest,_,_⟩ := hc
  have a0 : (0:ℚ) ≤ c.a := by rw [ae]; positivity
  have x0 : 0 ≤ x := (show (0:ℝ) ≤ (c.a:ℝ) by exact_mod_cast a0).trans xa
  have b0 := x0.trans xb
  have Rpos : 0 < (c.rho:ℝ) := by exact_mod_cast rp
  have l1 : 1 < (c.lambda:ℝ) := by exact_mod_cast lam1
  have l3 : (c.lambda:ℝ) ≤ 3 := by exact_mod_cast lam3
  have l0 : 0 ≤ (c.lambda:ℝ) := by linarith
  have L := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) l1.le 2
  have U := pow_le_pow_left₀ l0 l3 2
  have pl : 0 ≤ (piLo:ℝ) := by norm_num [piLo]
  have P := pow_le_pow_left₀ pl pi_enclosure.1 2
  have Q := pow_le_pow_left₀ pi_pos.le pi_enclosure.2 2
  have X := pow_le_pow_left₀ x0 xb 2
  have rs : radius x ^ 2 = x^2+π^2 := sq_sqrt (by positivity)
  have rr : (c.b:ℝ)^2+(piHi:ℝ)^2 ≤ (c.rho:ℝ)^2 := by exact_mod_cast rbound
  have admiss : (c.lambda:ℝ)^2*((c.b:ℝ)^2+(piLo:ℝ)^2) ≤
      (c.b:ℝ)^2+9*(piLo:ℝ)^2 := by exact_mod_cast radiusTest
  have ds : ‖PoleBridge.den x 3‖^2 = x^2+(3*π)^2 := by
    rw [Complex.sq_norm]
    simp [PoleBridge.den,Complex.normSq_apply,Complex.add_re,Complex.add_im]
    ring
  refine ⟨x0,(sq_le_sq₀ (radius_pos x).le Rpos.le).mp (by linarith only [rs,rr,Q,X]),
    lt_mul_of_one_lt_left (radius_pos x) l1, ?_⟩
  apply (sq_le_sq₀ (mul_nonneg l0 (radius_pos x).le) (norm_nonneg _)).mp
  rw [mul_pow,rs,ds]
  nlinarith only [admiss,
    mul_nonneg (show 0 ≤ (c.lambda:ℝ)^2-1 by linarith only [L]) (sub_nonneg.mpr X),
    mul_nonneg (show 0 ≤ 9-(c.lambda:ℝ)^2 by linarith only [U]) (sub_nonneg.mpr P)]

#print axioms pi_enclosure
#print axioms cell_radii
end LongCycleBounds.FiveCutoff
