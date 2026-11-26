import LongCycleBounds.FiveCellCost
import LongCycleBounds.FiveCutoffCompactSign
import LongCycleFinite.K5CompactCert.Verified

/-! The finite rational budget implies the analytic order-44 error after
supplying the certified lower bound for the genuine complex amplitude. -/
noncomputable section
namespace LongCycleBounds.FiveCutoff
open Real Finset FixedCutoff PoleBridge Band MarkedTwo LongCycleFinite.K5CompactCert

theorem residue_of_inverse_amplitude {c : Cell} (hc : c.Valid) {x : ℝ} (xa : (c.a:ℝ) ≤ x)
    (xb : x ≤ (c.b:ℝ)) {w : ℕ → ℝ} (w1 : w 1=0) (unit : ∀ i, w i ∈ Set.Icc (0:ℝ) 1)
    (inv : 1 ≤ ‖tiltValue (fun a ↦ tiltCoefficient w a x) 4 (nearestPole x)‖ * (c.invD:ℝ)) :
    let b := fun a ↦ tiltCoefficient w a x
    let R := (c.lambda:ℝ)*radius x
    max (radius x) (radius x*R/(2*π^2)) * (radius x/R)^44 * exp (cost b R 4) <
      (3/1000) * (s x * ‖tiltValue b 4 (nearestPole x)‖) := by
  let ρ := radius x
  let L : ℝ := c.lambda
  let R := L*ρ
  let b := fun a ↦ tiltCoefficient w a x
  let D := ‖tiltValue b 4 (nearestPole x)‖
  have rp : 0 < ρ := radius_pos x
  obtain ⟨_,cap,_,_⟩ := cell_radii hc.1 xa xb
  have l1 : (1:ℝ) < c.lambda := by exact_mod_cast hc.1.2.2.2.2.2.2.2.2.1
  have lp : 0 < L := by linarith
  have dl := (tilt_value_bounds b 4 (nearestPole x) (nearestPole_norm x).le).1
  have dp : 0 < D := (exp_pos _).trans_le dl
  have pl : 0 < (piLo:ℝ) := by norm_num [piLo]
  have P := pi_enclosure.1
  have spp : 0 < s x := div_pos pi_pos rp
  have recip : 1 ≤ s x * (c.reciprocalS:ℝ) := by
    have h : ρ/π ≤ (c.rho:ℝ)/(piLo:ℝ) := div_le_div₀ (rp.le.trans cap) cap pl P
    have round : (c.rho:ℝ)/(piLo:ℝ) ≤ (c.reciprocalS:ℝ) := by exact_mod_cast roundUp_ge (c.rho/piLo)
    have bound := (div_le_iff₀ pi_pos).mp (h.trans round)
    dsimp [s,ρ] at *
    rw [div_mul_eq_mul_div,le_div_iff₀ (radius_pos x),one_mul]
    linarith only [bound]
  have sq : ρ^2 ≤ (c.rho:ℝ)^2 := pow_le_pow_left₀ rp.le cap 2
  have den : 0 < 2*(piLo:ℝ)^2 := by positivity
  have denle : 2*(piLo:ℝ)^2 ≤ 2*π^2 := by linarith only [pow_le_pow_left₀ pl.le P 2]
  have fac : max ρ (ρ*R/(2*π^2)) ≤ (c.residueFactor:ℝ) := by
    simp only [Cell.residueFactor,Rat.cast_max,Rat.cast_div,Rat.cast_mul,Rat.cast_pow,Rat.cast_ofNat]
    apply max_le_max cap
    rw [show ρ*R=L*ρ^2 by dsimp [R]; ring]
    exact div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left sq lp.le) den denle
  have exp0 := exp_pos (cost b R 4)
  have ec : exp (cost b R 4) ≤ (c.expCost:ℝ) :=
    (exp_le_exp.mpr (cell_cost hc xa xb w1 unit)).trans (Cell.exponent_bounds hc).1
  have rfac : 0 ≤ max ρ (ρ*R/(2*π^2)) := rp.le.trans (le_max_left _ _)
  have sup := mul_le_mul fac ec exp0.le (rfac.trans fac)
  have idpos : 0 ≤ (c.invD:ℝ) := by
    have z : 0 < D*(c.invD:ℝ) := zero_lt_one.trans_le inv
    exact (pos_of_mul_pos_right z dp.le).le
  have rspos : 0 ≤ (c.reciprocalS:ℝ) := (pos_of_mul_pos_right (zero_lt_one.trans_le recip) spp.le).le
  have err : ((c.residueFactor:ℝ)*c.expCost*c.invD*c.reciprocalS)/L^44 ≤ (c.error44:ℝ) := by
    dsimp only [L]
    exact_mod_cast hc.2.2.1
  have emax : (c.error44:ℝ) < 3/1000 := by
    have rational : c.error44 < 3/1000 := hc.2.2.2.2.2.1.trans_lt (by decide +kernel)
    have z : (c.error44:ℝ) < ((3/1000:ℚ):ℝ) := Rat.cast_lt.mpr rational
    simpa only [Rat.cast_div,Rat.cast_ofNat] using z
  have mult : 1 ≤ (s x * D)*((c.invD:ℝ)*c.reciprocalS) := by
    have t := mul_le_mul inv recip (by norm_num : (0:ℝ) ≤ 1) (mul_nonneg dp.le idpos)
    nlinarith only [t]
  have pq : ρ/R=1/L := by dsimp [R];field_simp
  change max ρ (ρ*R/(2*π^2))*(ρ/R)^44*exp (cost b R 4) < (3/1000)*(s x*D)
  rw [pq,div_pow,one_pow]
  let A := max ρ (ρ*R/(2*π^2))*exp (cost b R 4)
  have a0 : 0 ≤ A := mul_nonneg rfac exp0.le
  have aUpper : A*((c.invD:ℝ)*c.reciprocalS)/L^44 ≤ (c.error44:ℝ) := by
    apply le_trans _ err
    apply div_le_div_of_nonneg_right _ (pow_nonneg lp.le _)
    simpa only [← mul_assoc] using mul_le_mul_of_nonneg_right sup (mul_nonneg idpos rspos)
  have lhs : max ρ (ρ*R/(2*π^2))*(1/L^44)*exp (cost b R 4) ≤
      (A*((c.invD:ℝ)*c.reciprocalS)/L^44)*(s x*D) := by
    have v := mul_le_mul_of_nonneg_left mult (div_nonneg a0 (pow_nonneg lp.le 44))
    calc
      _ = A/L^44*1 := by dsimp only [A]; ring
      _ ≤ A/L^44*((s x*D)*((c.invD:ℝ)*c.reciprocalS)) := v
      _ = _ := by ring
  exact lhs.trans_lt (mul_lt_mul_of_pos_right (aUpper.trans_lt emax) (mul_pos spp dp))

#print axioms residue_of_inverse_amplitude
end LongCycleBounds.FiveCutoff
