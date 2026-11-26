import LongCycleBounds.FixedCutoffSignedTilt
import LongCycleBounds.MarkedLabelExpansion

/-! Absolute estimates for both the positive sites and the zero site of
the logistic series with any finite, real, signed cycle-mark tilt. -/
noncomputable section
namespace LongCycleBounds.FixedCutoff
open Finset PowerSeries Real MarkedTwo
open scoped Classical

def label (b : ℕ → ℝ) (d : ℕ) (h : ℝ) (j : ℕ) : ℝ :=
  j.factorial * coeff j (tilt b d * linearExp h)

/-- Relative deviation of the positive label from its unmarked point mass. -/
theorem positive_label_error (b : ℕ → ℝ) (d : ℕ) {h : ℝ} (hh : 0 < h)
    {j : ℕ} (hj : 0 < j) :
    |label b d h j - h^j| ≤ h^j*(exp (cost b (j/h) d)-1) := by
  let ρ : ℝ := j/h
  have rpos : 0<ρ := by dsimp [ρ]; positivity
  have rj : ρ*h=(j:ℝ) := by dsimp [ρ];field_simp
  let F := scaledCoeff (linearExp h) ρ
  have form (i : ℕ) : F i=ρ^(i+1)*(h^i/i.factorial) := by simp [F,scaledCoeff,linearExp,coeff_mk]
  have nn (i : ℕ) : 0≤F i := by rw [form];positivity
  have inc (i : ℕ) (hi : i<j) : F i ≤ F (i+1) := by
    have rel : F (i+1)*((i:ℝ)+1) = F i * (ρ*h) := by
      rw [form,form,Nat.factorial_succ,Nat.cast_mul,Nat.cast_succ,pow_succ h,pow_succ ρ (i+1)]
      field_simp
    have pos : 0<(i:ℝ)+1 := by positivity
    apply le_of_mul_le_mul_right (a:=(i:ℝ)+1) _ pos
    rw [rel,rj]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hi) (nn i)
  have mono (i m : ℕ) (hi : i ≤ m) : m ≤ j → F i≤F m := by
    induction m,hi using Nat.le_induction with
    | base => exact fun _ ↦ le_rfl
    | succ m _ ih => exact fun hm ↦ (ih (by omega)).trans (inc m (by omega))
  let Y := scaledCoeff (tilt b d * linearExp h) ρ j
  have bias := signed_tilt_bias b rpos.le (nn j) (linearExp h) d j
    (fun i le ↦ (abs_of_nonneg (nn i)).trans_le (mono i j le le_rfl))
  change |Y-F j| ≤ _ at bias
  have resc : (ρ^(j+1)/j.factorial)*label b d h j = Y := by
    dsimp [Y,label,scaledCoeff]
    field_simp
  have baseline : (ρ^(j+1)/j.factorial)*h^j=F j := by rw [form];ring
  have z : 0<ρ^(j+1)/j.factorial := by positivity
  apply le_of_mul_le_mul_left (a:=ρ^(j+1)/j.factorial) _ z
  rw [←abs_of_pos z,←abs_mul,mul_sub,resc,baseline,abs_of_pos z,←mul_assoc,baseline]
  exact bias

/-- The zero site admits a separate estimate for every positive test radius. -/
theorem zero_label_bound (b : ℕ → ℝ) (d : ℕ) {ρ : ℝ} (hr : 0 < ρ) (j : ℕ) :
    |label b d 0 j| ≤ j.factorial*exp (cost b ρ d)/ρ^j := by
  have form (i : ℕ) : scaledCoeff (linearExp 0) ρ i =
      if i=0 then ρ else 0 := by
    by_cases hi : i=0 <;> simp [scaledCoeff,linearExp,coeff_mk,hi]
  have bound (i : ℕ) : |scaledCoeff (linearExp 0) ρ i| ≤ ρ := by
    rw [form]; split <;> simp [abs_of_pos hr,hr.le]
  have s := signed_tilt_bias b hr.le hr.le (linearExp 0) d j (fun i _ ↦ bound i)
  let Y := scaledCoeff (tilt b d * linearExp 0) ρ j
  have y : |Y| ≤ ρ*exp (cost b ρ d) := by
    have t := abs_sub_le Y (scaledCoeff (linearExp 0) ρ j) 0
    simp only [sub_zero] at t
    linarith [bound j]
  dsimp [Y,scaledCoeff] at y
  rw [abs_mul,abs_of_pos (pow_pos hr _),pow_succ] at y
  have c : ρ^j*|coeff j (tilt b d * linearExp 0)| ≤ exp (cost b ρ d) :=
    le_of_mul_le_mul_left (a:=ρ) (by nlinarith only [y]) hr
  rw [label,abs_mul,abs_of_nonneg (by positivity : 0≤(j.factorial:ℝ)),le_div_iff₀ (pow_pos hr j)]
  nlinarith only [mul_le_mul_of_nonneg_left c (by positivity : (0:ℝ)≤j.factorial)]


/-- A radius growing exponentially in x controls the zero label even
arbitrarily far in the negative-real tail. -/
theorem cost_zero_radius {d : ℕ} (hd : 0 < d) {x : ℝ} (hx : 0 ≤ x) (b : ℕ → ℝ)
    (hb : ∀ a, 1 ≤ a → a ≤ d → |b a| ≤ exp (-x)) :
    cost b (exp (x/d)) d ≤ d := by
  unfold cost
  calc
    _ ≤ ∑ _i ∈ range d, (1:ℝ) := by
      apply sum_le_sum
      intro i hi
      have ha : i+1 ≤ d := mem_range.mp hi
      have ha' : ((i+1 : ℕ) : ℝ) ≤ d := by exact_mod_cast ha
      have hd' : 0 < (d:ℝ) := by exact_mod_cast hd
      apply (mul_le_mul_of_nonneg_right (hb (i+1) (by omega) ha) (by positivity)).trans
      rw [←exp_nat_mul,←exp_add,←exp_zero]
      apply exp_le_exp.mpr
      have h : (i+1:ℕ) * (x/(d:ℝ)) ≤ x := by
        calc _ ≤ (d:ℝ)*(x/(d:ℝ)) := mul_le_mul_of_nonneg_right ha' (by positivity)
             _ = x := by field_simp
      linarith
    _ = _ := by simp

theorem zero_label_decay {d : ℕ} (hd : 0 < d) {x : ℝ} (hx : 0 ≤ x) (b : ℕ → ℝ)
    (hb : ∀ a, 1 ≤ a → a ≤ d → |b a| ≤ exp (-x)) (j : ℕ) :
    |label b d 0 j| ≤ j.factorial * exp d / (exp (x/d))^j := by
  apply (zero_label_bound b d (exp_pos _) j).trans
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
    (exp_le_exp.mpr (cost_zero_radius hd hx b hb)) (by positivity)) (by positivity)

/-- The expansion includes h=0 and converges absolutely for real t with |t|<1. -/
theorem logistic_label_sum (b : ℕ→ℝ) (d : ℕ) {t : ℝ} (ht : ‖t‖ < 1) (j : ℕ) :
    HasSum (fun h : ℕ ↦ t^h * label b d h j)
      (j.factorial * coeff j (tilt b d * logistic t)) := by
  apply ((mul_logistic_labels ht (tilt b d) j).mul_left (j.factorial:ℝ)).congr_fun
  intro h
  dsimp [label]
  ring

#print axioms positive_label_error
#print axioms zero_label_decay
#print axioms logistic_label_sum
end LongCycleBounds.FixedCutoff
