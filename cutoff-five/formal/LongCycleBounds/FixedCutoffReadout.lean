import LongCycleBounds.CycleProfileProduct
import LongCycleBounds.CycleProfileNormalization
import LongCycleBounds.FixedCutoffOuterGap

/-! Exact conversion between the two numerical coordinate systems and genuine
cycle-profile permutation rows. The sign lemmas consume the row insertion equation. -/
noncomputable section
namespace LongCycleBounds.FixedCutoff
open Real Finset PowerSeries PoleBridge Band MarkedTwo

def drift (w : ℕ→ℝ) (a : ℕ) (x : ℝ) : ℝ :=
  (w (a+1)-w a)*cycleMoment (a+1) x/a.factorial

theorem drift_bound {w : ℕ→ℝ} (unit : ∀ a, w a∈Set.Icc (0:ℝ) 1)
    {x : ℝ} (hx : 0≤x) (a : ℕ) : |drift w a x|≤exp (-x) := by
  have diff : |w (a+1)-w a|≤1 := abs_le.mpr ⟨by linarith [(unit (a+1)).1,(unit a).2],
    by linarith [(unit (a+1)).2,(unit a).1]⟩
  rw [drift,abs_div,abs_mul,abs_of_pos (by positivity : (0:ℝ)<a.factorial),div_le_iff₀ (by positivity)]
  have e := mul_le_mul diff (cycleMoment_abs hx (a+1)) (abs_nonneg _) zero_le_one
  simpa [mul_comm] using e

theorem tilt_bound {w : ℕ→ℝ} (unit : ∀ a, w a∈Set.Icc (0:ℝ) 1)
    {x : ℝ} (hx : 0≤x) {a : ℕ} (ha : 1≤a) : |tiltCoefficient w a x|≤exp (-x) := by
  have e := tiltCoefficient_abs hx ha (unit a)
  exact e.trans (div_le_self (exp_pos _).le (by exact_mod_cast ha))

def profileSeries (w : ℕ→ℝ) (k : ℕ) (x : ℝ) : PowerSeries ℝ :=
  tilt (fun a ↦ tiltCoefficient w a x) (k-1) * logistic (time x)

theorem profile_coefficient {k : ℕ} (hk : 2≤k) (w : ℕ→ℝ) (w1 : w 1=0)
    (tail : ∀ a≥k,w a=1) {x : ℝ} (hx : 0≤x) (j : ℕ) :
    (1-time x)*(j.factorial:ℝ)*coeff j (profileSeries w k x)= CycleProfile.normalizedRow w j x := by
  let t := time x
  have den : 0<1-t := by dsimp [t,time];linarith [exp_pos (-x)]
  have h := congrArg (coeff j) (CycleProfile.bounded_logistic hk w w1 tail hx)
  rw [CycleProfile.normalized_coefficient,coeff_C_mul] at h
  change (CycleProfile.row j w).eval t/((1-t)^j*j.factorial)=(1-t)*coeff j (profileSeries w k x) at h
  change (1-t)*_*_=(CycleProfile.row j w).eval t/(1-t)^j
  field_simp at h ⊢
  linarith only [h]

def gain (R : ℝ) (j : ℕ) (x : ℝ) : ℝ := R^(j+1)/((1-time x)*j.factorial)

theorem gain_pos {R : ℝ} (hR : 0<R) (j : ℕ) (x : ℝ) : 0<gain R j x := by
  have den : 0<1-time x := by unfold time;linarith [exp_pos (-x)]
  unfold gain
  positivity

theorem scaled_eq_gain {k : ℕ} (hk : 2≤k) (w : ℕ→ℝ) (w1 : w 1=0)
    (tail : ∀ a≥k,w a=1) {x : ℝ} (hx : 0≤x) (R : ℝ) (j : ℕ) :
    scaledCoeff (profileSeries w k x) R j = gain R j x*CycleProfile.normalizedRow w j x := by
  rw [←profile_coefficient hk w w1 tail hx j,scaledCoeff,gain]
  have den : 0<1-time x := by unfold time;linarith [exp_pos (-x)]
  field_simp

theorem raw_eq_profile {k : ℕ} (hk : 2≤k) (w : ℕ→ℝ) (w1 : w 1=0)
    (tail : ∀ a≥k,w a=1) {x : ℝ} (hx : 0≤x) (j : ℕ) :
    (1-time x)*raw (fun a ↦ tiltCoefficient w a x) (k-1) j x=CycleProfile.normalizedRow w j x := by
  rw [←profile_coefficient hk w w1 tail hx j]
  unfold profileSeries raw
  ring

/-- A single falling factorial and the factorials of the two rows exactly
cancel; p+1 survives from the upper row gain. -/
private theorem gain_ratio {p a : ℕ} (ha : a≤p) {R : ℝ} (_hR : 0<R) (x : ℝ) :
    gain R (p+1) x*(p.descFactorial a:ℝ) =
    R^(a+1)*gain R (p-a) x/((p:ℝ)+1) := by
  have fac : ((p-a).factorial:ℝ)*(p.descFactorial a:ℝ)=p.factorial := by
    exact_mod_cast Nat.factorial_mul_descFactorial ha
  have den : 0<1-time x := by unfold time;linarith [exp_pos (-x)]
  rw [gain,gain,Nat.factorial_succ,Nat.cast_mul,Nat.cast_succ]
  field_simp
  rw [show p+1+1=a+1+(p-a+1) by omega,pow_add]
  rw [←fac]
  ring

theorem raw_gap_to_normalized_sign {p k : ℕ} (hk : 2≤k) (w : ℕ→ℝ) (w1 : w 1=0)
    (tail : ∀ a≥k,w a=1) {x : ℝ} (hx : 0≤x)
    (ins : CycleProfile.normalizedRow w (p+1) x + deriv (CycleProfile.normalizedRow w p) x =
      ∑ i∈range (k-1), (p.descFactorial (i+1):ℝ)*drift w (i+1) x*CycleProfile.normalizedRow w (p-(i+1)) x)
    (gap : let A := fun j ↦ raw (fun a ↦ tiltCoefficient w a x) (k-1) j x
      ; |∑ i∈range (k-1), (p.descFactorial (i+1):ℝ)*drift w (i+1) x*A (p-(i+1))| < |A (p+1)|) :
    0<CycleProfile.normalizedRow w (p+1) x*(-deriv (CycleProfile.normalizedRow w p) x) := by
  let A := fun j ↦ raw (fun a ↦ tiltCoefficient w a x) (k-1) j x
  let H := fun j ↦ CycleProfile.normalizedRow w j x
  let I := ∑ i∈range (k-1), (p.descFactorial (i+1):ℝ)*drift w (i+1) x*A (p-(i+1))
  have den : 0<1-time x := by unfold time;linarith [exp_pos (-x)]
  have ih : ∑ i∈range (k-1), (p.descFactorial (i+1):ℝ)*drift w (i+1) x*H (p-(i+1))=(1-time x)*I := by
    dsimp only [I]
    rw [mul_sum]
    apply sum_congr rfl
    intro i _
    change _*CycleProfile.normalizedRow w _ x=_
    rw [←raw_eq_profile hk w w1 tail hx]
    dsimp [A]
    ring
  change H (p+1)+_=_ at ins
  rw [ih] at ins
  have aa : H (p+1)=(1-time x)*A (p+1) := (raw_eq_profile hk w w1 tail hx _).symm
  change |I| < |A (p+1)| at gap
  have e := (sq_lt_sq).2 gap
  have good : 0<A (p+1)*(A (p+1)-I) := by nlinarith only [e,sq_nonneg (A (p+1)-I)]
  change 0<H (p+1)*(-_) 
  rw [aa] at ins ⊢
  have dt : -deriv (CycleProfile.normalizedRow w p) x=(1-time x)*(A (p+1)-I) := by linarith only [ins]
  rw [dt]
  nlinarith only [mul_pos (sq_pos_of_pos den) good]

theorem scaled_gap_to_normalized_sign {p k : ℕ} (hk : 2≤k) (hp : k-1≤p)
    (w : ℕ→ℝ) (w1 : w 1=0) (tail : ∀ a≥k,w a=1) {x : ℝ} (hx : 0≤x)
    {R : ℝ} (hR : 0<R)
    (ins : CycleProfile.normalizedRow w (p+1) x + deriv (CycleProfile.normalizedRow w p) x =
      ∑ i∈range (k-1), (p.descFactorial (i+1):ℝ)*drift w (i+1) x*CycleProfile.normalizedRow w (p-(i+1)) x)
    (gap : let Y := scaledCoeff (profileSeries w k x) R
      ; |(∑ i∈range (k-1), drift w (i+1) x*R^(i+2)*Y (p+1-(i+2)))/((p:ℝ)+1)| < |Y (p+1)|) :
    0<CycleProfile.normalizedRow w (p+1) x*(-deriv (CycleProfile.normalizedRow w p) x) := by
  let Y := scaledCoeff (profileSeries w k x) R
  let H := fun j ↦ CycleProfile.normalizedRow w j x
  let g := gain R (p+1) x
  let I := (∑ i∈range (k-1),drift w (i+1) x*R^(i+2)*Y (p+1-(i+2)))/((p:ℝ)+1)
  have times : g*(H (p+1)+deriv (CycleProfile.normalizedRow w p) x)=I := by
    change g*(CycleProfile.normalizedRow w (p+1) x+_)=_
    rw [ins,mul_sum]
    dsimp only [I]
    rw [sum_div]
    apply sum_congr rfl
    intro i hi
    have a : i+1≤p := (show i+1≤k-1 from mem_range.mp hi).trans hp
    have same : p+1-(i+2)=p-(i+1) := by omega
    rw [same]
    change g*(_*_*_)=_*_*scaledCoeff (profileSeries w k x) R (p-(i+1)) / _
    rw [scaled_eq_gain hk w w1 tail hx]
    have e := gain_ratio a hR x
    change g*(p.descFactorial (i+1):ℝ)=_ at e
    linear_combination (drift w (i+1) x*H (p-(i+1)))*e
  have one : g*H (p+1)=Y (p+1) := (scaled_eq_gain hk w w1 tail hx R _).symm
  rw [mul_add,one] at times
  change |I| < |Y (p+1)| at gap
  have e := (sq_lt_sq).2 gap
  have good : 0<Y (p+1)*(Y (p+1)-I) := by nlinarith only [e,sq_nonneg (Y (p+1)-I)]
  have dt : g*(-deriv (CycleProfile.normalizedRow w p) x)=Y (p+1)-I := by linarith only [times]
  rw [←dt,←one] at good
  apply pos_of_mul_pos_right (a:=g^2) _ (sq_nonneg _)
  change 0<g^2*(H (p+1)*(-_))
  nlinarith only [good]

/-- Derangements never see the artificially assigned weight for a singleton. -/
theorem row_commonMark (k n : ℕ) (u : ℝ) :
    CycleProfile.row n (commonMark k u) = CycleProfile.row n (CycleProfile.profile k u) := by
  unfold CycleProfile.row
  apply sum_congr rfl
  intro σ _
  split_ifs with h
  · unfold CycleProfile.term CycleProfile.cycleWeight
    have e : σ.cycleType.map (commonMark k u)=σ.cycleType.map (CycleProfile.profile k u) := by
      apply Multiset.map_congr rfl
      intro i hi
      have low : 2≤ i := LongCycles.le_of_mem_cycleType h hi
      simp [commonMark,CycleProfile.profile,show i≠1 by omega]
    rw [e]
  · rfl

theorem normalized_commonMark (k j : ℕ) (u : ℝ) :
    CycleProfile.normalizedRow (commonMark k u) j = CycleProfile.normalizedRow (CycleProfile.profile k u) j := by
  funext x
  simp only [CycleProfile.normalizedRow,row_commonMark]

#print axioms row_commonMark
#print axioms scaled_gap_to_normalized_sign
#print axioms raw_gap_to_normalized_sign
#print axioms scaled_eq_gain
end LongCycleBounds.FixedCutoff
