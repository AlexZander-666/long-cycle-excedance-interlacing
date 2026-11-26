import LongCycleBounds.MarkedCompactSign
import LongCycleBounds.FixedCutoffAnalyticAssembly

/-! Uniform two-residue phase comparison for compact intervals and an arbitrary
finite signed insertion, with all row thresholds outside the profile quantifiers. -/
noncomputable section
namespace LongCycleBounds.FixedCutoff
open Real Finset PoleBridge MarkedTwo Filter
open scoped Topology

private theorem rotation_formula (x : ℝ) : compactRotation x=(c x:ℂ)-(s x:ℂ)*Complex.I := by
  have h := PoleBridge.pole_den x 1 le_rfl
  change (radius x:ℂ)/den x 1 = _
  rw [←h]
  apply Complex.ext <;> simp [PoleTails.pole]

/-- Conditional only on a geometric first-pole approximation. The residue B
and the input sequence Y may vary with every bounded parameter independently. -/
theorem compact_phase_threshold (d : ℕ) {X q M m U : ℝ}
    (hX : 0≤X) (q0 : 0≤q) (q1 : q<1) (hM : 0<M) (hm : 0< m) (_hU : 0<U) :
    ∃ P : ℕ, ∀ p≥P, ∀ x∈Set.Icc (0:ℝ) X, ∀ B : ℂ, m≤‖B‖ → ‖B‖≤U →
    ∀ Y C : ℕ→ℝ, (∀ j : ℕ, |Y j-2*(B*compactRotation x^(j+1)).re|≤M*q^(j+1)) →
      (∀ a, 1≤a → a≤d → |C a|≤1) → Y p=0 →
      |(∑ i∈range d, C (i+1)*(radius x)^(i+2)*Y (p+1-(i+2)))/((p:ℝ)+1)| < |Y (p+1)| := by
  let D := X+8
  let σ := 1/D
  have D1 : 1≤D := by dsimp [D];linarith
  have Dp : 0<D := by linarith
  have sp : 0<σ := by dsimp [σ];positivity
  have errpos : 0< m*σ/8 := by positivity
  have cv : Tendsto (fun i : ℕ ↦ M*q^i) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_pow_atTop_nhds_zero_of_lt_one q0 q1).const_mul M
  obtain ⟨J,hJ⟩ := eventually_atTop.mp (cv.eventually_lt_const errpos)
  let A := (d:ℝ)*D^(d+1)*(M+2*U)
  obtain ⟨K,hK⟩ := exists_nat_gt (A/(m*σ))
  refine ⟨J+K,?_⟩
  intro p hp x hx B lo hi Y C est coef zero
  let z := compactRotation x
  let S := B*z^(p+1)
  have rp : 0<radius x := radius_pos x
  have geom : radius x≤D := by
    apply (sq_le_sq₀ rp.le Dp.le).mp
    have sq : (radius x)^2=x^2+π^2 := sq_sqrt (by positivity)
    have xs := pow_le_pow_left₀ hx.1 hx.2 2
    dsimp [D]
    nlinarith only [sq,xs,hX,mul_pos (show 0<4-π by linarith [pi_lt_four]) (show 0<4+π by linarith [pi_pos])]
  have s0 : σ≤ s x := by
    change 1/D≤π/radius x
    rw [div_le_div_iff₀ Dp rp,one_mul]
    exact geom.trans (le_mul_of_one_le_left Dp.le (by linarith [pi_gt_three]))
  have su : s x≤1 := by nlinarith [circle x,sq_nonneg (c x),sq_nonneg (s x-1)]
  have sn : 0≤ s x := sp.le.trans s0
  have cu : |c x|≤1 := (sq_le_sq₀ (abs_nonneg _) (by norm_num)).mp (by
    rw [sq_abs];nlinarith [circle x,sq_nonneg (s x)])
  have qr : ‖z‖=1 := compactRotation_norm x
  have mag : ‖S‖=‖B‖ := by simp [S,norm_pow,qr]
  have er := (est p).trans_lt (hJ (p+1) (by omega))
  rw [zero,zero_sub,abs_neg,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤2)] at er
  change 2*|S.re| < m*σ/8 at er
  have im := Complex.norm_le_abs_re_add_abs_im S
  rw [mag] at im
  have step : (S*z).re=c x*S.re+s x*S.im := by
    rw [show z=(c x:ℂ)-(s x:ℂ)*Complex.I from rotation_formula x]
    simp [Complex.mul_re,Complex.sub_re,Complex.sub_im]
    ring
  have rev := abs_sub (S*z).re (c x*S.re)
  rw [step,add_sub_cancel_left,abs_mul,abs_of_nonneg sn,←step] at rev
  have eC : |c x*S.re|≤|S.re| := by
    rw [abs_mul];exact mul_le_of_le_one_left (abs_nonneg _) cu
  have adv := (est (p+1)).trans_lt (hJ (p+1+1) (by omega))
  rw [pow_succ,←mul_assoc] at adv
  change |Y (p+1)-2*(S*z).re| < m*σ/8 at adv
  have ed := abs_sub (Y (p+1)) (Y (p+1)-2*(S*z).re)
  rw [sub_sub_cancel,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤2)] at ed
  have strict : m*σ < |Y (p+1)| := by
    nlinarith only [mul_le_mul_of_nonneg_left (lo.trans im) sn,
      mul_le_mul_of_nonneg_left s0 hm.le,
      mul_le_of_le_one_left (abs_nonneg S.re) su,er,adv,ed,rev,eC,errpos]
  have cap (j : ℕ) : |Y j|≤M+2*U := by
    have tri := abs_sub_le (Y j) (2*(B*z^(j+1)).re) 0
    simp only [sub_zero,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤2)] at tri
    have rr := Complex.abs_re_le_norm (B*z^(j+1))
    rw [norm_mul,norm_pow,qr,one_pow,mul_one] at rr
    have e := (est j).trans (mul_le_of_le_one_right hM.le (pow_le_one₀ q0 q1.le))
    change |Y j-2*(B*z^(j+1)).re|≤M at e
    linarith only [tri,e,rr,hi]
  have sum : |∑ i∈range d, C (i+1)*(radius x)^(i+2)*Y (p+1-(i+2))|≤A := by
    apply (abs_sum_le_sum_abs ..).trans
    calc
      _ ≤ ∑ _i ∈ range d, D^(d+1)*(M+2*U) := by
        apply sum_le_sum
        intro i hi'
        have idx : i+1≤d := mem_range.mp hi'
        have pow := (pow_le_pow_left₀ rp.le geom (i+2)).trans (pow_le_pow_right₀ D1 (show i+2≤d+1 by omega))
        rw [abs_mul,abs_mul,abs_of_pos (pow_pos rp _)]
        apply mul_le_mul _ (cap _) (abs_nonneg _) (by positivity)
        exact (mul_le_mul (coef _ (by omega) idx) pow (pow_nonneg rp.le _) (by norm_num)).trans_eq (one_mul _)
      _ = _ := by simp [A];ring
  apply lt_trans _ strict
  rw [abs_div,abs_of_pos (by positivity : 0<(p:ℝ)+1),div_lt_iff₀ (by positivity)]
  apply sum.trans_lt
  have kl : A < (K:ℝ)*(m*σ) := (div_lt_iff₀ (by positivity)).mp hK
  have kp : (K:ℝ)≤p := by exact_mod_cast (show K≤p by omega)
  nlinarith only [kl,mul_le_mul_of_nonneg_right kp (mul_pos hm sp).le,mul_pos hm sp]

/-- Exact remaining analytic input. A nonvanishing amplitude is required uniformly
over the entire parameter cube; a pointwise-in-b coefficient limit would be weaker. -/
def CompactPoleEstimate (d : ℕ) (X : ℝ) : Prop :=
  ∃ q M m U : ℝ, 0≤q ∧ q<1 ∧ 0<M ∧ 0< m ∧ 0<U ∧
    ∀ x∈Set.Icc (0:ℝ) X, ∀ b : ℕ→ℝ, (∀ i, 1 ≤ i → i≤d → |b i|≤1) →
    ∃ B : ℂ, m≤‖B‖ ∧ ‖B‖≤U ∧ ∀ j : ℕ,
      |scaledCoeff (tilt b d*logistic (time x)) (radius x) j -
      2*(B*compactRotation x^(j+1)).re| ≤ M*q^(j+1)

theorem compact_profile_gap_of_estimate {k : ℕ} (hk : 2≤k) {X : ℝ} (hX : 0≤X)
    (est : CompactPoleEstimate (k-1) X) :
    ∃ P : ℕ, ∀ p≥P, ∀ u∈Set.Icc (0:ℝ) 1, ∀ x∈Set.Icc (0:ℝ) X,
      CycleProfile.normalizedRow (commonMark k u) p x=0 → ScaledGapAt (commonMark k u) k p x := by
  obtain ⟨q,M,m,U,q0,q1,hM,hm,hU,est⟩ := est
  obtain ⟨P,phase⟩ := compact_phase_threshold (k-1) hX q0 q1 hM hm hU
  refine ⟨P,?_⟩
  intro p hp u hu x hx zero
  let w := commonMark k u
  let b := fun a ↦ tiltCoefficient w a x
  have unit (a : ℕ) : w a∈Set.Icc (0:ℝ) 1 := by
    dsimp only [w,commonMark]
    split_ifs <;> first | exact hu | norm_num
  have er : exp (-x)≤1 := exp_le_one_iff.mpr (by linarith [hx.1])
  have hb (i : ℕ) (hi : 1≤ i) (_ : i≤k-1) : |b i|≤1 := (tilt_bound unit hx.1 hi).trans er
  obtain ⟨B,lo,hi,app⟩ := est x hx b hb
  have one : w 1=0 := by simp [w,commonMark]
  have tail (a : ℕ) (ha : k≤a) : w a=1 := by simp [w,commonMark,show a≠1 by omega,not_lt.mpr ha]
  have hzero := scaled_eq_gain hk w one tail hx.1 (radius x) p
  change CycleProfile.normalizedRow w p x=0 at zero
  rw [zero,mul_zero] at hzero
  exact phase p hp x hx B lo hi _ (fun a ↦ drift w a x) app
    (fun i _ _ ↦ (drift_bound unit hx.1 i).trans er) hzero

#print axioms compact_profile_gap_of_estimate
#print axioms compact_phase_threshold
end LongCycleBounds.FixedCutoff
