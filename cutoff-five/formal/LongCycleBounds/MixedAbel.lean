import LongCycleBounds.LinearCenteredInteraction

/-! Finite Abel cancellation for a pair of distinct complex odd poles. -/
noncomputable section
namespace LongCycleBounds.Band
open Finset

/-- A weighted homogeneous geometric sum, allowing either complex argument to vanish. -/
def abelSum (b : ℕ → ℝ) (z w : ℂ) (M : ℕ) : ℂ :=
  ∑ i ∈ range (M+1), (b i:ℂ)*z^i*w^(M-i)

private theorem abelSum_succ (b : ℕ → ℝ) (z w : ℂ) (M : ℕ) :
    abelSum b z w (M+1) = w*abelSum b z w M + (b (M+1):ℂ)*z^(M+1) := by
  unfold abelSum
  rw [sum_range_succ,mul_sum]
  simp only [Nat.sub_self,pow_zero,mul_one]
  congr 1
  apply sum_congr rfl
  intro i hi
  have := mem_range.mp hi
  rw [show M+1-i=M-i+1 by omega,pow_succ]
  ring

/-- Abel bound for nonincreasing nonnegative weights on the complex unit bidisk. -/
theorem abelSum_gap (b : ℕ → ℝ) (hb : ∀ i, 0≤b i) (hm : Antitone b)
    {z w : ℂ} (hz : ‖z‖≤1) (hw : ‖w‖≤1) (M : ℕ) :
    ‖(z-w)*abelSum b z w M‖ ≤ 2*b 0 := by
  let J (i : ℕ) := (z-w)*abelSum b z w i-(b i:ℂ)*z^(i+1)
  have hJ (i : ℕ) : ‖J i‖ ≤ 2*b 0-b i := by
    induction i with
    | zero =>
      have eqn : J 0 = -(b 0:ℂ)*w := by simp [J,abelSum]; ring
      rw [eqn,norm_mul,norm_neg,Complex.norm_real,Real.norm_of_nonneg (hb 0)]
      nlinarith [mul_le_mul_of_nonneg_left hw (hb 0)]
    | succ i ih =>
      have eqn : J (i+1) = w*J i + (((b i-b (i+1):ℝ):ℂ)*w*z^(i+1)) := by
        simp only [J,abelSum_succ,Complex.ofReal_sub,pow_succ z (i+1)]
        ring
      have hdiff := sub_nonneg.mpr (hm (Nat.le_succ i))
      have h1 : ‖w*J i‖≤‖J i‖ := by rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) hw
      have h2 : ‖((b i-b (i+1):ℝ):ℂ)*w*z^(i+1)‖ ≤ b i-b (i+1) := by
        rw [norm_mul,norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg hdiff]
        exact (mul_le_of_le_one_right (mul_nonneg hdiff (norm_nonneg _)) (pow_le_one₀ (norm_nonneg _) hz)).trans
          (mul_le_of_le_one_right hdiff hw)
      rw [eqn]
      exact (norm_add_le ..).trans (by linarith)
  have eqn : (z-w)*abelSum b z w M = J M+(b M:ℂ)*z^(M+1) := by simp [J]
  rw [eqn]
  apply (norm_add_le ..).trans
  rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg (hb M)]
  linarith [hJ M,mul_le_of_le_one_right (hb M) (pow_le_one₀ (norm_nonneg _) hz (n:=M+1))]

/-- Oriented mixed term before summing over odd labels. -/
def mixedPair (j k : ℕ) (z w : ℂ) : ℂ :=
  ∑ a ∈ Icc k (j-k), (interactionWeight j a:ℂ)*z^a*w^(j-a)

private theorem mixedPair_factor {j k : ℕ} (hk : 1≤k) (hj : 2*k≤j) (z w : ℂ) :
    mixedPair j k z w = z^k*w^k*(
      abelSum (fun i ↦ 1/(k+i:ℕ)) z w (j-2*k)+
      abelSum (fun i ↦ 1/(k+i:ℕ)) w z (j-2*k)) := by
  let M := j-2*k
  let b (i : ℕ) : ℝ := 1/(k+i:ℕ)
  have reindex : mixedPair j k z w = ∑ i ∈ range (M+1),
      (interactionWeight j (k+i):ℂ)*z^(k+i)*w^(j-(k+i)) := by
    unfold mixedPair
    rw [← Finset.Ico_add_one_right_eq_Icc,sum_Ico_eq_sum_range]
    simp only [show j-k+1-k=M+1 by dsimp [M]; omega, Nat.add_comm k]
  have reflected : abelSum b w z M = ∑ i ∈ range (M+1), (b (M-i):ℂ)*z^i*w^(M-i) := by
    unfold abelSum
    rw [← sum_range_reflect (fun i ↦ (b i:ℂ)*w^i*z^(M-i)) (M+1)]
    apply sum_congr rfl
    intro i hi
    have := mem_range.mp hi
    simp only [show M+1-1-i=M-i by omega,show M-(M-i)=i by omega]
    ring
  change _ = z^k*w^k*(abelSum b z w M+abelSum b w z M)
  rw [reindex,reflected,abelSum,←sum_add_distrib,mul_sum]
  apply sum_congr rfl
  intro i hi
  have hm := mem_range.mp hi
  have hab : j-(k+i)=k+(M-i) := by dsimp [M] at *; omega
  rw [interactionWeight_eq_add (by omega) (by dsimp [M] at hm; omega),hab,pow_add,pow_add]
  simp only [b,Complex.ofReal_add]
  ring

/-- The original support interval and the actual interaction weights, before division
by the pole separation. Applies also to the empty preceding row at the first split. -/
theorem mixedPair_gap {j k : ℕ} (hk : 1≤k) (hjk : k≤j) {z w : ℂ}
    (hz : ‖z‖≤1) (hw : ‖w‖≤1) :
    ‖z-w‖*‖mixedPair j k z w‖ ≤ 4/(k:ℝ)*‖z‖^k*‖w‖^k := by
  by_cases hj : 2*k≤j
  · let b (i : ℕ) : ℝ := 1/(k+i:ℕ)
    have hp : ∀ i, 0≤b i := fun i ↦ by dsimp [b]; positivity
    have hm : Antitone b := by
      intro i l hil
      apply one_div_le_one_div_of_le
      · exact_mod_cast (by omega : 0<k+i)
      · exact_mod_cast (by omega : k+i≤k+l)
    have h1 := abelSum_gap b hp hm hz hw (j-2*k)
    have h2 := abelSum_gap b hp hm hw hz (j-2*k)
    rw [norm_mul,norm_sub_rev w z,← norm_mul] at h2
    have hh : ‖(z-w)*(abelSum b z w (j-2*k)+abelSum b w z (j-2*k))‖≤4/(k:ℝ) := by
      rw [mul_add]
      apply (norm_add_le ..).trans
      have hb0 : b 0=1/(k:ℝ) := by simp [b]
      rw [hb0] at h1 h2
      exact (add_le_add h1 h2).trans_eq (by ring)
    rw [←norm_mul,mixedPair_factor hk hj]
    change ‖(z-w)*(z^k*w^k*_)‖ ≤ _
    rw [mul_left_comm,norm_mul,norm_mul,norm_pow,norm_pow]
    simpa only [mul_assoc,mul_left_comm,mul_comm] using
      mul_le_mul_of_nonneg_left hh (show 0≤‖z‖^k*‖w‖^k by positivity)
  · simp [mixedPair,Icc_eq_empty_of_lt (by omega : j-k<k)]
    positivity

/-- Half of the support weight. Reflecting the two pole arguments gives the other half. -/
def orientedPair (j k : ℕ) (z w : ℂ) : ℂ :=
  ∑ a ∈ Icc k (j-k), ((1/(a:ℝ):ℝ):ℂ)*z^a*w^(j-a)

private theorem orientedPair_factor {j k : ℕ} (hj : 2*k≤j) (z w : ℂ) :
    orientedPair j k z w = z^k*w^k*
      abelSum (fun i ↦ 1/(k+i:ℕ)) z w (j-2*k) := by
  unfold orientedPair abelSum
  rw [← Ico_add_one_right_eq_Icc,sum_Ico_eq_sum_range,mul_sum]
  rw [show j-k+1-k=j-2*k+1 by omega]
  apply sum_congr rfl
  intro i hi
  have := mem_range.mp hi
  rw [show j-(k+i)=k+(j-2*k-i) by omega,pow_add,pow_add]
  ring

theorem mixedPair_eq_oriented {j k : ℕ} (hk : 1≤k) (hjk : k≤j) (z w : ℂ) :
    mixedPair j k z w = orientedPair j k z w + orientedPair j k w z := by
  by_cases h : 2*k≤j
  · rw [mixedPair_factor hk h,orientedPair_factor h,orientedPair_factor h]
    ring
  · simp [mixedPair,orientedPair,Icc_eq_empty_of_lt (by omega : j-k<k)]

/-- The gap-weighted bound for one orientation. -/
theorem orientedPair_gap {j k : ℕ} (hk : 1≤k) (hjk : k≤j) {z w : ℂ}
    (hz : ‖z‖≤1) (hw : ‖w‖≤1) :
    ‖z-w‖*‖orientedPair j k z w‖ ≤ 2/(k:ℝ)*‖z‖^k*‖w‖^k := by
  by_cases hj : 2*k≤j
  · let b (i : ℕ) : ℝ := 1/(k+i:ℕ)
    have hm : Antitone b := by
      intro i l hil
      exact one_div_le_one_div_of_le (by exact_mod_cast (by omega : 0<k+i))
        (by exact_mod_cast (by omega : k+i≤k+l))
    have hh := abelSum_gap b (fun i ↦ by dsimp [b]; positivity) hm hz hw (j-2*k)
    rw [show 2*b 0=2/(k:ℝ) by simp [b,div_eq_mul_inv]] at hh
    rw [←norm_mul,orientedPair_factor hj,mul_left_comm,norm_mul,norm_mul,norm_pow,norm_pow]
    simpa only [mul_assoc,mul_left_comm,mul_comm] using
      mul_le_mul_of_nonneg_left hh (show 0≤‖z‖^k*‖w‖^k by positivity)
  · simp [orientedPair,Icc_eq_empty_of_lt (by omega : j-k<k)]
    positivity

/-- Unit-label separation on the signed odd lattice supplies the factor two in hgap.
The result remains in a form valid as s tends to zero. -/
theorem orientedPair_separated {j k : ℕ} (hk : 1≤k) (hjk : k≤j) {z w : ℂ}
    (hz : ‖z‖≤1) (hw : ‖w‖≤1) (hz₀ : 0<‖z‖) (hw₀ : 0<‖w‖) {s : ℝ}
    (hgap : 2*s*‖z‖*‖w‖≤‖z-w‖) :
    s*‖orientedPair j k z w‖ ≤ 1/(k:ℝ)*‖z‖^(k-1)*‖w‖^(k-1) := by
  have h := (mul_le_mul_of_nonneg_right hgap (norm_nonneg (orientedPair j k z w))).trans
    (orientedPair_gap hk hjk hz hw)
  have powz : ‖z‖^k=‖z‖^(k-1)*‖z‖ := by rw [←pow_succ]; congr 1; omega
  have poww : ‖w‖^k=‖w‖^(k-1)*‖w‖ := by rw [←pow_succ]; congr 1; omega
  rw [powz,poww] at h
  apply le_of_mul_le_mul_left _ (show 0<2*‖z‖*‖w‖ by positivity)
  convert h using 1 <;> ring

/-- One new endpoint when the total row index increases by one. -/
theorem orientedPair_next {p k : ℕ} (hk : 1≤k) (h : 2*k≤p+1) (z w : ℂ) :
    orientedPair (p+1) k z w = w*orientedPair p k z w +
       ((1/((p+1-k:ℕ):ℝ):ℝ):ℂ)*z^(p+1-k)*w^k := by
  unfold orientedPair
  rw [show p+1-k=p-k+1 by omega,sum_Icc_succ_top (by omega : k≤p-k+1),mul_sum]
  rw [show p+1-(p-k+1)=k by omega]
  congr 1
  apply sum_congr rfl
  intro a ha
  have := (mem_Icc.mp ha).2
  rw [show p+1-a=p-a+1 by omega,pow_succ]
  ring

/-- The shared weights do not drift if the two reciprocal halves are reflected separately. -/
theorem mixedPair_centered_exact {p k : ℕ} (hk : 1≤k) (h : 2*k≤p+1) (z w c : ℂ) :
    mixedPair (p+1) k z w-c*mixedPair p k z w =
      (w-c)*orientedPair p k z w+(z-c)*orientedPair p k w z+
      ((1/((p+1-k:ℕ):ℝ):ℝ):ℂ)*(z^(p+1-k)*w^k+w^(p+1-k)*z^k) := by
  rw [mixedPair_eq_oriented hk (by omega),mixedPair_eq_oriented hk (by omega),
      orientedPair_next hk h,orientedPair_next hk h]
  ring

/-- The mixed support kernel after using the pole separation. -/
theorem mixedPair_separated {j k : ℕ} (hk : 1≤k) (hjk : k≤j) {z w : ℂ}
    (hz : ‖z‖≤1) (hw : ‖w‖≤1) (hz₀ : 0<‖z‖) (hw₀ : 0<‖w‖) {s : ℝ} (hs : 0 ≤ s)
    (hgap : 2*s*‖z‖*‖w‖≤‖z-w‖) :
    s*‖mixedPair j k z w‖ ≤ 2/(k:ℝ)*‖z‖^(k-1)*‖w‖^(k-1) := by
  have hgap' : 2*s*‖w‖*‖z‖≤‖w-z‖ := by
    rw [norm_sub_rev w z]; linear_combination hgap
  have h1 := orientedPair_separated hk hjk hz hw hz₀ hw₀ hgap
  have h2 := orientedPair_separated hk hjk hw hz hw₀ hz₀ hgap'
  rw [mixedPair_eq_oriented hk hjk]
  apply (mul_le_mul_of_nonneg_left (norm_add_le ..) hs).trans
  rw [mul_add]
  exact (add_le_add h1 h2).trans_eq (by ring)

/-- Pointwise mixed-pole bound for the neighboring-row difference. Applied at signed
odd labels, u and v are the absolute values of those labels. -/
theorem mixedPair_centered_bound {p k : ℕ} (hk : 1≤k) (h : 2*k≤p+1) {z w c : ℂ}
    (hz : ‖z‖≤1) (hw : ‖w‖≤1) (hz₀ : 0<‖z‖) (hw₀ : 0<‖w‖) {s u v : ℝ}
    (hgap : 2*s*‖z‖*‖w‖≤‖z-w‖) (hu : 0≤u) (hv : 0≤v)
    (hcz : ‖z-c‖≤u*s) (hcw : ‖w-c‖≤v*s) :
    ‖mixedPair (p+1) k z w-c*mixedPair p k z w‖ ≤
      (u+v+2)/(k:ℝ)*‖z‖^(k-1)*‖w‖^(k-1) := by
  let R := ‖z‖^(k-1)*‖w‖^(k-1)
  have hgap' : 2*s*‖w‖*‖z‖≤‖w-z‖ := by
    rw [norm_sub_rev w z]; linear_combination hgap
  have h1 := orientedPair_separated (j:=p) hk (by omega) hz hw hz₀ hw₀ hgap
  have h2 := orientedPair_separated (j:=p) hk (by omega) hw hz hw₀ hz₀ hgap'
  have e1 : ‖(w-c)*orientedPair p k z w‖ ≤ v/k*R := by
    rw [norm_mul]
    calc _ ≤ (v*s)*‖orientedPair p k z w‖ := by gcongr
         _ = v*(s*‖orientedPair p k z w‖) := by ring
         _ ≤ _ := (mul_le_mul_of_nonneg_left h1 hv).trans_eq (by dsimp [R]; ring)
  have e2 : ‖(z-c)*orientedPair p k w z‖ ≤ u/k*R := by
    rw [norm_mul]
    calc _ ≤ (u*s)*‖orientedPair p k w z‖ := by gcongr
         _ = u*(s*‖orientedPair p k w z‖) := by ring
         _ ≤ _ := (mul_le_mul_of_nonneg_left h2 hu).trans_eq (by dsimp [R]; ring)
  have posk : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have posb : (0:ℝ)<(p+1-k:ℕ) := by exact_mod_cast (show 0<p+1-k by omega)
  have hk' : (1:ℝ)/(p+1-k:ℕ)≤1/(k:ℝ) := one_div_le_one_div_of_le posk
    (by exact_mod_cast (by omega : k≤p+1-k))
  have powers (a b : ℕ) (ha : k-1≤a) (hb : k-1≤b) : ‖z^a*w^b‖≤R := by
    rw [norm_mul,norm_pow,norm_pow]
    exact mul_le_mul (pow_le_pow_of_le_one (norm_nonneg _) hz ha)
      (pow_le_pow_of_le_one (norm_nonneg _) hw hb) (by positivity) (by positivity)
  have endpoints : ‖z^(p+1-k)*w^k+w^(p+1-k)*z^k‖≤2*R := by
    rw [mul_comm (w^(p+1-k)) (z^k),two_mul]
    exact (norm_add_le ..).trans (add_le_add (powers _ _ (by omega) (by omega))
      (powers _ _ (by omega) (by omega)))
  have e3 : ‖((1/((p+1-k:ℕ):ℝ):ℝ):ℂ)*(z^(p+1-k)*w^k+w^(p+1-k)*z^k)‖≤2/k*R := by
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (by positivity)]
    exact (mul_le_mul hk' endpoints (norm_nonneg _) (by positivity)).trans_eq (by ring)
  rw [mixedPair_centered_exact hk h]
  apply (norm_add_le ..).trans
  apply (add_le_add ((norm_add_le ..).trans (add_le_add e1 e2)) e3).trans_eq
  dsimp [R]
  ring

#print axioms mixedPair_centered_bound
#print axioms mixedPair_separated
#print axioms orientedPair_separated
#print axioms mixedPair_centered_exact

#print axioms abelSum_gap
#print axioms mixedPair_gap
end LongCycleBounds.Band
