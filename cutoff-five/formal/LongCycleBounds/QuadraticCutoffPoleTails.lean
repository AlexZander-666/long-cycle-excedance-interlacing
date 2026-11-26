import LongCycleBounds.FixedCutoffMiddle
import LongCycleBounds.MarkedCompactSign

/-! Exponential decay of the nonleading poles in both the logistic coefficient
and its centered successor difference. All constants are absolute. -/
noncomputable section
namespace LongCycleBounds.QuadraticCutoff
open Real PoleTails PoleBridge Bulk Band MarkedTwo

private def remainder (f : ℝ → ℂ) := f 3 + ∑' i : ℕ, f (2*(i:ℝ)+5)

private theorem remainder_bound {B : ℝ} (hB : 0 < B) (f : ℝ → ℂ)
    (hf : ∀ l ≥ 3, ‖f l‖ ≤ l*envelope l^4*B) :
    Summable (fun i : ℕ ↦ f (2*(i:ℝ)+5)) ∧ ‖remainder f‖ < B/3 := by
  let l (i : ℕ) := 2*(i:ℝ)+5
  let M (i : ℕ) := l i * envelope (l i)^4
  have hl (i : ℕ) : 3 ≤ l i := by dsimp [l]; linarith [show (0:ℝ) ≤ i by positivity]
  have hm (i : ℕ) : 0 ≤ M i := mul_nonneg (by linarith [hl i]) (by positivity)
  have hsum (n : ℕ) : ∑ i ∈ Finset.range n, M i ≤ 2/27 := (two_tails n).1
  have sm := summable_of_sum_range_le hm hsum
  have tm := Real.tsum_le_of_sum_range_le hm hsum
  have cp (i : ℕ) : ‖f (l i)‖ ≤ M i*B := hf _ (hl i)
  have hs := Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) cp (sm.mul_right B)
  refine ⟨hs.of_norm, ?_⟩
  have hh := (norm_tsum_le_tsum_norm hs).trans (Summable.tsum_le_tsum cp hs (sm.mul_right B))
  rw [tsum_mul_right] at hh
  have h3 := hf 3 le_rfl
  norm_num [envelope] at h3
  change ‖f 3 + ∑' i, f (l i)‖ < _
  linarith [norm_add_le (f 3) (∑' i, f (l i)),mul_le_mul_of_nonneg_right tm hB.le]


/-- Separating two identical exponent halves leaves both an exponential factor
at the nearest discarded pole and a summable label-dependent fourth power. -/
theorem geometric_pole_envelope {l s m : ℝ} (hl : 3≤l) (hs : s^2≤1)
    (hm : 16≤ m) (wide : 2≤ m*s^2) :
    amplitude l s m ≤ envelope l^4 * exp (-(m*s^2)/8) := by
  let a := 1+(l^2-1)*s^2
  have high : 1+8*s^2≤a := by
    dsimp [a]
    have l2 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤3) hl 2
    nlinarith only [mul_nonneg (sq_nonneg s) (show 0≤l^2-9 by linarith only [l2])]
  have ap : 0<a := by linarith [sq_nonneg s]
  have ap' : 0<1+8*s^2 := by positivity
  have ll : s^2/2≤log a := by
    apply le_trans _ (log_le_log ap' high)
    apply le_trans _ (one_sub_inv_le_log_of_pos ap')
    rw [le_sub_comm,←one_div,div_le_iff₀ ap']
    nlinarith only [sq_nonneg s,mul_nonneg (sq_nonneg s) (sub_nonneg.mpr hs)]
  have exp_half : a^(-(m/4))≤exp (-(m*s^2)/8) := by
    rw [rpow_def_of_pos ap]
    apply exp_le_exp.mpr
    nlinarith only [mul_le_mul_of_nonneg_right ll (show 0≤ m by linarith)]
  have poly := decay_p l s (m/2) (by linarith) (by linarith) (by linarith)
  change a^(-(m/2/2))≤_ at poly
  rw [show m/2/2=m/4 by ring] at poly
  change a^(-(m/2))≤_
  rw [show -(m/2)= -(m/4) + -(m/4) by ring,rpow_add ap]
  exact mul_le_mul poly exp_half (rpow_nonneg ap.le _) (by positivity)

/-- Two bounds before taking real parts, over the positive odd half of the lattice. -/
theorem nonleading_half {c s : ℝ} {p : ℕ} (hu : c^2+s^2=1) (hs : 0<s)
    (hp : 16≤(p:ℝ)) (wide : 2≤(p:ℝ)*s^2) :
    let z := pole c s 1
    let e := exp (-((p:ℝ)*s^2)/8)
    ‖total c s p-z^p‖ < e/3 ∧
      ‖total c s (p+1)-(c:ℂ)*total c s p-z^p*(z-(c:ℂ))‖ < s*e/3 := by
  let z := pole c s
  let E := exp (-((p:ℝ)*s^2)/8)
  let F (l : ℝ) := z l^p
  let D (l : ℝ) := F l*(z l-(c:ℂ))
  have ep : 0<E := exp_pos _
  have bound (l : ℝ) (hl : 3≤l) : ‖F l‖≤envelope l^4*E := by
    rw [show F l=pole c s l^p from rfl,norm_pole_pow _ _ _ hu (by linarith)]
    exact geometric_pole_envelope hl (by nlinarith [sq_nonneg c]) hp wide
  obtain ⟨sf,bf⟩ := remainder_bound ep F (by
    intro l hl
    calc _ ≤ envelope l^4*E := bound _ hl
         _ ≤ _ := by nlinarith only [mul_nonneg (show 0≤l-1 by linarith) (mul_nonneg (show 0≤envelope l^4 by positivity) ep.le)])
  obtain ⟨sd,bd⟩ := remainder_bound (mul_pos hs ep) D (by
    intro l hl
    change ‖F l*(z l-(c:ℂ))‖ ≤ _
    rw [norm_mul]
    calc _ ≤ (envelope l^4*E)*(l*s) :=
           mul_le_mul (bound l hl) (norm_centered _ _ _ hu (by linarith) hs.le) (norm_nonneg _) (by positivity)
         _ = _ := by ring)
  have decomp : total c s (p+1) - (c:ℂ)*total c s p = D 1 + remainder D := by
    have addterm : (∑' i : ℕ, z (2*(i:ℝ)+5)^(p+1)) =
        (c:ℂ)*(∑' i : ℕ, F (2*(i:ℝ)+5)) + ∑' i : ℕ, D (2*(i:ℝ)+5) := by
      rw [← tsum_mul_left, ← (sf.mul_left (c:ℂ)).tsum_add sd]
      apply tsum_congr
      intro i
      dsimp only [D,F]
      ring
    change z 1^(p+1)+(z 3^(p+1)+∑' i : ℕ, z (2*(i:ℝ)+5)^(p+1)) -
      (c:ℂ)*(F 1+(F 3+∑' i : ℕ, F (2*(i:ℝ)+5))) = D 1 + (D 3+_)
    rw [addterm]
    dsimp only [D,F]
    ring
  refine ⟨?_,?_⟩
  · change ‖F 1+remainder F-F 1‖<E/3
    simpa using bf
  · change ‖total c s (p+1)-(c:ℂ)*total c s p-D 1‖<s*E/3
    rwa [decomp,add_sub_cancel_left]

private theorem logistic_total {n j : ℕ} (hn : 8≤(n:ℝ)) (hj : 1≤j)
    (hi : (n:ℝ)≤2*((j+1:ℕ):ℝ)) (x : ℝ) (hx : 0≤x) (ang : 1≤(n:ℝ)*(s x)^2) :
    scaledCoeff (logistic (time x)) (radius x) j=2*(total (c x) (s x) (j+1)).re := by
  rw [logistic_scaled_moment x hj]
  congr 1
  rw [time,scaledMoment_poles _ (by omega) _ _ hx]
  have he := congrArg Complex.re (complete_normalization x n (j+1) hn ang hi)
  have eq : radius x^(j+1)*(oddPoleSum (j+1) x).re=2*(total (c x) (s x) (j+1)).re := by
    simpa [Complex.mul_re,←Complex.ofReal_pow] using he
  linarith only [eq]



/-- Genuine logistic coefficient of order j and the centered successor. The
exponent p=j+1 is one larger than the Taylor order. -/
theorem logistic_nonleading {x : ℝ} (hx : 0≤x) (j : ℕ)
    (hj : 16≤((j+1:ℕ):ℝ)) (wide : 2≤((j+1:ℕ):ℝ)*(s x)^2) :
    let V := scaledCoeff (logistic (time x)) (radius x)
    let z := compactRotation x
    let e := exp (-(((j+1:ℕ):ℝ)*(s x)^2)/8)
    |V j-2*(z^(j+1)).re| < 2*e/3 ∧
      |V (j+1)-c x*V j-2*(z^(j+1)*(z-(c x:ℂ))).re| < 2*s x*e/3 := by
  have hjn : 16≤j+1 := by exact_mod_cast hj
  have jpos : 1≤j := by omega
  have hh := nonleading_half (p:=j+1) (circle x) (div_pos pi_pos (radius_pos x)) hj wide
  have e1 := logistic_total (n:=j+1) (by linarith) jpos (by push_cast;linarith) x hx (by linarith)
  have e2 := logistic_total (n:=j+1) (j:=j+1) (by linarith) (by omega) (by push_cast;linarith) x hx (by linarith)
  have same : pole (c x) (s x) 1=compactRotation x := pole_den x 1 le_rfl
  dsimp only
  rw [e1,e2]
  simp only [same] at hh
  have v := (Complex.abs_re_le_norm _).trans_lt hh.1
  have c' := (Complex.abs_re_le_norm _).trans_lt hh.2
  simp only [Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at v c' ⊢
  constructor
  · rw [show ∀ a b : ℝ, 2*a-2*b=2*(a-b) by intro a b;ring,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
    linarith only [v]
  · rw [show ∀ a b c d f : ℝ, 2*a-b*(2*c)-2*(d-f)=2*(a-b*c-(d-f)) by intros;ring,
      abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
    linarith only [c']

#print axioms geometric_pole_envelope
#print axioms nonleading_half
#print axioms logistic_nonleading
end LongCycleBounds.QuadraticCutoff
