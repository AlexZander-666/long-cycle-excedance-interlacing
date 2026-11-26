import LongCycleBounds.HigherMixedAbel
import LongCycleBounds.PoleBridge
import LongCycleBounds.FullStripPoleExpansion
import Mathlib.Analysis.Real.Pi.Bounds

/-! Signed pole masses for every fixed aspect ratio in the central region. -/
noncomputable section
namespace LongCycleBounds.Band
open PoleTails PoleBridge Real Finset

private def den (C u : ℝ) := 1+u*(u+1)/(2*C)

private theorem den_pos {C u : ℝ} (hC : 0<C) (hu : 0≤u) : 0<den C u := by
  unfold den; positivity

private theorem power_majorant {C c s : ℝ} (hC : 0<C) {q : ℕ} (hq : 4≤q)
    (hc : c^2+s^2=1) (ha : 1 ≤ 2*C*(q:ℝ)*s^2) {u : ℝ} (hu : 0≤u) :
    ‖pole c s (2*u+1)‖^q ≤ (1/den C u)^2 := by
  let v := ((2*u+1)^2-1)*s^2
  have vpos : 0≤v := mul_nonneg (by nlinarith [sq_nonneg u]) (sq_nonneg s)
  have vp : 0<1+v := by linarith
  have bern := one_add_mul_self_le_rpow_one_add (by linarith : -1≤v)
    (by exact_mod_cast (show 1≤(q:ℝ)/4 by exact (le_div_iff₀ (by norm_num)).2 (by exact_mod_cast hq)))
  have step : den C u ≤ (1+v)^((q:ℝ)/4) := by
    apply le_trans _ bern
    unfold den
    dsimp only [v]
    rw [add_le_add_iff_left, div_le_iff₀ (by positivity : 0<2*C)]
    nlinarith only [mul_nonneg (mul_nonneg hu (by linarith : 0≤u+1)) (sub_nonneg.mpr ha)]
  have inv := one_div_le_one_div_of_le (den_pos hC hu) step
  rw [one_div,←Real.rpow_neg_one, ←Real.rpow_mul vp.le] at inv
  have pow2 := pow_le_pow_left₀ (Real.rpow_nonneg vp.le _) inv 2
  rw [←Real.rpow_natCast,←Real.rpow_mul vp.le] at pow2
  rw [←norm_pow,norm_pole_pow _ _ _ hc (by linarith) q]
  change (1+v)^(-((q:ℝ)/2)) ≤ _
  rw [show -((q:ℝ)/2) = ((q:ℝ)/4*(-1))*((2:ℕ):ℝ) by push_cast; ring]
  exact pow2

private theorem positive_mass_steps {C u : ℝ} (hC : 0<C) (hu : 0≤u) :
    (1/den C (u+1))^2 ≤ 2*C/(sqrt C+u)-2*C/(sqrt C+(u+1)) ∧
    (2*(u+1)+1)*(1/den C (u+1))^2 ≤ 3*C/den C u-3*C/den C (u+1) := by
  have r₀ := sqrt_pos_of_pos hC
  have r₂ := sq_sqrt hC.le
  have d₀ := den_pos hC hu
  have d₁ := den_pos hC (by linarith : 0≤u+1)
  have inc : (den C (u+1)-den C u)*C=u+1 := by unfold den; field_simp; ring
  have dstep : den C u ≤ den C (u+1) := by nlinarith
  have dl : (u+1)^2 ≤ 2*C*(den C (u+1)-1) := by
    unfold den
    field_simp
    nlinarith
  have dge : 1≤den C (u+1) := by unfold den; linarith [show 0 ≤ (u+1)*(u+1+1)/(2*C) by positivity]
  have major : (sqrt C+(u+1))^2 ≤ 2*C*(den C (u+1))^2 := by
    have e := mul_nonneg hC.le (sq_nonneg (den C (u+1)-1))
    nlinarith only [e,dl,r₂,sq_nonneg (sqrt C-(u+1)),mul_nonneg hC.le (sub_nonneg.mpr dge)]
  constructor
  · rw [div_sub_div _ _ (by positivity : sqrt C+u ≠ 0) (by positivity : sqrt C+(u+1) ≠ 0)]
    rw [div_pow,one_pow,div_le_div_iff₀ (sq_pos_of_pos d₁) (by positivity)]
    nlinarith only [major,show (0:ℝ) ≤ sqrt C+u+1 by positivity]
  · rw [div_sub_div _ _ d₀.ne' d₁.ne',div_pow,one_pow,←mul_div_assoc,mul_one,
      div_le_div_iff₀ (sq_pos_of_pos d₁) (by positivity)]
    have a : (2*(u+1)+1)*den C u ≤ 3*(u+1)*den C (u+1) :=
      mul_le_mul (by linarith) dstep d₀.le (by positivity)
    rw [show 3*C*den C (u+1)-den C u*(3*C)=3*(u+1) by linear_combination 3*inc]
    nlinarith only [mul_le_mul_of_nonneg_right a d₁.le]

private theorem mass_of_drop (f F : ℕ → ℝ) (hpos : ∀ i, 0 ≤ f i)
    (hF : ∀ i, 0 ≤ F i) (head : f 0≤1) (tail : ∀ i, f (i+1) ≤ F i-F (i+1)) :
    Summable f ∧ (∑' i, f i) ≤ 1+F 0 := by
  have bound (n : ℕ) : (∑ i ∈ range n, f i) ≤ 1+F 0 := by
    cases n with
    | zero => simp; linarith [hF 0]
    | succ n =>
      rw [sum_range_succ']
      have hh := sum_le_sum (s:=range n) (fun i _ ↦ tail i)
      rw [sum_range_sub' F n] at hh
      linarith [hF n]
  exact ⟨summable_of_sum_range_le hpos bound,Real.tsum_le_of_sum_range_le hpos bound⟩

private theorem both_halves (f : ℤ → ℝ) (a : ℕ → ℝ) {b : ℝ}
    (hp : ∀ i : ℕ, f i=a i) (hn : ∀ i : ℕ, f (-(i+1:ℤ))=a i)
    (h : Summable a ∧ (∑' i, a i) ≤ b) : Summable f ∧ (∑' i, f i) ≤ 2*b := by
  have s := Summable.of_nat_of_neg_add_one (f:=f) (by simpa only [hp] using h.1)
    (by simpa only [hn] using h.1)
  refine ⟨s,?_⟩
  rw [←tsum_nat_add_neg_add_one s]
  simp only [hp,hn,h.1.tsum_add h.1]
  linarith [h.2]

/-- Mass and first absolute label moment on the entire signed odd lattice. -/
theorem fixed_signed_pole_mass {C c s : ℝ} (hC : 0<C) {q : ℕ} (hq : 4≤q)
    (hc : c^2+s^2=1) (ha : 1≤2*C*(q:ℝ)*s^2) :
    let l := fun i : ℤ ↦ 2*(i:ℝ)+1
    let v := fun i ↦ ‖signedOddPole c s i‖^q
    Summable v ∧ Summable (fun i ↦ |l i| * v i) ∧
      (∑' i, v i) ≤ 2+4*sqrt C ∧ (∑' i, |l i| * v i) ≤ 2+6*C := by
  dsimp only
  let l (i : ℤ) := 2*(i:ℝ)+1
  let f (i : ℤ) := ‖signedOddPole c s i‖^q
  have flip (i : ℕ) : l (-(i+1:ℤ)) = -l i := by dsimp [l]; push_cast; ring
  have lpos (i : ℕ) : 0≤l i := by dsimp [l]; push_cast; positivity
  have flipf (i : ℕ) : f (-(i+1:ℤ)) = f i := by
    change ‖pole c s (l (-(i+1:ℤ)))‖^q=‖pole c s (l i)‖^q
    have conj (r : ℝ) : pole c s (-r)=star (pole c s r) := by
      apply Complex.ext <;> simp [pole]; ring
    rw [flip,conj,norm_star]
  have base (i : ℕ) : f i ≤ (1/den C i)^2 := by
    simpa only [f,signedOddPole,Int.cast_natCast] using power_majorant hC hq hc ha (u:=i) (by positivity)
  have head : f 0 ≤ 1 := by simpa only [Nat.cast_zero,den,zero_mul,zero_div,add_zero,div_one,one_pow] using base 0
  have a := mass_of_drop (fun i : ℕ ↦ f i) (fun i : ℕ ↦ 2*C/(sqrt C+i))
    (fun _ ↦ by dsimp [f]; positivity) (fun _ ↦ by positivity) head (fun i ↦ by
      have h := positive_mass_steps hC (u:=i) (by positivity)
      simpa only [Nat.cast_add_one] using (base (i+1)).trans (by simpa only [Nat.cast_add_one] using h.1))
  have w := mass_of_drop (fun i : ℕ ↦ l i*f i) (fun i : ℕ ↦ 3*C/den C i)
    (fun i ↦ mul_nonneg (lpos i) (by dsimp [f]; positivity))
    (fun i ↦ div_nonneg (by positivity) (den_pos hC (by positivity)).le)
    (by simpa only [Nat.cast_zero,l,Int.cast_zero,mul_zero,zero_add,one_mul] using head)
    (fun i ↦ by
      have b := mul_le_mul_of_nonneg_left (base (i+1)) (lpos (i+1))
      have h := positive_mass_steps hC (u:=i) (by positivity)
      dsimp only [l] at b ⊢
      push_cast at b ⊢
      exact b.trans h.2)
  have a' := both_halves f (fun i : ℕ ↦ f i) (fun _ ↦ rfl) flipf a
  have w' := both_halves (fun i ↦ |l i| * f i) (fun i : ℕ ↦ l i*f i)
    (fun i ↦ by rw [abs_of_nonneg (lpos i)])
    (fun i ↦ by rw [flip,abs_neg,abs_of_nonneg (lpos i),flipf]) w
  have rat : 2*C/sqrt C=2*sqrt C := by
    rw [div_eq_iff (sqrt_pos_of_pos hC).ne']; nlinarith [sq_sqrt hC.le]
  refine ⟨a'.1,w'.1,a'.2.trans_eq ?_,w'.2.trans_eq ?_⟩
  · simp only [Nat.cast_zero,add_zero,rat]; ring
  · simp only [Nat.cast_zero,den,zero_mul,zero_div,add_zero,div_one]; ring

/-- The predecessor angle retains its full order even when the low-order mass uses C. -/
theorem fixed_central_angle {n : ℕ} (hn : 2≤n) (x : ℝ) (hx : 0 ≤ x)
    (upper : x≤3*sqrt (n-2:ℕ)) : 1≤((n-1:ℕ):ℝ)*(s x)^2 := by
  have r : radius x^2=x^2+π^2 := sq_sqrt (by positivity)
  have sq := mul_self_le_mul_self hx upper
  have rs := sq_sqrt (show 0≤((n-2:ℕ):ℝ) by positivity)
  rw [Nat.cast_sub hn] at sq rs
  have nr : 2 ≤ (n:ℝ) := by exact_mod_cast hn
  have bpi : 9≤π^2 := by nlinarith [pi_gt_three,sq_nonneg (π-3)]
  unfold s
  rw [div_pow,←mul_div_assoc,le_div_iff₀ (sq_pos_of_pos (radius_pos x)),one_mul,r,
    Nat.cast_sub (by omega : 1≤n)]
  norm_num at sq rs ⊢
  nlinarith only [sq,rs,mul_nonneg (sub_nonneg.mpr nr) (sub_nonneg.mpr bpi)]

/-- Actual central phase for every higher-cycle slice (and every larger exponent). -/
theorem fixed_central_signed_pole_mass {C : ℝ} (hC : 0<C) {n k q : ℕ}
    (hn : 2≤n) (hk : 2≤k) (hwidth : (n:ℝ)≤C*k) (hq : k-1≤q) (hq4 : 4≤q)
    (x : ℝ) (hx : 0 ≤ x) (upper : x≤3*sqrt (n-2:ℕ)) :
    let l := fun i : ℤ ↦ 2*(i:ℝ)+1
    let v := fun i ↦ ‖signedOddPole (c x) (s x) i‖^q
    Summable v ∧ Summable (fun i ↦ |l i| * v i) ∧
      (∑' i, v i) ≤ 2+4*sqrt C ∧ (∑' i, |l i| * v i) ≤ 2+6*C := by
  apply fixed_signed_pole_mass hC hq4 (circle x)
  have width := mul_le_mul_of_nonneg_left
    (show (k:ℝ) ≤ 2*(q:ℝ) by exact_mod_cast (show k≤2*q by omega)) hC.le
  apply (fixed_central_angle hn x hx upper).trans
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  rw [Nat.cast_sub (by omega : 1≤n)]
  linarith

#print axioms fixed_signed_pole_mass
#print axioms fixed_central_angle
#print axioms fixed_central_signed_pole_mass
private theorem cubic_weight_bound {C c s l : ℝ} (hC : 0<C) (hc : c^2+s^2=1)
    (ha : 1≤4*C*s^2) (hl : 1≤l) : l*‖pole c s l‖^3 ≤ 8*C*sqrt C/l^2 := by
  have lpos : 0<l := by linarith
  let d := 1+(l^2-1)*s^2
  have ds : 0 ≤ (l^2-1)*s^2 := mul_nonneg (by nlinarith [sq_nonneg (l-1)]) (sq_nonneg s)
  have dp : 0<d := by dsimp [d]; linarith
  have hd : l^2 ≤ 4*C*d := by
    dsimp only [d]
    nlinarith only [mul_nonneg (sq_nonneg l) (sub_nonneg.mpr ha),
      mul_nonneg hC.le (sq_nonneg c),hc,
      show C*c^2+C*s^2=C by linear_combination C*hc]
  have a := (norm_pole_sq c s l hc hl)
  change ‖pole c s l‖^2 = 1/d at a
  have b : (l*‖pole c s l‖)^2 ≤ (2*sqrt C)^2 := by
    rw [mul_pow,a,←mul_div_assoc,mul_one,div_le_iff₀ dp]
    nlinarith only [hd, sq_sqrt hC.le, show C*d=(sqrt C)^2*d by rw [sq_sqrt hC.le]]
  have e := (sq_le_sq₀ (mul_nonneg lpos.le (norm_nonneg _)) (by positivity)).mp b
  have cub := pow_le_pow_left₀ (mul_nonneg lpos.le (norm_nonneg _)) e 3
  rw [le_div_iff₀ (sq_pos_of_pos lpos)]
  nlinarith only [cub, show (sqrt C)^3=C*sqrt C by rw [pow_succ,sq_sqrt hC.le]]

/-- Endpoint order three, where the weighted tail barely has two powers of summability. -/
theorem fixed_signed_pole_mass_three {C c s : ℝ} (hC : 0<C) (hc : c^2+s^2=1)
    (ha : 1≤4*C*s^2) :
    let l := fun i : ℤ ↦ 2*(i:ℝ)+1
    let v := fun i ↦ ‖signedOddPole c s i‖^3
    Summable v ∧ Summable (fun i ↦ |l i| * v i) ∧
      (∑' i, v i) ≤ 2+4*C*sqrt C ∧ (∑' i, |l i| * v i) ≤ 2+4*C*sqrt C := by
  let l (i : ℤ) := 2*(i:ℝ)+1
  let f (i : ℤ) := ‖signedOddPole c s i‖^3
  let F (r : ℕ) := 2*C*sqrt C / ((r:ℝ)+1)
  have lp (i : ℕ) : 1 ≤ l i := by dsimp [l]; push_cast; linarith [show (0:ℝ) ≤ i by positivity]
  have fn (i : ℤ) : 0 ≤ f i := by dsimp [f]; positivity
  have wp := mass_of_drop (fun i : ℕ ↦ l i*f i) F (fun i ↦ mul_nonneg (by linarith [lp i]) (fn _))
    (fun i ↦ by dsimp [F]; positivity)
  have head : l (0:ℕ)*f (0:ℕ) ≤ 1 := by
    have h := norm_pole_sq c s 1 hc le_rfl
    norm_num at h
    have h1 : ‖pole c s 1‖=1 := by rcases h with a|a; exact a; linarith [norm_nonneg (pole c s 1)]
    norm_num [l,f,signedOddPole,h1]
  have bound := wp head (fun i ↦ by
    let u : ℝ := i
    have hu : 0≤u := by dsimp [u]; positivity
    have lc : l (i+1:ℕ) = 2*u+3 := by dsimp [l,u]; push_cast; ring
    change l (i+1:ℕ)*‖pole c s (l (i+1:ℕ))‖^3 ≤ _
    rw [lc]
    refine (cubic_weight_bound hC hc ha (by linarith : 1≤2*u+3)).trans ?_
    change _ ≤ 2*C*sqrt C/(u+1)-2*C*sqrt C/((i+1:ℕ)+1:ℝ)
    rw [Nat.cast_add_one]
    change _ ≤ 2*C*sqrt C/(u+1)-2*C*sqrt C/(u+1+1)
    rw [div_sub_div _ _ (by positivity : u+1 ≠ 0) (by positivity : u+1+1 ≠ 0),
      div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith only [mul_nonneg hC.le (sqrt_nonneg C)])
  have flip (i : ℕ) : l (-(i+1:ℤ)) = -l i := by dsimp [l]; push_cast; ring
  have flipf (i : ℕ) : f (-(i+1:ℤ))=f i := by
    change ‖pole c s (l (-(i+1:ℤ)))‖^3=‖pole c s (l i)‖^3
    have cn (r : ℝ) : pole c s (-r)=star (pole c s r) := by
      apply Complex.ext <;> simp [pole]; ring
    rw [flip,cn,norm_star]
  have w := both_halves (fun i ↦ |l i| * f i) (fun i : ℕ ↦ l i*f i)
    (fun i ↦ by rw [abs_of_nonneg (by linarith [lp i])])
    (fun i ↦ by rw [flip,abs_neg,abs_of_nonneg (by linarith [lp i]),flipf]) bound
  have below (i : ℕ) : f i ≤ l i*f i := le_mul_of_one_le_left (fn _) (lp i)
  have su := Summable.of_nonneg_of_le (fun i : ℕ ↦ fn i) below bound.1
  have a := both_halves f (fun i : ℕ ↦ f i) (fun _ ↦ rfl) flipf
    ⟨su,(su.tsum_le_tsum below bound.1).trans bound.2⟩
  exact ⟨a.1,w.1,a.2.trans_eq (by norm_num [F];ring),w.2.trans_eq (by norm_num [F];ring)⟩

/-- Every admissible low order, including q=3. For q≥4 the preceding theorem is sharper. -/
theorem fixed_central_pole_mass_all {C : ℝ} (hC : 4≤C) {n k q : ℕ}
    (hn : 2≤n) (hk : 2≤k) (hwidth : (n:ℝ)≤C*k) (hq : k-1≤q) (hq3 : 3≤q)
    (x : ℝ) (hx : 0 ≤ x) (upper : x≤3*sqrt (n-2:ℕ)) :
    let l := fun i : ℤ ↦ 2*(i:ℝ)+1
    let v := fun i ↦ ‖signedOddPole (c x) (s x) i‖^q
    Summable v ∧ Summable (fun i ↦ |l i| * v i) ∧
      (∑' i, v i) ≤ 2+4*C*sqrt C ∧ (∑' i, |l i| * v i) ≤ 2+4*C*sqrt C := by
  have cp : 0<C := by linarith
  rcases eq_or_lt_of_le hq3 with h|h
  · subst q
    apply fixed_signed_pole_mass_three cp (circle x)
    apply (fixed_central_angle hn x hx upper).trans
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    rw [Nat.cast_sub (by omega : 1≤n)]
    have hk4 : (k:ℝ) ≤ 4 := by exact_mod_cast (show k≤4 by omega)
    nlinarith [mul_le_mul_of_nonneg_left hk4 cp.le]
  · obtain ⟨s₀,s₁,a,b⟩ := fixed_central_signed_pole_mass cp hn hk hwidth hq (by omega) x hx upper
    have sr : 2 ≤ sqrt C := (le_sqrt (by norm_num) cp.le).mpr (by linarith)
    exact ⟨s₀,s₁,a.trans (by nlinarith [mul_nonneg (by linarith : 0≤C-1) (sqrt_nonneg C)]),
      b.trans (by nlinarith [mul_le_mul_of_nonneg_left sr cp.le])⟩

#print axioms fixed_signed_pole_mass_three
#print axioms fixed_central_pole_mass_all
/-- The same column majorant controls every actual scaled Eulerian moment. -/
theorem fixed_central_scaledMoment {C : ℝ} (hC : 0<C) {n k q : ℕ}
    (hn : 2≤n) (hk : 2≤k) (hwidth : (n:ℝ)≤C*k) (hq : k-1≤q) (hq4 : 4≤q)
    (x : ℝ) (hx : 0 ≤ x) (upper : x≤3*sqrt (n-2:ℕ)) :
    |scaledMoment (radius x) (-exp (-x)) q| ≤ 1+2*sqrt C := by
  obtain ⟨sm,_,mass,_⟩ := fixed_central_signed_pole_mass hC hn hk hwidth hq hq4 x hx upper
  simp_rw [←norm_pow] at sm mass
  have est := (norm_tsum_le_tsum_norm sm).trans mass
  rw [signed_odd_pole_tsum x hx (by omega : 2≤q),norm_mul] at est
  simp only [Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs] at est
  linarith only [est]

#print axioms fixed_central_scaledMoment
end LongCycleBounds.Band
