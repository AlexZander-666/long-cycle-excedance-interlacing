import LongCycleBounds.MixedAbel
import LongCycleBounds.PoleTails

/-! The signed odd pole indexing and the constants in the mixed Abel bounds. -/
noncomputable section
namespace LongCycleBounds.Band
open PoleTails ComplexConjugate

private theorem pole_conj_negative (c s l : ℝ) :
    pole c s (-l) = conj (pole c s l) := by
  apply Complex.ext <;> simp [pole]
  ring

private theorem signed_polar {c s l : ℝ} (hc : c^2+s^2=1) (hl : 1 ≤ |l|) :
    pole c s l * ((c:ℂ) + ((l*s:ℝ):ℂ)*Complex.I) = 1 := by
  have hL : 0 ≤ l^2-1 := by nlinarith [sq_abs l, sq_nonneg (|l|-1)]
  have hd : 0<1+(l^2-1)*s^2 := by positivity
  apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im,pole] <;> field_simp <;> nlinarith [hc]

/-- Signed resolvent difference; valid also for antipodal labels such as 1 and -1. -/
theorem signed_pole_difference {c s l m : ℝ} (hc : c^2+s^2=1) (hl : 1 ≤ |l|) (hm : 1 ≤ |m|) :
    pole c s l - pole c s m =
      Complex.I*((m-l)*s:ℝ)*pole c s l*pole c s m := by
  let z := pole c s l
  let w := pole c s m
  let A := (c:ℂ) + ((l*s:ℝ):ℂ)*Complex.I
  let B := (c:ℂ) + ((m*s:ℝ):ℂ)*Complex.I
  have hA : z*A=1 := signed_polar hc hl
  have hB : w*B=1 := signed_polar hc hm
  calc z-w = z*(w*B)-w*(z*A) := by rw [hA,hB]; ring
       _ = _ := by dsimp only [A,B,z,w]; push_cast; ring

theorem signed_pole_norms {c s l : ℝ} (hc : c^2+s^2=1) (hs : 0  ≤  s) (hl : 1 ≤ |l|) :
    0<‖pole c s l‖ ∧ ‖pole c s l‖ ≤ 1 ∧ ‖pole c s l-(c:ℂ)‖ ≤ |l| * s := by
  have positive (r : ℝ) (hr : 1 ≤ r) :
      0<‖pole c s r‖ ∧ ‖pole c s r‖ ≤ 1 ∧ ‖pole c s r-(c:ℂ)‖ ≤ r*s := by
    have sq := norm_pole_sq c s r hc hr
    have ds : 0 ≤ (r^2-1)*s^2 := mul_nonneg (by nlinarith [sq_nonneg (r-1)]) (sq_nonneg s)
    have hp : 0<1/(1+(r^2-1)*s^2) := by positivity
    have hle : 1/(1+(r^2-1)*s^2) ≤ 1 := (div_le_one (by linarith)).2 (by linarith)
    exact ⟨by nlinarith [norm_nonneg (pole c s r)],by nlinarith [norm_nonneg (pole c s r)],
      norm_centered c s r hc hr hs⟩
  rcases le_or_gt 0 l with hp|hn
  · rw [abs_of_nonneg hp] at hl ⊢
    exact positive l hl
  · rw [abs_of_neg hn] at hl ⊢
    have h := positive (-l) hl
    rw [pole_conj_negative,Complex.norm_conj] at h
    have he : conj (pole c s l) - (c:ℂ) = conj (pole c s l - (c:ℂ)) := by
      rw [map_sub,Complex.conj_ofReal]
    rwa [he,Complex.norm_conj] at h

private theorem odd_absolute (i : ℤ) : 1 ≤ |2*(i:ℝ)+1| := by
  rcases le_or_gt 0 i with hi|hi
  · have : (0:ℝ) ≤ i := by exact_mod_cast hi
    rw [abs_of_nonneg (by linarith)]
    linarith
  · have : (i:ℝ) ≤ -1 := by exact_mod_cast (by omega : i ≤  -1)
    rw [abs_of_neg (by linarith)]
    linarith

private theorem odd_spacing {i j : ℤ} (ne : i≠j) : 2 ≤ |(2*(j:ℝ)+1)-(2*(i:ℝ)+1)| := by
  rcases lt_or_gt_of_ne ne with h|h
  · have : (i:ℝ)+1 ≤ j := by exact_mod_cast (by omega : i+1 ≤ j)
    rw [abs_of_nonneg (by linarith)]
    linarith
  · have : (j:ℝ)+1 ≤ i := by exact_mod_cast (by omega : j+1 ≤ i)
    rw [abs_of_neg (by linarith)]
    linarith

/-- Inputs for the two transfer inequalities at the same signed odd labels as PoleBridge. -/
theorem signed_odd_gap {c s : ℝ} (hc : c^2+s^2=1) (hs : 0  ≤  s) {i j : ℤ} (ne : i≠j) :
    let z := pole c s (2*(i:ℝ)+1)
    let w := pole c s (2*(j:ℝ)+1)
    2*s*‖z‖*‖w‖  ≤  ‖z-w‖ := by
  dsimp only
  rw [signed_pole_difference hc (odd_absolute i) (odd_absolute j)]
  simp only [norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hs]
  gcongr
  exact odd_spacing ne

/-- The finite off-diagonal part of the adjacent centered interaction, with genuine
signed poles and absolute signed labels in the majorant. -/
theorem signed_odd_mixed_centered {p k : ℕ} (hk : 1 ≤ k) (hp : 2*k ≤ p+1)
    {c s : ℝ} (hc : c^2+s^2=1) (hs : 0  ≤  s) {i j : ℤ} (ne : i≠j) :
    let l := 2*(i:ℝ)+1
    let m := 2*(j:ℝ)+1
    let z := pole c s l
    let w := pole c s m
    ‖mixedPair (p+1) k z w-(c:ℂ)*mixedPair p k z w‖  ≤ 
      (|l|+|m|+2)/(k:ℝ)*‖z‖^(k-1)*‖w‖^(k-1) := by
  obtain ⟨hz,hzu,hzc⟩ := signed_pole_norms hc hs (odd_absolute i)
  obtain ⟨hw,hwu,hwc⟩ := signed_pole_norms hc hs (odd_absolute j)
  exact mixedPair_centered_bound hk hp hzu hwu hz hw (signed_odd_gap hc hs ne)
    (abs_nonneg _) (abs_nonneg _) hzc hwc

theorem signed_odd_mixed_size {p k : ℕ} (hk : 1 ≤ k) (hp : k ≤ p)
    {c s : ℝ} (hc : c^2+s^2=1) (hs : 0  ≤  s) {i j : ℤ} (ne : i≠j) :
    let z := pole c s (2*(i:ℝ)+1)
    let w := pole c s (2*(j:ℝ)+1)
    s*‖mixedPair p k z w‖  ≤  2/(k:ℝ)*‖z‖^(k-1)*‖w‖^(k-1) := by
  obtain ⟨hz,hzu,_⟩ := signed_pole_norms hc hs (odd_absolute i)
  obtain ⟨hw,hwu,_⟩ := signed_pole_norms hc hs (odd_absolute j)
  exact mixedPair_separated hk hp hzu hwu hz hw hs (signed_odd_gap hc hs ne)

#print axioms signed_pole_difference
#print axioms signed_odd_gap
#print axioms signed_odd_mixed_size
#print axioms signed_odd_mixed_centered
end LongCycleBounds.Band
