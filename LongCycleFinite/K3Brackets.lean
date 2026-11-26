import LongCycleFinite.Assembly

/-! A dyadic checker for independent gamma brackets from two adjacent rows. -/

namespace LongCycleFinite.K3

open Polynomial

def bracketAt (ws : List Window) (i : ℕ) : Window := ws[i]?.getD default

/-- Directed rounding normally suffices. The exact check handles any inconclusive endpoint. -/
def endpointOK (negative : Bool) (cs : List ℤ) (x : Dyadic) : Bool :=
  roundedSign negative cs x || positiveAt negative cs x

def rowSigns (cs : List ℤ) (ws : List Window) : Bool :=
  (List.range ws.length).all fun i ↦
    let w := bracketAt ws i
    let negative := negativeSign (ws.length - i)
    endpointOK negative cs w.left && endpointOK (!negative) cs w.right

def rowOK (d : ℕ) (cs : List ℤ) (outer : Dyadic) (ws : List Window) : Bool :=
  decide (cs.length = d + 1 ∧ ws.length = d) &&
    endpointOK false cs Dyadic.zero && orderOK outer ws && rowSigns cs ws

/-- For the even new row, a new root is strictly on each side of every old root. -/
def extraOrder (old new : List Window) : Bool :=
  (List.range old.length).all fun i ↦
    (bracketAt new i).right.less (bracketAt old i).left &&
      (bracketAt old i).right.less (bracketAt new (i + 1)).left

/-- For the odd new row, the old gamma roots start the alternating sequence. -/
def equalOrder (old new : List Window) : Bool :=
  (List.range old.length).all fun i ↦
    (bracketAt old i).right.less (bracketAt new i).left &&
      (if i + 1 < old.length then
        (bracketAt new i).right.less (bracketAt old (i + 1)).left else true)

noncomputable section

private theorem endpointOK_sound {negative : Bool} {cs : List ℤ} {x : Dyadic}
    (h : endpointOK negative cs x = true) : HasSign negative ((ofCoeffs cs).eval x.value) := by
  rcases Bool.or_eq_true_iff.mp h with hn | hn
  · exact roundedSign_sound negative cs x hn
  · exact (positiveAt_iff negative cs x).mp hn

private theorem product_negative {negative : Bool} {x y : ℝ}
    (ha : HasSign negative x) (hb : HasSign (!negative) y) : x * y < 0 := by
  cases negative
  · exact mul_neg_of_pos_of_neg ha hb
  · exact mul_neg_of_neg_of_pos ha hb

private theorem bracketAt_eq_get (ws : List Window) (i : Fin ws.length) :
    bracketAt ws i.val = ws.get i := by
  simp [bracketAt]

structure LocatedRoots (cs : List ℤ) (ws : List Window) (d : ℕ) where
  points : Fin d → ℝ
  length_eq : cs.length = d + 1
  windows_eq : ws.length = d
  pos_zero : 0 < (ofCoeffs cs).eval 0
  strictMono : StrictMono points
  negative : ∀ i, points i < 0
  zeroes : ∀ i, (ofCoeffs cs).eval (points i) = 0
  located : ∀ i, (bracketAt ws i.val).left.value < points i ∧
    points i < (bracketAt ws i.val).right.value

/-- Each validated bracket contains a root. The separate degree bound later makes
these all the roots and excludes multiplicities. -/
theorem locatedRoots_of_rowOK {d : ℕ} {cs : List ℤ} {outer : Dyadic} {ws : List Window}
    (h : rowOK d cs outer ws = true) : Nonempty (LocatedRoots cs ws d) := by
  have hc : (((cs.length = d + 1 ∧ ws.length = d) ∧ endpointOK false cs Dyadic.zero = true) ∧
      orderOK outer ws = true) ∧ rowSigns cs ws = true := by
    simpa only [rowOK, Bool.and_eq_true_iff, decide_eq_true_eq] using h
  obtain ⟨⟨⟨⟨hl, hw⟩, hz⟩, ho⟩, hs⟩ := hc
  subst d
  have hz₀ : 0 < (ofCoeffs cs).eval 0 := by
    simpa only [HasSign, Bool.false_eq_true, ↓reduceIte, Dyadic.value_zero] using endpointOK_sound hz
  obtain ⟨_, win, ordered⟩ := orderOK_between ho
  have flip (i : Fin ws.length) :
      (ofCoeffs cs).eval (ws.get i).left.value * (ofCoeffs cs).eval (ws.get i).right.value < 0 := by
    have hsi := List.all_eq_true.mp hs i.val (List.mem_range.mpr i.isLt)
    rw [bracketAt_eq_get ws i] at hsi
    obtain ⟨hleft, hright⟩ := Bool.and_eq_true_iff.mp hsi
    exact product_negative (endpointOK_sound hleft) (endpointOK_sound hright)
  choose r hr using fun i ↦ root_between (ofCoeffs cs) (win i).2.1 (flip i)
  refine ⟨⟨r, hl, rfl, hz₀, fun i j hij ↦
    (hr i).2.1.trans ((ordered i j hij).trans (hr j).1),
    fun i ↦ (hr i).2.1.trans (win i).2.2, fun i ↦ (hr i).2.2, ?_⟩⟩
  intro i
  rw [bracketAt_eq_get ws i]
  exact ⟨(hr i).1, (hr i).2.1⟩

private theorem LocatedRoots.factor {cs : List ℤ} {ws : List Window} {d : ℕ}
    (r : LocatedRoots cs ws d) :
    ofCoeffs cs = C (ofCoeffs cs).leadingCoeff * ∏ i, (X - C (r.points i)) :=
  factor_of_degree_bound r.points (by intro h; simpa [h] using r.pos_zero)
    ((ofCoeffs_degree_le cs).trans (by rw [r.length_eq]; omega))
    r.strictMono.injective r.zeroes

private theorem LocatedRoots.leadingCoeff_ne_zero {cs : List ℤ} {ws : List Window} {d : ℕ}
    (r : LocatedRoots cs ws d) : (ofCoeffs cs).leadingCoeff ≠ 0 :=
  Polynomial.leadingCoeff_ne_zero.mpr (by intro h; simpa [h] using r.pos_zero)

/-- The checked even case reuses the strict gamma interlacing lift. -/
theorem checked_even {p q : List ℤ} {wp wq : List Window} {outerP outerQ : Dyadic} {d : ℕ}
    (hp : rowOK d p outerP wp = true) (hq : rowOK (d+1) q outerQ wq = true)
    (ho : extraOrder wp wq = true) :
    StrictNegativeInterlacing (expandGamma (d+d+1) p) (expandGamma (d+d+1+1) q) (d+d+1) := by
  obtain ⟨r⟩ := locatedRoots_of_rowOK hp
  obtain ⟨s⟩ := locatedRoots_of_rowOK hq
  apply expandGamma_interlacing r.length_eq s.length_eq
  refine ⟨r.points, s.points, r.leadingCoeff_ne_zero, s.leadingCoeff_ne_zero, r.factor,
    s.factor, r.strictMono, s.strictMono, r.negative, s.negative, ?_⟩
  intro i
  have hi : i.val < wp.length := by rw [r.windows_eq]; exact i.isLt
  have he := List.all_eq_true.mp ho i.val (List.mem_range.mpr hi)
  obtain ⟨hleft, hright⟩ := Bool.and_eq_true_iff.mp he
  exact ⟨(s.located i.castSucc).2.trans
      (((Dyadic.less_iff _ _).mp hleft).trans (r.located i).1),
    (r.located i).2.trans (((Dyadic.less_iff _ _).mp hright).trans (s.located i.succ).1)⟩

private theorem expanded_at_zero_positive {cs : List ℤ} {ws : List Window} {d e : ℕ}
    (r : LocatedRoots cs ws d) (h : 2 * (cs.length - 1) ≤ e) :
    0 < (expandGamma e cs).eval 0 := by
  rw [eval_expandGamma _ _ h (by norm_num : (0 : ℝ) ≠ -1)]
  simpa [gammaArgument] using r.pos_zero

private theorem lift_left_of {d c : ℕ} (r : Fin d → ℝ) (i : Fin (d+d+c)) (h : i.val < d) :
    liftRoots c r i = reciprocalLift (r ⟨d-1-i.val, by omega⟩) := by
  simp [liftRoots, h]

private theorem lift_center_of {d c : ℕ} (r : Fin d → ℝ) (i : Fin (d+d+c))
    (h₁ : d ≤ i.val) (h₂ : i.val < d+c) :
    liftRoots c r i = -1 := by
  simp [liftRoots, not_lt.mpr h₁, h₂]

private theorem lift_right_of {d c : ℕ} (r : Fin d → ℝ) (i : Fin (d+d+c))
    (h : d+c ≤ i.val) :
    liftRoots c r i = negLift (r ⟨i.val-(d+c), by have := i.isLt; omega⟩) := by
  simp [liftRoots, not_lt.mpr h, not_lt.mpr (show d ≤ i.val by omega)]

/-- An equal-degree gamma pair lifts to degrees `2*d` and `2*d+1`. The new
row supplies the intervening root at minus one. -/
theorem checked_odd {p q : List ℤ} {wp wq : List Window} {outerP outerQ : Dyadic} {d : ℕ}
    (hp : rowOK d p outerP wp = true) (hq : rowOK d q outerQ wq = true)
    (ho : equalOrder wp wq = true) :
    StrictNegativeInterlacing (expandGamma (d+d) p) (expandGamma (d+d+1) q) (d+d) := by
  obtain ⟨r⟩ := locatedRoots_of_rowOK hp
  obtain ⟨s⟩ := locatedRoots_of_rowOK hq
  have hfirst (i : Fin d) : r.points i < s.points i := by
    have hi : i.val < wp.length := by rw [r.windows_eq]; exact i.isLt
    have h := (Bool.and_eq_true_iff.mp
      (List.all_eq_true.mp ho i.val (List.mem_range.mpr hi))).1
    exact (r.located i).2.trans (((Dyadic.less_iff _ _).mp h).trans (s.located i).1)
  have hnext (i j : Fin d) (hij : i.val+1=j.val) : s.points i < r.points j := by
    have hi : i.val < wp.length := by rw [r.windows_eq]; exact i.isLt
    have hj : i.val+1 < wp.length := by rw [hij, r.windows_eq]; exact j.isLt
    have he := (Bool.and_eq_true_iff.mp
      (List.all_eq_true.mp ho i.val (List.mem_range.mpr hi))).2
    rw [if_pos hj, hij] at he
    exact (s.located i).2.trans (((Dyadic.less_iff _ _).mp he).trans (r.located j).1)
  let P := expandGamma (d+d) p
  let Q := expandGamma (d+d+1) q
  let R : Fin (d+d) → ℝ := liftRoots 0 r.points
  let S := liftRoots 1 s.points
  have hpl : 2 * (p.length - 1) ≤ d+d := by rw [r.length_eq]; omega
  have hql : 2 * (q.length - 1) ≤ d+d+1 := by rw [s.length_eq]; omega
  have hnP : P ≠ 0 := by intro h; simpa [P, h] using expanded_at_zero_positive r hpl
  have hnQ : Q ≠ 0 := by intro h; simpa [Q, h] using expanded_at_zero_positive s hql
  have hr : StrictMono R := liftRoots_strictMono (by decide) r.points r.strictMono r.negative
  have hs : StrictMono S := liftRoots_strictMono (by decide) s.points s.strictMono s.negative
  have hzP (i) : P.eval (R i) = 0 :=
    liftRoots_eval hpl r.points r.negative r.zeroes (fun h ↦ (h rfl).elim) i
  have hzQ (i) : Q.eval (S i) = 0 :=
    liftRoots_eval hql s.points s.negative s.zeroes (fun _ ↦ by
      rw [show d+d+1=2*d+1 by omega]
      exact expandGamma_odd_at_center q d s.length_eq.le) i
  refine ⟨R, S, leadingCoeff_ne_zero.mpr hnP, leadingCoeff_ne_zero.mpr hnQ,
    factor_of_degree_bound R hnP (expandGamma_degree_le p _ hpl) hr.injective hzP,
    factor_of_degree_bound S hnQ (expandGamma_degree_le q _ hql) hs.injective hzQ,
    hr, hs, liftRoots_negative (c := 0) r.points r.negative, liftRoots_negative s.points s.negative, ?_⟩
  intro i
  have hiv := i.isLt
  change liftRoots 1 s.points i.castSucc < liftRoots 0 r.points i ∧
    liftRoots 0 r.points i < liftRoots 1 s.points i.succ
  by_cases hl : i.val < d
  · rw [lift_left_of (c := 0) r.points i hl, lift_left_of (c := 1) s.points i.castSucc hl]
    refine ⟨reciprocalLift_strictAnti (r.negative _) (s.negative _) (hfirst _), ?_⟩
    by_cases hnextleft : i.val+1 < d
    · rw [lift_left_of (c := 1) s.points i.succ hnextleft]
      exact reciprocalLift_strictAnti (s.negative _) (r.negative _)
        (hnext _ _ (by simp only [Fin.val_succ]; omega))
    · rw [lift_center_of (c := 1) s.points i.succ (by simp; omega) (by simp; omega)]
      exact reciprocalLift_lt_center (r.negative _)
  · rw [lift_right_of (c := 0) r.points i (by omega), lift_right_of (c := 1) s.points i.succ (by simp; omega)]
    refine ⟨?_, negLift_strictMono (r.negative _) (s.negative _) ?_⟩
    · by_cases he : i.val = d
      · rw [lift_center_of (c := 1) s.points i.castSucc (by simpa using he.ge) (by simp; omega)]
        exact (negLift_range (r.negative _)).1
      · rw [lift_right_of (c := 1) s.points i.castSucc (by simp; omega)]
        exact negLift_strictMono (s.negative _) (r.negative _)
          (hnext _ _ (by simp only [Fin.val_castSucc, Nat.add_zero]; omega))
    · have index : (⟨i.succ.val-(d+1), by have := i.succ.isLt; omega⟩ : Fin d) =
          ⟨i.val-(d+0), by omega⟩ := by
        apply Fin.ext
        simp only [Fin.val_succ, Nat.add_sub_add_right, Nat.add_zero]
      rw [index]
      exact hfirst _

end

end LongCycleFinite.K3
