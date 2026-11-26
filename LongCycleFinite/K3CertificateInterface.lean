import LongCycleFinite.K3Readout

/-! A semantic interface for alternate dyadic-sign checkers on the same certificates. -/

namespace LongCycleFinite.K3

private def bracketEndpoints : ℕ → List Window → List (Bool × Dyadic)
  | _, [] => []
  | j, w :: ws =>
    (negativeSign j, w.left) :: (!negativeSign j, w.right) :: bracketEndpoints (j-1) ws

def certificateEndpoints (c : RowCertificate) : List (Bool × Dyadic) :=
  (false, Dyadic.zero) :: bracketEndpoints c.brackets.length c.brackets

noncomputable def EndpointHasSign (cs : List ℤ) (item : Bool × Dyadic) : Prop :=
  HasSign item.1 ((ofCoeffs cs).eval item.2.value)

private theorem bracketEndpoints_mem (j : ℕ) {ws : List Window} (i : Fin ws.length) :
    (negativeSign (j-i.val), (bracketAt ws i.val).left) ∈ bracketEndpoints j ws ∧
      (!negativeSign (j-i.val), (bracketAt ws i.val).right) ∈ bracketEndpoints j ws := by
  induction ws generalizing j with
  | nil => exact Fin.elim0 i
  | cons w ws ih =>
    refine Fin.cases ?_ (fun a ↦ ?_) i
    · simp [bracketAt, bracketEndpoints]
    · obtain ⟨left, right⟩ := ih (j-1) a
      have h₁ : (negativeSign (j-1-a.val), (bracketAt ws a.val).left) ∈
          bracketEndpoints j (w :: ws) := by
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ left)
      have h₂ : (!negativeSign (j-1-a.val), (bracketAt ws a.val).right) ∈
          bracketEndpoints j (w :: ws) := by
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ right)
      simpa [bracketAt, Nat.sub_sub, Nat.add_comm] using And.intro h₁ h₂

private theorem endpointOK_of_sign {negative : Bool} {cs : List ℤ} {x : Dyadic}
    (h : EndpointHasSign cs (negative, x)) : endpointOK negative cs x = true :=
  Bool.or_eq_true_iff.mpr (Or.inr ((positiveAt_iff negative cs x).mpr h))

/-- The root readout accepts the same semantic endpoint proofs from any
sound checker, with the original exact window order and degrees. -/
theorem rowAtOK_of_all_signed {n : ℕ} {c : RowCertificate}
    (hLen : (gammaRow n).length = (n-2)/2 + 1 ∧ c.brackets.length = (n-2)/2)
    (hOrder : orderOK c.outer c.brackets = true)
    (hSigns : ∀ v ∈ certificateEndpoints c, EndpointHasSign (gammaRow n) v) :
    rowAtOK n c = true := by
  have hz := endpointOK_of_sign (hSigns (false, Dyadic.zero) (by simp [certificateEndpoints]))
  have hv : rowSigns (gammaRow n) c.brackets = true := by
    apply List.all_eq_true.mpr
    intro i hi
    let j : Fin c.brackets.length := ⟨i, List.mem_range.mp hi⟩
    obtain ⟨left, right⟩ := bracketEndpoints_mem c.brackets.length j
    refine Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩
    · exact endpointOK_of_sign (hSigns _ (List.mem_cons_of_mem _ left))
    · exact endpointOK_of_sign (hSigns _ (List.mem_cons_of_mem _ right))
  simp [rowAtOK, rowOK, hLen, hz, hOrder, hv]

/-- A consecutive group with a common magnitude exponent and fixed-point scale. -/
structure SignBlock where
  magnitudeExponent : ℤ
  scaleExponent : ℤ
  count : ℕ

/-- Each block consumes a consecutive portion of the fixed endpoint sequence. -/
def checkSignBlocks (verify : SignBlock → List (Bool × Dyadic) → Bool) :
    List SignBlock → List (Bool × Dyadic) → Bool
  | [], items => items.isEmpty
  | block :: blocks, items =>
    verify block (items.take block.count) && checkSignBlocks verify blocks (items.drop block.count)

theorem checkedSignBlocks_all_signed {cs : List ℤ}
    {verify : SignBlock → List (Bool × Dyadic) → Bool}
    (sound : ∀ block items, verify block items = true → ∀ item ∈ items, EndpointHasSign cs item)
    {blocks : List SignBlock} {items : List (Bool × Dyadic)}
    (h : checkSignBlocks verify blocks items = true) :
    ∀ item ∈ items, EndpointHasSign cs item := by
  induction blocks generalizing items with
  | nil => simp [checkSignBlocks] at h; simp [h]
  | cons block blocks ih =>
    obtain ⟨start, tail⟩ := Bool.and_eq_true_iff.mp h
    intro item mem
    rw [← List.take_append_drop block.count items] at mem
    rcases List.mem_append.mp mem with first | rest
    · exact sound block (items.take block.count) start item first
    · exact ih tail item rest

theorem rowAtOK_of_sign_blocks {n : ℕ} {c : RowCertificate}
    {verify : SignBlock → List (Bool × Dyadic) → Bool} {blocks : List SignBlock}
    (sound : ∀ block items,
      verify block items = true → ∀ item ∈ items, EndpointHasSign (gammaRow n) item)
    (hLen : (gammaRow n).length = (n-2)/2 + 1 ∧ c.brackets.length = (n-2)/2)
    (hOrder : orderOK c.outer c.brackets = true)
    (h : checkSignBlocks verify blocks (certificateEndpoints c) = true) :
    rowAtOK n c = true :=
  rowAtOK_of_all_signed hLen hOrder (checkedSignBlocks_all_signed sound h)

#print axioms rowAtOK_of_all_signed
#print axioms checkedSignBlocks_all_signed
#print axioms rowAtOK_of_sign_blocks

end LongCycleFinite.K3
