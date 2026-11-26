import LongCycleFinite.K4Readout
import LongCycleFinite.K3NaturalChunk

namespace LongCycleFinite
open K3

/-- Remove the separate positive-at-zero test from the shared endpoint list. -/
private def endpoints (ws : List Window) : List (Bool × Dyadic) :=
  (certificateEndpoints ⟨Dyadic.zero, ws⟩).drop 1

private theorem endpoints_cons (w : Window) (ws : List Window) :
    endpoints (w :: ws) = (negativeSign (ws.length+1), w.left) ::
      (!negativeSign (ws.length+1), w.right) :: endpoints ws := by rfl

private theorem endpoints_mem {ws : List Window} (i : Fin ws.length) :
    (negativeSign (ws.length-i.val), (bracketAt ws i.val).left) ∈ endpoints ws ∧
      (!negativeSign (ws.length-i.val), (bracketAt ws i.val).right) ∈ endpoints ws := by
  induction ws with
  | nil => exact Fin.elim0 i
  | cons w ws ih =>
    rw [endpoints_cons]
    refine Fin.cases ?_ (fun a ↦ ?_) i
    · simp [bracketAt]
    · obtain ⟨left, right⟩ := ih a
      constructor
      · apply List.mem_cons_of_mem; apply List.mem_cons_of_mem
        simpa [bracketAt] using left
      · apply List.mem_cons_of_mem; apply List.mem_cons_of_mem
        simpa [bracketAt] using right

private theorem endpointOK_of_sign {negative : Bool} {cs : List ℤ} {x : Dyadic}
    (h : EndpointHasSign cs (negative, x)) : endpointOK negative cs x = true :=
  Bool.or_eq_true_iff.mpr (Or.inr ((positiveAt_iff negative cs x).mpr h))


theorem rowOK_of_all_signed {d : ℕ} {cs : List ℤ} {c : RowCertificate}
    (hLen : cs.length = d + 1 ∧ c.brackets.length = d)
    (hOrder : orderOK c.outer c.brackets = true)
    (hSigns : ∀ v ∈ certificateEndpoints c, EndpointHasSign cs v) :
    rowOK d cs c.outer c.brackets = true := by
  have hz := endpointOK_of_sign (hSigns (false, Dyadic.zero) (by simp [certificateEndpoints]))
  have hv : rowSigns cs c.brackets = true := by
    apply List.all_eq_true.mpr
    intro i hi
    let j : Fin c.brackets.length := ⟨i, List.mem_range.mp hi⟩
    obtain ⟨left, right⟩ := endpoints_mem j
    have formula : certificateEndpoints c = (false, Dyadic.zero) :: endpoints c.brackets := rfl
    rw [formula] at hSigns
    refine Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩
    · exact endpointOK_of_sign (hSigns _ (List.mem_cons_of_mem _ left))
    · exact endpointOK_of_sign (hSigns _ (List.mem_cons_of_mem _ right))
  simp [rowOK, hLen, hz, hOrder, hv]


namespace K4

/-- Check a possibly large row using the common natural Horner/chunk interface. -/
theorem rowAtOK_of_natural {n : ℕ} {c : RowCertificate} {cs : List ℤ}
    (hCoeffs : gammaRow n = cs)
    (hLen : cs.length = (n-2)/2 + 1 ∧ c.brackets.length = (n-2)/2)
    (hOrder : orderOK c.outer c.brackets = true)
    (h : K3.naturalCertificateOK cs c = true) : rowAtOK n c = true := by
  unfold rowAtOK
  rw [hCoeffs]
  refine rowOK_of_all_signed hLen hOrder ?_
  intro item mem
  exact K3.naturalSign_sound (List.all_eq_true.mp h item mem)

#print axioms rowAtOK_of_natural

end K4
end LongCycleFinite

