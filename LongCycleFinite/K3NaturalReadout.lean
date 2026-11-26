import LongCycleFinite.K3CertificateInterface
import LongCycleFinite.K3NaturalArithmetic

/-! The alternative exact unsigned sign checker for the same dyadic data. -/

namespace LongCycleFinite.K3

def naturalCertificateOK (cs : List ℤ) (c : RowCertificate) : Bool :=
  (certificateEndpoints c).all fun p ↦ naturalSign p.1 cs p.2

theorem rowAtOK_of_natural {n : ℕ} {c : RowCertificate} {cs : List ℤ}
    (hCoeffs : gammaRow n = cs)
    (hLen : cs.length = (n-2)/2 + 1 ∧ c.brackets.length = (n-2)/2)
    (hOrder : orderOK c.outer c.brackets = true)
    (h : naturalCertificateOK cs c = true) :
    rowAtOK n c = true := by
  refine rowAtOK_of_all_signed (by rwa [hCoeffs]) hOrder ?_
  intro item mem
  rw [hCoeffs]
  exact naturalSign_sound (List.all_eq_true.mp h item mem)

#print axioms rowAtOK_of_natural

end LongCycleFinite.K3
