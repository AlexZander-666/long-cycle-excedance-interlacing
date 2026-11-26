import LongCycleFinite.K3NaturalReadout

/-! Restart kernel reduction at bounded segments of a long row's endpoint list. -/

namespace LongCycleFinite.K3

def naturalChunkOK (cs : List ℤ) (c : RowCertificate) (width index : ℕ) : Bool :=
  (((certificateEndpoints c).drop (width * index)).take width).all
    (fun p ↦ naturalSign p.1 cs p.2)

private theorem all_of_chunks {α : Type} (p : α → Bool) (width count : ℕ) (items : List α)
    (hlen : items.length ≤ width * count)
    (h : ∀ i : Fin count, ((items.drop (width * i.val)).take width).all p = true) :
    items.all p = true := by
  induction count generalizing items with
  | zero =>
    simp at hlen
    simp [hlen]
  | succ count ih =>
    have htake : (items.take width).all p = true := by
      simpa only [Fin.val_zero, Nat.mul_zero, List.drop_zero] using h 0
    have hbound : (items.drop width).length ≤ width * count := by
      rw [List.length_drop]
      rw [Nat.mul_succ] at hlen
      omega
    have htail : (items.drop width).all p = true := by
      apply ih _ hbound
      intro i
      simpa only [List.drop_drop, Fin.val_succ, Nat.mul_succ, Nat.add_comm] using h i.succ
    rw [← List.take_append_drop width items, List.all_append, htake, htail]
    rfl

theorem naturalCertificateOK_of_chunks {cs : List ℤ} {c : RowCertificate} {width count : ℕ}
    (hLen : (certificateEndpoints c).length ≤ width * count)
    (h : ∀ i : Fin count, naturalChunkOK cs c width i.val = true) :
    naturalCertificateOK cs c = true :=
  all_of_chunks _ width count _ hLen h

#print axioms naturalCertificateOK_of_chunks

end LongCycleFinite.K3
