import LongCycleFinite.K3Readout

namespace LongCycleFinite.K3.DataExplicit

set_option maxRecDepth 16384
set_option maxHeartbeats 0

def gamma0003 : List ℤ := [
  1,
]

theorem state0003 :
    gammaState 0 = ⟨gamma0003, [], []⟩ := by
  rfl

def cert0003 : RowCertificate := ⟨⟨-1, 0⟩, [
]⟩

theorem row0003 : rowAtOK 3 cert0003 = true := by
  change rowOK 0 (gammaState 0).current cert0003.outer cert0003.brackets = true
  rw [state0003]
  decide +kernel

def gamma0004 : List ℤ := [
  1,
  2,
]

theorem state0004 :
    gammaState 1 = ⟨gamma0004, gamma0003, []⟩ := by
  rw [gammaState, state0003]
  rfl

def cert0004 : RowCertificate := ⟨⟨-8796093061531, 43⟩, [
  ⟨⟨-8796093061531, 44⟩, ⟨-8796092722607, 44⟩⟩,
]⟩

theorem row0004 : rowAtOK 4 cert0004 = true := by
  change rowOK 1 (gammaState 1).current cert0004.outer cert0004.brackets = true
  rw [state0004]
  decide +kernel

theorem order0004 : orderAtOK 4 cert0003 cert0004 = true := by decide +kernel

theorem pair0004 : OriginalPair 4 :=
  original_of_certificates (by decide) row0003 row0004 order0004

def gamma0005 : List ℤ := [
  1,
  8,
]

theorem state0005 :
    gammaState 2 = ⟨gamma0005, gamma0004, gamma0003⟩ := by
  rw [gammaState, state0004]
  rfl

def cert0005 : RowCertificate := ⟨⟨-8796093449339, 45⟩, [
  ⟨⟨-8796093449339, 46⟩, ⟨-4398046489853, 45⟩⟩,
]⟩

theorem row0005 : rowAtOK 5 cert0005 = true := by
  change rowOK 1 (gammaState 2).current cert0005.outer cert0005.brackets = true
  rw [state0005]
  decide +kernel

theorem order0005 : orderAtOK 5 cert0004 cert0005 = true := by decide +kernel

theorem pair0005 : OriginalPair 5 :=
  original_of_certificates (by decide) row0004 row0005 order0005

def gamma0006 : List ℤ := [
  1,
  32,
  16,
]

theorem state0006 :
    gammaState 3 = ⟨gamma0006, gamma0005, gamma0004⟩ := by
  rw [gammaState, state0005]
  rfl

def cert0006 : RowCertificate := ⟨⟨-17312873763839, 42⟩, [
  ⟨⟨-17312873763839, 43⟩, ⟨-17312872977407, 43⟩⟩,
  ⟨⟨-2234500659327, 46⟩, ⟨-8938002167675, 48⟩⟩,
]⟩

theorem row0006 : rowAtOK 6 cert0006 = true := by
  change rowOK 2 (gammaState 3).current cert0006.outer cert0006.brackets = true
  rw [state0006]
  decide +kernel

theorem order0006 : orderAtOK 6 cert0005 cert0006 = true := by decide +kernel

theorem pair0006 : OriginalPair 6 :=
  original_of_certificates (by decide) row0005 row0006 order0006

def gamma0007 : List ℤ := [
  1,
  87,
  206,
]

theorem state0007 :
    gammaState 4 = ⟨gamma0007, gamma0006, gamma0005⟩ := by
  rw [gammaState, state0006]
  rfl

def cert0007 : RowCertificate := ⟨⟨-14443351418723, 44⟩, [
  ⟨⟨-14443351418723, 45⟩, ⟨-7221675472661, 44⟩⟩,
  ⟨⟨-13314179648843, 50⟩, ⟨-13314178943727, 50⟩⟩,
]⟩

theorem row0007 : rowAtOK 7 cert0007 = true := by
  change rowOK 2 (gammaState 4).current cert0007.outer cert0007.brackets = true
  rw [state0007]
  decide +kernel

theorem order0007 : orderAtOK 7 cert0006 cert0007 = true := by decide +kernel

theorem pair0007 : OriginalPair 7 :=
  original_of_certificates (by decide) row0006 row0007 order0007

def gamma0008 : List ℤ := [
  1,
  205,
  1308,
  412,
]

theorem state0008 :
    gammaState 5 = ⟨gamma0008, gamma0007, gamma0006⟩ := by
  rw [gammaState, state0007]
  rfl

def cert0008 : RowCertificate := ⟨⟨-3309202784971, 39⟩, [
  ⟨⟨-3309202784971, 40⟩, ⟨-3309202645841, 40⟩⟩,
  ⟨⟨-11260063713739, 46⟩, ⟨-5630031648317, 45⟩⟩,
  ⟨⟨-2837187317161, 49⟩, ⟨-5674374368433, 50⟩⟩,
]⟩

theorem row0008 : rowAtOK 8 cert0008 = true := by
  change rowOK 3 (gammaState 5).current cert0008.outer cert0008.brackets = true
  rw [state0008]
  decide +kernel

theorem order0008 : orderAtOK 8 cert0007 cert0008 = true := by decide +kernel

theorem pair0008 : OriginalPair 8 :=
  original_of_certificates (by decide) row0007 row0008 order0008

def gamma0009 : List ℤ := [
  1,
  450,
  6460,
  7328,
]

theorem state0009 :
    gammaState 6 = ⟨gamma0009, gamma0008, gamma0007⟩ := by
  rw [gammaState, state0008]
  rfl

def cert0009 : RowCertificate := ⟨⟨-7085488958937, 42⟩, [
  ⟨⟨-7085488958937, 43⟩, ⟨-7085488565069, 43⟩⟩,
  ⟨⟨-10375953207813, 47⟩, ⟨-1296994102425, 44⟩⟩,
  ⟨⟨-10348469682467, 52⟩, ⟨-646779326367, 48⟩⟩,
]⟩

theorem row0009 : rowAtOK 9 cert0009 = true := by
  change rowOK 3 (gammaState 6).current cert0009.outer cert0009.brackets = true
  rw [state0009]
  decide +kernel

theorem order0009 : orderAtOK 9 cert0008 cert0009 = true := by decide +kernel

theorem pair0009 : OriginalPair 9 :=
  original_of_certificates (by decide) row0008 row0009 order0009

def gamma0010 : List ℤ := [
  1,
  950,
  27012,
  75488,
  14656,
]

theorem state0010 :
    gammaState 7 = ⟨gamma0010, gamma0009, gamma0008⟩ := by
  rw [gammaState, state0009]
  rfl

def cert0010 : RowCertificate := ⟨⟨-10482448581361, 40⟩, [
  ⟨⟨-10482448581361, 41⟩, ⟨-1310306004417, 38⟩⟩,
  ⟨⟨-1514864266073, 42⟩, ⟨-12118913539463, 45⟩⟩,
  ⟨⟨-2692528376405, 46⟩, ⟨-10770113147021, 48⟩⟩,
  ⟨⟨-2445609118469, 51⟩, ⟨-305701126457, 48⟩⟩,
]⟩

theorem row0010 : rowAtOK 10 cert0010 = true := by
  change rowOK 4 (gammaState 7).current cert0010.outer cert0010.brackets = true
  rw [state0010]
  decide +kernel

theorem order0010 : orderAtOK 10 cert0009 cert0010 = true := by decide +kernel

theorem pair0010 : OriginalPair 10 :=
  original_of_certificates (by decide) row0009 row0010 order0010

def gamma0011 : List ℤ := [
  1,
  1961,
  101661,
  576908,
  393772,
]

theorem state0011 :
    gammaState 8 = ⟨gamma0011, gamma0010, gamma0009⟩ := by
  rw [gammaState, state0010]
  rfl

def cert0011 : RowCertificate := ⟨⟨-5558853915565, 41⟩, [
  ⟨⟨-5558853915565, 42⟩, ⟨-11117707339911, 43⟩⟩,
  ⟨⟨-12612369108101, 46⟩, ⟨-6306184313257, 45⟩⟩,
  ⟨⟨-12040159413013, 49⟩, ⟨-12040159034557, 49⟩⟩,
  ⟨⟨-590133450827, 50⟩, ⟨-2360533700589, 52⟩⟩,
]⟩

theorem row0011 : rowAtOK 11 cert0011 = true := by
  change rowOK 4 (gammaState 8).current cert0011.outer cert0011.brackets = true
  rw [state0011]
  decide +kernel

theorem order0011 : orderAtOK 11 cert0010 cert0011 = true := by decide +kernel

theorem pair0011 : OriginalPair 11 :=
  original_of_certificates (by decide) row0010 row0011 order0011

theorem range0004_0011 {n : ℕ} (lo : 4 ≤ n) (hi : n ≤ 11) : OriginalPair n := by
  interval_cases n
  · exact pair0004
  · exact pair0005
  · exact pair0006
  · exact pair0007
  · exact pair0008
  · exact pair0009
  · exact pair0010
  · exact pair0011

#print axioms range0004_0011

end LongCycleFinite.K3.DataExplicit
