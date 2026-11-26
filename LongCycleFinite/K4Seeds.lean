import LongCycleFinite.K4Readout

/-! Direct kernel replay of the first dyadic brackets in the distributed certificate. -/

namespace LongCycleFinite.K4.Data

set_option maxRecDepth 16384
set_option maxHeartbeats 0

def cert0004 : RowCertificate := ⟨⟨-8796093061531, 43⟩, [
  ⟨⟨-8796093061531, 44⟩, ⟨-8796092722607, 44⟩⟩,
]⟩

theorem row0004 : rowAtOK 4 cert0004 = true := by decide +kernel

def cert0005 : RowCertificate := ⟨⟨-8796093449339, 45⟩, [
  ⟨⟨-8796093449339, 46⟩, ⟨-4398046489853, 45⟩⟩,
]⟩

theorem row0005 : rowAtOK 5 cert0005 = true := by decide +kernel

theorem order0005 : orderAtOK 5 cert0004 cert0005 = true := by decide +kernel

theorem pair0005 : OriginalPair 5 :=
  original_of_certificates (by decide) row0004 row0005 order0005

def cert0006 : RowCertificate := ⟨⟨-11680635070373, 42⟩, [
  ⟨⟨-11680635070373, 43⟩, ⟨-11680634677157, 43⟩⟩,
  ⟨⟨-6623891392973, 47⟩, ⟨-3311945523095, 46⟩⟩,
]⟩

theorem row0006 : rowAtOK 6 cert0006 = true := by decide +kernel

theorem order0006 : orderAtOK 6 cert0005 cert0006 = true := by decide +kernel

theorem pair0006 : OriginalPair 6 :=
  original_of_certificates (by decide) row0005 row0006 order0006

def cert0007 : RowCertificate := ⟨⟨-12738269361455, 44⟩, [
  ⟨⟨-12738269361455, 45⟩, ⟨-6369134338703, 44⟩⟩,
  ⟨⟨-11433265279131, 49⟩, ⟨-5716632375043, 48⟩⟩,
]⟩

theorem row0007 : rowAtOK 7 cert0007 = true := by decide +kernel

theorem order0007 : orderAtOK 7 cert0006 cert0007 = true := by decide +kernel

theorem pair0007 : OriginalPair 7 :=
  original_of_certificates (by decide) row0006 row0007 order0007

def cert0008 : RowCertificate := ⟨⟨-16690192779489, 42⟩, [
  ⟨⟨-16690192779489, 43⟩, ⟨-16690191797847, 43⟩⟩,
  ⟨⟨-12872610599659, 46⟩, ⟨-12872610209909, 46⟩⟩,
  ⟨⟨-15746144355909, 51⟩, ⟨-15746143427657, 51⟩⟩,
]⟩

theorem row0008 : rowAtOK 8 cert0008 = true := by decide +kernel

theorem order0008 : orderAtOK 8 cert0007 cert0008 = true := by decide +kernel

theorem pair0008 : OriginalPair 8 :=
  original_of_certificates (by decide) row0007 row0008 order0008

def cert0009 : RowCertificate := ⟨⟨-11026281236449, 43⟩, [
  ⟨⟨-11026281236449, 44⟩, ⟨-5513140446743, 43⟩⟩,
  ⟨⟨-13276126402615, 47⟩, ⟨-6638062987305, 46⟩⟩,
  ⟨⟨-12729090721977, 52⟩, ⟨-3182272519211, 50⟩⟩,
]⟩

theorem row0009 : rowAtOK 9 cert0009 = true := by decide +kernel

theorem order0009 : orderAtOK 9 cert0008 cert0009 = true := by decide +kernel

theorem pair0009 : OriginalPair 9 :=
  original_of_certificates (by decide) row0008 row0009 order0009

def cert0010 : RowCertificate := ⟨⟨-14510113735, 31⟩, [
  ⟨⟨-14510113735, 32⟩, ⟨-14858355614927, 42⟩⟩,
  ⟨⟨-5629045031571, 44⟩, ⟨-2814522415223, 43⟩⟩,
  ⟨⟨-7168240467521, 47⟩, ⟨-7168240236475, 47⟩⟩,
  ⟨⟨-11162094693917, 53⟩, ⟨-11162094165379, 53⟩⟩,
]⟩

theorem row0010 : rowAtOK 10 cert0010 = true := by decide +kernel

theorem order0010 : orderAtOK 10 cert0009 cert0010 = true := by decide +kernel

theorem pair0010 : OriginalPair 10 :=
  original_of_certificates (by decide) row0009 row0010 order0010

def cert0011 : RowCertificate := ⟨⟨-8850612002219, 42⟩, [
  ⟨⟨-8850612002219, 43⟩, ⟨-4425305812435, 42⟩⟩,
  ⟨⟨-13108320250003, 46⟩, ⟨-6554159923347, 45⟩⟩,
  ⟨⟨-8088839046213, 48⟩, ⟨-16177677575395, 49⟩⟩,
  ⟨⟨-10265550973035, 54⟩, ⟨-5132775251299, 53⟩⟩,
]⟩

theorem row0011 : rowAtOK 11 cert0011 = true := by decide +kernel

theorem order0011 : orderAtOK 11 cert0010 cert0011 = true := by decide +kernel

theorem pair0011 : OriginalPair 11 :=
  original_of_certificates (by decide) row0010 row0011 order0011

def cert0012 : RowCertificate := ⟨⟨-5402580686491, 39⟩, [
  ⟨⟨-5402580686491, 40⟩, ⟨-10805161031957, 41⟩⟩,
  ⟨⟨-4399523749681, 43⟩, ⟨-1099880899851, 41⟩⟩,
  ⟨⟨-16507757136823, 47⟩, ⟨-16507756187947, 47⟩⟩,
  ⟨⟨-2295560874597, 47⟩, ⟨-2295560799295, 47⟩⟩,
  ⟨⟨-4864860443645, 54⟩, ⟨-9729720447941, 55⟩⟩,
]⟩

theorem row0012 : rowAtOK 12 cert0012 = true := by decide +kernel

theorem order0012 : orderAtOK 12 cert0011 cert0012 = true := by decide +kernel

theorem pair0012 : OriginalPair 12 :=
  original_of_certificates (by decide) row0011 row0012 order0012

def cert0013 : RowCertificate := ⟨⟨-6298226545771, 41⟩, [
  ⟨⟨-6298226545771, 42⟩, ⟨-787278283241, 39⟩⟩,
  ⟨⟨-10540675698559, 45⟩, ⟨-2635168789397, 43⟩⟩,
  ⟨⟨-167173734843, 41⟩, ⟨-5349559206465, 46⟩⟩,
  ⟨⟨-5328892107005, 49⟩, ⟨-10657783863029, 50⟩⟩,
  ⟨⟨-9398201700479, 56⟩, ⟨-9398201277655, 56⟩⟩,
]⟩

theorem row0013 : rowAtOK 13 cert0013 = true := by decide +kernel

theorem order0013 : orderAtOK 13 cert0012 cert0013 = true := by decide +kernel

theorem pair0013 : OriginalPair 13 :=
  original_of_certificates (by decide) row0012 row0013 order0013

def cert0014 : RowCertificate := ⟨⟨-15134951746773, 40⟩, [
  ⟨⟨-15134951746773, 41⟩, ⟨-1891868907677, 38⟩⟩,
  ⟨⟨-12502717216993, 44⟩, ⟨-12502716809593, 44⟩⟩,
  ⟨⟨-13795020523099, 46⟩, ⟨-13795020054255, 46⟩⟩,
  ⟨⟨-7045045593641, 47⟩, ⟨-7045045180955, 47⟩⟩,
  ⟨⟨-1584234396197, 48⟩, ⟨-12673874751967, 51⟩⟩,
  ⟨⟨-4594426642653, 56⟩, ⟨-4594426435385, 56⟩⟩,
]⟩

theorem row0014 : rowAtOK 14 cert0014 = true := by decide +kernel

theorem order0014 : orderAtOK 14 cert0013 cert0014 = true := by decide +kernel

theorem pair0014 : OriginalPair 14 :=
  original_of_certificates (by decide) row0013 row0014 order0014

def cert0015 : RowCertificate := ⟨⟨-17213140342597, 42⟩, [
  ⟨⟨-17213140342597, 43⟩, ⟨-17213139555661, 43⟩⟩,
  ⟨⟨-1889978020347, 42⟩, ⟨-7559911811559, 44⟩⟩,
  ⟨⟨-4726656433441, 45⟩, ⟨-9453312560737, 46⟩⟩,
  ⟨⟨-1175883483675, 45⟩, ⟨-9407067311175, 48⟩⟩,
  ⟨⟨-7700929130433, 51⟩, ⟨-15401857751897, 52⟩⟩,
  ⟨⟨-9054910140871, 58⟩, ⟨-9054909867023, 58⟩⟩,
]⟩

theorem row0015 : rowAtOK 15 cert0015 = true := by decide +kernel

theorem order0015 : orderAtOK 15 cert0014 cert0015 = true := by decide +kernel

theorem pair0015 : OriginalPair 15 :=
  original_of_certificates (by decide) row0014 row0015 order0015

theorem seeds {n : ℕ} (lo : 5 ≤ n) (hi : n ≤ 15) : OriginalPair n := by
  interval_cases n
  all_goals first | exact pair0005 | exact pair0006 | exact pair0007 | exact pair0008 | exact pair0009 | exact pair0010 | exact pair0011 | exact pair0012 | exact pair0013 | exact pair0014 | exact pair0015

#print axioms seeds

end LongCycleFinite.K4.Data
