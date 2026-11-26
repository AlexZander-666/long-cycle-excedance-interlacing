import LongCycleFinite.K3DataExplicit.Rows0011

namespace LongCycleFinite.K3.DataExplicit

set_option maxRecDepth 16384
set_option maxHeartbeats 0

def gamma0012 : List ℤ := [
  1,
  3995,
  357187,
  3679542,
  5833348,
  787544,
]

theorem state0012 :
    gammaState 9 = ⟨gamma0012, gamma0011, gamma0010⟩ := by
  rw [gammaState, state0011]
  rfl

def cert0012 : RowCertificate := ⟨⟨-14781776138289, 40⟩, [
  ⟨⟨-14781776138289, 41⟩, ⟨-14781775281531, 41⟩⟩,
  ⟨⟨-5004822262421, 43⟩, ⟨-2502411027929, 42⟩⟩,
  ⟨⟨-14530849548197, 47⟩, ⟨-113522258251, 40⟩⟩,
  ⟨⟨-14132836877465, 50⟩, ⟨-14132836443761, 50⟩⟩,
  ⟨⟨-2307324077181, 53⟩, ⟨-9229295905447, 55⟩⟩,
]⟩

theorem row0012 : rowAtOK 12 cert0012 = true := by
  change rowOK 5 (gammaState 9).current cert0012.outer cert0012.brackets = true
  rw [state0012]
  decide +kernel

theorem order0012 : orderAtOK 12 cert0011 cert0012 = true := by decide +kernel

theorem pair0012 : OriginalPair 12 :=
  original_of_certificates (by decide) row0011 row0012 order0012

def gamma0013 : List ℤ := [
  1,
  8076,
  1198181,
  20787204,
  63585284,
  29025952,
]

theorem state0013 :
    gammaState 10 = ⟨gamma0013, gamma0012, gamma0011⟩ := by
  rw [gammaState, state0012]
  rfl

def cert0013 : RowCertificate := ⟨⟨-3973373852073, 40⟩, [
  ⟨⟨-3973373852073, 41⟩, ⟨-15893494681263, 43⟩⟩,
  ⟨⟨-10994964744527, 45⟩, ⟨-10994964402055, 45⟩⟩,
  ⟨⟨-8939630531797, 47⟩, ⟨-2234907562435, 45⟩⟩,
  ⟨⟨-8571110093107, 50⟩, ⟨-4285554915555, 49⟩⟩,
  ⟨⟨-2273069077959, 54⟩, ⟨-9092275911251, 56⟩⟩,
]⟩

theorem row0013 : rowAtOK 13 cert0013 = true := by
  change rowOK 5 (gammaState 10).current cert0013.outer cert0013.brackets = true
  rw [state0013]
  decide +kernel

theorem order0013 : orderAtOK 13 cert0012 cert0013 = true := by decide +kernel

theorem pair0013 : OriginalPair 13 :=
  original_of_certificates (by decide) row0012 row0013 order0013

def gamma0014 : List ℤ := [
  1,
  16252,
  3892869,
  107852908,
  570797284,
  586381632,
  58051904,
]

theorem state0014 :
    gammaState 11 = ⟨gamma0014, gamma0013, gamma0012⟩ := by
  rw [gammaState, state0013]
  rfl

def cert0014 : RowCertificate := ⟨⟨-2483641744155, 37⟩, [
  ⟨⟨-2483641744155, 38⟩, ⟨-4967283335211, 39⟩⟩,
  ⟨⟨-14589934297655, 44⟩, ⟨-14589933744293, 44⟩⟩,
  ⟨⟨-13407295476789, 46⟩, ⟨-6703647378509, 45⟩⟩,
  ⟨⟨-11511303719281, 48⟩, ⟨-5755651685451, 47⟩⟩,
  ⟨⟨-2658861907397, 49⟩, ⟨-5317723651009, 50⟩⟩,
  ⟨⟨-9001991298991, 57⟩, ⟨-9001990898241, 57⟩⟩,
]⟩

theorem row0014 : rowAtOK 14 cert0014 = true := by
  change rowOK 6 (gammaState 11).current cert0014.outer cert0014.brackets = true
  rw [state0014]
  decide +kernel

theorem order0014 : orderAtOK 14 cert0013 cert0014 = true := by decide +kernel

theorem pair0014 : OriginalPair 14 :=
  original_of_certificates (by decide) row0013 row0014 order0014

def gamma0015 : List ℤ := [
  1,
  32619,
  12367192,
  526201553,
  4483059638,
  8615502732,
  2823556360,
]

theorem state0015 :
    gammaState 12 = ⟨gamma0015, gamma0014, gamma0013⟩ := by
  rw [gammaState, state0014]
  rfl

def cert0015 : RowCertificate := ⟨⟨-5341189146239, 40⟩, [
  ⟨⟨-5341189146239, 41⟩, ⟨-10682377792287, 42⟩⟩,
  ⟨⟨-8238755564513, 44⟩, ⟨-16477510223409, 45⟩⟩,
  ⟨⟨-17432990363947, 47⟩, ⟨-2179123688269, 44⟩⟩,
  ⟨⟨-3828908080929, 47⟩, ⟨-3828907854451, 47⟩⟩,
  ⟨⟨-6706492330859, 51⟩, ⟨-6706492121385, 51⟩⟩,
  ⟨⟨-4470648367261, 57⟩, ⟨-4470648233121, 57⟩⟩,
]⟩

theorem row0015 : rowAtOK 15 cert0015 = true := by
  change rowOK 6 (gammaState 12).current cert0015.outer cert0015.brackets = true
  rw [state0015]
  decide +kernel

theorem order0015 : orderAtOK 15 cert0014 cert0015 = true := by decide +kernel

theorem pair0015 : OriginalPair 15 :=
  original_of_certificates (by decide) row0014 row0015 order0015

def gamma0016 : List ℤ := [
  1,
  65369,
  38667174,
  2453224673,
  31964776352,
  103200067592,
  74505635872,
  5647112720,
]

theorem state0016 :
    gammaState 13 = ⟨gamma0016, gamma0015, gamma0014⟩ := by
  rw [gammaState, state0015]
  rfl

def cert0016 : RowCertificate := ⟨⟨-6414959378385, 38⟩, [
  ⟨⟨-6414959378385, 39⟩, ⟨-12829918345165, 40⟩⟩,
  ⟨⟨-9901433035487, 43⟩, ⟨-4950716339177, 42⟩⟩,
  ⟨⟨-323903700129, 40⟩, ⟨-10364918042945, 45⟩⟩,
  ⟨⟨-1480035356929, 44⟩, ⟨-11840282303317, 47⟩⟩,
  ⟨⟨-5218518772483, 48⟩, ⟨-2609259233531, 47⟩⟩,
  ⟨⟨-8558874687653, 52⟩, ⟨-8558874415617, 52⟩⟩,
  ⟨⟨-8899760395795, 59⟩, ⟨-8899760123481, 59⟩⟩,
]⟩

theorem row0016 : rowAtOK 16 cert0016 = true := by
  change rowOK 7 (gammaState 13).current cert0016.outer cert0016.brackets = true
  rw [state0016]
  decide +kernel

theorem order0016 : orderAtOK 16 cert0015 cert0016 = true := by decide +kernel

theorem pair0016 : OriginalPair 16 :=
  original_of_certificates (by decide) row0015 row0016 order0016

def gamma0017 : List ℤ := [
  1,
  130886,
  119520618,
  11053386452,
  212017825488,
  1071273395856,
  1417505787680,
  350165673728,
]

theorem state0017 :
    gammaState 14 = ⟨gamma0017, gamma0016, gamma0015⟩ := by
  rw [gammaState, state0016]
  rfl

def cert0017 : RowCertificate := ⟨⟨-3443673651287, 39⟩, [
  ⟨⟨-3443673651287, 40⟩, ⟨-13774693950163, 42⟩⟩,
  ⟨⟨-11349400365673, 44⟩, ⟨-11349399929951, 44⟩⟩,
  ⟨⟨-13925053934061, 46⟩, ⟨-6962526746349, 45⟩⟩,
  ⟨⟨-4150052857595, 46⟩, ⟨-16600210681505, 48⟩⟩,
  ⟨⟨-7242289780697, 49⟩, ⟨-7242289357775, 49⟩⟩,
  ⟨⟨-11019887873643, 53⟩, ⟨-5509943758325, 52⟩⟩,
  ⟨⟨-4435438434555, 59⟩, ⟨-8870876592539, 60⟩⟩,
]⟩

theorem row0017 : rowAtOK 17 cert0017 = true := by
  change rowOK 7 (gammaState 14).current cert0017.outer cert0017.brackets = true
  rw [state0017]
  decide +kernel

theorem order0017 : orderAtOK 17 cert0016 cert0017 = true := by decide +kernel

theorem pair0017 : OriginalPair 17 :=
  original_of_certificates (by decide) row0016 row0017 order0017

def gamma0018 : List ℤ := [
  1,
  261938,
  366401074,
  48524937516,
  1330613494784,
  10005586042736,
  21806982843872,
  11690363780864,
  700331347456,
]

theorem state0018 :
    gammaState 15 = ⟨gamma0018, gamma0017, gamma0016⟩ := by
  rw [gammaState, state0017]
  rfl

def cert0018 : RowCertificate := ⟨⟨-16086352173417, 39⟩, [
  ⟨⟨-16086352173417, 40⟩, ⟨-16086351642661, 40⟩⟩,
  ⟨⟨-12823179308733, 43⟩, ⟨-12823178860327, 43⟩⟩,
  ⟨⟨-7269798381293, 44⟩, ⟨-1817449536701, 42⟩⟩,
  ⟨⟨-4887682995505, 45⟩, ⟨-4887682704187, 45⟩⟩,
  ⟨⟨-11916338509053, 48⟩, ⟨-11916337981729, 48⟩⟩,
  ⟨⟨-10190776003285, 50⟩, ⟨-10190775406179, 50⟩⟩,
  ⟨⟨-14283940310789, 54⟩, ⟨-14283939838923, 54⟩⟩,
  ⟨⟨-8850505421181, 61⟩, ⟨-8850505140109, 61⟩⟩,
]⟩

theorem row0018 : rowAtOK 18 cert0018 = true := by
  change rowOK 8 (gammaState 15).current cert0018.outer cert0018.brackets = true
  rw [state0018]
  decide +kernel

theorem order0018 : orderAtOK 18 cert0017 cert0018 = true := by decide +kernel

theorem pair0018 : OriginalPair 18 :=
  original_of_certificates (by decide) row0017 row0018 order0018

def gamma0019 : List ℤ := [
  1,
  524061,
  1116538943,
  208809453462,
  7998909599209,
  86213942954816,
  288505522761512,
  279378135286304,
  53928445496720,
]

theorem state0019 :
    gammaState 16 = ⟨gamma0019, gamma0018, gamma0017⟩ := by
  rw [gammaState, state0018]
  rfl

def cert0019 : RowCertificate := ⟨⟨-17223971789359, 41⟩, [
  ⟨⟨-17223971789359, 42⟩, ⟨-17223970960861, 42⟩⟩,
  ⟨⟨-14821281885699, 44⟩, ⟨-14821281338035, 44⟩⟩,
  ⟨⟨-2491162792051, 43⟩, ⟨-9964650592905, 45⟩⟩,
  ⟨⟨-7082320449911, 46⟩, ⟨-7082320044821, 46⟩⟩,
  ⟨⟨-17423473336181, 49⟩, ⟨-4355868143119, 47⟩⟩,
  ⟨⟨-1811786230581, 48⟩, ⟨-7247144494689, 50⟩⟩,
  ⟨⟨-9305256005473, 54⟩, ⟨-9305255692065, 54⟩⟩,
  ⟨⟨-4417979880847, 61⟩, ⟨-4417979737995, 61⟩⟩,
]⟩

theorem row0019 : rowAtOK 19 cert0019 = true := by
  change rowOK 8 (gammaState 16).current cert0019.outer cert0019.brackets = true
  rw [state0019]
  decide +kernel

theorem order0019 : orderAtOK 19 cert0018 cert0019 = true := by decide +kernel

theorem pair0019 : OriginalPair 19 :=
  original_of_certificates (by decide) row0018 row0019 order0019

def gamma0020 : List ℤ := [
  1,
  1048327,
  3387720165,
  884705852044,
  46478485055501,
  697519078673106,
  3409721611389384,
  5362473799598832,
  2221503151395792,
  107856890993440,
]

theorem state0020 :
    gammaState 17 = ⟨gamma0020, gamma0019, gamma0018⟩ := by
  rw [gammaState, state0019]
  rfl

def cert0020 : RowCertificate := ⟨⟨-4925692242287, 37⟩, [
  ⟨⟨-4925692242287, 38⟩, ⟨-9851384152743, 39⟩⟩,
  ⟨⟨-16061307051357, 43⟩, ⟨-501915828153, 38⟩⟩,
  ⟨⟨-9598540335621, 44⟩, ⟨-9598540042397, 44⟩⟩,
  ⟨⟨-7144453398815, 45⟩, ⟨-7144453015945, 45⟩⟩,
  ⟨⟨-5253967656979, 46⟩, ⟨-5253967364655, 46⟩⟩,
  ⟨⟨-12921570173355, 49⟩, ⟨-1615196201055, 46⟩⟩,
  ⟨⟨-10394949718627, 51⟩, ⟨-2598737274859, 49⟩⟩,
  ⟨⟨-3043163565491, 53⟩, ⟨-12172653703751, 55⟩⟩,
  ⟨⟨-2206366286675, 61⟩, ⟨-551591553519, 59⟩⟩,
]⟩

theorem row0020 : rowAtOK 20 cert0020 = true := by
  change rowOK 9 (gammaState 17).current cert0020.outer cert0020.brackets = true
  rw [state0020]
  decide +kernel

theorem order0020 : orderAtOK 20 cert0019 cert0020 = true := by decide +kernel

theorem pair0020 : OriginalPair 20 :=
  original_of_certificates (by decide) row0019 row0020 order0020

def gamma0021 : List ℤ := [
  1,
  2096880,
  10246475179,
  3703295776856,
  262845103854601,
  5367500737157616,
  36929417886615224,
  87959776473798944,
  65114487877716944,
  10097644471534208,
]

theorem state0021 :
    gammaState 18 = ⟨gamma0021, gamma0020, gamma0019⟩ := by
  rw [gammaState, state0020]
  rfl

def cert0021 : RowCertificate := ⟨⟨-10515719035717, 40⟩, [
  ⟨⟨-10515719035717, 41⟩, ⟨-10515718525295, 41⟩⟩,
  ⟨⟨-9325848002311, 43⟩, ⟨-2331461916669, 41⟩⟩,
  ⟨⟨-208212899863, 39⟩, ⟨-13325624872839, 45⟩⟩,
  ⟨⟨-10579325064135, 46⟩, ⟨-5289662262805, 45⟩⟩,
  ⟨⟨-15878129632429, 48⟩, ⟨-7939064382439, 47⟩⟩,
  ⟨⟨-4846339835491, 48⟩, ⟨-9692679246193, 49⟩⟩,
  ⟨⟨-15010626116973, 52⟩, ⟨-15010625665005, 52⟩⟩,
  ⟨⟨-499196587567, 51⟩, ⟨-15974290048013, 56⟩⟩,
  ⟨⟨-2204456872807, 62⟩, ⟨-4408913598065, 63⟩⟩,
]⟩

theorem row0021 : rowAtOK 21 cert0021 = true := by
  change rowOK 9 (gammaState 18).current cert0021.outer cert0021.brackets = true
  rw [state0021]
  decide +kernel

theorem order0021 : orderAtOK 21 cert0020 cert0021 = true := by decide +kernel

theorem pair0021 : OriginalPair 21 :=
  original_of_certificates (by decide) row0020 row0021 order0021

def gamma0022 : List ℤ := [
  1,
  4194008,
  30920772267,
  15355050540824,
  1454361194698281,
  39667367723580808,
  373225866495655016,
  1281276221982922208,
  1524297564047565776,
  502988345535954944,
  20195288943068416,
]

theorem state0022 :
    gammaState 19 = ⟨gamma0022, gamma0021, gamma0020⟩ := by
  rw [gammaState, state0021]
  rfl

def cert0022 : RowCertificate := ⟨⟨-11839827931133, 38⟩, [
  ⟨⟨-11839827931133, 39⟩, ⟨-5919913762975, 38⟩⟩,
  ⟨⟨-4904153642837, 41⟩, ⟨-4904153486673, 41⟩⟩,
  ⟨⟨-12162218990319, 44⟩, ⟨-12162218275725, 44⟩⟩,
  ⟨⟨-2422068221281, 43⟩, ⟨-9688272406143, 45⟩⟩,
  ⟨⟨-8022736969969, 46⟩, ⟨-8022736575995, 46⟩⟩,
  ⟨⟨-3042792315977, 46⟩, ⟨-12171168606363, 48⟩⟩,
  ⟨⟨-14675392259163, 50⟩, ⟨-14675391612083, 50⟩⟩,
  ⟨⟨-10896801324601, 52⟩, ⟨-10896800992621, 52⟩⟩,
  ⟨⟨-2627059152177, 54⟩, ⟨-5254118049279, 55⟩⟩,
  ⟨⟨-1101528787385, 62⟩, ⟨-8812229999299, 65⟩⟩,
]⟩

theorem row0022 : rowAtOK 22 cert0022 = true := by
  change rowOK 10 (gammaState 19).current cert0022.outer cert0022.brackets = true
  rw [state0022]
  decide +kernel

theorem order0022 : orderAtOK 22 cert0021 cert0022 = true := by decide +kernel

theorem pair0022 : OriginalPair 22 :=
  original_of_certificates (by decide) row0021 row0022 order0022

def gamma0023 : List ℤ := [
  1,
  8388287,
  93155464626,
  63192230233955,
  7906114440456641,
  283645405062064323,
  3567055327114688758,
  17009469332024805624,
  30332724187930488672,
  17737431195712503600,
  2259016502337056992,
]

theorem state0023 :
    gammaState 20 = ⟨gamma0023, gamma0022, gamma0021⟩ := by
  rw [gammaState, state0022]
  rfl

def cert0023 : RowCertificate := ⟨⟨-3149721592747, 38⟩, [
  ⟨⟨-3149721592747, 39⟩, ⟨-3149721438731, 39⟩⟩,
  ⟨⟨-5709987371461, 42⟩, ⟨-11419974339533, 43⟩⟩,
  ⟨⟨-17026719634889, 45⟩, ⟨-8513359381253, 44⟩⟩,
  ⟨⟨-909915133509, 42⟩, ⟨-3639660364851, 44⟩⟩,
  ⟨⟨-3098761840321, 45⟩, ⟨-3098761691907, 45⟩⟩,
  ⟨⟨-9438883722803, 48⟩, ⟨-9438883216025, 48⟩⟩,
  ⟨⟨-699575426511, 46⟩, ⟨-11193206326327, 50⟩⟩,
  ⟨⟨-15890790255819, 53⟩, ⟨-7945394800225, 52⟩⟩,
  ⟨⟨-13853453086865, 57⟩, ⟨-6926726198021, 56⟩⟩,
  ⟨⟨-2202026370653, 64⟩, ⟨-8808105178189, 66⟩⟩,
]⟩

theorem row0023 : rowAtOK 23 cert0023 = true := by
  change rowOK 10 (gammaState 20).current cert0023.outer cert0023.brackets = true
  rw [state0023]
  decide +kernel

theorem order0023 : orderAtOK 23 cert0022 cert0023 = true := by decide +kernel

theorem pair0023 : OriginalPair 23 :=
  original_of_certificates (by decide) row0022 row0023 order0023

def gamma0024 : List ℤ := [
  1,
  16776869,
  280315659424,
  258528564953391,
  42363272940846423,
  1973931217099472657,
  32567563887669113260,
  209625893269576494308,
  533380911787592809616,
  497175519269492309552,
  133828472751280803136,
  4518033004674113984,
]

theorem state0024 :
    gammaState 21 = ⟨gamma0024, gamma0023, gamma0022⟩ := by
  rw [gammaState, state0023]
  rfl

def cert0024 : RowCertificate := ⟨⟨-14008581189929, 38⟩, [
  ⟨⟨-14008581189929, 39⟩, ⟨-14008580704479, 39⟩⟩,
  ⟨⟨-11744907482055, 42⟩, ⟨-11744907107441, 42⟩⟩,
  ⟨⟨-7478974071875, 43⟩, ⟨-14957947289819, 44⟩⟩,
  ⟨⟨-6248381376775, 44⟩, ⟨-781047635785, 41⟩⟩,
  ⟨⟨-11209672913765, 46⟩, ⟨-11209672415403, 46⟩⟩,
  ⟨⟨-303636339185, 42⟩, ⟨-4858181198209, 46⟩⟩,
  ⟨⟨-115466107163, 42⟩, ⟨-14779660925245, 49⟩⟩,
  ⟨⟨-17179991482461, 51⟩, ⟨-17179990710229, 51⟩⟩,
  ⟨⟨-11628847948215, 53⟩, ⟨-11628847458663, 53⟩⟩,
  ⟨⟨-4573538003321, 56⟩, ⟨-9147075538675, 57⟩⟩,
  ⟨⟨-275157887145, 62⟩, ⟨-4402526039817, 66⟩⟩,
]⟩

theorem row0024 : rowAtOK 24 cert0024 = true := by
  change rowOK 11 (gammaState 21).current cert0024.outer cert0024.brackets = true
  rw [state0024]
  decide +kernel

theorem order0024 : orderAtOK 24 cert0023 cert0024 = true := by decide +kernel

theorem pair0024 : OriginalPair 24 :=
  original_of_certificates (by decide) row0023 row0024 order0024

def gamma0025 : List ℤ := [
  1,
  33554058,
  842775599240,
  1052739756698520,
  224327272732008051,
  13431162634677261342,
  286295489915779439596,
  2431368763062795004080,
  8508074735668845724880,
  11793032261823164965088,
  5588342137787950875456,
  595104186809499463168,
]

theorem state0025 :
    gammaState 22 = ⟨gamma0025, gamma0024, gamma0023⟩ := by
  rw [gammaState, state0024]
  rfl

def cert0025 : RowCertificate := ⟨⟨-1857717859559, 37⟩, [
  ⟨⟨-1857717859559, 38⟩, ⟨-7430871072635, 40⟩⟩,
  ⟨⟨-3423256113711, 41⟩, ⟨-13693023977683, 43⟩⟩,
  ⟨⟨-10529250520979, 44⟩, ⟨-10529250001849, 44⟩⟩,
  ⟨⟨-9486109789937, 45⟩, ⟨-4743054689573, 44⟩⟩,
  ⟨⟨-8589161145, 36⟩, ⟨-4397650316951, 45⟩⟩,
  ⟨⟨-3853596621973, 46⟩, ⟨-481699555315, 43⟩⟩,
  ⟨⟨-728893215707, 45⟩, ⟨-11662290826377, 49⟩⟩,
  ⟨⟨-6625996216939, 50⟩, ⟨-13251991831111, 51⟩⟩,
  ⟨⟨-17071170719047, 54⟩, ⟨-4267792496385, 52⟩⟩,
  ⟨⟨-1511974898257, 55⟩, ⟨-3023949637981, 56⟩⟩,
  ⟨⟨-8802785402271, 68⟩, ⟨-2200696272187, 66⟩⟩,
]⟩

theorem row0025 : rowAtOK 25 cert0025 = true := by
  change rowOK 11 (gammaState 22).current cert0025.outer cert0025.brackets = true
  rw [state0025]
  decide +kernel

theorem order0025 : orderAtOK 25 cert0024 cert0025 = true := by decide +kernel

theorem pair0025 : OriginalPair 25 :=
  original_of_certificates (by decide) row0024 row0025 order0025

def gamma0026 : List ℤ := [
  1,
  67108462,
  2532252554256,
  4270931138953000,
  1176387184457976435,
  89688628322160801882,
  2438372279430684168964,
  26819567480783914331152,
  125440151155757363284560,
  246143186173974636400800,
  184723315492612860360896,
  41349008019142815908352,
  1190208373618998926336,
]

theorem state0026 :
    gammaState 23 = ⟨gamma0026, gamma0025, gamma0024⟩ := by
  rw [gammaState, state0025]
  rfl

def cert0026 : RowCertificate := ⟨⟨-511178454121, 33⟩, [
  ⟨⟨-511178454121, 34⟩, ⟨-16357709959231, 39⟩⟩,
  ⟨⟨-6920368955685, 41⟩, ⟨-865046091823, 38⟩⟩,
  ⟨⟨-1124025784957, 40⟩, ⟨-8992205777285, 43⟩⟩,
  ⟨⟨-1944716976203, 42⟩, ⟨-972358444991, 41⟩⟩,
  ⟨⟨-7383310274419, 45⟩, ⟨-7383309971123, 45⟩⟩,
  ⟨⟨-7004623881479, 46⟩, ⟨-14009247173861, 47⟩⟩,
  ⟨⟨-12346195345129, 48⟩, ⟨-12346194773923, 48⟩⟩,
  ⟨⟨-578924818783, 45⟩, ⟨-9262796602871, 49⟩⟩,
  ⟨⟨-10265905698641, 51⟩, ⟨-5132952612861, 50⟩⟩,
  ⟨⟨-785111043629, 50⟩, ⟨-3140444036829, 52⟩⟩,
  ⟨⟨-4003351877757, 57⟩, ⟨-16013406651743, 59⟩⟩,
  ⟨⟨-8801097120451, 69⟩, ⟨-8801096802483, 69⟩⟩,
]⟩

theorem row0026 : rowAtOK 26 cert0026 = true := by
  change rowOK 12 (gammaState 23).current cert0026.outer cert0026.brackets = true
  rw [state0026]
  decide +kernel

theorem order0026 : orderAtOK 26 cert0025 cert0026 = true := by decide +kernel

theorem pair0026 : OriginalPair 26 :=
  original_of_certificates (by decide) row0025 row0026 order0026

def gamma0027 : List ℤ := [
  1,
  134217297,
  7605162917521,
  17276117247295040,
  6119711226902042250,
  589544223541395144687,
  20221415194592620248969,
  283661932816100196513852,
  1733481125330106916834180,
  4641823076562831839686160,
  5147256748269022101383856,
  2017468873814782934806592,
  182337101660137336720576,
]

theorem state0027 :
    gammaState 24 = ⟨gamma0027, gamma0026, gamma0025⟩ := by
  rw [gammaState, state0026]
  rfl

def cert0027 : RowCertificate := ⟨⟨-8652236457623, 39⟩, [
  ⟨⟨-8652236457623, 40⟩, ⟨-33797796991, 32⟩⟩,
  ⟨⟨-16145124586181, 43⟩, ⟨-16145124029197, 43⟩⟩,
  ⟨⟨-12708005379631, 44⟩, ⟨-12708004771333, 44⟩⟩,
  ⟨⟨-371751111609, 40⟩, ⟨-11896035084255, 45⟩⟩,
  ⟨⟨-11716844325917, 46⟩, ⟨-5858421931633, 45⟩⟩,
  ⟨⟨-11292291501697, 47⟩, ⟨-5646145517313, 46⟩⟩,
  ⟨⟨-9968766328625, 48⟩, ⟨-9968765868787, 48⟩⟩,
  ⟨⟨-7397540415689, 49⟩, ⟨-14795080033115, 50⟩⟩,
  ⟨⟨-3990705973903, 50⟩, ⟨-15962823150439, 52⟩⟩,
  ⟨⟨-2315783605063, 52⟩, ⟨-36184117211, 46⟩⟩,
  ⟨⟨-10610094206881, 59⟩, ⟨-10610093624785, 59⟩⟩,
  ⟨⟨-2199959474097, 68⟩, ⟨-4399918787027, 69⟩⟩,
]⟩

theorem row0027 : rowAtOK 27 cert0027 = true := by
  change rowOK 12 (gammaState 24).current cert0027.outer cert0027.brackets = true
  rw [state0027]
  decide +kernel

theorem order0027 : orderAtOK 27 cert0026 cert0027 = true := by decide +kernel

theorem pair0027 : OriginalPair 27 :=
  original_of_certificates (by decide) row0026 row0027 order0027

theorem range0012_0027 {n : ℕ} (lo : 12 ≤ n) (hi : n ≤ 27) : OriginalPair n := by
  interval_cases n
  · exact pair0012
  · exact pair0013
  · exact pair0014
  · exact pair0015
  · exact pair0016
  · exact pair0017
  · exact pair0018
  · exact pair0019
  · exact pair0020
  · exact pair0021
  · exact pair0022
  · exact pair0023
  · exact pair0024
  · exact pair0025
  · exact pair0026
  · exact pair0027

#print axioms range0012_0027

end LongCycleFinite.K3.DataExplicit
