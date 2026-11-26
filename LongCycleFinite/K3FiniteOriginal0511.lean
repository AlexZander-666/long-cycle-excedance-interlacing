import LongCycleFinite.K3Prefix255
import LongCycleFinite.K3PairsNatural.Rows0259
import LongCycleFinite.K3PairsNatural.Rows0263
import LongCycleFinite.K3PairsNatural.Rows0267
import LongCycleFinite.K3PairsNatural.Rows0271
import LongCycleFinite.K3PairsNatural.Rows0275
import LongCycleFinite.K3PairsNatural.Rows0279
import LongCycleFinite.K3PairsNatural.Rows0283
import LongCycleFinite.K3PairsNatural.Rows0287
import LongCycleFinite.K3PairsNatural.Rows0291
import LongCycleFinite.K3PairsNatural.Rows0295
import LongCycleFinite.K3PairsNatural.Rows0299
import LongCycleFinite.K3PairsNatural.Rows0303
import LongCycleFinite.K3PairsNatural.Rows0307
import LongCycleFinite.K3PairsNatural.Rows0311
import LongCycleFinite.K3PairsNatural.Rows0315
import LongCycleFinite.K3PairsNatural.Rows0319
import LongCycleFinite.K3PairsNatural.Rows0323
import LongCycleFinite.K3PairsNatural.Rows0327
import LongCycleFinite.K3PairsNatural.Rows0331
import LongCycleFinite.K3PairsNatural.Rows0335
import LongCycleFinite.K3PairsNatural.Rows0339
import LongCycleFinite.K3PairsNatural.Rows0343
import LongCycleFinite.K3PairsNatural.Rows0347
import LongCycleFinite.K3PairsNatural.Rows0351
import LongCycleFinite.K3PairsNatural.Rows0355
import LongCycleFinite.K3PairsNatural.Rows0359
import LongCycleFinite.K3PairsNatural.Rows0363
import LongCycleFinite.K3PairsNatural.Rows0367
import LongCycleFinite.K3PairsNatural.Rows0371
import LongCycleFinite.K3PairsNatural.Rows0375
import LongCycleFinite.K3PairsNatural.Rows0379
import LongCycleFinite.K3PairsNatural.Rows0383
import LongCycleFinite.K3PairsNatural.Rows0387
import LongCycleFinite.K3PairsNatural.Rows0391
import LongCycleFinite.K3PairsNatural.Rows0395
import LongCycleFinite.K3PairsNatural.Rows0399
import LongCycleFinite.K3PairsNatural.Rows0403
import LongCycleFinite.K3PairsNatural.Rows0407
import LongCycleFinite.K3PairsNatural.Rows0411
import LongCycleFinite.K3PairsNatural.Rows0415
import LongCycleFinite.K3PairsNatural.Rows0419
import LongCycleFinite.K3PairsNatural.Rows0423
import LongCycleFinite.K3PairsNatural.Rows0427
import LongCycleFinite.K3PairsNatural.Rows0431
import LongCycleFinite.K3PairsNatural.Rows0435
import LongCycleFinite.K3PairsNatural.Rows0439
import LongCycleFinite.K3PairsNatural.Rows0443
import LongCycleFinite.K3PairsNatural.Rows0447
import LongCycleFinite.K3PairsNatural.Rows0451
import LongCycleFinite.K3PairsNatural.Rows0455
import LongCycleFinite.K3PairsNatural.Rows0459
import LongCycleFinite.K3PairsNatural.Rows0463
import LongCycleFinite.K3PairsNatural.Rows0467
import LongCycleFinite.K3PairsNatural.Rows0471
import LongCycleFinite.K3PairsNatural.Rows0475
import LongCycleFinite.K3PairsNatural.Rows0479
import LongCycleFinite.K3PairsNatural.Rows0483
import LongCycleFinite.K3PairsNatural.Rows0487
import LongCycleFinite.K3PairsNatural.Rows0491
import LongCycleFinite.K3PairsNatural.Rows0495
import LongCycleFinite.K3PairsNatural.Rows0499
import LongCycleFinite.K3PairsNatural.Rows0503
import LongCycleFinite.K3PairsNatural.Rows0507
import LongCycleFinite.K3PairsNatural.Rows0511

namespace LongCycleFinite.K3

set_option warningAsError true

theorem mergedRange0256_0271 {n : ℕ} (lo : 256 ≤ n) (hi : n ≤ 271) : OriginalPair n := by
  by_cases h259 : n ≤ 259
  · exact DataExplicit.range0256_0259 lo h259
  by_cases h263 : n ≤ 263
  · exact DataExplicit.range0260_0263 (by omega) h263
  by_cases h267 : n ≤ 267
  · exact DataExplicit.range0264_0267 (by omega) h267
  exact DataExplicit.range0268_0271 (by omega) hi

#print axioms mergedRange0256_0271

theorem mergedRange0272_0287 {n : ℕ} (lo : 272 ≤ n) (hi : n ≤ 287) : OriginalPair n := by
  by_cases h275 : n ≤ 275
  · exact DataExplicit.range0272_0275 lo h275
  by_cases h279 : n ≤ 279
  · exact DataExplicit.range0276_0279 (by omega) h279
  by_cases h283 : n ≤ 283
  · exact DataExplicit.range0280_0283 (by omega) h283
  exact DataExplicit.range0284_0287 (by omega) hi

#print axioms mergedRange0272_0287

theorem mergedRange0288_0303 {n : ℕ} (lo : 288 ≤ n) (hi : n ≤ 303) : OriginalPair n := by
  by_cases h291 : n ≤ 291
  · exact DataExplicit.range0288_0291 lo h291
  by_cases h295 : n ≤ 295
  · exact DataExplicit.range0292_0295 (by omega) h295
  by_cases h299 : n ≤ 299
  · exact DataExplicit.range0296_0299 (by omega) h299
  exact DataExplicit.range0300_0303 (by omega) hi

#print axioms mergedRange0288_0303

theorem mergedRange0304_0319 {n : ℕ} (lo : 304 ≤ n) (hi : n ≤ 319) : OriginalPair n := by
  by_cases h307 : n ≤ 307
  · exact DataExplicit.range0304_0307 lo h307
  by_cases h311 : n ≤ 311
  · exact DataExplicit.range0308_0311 (by omega) h311
  by_cases h315 : n ≤ 315
  · exact DataExplicit.range0312_0315 (by omega) h315
  exact DataExplicit.range0316_0319 (by omega) hi

#print axioms mergedRange0304_0319

theorem mergedRange0320_0335 {n : ℕ} (lo : 320 ≤ n) (hi : n ≤ 335) : OriginalPair n := by
  by_cases h323 : n ≤ 323
  · exact DataExplicit.range0320_0323 lo h323
  by_cases h327 : n ≤ 327
  · exact DataExplicit.range0324_0327 (by omega) h327
  by_cases h331 : n ≤ 331
  · exact DataExplicit.range0328_0331 (by omega) h331
  exact DataExplicit.range0332_0335 (by omega) hi

#print axioms mergedRange0320_0335

theorem mergedRange0336_0351 {n : ℕ} (lo : 336 ≤ n) (hi : n ≤ 351) : OriginalPair n := by
  by_cases h339 : n ≤ 339
  · exact DataExplicit.range0336_0339 lo h339
  by_cases h343 : n ≤ 343
  · exact DataExplicit.range0340_0343 (by omega) h343
  by_cases h347 : n ≤ 347
  · exact DataExplicit.range0344_0347 (by omega) h347
  exact DataExplicit.range0348_0351 (by omega) hi

#print axioms mergedRange0336_0351

theorem mergedRange0352_0367 {n : ℕ} (lo : 352 ≤ n) (hi : n ≤ 367) : OriginalPair n := by
  by_cases h355 : n ≤ 355
  · exact DataExplicit.range0352_0355 lo h355
  by_cases h359 : n ≤ 359
  · exact DataExplicit.range0356_0359 (by omega) h359
  by_cases h363 : n ≤ 363
  · exact DataExplicit.range0360_0363 (by omega) h363
  exact DataExplicit.range0364_0367 (by omega) hi

#print axioms mergedRange0352_0367

theorem mergedRange0368_0383 {n : ℕ} (lo : 368 ≤ n) (hi : n ≤ 383) : OriginalPair n := by
  by_cases h371 : n ≤ 371
  · exact DataExplicit.range0368_0371 lo h371
  by_cases h375 : n ≤ 375
  · exact DataExplicit.range0372_0375 (by omega) h375
  by_cases h379 : n ≤ 379
  · exact DataExplicit.range0376_0379 (by omega) h379
  exact DataExplicit.range0380_0383 (by omega) hi

#print axioms mergedRange0368_0383

theorem mergedRange0384_0399 {n : ℕ} (lo : 384 ≤ n) (hi : n ≤ 399) : OriginalPair n := by
  by_cases h387 : n ≤ 387
  · exact DataExplicit.range0384_0387 lo h387
  by_cases h391 : n ≤ 391
  · exact DataExplicit.range0388_0391 (by omega) h391
  by_cases h395 : n ≤ 395
  · exact DataExplicit.range0392_0395 (by omega) h395
  exact DataExplicit.range0396_0399 (by omega) hi

#print axioms mergedRange0384_0399

theorem mergedRange0400_0415 {n : ℕ} (lo : 400 ≤ n) (hi : n ≤ 415) : OriginalPair n := by
  by_cases h403 : n ≤ 403
  · exact DataExplicit.range0400_0403 lo h403
  by_cases h407 : n ≤ 407
  · exact DataExplicit.range0404_0407 (by omega) h407
  by_cases h411 : n ≤ 411
  · exact DataExplicit.range0408_0411 (by omega) h411
  exact DataExplicit.range0412_0415 (by omega) hi

#print axioms mergedRange0400_0415

theorem mergedRange0416_0431 {n : ℕ} (lo : 416 ≤ n) (hi : n ≤ 431) : OriginalPair n := by
  by_cases h419 : n ≤ 419
  · exact DataExplicit.range0416_0419 lo h419
  by_cases h423 : n ≤ 423
  · exact DataExplicit.range0420_0423 (by omega) h423
  by_cases h427 : n ≤ 427
  · exact DataExplicit.range0424_0427 (by omega) h427
  exact DataExplicit.range0428_0431 (by omega) hi

#print axioms mergedRange0416_0431

theorem mergedRange0432_0447 {n : ℕ} (lo : 432 ≤ n) (hi : n ≤ 447) : OriginalPair n := by
  by_cases h435 : n ≤ 435
  · exact DataExplicit.range0432_0435 lo h435
  by_cases h439 : n ≤ 439
  · exact DataExplicit.range0436_0439 (by omega) h439
  by_cases h443 : n ≤ 443
  · exact DataExplicit.range0440_0443 (by omega) h443
  exact DataExplicit.range0444_0447 (by omega) hi

#print axioms mergedRange0432_0447

theorem mergedRange0448_0463 {n : ℕ} (lo : 448 ≤ n) (hi : n ≤ 463) : OriginalPair n := by
  by_cases h451 : n ≤ 451
  · exact DataExplicit.range0448_0451 lo h451
  by_cases h455 : n ≤ 455
  · exact DataExplicit.range0452_0455 (by omega) h455
  by_cases h459 : n ≤ 459
  · exact DataExplicit.range0456_0459 (by omega) h459
  exact DataExplicit.range0460_0463 (by omega) hi

#print axioms mergedRange0448_0463

theorem mergedRange0464_0479 {n : ℕ} (lo : 464 ≤ n) (hi : n ≤ 479) : OriginalPair n := by
  by_cases h467 : n ≤ 467
  · exact DataExplicit.range0464_0467 lo h467
  by_cases h471 : n ≤ 471
  · exact DataExplicit.range0468_0471 (by omega) h471
  by_cases h475 : n ≤ 475
  · exact DataExplicit.range0472_0475 (by omega) h475
  exact DataExplicit.range0476_0479 (by omega) hi

#print axioms mergedRange0464_0479

theorem mergedRange0480_0495 {n : ℕ} (lo : 480 ≤ n) (hi : n ≤ 495) : OriginalPair n := by
  by_cases h483 : n ≤ 483
  · exact DataExplicit.range0480_0483 lo h483
  by_cases h487 : n ≤ 487
  · exact DataExplicit.range0484_0487 (by omega) h487
  by_cases h491 : n ≤ 491
  · exact DataExplicit.range0488_0491 (by omega) h491
  exact DataExplicit.range0492_0495 (by omega) hi

#print axioms mergedRange0480_0495

theorem mergedRange0496_0511 {n : ℕ} (lo : 496 ≤ n) (hi : n ≤ 511) : OriginalPair n := by
  by_cases h499 : n ≤ 499
  · exact DataExplicit.range0496_0499 lo h499
  by_cases h503 : n ≤ 503
  · exact DataExplicit.range0500_0503 (by omega) h503
  by_cases h507 : n ≤ 507
  · exact DataExplicit.range0504_0507 (by omega) h507
  exact DataExplicit.range0508_0511 (by omega) hi

#print axioms mergedRange0496_0511

theorem finite_original_4_511 {n : ℕ} (lo : 4 ≤ n) (hi : n ≤ 511) : OriginalPair n := by
  by_cases h255 : n ≤ 255
  · exact finite_original_4_255 lo h255
  by_cases h271 : n ≤ 271
  · exact mergedRange0256_0271 (by omega) h271
  by_cases h287 : n ≤ 287
  · exact mergedRange0272_0287 (by omega) h287
  by_cases h303 : n ≤ 303
  · exact mergedRange0288_0303 (by omega) h303
  by_cases h319 : n ≤ 319
  · exact mergedRange0304_0319 (by omega) h319
  by_cases h335 : n ≤ 335
  · exact mergedRange0320_0335 (by omega) h335
  by_cases h351 : n ≤ 351
  · exact mergedRange0336_0351 (by omega) h351
  by_cases h367 : n ≤ 367
  · exact mergedRange0352_0367 (by omega) h367
  by_cases h383 : n ≤ 383
  · exact mergedRange0368_0383 (by omega) h383
  by_cases h399 : n ≤ 399
  · exact mergedRange0384_0399 (by omega) h399
  by_cases h415 : n ≤ 415
  · exact mergedRange0400_0415 (by omega) h415
  by_cases h431 : n ≤ 431
  · exact mergedRange0416_0431 (by omega) h431
  by_cases h447 : n ≤ 447
  · exact mergedRange0432_0447 (by omega) h447
  by_cases h463 : n ≤ 463
  · exact mergedRange0448_0463 (by omega) h463
  by_cases h479 : n ≤ 479
  · exact mergedRange0464_0479 (by omega) h479
  by_cases h495 : n ≤ 495
  · exact mergedRange0480_0495 (by omega) h495
  exact mergedRange0496_0511 (by omega) hi

#print axioms finite_original_4_511

end LongCycleFinite.K3
