import GMUBinaryPartitions.Check

/-!
# Values of `b m n`, checked by the kernel

Each value is entry `n` of `bList m N L` (sound by `bList_sound`, since `L < 2^N`), evaluated by
`decide +kernel`: the kernel reduces the list computation itself, using its GMP arithmetic on
natural-number literals. No `native_decide`.
-/

namespace GMU

set_option maxRecDepth 100000

/-- `b₁(4) = 4`. -/
theorem b_1_4 : b 1 4 = 4 := by
  rw [← bList_sound 1 5 16 4 (by norm_num) (by norm_num)]
  exact_mod_cast (show get0 (bList 1 5 16) 4 = 4 by decide +kernel)

/-- `b₁(16) = 36`. -/
theorem b_1_16 : b 1 16 = 36 := by
  rw [← bList_sound 1 5 16 16 (by norm_num) (by norm_num)]
  exact_mod_cast (show get0 (bList 1 5 16) 16 = 36 by decide +kernel)

/-- `b₁(64) = 1828`. -/
theorem b_1_64 : b 1 64 = 1828 := by
  rw [← bList_sound 1 7 64 64 (by norm_num) (by norm_num)]
  exact_mod_cast (show get0 (bList 1 7 64) 64 = 1828 by decide +kernel)

/-- `b₇(16) = 5586084`. -/
theorem b_7_16 : b 7 16 = 5586084 := by
  rw [← bList_sound 7 5 16 16 (by norm_num) (by norm_num)]
  exact_mod_cast (show get0 (bList 7 5 16) 16 = 5586084 by decide +kernel)

/-- `b₇(64) = 346264420529188`. -/
theorem b_7_64 : b 7 64 = 346264420529188 := by
  rw [← bList_sound 7 7 64 64 (by norm_num) (by norm_num)]
  exact_mod_cast (show get0 (bList 7 7 64) 64 = 346264420529188 by decide +kernel)

/-- `b₁₅(32) = 1199991982437540`. -/
theorem b_15_32 : b 15 32 = 1199991982437540 := by
  rw [← bList_sound 15 6 32 32 (by norm_num) (by norm_num)]
  exact_mod_cast (show get0 (bList 15 6 32) 32 = 1199991982437540 by decide +kernel)

/-- `b₁₅(128) = 66243595743894015443321698798500`. -/
theorem b_15_128 : b 15 128 = 66243595743894015443321698798500 := by
  rw [← bList_sound 15 8 128 128 (by norm_num) (by norm_num)]
  exact_mod_cast (show get0 (bList 15 8 128) 128 = 66243595743894015443321698798500 by
    decide +kernel)

/-- `b₃₁(64) = 72767465226443722145355896761508`. -/
theorem b_31_64 : b 31 64 = 72767465226443722145355896761508 := by
  rw [← bList_sound 31 7 64 64 (by norm_num) (by norm_num)]
  exact_mod_cast (show get0 (bList 31 7 64) 64 = 72767465226443722145355896761508 by
    decide +kernel)

/-- `b₃₁(256)`, a 67-digit number. -/
theorem b_31_256 : b 31 256 =
    3052369194453650254501535715298757541552490784809850699183520381604 := by
  rw [← bList_sound 31 9 256 256 (by norm_num) (by norm_num)]
  exact_mod_cast (show get0 (bList 31 9 256) 256 =
    3052369194453650254501535715298757541552490784809850699183520381604 by decide +kernel)

end GMU
