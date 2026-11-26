import GMUBinaryPartitions.Main

/-!
# The `m = 6` witness, by `native_decide`

`b₆₃(512)` takes the kernel's list reduction more than six minutes and 8 GB (we stopped it), so
the two `m = 6` values are evaluated with `native_decide`, through the same checker `bList`,
whose soundness `bList_sound` is proved from the standard axioms. These are the only two
`native_decide` calls in the package; the headline `gmu_conjecture_5_6_false` and the `m = 1, 3,
4, 5` theorems do not use them.
-/

namespace GMU

/-- `b₆₃(128)`, a 66-digit number. -/
theorem b_63_128 : b 63 128 =
    365620611553381231445218127332308097349918064875247599914556431524 := by
  rw [← bList_sound 63 8 128 128 (by norm_num) (by norm_num)]
  exact_mod_cast (show get0 (bList 63 8 128) 128 =
    365620611553381231445218127332308097349918064875247599914556431524 by native_decide)

/-- `b₆₃(512)`, a 136-digit number. -/
theorem b_63_512 : b 63 512 =
    8677085767182302653082053495178845797116433918467639429886379217785248109664564856573200989059500303674665939398661848015590457004243108 := by
  rw [← bList_sound 63 10 512 512 (by norm_num) (by norm_num)]
  exact_mod_cast (show get0 (bList 63 10 512) 512 =
    8677085767182302653082053495178845797116433918467639429886379217785248109664564856573200989059500303674665939398661848015590457004243108 by
    native_decide)

/-- `m = 6, k = 8, n = 1`: `b₆₃(512) − b₆₃(128)` has 2-adic valuation `10 < 14`. -/
theorem gmu_conjecture_5_6_fails_at_m6 :
    ¬ b (2 ^ 6 - 1) (2 ^ (8 + 1) * 1) ≡ b (2 ^ 6 - 1) (2 ^ (8 - 1) * 1)
      [ZMOD 2 ^ (4 * ((8 + 1) / 2) - 2)] := by
  show ¬ b 63 512 ≡ b 63 128 [ZMOD 2 ^ 14]
  rw [b_63_512, b_63_128, Int.ModEq]; norm_num

end GMU
