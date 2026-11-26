import Cramer.Small

/-!
# The range `2 ≤ x < 6.4·10^7`: a prime in `(x, x + (3/2)√x log x]` by a checked prime chain

`primeChain32` is a list of 696 primes `2 = q₀ < q₁ < … < q_695 = 64165103`, each paired with
`k = ⌊8 log₂ q⌋`. `chainOK32` checks `2^k ≤ q_i^8` and
`(q_{i+1} − q_i)² · 256 · 10⁶ ≤ 9 q_i (693 k)²`, which gives
`q_{i+1} − q_i ≤ (3/2) √q_i (0.693 k / 8) ≤ (3/2) √q_i log q_i` (`gap_le_32`). The check is
evaluated by `decide` in the kernel (no `native_decide`); primality of each entry is proved by
`norm_num`, in chunks of 40. The list was generated greedily (largest admissible prime at each
step).
-/

namespace Cramer

open Real

/-- Chunk 0 of the chain. -/
def chain32Chunk0 : List (ℕ × ℕ) := [(2, 8), (3, 12), (5, 18), (7, 22), (13, 29), (23, 36), (43, 43), (79, 50), (131, 56), (211, 61), (317, 66), (467, 70), (661, 74), (907, 78), (1201, 81), (1559, 84), (1987, 87), (2477, 90), (3049, 92), (3709, 94), (4451, 96), (5281, 98), (6203, 100), (7219, 102), (8329, 104), (9551, 105), (10883, 107), (12329, 108), (13883, 110), (15559, 111), (17351, 112), (19267, 113), (21283, 115), (23459, 116), (25763, 117), (28201, 118), (30773, 119), (33479, 120), (36319, 121), (39313, 122)]

theorem chain32_prime_0 : ∀ e ∈ chain32Chunk0, e.1.Prime := by
  simp only [chain32Chunk0, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Chunk 1 of the chain. -/
def chain32Chunk1 : List (ℕ × ℕ) := [(42451, 122), (45707, 123), (49123, 124), (52691, 125), (56417, 126), (60293, 127), (64333, 127), (68507, 128), (72859, 129), (77383, 129), (82039, 130), (86869, 131), (91873, 131), (97021, 132), (102359, 133), (107881, 133), (113557, 134), (119419, 134), (125429, 135), (131641, 136), (138041, 136), (144593, 137), (151357, 137), (158269, 138), (165397, 138), (172687, 139), (180181, 139), (187843, 140), (195709, 140), (203713, 141), (211979, 141), (220411, 141), (229003, 142), (237821, 142), (246817, 143), (256033, 143), (265427, 144), (275059, 144), (284857, 144), (294829, 145)]

theorem chain32_prime_1 : ∀ e ∈ chain32Chunk1, e.1.Prime := by
  simp only [chain32Chunk1, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Chunk 2 of the chain. -/
def chain32Chunk2 : List (ℕ × ℕ) := [(305047, 145), (315451, 146), (326101, 146), (336929, 146), (347933, 147), (359171, 147), (370613, 147), (382241, 148), (394129, 148), (406183, 149), (418511, 149), (431029, 149), (443731, 150), (456697, 150), (469849, 150), (483179, 151), (496817, 151), (510619, 151), (524633, 152), (538931, 152), (553417, 152), (568109, 152), (582983, 153), (598159, 153), (613523, 153), (629081, 154), (644951, 154), (661019, 154), (677239, 154), (693701, 155), (710473, 155), (727427, 155), (744599, 156), (762061, 156), (779749, 156), (797647, 156), (815729, 157), (834151, 157), (852769, 157), (871597, 157)]

theorem chain32_prime_2 : ∀ e ∈ chain32Chunk2, e.1.Prime := by
  simp only [chain32Chunk2, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Chunk 3 of the chain. -/
def chain32Chunk3 : List (ℕ × ℕ) := [(890609, 158), (909977, 158), (929561, 158), (949307, 158), (969301, 159), (989641, 159), (1010179, 159), (1030933, 159), (1051903, 160), (1073221, 160), (1094747, 160), (1116499, 160), (1138457, 160), (1160639, 161), (1183163, 161), (1205903, 161), (1228861, 161), (1252049, 162), (1275601, 162), (1299367, 162), (1323349, 162), (1347557, 162), (1371991, 163), (1396789, 163), (1421813, 163), (1447067, 163), (1472543, 163), (1498229, 164), (1524293, 164), (1550597, 164), (1577119, 164), (1603871, 164), (1630843, 165), (1658213, 165), (1685821, 165), (1713641, 165), (1741699, 165), (1769987, 166), (1798679, 166), (1827593, 166)]

theorem chain32_prime_3 : ∀ e ∈ chain32Chunk3, e.1.Prime := by
  simp only [chain32Chunk3, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Chunk 4 of the chain. -/
def chain32Chunk4 : List (ℕ × ℕ) := [(1856747, 166), (1886119, 166), (1915741, 166), (1945579, 167), (1975823, 167), (2006317, 167), (2037043, 167), (2067997, 167), (2099197, 168), (2130809, 168), (2162663, 168), (2194757, 168), (2227087, 168), (2259643, 168), (2292457, 169), (2325703, 169), (2359187, 169), (2392891, 169), (2426833, 169), (2461037, 169), (2495473, 170), (2530361, 170), (2565463, 170), (2600837, 170), (2636453, 170), (2672317, 170), (2708417, 170), (2744761, 171), (2781521, 171), (2818577, 171), (2855873, 171), (2893421, 171), (2931211, 171), (2969251, 172), (3007747, 172), (3046501, 172), (3085499, 172), (3124747, 172), (3164251, 172), (3203999, 172)]

theorem chain32_prime_4 : ∀ e ∈ chain32Chunk4, e.1.Prime := by
  simp only [chain32Chunk4, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Chunk 5 of the chain. -/
def chain32Chunk5 : List (ℕ × ℕ) := [(3244001, 173), (3284483, 173), (3325219, 173), (3366203, 173), (3407431, 173), (3448897, 173), (3490639, 173), (3532637, 174), (3575119, 174), (3617857, 174), (3660847, 174), (3704087, 174), (3747589, 174), (3791341, 174), (3835361, 174), (3879607, 175), (3924353, 175), (3969391, 175), (4014691, 175), (4060249, 175), (4106059, 175), (4152119, 175), (4198433, 176), (4245289, 176), (4292383, 176), (4339757, 176), (4387391, 176), (4435279, 176), (4483433, 176), (4531847, 176), (4580503, 177), (4629721, 177), (4679203, 177), (4728947, 177), (4778953, 177), (4829219, 177), (4879753, 177), (4930553, 177), (4981609, 177), (5032939, 178)]

theorem chain32_prime_5 : ∀ e ∈ chain32Chunk5, e.1.Prime := by
  simp only [chain32Chunk5, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Chunk 6 of the chain. -/
def chain32Chunk6 : List (ℕ × ℕ) := [(5084813, 178), (5136947, 178), (5189363, 178), (5242021, 178), (5294969, 178), (5348159, 178), (5401633, 178), (5455379, 179), (5509687, 179), (5564269, 179), (5619109, 179), (5674241, 179), (5729609, 179), (5785271, 179), (5841211, 179), (5897417, 179), (5953889, 180), (6010957, 180), (6068273, 180), (6125887, 180), (6183761, 180), (6241913, 180), (6300341, 180), (6359047, 180), (6417947, 180), (6477199, 181), (6537053, 181), (6597179, 181), (6657583, 181), (6718259, 181), (6779207, 181), (6840439, 181), (6901919, 181), (6963703, 181), (7025737, 181), (7088069, 182), (7151021, 182), (7214257, 182), (7277761, 182), (7341557, 182)]

theorem chain32_prime_6 : ∀ e ∈ chain32Chunk6, e.1.Prime := by
  simp only [chain32Chunk6, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Chunk 7 of the chain. -/
def chain32Chunk7 : List (ℕ × ℕ) := [(7405633, 182), (7469951, 182), (7534511, 182), (7599419, 182), (7664611, 182), (7730057, 183), (7796161, 183), (7862539, 183), (7929199, 183), (7996133, 183), (8063371, 183), (8130883, 183), (8198683, 183), (8266759, 183), (8335123, 183), (8403761, 184), (8473051, 184), (8542643, 184), (8612503, 184), (8682659, 184), (8753089, 184), (8823823, 184), (8894843, 184), (8966137, 184), (9037723, 184), (9109591, 184), (9181727, 185), (9254549, 185), (9327671, 185), (9401083, 185), (9474779, 185), (9548761, 185), (9623023, 185), (9697579, 185), (9772423, 185), (9847549, 185), (9922967, 185), (9998689, 186), (10075097, 186), (10151797, 186)]

theorem chain32_prime_7 : ∀ e ∈ chain32Chunk7, e.1.Prime := by
  simp only [chain32Chunk7, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Chunk 8 of the chain. -/
def chain32Chunk8 : List (ℕ × ℕ) := [(10228769, 186), (10306057, 186), (10383629, 186), (10461499, 186), (10539629, 186), (10618063, 186), (10696799, 186), (10775803, 186), (10855123, 186), (10934719, 187), (11015057, 187), (11095697, 187), (11176621, 187), (11257843, 187), (11339311, 187), (11421121, 187), (11503213, 187), (11585617, 187), (11668309, 187), (11751277, 187), (11834569, 187), (11918087, 188), (12002413, 188), (12087013, 188), (12171937, 188), (12257129, 188), (12342637, 188), (12428431, 188), (12514517, 188), (12600923, 188), (12687613, 188), (12774617, 188), (12861889, 188), (12949471, 189), (13037839, 189), (13126507, 189), (13215479, 189), (13304747, 189), (13394321, 189), (13484189, 189)]

theorem chain32_prime_8 : ∀ e ∈ chain32Chunk8, e.1.Prime := by
  simp only [chain32Chunk8, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Chunk 9 of the chain. -/
def chain32Chunk9 : List (ℕ × ℕ) := [(13574357, 189), (13664837, 189), (13755617, 189), (13846699, 189), (13938061, 189), (14029727, 189), (14121689, 190), (14214463, 190), (14307539, 190), (14400899, 190), (14494583, 190), (14588573, 190), (14682869, 190), (14777461, 190), (14872337, 190), (14967529, 190), (15063023, 190), (15158839, 190), (15254959, 190), (15351383, 190), (15448073, 191), (15545609, 191), (15643457, 191), (15741601, 191), (15840067, 191), (15938837, 191), (16037873, 191), (16137259, 191), (16236953, 191), (16336939, 191), (16437251, 191), (16537867, 191), (16638793, 191), (16740023, 191), (16841563, 192), (16943929, 192), (17046613, 192), (17149607, 192), (17252899, 192), (17356523, 192)]

theorem chain32_prime_9 : ∀ e ∈ chain32Chunk9, e.1.Prime := by
  simp only [chain32Chunk9, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Chunk 10 of the chain. -/
def chain32Chunk10 : List (ℕ × ℕ) := [(17460437, 192), (17564681, 192), (17669233, 192), (17774051, 192), (17879227, 192), (17984693, 192), (18090491, 192), (18196589, 192), (18303001, 193), (18410279, 193), (18517853, 193), (18625753, 193), (18733973, 193), (18842501, 193), (18951329, 193), (19060493, 193), (19169947, 193), (19279709, 193), (19389793, 193), (19500211, 193), (19610917, 193), (19721963, 193), (19833323, 193), (19944973, 193), (20056961, 194), (20169841, 194), (20283037, 194), (20396533, 194), (20510353, 194), (20624497, 194), (20738957, 194), (20853719, 194), (20968817, 194), (21084227, 194), (21199973, 194), (21316037, 194), (21432413, 194), (21549109, 194), (21666121, 194), (21783451, 195)]

theorem chain32_prime_10 : ∀ e ∈ chain32Chunk10, e.1.Prime := by
  simp only [chain32Chunk10, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Chunk 11 of the chain. -/
def chain32Chunk11 : List (ℕ × ℕ) := [(21901709, 195), (22020283, 195), (22139141, 195), (22258343, 195), (22377871, 195), (22497721, 195), (22617899, 195), (22738369, 195), (22859149, 195), (22980271, 195), (23101709, 195), (23223467, 195), (23345563, 195), (23467943, 195), (23590687, 195), (23713721, 195), (23837089, 196), (23961409, 196), (24086047, 196), (24211007, 196), (24336317, 196), (24461951, 196), (24587903, 196), (24714181, 196), (24840787, 196), (24967687, 196), (25094933, 196), (25222471, 196), (25350371, 196), (25478587, 196), (25607107, 196), (25735981, 196), (25865173, 196), (25994693, 197), (26125181, 197), (26256017, 197), (26387177, 197), (26518649, 197), (26650453, 197), (26782597, 197)]

theorem chain32_prime_11 : ∀ e ∈ chain32Chunk11, e.1.Prime := by
  simp only [chain32Chunk11, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Chunk 12 of the chain. -/
def chain32Chunk12 : List (ℕ × ℕ) := [(26915069, 197), (27047863, 197), (27180973, 197), (27314423, 197), (27448163, 197), (27582263, 197), (27716677, 197), (27851407, 197), (27986489, 197), (28121897, 197), (28257611, 198), (28394371, 198), (28531463, 198), (28668859, 198), (28806607, 198), (28944691, 198), (29083099, 198), (29221817, 198), (29360867, 198), (29500267, 198), (29639989, 198), (29780053, 198), (29920427, 198), (30061147, 198), (30202189, 198), (30343553, 198), (30485249, 198), (30627293, 198), (30769657, 199), (30913073, 199), (31056829, 199), (31200919, 199), (31345339, 199), (31490099, 199), (31635199, 199), (31780627, 199), (31926329, 199), (32072429, 199), (32218853, 199), (32365621, 199)]

theorem chain32_prime_12 : ∀ e ∈ chain32Chunk12, e.1.Prime := by
  simp only [chain32Chunk12, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Chunk 13 of the chain. -/
def chain32Chunk13 : List (ℕ × ℕ) := [(32512709, 199), (32660141, 199), (32807911, 199), (32956009, 199), (33104443, 199), (33253217, 199), (33402311, 199), (33551741, 199), (33701501, 200), (33852359, 200), (34003561, 200), (34155071, 200), (34306939, 200), (34459121, 200), (34611671, 200), (34764559, 200), (34917781, 200), (35071331, 200), (35225219, 200), (35379403, 200), (35533973, 200), (35688881, 200), (35844121, 200), (35999687, 200), (36155611, 200), (36311861, 200), (36468433, 200), (36625363, 201), (36783413, 201), (36941813, 201), (37100489, 201), (37259569, 201), (37418981, 201), (37578743, 201), (37738823, 201), (37899263, 201), (38060041, 201), (38221153, 201), (38382611, 201), (38544391, 201)]

theorem chain32_prime_13 : ∀ e ∈ chain32Chunk13, e.1.Prime := by
  simp only [chain32Chunk13, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Chunk 14 of the chain. -/
def chain32Chunk14 : List (ℕ × ℕ) := [(38706527, 201), (38869013, 201), (39031841, 201), (39194993, 201), (39358477, 201), (39522311, 201), (39686501, 201), (39851023, 201), (40015879, 202), (40181887, 202), (40348261, 202), (40514977, 202), (40682023, 202), (40849421, 202), (41017159, 202), (41185259, 202), (41353703, 202), (41522491, 202), (41691623, 202), (41861093, 202), (42030899, 202), (42201059, 202), (42371551, 202), (42542377, 202), (42713557, 202), (42885083, 202), (43056953, 202), (43229171, 202), (43401707, 202), (43574611, 203), (43748729, 203), (43923163, 203), (44097973, 203), (44273087, 203), (44448589, 203), (44624443, 203), (44800631, 203), (44977181, 203), (45154049, 203), (45331291, 203)]

theorem chain32_prime_14 : ∀ e ∈ chain32Chunk14, e.1.Prime := by
  simp only [chain32Chunk14, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Chunk 15 of the chain. -/
def chain32Chunk15 : List (ℕ × ℕ) := [(45508877, 203), (45686813, 203), (45865093, 203), (46043719, 203), (46222699, 203), (46402021, 203), (46581697, 203), (46761721, 203), (46942079, 203), (47122781, 203), (47303819, 203), (47485189, 204), (47667817, 204), (47850821, 204), (48034099, 204), (48217777, 204), (48401833, 204), (48586247, 204), (48770963, 204), (48956071, 204), (49141537, 204), (49327351, 204), (49513507, 204), (49700017, 204), (49886887, 204), (50074103, 204), (50261671, 204), (50449573, 204), (50637841, 204), (50826443, 204), (51015409, 204), (51204721, 204), (51394379, 204), (51584371, 204), (51774731, 205), (51966379, 205), (52158389, 205), (52350763, 205), (52543489, 205), (52736569, 205)]

theorem chain32_prime_15 : ∀ e ∈ chain32Chunk15, e.1.Prime := by
  simp only [chain32Chunk15, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Chunk 16 of the chain. -/
def chain32Chunk16 : List (ℕ × ℕ) := [(52930001, 205), (53123773, 205), (53317919, 205), (53512409, 205), (53707189, 205), (53902399, 205), (54097949, 205), (54293861, 205), (54490133, 205), (54686761, 205), (54883739, 205), (55081069, 205), (55278731, 205), (55476769, 205), (55675159, 205), (55873903, 205), (56073001, 205), (56272457, 205), (56472271, 206), (56673391, 206), (56874889, 206), (57076739, 206), (57278959, 206), (57481537, 206), (57684439, 206), (57887693, 206), (58091317, 206), (58295327, 206), (58499681, 206), (58704407, 206), (58909483, 206), (59114903, 206), (59320669, 206), (59526799, 206), (59733313, 206), (59940169, 206), (60147391, 206), (60354979, 206), (60562927, 206), (60771229, 206)]

theorem chain32_prime_16 : ∀ e ∈ chain32Chunk16, e.1.Prime := by
  simp only [chain32Chunk16, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Chunk 17 of the chain. -/
def chain32Chunk17 : List (ℕ × ℕ) := [(60979871, 206), (61188893, 206), (61398229, 206), (61607963, 207), (61819063, 207), (62030539, 207), (62242373, 207), (62454571, 207), (62667127, 207), (62880049, 207), (63093311, 207), (63306931, 207), (63520939, 207), (63735289, 207), (63950011, 207), (64165103, 207)]

theorem chain32_prime_17 : ∀ e ∈ chain32Chunk17, e.1.Prime := by
  simp only [chain32Chunk17, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- The checked chain of primes, each with `⌊8 log₂ q⌋`. -/
def primeChain32 : List (ℕ × ℕ) := chain32Chunk0 ++ chain32Chunk1 ++ chain32Chunk2 ++ chain32Chunk3 ++ chain32Chunk4 ++ chain32Chunk5 ++ chain32Chunk6 ++ chain32Chunk7 ++ chain32Chunk8 ++ chain32Chunk9 ++ chain32Chunk10 ++ chain32Chunk11 ++ chain32Chunk12 ++ chain32Chunk13 ++ chain32Chunk14 ++ chain32Chunk15 ++ chain32Chunk16 ++ chain32Chunk17

/-- The arithmetic check: `2^k ≤ p^8` at every node, and the gap condition between neighbours. -/
def chainOK32 : ℕ × ℕ → List (ℕ × ℕ) → Bool
  | (p, k), [] => decide (2 ^ k ≤ p ^ 8)
  | (p, k), (q, k') :: l =>
      decide (2 ^ k ≤ p ^ 8) && decide (p < q)
        && decide ((q - p) ^ 2 * (256 * 10 ^ 6) ≤ 9 * p * (693 * k) ^ 2) && chainOK32 (q, k') l

theorem primeChain32_ok : chainOK32 (2, 8) primeChain32.tail = true := by decide +kernel

theorem primeChain32_head : primeChain32 = (2, 8) :: primeChain32.tail := by decide +kernel

theorem primeChain32_last : lastP 2 primeChain32.tail = 64165103 := by decide +kernel

theorem primeChain32_prime : ∀ e ∈ primeChain32, e.1.Prime := by
  rw [primeChain32]
  simp only [List.forall_mem_append, and_assoc]
  exact ⟨chain32_prime_0, chain32_prime_1, chain32_prime_2, chain32_prime_3, chain32_prime_4, chain32_prime_5, chain32_prime_6, chain32_prime_7, chain32_prime_8, chain32_prime_9, chain32_prime_10, chain32_prime_11, chain32_prime_12, chain32_prime_13, chain32_prime_14, chain32_prime_15, chain32_prime_16, chain32_prime_17⟩

/-- `2^k ≤ p^8` gives `0.693 k / 8 ≤ log p`. -/
lemma log_ge_of_pow_le_32 {p k : ℕ} (hp : 2 ^ k ≤ p ^ 8) (_hp1 : 1 ≤ p) :
    0.693 * (k : ℝ) / 8 ≤ Real.log p := by
  have h1 : Real.log ((2 : ℝ) ^ k) ≤ Real.log ((p : ℝ) ^ 8) :=
    Real.log_le_log (by positivity) (by exact_mod_cast hp)
  rw [Real.log_pow, Real.log_pow] at h1
  have := Real.log_two_gt_d9
  have hk : (0 : ℝ) ≤ k := k.cast_nonneg
  push_cast at h1
  nlinarith

/-- The gap condition implies `q ≤ p + (3/2) √p log p`. -/
lemma gap_le_32 {p q k : ℕ} (hp : 2 ^ k ≤ p ^ 8) (hpq : p < q)
    (hg : (q - p) ^ 2 * (256 * 10 ^ 6) ≤ 9 * p * (693 * k) ^ 2) :
    (q : ℝ) ≤ p + 3 / 2 * √(p : ℝ) * Real.log p := by
  have hp1 : 1 ≤ p := by
    rcases Nat.eq_zero_or_pos p with h | h
    · subst h; simp at hp
    · exact h
  have hlog := log_ge_of_pow_le_32 hp hp1
  set X := 3 / 2 * √(p : ℝ) * (0.693 * k / 8) with hX
  have hX0 : 0 ≤ X := by positivity
  have hg' : ((q : ℝ) - p) ^ 2 ≤ X ^ 2 := by
    have h1 : (((q - p) ^ 2 * (256 * 10 ^ 6) : ℕ) : ℝ) ≤ ((9 * p * (693 * k) ^ 2 : ℕ) : ℝ) := by
      exact_mod_cast hg
    push_cast [Nat.cast_sub hpq.le] at h1
    rw [hX, mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
    nlinarith
  have hq : (q : ℝ) - p ≤ X := by
    by_contra hc
    push Not at hc
    nlinarith
  have : X ≤ 3 / 2 * √(p : ℝ) * Real.log p :=
    mul_le_mul_of_nonneg_left hlog (by positivity)
  linarith

/-- `x ↦ x + (3/2)√x log x` is monotone on `[1, ∞)`. -/
lemma step_mono_32 {p y : ℝ} (hp : 1 ≤ p) (hpy : p ≤ y) :
    p + 3 / 2 * √p * Real.log p ≤ y + 3 / 2 * √y * Real.log y := by
  have h1 : √p ≤ √y := Real.sqrt_le_sqrt hpy
  have h2 : Real.log p ≤ Real.log y := Real.log_le_log (by linarith) hpy
  have h3 : 0 ≤ Real.log p := Real.log_nonneg hp
  have h4 : 0 ≤ √p := Real.sqrt_nonneg _
  have h5 : √p * Real.log p ≤ √y * Real.log y :=
    mul_le_mul h1 h2 h3 (by linarith)
  linarith

/-- Walking a checked chain. -/
theorem exists_prime_of_chain_32 : ∀ (L : List (ℕ × ℕ)) (p k : ℕ), chainOK32 (p, k) L = true →
    p.Prime → (∀ e ∈ L, e.1.Prime) → ∀ y : ℝ, (p : ℝ) ≤ y → y < lastP p L →
    ∃ q : ℕ, q.Prime ∧ y < q ∧ (q : ℝ) ≤ y + 3 / 2 * √y * Real.log y
  | [], p, k, _, _, _, y, hpy, hy => by simp [lastP] at hy; linarith
  | (q, k') :: l, p, k, hc, hp, hl, y, hpy, hy => by
    simp only [chainOK32, Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨hpk, hpq⟩, hg⟩, hc'⟩ := hc
    have hq : q.Prime := hl (q, k') (by simp)
    rcases lt_or_ge y q with h | h
    · refine ⟨q, hq, h, ?_⟩
      have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
      exact (gap_le_32 hpk hpq hg).trans (step_mono_32 hp1 hpy)
    · exact exists_prime_of_chain_32 l q k' hc' hq (fun e he => hl e (by simp [he])) y h
        (by simpa [lastP] using hy)

/-- **Every `(x, x + (3/2)√x log x]` with `2 ≤ x < 6.4·10^7` contains a prime** (no hypothesis). -/
theorem exists_prime_small_32 {x : ℝ} (hx2 : 2 ≤ x) (hx : x < 64 * 10 ^ 6) :
    ∃ p : ℕ, p.Prime ∧ x < p ∧ (p : ℝ) ≤ x + 3 / 2 * √x * Real.log x := by
  have hall := primeChain32_prime
  rw [primeChain32_head] at hall
  refine exists_prime_of_chain_32 primeChain32.tail 2 8 primeChain32_ok Nat.prime_two
    (fun e he => hall e (List.mem_cons_of_mem _ he)) x (by norm_num; linarith) ?_
  rw [primeChain32_last]; push_cast; linarith

end Cramer
