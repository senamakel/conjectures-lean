import Cramer.Small

/-!
# The range `4 ≤ x < 10^8` for the constant `22/25`: a checked prime chain

`primeChainCMS` is a list of 1426 primes `5 = q₀ < q₁ < … < q_1425 = 100044563`, each paired with
`k = ⌊16 log₂ q⌋`. `chainOKCMS` checks `2^k ≤ q_i^16` and
`625 (q_{i+1} − q_i)² (16·10⁴)² ≤ 484 q_i (6931 k)²`, which gives
`q_{i+1} − q_i ≤ (22/25) √q_i (0.6931 k / 16) ≤ (22/25) √q_i log q_i` (`gap_le_cms`). The check is
evaluated by `decide` in the kernel (no `native_decide`); primality of each entry is proved by
`norm_num`, in chunks of 40. The list was generated greedily (largest admissible prime at each
step, `scripts/cms_chain.py`).
-/

namespace Cramer.CMS

open Real

/-- Chunk 0 of the chain. -/
def chainCMSChunk0 : List (ℕ × ℕ) := [(5, 37), (7, 44), (11, 55), (17, 65), (23, 72), (31, 79), (47, 88), (67, 97), (97, 105), (131, 112), (179, 119), (239, 126), (313, 132), (401, 138), (503, 143), (619, 148), (757, 153), (911, 157), (1091, 161), (1291, 165), (1511, 168), (1759, 172), (2029, 175), (2311, 178), (2633, 181), (2971, 184), (3347, 187), (3739, 189), (4177, 192), (4649, 194), (5153, 197), (5689, 199), (6257, 201), (6863, 203), (7499, 205), (8171, 207), (8867, 209), (9613, 211), (10399, 213), (11213, 215)]

theorem chainCMS_prime_0 : ∀ e ∈ chainCMSChunk0, e.1.Prime := by
  simp only [chainCMSChunk0, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Chunk 1 of the chain. -/
def chainCMSChunk1 : List (ℕ × ℕ) := [(12073, 216), (12973, 218), (13913, 220), (14897, 221), (15923, 223), (16993, 224), (18097, 226), (19249, 227), (20443, 229), (21683, 230), (22973, 231), (24281, 233), (25657, 234), (27077, 235), (28549, 236), (30059, 238), (31627, 239), (33247, 240), (34913, 241), (36629, 242), (38393, 243), (40193, 244), (42043, 245), (43951, 246), (45893, 247), (47903, 248), (49957, 249), (52069, 250), (54217, 251), (56443, 252), (58711, 253), (61043, 254), (63421, 255), (65867, 256), (68371, 256), (70921, 257), (73529, 258), (76163, 259), (78887, 260), (81667, 261)]

theorem chainCMS_prime_1 : ∀ e ∈ chainCMSChunk1, e.1.Prime := by
  simp only [chainCMSChunk1, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Chunk 2 of the chain. -/
def chainCMSChunk2 : List (ℕ × ℕ) := [(84509, 261), (87383, 262), (90313, 263), (93323, 264), (96377, 264), (99497, 265), (102679, 266), (105913, 267), (109211, 267), (112573, 268), (115987, 269), (119447, 269), (122971, 270), (126551, 271), (130223, 271), (133949, 272), (137743, 273), (141601, 273), (145517, 274), (149497, 275), (153533, 275), (157639, 276), (161807, 276), (166031, 277), (170327, 278), (174679, 278), (179107, 279), (183593, 279), (188147, 280), (192767, 280), (197453, 281), (202201, 282), (207029, 282), (211891, 283), (216851, 283), (221873, 284), (226943, 284), (232091, 285), (237319, 285), (242603, 286)]

theorem chainCMS_prime_2 : ∀ e ∈ chainCMSChunk2, e.1.Prime := by
  simp only [chainCMSChunk2, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Chunk 3 of the chain. -/
def chainCMSChunk3 : List (ℕ × ℕ) := [(247957, 286), (253381, 287), (258887, 287), (264443, 288), (270073, 288), (275773, 289), (281557, 289), (287393, 290), (293311, 290), (299287, 291), (305353, 291), (311473, 291), (317663, 292), (323933, 292), (330247, 293), (336653, 293), (343127, 294), (349667, 294), (356287, 295), (362987, 295), (369751, 295), (376589, 296), (383489, 296), (390463, 297), (397519, 297), (404597, 298), (411821, 298), (419087, 298), (426427, 299), (433861, 299), (441361, 300), (448939, 300), (456587, 300), (464311, 301), (472127, 301), (479971, 301), (487897, 302), (495931, 302), (504017, 303), (512207, 303)]

theorem chainCMS_prime_3 : ∀ e ∈ chainCMSChunk3, e.1.Prime := by
  simp only [chainCMSChunk3, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Chunk 4 of the chain. -/
def chainCMSChunk4 : List (ℕ × ℕ) := [(520451, 303), (528779, 304), (537197, 304), (545663, 304), (554209, 305), (562841, 305), (571541, 305), (580303, 306), (589189, 306), (598141, 307), (607181, 307), (616289, 307), (625451, 308), (634727, 308), (644057, 308), (653473, 309), (662957, 309), (672521, 309), (682153, 310), (691907, 310), (701731, 310), (711629, 311), (721621, 311), (731683, 311), (741809, 312), (752033, 312), (762329, 312), (772703, 312), (783151, 313), (793699, 313), (804317, 313), (814991, 314), (825791, 314), (836663, 314), (847607, 315), (858631, 315), (869753, 315), (880951, 315), (892219, 316), (903569, 316)]

theorem chainCMS_prime_4 : ∀ e ∈ chainCMSChunk4, e.1.Prime := by
  simp only [chainCMSChunk4, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Chunk 5 of the chain. -/
def chainCMSChunk5 : List (ℕ × ℕ) := [(915017, 316), (926537, 317), (938129, 317), (949811, 317), (961567, 318), (973439, 318), (985399, 318), (997427, 318), (1009531, 319), (1021747, 319), (1034029, 319), (1046393, 319), (1058821, 320), (1071373, 320), (1083983, 320), (1096673, 321), (1109477, 321), (1122287, 321), (1135247, 321), (1148263, 322), (1161403, 322), (1174627, 322), (1187911, 322), (1201283, 323), (1214767, 323), (1228333, 323), (1241971, 323), (1255687, 324), (1269497, 324), (1283389, 324), (1297369, 324), (1311433, 325), (1325617, 325), (1339873, 325), (1354207, 325), (1368617, 326), (1383139, 326), (1397743, 326), (1412429, 326), (1427191, 327)]

theorem chainCMS_prime_5 : ∀ e ∈ chainCMSChunk5, e.1.Prime := by
  simp only [chainCMSChunk5, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Chunk 6 of the chain. -/
def chainCMSChunk6 : List (ℕ × ℕ) := [(1442071, 327), (1457039, 327), (1472083, 327), (1487201, 328), (1502437, 328), (1517753, 328), (1533139, 328), (1548619, 329), (1564183, 329), (1579867, 329), (1595623, 329), (1611451, 329), (1627361, 330), (1643387, 330), (1659491, 330), (1675679, 330), (1691939, 331), (1708351, 331), (1724843, 331), (1741409, 331), (1758019, 331), (1774741, 332), (1791599, 332), (1808539, 332), (1825553, 332), (1842641, 333), (1859863, 333), (1877171, 333), (1894489, 333), (1911961, 333), (1929509, 334), (1947193, 334), (1964951, 334), (1982797, 334), (2000717, 334), (2018713, 335), (2036833, 335), (2055041, 335), (2073347, 335), (2091709, 335)]

theorem chainCMS_prime_6 : ∀ e ∈ chainCMSChunk6, e.1.Prime := by
  simp only [chainCMSChunk6, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Chunk 7 of the chain. -/
def chainCMSChunk7 : List (ℕ × ℕ) := [(2110177, 336), (2128783, 336), (2147461, 336), (2166221, 336), (2185037, 336), (2203969, 337), (2223037, 337), (2242189, 337), (2261407, 337), (2280709, 337), (2300087, 338), (2319613, 338), (2339221, 338), (2358919, 338), (2378699, 338), (2398567, 339), (2418557, 339), (2438629, 339), (2458793, 339), (2479049, 339), (2499389, 340), (2519879, 340), (2540443, 340), (2561099, 340), (2581837, 340), (2602637, 340), (2623531, 341), (2644573, 341), (2665687, 341), (2686907, 341), (2708213, 341), (2729593, 342), (2751113, 342), (2772713, 342), (2794403, 342), (2816173, 342), (2838047, 342), (2860007, 343), (2882111, 343), (2904299, 343)]

theorem chainCMS_prime_7 : ∀ e ∈ chainCMSChunk7, e.1.Prime := by
  simp only [chainCMSChunk7, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Chunk 8 of the chain. -/
def chainCMSChunk8 : List (ℕ × ℕ) := [(2926579, 343), (2948929, 343), (2971363, 344), (2993959, 344), (3016639, 344), (3039389, 344), (3062239, 344), (3085139, 344), (3108163, 345), (3131339, 345), (3154607, 345), (3177961, 345), (3201391, 345), (3224909, 345), (3248503, 346), (3272239, 346), (3296093, 346), (3320029, 346), (3344041, 346), (3368117, 346), (3392281, 347), (3416641, 347), (3441091, 347), (3465611, 347), (3490229, 347), (3514939, 347), (3539713, 348), (3564661, 348), (3589699, 348), (3614833, 348), (3640037, 348), (3665329, 348), (3690721, 349), (3716269, 349), (3741877, 349), (3767609, 349), (3793429, 349), (3819337, 349), (3845329, 349), (3871397, 350)]

theorem chainCMS_prime_8 : ∀ e ∈ chainCMSChunk8, e.1.Prime := by
  simp only [chainCMSChunk8, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Chunk 9 of the chain. -/
def chainCMSChunk9 : List (ℕ × ℕ) := [(3897637, 350), (3923977, 350), (3950399, 350), (3976913, 350), (4003513, 350), (4030199, 351), (4057043, 351), (4083979, 351), (4111007, 351), (4138129, 351), (4165339, 351), (4192637, 351), (4219991, 352), (4247549, 352), (4275181, 352), (4302919, 352), (4330717, 352), (4358621, 352), (4386623, 353), (4414789, 353), (4443041, 353), (4471393, 353), (4499839, 353), (4528369, 353), (4556999, 353), (4585723, 354), (4614619, 354), (4643593, 354), (4672669, 354), (4701811, 354), (4731061, 354), (4760369, 354), (4789793, 355), (4819379, 355), (4849081, 355), (4878871, 355), (4908749, 355), (4938707, 355), (4968763, 355), (4998913, 356)]

theorem chainCMS_prime_9 : ∀ e ∈ chainCMSChunk9, e.1.Prime := by
  simp only [chainCMSChunk9, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Chunk 10 of the chain. -/
def chainCMSChunk10 : List (ℕ × ℕ) := [(5029253, 356), (5059679, 356), (5090171, 356), (5120737, 356), (5151437, 356), (5182217, 356), (5213093, 357), (5244139, 357), (5275279, 357), (5306531, 357), (5337853, 357), (5369291, 357), (5400823, 357), (5432443, 357), (5464127, 358), (5496013, 358), (5527987, 358), (5560073, 358), (5592247, 358), (5624483, 358), (5656837, 358), (5689289, 359), (5721931, 359), (5754659, 359), (5787479, 359), (5820389, 359), (5853403, 359), (5886499, 359), (5919691, 359), (5952983, 360), (5986447, 360), (6019991, 360), (6053639, 360), (6087401, 360), (6121253, 360), (6155179, 360), (6189223, 360), (6223351, 361), (6257677, 361), (6292081, 361)]

theorem chainCMS_prime_10 : ∀ e ∈ chainCMSChunk10, e.1.Prime := by
  simp only [chainCMSChunk10, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Chunk 11 of the chain. -/
def chainCMSChunk11 : List (ℕ × ℕ) := [(6326599, 361), (6361207, 361), (6395903, 361), (6430687, 361), (6465581, 361), (6500573, 362), (6535751, 362), (6571021, 362), (6606389, 362), (6641851, 362), (6677401, 362), (6713059, 362), (6748799, 362), (6784643, 363), (6820663, 363), (6856781, 363), (6893011, 363), (6929339, 363), (6965759, 363), (7002257, 363), (7038859, 363), (7075529, 364), (7112437, 364), (7149433, 364), (7186523, 364), (7223719, 364), (7261003, 364), (7298393, 364), (7335863, 364), (7373411, 365), (7411189, 365), (7449067, 365), (7486981, 365), (7525051, 365), (7563191, 365), (7601453, 365), (7639799, 365), (7678217, 365), (7716767, 366), (7755521, 366)]

theorem chainCMS_prime_11 : ∀ e ∈ chainCMSChunk11, e.1.Prime := by
  simp only [chainCMSChunk11, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Chunk 12 of the chain. -/
def chainCMSChunk12 : List (ℕ × ℕ) := [(7794373, 366), (7833323, 366), (7872367, 366), (7911503, 366), (7950739, 366), (7990079, 366), (8029517, 366), (8069041, 367), (8108773, 367), (8148589, 367), (8188519, 367), (8228551, 367), (8268679, 367), (8308891, 367), (8349217, 367), (8389607, 368), (8430217, 368), (8470927, 368), (8511731, 368), (8552653, 368), (8593667, 368), (8634767, 368), (8675923, 368), (8717239, 368), (8758637, 368), (8800153, 369), (8841881, 369), (8883703, 369), (8925617, 369), (8967611, 369), (9009727, 369), (9051947, 369), (9094247, 369), (9136657, 369), (9179171, 370), (9221893, 370), (9264721, 370), (9307633, 370), (9350633, 370), (9393763, 370)]

theorem chainCMS_prime_12 : ∀ e ∈ chainCMSChunk12, e.1.Prime := by
  simp only [chainCMSChunk12, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Chunk 13 of the chain. -/
def chainCMSChunk13 : List (ℕ × ℕ) := [(9436981, 370), (9480293, 370), (9523711, 370), (9567223, 371), (9610957, 371), (9654797, 371), (9698737, 371), (9742757, 371), (9786893, 371), (9831127, 371), (9875449, 371), (9919883, 371), (9964403, 371), (10009037, 372), (10053887, 372), (10098821, 372), (10143863, 372), (10188991, 372), (10234253, 372), (10279613, 372), (10325041, 372), (10370593, 372), (10416233, 372), (10461991, 373), (10507951, 373), (10554029, 373), (10600211, 373), (10646483, 373), (10692863, 373), (10739353, 373), (10785899, 373), (10832567, 373), (10879361, 374), (10926367, 374), (10973447, 374), (11020651, 374), (11067943, 374), (11115373, 374), (11162891, 374), (11210509, 374)]

theorem chainCMS_prime_13 : ∀ e ∈ chainCMSChunk13, e.1.Prime := by
  simp only [chainCMSChunk13, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Chunk 14 of the chain. -/
def chainCMSChunk14 : List (ℕ × ℕ) := [(11258237, 374), (11306059, 374), (11353987, 374), (11402023, 375), (11450291, 375), (11498659, 375), (11547113, 375), (11595677, 375), (11644343, 375), (11693111, 375), (11741959, 375), (11790941, 375), (11840011, 375), (11889197, 376), (11938603, 376), (11988121, 376), (12037747, 376), (12087463, 376), (12137291, 376), (12187223, 376), (12237227, 376), (12287347, 376), (12337573, 376), (12387887, 376), (12438311, 377), (12488941, 377), (12539729, 377), (12590603, 377), (12641567, 377), (12692663, 377), (12743837, 377), (12795137, 377), (12846541, 377), (12898051, 377), (12949639, 378), (13001489, 378), (13053431, 378), (13105489, 378), (13157647, 378), (13209881, 378)]

theorem chainCMS_prime_14 : ∀ e ∈ chainCMSChunk14, e.1.Prime := by
  simp only [chainCMSChunk14, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Chunk 15 of the chain. -/
def chainCMSChunk15 : List (ℕ × ℕ) := [(13262239, 378), (13314703, 378), (13367267, 378), (13419949, 378), (13472707, 378), (13525559, 379), (13578659, 379), (13631879, 379), (13685213, 379), (13738643, 379), (13792187, 379), (13845817, 379), (13899569, 379), (13953427, 379), (14007373, 379), (14061427, 379), (14115587, 380), (14170003, 380), (14224531, 380), (14279149, 380), (14333881, 380), (14388713, 380), (14443643, 380), (14498683, 380), (14553827, 380), (14609087, 380), (14664451, 380), (14719921, 380), (14775487, 381), (14831309, 381), (14887217, 381), (14943251, 381), (14999359, 381), (15055603, 381), (15111937, 381), (15168389, 381), (15224927, 381), (15281593, 381), (15338363, 381), (15395227, 382)]

theorem chainCMS_prime_15 : ∀ e ∈ chainCMSChunk15, e.1.Prime := by
  simp only [chainCMSChunk15, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Chunk 16 of the chain. -/
def chainCMSChunk16 : List (ℕ × ℕ) := [(15452363, 382), (15509597, 382), (15566923, 382), (15624317, 382), (15681857, 382), (15739523, 382), (15797293, 382), (15855163, 382), (15913133, 382), (15971183, 382), (16029359, 382), (16087619, 383), (16146173, 383), (16204817, 383), (16263587, 383), (16322443, 383), (16381397, 383), (16440481, 383), (16499647, 383), (16558951, 383), (16618321, 383), (16677811, 383), (16737421, 383), (16797127, 384), (16857119, 384), (16917217, 384), (16977421, 384), (17037721, 384), (17098121, 384), (17158637, 384), (17219239, 384), (17279981, 384), (17340809, 384), (17401763, 384), (17462821, 384), (17523983, 385), (17585419, 385), (17646961, 385), (17708599, 385), (17770351, 385)]

theorem chainCMS_prime_16 : ∀ e ∈ chainCMSChunk16, e.1.Prime := by
  simp only [chainCMSChunk16, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Chunk 17 of the chain. -/
def chainCMSChunk17 : List (ℕ × ℕ) := [(17832209, 385), (17894179, 385), (17956259, 385), (18018443, 385), (18080731, 385), (18143137, 385), (18205619, 385), (18268223, 385), (18330941, 386), (18393937, 386), (18457039, 386), (18520247, 386), (18583571, 386), (18647003, 386), (18710521, 386), (18774169, 386), (18837899, 386), (18901763, 386), (18965729, 386), (19029799, 386), (19093981, 386), (19158259, 387), (19222831, 387), (19287511, 387), (19352293, 387), (19417187, 387), (19482161, 387), (19547273, 387), (19612487, 387), (19677817, 387), (19743257, 387), (19808807, 387), (19874447, 387), (19940191, 387), (20006057, 388), (20072209, 388), (20138453, 388), (20204827, 388), (20271299, 388), (20337883, 388)]

theorem chainCMS_prime_17 : ∀ e ∈ chainCMSChunk17, e.1.Prime := by
  simp only [chainCMSChunk17, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Chunk 18 of the chain. -/
def chainCMSChunk18 : List (ℕ × ℕ) := [(20404577, 388), (20471327, 388), (20538239, 388), (20605267, 388), (20672371, 388), (20739619, 388), (20806937, 388), (20874397, 389), (20942101, 389), (21009941, 389), (21077899, 389), (21145979, 389), (21214169, 389), (21282467, 389), (21350869, 389), (21419381, 389), (21487981, 389), (21556709, 389), (21625531, 389), (21694487, 389), (21763541, 390), (21832871, 390), (21902333, 390), (21971903, 390), (22041583, 390), (22111363, 390), (22181267, 390), (22251277, 390), (22321399, 390), (22391609, 390), (22461941, 390), (22532401, 390), (22602961, 390), (22673633, 390), (22744411, 391), (22815487, 391), (22886671, 391), (22957969, 391), (23029343, 391), (23100851, 391)]

theorem chainCMS_prime_18 : ∀ e ∈ chainCMSChunk18, e.1.Prime := by
  simp only [chainCMSChunk18, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Chunk 19 of the chain. -/
def chainCMSChunk19 : List (ℕ × ℕ) := [(23172451, 391), (23244181, 391), (23316023, 391), (23387983, 391), (23460061, 391), (23532227, 391), (23604527, 391), (23676911, 391), (23749417, 392), (23822209, 392), (23895139, 392), (23968183, 392), (24041323, 392), (24114583, 392), (24187951, 392), (24261443, 392), (24335027, 392), (24408739, 392), (24482551, 392), (24556489, 392), (24630527, 392), (24704681, 392), (24778933, 393), (24853489, 393), (24928157, 393), (25002893, 393), (25077799, 393), (25152797, 393), (25227931, 393), (25303171, 393), (25378517, 393), (25453969, 393), (25529531, 393), (25605199, 393), (25681003, 393), (25756909, 393), (25832927, 393), (25909069, 394), (25985489, 394), (26062033, 394)]

theorem chainCMS_prime_19 : ∀ e ∈ chainCMSChunk19, e.1.Prime := by
  simp only [chainCMSChunk19, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Chunk 20 of the chain. -/
def chainCMSChunk20 : List (ℕ × ℕ) := [(26138701, 394), (26215489, 394), (26292379, 394), (26369377, 394), (26446487, 394), (26523713, 394), (26601061, 394), (26678501, 394), (26756071, 394), (26833753, 394), (26911529, 394), (26989433, 394), (27067459, 395), (27145777, 395), (27224227, 395), (27302789, 395), (27381467, 395), (27460259, 395), (27539153, 395), (27618139, 395), (27697261, 395), (27776503, 395), (27855823, 395), (27935291, 395), (28014869, 395), (28094551, 395), (28174337, 395), (28254253, 396), (28334473, 396), (28414777, 396), (28495241, 396), (28575763, 396), (28656451, 396), (28737251, 396), (28818151, 396), (28899181, 396), (28980331, 396), (29061577, 396), (29142937, 396), (29224427, 396)]

theorem chainCMS_prime_20 : ∀ e ∈ chainCMSChunk20, e.1.Prime := by
  simp only [chainCMSChunk20, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Chunk 21 of the chain. -/
def chainCMSChunk21 : List (ℕ × ℕ) := [(29306029, 396), (29387749, 396), (29469569, 397), (29551723, 397), (29633957, 397), (29716339, 397), (29798837, 397), (29881447, 397), (29964167, 397), (30046979, 397), (30129907, 397), (30212969, 397), (30296143, 397), (30379417, 397), (30462811, 397), (30546311, 397), (30629933, 397), (30713623, 397), (30797447, 398), (30881629, 398), (30965941, 398), (31050353, 398), (31134889, 398), (31219543, 398), (31304309, 398), (31389187, 398), (31474171, 398), (31559263, 398), (31644493, 398), (31729823, 398), (31815257, 398), (31900831, 398), (31986523, 398), (32072329, 398), (32158249, 399), (32244493, 399), (32330849, 399), (32417321, 399), (32503901, 399), (32590561, 399)]

theorem chainCMS_prime_21 : ∀ e ∈ chainCMSChunk21, e.1.Prime := by
  simp only [chainCMSChunk21, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Chunk 22 of the chain. -/
def chainCMSChunk22 : List (ℕ × ℕ) := [(32677373, 399), (32764309, 399), (32851349, 399), (32938517, 399), (33025799, 399), (33113207, 399), (33200701, 399), (33288319, 399), (33376067, 399), (33463931, 399), (33551909, 399), (33640003, 400), (33728413, 400), (33816967, 400), (33905621, 400), (33994403, 400), (34083307, 400), (34172309, 400), (34261399, 400), (34350643, 400), (34440001, 400), (34529483, 400), (34619059, 400), (34708753, 400), (34798559, 400), (34888507, 400), (34978547, 400), (35068703, 401), (35159219, 401), (35249849, 401), (35340593, 401), (35431457, 401), (35522447, 401), (35613547, 401), (35704751, 401), (35796091, 401), (35887543, 401), (35979113, 401), (36070799, 401), (36162593, 401)]

theorem chainCMS_prime_22 : ∀ e ∈ chainCMSChunk22, e.1.Prime := by
  simp only [chainCMSChunk22, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Chunk 23 of the chain. -/
def chainCMSChunk23 : List (ℕ × ℕ) := [(36254513, 401), (36346549, 401), (36438707, 401), (36530953, 401), (36623341, 402), (36716063, 402), (36808913, 402), (36901847, 402), (36994933, 402), (37088141, 402), (37181453, 402), (37274879, 402), (37368439, 402), (37462097, 402), (37555891, 402), (37649803, 402), (37743829, 402), (37837973, 402), (37932217, 402), (38026591, 402), (38121079, 402), (38215693, 403), (38310611, 403), (38405681, 403), (38500841, 403), (38596157, 403), (38691571, 403), (38787121, 403), (38882783, 403), (38978551, 403), (39074423, 403), (39170447, 403), (39266593, 403), (39362849, 403), (39459229, 403), (39555713, 403), (39652331, 403), (39749057, 403), (39845903, 403), (39942871, 404)]

theorem chainCMS_prime_23 : ∀ e ∈ chainCMSChunk23, e.1.Prime := by
  simp only [chainCMSChunk23, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Chunk 24 of the chain. -/
def chainCMSChunk24 : List (ℕ × ℕ) := [(40040197, 404), (40137613, 404), (40235177, 404), (40332833, 404), (40430623, 404), (40528547, 404), (40626587, 404), (40724699, 404), (40822973, 404), (40921367, 404), (41019871, 404), (41118463, 404), (41217193, 404), (41316059, 404), (41415047, 404), (41514133, 404), (41613359, 404), (41712667, 405), (41812363, 405), (41912183, 405), (42012133, 405), (42112201, 405), (42212351, 405), (42312649, 405), (42413029, 405), (42513563, 405), (42614227, 405), (42715009, 405), (42815879, 405), (42916901, 405), (43018037, 405), (43119287, 405), (43220659, 405), (43322119, 405), (43423733, 405), (43525459, 406), (43627561, 406), (43729769, 406), (43832083, 406), (43934537, 406)]

theorem chainCMS_prime_24 : ∀ e ∈ chainCMSChunk24, e.1.Prime := by
  simp only [chainCMSChunk24, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Chunk 25 of the chain. -/
def chainCMSChunk25 : List (ℕ × ℕ) := [(44037101, 406), (44139787, 406), (44242591, 406), (44345519, 406), (44448577, 406), (44551753, 406), (44655019, 406), (44758411, 406), (44861881, 406), (44965537, 406), (45069307, 406), (45173171, 406), (45277187, 406), (45381307, 406), (45485567, 407), (45590203, 407), (45694937, 407), (45799801, 407), (45904799, 407), (46009897, 407), (46115129, 407), (46220453, 407), (46325891, 407), (46431491, 407), (46537207, 407), (46643039, 407), (46748993, 407), (46855069, 407), (46961269, 407), (47067571, 407), (47174009, 407), (47280529, 407), (47387209, 407), (47494003, 408), (47601187, 408), (47708471, 408), (47815897, 408), (47923441, 408), (48031097, 408), (48138863, 408)]

theorem chainCMS_prime_25 : ∀ e ∈ chainCMSChunk25, e.1.Prime := by
  simp only [chainCMSChunk25, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Chunk 26 of the chain. -/
def chainCMSChunk26 : List (ℕ × ℕ) := [(48246773, 408), (48354793, 408), (48462923, 408), (48571157, 408), (48679549, 408), (48788059, 408), (48896657, 408), (49005413, 408), (49114279, 408), (49223269, 408), (49332331, 408), (49441571, 408), (49550929, 408), (49660409, 409), (49770251, 409), (49880239, 409), (49990337, 409), (50100571, 409), (50210921, 409), (50321399, 409), (50431981, 409), (50542693, 409), (50653513, 409), (50764463, 409), (50875549, 409), (50986717, 409), (51098023, 409), (51209467, 409), (51321037, 409), (51432707, 409), (51544501, 409), (51656417, 409), (51768473, 410), (51880879, 410), (51993451, 410), (52106149, 410), (52218923, 410), (52331861, 410), (52444897, 410), (52558081, 410)]

theorem chainCMS_prime_26 : ∀ e ∈ chainCMSChunk26, e.1.Prime := by
  simp only [chainCMSChunk26, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Chunk 27 of the chain. -/
def chainCMSChunk27 : List (ℕ × ℕ) := [(52671383, 410), (52784803, 410), (52898353, 410), (53012027, 410), (53125811, 410), (53239727, 410), (53353763, 410), (53467913, 410), (53582197, 410), (53696597, 410), (53811101, 410), (53925737, 410), (54040507, 411), (54155677, 411), (54270959, 411), (54386333, 411), (54501859, 411), (54617503, 411), (54733291, 411), (54849167, 411), (54965191, 411), (55081337, 411), (55197587, 411), (55313989, 411), (55430509, 411), (55547153, 411), (55663921, 411), (55780807, 411), (55897813, 411), (56014943, 411), (56132203, 411), (56249561, 411), (56367013, 411), (56484629, 412), (56602661, 412), (56720813, 412), (56839093, 412), (56957489, 412), (57076013, 412), (57194663, 412)]

theorem chainCMS_prime_27 : ∀ e ∈ chainCMSChunk27, e.1.Prime := by
  simp only [chainCMSChunk27, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Chunk 28 of the chain. -/
def chainCMSChunk28 : List (ℕ × ℕ) := [(57313427, 412), (57432313, 412), (57551327, 412), (57670469, 412), (57789707, 412), (57909077, 412), (58028591, 412), (58148221, 412), (58267973, 412), (58387859, 412), (58507847, 412), (58627973, 412), (58748227, 412), (58868573, 412), (58989071, 413), (59109959, 413), (59230981, 413), (59352079, 413), (59473307, 413), (59594719, 413), (59716253, 413), (59837903, 413), (59959681, 413), (60081559, 413), (60203557, 413), (60325709, 413), (60447929, 413), (60570317, 413), (60692843, 413), (60815479, 413), (60938243, 413), (61061129, 413), (61184153, 413), (61307299, 413), (61430563, 413), (61553953, 414), (61677769, 414), (61801711, 414), (61925767, 414), (62049959, 414)]

theorem chainCMS_prime_28 : ∀ e ∈ chainCMSChunk28, e.1.Prime := by
  simp only [chainCMSChunk28, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Chunk 29 of the chain. -/
def chainCMSChunk29 : List (ℕ × ℕ) := [(62174269, 414), (62298703, 414), (62423261, 414), (62547937, 414), (62672749, 414), (62797681, 414), (62922719, 414), (63047851, 414), (63173141, 414), (63298549, 414), (63424091, 414), (63549767, 414), (63675559, 414), (63801469, 414), (63927517, 414), (64053679, 414), (64179977, 414), (64306351, 415), (64433209, 415), (64560173, 415), (64687253, 415), (64814447, 415), (64941803, 415), (65069287, 415), (65196889, 415), (65324599, 415), (65452433, 415), (65580401, 415), (65708507, 415), (65836721, 415), (65965069, 415), (66093551, 415), (66222133, 415), (66350857, 415), (66479663, 415), (66608627, 415), (66737711, 415), (66866929, 415), (66996277, 415), (67125761, 416)]

theorem chainCMS_prime_29 : ∀ e ∈ chainCMSChunk29, e.1.Prime := by
  simp only [chainCMSChunk29, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Chunk 30 of the chain. -/
def chainCMSChunk30 : List (ℕ × ℕ) := [(67255681, 416), (67385707, 416), (67515881, 416), (67646171, 416), (67776587, 416), (67907137, 416), (68037787, 416), (68168587, 416), (68299513, 416), (68430569, 416), (68561741, 416), (68693017, 416), (68824447, 416), (68955977, 416), (69087661, 416), (69219421, 416), (69351353, 416), (69483389, 416), (69615577, 416), (69747869, 416), (69880297, 416), (70012861, 416), (70145521, 417), (70278653, 417), (70411903, 417), (70545289, 417), (70678801, 417), (70812437, 417), (70946177, 417), (71080069, 417), (71214061, 417), (71348191, 417), (71482457, 417), (71616841, 417), (71751359, 417), (71885969, 417), (72020713, 417), (72155543, 417), (72290557, 417), (72425713, 417)]

theorem chainCMS_prime_30 : ∀ e ∈ chainCMSChunk30, e.1.Prime := by
  simp only [chainCMSChunk30, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Chunk 31 of the chain. -/
def chainCMSChunk31 : List (ℕ × ℕ) := [(72560989, 417), (72696397, 417), (72831931, 417), (72967549, 417), (73103333, 417), (73239233, 418), (73375573, 418), (73512041, 418), (73648643, 418), (73785343, 418), (73922213, 418), (74059211, 418), (74196319, 418), (74333561, 418), (74470939, 418), (74608403, 418), (74746033, 418), (74883751, 418), (75021619, 418), (75159631, 418), (75297769, 418), (75436003, 418), (75574399, 418), (75712877, 418), (75851497, 418), (75990251, 418), (76129133, 418), (76268149, 418), (76407293, 418), (76546577, 419), (76686287, 419), (76826137, 419), (76966129, 419), (77106247, 419), (77246497, 419), (77386861, 419), (77527369, 419), (77667979, 419), (77808737, 419), (77949629, 419)]

theorem chainCMS_prime_31 : ∀ e ∈ chainCMSChunk31, e.1.Prime := by
  simp only [chainCMSChunk31, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Chunk 32 of the chain. -/
def chainCMSChunk32 : List (ℕ × ℕ) := [(78090619, 419), (78231709, 419), (78372947, 419), (78514349, 419), (78655771, 419), (78797413, 419), (78939193, 419), (79081103, 419), (79223129, 419), (79365269, 419), (79507553, 419), (79649963, 419), (79792487, 419), (79935161, 420), (80078303, 420), (80221571, 420), (80364943, 420), (80508469, 420), (80652101, 420), (80795881, 420), (80939777, 420), (81083813, 420), (81227947, 420), (81372223, 420), (81516641, 420), (81661189, 420), (81805847, 420), (81950641, 420), (82095577, 420), (82240643, 420), (82385803, 420), (82531103, 420), (82676509, 420), (82822087, 420), (82967791, 420), (83113603, 420), (83259559, 420), (83405629, 421), (83552171, 421), (83698861, 421)]

theorem chainCMS_prime_32 : ∀ e ∈ chainCMSChunk32, e.1.Prime := by
  simp only [chainCMSChunk32, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Chunk 33 of the chain. -/
def chainCMSChunk33 : List (ℕ × ℕ) := [(83845681, 421), (83992621, 421), (84139697, 421), (84286903, 421), (84434237, 421), (84581689, 421), (84729283, 421), (84877003, 421), (85024817, 421), (85172783, 421), (85320863, 421), (85469089, 421), (85617449, 421), (85765921, 421), (85914533, 421), (86063279, 421), (86212153, 421), (86361151, 421), (86510279, 421), (86659549, 421), (86808947, 421), (86958461, 421), (87108089, 422), (87258217, 422), (87408481, 422), (87558871, 422), (87709387, 422), (87860033, 422), (88010807, 422), (88161721, 422), (88312753, 422), (88463899, 422), (88615181, 422), (88766603, 422), (88918163, 422), (89069843, 422), (89221633, 422), (89373553, 422), (89525629, 422), (89677807, 422)]

theorem chainCMS_prime_33 : ∀ e ∈ chainCMSChunk33, e.1.Prime := by
  simp only [chainCMSChunk33, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Chunk 34 of the chain. -/
def chainCMSChunk34 : List (ℕ × ℕ) := [(89830093, 422), (89982533, 422), (90135119, 422), (90287837, 422), (90440689, 422), (90593627, 422), (90746699, 422), (90899923, 423), (91053659, 423), (91207517, 423), (91361483, 423), (91515587, 423), (91669843, 423), (91824217, 423), (91978717, 423), (92133343, 423), (92288107, 423), (92443007, 423), (92597969, 423), (92753131, 423), (92908411, 423), (93063823, 423), (93219359, 423), (93375031, 423), (93530837, 423), (93686753, 423), (93842789, 423), (93998969, 423), (94155293, 423), (94311757, 423), (94468349, 423), (94624991, 423), (94781839, 423), (94938793, 424), (95096279, 424), (95253889, 424), (95411629, 424), (95569501, 424), (95727509, 424), (95885633, 424)]

theorem chainCMS_prime_34 : ∀ e ∈ chainCMSChunk34, e.1.Prime := by
  simp only [chainCMSChunk34, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Chunk 35 of the chain. -/
def chainCMSChunk35 : List (ℕ × ℕ) := [(96043873, 424), (96202237, 424), (96360749, 424), (96519403, 424), (96678191, 424), (96837109, 424), (96996143, 424), (97155313, 424), (97314617, 424), (97474061, 424), (97633621, 424), (97793291, 424), (97953083, 424), (98113051, 424), (98273143, 424), (98433359, 424), (98593699, 424), (98754163, 424), (98914747, 424), (99075491, 424), (99236369, 425), (99397741, 425), (99559261, 425), (99720899, 425), (99882649, 425), (100044563, 425)]

theorem chainCMS_prime_35 : ∀ e ∈ chainCMSChunk35, e.1.Prime := by
  simp only [chainCMSChunk35, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- The checked chain of primes, each with `⌊16 log₂ q⌋`. -/
def primeChainCMS : List (ℕ × ℕ) := chainCMSChunk0 ++ chainCMSChunk1 ++ chainCMSChunk2 ++ chainCMSChunk3 ++ chainCMSChunk4 ++ chainCMSChunk5 ++ chainCMSChunk6 ++ chainCMSChunk7 ++ chainCMSChunk8 ++ chainCMSChunk9 ++ chainCMSChunk10 ++ chainCMSChunk11 ++ chainCMSChunk12 ++ chainCMSChunk13 ++ chainCMSChunk14 ++ chainCMSChunk15 ++ chainCMSChunk16 ++ chainCMSChunk17 ++ chainCMSChunk18 ++ chainCMSChunk19 ++ chainCMSChunk20 ++ chainCMSChunk21 ++ chainCMSChunk22 ++ chainCMSChunk23 ++ chainCMSChunk24 ++ chainCMSChunk25 ++ chainCMSChunk26 ++ chainCMSChunk27 ++ chainCMSChunk28 ++ chainCMSChunk29 ++ chainCMSChunk30 ++ chainCMSChunk31 ++ chainCMSChunk32 ++ chainCMSChunk33 ++ chainCMSChunk34 ++ chainCMSChunk35

/-- The arithmetic check: `2^k ≤ p^16` at every node, and the gap condition between neighbours. -/
def chainOKCMS : ℕ × ℕ → List (ℕ × ℕ) → Bool
  | (p, k), [] => decide (2 ^ k ≤ p ^ 16)
  | (p, k), (q, k') :: l =>
      decide (2 ^ k ≤ p ^ 16) && decide (p < q)
        && decide ((q - p) ^ 2 * (16 * 10 ^ 4) ^ 2 * 625 ≤ 484 * p * (6931 * k) ^ 2) && chainOKCMS (q, k') l

set_option maxRecDepth 100000 in
theorem primeChainCMS_ok : chainOKCMS (5, 37) primeChainCMS.tail = true := by decide +kernel

theorem primeChainCMS_head : primeChainCMS = (5, 37) :: primeChainCMS.tail := by decide +kernel

set_option maxRecDepth 100000 in
theorem primeChainCMS_last : lastP 5 primeChainCMS.tail = 100044563 := by decide +kernel

theorem primeChainCMS_prime : ∀ e ∈ primeChainCMS, e.1.Prime := by
  rw [primeChainCMS]
  simp only [List.forall_mem_append, and_assoc]
  exact ⟨chainCMS_prime_0, chainCMS_prime_1, chainCMS_prime_2, chainCMS_prime_3, chainCMS_prime_4, chainCMS_prime_5, chainCMS_prime_6, chainCMS_prime_7, chainCMS_prime_8, chainCMS_prime_9, chainCMS_prime_10, chainCMS_prime_11, chainCMS_prime_12, chainCMS_prime_13, chainCMS_prime_14, chainCMS_prime_15, chainCMS_prime_16, chainCMS_prime_17, chainCMS_prime_18, chainCMS_prime_19, chainCMS_prime_20, chainCMS_prime_21, chainCMS_prime_22, chainCMS_prime_23, chainCMS_prime_24, chainCMS_prime_25, chainCMS_prime_26, chainCMS_prime_27, chainCMS_prime_28, chainCMS_prime_29, chainCMS_prime_30, chainCMS_prime_31, chainCMS_prime_32, chainCMS_prime_33, chainCMS_prime_34, chainCMS_prime_35⟩

/-- `2^k ≤ p^16` gives `0.6931 k / 16 ≤ log p`. -/
lemma log_ge_of_pow_le_cms {p k : ℕ} (hp : 2 ^ k ≤ p ^ 16) :
    0.6931 * (k : ℝ) / 16 ≤ Real.log p := by
  have h1 : Real.log ((2 : ℝ) ^ k) ≤ Real.log ((p : ℝ) ^ 16) :=
    Real.log_le_log (by positivity) (by exact_mod_cast hp)
  rw [Real.log_pow, Real.log_pow] at h1
  have := Real.log_two_gt_d9
  have hk : (0 : ℝ) ≤ k := k.cast_nonneg
  push_cast at h1
  nlinarith

/-- The gap condition implies `q ≤ p + (22/25) √p log p`. -/
lemma gap_le_cms {p q k : ℕ} (hp : 2 ^ k ≤ p ^ 16) (hpq : p < q)
    (hg : (q - p) ^ 2 * (16 * 10 ^ 4) ^ 2 * 625 ≤ 484 * p * (6931 * k) ^ 2) :
    (q : ℝ) ≤ p + 22 / 25 * √(p : ℝ) * Real.log p := by
  have hlog := log_ge_of_pow_le_cms hp
  set X := 22 / 25 * √(p : ℝ) * (0.6931 * k / 16) with hX
  have hX0 : 0 ≤ X := by positivity
  have hg' : ((q : ℝ) - p) ^ 2 ≤ X ^ 2 := by
    have h1 : (((q - p) ^ 2 * (16 * 10 ^ 4) ^ 2 * 625 : ℕ) : ℝ) ≤ ((484 * p * (6931 * k) ^ 2 : ℕ) : ℝ) := by
      exact_mod_cast hg
    push_cast [Nat.cast_sub hpq.le] at h1
    rw [hX, mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
    nlinarith
  have hq : (q : ℝ) - p ≤ X := by
    by_contra hc
    push Not at hc
    nlinarith
  have : X ≤ 22 / 25 * √(p : ℝ) * Real.log p :=
    mul_le_mul_of_nonneg_left hlog (by positivity)
  linarith

/-- `x ↦ x + (22/25)√x log x` is monotone on `[1, ∞)`. -/
lemma step_mono_cms {p y : ℝ} (hp : 1 ≤ p) (hpy : p ≤ y) :
    p + 22 / 25 * √p * Real.log p ≤ y + 22 / 25 * √y * Real.log y := by
  have h1 : √p ≤ √y := Real.sqrt_le_sqrt hpy
  have h2 : Real.log p ≤ Real.log y := Real.log_le_log (by linarith) hpy
  have h3 : 0 ≤ Real.log p := Real.log_nonneg hp
  have h4 : 0 ≤ √p := Real.sqrt_nonneg _
  have h5 : √p * Real.log p ≤ √y * Real.log y :=
    mul_le_mul h1 h2 h3 (by linarith)
  linarith

/-- Walking a checked chain. -/
theorem exists_prime_of_chain_cms : ∀ (L : List (ℕ × ℕ)) (p k : ℕ), chainOKCMS (p, k) L = true →
    1 ≤ p → (∀ e ∈ L, e.1.Prime) → ∀ y : ℝ, (p : ℝ) ≤ y → y < lastP p L →
    ∃ q : ℕ, q.Prime ∧ y < q ∧ (q : ℝ) ≤ y + 22 / 25 * √y * Real.log y
  | [], p, k, _, _, _, y, hpy, hy => by simp [lastP] at hy; linarith
  | (q, k') :: l, p, k, hc, hp, hl, y, hpy, hy => by
    simp only [chainOKCMS, Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨hpk, hpq⟩, hg⟩, hc'⟩ := hc
    have hq : q.Prime := hl (q, k') (by simp)
    rcases lt_or_ge y q with h | h
    · refine ⟨q, hq, h, ?_⟩
      have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
      exact (gap_le_cms hpk hpq hg).trans (step_mono_cms hp1 hpy)
    · exact exists_prime_of_chain_cms l q k' hc' (by omega) (fun e he => hl e (by simp [he])) y h
        (by simpa [lastP] using hy)

/-- **Every `(x, x + (22/25)√x log x]` with `5 ≤ x < 10^8` contains a prime** (no hypothesis). -/
theorem exists_prime_small_cms {x : ℝ} (hx5 : 5 ≤ x) (hx : x < 10 ^ 8) :
    ∃ p : ℕ, p.Prime ∧ x < p ∧ (p : ℝ) ≤ x + 22 / 25 * √x * Real.log x := by
  have hall := primeChainCMS_prime
  rw [primeChainCMS_head] at hall
  refine exists_prime_of_chain_cms primeChainCMS.tail 5 37 primeChainCMS_ok (by norm_num)
    (fun e he => hall e (List.mem_cons_of_mem _ he)) x (by norm_num; linarith) ?_
  rw [primeChainCMS_last]; push_cast; linarith

end Cramer.CMS
