import Cramer.Small

/-!
# The range `2 ≤ x < 10^8`: a prime in `(x, x + (107/100)√x log x]` by a checked prime chain

`primeChain107` is a list of 1176 primes `2 = q₀ < q₁ < … < q_1175 = 100102841`, each paired with
`k = ⌊16 log₂ q⌋`. `chainOK107` checks `2^k ≤ q_i^16` and
`(q_{i+1} − q_i)² · (16·10⁶)² ≤ 11449 q_i (6931 k)²`, which gives
`q_{i+1} − q_i ≤ (107/100) √q_i (0.6931 k / 16) ≤ (107/100) √q_i log q_i` (`gap_le_107`). The check is
evaluated by `decide` in the kernel (no `native_decide`); primality of each entry is proved by
`norm_num`, in chunks of 40. The list was generated greedily (largest admissible prime at each
step, `scripts/shift_chain.py`).
-/

namespace Cramer.Shift

open Real

/-- Chunk 0 of the chain. -/
def chain107Chunk0 : List (ℕ × ℕ) := [(2, 16), (3, 25), (5, 37), (7, 44), (11, 55), (19, 67), (31, 79), (47, 88), (73, 99), (109, 108), (157, 116), (223, 124), (307, 132), (409, 138), (523, 144), (673, 150), (853, 155), (1061, 160), (1301, 165), (1571, 169), (1879, 174), (2221, 177), (2593, 181), (3019, 184), (3469, 188), (3967, 191), (4523, 194), (5119, 197), (5749, 199), (6427, 202), (7177, 204), (7963, 207), (8819, 209), (9721, 211), (10667, 214), (11689, 216), (12763, 218), (13903, 220), (15101, 222), (16363, 223)]

theorem chain107_prime_0 : ∀ e ∈ chain107Chunk0, e.1.Prime := by
  simp only [chain107Chunk0, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Chunk 1 of the chain. -/
def chain107Chunk1 : List (ℕ × ℕ) := [(17683, 225), (19069, 227), (20521, 229), (22039, 230), (23609, 232), (25261, 233), (26959, 235), (28729, 236), (30577, 238), (32503, 239), (34499, 241), (36571, 242), (38713, 243), (40927, 245), (43223, 246), (45589, 247), (48029, 248), (50543, 250), (53147, 251), (55829, 252), (58579, 253), (61417, 254), (64333, 255), (67307, 256), (70381, 257), (73529, 258), (76771, 259), (80077, 260), (83477, 261), (86969, 262), (90547, 263), (94207, 264), (97961, 265), (101797, 266), (105727, 267), (109751, 267), (113843, 268), (118033, 269), (122299, 270), (126653, 271)]

theorem chain107_prime_1 : ∀ e ∈ chain107Chunk1, e.1.Prime := by
  simp only [chain107Chunk1, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Chunk 2 of the chain. -/
def chain107Chunk2 : List (ℕ × ℕ) := [(131113, 272), (135671, 272), (140297, 273), (145031, 274), (149867, 275), (154799, 275), (159811, 276), (164911, 277), (170123, 278), (175433, 278), (180811, 279), (186301, 280), (191899, 280), (197573, 281), (203353, 282), (209233, 282), (215197, 283), (221281, 284), (227473, 284), (233747, 285), (240131, 285), (246599, 286), (253159, 287), (259841, 287), (266603, 288), (273473, 288), (280451, 289), (287537, 290), (294731, 290), (302009, 291), (309403, 291), (316903, 292), (324517, 292), (332221, 293), (340037, 294), (347983, 294), (355969, 295), (364127, 295), (372377, 296), (380729, 296)]

theorem chain107_prime_2 : ∀ e ∈ chain107Chunk2, e.1.Prime := by
  simp only [chain107Chunk2, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Chunk 3 of the chain. -/
def chain107Chunk3 : List (ℕ × ℕ) := [(389189, 297), (397763, 297), (406423, 298), (415213, 298), (424103, 299), (433123, 299), (442243, 300), (451481, 300), (460813, 301), (470279, 301), (479839, 301), (489493, 302), (499283, 302), (509149, 303), (519161, 303), (529273, 304), (539509, 304), (549839, 305), (560317, 305), (570887, 305), (581557, 306), (592369, 306), (603283, 307), (614333, 307), (625483, 308), (636773, 308), (648133, 308), (659621, 309), (671249, 309), (682967, 310), (694831, 310), (706801, 310), (718871, 311), (731057, 311), (743377, 312), (755813, 312), (768377, 312), (781051, 313), (793867, 313), (806791, 313)]

theorem chain107_prime_3 : ∀ e ∈ chain107Chunk3, e.1.Prime := by
  simp only [chain107Chunk3, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Chunk 4 of the chain. -/
def chain107Chunk4 : List (ℕ × ℕ) := [(819811, 314), (832987, 314), (846259, 315), (859681, 315), (873209, 315), (886819, 316), (900607, 316), (914491, 316), (928471, 317), (942607, 317), (956861, 317), (971207, 318), (985729, 318), (1000357, 318), (1015097, 319), (1029989, 319), (1044971, 319), (1060061, 320), (1075303, 320), (1090681, 320), (1106167, 321), (1121737, 321), (1137481, 321), (1153349, 322), (1169369, 322), (1185497, 322), (1201729, 323), (1218131, 323), (1234627, 323), (1251259, 324), (1268053, 324), (1284937, 324), (1301959, 324), (1319083, 325), (1336343, 325), (1353743, 325), (1371263, 326), (1388953, 326), (1406707, 326), (1424603, 327)]

theorem chain107_prime_4 : ∀ e ∈ chain107Chunk4, e.1.Prime := by
  simp only [chain107Chunk4, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Chunk 5 of the chain. -/
def chain107Chunk5 : List (ℕ × ℕ) := [(1442669, 327), (1460867, 327), (1479173, 327), (1497593, 328), (1516189, 328), (1534901, 328), (1553729, 329), (1572731, 329), (1591841, 329), (1611079, 329), (1630429, 330), (1649959, 330), (1669597, 330), (1689353, 331), (1709287, 331), (1729333, 331), (1749499, 331), (1769791, 332), (1790233, 332), (1810819, 332), (1831523, 332), (1852327, 333), (1873321, 333), (1894439, 333), (1915663, 333), (1937017, 334), (1958563, 334), (1980227, 334), (2002009, 334), (2023913, 335), (2045999, 335), (2068201, 335), (2090509, 335), (2112953, 336), (2135563, 336), (2158307, 336), (2181173, 336), (2204173, 337), (2227361, 337), (2250671, 337)]

theorem chain107_prime_5 : ∀ e ∈ chain107Chunk5, e.1.Prime := by
  simp only [chain107Chunk5, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Chunk 6 of the chain. -/
def chain107Chunk6 : List (ℕ × ℕ) := [(2274101, 337), (2297653, 338), (2321399, 338), (2345261, 338), (2369251, 338), (2393351, 339), (2417609, 339), (2442019, 339), (2466571, 339), (2491243, 339), (2516021, 340), (2541001, 340), (2566097, 340), (2591333, 340), (2616701, 341), (2642257, 341), (2667949, 341), (2693749, 341), (2719669, 341), (2745731, 342), (2771971, 342), (2798363, 342), (2824879, 342), (2851481, 343), (2878313, 343), (2905267, 343), (2932357, 343), (2959559, 343), (2986889, 344), (3014399, 344), (3042079, 344), (3069889, 344), (3097813, 345), (3125957, 345), (3154223, 345), (3182623, 345), (3211151, 345), (3239791, 346), (3268651, 346), (3297617, 346)]

theorem chain107_prime_6 : ∀ e ∈ chain107Chunk6, e.1.Prime := by
  simp only [chain107Chunk6, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Chunk 7 of the chain. -/
def chain107Chunk7 : List (ℕ × ℕ) := [(3326717, 346), (3355949, 346), (3385313, 347), (3414893, 347), (3444607, 347), (3474439, 347), (3504407, 347), (3534497, 348), (3564817, 348), (3595271, 348), (3625849, 348), (3656561, 348), (3687403, 349), (3718459, 349), (3749633, 349), (3780949, 349), (3812399, 349), (3843977, 349), (3875681, 350), (3907613, 350), (3939673, 350), (3971861, 350), (4004191, 350), (4036649, 351), (4069333, 351), (4102141, 351), (4135069, 351), (4168133, 351), (4201343, 352), (4234781, 352), (4268339, 352), (4302043, 352), (4335883, 352), (4369801, 352), (4403881, 353), (4438211, 353), (4472651, 353), (4507249, 353), (4541981, 353), (4576849, 354)]

theorem chain107_prime_7 : ∀ e ∈ chain107Chunk7, e.1.Prime := by
  simp only [chain107Chunk7, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Chunk 8 of the chain. -/
def chain107Chunk8 : List (ℕ × ℕ) := [(4611931, 354), (4647157, 354), (4682527, 354), (4718033, 354), (4753657, 354), (4789409, 355), (4825369, 355), (4861501, 355), (4897777, 355), (4934183, 355), (4970729, 355), (5007413, 356), (5044307, 356), (5081339, 356), (5118517, 356), (5155849, 356), (5193301, 356), (5230889, 357), (5268727, 357), (5306701, 357), (5344813, 357), (5383039, 357), (5421421, 357), (5459939, 358), (5498707, 358), (5537611, 358), (5576657, 358), (5615833, 358), (5655137, 358), (5694581, 359), (5734283, 359), (5774129, 359), (5814113, 359), (5854207, 359), (5894443, 359), (5934839, 360), (5975447, 360), (6016229, 360), (6057157, 360), (6098171, 360)]

theorem chain107_prime_8 : ∀ e ∈ chain107Chunk8, e.1.Prime := by
  simp only [chain107Chunk8, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Chunk 9 of the chain. -/
def chain107Chunk9 : List (ℕ × ℕ) := [(6139369, 360), (6180689, 360), (6222173, 361), (6263879, 361), (6305737, 361), (6347753, 361), (6389899, 361), (6432193, 361), (6474623, 362), (6517309, 362), (6560143, 362), (6603083, 362), (6646193, 362), (6689429, 362), (6732823, 362), (6776351, 363), (6820147, 363), (6864079, 363), (6908149, 363), (6952367, 363), (6996721, 363), (7041193, 363), (7085839, 364), (7130749, 364), (7175783, 364), (7220977, 364), (7266313, 364), (7311779, 364), (7357373, 364), (7403131, 365), (7449151, 365), (7495321, 365), (7541627, 365), (7588073, 365), (7634657, 365), (7681403, 365), (7728271, 366), (7775429, 366), (7822733, 366), (7870157, 366)]

theorem chain107_prime_9 : ∀ e ∈ chain107Chunk9, e.1.Prime := by
  simp only [chain107Chunk9, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Chunk 10 of the chain. -/
def chain107Chunk10 : List (ℕ × ℕ) := [(7917743, 366), (7965473, 366), (8013329, 366), (8061343, 367), (8109617, 367), (8158027, 367), (8206603, 367), (8255323, 367), (8304193, 367), (8353207, 367), (8402371, 368), (8451811, 368), (8501399, 368), (8551099, 368), (8600971, 368), (8650981, 368), (8701141, 368), (8751451, 368), (8801911, 369), (8852647, 369), (8903509, 369), (8954531, 369), (9005693, 369), (9057017, 369), (9108487, 369), (9160103, 370), (9211999, 370), (9264041, 370), (9316231, 370), (9368573, 370), (9421063, 370), (9473701, 370), (9526487, 370), (9579413, 371), (9632629, 371), (9685997, 371), (9739493, 371), (9793159, 371), (9846953, 371), (9900907, 371)]

theorem chain107_prime_10 : ∀ e ∈ chain107Chunk10, e.1.Prime := by
  simp only [chain107Chunk10, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Chunk 11 of the chain. -/
def chain107Chunk11 : List (ℕ × ℕ) := [(9955009, 371), (10009253, 372), (10063793, 372), (10118473, 372), (10173313, 372), (10228303, 372), (10283423, 372), (10338697, 372), (10394129, 372), (10449701, 373), (10505563, 373), (10561583, 373), (10617769, 373), (10674101, 373), (10730569, 373), (10787191, 373), (10843957, 373), (10900849, 374), (10958063, 374), (11015423, 374), (11072951, 374), (11130629, 374), (11188453, 374), (11246437, 374), (11304547, 374), (11362823, 375), (11421401, 375), (11480141, 375), (11539027, 375), (11598053, 375), (11657237, 375), (11716571, 375), (11776057, 375), (11835661, 375), (11895437, 376), (11955533, 376), (12015781, 376), (12076193, 376), (12136741, 376), (12197443, 376)]

theorem chain107_prime_11 : ∀ e ∈ chain107Chunk11, e.1.Prime := by
  simp only [chain107Chunk11, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Chunk 12 of the chain. -/
def chain107Chunk12 : List (ℕ × ℕ) := [(12258307, 376), (12319313, 376), (12380453, 376), (12441769, 377), (12503371, 377), (12565139, 377), (12627049, 377), (12689143, 377), (12751381, 377), (12813761, 377), (12876301, 377), (12938987, 378), (13001993, 378), (13065149, 378), (13128461, 378), (13191929, 378), (13255553, 378), (13319311, 378), (13383241, 378), (13447331, 378), (13511569, 379), (13576133, 379), (13640849, 379), (13705697, 379), (13770709, 379), (13835897, 379), (13901231, 379), (13966721, 379), (14032349, 379), (14098153, 379), (14164109, 380), (14230397, 380), (14296829, 380), (14363423, 380), (14430149, 380), (14497051, 380), (14564113, 380), (14631329, 380), (14698699, 380), (14766223, 381)]

theorem chain107_prime_12 : ∀ e ∈ chain107Chunk12, e.1.Prime := by
  simp only [chain107Chunk12, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Chunk 13 of the chain. -/
def chain107Chunk13 : List (ℕ × ℕ) := [(14834069, 381), (14902079, 381), (14970211, 381), (15038537, 381), (15106997, 381), (15175621, 381), (15244409, 381), (15313357, 381), (15382459, 381), (15451721, 382), (15521299, 382), (15591049, 382), (15660949, 382), (15730999, 382), (15801223, 382), (15871577, 382), (15942109, 382), (16012783, 382), (16083619, 383), (16154791, 383), (16226141, 383), (16297643, 383), (16369303, 383), (16441127, 383), (16513087, 383), (16585223, 383), (16657517, 383), (16729963, 383), (16802573, 384), (16875527, 384), (16948619, 384), (17021831, 384), (17095207, 384), (17168719, 384), (17242457, 384), (17316331, 384), (17390393, 384), (17464607, 384), (17538977, 385), (17613691, 385)]

theorem chain107_prime_13 : ∀ e ∈ chain107Chunk13, e.1.Prime := by
  simp only [chain107Chunk13, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Chunk 14 of the chain. -/
def chain107Chunk14 : List (ℕ × ℕ) := [(17688581, 385), (17763593, 385), (17838787, 385), (17914153, 385), (17989667, 385), (18065329, 385), (18141173, 385), (18217159, 385), (18293311, 385), (18369623, 386), (18446303, 386), (18523111, 386), (18600097, 386), (18677257, 386), (18754559, 386), (18832031, 386), (18909629, 386), (18987391, 386), (19065329, 386), (19143437, 387), (19221913, 387), (19300537, 387), (19379333, 387), (19458287, 387), (19537391, 387), (19616671, 387), (19696097, 387), (19775671, 387), (19855427, 387), (19935353, 387), (20015431, 388), (20095883, 388), (20176483, 388), (20257261, 388), (20338181, 388), (20419283, 388), (20500541, 388), (20581961, 388), (20663543, 388), (20745289, 388)]

theorem chain107_prime_14 : ∀ e ∈ chain107Chunk14, e.1.Prime := by
  simp only [chain107Chunk14, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Chunk 15 of the chain. -/
def chain107Chunk15 : List (ℕ × ℕ) := [(20827199, 388), (20909209, 389), (20991653, 389), (21074239, 389), (21156953, 389), (21239839, 389), (21322901, 389), (21406157, 389), (21489557, 389), (21573131, 389), (21656867, 389), (21740767, 389), (21824819, 390), (21909263, 390), (21993871, 390), (22078633, 390), (22163539, 390), (22248593, 390), (22333783, 390), (22419179, 390), (22504763, 390), (22590517, 390), (22676417, 390), (22762489, 391), (22848941, 391), (22935571, 391), (23022347, 391), (23109283, 391), (23196403, 391), (23283671, 391), (23371111, 391), (23458679, 391), (23546447, 391), (23634383, 391), (23722483, 391), (23810749, 392), (23899409, 392), (23988233, 392), (24077213, 392), (24166349, 392)]

theorem chain107_prime_15 : ∀ e ∈ chain107Chunk15, e.1.Prime := by
  simp only [chain107Chunk15, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Chunk 16 of the chain. -/
def chain107Chunk16 : List (ℕ × ℕ) := [(24255643, 392), (24345091, 392), (24434737, 392), (24524551, 392), (24614501, 392), (24704629, 392), (24794909, 393), (24885577, 393), (24976429, 393), (25067461, 393), (25158649, 393), (25250003, 393), (25341529, 393), (25433179, 393), (25525043, 393), (25617041, 393), (25709237, 393), (25801553, 393), (25894031, 394), (25986953, 394), (26080039, 394), (26173271, 394), (26266699, 394), (26360291, 394), (26454041, 394), (26547967, 394), (26642059, 394), (26736319, 394), (26830747, 394), (26925323, 394), (27020023, 395), (27115163, 395), (27210461, 395), (27305951, 395), (27401617, 395), (27497447, 395), (27593437, 395), (27689611, 395), (27785911, 395), (27882403, 395)]

theorem chain107_prime_16 : ∀ e ∈ chain107Chunk16, e.1.Prime := by
  simp only [chain107Chunk16, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Chunk 17 of the chain. -/
def chain107Chunk17 : List (ℕ × ℕ) := [(27979079, 395), (28075909, 395), (28172917, 395), (28270093, 396), (28367681, 396), (28465433, 396), (28563361, 396), (28661447, 396), (28759681, 396), (28858111, 396), (28956679, 396), (29055443, 396), (29154373, 396), (29253467, 396), (29352733, 396), (29452169, 396), (29551777, 397), (29651803, 397), (29751973, 397), (29852327, 397), (29952847, 397), (30053549, 397), (30154427, 397), (30255413, 397), (30356629, 397), (30458011, 397), (30559553, 397), (30661273, 397), (30763163, 397), (30865223, 398), (30967709, 398), (31070363, 398), (31173187, 398), (31276183, 398), (31379351, 398), (31482683, 398), (31586171, 398), (31689841, 398), (31793683, 398), (31897699, 398)]

theorem chain107_prime_17 : ∀ e ∈ chain107Chunk17, e.1.Prime := by
  simp only [chain107Chunk17, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Chunk 18 of the chain. -/
def chain107Chunk18 : List (ℕ × ℕ) := [(32001829, 398), (32106187, 398), (32210701, 399), (32315663, 399), (32420771, 399), (32526073, 399), (32631541, 399), (32737181, 399), (32842991, 399), (32948947, 399), (33055103, 399), (33161419, 399), (33267911, 399), (33374573, 399), (33481397, 399), (33588337, 400), (33695777, 400), (33803381, 400), (33911161, 400), (34019113, 400), (34127237, 400), (34235527, 400), (34343987, 400), (34452631, 400), (34561453, 400), (34670437, 400), (34779599, 400), (34888937, 400), (34998413, 400), (35108069, 401), (35218199, 401), (35328481, 401), (35438917, 401), (35549557, 401), (35660377, 401), (35771327, 401), (35882491, 401), (35993813, 401), (36105317, 401), (36216989, 401)]

theorem chain107_prime_18 : ∀ e ∈ chain107Chunk18, e.1.Prime := by
  simp only [chain107Chunk18, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Chunk 19 of the chain. -/
def chain107Chunk19 : List (ℕ × ℕ) := [(36328819, 401), (36440827, 401), (36552991, 401), (36665359, 402), (36778169, 402), (36891163, 402), (37004333, 402), (37117673, 402), (37231189, 402), (37344799, 402), (37458661, 402), (37572701, 402), (37686911, 402), (37801289, 402), (37915841, 402), (38030543, 402), (38145449, 402), (38260529, 403), (38376053, 403), (38491763, 403), (38607641, 403), (38723701, 403), (38839921, 403), (38956331, 403), (39072907, 403), (39189659, 403), (39306593, 403), (39423701, 403), (39540973, 403), (39658391, 403), (39776003, 403), (39893801, 403), (40011781, 404), (40130221, 404), (40248823, 404), (40367597, 404), (40486561, 404), (40605701, 404), (40725023, 404), (40844519, 404)]

theorem chain107_prime_19 : ∀ e ∈ chain107Chunk19, e.1.Prime := by
  simp only [chain107Chunk19, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Chunk 20 of the chain. -/
def chain107Chunk20 : List (ℕ × ℕ) := [(40964191, 404), (41084011, 404), (41204029, 404), (41324207, 404), (41444581, 404), (41565127, 404), (41685827, 405), (41807023, 405), (41928389, 405), (42049939, 405), (42171631, 405), (42293533, 405), (42415601, 405), (42537857, 405), (42660271, 405), (42782879, 405), (42905657, 405), (43028617, 405), (43151743, 405), (43275041, 405), (43398491, 405), (43522153, 406), (43646299, 406), (43770619, 406), (43895083, 406), (44019761, 406), (44144561, 406), (44269571, 406), (44394739, 406), (44520109, 406), (44645669, 406), (44771399, 406), (44897309, 406), (45023393, 406), (45149647, 406), (45276079, 406), (45402701, 406), (45529501, 407), (45656783, 407), (45784231, 407)]

theorem chain107_prime_20 : ∀ e ∈ chain107Chunk20, e.1.Prime := by
  simp only [chain107Chunk20, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Chunk 21 of the chain. -/
def chain107Chunk21 : List (ℕ × ℕ) := [(45911867, 407), (46039667, 407), (46167661, 407), (46295831, 407), (46424153, 407), (46552687, 407), (46681399, 407), (46810277, 407), (46939303, 407), (47068547, 407), (47197963, 407), (47327519, 407), (47457283, 408), (47587549, 408), (47717993, 408), (47848627, 408), (47979439, 408), (48110423, 408), (48241591, 408), (48372923, 408), (48504433, 408), (48636121, 408), (48768001, 408), (48900013, 408), (49032253, 408), (49164673, 408), (49297271, 408), (49430047, 408), (49562987, 409), (49696411, 409), (49830049, 409), (49963831, 409), (50097811, 409), (50231989, 409), (50366347, 409), (50500871, 409), (50635549, 409), (50770441, 409), (50905513, 409), (51040763, 409)]

theorem chain107_prime_21 : ∀ e ∈ chain107Chunk21, e.1.Prime := by
  simp only [chain107Chunk21, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Chunk 22 of the chain. -/
def chain107Chunk22 : List (ℕ × ℕ) := [(51176201, 409), (51311809, 409), (51447589, 409), (51583517, 409), (51719659, 409), (51855989, 410), (51992827, 410), (52129853, 410), (52267049, 410), (52404431, 410), (52541963, 410), (52679713, 410), (52817621, 410), (52955681, 410), (53093951, 410), (53232407, 410), (53371039, 410), (53509867, 410), (53648849, 410), (53788039, 410), (53927399, 410), (54066941, 411), (54207011, 411), (54347269, 411), (54487681, 411), (54628283, 411), (54769073, 411), (54910049, 411), (55051207, 411), (55192541, 411), (55334057, 411), (55475723, 411), (55617593, 411), (55759651, 411), (55901893, 411), (56044301, 411), (56186903, 411), (56329681, 411), (56472653, 412), (56616151, 412)]

theorem chain107_prime_22 : ∀ e ∈ chain107Chunk22, e.1.Prime := by
  simp only [chain107Chunk22, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Chunk 23 of the chain. -/
def chain107Chunk23 : List (ℕ × ℕ) := [(56759827, 412), (56903683, 412), (57047651, 412), (57191867, 412), (57336269, 412), (57480853, 412), (57625627, 412), (57770563, 412), (57915709, 412), (58061033, 412), (58206541, 412), (58352233, 412), (58498109, 412), (58644167, 412), (58790393, 412), (58936799, 413), (59083723, 413), (59230861, 413), (59378177, 413), (59525671, 413), (59673353, 413), (59821219, 413), (59969249, 413), (60117461, 413), (60265847, 413), (60414391, 413), (60563159, 413), (60712123, 413), (60861257, 413), (61010597, 413), (61160111, 413), (61309811, 413), (61459693, 413), (61609727, 414), (61760329, 414), (61911133, 414), (62062111, 414), (62213279, 414), (62364613, 414), (62516149, 414)]

theorem chain107_prime_23 : ∀ e ∈ chain107Chunk23, e.1.Prime := by
  simp only [chain107Chunk23, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Chunk 24 of the chain. -/
def chain107Chunk24 : List (ℕ × ℕ) := [(62667863, 414), (62819767, 414), (62971829, 414), (63124069, 414), (63276527, 414), (63429169, 414), (63581971, 414), (63734971, 414), (63888137, 414), (64041517, 414), (64195073, 414), (64348813, 415), (64503113, 415), (64657597, 415), (64812257, 415), (64967107, 415), (65122147, 415), (65277367, 415), (65432753, 415), (65588321, 415), (65744101, 415), (65900059, 415), (66056209, 415), (66212543, 415), (66369013, 415), (66525691, 415), (66682573, 415), (66839621, 415), (66996877, 415), (67154317, 416), (67312321, 416), (67470511, 416), (67628851, 416), (67787411, 416), (67946129, 416), (68105027, 416), (68264143, 416), (68423447, 416), (68582933, 416), (68742613, 416)]

theorem chain107_prime_24 : ∀ e ∈ chain107Chunk24, e.1.Prime := by
  simp only [chain107Chunk24, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Chunk 25 of the chain. -/
def chain107Chunk25 : List (ℕ × ℕ) := [(68902481, 416), (69062533, 416), (69222773, 416), (69383183, 416), (69543737, 416), (69704527, 416), (69865493, 416), (70026653, 416), (70188007, 417), (70349899, 417), (70511999, 417), (70674301, 417), (70836749, 417), (70999403, 417), (71162263, 417), (71325311, 417), (71488517, 417), (71651917, 417), (71815519, 417), (71979311, 417), (72143287, 417), (72307453, 417), (72471809, 417), (72636349, 417), (72801067, 417), (72965953, 417), (73131041, 417), (73296317, 418), (73462183, 418), (73628227, 418), (73794443, 418), (73960879, 418), (74127499, 418), (74294309, 418), (74461259, 418), (74628443, 418), (74795813, 418), (74963321, 418), (75131047, 418), (75298963, 418)]

theorem chain107_prime_25 : ∀ e ∈ chain107Chunk25, e.1.Prime := by
  simp only [chain107Chunk25, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Chunk 26 of the chain. -/
def chain107Chunk26 : List (ℕ × ℕ) := [(75467059, 418), (75635359, 418), (75803831, 418), (75972517, 418), (76141357, 418), (76310413, 418), (76479653, 419), (76649491, 419), (76819469, 419), (76989673, 419), (77160077, 419), (77330653, 419), (77501429, 419), (77672383, 419), (77843533, 419), (78014837, 419), (78186343, 419), (78358069, 419), (78529973, 419), (78702073, 419), (78874363, 419), (79046827, 419), (79219489, 419), (79392323, 419), (79565359, 419), (79738579, 419), (79911983, 420), (80086009, 420), (80260223, 420), (80434621, 420), (80609209, 420), (80783959, 420), (80958929, 420), (81134089, 420), (81309433, 420), (81484967, 420), (81660659, 420), (81836569, 420), (82012661, 420), (82188941, 420)]

theorem chain107_prime_26 : ∀ e ∈ chain107Chunk26, e.1.Prime := by
  simp only [chain107Chunk26, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Chunk 27 of the chain. -/
def chain107Chunk27 : List (ℕ × ℕ) := [(82365421, 420), (82542077, 420), (82718903, 420), (82895957, 420), (83073191, 420), (83250613, 420), (83428237, 421), (83606461, 421), (83784887, 421), (83963461, 421), (84142259, 421), (84321253, 421), (84500441, 421), (84679799, 421), (84859367, 421), (85039099, 421), (85219039, 421), (85399169, 421), (85579453, 421), (85759957, 421), (85940663, 421), (86121527, 421), (86302613, 421), (86483869, 421), (86665309, 421), (86846957, 421), (87028807, 421), (87210787, 422), (87393389, 422), (87576217, 422), (87759263, 422), (87942497, 422), (88125859, 422), (88309453, 422), (88493261, 422), (88677241, 422), (88861433, 422), (89045807, 422), (89230367, 422), (89415133, 422)]

theorem chain107_prime_27 : ∀ e ∈ chain107Chunk27, e.1.Prime := by
  simp only [chain107Chunk27, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Chunk 28 of the chain. -/
def chain107Chunk28 : List (ℕ × ℕ) := [(89600087, 422), (89785219, 422), (89970533, 422), (90156061, 422), (90341759, 422), (90527663, 422), (90713767, 422), (90900041, 423), (91086967, 423), (91274087, 423), (91461371, 423), (91648873, 423), (91836571, 423), (92024447, 423), (92212517, 423), (92400793, 423), (92589209, 423), (92777863, 423), (92966711, 423), (93155737, 423), (93344963, 423), (93534377, 423), (93723983, 423), (93913777, 423), (94103777, 423), (94293967, 423), (94484329, 423), (94674889, 423), (94865623, 423), (95056561, 424), (95248169, 424), (95439943, 424), (95631923, 424), (95824111, 424), (96016471, 424), (96209041, 424), (96401807, 424), (96594749, 424), (96787891, 424), (96981229, 424)]

theorem chain107_prime_28 : ∀ e ∈ chain107Chunk28, e.1.Prime := by
  simp only [chain107Chunk28, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Chunk 29 of the chain. -/
def chain107Chunk29 : List (ℕ × ℕ) := [(97174729, 424), (97368451, 424), (97562299, 424), (97756411, 424), (97950703, 424), (98145197, 424), (98339797, 424), (98534621, 424), (98729663, 424), (98924933, 424), (99120391, 425), (99316513, 425), (99512801, 425), (99709289, 425), (99905987, 425), (100102841, 425)]

theorem chain107_prime_29 : ∀ e ∈ chain107Chunk29, e.1.Prime := by
  simp only [chain107Chunk29, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- The checked chain of primes, each with `⌊16 log₂ q⌋`. -/
def primeChain107 : List (ℕ × ℕ) := chain107Chunk0 ++ chain107Chunk1 ++ chain107Chunk2 ++ chain107Chunk3 ++ chain107Chunk4 ++ chain107Chunk5 ++ chain107Chunk6 ++ chain107Chunk7 ++ chain107Chunk8 ++ chain107Chunk9 ++ chain107Chunk10 ++ chain107Chunk11 ++ chain107Chunk12 ++ chain107Chunk13 ++ chain107Chunk14 ++ chain107Chunk15 ++ chain107Chunk16 ++ chain107Chunk17 ++ chain107Chunk18 ++ chain107Chunk19 ++ chain107Chunk20 ++ chain107Chunk21 ++ chain107Chunk22 ++ chain107Chunk23 ++ chain107Chunk24 ++ chain107Chunk25 ++ chain107Chunk26 ++ chain107Chunk27 ++ chain107Chunk28 ++ chain107Chunk29

/-- The arithmetic check: `2^k ≤ p^16` at every node, and the gap condition between neighbours. -/
def chainOK107 : ℕ × ℕ → List (ℕ × ℕ) → Bool
  | (p, k), [] => decide (2 ^ k ≤ p ^ 16)
  | (p, k), (q, k') :: l =>
      decide (2 ^ k ≤ p ^ 16) && decide (p < q)
        && decide ((q - p) ^ 2 * (16 * 10 ^ 6) ^ 2 ≤ 11449 * p * (6931 * k) ^ 2) && chainOK107 (q, k') l

set_option maxRecDepth 100000 in
theorem primeChain107_ok : chainOK107 (2, 16) primeChain107.tail = true := by decide +kernel

theorem primeChain107_head : primeChain107 = (2, 16) :: primeChain107.tail := by decide +kernel

set_option maxRecDepth 100000 in
theorem primeChain107_last : lastP 2 primeChain107.tail = 100102841 := by decide +kernel

theorem primeChain107_prime : ∀ e ∈ primeChain107, e.1.Prime := by
  rw [primeChain107]
  simp only [List.forall_mem_append, and_assoc]
  exact ⟨chain107_prime_0, chain107_prime_1, chain107_prime_2, chain107_prime_3, chain107_prime_4, chain107_prime_5, chain107_prime_6, chain107_prime_7, chain107_prime_8, chain107_prime_9, chain107_prime_10, chain107_prime_11, chain107_prime_12, chain107_prime_13, chain107_prime_14, chain107_prime_15, chain107_prime_16, chain107_prime_17, chain107_prime_18, chain107_prime_19, chain107_prime_20, chain107_prime_21, chain107_prime_22, chain107_prime_23, chain107_prime_24, chain107_prime_25, chain107_prime_26, chain107_prime_27, chain107_prime_28, chain107_prime_29⟩

/-- `2^k ≤ p^16` gives `0.6931 k / 16 ≤ log p`. -/
lemma log_ge_of_pow_le_107 {p k : ℕ} (hp : 2 ^ k ≤ p ^ 16) (_hp1 : 1 ≤ p) :
    0.6931 * (k : ℝ) / 16 ≤ Real.log p := by
  have h1 : Real.log ((2 : ℝ) ^ k) ≤ Real.log ((p : ℝ) ^ 16) :=
    Real.log_le_log (by positivity) (by exact_mod_cast hp)
  rw [Real.log_pow, Real.log_pow] at h1
  have := Real.log_two_gt_d9
  have hk : (0 : ℝ) ≤ k := k.cast_nonneg
  push_cast at h1
  nlinarith

/-- The gap condition implies `q ≤ p + (107/100) √p log p`. -/
lemma gap_le_107 {p q k : ℕ} (hp : 2 ^ k ≤ p ^ 16) (hpq : p < q)
    (hg : (q - p) ^ 2 * (16 * 10 ^ 6) ^ 2 ≤ 11449 * p * (6931 * k) ^ 2) :
    (q : ℝ) ≤ p + 107 / 100 * √(p : ℝ) * Real.log p := by
  have hp1 : 1 ≤ p := by
    rcases Nat.eq_zero_or_pos p with h | h
    · subst h; simp at hp
    · exact h
  have hlog := log_ge_of_pow_le_107 hp hp1
  set X := 107 / 100 * √(p : ℝ) * (0.6931 * k / 16) with hX
  have hX0 : 0 ≤ X := by positivity
  have hg' : ((q : ℝ) - p) ^ 2 ≤ X ^ 2 := by
    have h1 : (((q - p) ^ 2 * (16 * 10 ^ 6) ^ 2 : ℕ) : ℝ) ≤ ((11449 * p * (6931 * k) ^ 2 : ℕ) : ℝ) := by
      exact_mod_cast hg
    push_cast [Nat.cast_sub hpq.le] at h1
    rw [hX, mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
    nlinarith
  have hq : (q : ℝ) - p ≤ X := by
    by_contra hc
    push Not at hc
    nlinarith
  have : X ≤ 107 / 100 * √(p : ℝ) * Real.log p :=
    mul_le_mul_of_nonneg_left hlog (by positivity)
  linarith

/-- `x ↦ x + (107/100)√x log x` is monotone on `[1, ∞)`. -/
lemma step_mono_107 {p y : ℝ} (hp : 1 ≤ p) (hpy : p ≤ y) :
    p + 107 / 100 * √p * Real.log p ≤ y + 107 / 100 * √y * Real.log y := by
  have h1 : √p ≤ √y := Real.sqrt_le_sqrt hpy
  have h2 : Real.log p ≤ Real.log y := Real.log_le_log (by linarith) hpy
  have h3 : 0 ≤ Real.log p := Real.log_nonneg hp
  have h4 : 0 ≤ √p := Real.sqrt_nonneg _
  have h5 : √p * Real.log p ≤ √y * Real.log y :=
    mul_le_mul h1 h2 h3 (by linarith)
  linarith

/-- Walking a checked chain. -/
theorem exists_prime_of_chain_107 : ∀ (L : List (ℕ × ℕ)) (p k : ℕ), chainOK107 (p, k) L = true →
    p.Prime → (∀ e ∈ L, e.1.Prime) → ∀ y : ℝ, (p : ℝ) ≤ y → y < lastP p L →
    ∃ q : ℕ, q.Prime ∧ y < q ∧ (q : ℝ) ≤ y + 107 / 100 * √y * Real.log y
  | [], p, k, _, _, _, y, hpy, hy => by simp [lastP] at hy; linarith
  | (q, k') :: l, p, k, hc, hp, hl, y, hpy, hy => by
    simp only [chainOK107, Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨hpk, hpq⟩, hg⟩, hc'⟩ := hc
    have hq : q.Prime := hl (q, k') (by simp)
    rcases lt_or_ge y q with h | h
    · refine ⟨q, hq, h, ?_⟩
      have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
      exact (gap_le_107 hpk hpq hg).trans (step_mono_107 hp1 hpy)
    · exact exists_prime_of_chain_107 l q k' hc' hq (fun e he => hl e (by simp [he])) y h
        (by simpa [lastP] using hy)

/-- **Every `(x, x + (107/100)√x log x]` with `2 ≤ x < 10^8` contains a prime** (no hypothesis). -/
theorem exists_prime_small_107 {x : ℝ} (hx2 : 2 ≤ x) (hx : x < 10 ^ 8) :
    ∃ p : ℕ, p.Prime ∧ x < p ∧ (p : ℝ) ≤ x + 107 / 100 * √x * Real.log x := by
  have hall := primeChain107_prime
  rw [primeChain107_head] at hall
  refine exists_prime_of_chain_107 primeChain107.tail 2 16 primeChain107_ok Nat.prime_two
    (fun e he => hall e (List.mem_cons_of_mem _ he)) x (by norm_num; linarith) ?_
  rw [primeChain107_last]; push_cast; linarith

end Cramer.Shift
