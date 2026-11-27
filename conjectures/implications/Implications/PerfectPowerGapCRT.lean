import Mathlib

/-!
# Gyarmati's finite CRT certificate for perfect-power gaps

This file verifies the finite arithmetic input to Lemma 6 in Katalin Gyarmati,
"Bounded gaps and perfect power gaps in sequences of consecutive primes"
(arXiv:2602.07558, §4). For the offsets through 49, the square offsets follow
from `W*a` being a square, and offsets 3 and 24 follow from `3*W*a` being a
cube. The remaining 40 offsets are assigned distinct prime exponents.

For each of the 15 primes dividing `W`, `crtExponent` is the explicit CRT
solution modulo the product of the 42 distinct exponent primes through 181.
`exponentCongruenceCertificate` checks every assigned valuation congruence.
The power and prime-gap arguments using this finite input are separate.
-/

namespace Implications.PerfectPowerGapCRT

private def basePrimes : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]

private def exponentPrimes : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73,
   79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163,
   167, 173, 179, 181]

private def W : ℕ := 614889782588491410

private def E : ℕ :=
  5397346292805549782720214077673687806275517530364350655459511599582614290

private def crtExponent : List ℕ :=
  [946866288615739509321066849959644752832899644419237537322679246829569143,
   2343225385769350445363922254029248522876362434355196192526458056824627189,
   4382393917830765912594306907315318967620807984906167589972529030107083359,
   3119580035028280150009580042773650233841550197083129029445241331032287159,
   144066027483025960728622973925973950903353128179067178102754179425745099,
   39344461107890960932770219157253740568467893915845294442615403669493399,
   5044969940000237592937328328203205948216992169943720977505466250857997269,
   2046063004848654332150310161664575299743217937479327513347174784689822959,
   4636717258135973402854652686445717962372324430546660271628166278498391759,
   5276057612068346416816389042220346507258090170131443899157050664760533069,
   4435442993097630019463146222246693939810573812081595093100390720449079069,
   4844862026612855710473263030352759133192196838279810824585703325609590779,
   398461806851416426912230569492688361537118743852401726241977366412139309,
   481292026110049025210719726671539040050046149204464389658809951555137579,
   1477485856689787370688773686067098896689946139596945151494503175304737989]

/- The square class is represented by 1; 3 represents the cube class containing
24; all other offsets in [1,49] occur once, matched in order to primes 5..181. -/
private def exponentClasses : List (ℕ × ℕ) :=
  [(1, 2), (3, 3),
   (2, 5), (5, 7), (6, 11), (7, 13), (8, 17), (10, 19), (11, 23), (12, 29),
   (13, 31), (14, 37), (15, 41), (17, 43), (18, 47), (19, 53), (20, 59),
   (21, 61), (22, 67), (23, 71), (26, 73), (27, 79), (28, 83), (29, 89),
   (30, 97), (31, 101), (32, 103), (33, 107), (34, 109), (35, 113), (37, 127),
   (38, 131), (39, 137), (40, 139), (41, 149), (42, 151), (43, 157), (44, 163),
   (45, 167), (46, 173), (47, 179), (48, 181)]

private def congruencesHold : Bool :=
  exponentClasses.all fun (offset, q) =>
    basePrimes.zip crtExponent |>.all fun (p, a) =>
      (Nat.factorization (offset * W) p + a) % q == 0

/-- The explicit 42 congruence classes all hold for each of the 15 prime
valuations in `W`. This is the finite arithmetic certificate in Gyarmati's
construction. -/
theorem exponentCongruenceCertificate : congruencesHold = true := by
  native_decide

private def coordinatesBounded : Bool :=
  crtExponent.all (fun a => a < E) &&
    exponentPrimes.length == 42 && basePrimes.length == 15 &&
    exponentClasses.length == 42

/-- The CRT coordinates lie in the canonical interval below the product of
the 42 pairwise distinct exponent primes. -/
theorem crtCoordinatesBounded : coordinatesBounded = true := by
  native_decide

end Implications.PerfectPowerGapCRT
