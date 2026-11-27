import Implications.WilfReversal
import Implications.WilfChainCertificate

/-!
# Reversed orientations of the archived Wilf chains

The local chains in `WilfChainCertificate` prove twelve exact Wilf equivalences.
This module applies simultaneous pattern and start reversal to each archived
pair. The rank lists below are the checked certificate patterns, written out
so the reversed statements have stable, readable names.
-/

namespace Implications.WilfArchiveOrientation

open WilfMarked WilfPatternSwap WilfChainCertificate WilfReversal

private def pattern34275681 : Fin 8 → Fin 8 := ![2, 3, 1, 6, 4, 5, 7, 0]
private def pattern34265781 : Fin 8 → Fin 8 := ![2, 3, 1, 5, 4, 6, 7, 0]
private def pattern45372681 : Fin 8 → Fin 8 := ![3, 4, 2, 6, 1, 5, 7, 0]
private def pattern45362781 : Fin 8 → Fin 8 := ![3, 4, 2, 5, 1, 6, 7, 0]
private def pattern56472381 : Fin 8 → Fin 8 := ![4, 5, 3, 6, 1, 2, 7, 0]
private def pattern56432781 : Fin 8 → Fin 8 := ![4, 5, 3, 2, 1, 6, 7, 0]
private def pattern45371682 : Fin 8 → Fin 8 := ![3, 4, 2, 6, 0, 5, 7, 1]
private def pattern45361782 : Fin 8 → Fin 8 := ![3, 4, 2, 5, 0, 6, 7, 1]
private def pattern56431782 : Fin 8 → Fin 8 := ![4, 5, 3, 2, 0, 6, 7, 1]
private def pattern56471382 : Fin 8 → Fin 8 := ![4, 5, 3, 6, 0, 2, 7, 1]
private def pattern67541382 : Fin 8 → Fin 8 := ![5, 6, 4, 3, 0, 2, 7, 1]
private def pattern67531482 : Fin 8 → Fin 8 := ![5, 6, 4, 2, 0, 3, 7, 1]
private def pattern34276581 : Fin 8 → Fin 8 := ![2, 3, 1, 6, 5, 4, 7, 0]
private def pattern34285671 : Fin 8 → Fin 8 := ![2, 3, 1, 7, 4, 5, 6, 0]
private def pattern34286571 : Fin 8 → Fin 8 := ![2, 3, 1, 7, 5, 4, 6, 0]
private def pattern45376281 : Fin 8 → Fin 8 := ![3, 4, 2, 6, 5, 1, 7, 0]
private def pattern56482371 : Fin 8 → Fin 8 := ![4, 5, 3, 7, 1, 2, 6, 0]
private def pattern56483271 : Fin 8 → Fin 8 := ![4, 5, 3, 7, 2, 1, 6, 0]
private def pattern45386271 : Fin 8 → Fin 8 := ![3, 4, 2, 7, 5, 1, 6, 0]
private def pattern45382671 : Fin 8 → Fin 8 := ![3, 4, 2, 7, 1, 5, 6, 0]
private def pattern56473281 : Fin 8 → Fin 8 := ![4, 5, 3, 6, 2, 1, 7, 0]

theorem exactOccurrenceCount_eq_reverse_archive_34275681_34265781
    (n : ℕ) (marks : Finset (Fin n)) :
    WilfCounts.exactCount (occurrenceSet (reversePattern pattern34275681)) marks =
      WilfCounts.exactCount (occurrenceSet (reversePattern pattern34265781)) marks :=
  exactOccurrenceCount_eq_reverse_of_eq n pattern34275681 pattern34265781
    (fun m => exactOccurrenceCount_eq_34275681_34265781 n m) marks

theorem exactOccurrenceCount_eq_reverse_archive_45372681_45362781
    (n : ℕ) (marks : Finset (Fin n)) :
    WilfCounts.exactCount (occurrenceSet (reversePattern pattern45372681)) marks =
      WilfCounts.exactCount (occurrenceSet (reversePattern pattern45362781)) marks :=
  exactOccurrenceCount_eq_reverse_of_eq n pattern45372681 pattern45362781
    (fun m => exactOccurrenceCount_eq_45372681_45362781 n m) marks

theorem exactOccurrenceCount_eq_reverse_archive_56472381_56432781
    (n : ℕ) (marks : Finset (Fin n)) :
    WilfCounts.exactCount (occurrenceSet (reversePattern pattern56472381)) marks =
      WilfCounts.exactCount (occurrenceSet (reversePattern pattern56432781)) marks :=
  exactOccurrenceCount_eq_reverse_of_eq n pattern56472381 pattern56432781
    (fun m => exactOccurrenceCount_eq_56472381_56432781 n m) marks

theorem exactOccurrenceCount_eq_reverse_archive_45371682_45361782
    (n : ℕ) (marks : Finset (Fin n)) :
    WilfCounts.exactCount (occurrenceSet (reversePattern pattern45371682)) marks =
      WilfCounts.exactCount (occurrenceSet (reversePattern pattern45361782)) marks :=
  exactOccurrenceCount_eq_reverse_of_eq n pattern45371682 pattern45361782
    (fun m => exactOccurrenceCount_eq_45371682_45361782 n m) marks

theorem exactOccurrenceCount_eq_reverse_archive_56431782_56471382
    (n : ℕ) (marks : Finset (Fin n)) :
    WilfCounts.exactCount (occurrenceSet (reversePattern pattern56431782)) marks =
      WilfCounts.exactCount (occurrenceSet (reversePattern pattern56471382)) marks :=
  exactOccurrenceCount_eq_reverse_of_eq n pattern56431782 pattern56471382
    (fun m => exactOccurrenceCount_eq_56431782_56471382 n m) marks

theorem exactOccurrenceCount_eq_reverse_archive_67541382_67531482
    (n : ℕ) (marks : Finset (Fin n)) :
    WilfCounts.exactCount (occurrenceSet (reversePattern pattern67541382)) marks =
      WilfCounts.exactCount (occurrenceSet (reversePattern pattern67531482)) marks :=
  exactOccurrenceCount_eq_reverse_of_eq n pattern67541382 pattern67531482
    (fun m => exactOccurrenceCount_eq_67541382_67531482 n m) marks

theorem exactOccurrenceCount_eq_reverse_archive_34275681_34276581
    (n : ℕ) (marks : Finset (Fin n)) :
    WilfCounts.exactCount (occurrenceSet (reversePattern pattern34275681)) marks =
      WilfCounts.exactCount (occurrenceSet (reversePattern pattern34276581)) marks :=
  exactOccurrenceCount_eq_reverse_of_eq n pattern34275681 pattern34276581
    (fun m => exactOccurrenceCount_eq_34275681_34276581 n m) marks

theorem exactOccurrenceCount_eq_reverse_archive_34285671_34286571
    (n : ℕ) (marks : Finset (Fin n)) :
    WilfCounts.exactCount (occurrenceSet (reversePattern pattern34285671)) marks =
      WilfCounts.exactCount (occurrenceSet (reversePattern pattern34286571)) marks :=
  exactOccurrenceCount_eq_reverse_of_eq n pattern34285671 pattern34286571
    (fun m => exactOccurrenceCount_eq_34285671_34286571 n m) marks

theorem exactOccurrenceCount_eq_reverse_archive_45376281_45372681
    (n : ℕ) (marks : Finset (Fin n)) :
    WilfCounts.exactCount (occurrenceSet (reversePattern pattern45376281)) marks =
      WilfCounts.exactCount (occurrenceSet (reversePattern pattern45372681)) marks :=
  exactOccurrenceCount_eq_reverse_of_eq n pattern45376281 pattern45372681
    (fun m => exactOccurrenceCount_eq_45376281_45372681 n m) marks

theorem exactOccurrenceCount_eq_reverse_archive_56482371_56483271
    (n : ℕ) (marks : Finset (Fin n)) :
    WilfCounts.exactCount (occurrenceSet (reversePattern pattern56482371)) marks =
      WilfCounts.exactCount (occurrenceSet (reversePattern pattern56483271)) marks :=
  exactOccurrenceCount_eq_reverse_of_eq n pattern56482371 pattern56483271
    (fun m => exactOccurrenceCount_eq_56482371_56483271 n m) marks

theorem exactOccurrenceCount_eq_reverse_archive_45386271_45382671
    (n : ℕ) (marks : Finset (Fin n)) :
    WilfCounts.exactCount (occurrenceSet (reversePattern pattern45386271)) marks =
      WilfCounts.exactCount (occurrenceSet (reversePattern pattern45382671)) marks :=
  exactOccurrenceCount_eq_reverse_of_eq n pattern45386271 pattern45382671
    (fun m => exactOccurrenceCount_eq_45386271_45382671 n m) marks

theorem exactOccurrenceCount_eq_reverse_archive_56472381_56473281
    (n : ℕ) (marks : Finset (Fin n)) :
    WilfCounts.exactCount (occurrenceSet (reversePattern pattern56472381)) marks =
      WilfCounts.exactCount (occurrenceSet (reversePattern pattern56473281)) marks :=
  exactOccurrenceCount_eq_reverse_of_eq n pattern56472381 pattern56473281
    (fun m => exactOccurrenceCount_eq_56472381_56473281 n m) marks

#print axioms exactOccurrenceCount_eq_reverse_archive_34275681_34265781
#print axioms exactOccurrenceCount_eq_reverse_archive_45372681_45362781
#print axioms exactOccurrenceCount_eq_reverse_archive_56472381_56432781
#print axioms exactOccurrenceCount_eq_reverse_archive_45371682_45361782
#print axioms exactOccurrenceCount_eq_reverse_archive_56431782_56471382
#print axioms exactOccurrenceCount_eq_reverse_archive_67541382_67531482
#print axioms exactOccurrenceCount_eq_reverse_archive_34275681_34276581
#print axioms exactOccurrenceCount_eq_reverse_archive_34285671_34286571
#print axioms exactOccurrenceCount_eq_reverse_archive_45376281_45372681
#print axioms exactOccurrenceCount_eq_reverse_archive_56482371_56483271
#print axioms exactOccurrenceCount_eq_reverse_archive_45386271_45382671
#print axioms exactOccurrenceCount_eq_reverse_archive_56472381_56473281

end Implications.WilfArchiveOrientation
