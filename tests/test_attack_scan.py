import unittest

from scripts.attack_scan import evidence_score, lemma_record, proposition, rows
from scripts.attack_tools import link_targets, overlaps


class AttackScanTest(unittest.TestCase):
    def test_proposition_keeps_parameter_scope(self):
        self.assertEqual(proposition("theorem target : ∀ x, P x"), "∀ x, P x")
        statement = "theorem target (x : Nat) : P x"
        self.assertEqual(proposition(statement), statement)

    def test_same_printed_proposition_precedes_symbol_overlap(self):
        goal = "∀ G, G.IsClique s"
        exact = lemma_record(goal, {"signature": "theorem bridge : ∀ G,  G.IsClique s"})
        near = lemma_record(goal, {"signature": "∀ G, G.IsClique t"})
        self.assertGreater(evidence_score(exact), evidence_score(near))

    def test_rows_accepts_structured_and_text_mcp_results(self):
        self.assertEqual(rows({"structuredContent": {"result": [{"name": "A"}]}}),
                         [{"name": "A"}])
        self.assertEqual(rows({"content": [{"type": "text", "text": '{"name":"B"}'}]}),
                         [{"name": "B"}])

    def test_paths_match_related_lean_ids_on_dot_boundaries(self):
        prs = [{"number": 1, "files": [{"path": "proofs/P.R1.H1.lean"}]},
               {"number": 2, "files": [{"path": "proofs/P2.R1.H1.lean"}]},
               {"number": 3, "files": [{"path": "docs/P.lean"}]}]
        self.assertEqual([pr["number"] for pr in overlaps("P", prs)], [1])
        self.assertEqual([pr["number"] for pr in overlaps("P.R1.H1.R1", prs)], [1])

    def test_link_suggestions_require_distinct_targets_and_evidence(self):
        hit = {"name": "bridge", "shared_symbols": ["G.IsClique"],
               "same_printed_proposition": False}
        weak = {**hit, "name": "generic", "shared_symbols": []}
        results = link_targets([
            {"id": "A", "proposed_bridges": [hit, hit, weak]},
            {"id": "B", "proposed_bridges": [hit, weak]},
        ])
        self.assertEqual([row["lemma"] for row in results], ["bridge"])
        self.assertEqual(set(results[0]["targets"]), {"A", "B"})


if __name__ == "__main__":
    unittest.main()
