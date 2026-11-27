import json
from pathlib import Path
import re
import tempfile
import unittest

from scripts.attack import transcript_matches


class TranscriptSearchTest(unittest.TestCase):
    def test_scopes_and_roles_prevent_returning_other_projects_and_tool_payloads(self):
        records = [
            {"type": "user", "cwd": "/unrelated", "message": {"content": "target"}},
            {"type": "assistant", "cwd": "/checkout/worktrees/attack",
             "message": {"content": [{"type": "text", "text": "target"}]}},
            {"type": "user", "message": {"content": [{"type": "tool_result", "text": "target"}]}},
            {"type": "session_meta", "payload": {"cwd": "/checkout"}},
            {"type": "response_item", "payload": {"type": "function_call_output",
                                                  "output": "target"}},
            {"type": "response_item", "payload": None},
            {"type": "response_item", "payload": {"type": "message", "role": "assistant",
                                                  "content": [{"type": "output_text",
                                                               "text": "target"}]}},
            {"type": "turn_context", "payload": {"cwd": "/unrelated"}},
            {"type": "response_item", "payload": {"type": "message", "role": "user",
                                                  "content": [{"type": "input_text",
                                                               "text": "target"}]}},
        ]
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "transcript.jsonl"
            path.write_text("\n".join(map(json.dumps, records)), encoding="utf-8")
            matches = list(transcript_matches(path, [Path("/checkout")], re.compile("target")))
        self.assertEqual(matches, [(2, "assistant", "target"), (7, "assistant", "target")])


if __name__ == "__main__":
    unittest.main()
