"""Controls for the immutable pre-field source comparison."""

from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import check_bpf_pre_copies as check


class BpfPreCopiesTest(unittest.TestCase):
    def fixture(self):
        sources = {path: "" for _, path in check.COPIES}
        pre = []
        for name, path in check.COPIES:
            body = "Definition " + name + " (inp : ProcInput) : Prop := P inp"
            sources[path] += body + " /\\ in_selfkill_terminal inp = false.\n"
            pre.append(check.rename(body + ".", name + "_pre"))
        inherited = "Definition valid_input_inherited (inp : ProcInput) : Prop := Q inp."
        sources[check.RUN] += inherited
        socket = "Definition setsockopt_spec (fd level optlen : word) : Sys SyscallEffect := old_body fd."
        sources[check.SOCKET] = socket
        return (
            sources,
            "\n".join(pre),
            check.rename(inherited, "valid_input_inherited_pre24"),
            check.rename(socket, "setsockopt_no_cgroup_bpf_spec"),
        )

    def test_exact_sources_pass(self):
        self.assertEqual(check.compare(*self.fixture()), [])

    def test_changed_pre23_body_is_rejected(self):
        sources, pre, inherited, socket = self.fixture()
        pre = pre.replace("P inp", "R inp", 1)
        self.assertEqual(len(check.compare(sources, pre, inherited, socket)), 1)

    def test_changed_inherited_predicate_is_rejected(self):
        sources, pre, inherited, socket = self.fixture()
        errors = check.compare(sources, pre, inherited.replace("Q inp", "R inp"), socket)
        self.assertEqual(len(errors), 1)
        self.assertIn("valid_input_inherited_pre24", errors[0])

    def test_changed_option_body_is_rejected(self):
        sources, pre, inherited, socket = self.fixture()
        errors = check.compare(sources, pre, inherited, socket.replace("old_body", "wrong_body"))
        self.assertEqual(len(errors), 1)
        self.assertIn("setsockopt_no_cgroup_bpf_spec", errors[0])

    def test_missing_source_is_rejected(self):
        sources, pre, inherited, socket = self.fixture()
        sources[check.SOCKET] = ""
        self.assertEqual(len(check.compare(sources, pre, inherited, socket)), 1)


if __name__ == "__main__":
    unittest.main()
