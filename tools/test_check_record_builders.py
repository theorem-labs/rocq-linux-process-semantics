"""Regression cases for positional constructor detection."""
import unittest

from check_record_builders import CONSTRUCTORS, PATTERN


class ConstructorPatternTests(unittest.TestCase):
    constructor = CONSTRUCTORS[0]

    def test_application_at_list_start(self):
        self.assertEqual(PATTERN.findall(f"[{self.constructor} 0]"), [self.constructor])

    def test_coqdoc_reference_is_not_application(self):
        self.assertEqual(PATTERN.findall(f"[{self.constructor}]"), [])

    def test_qualified_or_longer_name_is_not_application(self):
        self.assertEqual(PATTERN.findall(f"Other.{self.constructor} {self.constructor}_extra"), [])


if __name__ == "__main__":
    unittest.main()
