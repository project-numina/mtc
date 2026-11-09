"""Exercise the frozen statement source normalization."""
import unittest

from check_statement_equivalence import normalize


class NormalizeTests(unittest.TestCase):
    def test_nested_comments_are_ignored(self):
        self.assertEqual(normalize('def x /- a /- b -/ c -/ : Nat := 1 -- note\n'),
                         normalize('def x : Nat := 1'))

    def test_strings_are_not_discarded(self):
        self.assertNotEqual(normalize('def x := "first"'), normalize('def x := "second"'))

    def test_unterminated_comment_is_rejected(self):
        with self.assertRaises(ValueError):
            normalize('def x := 1 /- unfinished')


if __name__ == '__main__':
    unittest.main()
