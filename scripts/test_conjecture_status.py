"""Exercise metadata validation and dashboard output on isolated files."""
from pathlib import Path
from tempfile import TemporaryDirectory
import unittest
from unittest.mock import patch

import conjecture_status as status


class StatusTests(unittest.TestCase):
    def setUp(self):
        self.temp = TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.path = self.root / 'Conjectures' / 'Example' / 'Test.lean'
        self.path.parent.mkdir(parents=True)
        self.fixture = ('/-!\nStatus: open\nSource: reference | detail\n'
                        'Declaration: MTC.Conjectures.Example.test\n-/\n')
        self.path.write_text(self.fixture)
        self.patch = patch.object(status, 'ROOT', self.root)
        self.patch.start()
        self.addCleanup(self.patch.stop)

    def test_dashboard_and_link(self):
        result = status.render(status.entries())
        self.assertIn('../Conjectures/Example/Test.lean', result)
        self.assertIn('reference \\| detail', result)

    def test_blank_source_cannot_consume_next_field(self):
        self.path.write_text(self.fixture.replace('Source: reference | detail', 'Source:'))
        with self.assertRaises(ValueError):
            status.entries()

    def test_duplicate_fields_are_rejected(self):
        self.path.write_text(self.fixture.replace('Status: open', 'Status: open\nStatus: proved'))
        with self.assertRaises(ValueError):
            status.entries()

    def test_bad_status_and_namespace_are_rejected(self):
        for text in (self.fixture.replace('Status: open', 'Status: maybe'),
                     self.fixture.replace('MTC.Conjectures.Example.test', 'MTC.Other.test')):
            self.path.write_text(text)
            with self.assertRaises(ValueError):
                status.entries()


if __name__ == '__main__':
    unittest.main()
