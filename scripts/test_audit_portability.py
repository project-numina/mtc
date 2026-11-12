"""Check audit portability under legacy encodings and Windows Git settings."""
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

from check_pivotal_invariants import FILES, ROOT, digest


class AuditPortabilityTests(unittest.TestCase):
    def test_source_checks_without_utf8_mode(self):
        env = dict(os.environ, PYTHONUTF8='0', PYTHONCOERCECLOCALE='0', LC_ALL='C')
        for script in ('check-audit-imports.py', 'check_statement_equivalence.py',
                       'check_pivotal_invariants.py'):
            with self.subTest(script=script):
                result = subprocess.run(
                    [sys.executable, str(ROOT / 'scripts' / script)],
                    env=env, capture_output=True,
                )
                self.assertEqual(result.returncode, 0, result.stderr.decode('utf-8', errors='replace'))

    def test_windows_checkout_preserves_frozen_sources(self):
        scratch = ROOT / 'scratch'
        scratch.mkdir(exist_ok=True)
        with tempfile.TemporaryDirectory(dir=scratch) as temporary:
            source = Path(temporary) / 'source'
            checkout = Path(temporary) / 'checkout'
            source.mkdir()
            checkout.mkdir()
            shutil.copyfile(ROOT / '.gitattributes', source / '.gitattributes')
            for filename in FILES:
                target = source / filename
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(ROOT / filename, target)

            def git(*args):
                subprocess.run(
                    ['git', '-C', str(source), *args], check=True, capture_output=True,
                )

            git('init')
            git('config', 'core.autocrlf', 'true')
            git('add', '.')
            git('checkout-index', '--all', '--prefix=' + checkout.as_posix() + '/')
            for filename, expected in FILES.items():
                with self.subTest(filename=filename):
                    self.assertEqual(digest((checkout / filename).read_bytes()), expected)


if __name__ == '__main__':
    unittest.main()
