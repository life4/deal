import subprocess
import sys


def test_cli_calling():
    result = subprocess.run([sys.executable, '-m', 'deal.linter', 'setup.py'])
    assert result.returncode == 0
