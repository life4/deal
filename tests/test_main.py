import subprocess
import sys


def test_cli_calling():
    result = subprocess.run([sys.executable, '-m', 'deal', 'lint', __file__])
    assert result.returncode == 0
