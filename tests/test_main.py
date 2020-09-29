# built-in
import subprocess
import sys


def test_cli_calling():
    result = subprocess.run([sys.executable, '-m', 'deal', 'lint', __file__])
    assert result.returncode == 0


def test_do_not_import_linter():
    """When deal is imported, it must not trigger importing linter.
    """
    old_modules = sys.modules.copy()
    for name in list(sys.modules):
        if name == 'deal' or name.startswith('deal.'):
            del sys.modules[name]
        if name == 'astroid' or name.startswith('astroid.'):
            del sys.modules[name]

    import deal  # noqa: F401

    for name in list(sys.modules):
        if name.startswith('deal.lint'):
            raise ImportError('oh no, linter was imported')
        if name == 'astroid' or name.startswith('astroid.'):
            raise ImportError('oh no, astroid was imported')

    sys.modules = old_modules
