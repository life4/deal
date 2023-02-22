from __future__ import annotations
from pathlib import Path

import sys
from importlib import import_module
import multiprocessing


def test_astroid_is_optional(tmp_path: Path) -> None:
    proc = multiprocessing.Process(
        target=_test_astroid_is_optional,
        args=(tmp_path,),
    )
    try:
        proc.start()
    finally:
        proc.join()
    assert proc.exitcode == 0


def _test_astroid_is_optional(tmp_path: Path) -> None:
    # put the patched astroid into PYTHONPATH
    package_path = tmp_path / 'pkg'
    package_path.mkdir()
    module_path = package_path / 'astroid.py'
    module_path.write_text('raise ImportError\n')
    sys.path.insert(0, package_path)

    # remove the real astroid from the cache
    for mod_name in list(sys.modules.keys()):
        if mod_name.startswith('astroid'):
            del sys.modules[mod_name]

    # find all modules that import astroid
    # and re-import them
    for mod_name, module in list(sys.modules.items()):
        if not mod_name.startswith('deal.'):
            continue
        if not hasattr(module, 'astroid'):
            continue
        del sys.modules[mod_name]
        import_module(mod_name)
