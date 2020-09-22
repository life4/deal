from pathlib import Path
from typing import Iterator

try:
    import pygments
except ImportError:
    pygments = None
else:
    from pygments.formatters import TerminalFormatter
    from pygments.lexers import PythonLexer


def highlight(source: str) -> str:
    if pygments is None:
        return source
    source = pygments.highlight(
        code=source,
        lexer=PythonLexer(),
        formatter=TerminalFormatter(),
    )
    return source.strip()


def get_paths(path: Path) -> Iterator[Path]:
    """Recursively yields python files.
    """
    if not path.exists():
        raise FileNotFoundError(str(path))
    if path.is_file():
        if path.suffix == '.py':
            yield path
        return
    for subpath in path.iterdir():
        if subpath.name[0] == '.':
            continue
        if subpath.name == '__pycache__':
            continue
        yield from get_paths(subpath)
