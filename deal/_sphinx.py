
from typing import List, TYPE_CHECKING
from ._decorators import Raises
from ._introspection import get_contracts

if TYPE_CHECKING:
    from sphinx.application import Sphinx
    from sphinx.ext.autodoc import Options


def autodoc_process(
    app: 'Sphinx',
    what: str,
    name: str,
    obj,
    options: 'Options',
    lines: List[str],
) -> None:
    """
    Process docstrings to add information about contracts.

    https://www.sphinx-doc.org/en/master/usage/extensions/autodoc.html
    https://sphinx-rtd-tutorial.readthedocs.io/en/latest/docstrings.html
    """
    for contract in get_contracts(obj):
        if isinstance(contract, Raises):
            for exc in contract.exceptions:
                lines.append(f':raises {exc}')


def register_sphinx(app: 'Sphinx') -> None:
    app.connect('autodoc-process-docstring', autodoc_process)
