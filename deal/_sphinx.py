import enum
from typing import List, TYPE_CHECKING
from ._decorators import Raises
from ._introspection import get_contracts

if TYPE_CHECKING:
    from sphinx.application import Sphinx as SphinxApp
    from sphinx.ext.autodoc import Options


class AutoDoc(enum.Enum):
    Sphinx = "sphinx"
    Google = "google"
    Numpy = "numpy"

    def register(self, app: 'SphinxApp') -> None:
        if 'sphinx.ext.autodoc' not in app.extensions:
            from sphinx.ext.autodoc import setup as setup_autodoc
            setup_autodoc(app)
        app.connect('autodoc-process-docstring', autodoc_process)


def autodoc_process(
    app: 'SphinxApp',
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
