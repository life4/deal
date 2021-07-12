import enum
from typing import List, TYPE_CHECKING
from ._decorators import Raises
from ._introspection import get_contracts

if TYPE_CHECKING:
    from sphinx.application import Sphinx as SphinxApp
    from sphinx.ext.autodoc import Options


class AutoDoc(enum.Enum):
    """
    Process docstrings to add information about contracts.

    https://www.sphinx-doc.org/en/master/usage/extensions/autodoc.html
    https://sphinx-rtd-tutorial.readthedocs.io/en/latest/docstrings.html
    """
    Sphinx = "sphinx"
    Google = "google"
    Numpy = "numpy"

    def register(self, app: 'SphinxApp') -> None:
        if self == AutoDoc.Sphinx:
            app.setup_extension('sphinx.ext.autodoc')
            app.connect('autodoc-process-docstring', _process_sphinx)
            return

        if self == AutoDoc.Google:
            app.setup_extension('sphinx.ext.napoleon')
            # app.add_config_value('napoleon_google_docstring', True, 'env')
            # app.add_config_value('napoleon_numpy_docstring', False, 'env')
            app.connect('autodoc-process-docstring', _process_sphinx)


def _process_sphinx(
    app: 'SphinxApp',
    what: str,
    name: str,
    obj,
    options: 'Options',
    lines: List[str],
) -> None:
    for contract in get_contracts(obj):
        if isinstance(contract, Raises):
            for exc in contract.exceptions:
                lines.append(f':raises {exc.__qualname__}:')
