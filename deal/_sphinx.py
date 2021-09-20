from typing import Dict, List, TYPE_CHECKING
from ._decorators import Raises, Reason, Pre, Post, Ensure
from ._introspection import get_contracts
from ._source import get_validator_source

if TYPE_CHECKING:
    from sphinx.application import Sphinx as SphinxApp
    from sphinx.ext.autodoc import Options


def autodoc(app: 'SphinxApp') -> None:
    """
    Process docstrings to add information about deal contracts.

    https://www.sphinx-doc.org/en/master/usage/extensions/autodoc.html
    https://sphinx-rtd-tutorial.readthedocs.io/en/latest/docstrings.html
    """
    assert 'sphinx.ext.autodoc' in app.extensions
    app.connect('autodoc-process-docstring', _process_docstring)


def _process_docstring(
    app: 'SphinxApp',
    what: str,
    name: str,
    obj,
    options: 'Options',
    lines: List[str],
) -> None:
    raises: Dict[str, str] = dict()
    contracts = []
    for contract in get_contracts(obj):
        if isinstance(contract, Raises):
            for exc in contract.exceptions:
                raises.setdefault(exc.__qualname__, '')
        if isinstance(contract, Reason):
            if contract.message:
                message = contract.message
            else:
                source = get_validator_source(contract._make_validator())
                message = f'``{source}``'
            raises[contract.event.__qualname__] = message
        if isinstance(contract, (Pre, Post, Ensure)):
            if contract.message:
                message = contract.message
            else:
                source = get_validator_source(contract._make_validator())
                message = f'``{source}``'
            contracts.append(f'  * {message}')
    for exc_name, descr in sorted(raises.items()):
        lines.append(f':raises {exc_name}: {descr}')
    if contracts:
        lines.append(':contracts:')
        lines.extend(contracts)
