# built-in
import typing


if typing.TYPE_CHECKING:
    # app
    from ._proxy import ProxySort


ProxyType = typing.Type['ProxySort']
P = typing.TypeVar('P', bound=ProxyType)


class Registry:
    _proxies: typing.Dict[str, ProxyType]

    def __init__(self) -> None:
        self._proxies = dict()

    def __getitem__(self, name: str) -> ProxyType:
        return self._proxies[name]

    def add(self, cls: P) -> P:
        self._proxies[cls.type_name] = cls
        return cls


registry = Registry()
