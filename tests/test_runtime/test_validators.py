import pytest

from deal._runtime._validators import _args_to_vars, _get_signature


@pytest.mark.parametrize('args, kwargs, f, expected', [
    # args
    (
        [1], dict(),
        lambda x: 0,
        dict(x=1),
    ),
    # kwargs
    (
        [], dict(x=2),
        lambda x: 0,
        dict(x=2),
    ),
    # args and kwargs
    (
        [1, 2], dict(c=3, d=4),
        lambda a, b, c, d: 0,
        dict(a=1, b=2, c=3, d=4),
    ),
    # *args
    (
        [1, 2], dict(),
        lambda *other: 0,
        dict(other=(1, 2)),
    ),
    # **kwargs
    (
        [], dict(a=1, b=2),
        lambda **other: 0,
        dict(a=1, b=2, other=dict(a=1, b=2)),
    ),
])
def test_args_to_vars(args, kwargs, f, expected):
    sig = _get_signature(f)
    actual = _args_to_vars(args=args, kwargs=kwargs, signature=sig)
    assert actual == expected
