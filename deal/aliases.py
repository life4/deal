from .core import Pre, Post, Invariant, Raises, Offline


__all__ = [
    'require', 'pre',
    'ensure', 'post',
    'inv', 'invariant',
    'raises', 'safe',
    'offline',
]


require = pre = Pre
ensure = post = Post
inv = invariant = Invariant
raises = Raises


def offline(_func=None, message=None, exception=None, debug=False):
    if _func is not None:
        return Offline()(_func)
    return Offline(message=message, exception=exception, debug=debug)


def safe(_func=None, message=None, exception=None, debug=False):
    if _func is not None:
        return Raises()(_func)
    return Raises(message=message, exception=exception, debug=debug)
