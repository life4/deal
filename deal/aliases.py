from .core import Pre, Post, Invariant, Raises, Offline


__all__ = [
    'require', 'pre',
    'ensure', 'post',
    'inv', 'invariant',
    'raises', 'offline',
]


require = pre = Pre
ensure = post = Post
inv = invariant = Invariant
raises = Raises
offline = Offline
