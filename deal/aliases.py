from .core import Pre, Post, Invariant, Raises


__all__ = [
    'require', 'pre',
    'ensure', 'post',
    'inv', 'invariant',
    'raises',
]


require = pre = Pre
ensure = post = Post
inv = invariant = Invariant
raises = Raises
