from .core import Pre, Post, Invariant


__all__ = [
    'require', 'pre',
    'ensure', 'post',
    'inv', 'invariant',
]


require = pre = Pre
ensure = post = Post
inv = invariant = Invariant
