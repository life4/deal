# external
import z3

# app
from .._context import Context
from .._exceptions import UnsupportedError
from .._proxies import FloatSort, IntSort, ProxySort, random_name, wrap
from ._registry import register


@register('random.Random.randint')
def random_randint(a, b, ctx: Context, **kwargs):
    result = wrap(z3.Int(random_name('randint')))
    ctx.given.add(result >= a)
    ctx.given.add(result <= b)
    return result


@register('random.Random.randrange')
def random_randrange(start, stop, ctx: Context, **kwargs):
    result = wrap(z3.Int(random_name('randrange')))
    ctx.given.add(result >= start)
    ctx.given.add(result < stop)
    return result


@register('random.Random.choice')
def random_choice(seq, ctx: Context, **kwargs):
    zero = IntSort.val(0)
    one = IntSort.val(1)
    if not isinstance(seq, ProxySort):
        raise UnsupportedError("bad argument type for random.choice")
    index = random_randint(
        a=zero,
        b=seq.length - one,
        ctx=ctx,
    )
    return seq.get_item(index)


@register('random.Random.random')
def random_random(ctx: Context, **kwargs):
    zero = FloatSort.val(0)
    one = FloatSort.val(1)
    result = wrap(z3.Const(
        name=random_name('random'),
        sort=FloatSort.sort(),
    ))
    ctx.given.add(result >= zero)
    ctx.given.add(result <= one)
    return result
