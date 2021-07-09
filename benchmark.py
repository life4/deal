from timeit import Timer
from textwrap import dedent


SCALES = (
    (1.0, "s"),
    (1e-3, "ms"),
    (1e-6, "us"),
    (1e-9, "ns"),
)


def format_time(dt, precision=3):
    for scale, unit in SCALES:
        if dt >= scale:
            break
    value = round(dt / scale, precision)
    return f'{value} {unit}'


def format_amount(number: float, k=0) -> str:
    if number < 1000:
        suffix = 'k' * k
        return f'{number:.0f}{suffix}'
    return format_amount(number / 1000, k + 1)


def benchmark(name: str, timer: Timer, repeat=5) -> None:
    print(f'# {name}')
    number, _ = timer.autorange(None)
    if number == 1:
        number, _ = timer.autorange(None)
    raw_timings = timer.repeat(repeat=repeat, number=number)
    timings = [dt / number for dt in raw_timings]
    print('  {loops} loops, best of {repeat}: {best}'.format(
        loops=format_amount(number),
        repeat=repeat,
        best=format_time(min(timings)),
    ))

    best = min(timings)
    worst = max(timings)
    if worst >= best * 4:
        msg = '  WARNING: worst time is more than 4x slower than the best time'
        print(msg)


def timer(code) -> Timer:
    setup, stmt = dedent(code).split('---')
    return Timer(stmt=stmt, setup=setup)


benchmark('import', timer(
    """
    ---
    import deal
    """
))

print('\n# CLASSIC CONTRACTS')
benchmark('decorate', timer(
    """
    import deal
    ---
    @deal.pre(lambda: True)
    def f():
        pass
    """
))
benchmark('call', timer(
    """
    import deal
    @deal.pre(lambda: True)
    def f():
        pass
    ---
    f()
    """
))
benchmark('call with args', timer(
    """
    import deal
    @deal.pre(lambda a, b: True)
    def f(a, b):
        pass
    ---
    f(1, b=2)
    """
))
benchmark('contract error', timer(
    """
    import deal
    @deal.pre(lambda: False)
    def f():
        pass
    ---
    try:
        f()
    except deal.ContractError:
        pass
    else:
        raise Exception
    """
))

print('\n# VAA SIMPLE')
benchmark('decorate', timer(
    """
    import deal
    ---
    @deal.pre(lambda _: True)
    def f():
        pass
    """
))
benchmark('call', timer(
    """
    import deal
    @deal.pre(lambda _: True)
    def f():
        pass
    ---
    f()
    """
))
benchmark('call with args', timer(
    """
    import deal
    @deal.pre(lambda _: True)
    def f(a, b):
        pass
    ---
    f(1, b=2)
    """
))
benchmark('contract error', timer(
    """
    import deal
    @deal.pre(lambda _: False)
    def f():
        pass
    ---
    try:
        f()
    except deal.ContractError:
        pass
    else:
        raise Exception
    """
))
