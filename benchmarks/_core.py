from timeit import Timer
from typing import List


SCALES = (
    (1.0, 's'),
    (1e-3, 'ms'),
    (1e-6, 'us'),
    (1e-9, 'ns'),
)
TICKS = '▁▂▃▄▅▆▇█'
CHUNKS = 6
PRECISION = 3
REPEAT = 5


def format_time(dt):
    for scale, unit in SCALES:
        if dt >= scale:
            break
    value = round(dt / scale, PRECISION)
    return f'{value} {unit}'


def format_amount(number: float, k=0) -> str:
    if number < 1000:
        suffix = 'k' * k
        return f'{number:.0f}{suffix}'
    return format_amount(number / 1000, k + 1)


def run_test(*, name: str, test: str, setup: str = '') -> None:
    print(f'  {name}')
    timer = Timer(stmt=test, setup=setup)
    number, _ = timer.autorange(None)
    if number == 1:
        number, _ = timer.autorange(None)
    raw_timings = timer.repeat(repeat=REPEAT, number=number)
    timings = [dt / number for dt in raw_timings]
    print('    {loops} loops, best of {repeat}: {best} {hist}'.format(
        loops=format_amount(number),
        repeat=REPEAT,
        best=format_time(min(timings)),
        hist=make_histogram(timings),
    ))


def make_histogram(timings: List[float]) -> str:
    """Generate ASCII histogram for the given time points
    """
    best = min(timings)
    worst = max(timings)
    diff = worst - best

    if diff == 0:
        return TICKS[-1] * CHUNKS

    histogram = []
    for time in timings:
        ratio = (time - best) / diff
        index = int(round(ratio * CHUNKS))
        histogram.append(TICKS[index])
    return ''.join(histogram)
