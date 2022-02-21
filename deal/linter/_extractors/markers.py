import ast
from typing import Iterator, Optional

import astroid

from .._contract import Category
from .._stub import StubsManager
from .common import TOKENS, Extractor, Token, get_full_name, get_name, get_stub, infer
from .contracts import get_contracts
from .value import get_value


get_markers = Extractor()
DEFINITELY_RANDOM_FUNCS = frozenset({
    'randint',
    'randbytes',
    'randrange',
    'getrandbits',
    'shuffle',
})
SYSCALLS = frozenset({
    # https://docs.python.org/3/library/os.html#process-management
    'os.abort',
    'os.execv',
    'os.fork',
    'os.forkpty',
    'os.kill',
    'os.killpg',
    'os.plock',
    'os.posix_spawn',
    'os.posix_spawnp',
    'os.putenv',
    'os.startfile',
    'os.system',
    'os.wait',
    'os.wait3',
    'os.wait4',
    'os.waitid',
    'os.waitpid',

    'subprocess.call',
    'subprocess.check_call',
    'subprocess.check_out',
    'subprocess.getoutput',
    'subprocess.getstatusoutput',
    'subprocess.run',
    'subprocess.Popen',
})
SYSCALLS_PREFIXES = ('os.exec', 'os.spawn', 'os.popen')
TIMES = frozenset({
    'os.times',
    'datetime.now',
    'date.today',
    'datetime.datetime.now',
    'datetime.date.today',

    'time.clock_gettime',
    'time.clock_gettime_ns',
    'time.get_clock_info',
    'time.monotonic',
    'time.monotonic_ns',
    'time.perf_counter',
    'time.perf_counter_ns',
    'time.process_time',
    'time.process_time_ns',
    'time.time',
    'time.time_ns',
    'time.thread_time',
    'time.thread_time_ns',
})
NETWORK_FUNCS = frozenset({
    '_socket.socket.connect',
    '_socket.socket.sendall',
    '_socket.socket.recv',
    '_socket.socket.listen',
    '_socket.socket.bind',
    '_socket.socket.getaddrinfo',
    '_socket.socket.close',

    'asyncio.streams.open_connection',
    'asyncio.streams.start_server',
    'asyncio.streams.open_unix_connection',
    'asyncio.streams.start_unix_server',
})


@get_markers.register(*TOKENS.GLOBAL)
def handle_global(expr, **kwargs) -> Optional[Token]:
    return Token(marker='global', line=expr.lineno, col=expr.col_offset)


@get_markers.register(*TOKENS.NONLOCAL)
def handle_nonlocal(expr, **kwargs) -> Optional[Token]:
    return Token(marker='global', line=expr.lineno, col=expr.col_offset)


@get_markers.register(ast.Import)
def handle_ast_import(expr: ast.Import, **kwargs) -> Optional[Token]:
    return Token(marker='import', line=expr.lineno, col=expr.col_offset)


@get_markers.register(astroid.Import)
def handle_astroid_import(expr: astroid.Import, **kwargs) -> Optional[Token]:
    return Token(marker='import', line=expr.lineno, col=expr.col_offset)


@get_markers.register(ast.ImportFrom)
def handle_ast_import_from(expr: ast.ImportFrom, **kwargs) -> Optional[Token]:
    return Token(marker='import', line=expr.lineno, col=expr.col_offset)


@get_markers.register(astroid.ImportFrom)
def handle_astroid_import_from(expr: astroid.ImportFrom, **kwargs) -> Optional[Token]:
    return Token(marker='import', line=expr.lineno, col=expr.col_offset)


@get_markers.register(*TOKENS.CALL)
def handle_call(expr, dive: bool = True, stubs: Optional[StubsManager] = None) -> Iterator[Token]:
    name = get_name(expr.func)
    if name is None:
        return

    # stdout, stderr, stdin
    token = _check_print(expr=expr, name=name)
    if token is not None:
        yield token
        return
    if name.startswith('sys.stdout'):
        yield Token(marker='stdout', value='sys.stdout.')
        return
    if name.startswith('sys.stderr'):
        yield Token(marker='stderr', value='sys.stderr.')
        return
    if name.startswith('sys.stdin'):
        yield Token(marker='stdin', value='sys.stdin.')
        return
    if name == 'input':
        yield Token(marker='stdin', value='input')
        return

    # random, import,
    if name == '__import__':
        yield Token(marker='import')
        return
    if _is_random(expr=expr, name=name):
        yield Token(marker='random', value=name)
        return
    if _is_syscall(expr=expr, name=name):
        yield Token(marker='syscall', value=name)
        return
    if _is_time(expr=expr, name=name):
        yield Token(marker='time', value=name)
        return

    # read and write
    if name == 'open':
        if _is_open_to_write(expr):
            yield Token(marker='write', value='open')
        else:
            yield Token(marker='read', value='open')
        return
    if _is_pathlib_write(expr):
        yield Token(marker='write', value='Path.open')
        return

    yield from _infer_markers(expr=expr, dive=dive, stubs=stubs)


def _infer_markers(expr, dive: bool, stubs: Optional[StubsManager] = None) -> Iterator[Token]:
    inferred = infer(expr=expr.func)
    stubs_found = False
    if type(expr) is astroid.Call and stubs is not None:
        for token in _markers_from_stubs(expr=expr, inferred=inferred, stubs=stubs):
            stubs_found = True
            yield token

    if not stubs_found:
        for token in _markers_from_inferred(expr=expr, inferred=inferred):
            dive = False
            yield token
        if dive:
            yield from _markers_from_func(expr=expr, inferred=inferred)


def _markers_from_inferred(expr: astroid.NodeNG, inferred: tuple) -> Iterator[Token]:
    for node in inferred:
        module, full_name = get_full_name(node)
        qual_name = f'{module}.{full_name}'
        if qual_name in NETWORK_FUNCS:
            yield Token(
                marker='network',
                value=full_name,
                line=expr.lineno,
                col=expr.col_offset,
            )
            return
        if isinstance(node, astroid.BoundMethod):
            if node.bound.pytype() == 'random.Random':
                yield Token(
                    marker='random',
                    value=full_name,
                    line=expr.lineno,
                    col=expr.col_offset,
                )
                return


def _is_open_to_write(expr) -> bool:
    for arg in expr.args:
        if isinstance(arg, astroid.Const) and arg.value == 'w':
            return True
        if isinstance(arg, ast.Str) and 'w' in arg.s:
            return True

    if not expr.keywords:
        return False
    for arg in expr.keywords:
        if arg.arg != 'mode':
            continue
        if isinstance(arg.value, astroid.Const) and 'w' in arg.value.value:
            return True
        if isinstance(arg.value, ast.Str) and 'w' in arg.value.s:
            return True
    return False


def _is_pathlib_write(expr) -> bool:
    if not isinstance(expr, astroid.Call):
        return False
    if not isinstance(expr.func, astroid.Attribute):
        return False
    if expr.func.attrname not in ('write_text', 'write_bytes', 'open'):
        return False

    # if it's open, check that mode is "w"
    if expr.func.attrname == 'open':
        if not _is_open_to_write(expr):
            return False

    for value in infer(expr.func.expr):
        if isinstance(value, astroid.Instance):
            if value.pytype().startswith('pathlib.'):
                return True
    return False


def _markers_from_stubs(expr: astroid.Call, inferred, stubs: StubsManager) -> Iterator[Token]:
    for value in inferred:
        if type(value) is not astroid.FunctionDef:
            continue
        module_name, func_name = get_full_name(expr=value)
        stub = get_stub(module_name=module_name, expr=value, stubs=stubs)
        if stub is None:
            continue
        names = stub.get(func=func_name, contract=Category.HAS)
        for name in names:
            yield Token(marker=name, line=expr.lineno, col=expr.col_offset)


def _markers_from_func(expr: astroid.NodeNG, inferred: tuple) -> Iterator[Token]:
    for value in inferred:
        if not isinstance(value, (astroid.FunctionDef, astroid.UnboundMethod)):
            continue

        # recursively infer markers from the function body
        for token in get_markers(body=value.body, dive=False):
            yield Token(
                marker=token.marker,
                value=token.value,
                line=expr.lineno,
                col=expr.col_offset,
            )

        # get explicitly specified markers from `@deal.has`
        for contract in get_contracts(value):
            if contract.name != 'has':
                continue
            for arg in contract.args:
                value = get_value(arg)
                if type(value) is not str:
                    continue
                yield Token(marker=value, line=expr.lineno, col=expr.col_offset)
    return None


def _check_print(expr, name: str) -> Optional[Token]:
    """Return token if expr is `print` function call.

    Marker type depends on `file=` keyword argument.
    If it is missed, the type is `stdout`.
    If it is `stdout` or `stderr`, the type is `stdout` or `stderr`.
    Otherwise, there is no marker. It writes something into a stream, and it's ok.
    """
    if name != 'print':
        return None
    for kwarg in (expr.keywords or []):
        if kwarg.arg != 'file':
            continue
        value = get_name(expr=kwarg.value)
        if value in ('stdout', 'sys.stdout'):
            return Token(
                marker='stdout',
                value='print',
                line=expr.lineno,
                col=expr.col_offset,
            )
        if value in ('stderr', 'sys.stderr'):
            return Token(
                marker='stderr',
                value='print',
                line=expr.lineno,
                col=expr.col_offset,
            )
        return None
    return Token(
        marker='stdout',
        value='print',
        line=expr.lineno,
        col=expr.col_offset,
    )


def _is_random(expr, name: str) -> bool:
    if name.startswith('random.'):
        return True
    if '.' in name:
        return False
    if name in DEFINITELY_RANDOM_FUNCS:
        return True
    return False


def _is_syscall(expr, name: str) -> bool:
    if name in SYSCALLS:
        return True
    if name.startswith(SYSCALLS_PREFIXES):
        return True
    return False


def _is_time(expr, name: str) -> bool:
    if name in TIMES:
        return True
    if f'time.{name}' in TIMES:
        return True
    return False
