# built-in
import doctest
import re

# external
import pytest

# project
import deal._aliases
from deal._state import state


rex = re.compile(r'deal\.(\w*ContractError)')


class Checker(doctest.OutputChecker):
    def __init__(self):
        self.diff = []

    def check_output(self, want: str, got: str, optionflags: int) -> bool:
        got = rex.sub(r'\1', got)
        ok = super().check_output(want=want, got=got, optionflags=optionflags)
        if not ok:
            self.diff.append((got, want))
        return ok


finder = doctest.DocTestFinder(exclude_empty=True)


@pytest.mark.parametrize('test', finder.find(deal._aliases))
def test_doctest(test):
    state.color = False
    try:
        runner = doctest.DocTestRunner(checker=Checker())
        runner.run(test)
        result = runner.summarize(verbose=False)
        if result.failed:
            print('Kinda diff:')
            print(*runner._checker.diff, sep='\n')
        assert not result.failed
    finally:
        state.color = True
