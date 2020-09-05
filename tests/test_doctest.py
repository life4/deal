import doctest

import pytest

import deal._aliases


class Checker(doctest.OutputChecker):
    def check_output(self, want: str, got: str, optionflags: int) -> bool:
        got = got.replace('deal._exceptions.', '')
        return super().check_output(want=want, got=got, optionflags=optionflags)


finder = doctest.DocTestFinder(exclude_empty=True)


@pytest.mark.parametrize('test', finder.find(deal._aliases))
def test_doctest(test):
    runner = doctest.DocTestRunner(checker=Checker())
    runner.run(test)
    failed, _total = runner.summarize()
    assert not failed
