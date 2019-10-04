import unittest
from typing import NoReturn

import marshmallow
import urllib3
import vaa

import deal
import pytest


class TestPreDeal:
    @pytest.mark.parametrize('correct,incorrect', [(1, -1), (2, -2), (3, -3), (5, -5), (7, -7), (11, -11)])
    def test_pre_contract_fulfilled(self, correct, incorrect):
        func = deal.pre(lambda x: x > 0)(lambda x: x)
        assert func(correct) == correct
        with pytest.raises(deal.PreContractError):
            func(incorrect)

    @pytest.mark.parametrize('correct,incorrect_min,incorrect_max',
                             [(1, -1, 20), (2, -2, 21), (3, -3, 22), (5, -5, 23), (7, -7, 24), (9, -11, 25)])
    def test_chain_all_contracts_fulfilled(self, correct, incorrect_min, incorrect_max):
        func = deal.pre(lambda x: x < 10)(lambda x: x)
        func = deal.pre(lambda x: x > 0)(func)
        assert func(correct) == correct
        with pytest.raises(deal.PreContractError):
            func(incorrect_min)
        with pytest.raises(deal.PreContractError):
            func(incorrect_max)

    def test_correct_exceptions_raised_on_contract_fail(self):
        func = deal.pre(lambda x: x > 0)(lambda x: x)
        with pytest.raises(deal.PreContractError):
            func(-2)

        func = deal.pre(lambda x: x > 0, message='TEST')(lambda x: x)
        try:
            func(-2)
        except AssertionError as e:
            assert e.args[0] == 'TEST'

        func = deal.pre(lambda x: x > 0, exception=NameError)(lambda x: x)
        with pytest.raises(NameError):
            func(-2)

        func = deal.pre(lambda x: x > 0, exception=NameError('TEST'))(lambda x: x)
        with pytest.raises(NameError):
            func(-2)
        try:
            func(-2)
        except NameError as e:
            assert e.args[0] == 'TEST'

        func = deal.pre(lambda x: x > 0, message='TEST', exception=NameError)(lambda x: x)
        with pytest.raises(NameError):
            func(-2)
        try:
            func(-2)
        except NameError as e:
            assert e.args[0] == 'TEST'

    def test_raise_error_with_param_on_contract_failure(self):
        func = deal.pre(lambda x: x > 0 or 'TEST')(lambda x: x)
        assert func(4) == 4

        with pytest.raises(deal.PreContractError):
            func(-2)

        try:
            func(-2)
        except deal.PreContractError as e:
            assert e.args[0] == 'TEST'

    def test_method_decoration_name_is_correct(self):
        @deal.pre(lambda x: x > 0)
        def some_function(x):
            return x

        assert some_function.__name__ == 'some_function'

    def test_class_method_decorator_raises_error_on_contract_fail(self):
        class Class:
            y = 7

            @deal.pre(lambda self, x: x > 0)
            def method(self, x):
                return x * 2

            @deal.pre(lambda self, x: x > 0)
            def method2(self, y):
                return self.y

        assert Class().method(2) == 4
        assert Class().method2(2) == 7
        with pytest.raises(deal.PreContractError):
            Class().method(-2)
        with pytest.raises(deal.PreContractError):
            Class().method2(-2)

    # ignored test
    def _test_validator(self, validator):
        func = deal.pre(validator)(lambda x: x)
        assert func(4) == 4

        with pytest.raises(deal.PreContractError):
            func(-2)

        try:
            func(-2)
        except deal.PreContractError as e:
            assert e.args[0] == 'TEST'


class TestPostDeal:
    def test_return_value_fulfils_contract(self):
        func = deal.post(lambda x: x > 0)(lambda x: -x)
        assert func(-4) == 4

        with pytest.raises(deal.PostContractError):
            func(4)


class TestInvDeal:
    def test_setting_object_attribute_fulfills_contract(self):
        @deal.inv(lambda obj: obj.x > 0)
        class A:
            x = 2

        a = A()
        a.x = 4
        with pytest.raises(deal.InvContractError):
            a.x = -2

    def test_setting_wrong_args_by_method_raises_error(self):
        @deal.inv(lambda obj: obj.x > 0)
        class A:
            x = 2

            def f(self, x):
                self.x = x

        a = A()

        a.f(4)
        with pytest.raises(deal.InvContractError):
            a.f(-2)

    def test_chain_contracts_both_fulfill(self):
        @deal.inv(lambda obj: obj.x > 0)
        @deal.inv(lambda obj: obj.x < 10)
        class A:
            x = 2

        a = A()
        a.x = 4
        with pytest.raises(deal.InvContractError):
            a.x = -2
        with pytest.raises(deal.InvContractError):
            a.x = 20

    def test_patched_invariants_instance(self):
        class A:
            x = 2

        PatchedA = deal.inv(lambda obj: obj.x > 0)(A)  # noQA
        a = PatchedA()
        assert isinstance(a, PatchedA)
        assert isinstance(a, A)

        PatchedA2 = deal.inv(lambda obj: obj.x > 0)(PatchedA)  # noQA
        a = PatchedA2()
        assert isinstance(a, PatchedA)
        assert isinstance(a, PatchedA2)
        assert isinstance(a, A)

        assert a.__class__.__name__.count('Invarianted') == 1


class MarshmallowSchemeTests(unittest.TestCase):
    def setUp(self):
        class _Scheme(marshmallow.Schema):
            name = marshmallow.fields.Str()

        self.Scheme = vaa.marshmallow(_Scheme)

    def test_scheme_string_validation_args_correct(self):
        @deal.pre(self.Scheme)
        def func(name):
            return name * 2

        assert func('Chris') == 'ChrisChris'

        with pytest.raises(deal.PreContractError):
            func(123)

        try:
            func(123)
        except deal.PreContractError as e:
            assert e.args[0] == {'name': ['Not a valid string.']}

    def test_method_chain_decorator_with_scheme_is_fulfilled(self):
        @deal.pre(self.Scheme)
        @deal.pre(lambda name: name != 'Oleg')
        def func(name):
            return name * 2

        assert func('Chris') == 'ChrisChris'

        with pytest.raises(deal.PreContractError):
            func(123)

        with pytest.raises(deal.PreContractError):
            func('Oleg')

    def test_scheme_contract_is_satisfied_when_setting_arg(self):
        @deal.inv(self.Scheme)
        class User:
            name = ''

        user = User()

        user.name = 'Chris'

        with pytest.raises(deal.InvContractError):
            user.name = 123

        try:
            user.name = 123
        except deal.InvContractError as e:
            assert e.args[0] == {'name': ['Not a valid string.']}

    def test_scheme_contract_is_satisfied_within_chain(self):
        @deal.inv(lambda user: user.name != 'Oleg')
        @deal.inv(self.Scheme)
        @deal.inv(lambda user: user.name != 'Chris')
        class User:
            name = ''

        user = User()
        user.name = 'Gram'

        user = User()
        with pytest.raises(deal.InvContractError):
            user.name = 'Oleg'

        user = User()
        with pytest.raises(deal.InvContractError):
            user.name = 123

        user = User()
        with pytest.raises(deal.InvContractError):
            user.name = 'Chris'

    def test_scheme_contract_is_satisfied_when_passing_args(self):
        @deal.pre(self.Scheme)
        def func(name):
            return name * 2

        assert func('Chris') == 'ChrisChris'

        assert func(name='Chris') == 'ChrisChris'

        @deal.pre(self.Scheme)
        def func(**kwargs):
            return kwargs['name'] * 3

        assert func(name='Chris') == 'ChrisChrisChris'

        @deal.pre(self.Scheme)
        def func(name='Max'):
            return name * 2

        assert func() == 'MaxMax'


class TestDefaultScheme(MarshmallowSchemeTests):
    def setUp(self):
        class MyScheme(deal.Scheme):
            def is_valid(self):
                if not isinstance(self.data['name'], str):
                    self.errors = {'name': ['Not a valid string.']}
                    return False
                return True

        self.Scheme = MyScheme


class TestRaises:
    def test_raises_expects_function_to_raise_error(self):
        func = deal.raises(ZeroDivisionError)(lambda x: 1 / x)
        with pytest.raises(ZeroDivisionError):
            func(0)
        func(2)

        func = deal.raises(KeyError)(lambda x: 1 / x)
        with pytest.raises(deal.RaisesContractError):
            func(0)

    def test_raises_doesnt_override_another_constract(self):
        @deal.raises(ZeroDivisionError)
        @deal.offline
        def func(do, number):
            if do:
                http = urllib3.PoolManager()
                http.request('GET', 'http://httpbin.org/robots.txt')
            1 / number

        func(False, 1)
        with pytest.raises(deal.OfflineContractError):
            func(True, 1)
        with pytest.raises(ZeroDivisionError):
            func(False, 0)


class TestOffline:
    def test_network_request_in_offline_raises_exception(self):

        @deal.offline
        def func(do):
            if do:
                http = urllib3.PoolManager()
                http.request('GET', 'http://httpbin.org/robots.txt')

        func(False)
        with pytest.raises(deal.OfflineContractError):
            func(True)

    def test_network_request_in_offline_and_raises_specified_exception(self):

        @deal.offline(exception=KeyError)
        def func(do):
            if do:
                http = urllib3.PoolManager()
                http.request('GET', 'http://httpbin.org/robots.txt')

        func(False)
        with pytest.raises(KeyError):
            func(True)


class TestSilent:
    def test_silent_contract_not_allow_print(self):
        @deal.silent
        def func(msg):
            if msg:
                print(msg)

        func(None)
        with pytest.raises(deal.SilentContractError):
            func('bad')


class TestChain:
    def test_chained_contract_decorator(self):

        @deal.chain(deal.silent, deal.offline)
        def func(msg, do):
            if msg:
                print(msg)
            if do:
                http = urllib3.PoolManager()
                http.request('GET', 'http://httpbin.org/robots.txt')

        func(False, False)
        with pytest.raises(deal.SilentContractError):
            func(True, False)
        with pytest.raises(deal.OfflineContractError):
            func(False, True)


class TestState:
    def setUp(self):
        deal.reset()

    def tearDown(self):
        deal.reset()

    def test_contract_state_switch_custom_param(self):
        func = deal.pre(lambda x: x > 0, debug=True)(lambda x: x * 2)
        deal.switch(debug=False)
        func(-2)
        deal.switch(debug=True)
        with pytest.raises(deal.PreContractError):
            func(-2)

    def test_contract_state_switch_default_param(self):
        func = deal.pre(lambda x: x > 0)(lambda x: x * 2)
        deal.switch(main=False)
        func(-2)
        deal.switch(main=True)
        with pytest.raises(deal.PreContractError):
            func(-2)


class TestEnsure:
    def test_parameters_and_result_fulfill_constact(self):
        @deal.ensure(lambda a, b, result: a > 0 and b > 0 and result != 'same number')
        def func(a, b):
            if a == b:
                return 'same number'
            else:
                return 'different numbers'

        assert func(1, 2) == 'different numbers'
        with pytest.raises(deal.PostContractError):
            func(0, 1)
        with pytest.raises(deal.PostContractError):
            func(1, 0)
        with pytest.raises(deal.PostContractError):
            func(1, 1)


class CaseTest(unittest.TestCase):
    def setUp(self):
        @deal.raises(ZeroDivisionError)
        @deal.pre(lambda a, b: a > 0 and b > 0)
        def div(a: int, b: int) -> float:
            assert isinstance(a, int)
            assert isinstance(b, int)
            assert a > 0
            assert b > 0
            return a / b

        self.func = div

    def test_count(self):
        for count in (1, 10, 20, 50):
            cases = deal.cases(self.func, count=count)
            assert len(list(cases)) == count

    def test_params_detected(self):
        for case in deal.cases(self.func, count=10):
            assert set(case.kwargs) == {'a', 'b'}

    def test_params_type(self):
        for case in deal.cases(self.func, count=10):
            assert type(case.kwargs['a']) is int
            assert type(case.kwargs['b']) is int

    def test_params_ok_with_excs(self):
        results = []
        for case in deal.cases(self.func, count=20):
            result = case()
            results.append(result)
        assert any(r is not NoReturn for r in results), 'exception occured on every run'
        assert any(r is NoReturn for r in results), 'no exception occured'

    def test_return_type_checks(self):
        def div(a: int, b: int):
            return 1

        for case in deal.cases(div, count=20):
            case()

        def div(a: int, b: int) -> str:
            return 1

        with pytest.raises(TypeError):
            case = next(iter(deal.cases(div, count=20)))
            case()

    def test_explicit_kwargs(self):
        def div(a: int, b: int):
            assert b == 4

        for case in deal.cases(div, kwargs=dict(b=4), count=20):
            case()


if __name__ == '__main__':
    pytest.main(['tests.py'])
