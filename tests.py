import unittest

import marshmallow
import urllib3
import vaa

import deal
import pytest


class PreTest(unittest.TestCase):

    def test_main(self):
        func = deal.pre(lambda x: x > 0)(lambda x: x)
        assert func(4) == 4
        with pytest.raises(deal.PreContractError):
            func(-1)

    def test_chain(self):
        func = deal.pre(lambda x: x < 10)(lambda x: x)
        func = deal.pre(lambda x: x > 0)(func)
        assert func(4) == 4
        with pytest.raises(deal.PreContractError):
            func(-2)
        with pytest.raises(deal.PreContractError):
            func(20)

    def test_init(self):
        deal.pre(lambda x: x > 0)

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

    def _test_validator(self, validator):
        func = deal.pre(validator)(lambda x: x)
        assert func(4) == 4

        with pytest.raises(deal.PreContractError):
            func(-2)

        try:
            func(-2)
        except deal.PreContractError as e:
            assert e.args[0] == 'TEST'

    def test_error_returning(self):
        func = deal.pre(lambda x: x > 0 or 'TEST')(lambda x: x)
        assert func(4) == 4

        with pytest.raises(deal.PreContractError):
            func(-2)

        try:
            func(-2)
        except deal.PreContractError as e:
            assert e.args[0] == 'TEST'

    def test_wrapping(self):
        @deal.pre(lambda x: x > 0)
        def some_function(x):
            return x
        assert some_function.__name__ == 'some_function'

    def test_method_decorator(self):

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


class PostTest(unittest.TestCase):
    def test_main(self):
        func = deal.post(lambda x: x > 0)(lambda x: -x)
        assert func(-4) == 4

        with pytest.raises(deal.PostContractError):
            func(4)


class InvTest(unittest.TestCase):
    def test_setattr(self):
        @deal.inv(lambda obj: obj.x > 0)
        class A:
            x = 2

        a = A()
        a.x = 4
        with pytest.raises(deal.InvContractError):
            a.x = -2

    def test_method_call(self):
        @deal.inv(lambda obj: obj.x > 0)
        class A:
            x = 2

            def f(self, x):
                self.x = x

        a = A()

        a.f(4)
        with pytest.raises(deal.InvContractError):
            a.f(-2)

    def test_chain(self):
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

    def test_instance(self):
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

    def test_validation(self):
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

    def test_pre_chain(self):
        @deal.pre(self.Scheme)
        @deal.pre(lambda name: name != 'Oleg')
        def func(name):
            return name * 2

        assert func('Chris') == 'ChrisChris'

        with pytest.raises(deal.PreContractError):
            func(123)

        with pytest.raises(deal.PreContractError):
            func('Oleg')

    def test_invariant(self):
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

    def test_invariant_chain(self):
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

    def test_arg_passing(self):
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


class DefaultSchemeTests(MarshmallowSchemeTests):
    def setUp(self):
        class MyScheme(deal.Scheme):
            def is_valid(self):
                if not isinstance(self.data['name'], str):
                    self.errors = {'name': ['Not a valid string.']}
                    return False
                return True
        self.Scheme = MyScheme


class RaisesTest(unittest.TestCase):
    def test_main(self):
        func = deal.raises(ZeroDivisionError)(lambda x: 1 / x)
        with pytest.raises(ZeroDivisionError):
            func(0)
        func(2)

        func = deal.raises(KeyError)(lambda x: 1 / x)
        with pytest.raises(deal.RaisesContractError):
            func(0)

    def test_preserve_original_contract_error(self):
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


class OfflineTest(unittest.TestCase):
    def test_main(self):

        @deal.offline
        def func(do):
            if do:
                http = urllib3.PoolManager()
                http.request('GET', 'http://httpbin.org/robots.txt')

        func(False)
        with pytest.raises(deal.OfflineContractError):
            func(True)

    def test_different_exception(self):

        @deal.offline(exception=KeyError)
        def func(do):
            if do:
                http = urllib3.PoolManager()
                http.request('GET', 'http://httpbin.org/robots.txt')

        func(False)
        with pytest.raises(KeyError):
            func(True)


class SilentTest(unittest.TestCase):
    def test_main(self):

        @deal.silent
        def func(msg):
            if msg:
                print(msg)

        func(None)
        with pytest.raises(deal.SilentContractError):
            func('bad')


class ChainTest(unittest.TestCase):
    def test_main(self):

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


class StateTest(unittest.TestCase):
    def setUp(self):
        deal.reset()

    def tearDown(self):
        deal.reset()

    def test_debug(self):
        func = deal.pre(lambda x: x > 0, debug=True)(lambda x: x * 2)
        deal.switch(debug=False)
        func(-2)
        deal.switch(debug=True)
        with pytest.raises(deal.PreContractError):
            func(-2)

    def test_main(self):
        func = deal.pre(lambda x: x > 0)(lambda x: x * 2)
        deal.switch(main=False)
        func(-2)
        deal.switch(main=True)
        with pytest.raises(deal.PreContractError):
            func(-2)


class EnsureTest(unittest.TestCase):
    def test_main(self):
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


if __name__ == '__main__':
    pytest.main(['tests.py'])
