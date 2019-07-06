import djburger
import marshmallow
import urllib3

import deal
from deal.schemes import is_scheme

try:
    import unittest2 as unittest
except ImportError:
    import unittest


class PreTest(unittest.TestCase):
    def test_main(self):
        func = deal.pre(lambda x: x > 0)(lambda x: x)

        with self.subTest(text='good'):
            self.assertEqual(func(4), 4)

        with self.subTest(text='error'):
            with self.assertRaises(deal.PreContractError):
                func(-2)

    def test_chain(self):
        func = deal.pre(lambda x: x < 10)(lambda x: x)
        func = deal.pre(lambda x: x > 0)(func)

        with self.subTest(text='good'):
            self.assertEqual(func(4), 4)

        with self.subTest(text='error'):
            with self.assertRaises(deal.PreContractError):
                func(-2)

        with self.subTest(text='error'):
            with self.assertRaises(deal.PreContractError):
                func(20)

    def test_init(self):
        with self.subTest(text='init has not raised any exceptions'):
            func = deal.pre(lambda x: x > 0)

        with self.subTest(text='validator'):
            func = deal.pre(lambda x: x > 0)(lambda x: x)
            with self.assertRaises(deal.PreContractError):
                func(-2)

        with self.subTest(text='message'):
            func = deal.pre(lambda x: x > 0, message='TEST')(lambda x: x)
            try:
                func(-2)
            except AssertionError as e:
                self.assertEqual(e.args[0], 'TEST')

        with self.subTest(text='exception'):
            func = deal.pre(lambda x: x > 0, exception=NameError)(lambda x: x)
            with self.assertRaises(NameError):
                func(-2)

        with self.subTest(text='exception with name'):
            func = deal.pre(lambda x: x > 0, exception=NameError('TEST'))(lambda x: x)
            with self.subTest(text='exception/exception'):
                with self.assertRaises(NameError):
                    func(-2)
            with self.subTest(text='exception/message'):
                try:
                    func(-2)
                except NameError as e:
                    self.assertEqual(e.args[0], 'TEST')

        with self.subTest(text='exception+message'):
            func = deal.pre(lambda x: x > 0, message='TEST', exception=NameError)(lambda x: x)
            with self.subTest(text='exception+message/exception'):
                with self.assertRaises(NameError):
                    func(-2)
            with self.subTest(text='exception+message/message'):
                try:
                    func(-2)
                except NameError as e:
                    self.assertEqual(e.args[0], 'TEST')

    def _test_validator(self, validator):
        func = deal.pre(validator)(lambda x: x)
        with self.subTest(text='good'):
            self.assertEqual(func(4), 4)

        with self.subTest(text='error'):
            with self.assertRaises(deal.PreContractError):
                func(-2)

        with self.subTest(text='error message'):
            try:
                func(-2)
            except deal.PreContractError as e:
                self.assertEqual(e.args[0], 'TEST')

    def test_django_style(self):
        class Validator:
            def __init__(self, x):
                self.x = x

            def is_valid(self):
                if self.x <= 0:
                    self.errors = 'TEST'
                    return False
                return True

        self._test_validator(Validator)

    def test_django_style_hidden_attr(self):
        class Validator:
            def __init__(self, x):
                self.x = x

            def is_valid(self):
                if self.x <= 0:
                    self._errors = 'TEST'
                    return False
                return True

        self._test_validator(Validator)

    def test_django_style_without_attr(self):
        class Validator:
            def __init__(self, x):
                self.x = x

            def is_valid(self):
                if self.x <= 0:
                    return False
                return True

        func = deal.pre(Validator)(lambda x: x)
        with self.subTest(text='good'):
            self.assertEqual(func(4), 4)

        with self.subTest(text='error'):
            with self.assertRaises(deal.PreContractError):
                func(-2)

    def test_error_returning(self):
        func = deal.pre(lambda x: x > 0 or 'TEST')(lambda x: x)
        with self.subTest(text='good'):
            self.assertEqual(func(4), 4)

        with self.subTest(text='error'):
            with self.assertRaises(deal.PreContractError):
                func(-2)

        with self.subTest(text='error message'):
            try:
                func(-2)
            except deal.PreContractError as e:
                self.assertEqual(e.args[0], 'TEST')

    def test_wrapping(self):
        @deal.pre(lambda x: x > 0)
        def some_function(x):
            return x
        with self.subTest(text='good'):
            self.assertEqual(some_function.__name__, 'some_function')

    def test_method_decorator(self):

        class Class:
            y = 7

            @deal.pre(lambda self, x: x > 0)
            def method(self, x):
                return x * 2

            @deal.pre(lambda self, x: x > 0)
            def method2(self, y):
                return self.y

        self.assertEqual(Class().method(2), 4)
        self.assertEqual(Class().method2(2), 7)
        with self.assertRaises(deal.PreContractError):
            Class().method(-2)
        with self.assertRaises(deal.PreContractError):
            Class().method2(-2)


class PostTest(unittest.TestCase):
    def test_main(self):
        func = deal.post(lambda x: x > 0)(lambda x: -x)
        with self.subTest(text='good'):
            self.assertEqual(func(-4), 4)
        with self.subTest(text='error'):
            with self.assertRaises(deal.PostContractError):
                func(4)


class InvTest(unittest.TestCase):
    def test_setattr(self):
        @deal.inv(lambda obj: obj.x > 0)
        class A:
            x = 2

        a = A()
        with self.subTest(text='good'):
            a.x = 4
        with self.subTest(text='error'):
            with self.assertRaises(deal.InvContractError):
                a.x = -2

    def test_method_call(self):
        @deal.inv(lambda obj: obj.x > 0)
        class A:
            x = 2

            def f(self, x):
                self.x = x

        a = A()
        with self.subTest(text='good'):
            a.f(4)
        with self.subTest(text='error'):
            with self.assertRaises(deal.InvContractError):
                a.f(-2)

    def test_chain(self):
        @deal.inv(lambda obj: obj.x > 0)
        @deal.inv(lambda obj: obj.x < 10)
        class A:
            x = 2

        a = A()
        with self.subTest(text='good'):
            a.x = 4
        with self.subTest(text='error'):
            with self.assertRaises(deal.InvContractError):
                a.x = -2
        with self.subTest(text='error'):
            with self.assertRaises(deal.InvContractError):
                a.x = 20

    def test_instance(self):
        class A:
            x = 2
        PatchedA = deal.inv(lambda obj: obj.x > 0)(A)  # noQA
        a = PatchedA()
        with self.subTest(text='isinstance'):
            self.assertIsInstance(a, PatchedA)
            self.assertIsInstance(a, A)

        PatchedA2 = deal.inv(lambda obj: obj.x > 0)(PatchedA)  # noQA
        a = PatchedA2()
        with self.subTest(text='isinstance'):
            self.assertIsInstance(a, PatchedA)
            self.assertIsInstance(a, PatchedA2)
            self.assertIsInstance(a, A)
        with self.subTest(text='class name'):
            self.assertEqual(a.__class__.__name__.count('Invarianted'), 1)


class MarshmallowSchemeTests(unittest.TestCase):
    def setUp(self):
        class _Scheme(djburger.v.b.Marshmallow):
            name = marshmallow.fields.Str()
        self.Scheme = _Scheme

    def test_detecting(self):
        with self.subTest('is scheme'):
            self.assertTrue(is_scheme(self.Scheme))
        with self.subTest('is func'):
            self.assertFalse(is_scheme(deal.pre))
        with self.subTest('is class'):
            self.assertFalse(is_scheme(deal.InvContractError))

    def test_validation(self):
        @deal.pre(self.Scheme)
        def func(name):
            return name * 2

        with self.subTest('simple call'):
            self.assertEqual(func('Chris'), 'ChrisChris')

        with self.subTest('not passed validation'):
            with self.assertRaises(deal.PreContractError):
                func(123)

        with self.subTest('error message'):
            try:
                func(123)
            except deal.PreContractError as e:
                self.assertEqual(e.args[0], {'name': ['Not a valid string.']})

    def test_arg_passing(self):
        @deal.pre(self.Scheme)
        def func(name):
            return name * 2

        with self.subTest('arg'):
            self.assertEqual(func('Chris'), 'ChrisChris')

        with self.subTest('kwarg'):
            self.assertEqual(func(name='Chris'), 'ChrisChris')

        @deal.pre(self.Scheme)
        def func(**kwargs):
            return kwargs['name'] * 3

        with self.subTest('kwargs'):
            self.assertEqual(func(name='Chris'), 'ChrisChrisChris')

        @deal.pre(self.Scheme)
        def func(name='Max'):
            return name * 2

        with self.subTest('default'):
            self.assertEqual(func(), 'MaxMax')


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
        with self.subTest(text='good'):
            with self.assertRaises(ZeroDivisionError):
                func(0)
        with self.subTest(text='good'):
            func(2)

        func = deal.raises(KeyError)(lambda x: 1 / x)
        with self.subTest(text='error'):
            with self.assertRaises(deal.RaisesContractError):
                func(0)

    def test_preserve_original_contract_error(self):
        @deal.raises(ZeroDivisionError)
        @deal.offline
        def func(do, number):
            if do:
                http = urllib3.PoolManager()
                http.request('GET', 'http://httpbin.org/robots.txt')
            1 / number

        with self.subTest(text='good'):
            func(False, 1)
        with self.subTest(text='error'):
            with self.assertRaises(deal.OfflineContractError):
                func(True, 1)
        with self.subTest(text='error'):
            with self.assertRaises(ZeroDivisionError):
                func(False, 0)


class OfflineTest(unittest.TestCase):
    def test_main(self):

        @deal.offline
        def func(do):
            if do:
                http = urllib3.PoolManager()
                http.request('GET', 'http://httpbin.org/robots.txt')

        with self.subTest(text='good'):
            func(False)
        with self.subTest(text='error'):
            with self.assertRaises(deal.OfflineContractError):
                func(True)

    def test_different_exception(self):

        @deal.offline(exception=KeyError)
        def func(do):
            if do:
                http = urllib3.PoolManager()
                http.request('GET', 'http://httpbin.org/robots.txt')

        with self.subTest(text='good'):
            func(False)
        with self.subTest(text='error'):
            with self.assertRaises(KeyError):
                func(True)


class SilentTest(unittest.TestCase):
    def test_main(self):

        @deal.silent
        def func(msg):
            if msg:
                print(msg)

        with self.subTest(text='good'):
            func(None)
        with self.subTest(text='error'):
            with self.assertRaises(deal.SilentContractError):
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

        with self.subTest(text='good'):
            func(False, False)
        with self.subTest(text='silent error'):
            with self.assertRaises(deal.SilentContractError):
                func(True, False)
        with self.subTest(text='offline error'):
            with self.assertRaises(deal.OfflineContractError):
                func(False, True)


class StateTest(unittest.TestCase):
    def setUp(self):
        deal.reset()

    def tearDown(self):
        deal.reset()

    def test_debug(self):
        func = deal.pre(lambda x: x > 0, debug=True)(lambda x: x * 2)
        deal.switch(debug=False)
        with self.subTest(text='good'):
            func(-2)
        deal.switch(debug=True)
        with self.subTest(text='error'):
            with self.assertRaises(deal.PreContractError):
                func(-2)

    def test_main(self):
        func = deal.pre(lambda x: x > 0)(lambda x: x * 2)
        deal.switch(main=False)
        with self.subTest(text='good'):
            func(-2)
        deal.switch(main=True)
        with self.subTest(text='error'):
            with self.assertRaises(deal.PreContractError):
                func(-2)


if __name__ == '__main__':
    unittest.main()
