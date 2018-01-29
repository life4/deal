from deal import pre, post, inv, PreContractError, PostContractError, InvContractError

try:
    import unittest2 as unittest
except ImportError:
    import unittest


class PreTest(unittest.TestCase):
    def test_main(self):
        func = pre(lambda x: x > 0)(lambda x: x)

        with self.subTest(text='good'):
            self.assertEqual(func(4), 4)

        with self.subTest(text='error'):
            with self.assertRaises(PreContractError):
                func(-2)

    def test_chain(self):
        func = pre(lambda x: x < 10)(lambda x: x)
        func = pre(lambda x: x > 0)(func)

        with self.subTest(text='good'):
            self.assertEqual(func(4), 4)

        with self.subTest(text='error'):
            with self.assertRaises(PreContractError):
                func(-2)

        with self.subTest(text='error'):
            with self.assertRaises(PreContractError):
                func(20)

    def test_init(self):
        with self.subTest(text='init doesn\'t raise any exceptions'):
            func = pre(lambda x: x > 0)

        with self.subTest(text='validator'):
            func = pre(lambda x: x > 0)(lambda x: x)
            with self.assertRaises(PreContractError):
                func(-2)

        with self.subTest(text='message'):
            func = pre(lambda x: x > 0, message='TEST')(lambda x: x)
            try:
                func(-2)
            except AssertionError as e:
                self.assertEqual(e.args[0], 'TEST')

        with self.subTest(text='exception'):
            func = pre(lambda x: x > 0, exception=NameError)(lambda x: x)
            with self.assertRaises(NameError):
                func(-2)

        with self.subTest(text='exception with name'):
            func = pre(lambda x: x > 0, exception=NameError('TEST'))(lambda x: x)
            with self.subTest(text='exception/exception'):
                with self.assertRaises(NameError):
                    func(-2)
            with self.subTest(text='exception/message'):
                try:
                    func(-2)
                except NameError as e:
                    self.assertEqual(e.args[0], 'TEST')

        with self.subTest(text='exception+message'):
            func = pre(lambda x: x > 0, message='TEST', exception=NameError)(lambda x: x)
            with self.subTest(text='exception+message/exception'):
                with self.assertRaises(NameError):
                    func(-2)
            with self.subTest(text='exception+message/message'):
                try:
                    func(-2)
                except NameError as e:
                    self.assertEqual(e.args[0], 'TEST')

    def test_call(self):
        with self.subTest(text='call return patched function'):
            deco = pre(lambda x: x > 0)
            func = deco(lambda x: x)
            self.assertIsInstance(func, type(deco.patched_function))

    def test_django_style(self):
        class Validator(object):
            def __init__(self, x):
                self.x = x

            def is_valid(self):
                if self.x <= 0:
                    self.errors = 'TEST'
                    return False
                return True

        func = pre(Validator)(lambda x: x)
        with self.subTest(text='good'):
            self.assertEqual(func(4), 4)

        with self.subTest(text='error'):
            with self.assertRaises(PreContractError):
                func(-2)

        with self.subTest(text='error message'):
            try:
                func(-2)
            except PreContractError as e:
                self.assertEqual(e.args[0], 'TEST')

    def test_error_returning(self):
        func = pre(lambda x: x > 0 or 'TEST')(lambda x: x)
        with self.subTest(text='good'):
            self.assertEqual(func(4), 4)

        with self.subTest(text='error'):
            with self.assertRaises(PreContractError):
                func(-2)

        with self.subTest(text='error message'):
            try:
                func(-2)
            except PreContractError as e:
                self.assertEqual(e.args[0], 'TEST')


class PostTest(unittest.TestCase):
    def test_main(self):
        func = post(lambda x: x > 0)(lambda x: -x)
        with self.subTest(text='good'):
            self.assertEqual(func(-4), 4)
        with self.subTest(text='error'):
            with self.assertRaises(PostContractError):
                func(4)


class InvTest(unittest.TestCase):
    def test_setattr(self):
        @inv(lambda obj: obj.x > 0)
        class A(object):
            x = 2

        a = A()
        with self.subTest(text='good'):
            a.x = 4
        with self.subTest(text='error'):
            with self.assertRaises(InvContractError):
                a.x = -2

    def test_method_call(self):
        @inv(lambda obj: obj.x > 0)
        class A(object):
            x = 2

            def f(self, x):
                self.x = x

        a = A()
        with self.subTest(text='good'):
            a.f(4)
        with self.subTest(text='error'):
            with self.assertRaises(InvContractError):
                a.f(-2)

    def test_chain(self):
        @inv(lambda obj: obj.x > 0)
        @inv(lambda obj: obj.x < 10)
        class A(object):
            x = 2

        a = A()
        with self.subTest(text='good'):
            a.x = 4
        with self.subTest(text='error'):
            with self.assertRaises(InvContractError):
                a.x = -2
        with self.subTest(text='error'):
            with self.assertRaises(InvContractError):
                a.x = 20

    def test_instance(self):
        class A(object):
            x = 2
        PatchedA = inv(lambda obj: obj.x > 0)(A)  # noQA
        a = PatchedA()
        with self.subTest(text='isinstance'):
            self.assertIsInstance(a, PatchedA)
            self.assertIsInstance(a, A)

        PatchedA2 = inv(lambda obj: obj.x > 0)(PatchedA)  # noQA
        a = PatchedA2()
        with self.subTest(text='isinstance'):
            self.assertIsInstance(a, PatchedA)
            self.assertIsInstance(a, PatchedA2)
            self.assertIsInstance(a, A)
        with self.subTest(text='class name'):
            self.assertEqual(a.__class__.__name__.count('Invarianted'), 1)


if __name__ == '__main__':
    unittest.main()
