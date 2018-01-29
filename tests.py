from deal import pre, post, inv
from deal.core import Pre, Post, Invariant
from deal.exceptions import ContractError, PreContractError, PostContractError, InvContractError

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


class PostTest(unittest.TestCase):
    def test_main(self):
        func = post(lambda x: x > 0)(lambda x: x)
        with self.subTest(text='good'):
            self.assertEqual(func(4), 4)
        with self.subTest(text='error'):
            with self.assertRaises(PostContractError):
                func(-2)


class InvTest(unittest.TestCase):
    def test_main(self):
        @inv(lambda obj: obj.x > 0)
        class A(object):
            x = 2

        a = A()
        with self.subTest(text='good'):
            a.x = 4
        with self.subTest(text='error'):
            with self.assertRaises(InvContractError):
                a.x = -2


if __name__ == '__main__':
    unittest.main()
