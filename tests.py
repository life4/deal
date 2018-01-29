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


class PostTest(unittest.TestCase):
    def test_true_false(self):
        func = post(lambda x: x > 0)(lambda x: x)
        with self.subTest(text='good'):
            self.assertEqual(func(4), 4)
        with self.subTest(text='error'):
            with self.assertRaises(PostContractError):
                func(-2)


class InvTest(unittest.TestCase):
    def test_true_false(self):
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
