from contracts import pre, post, inv, ValidationError
try:
    import unittest2 as unittest
except ImportError:
    import unittest


class PreTest(unittest.TestCase):
    def test_true_false(self):
        func = pre(lambda x: x > 0)(lambda x: x)
        self.assertEqual(func(4), 4)
        with self.assertRaises(ValidationError):
            func(-2)
        with self.assertRaises(ValidationError):
            func(0)


class PostTest(unittest.TestCase):
    def test_true_false(self):
        func = post(lambda x: x > 0)(lambda x: x)
        self.assertEqual(func(4), 4)
        with self.assertRaises(ValidationError):
            func(-2)
        with self.assertRaises(ValidationError):
            func(0)


class InvTest(unittest.TestCase):
    def test_true_false(self):
        @inv(lambda obj: obj.x > 0)
        class A(object):
            x = 2

        a = A()
        a.x = 4
        self.assertEqual(a.x, 4)
        with self.assertRaises(ValidationError):
            a.x = -2
        with self.assertRaises(ValidationError):
            a.x = 0


if __name__ == '__main__':
    unittest.main()
