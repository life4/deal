# project
import deal


@deal.require(lambda x: x > 0)
@deal.post(lambda x: x > 0)
@deal.ensure(lambda *args, **kwargs: True)
@deal.raises(ValueError)
def test(x: int) -> int:
    return x


@deal.inv(lambda o: o.x >= 0)
class Test(object):
    x = 0


reveal_type(test)
reveal_type(Test)
