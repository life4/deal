import re

import deal


def contract(template: str, *args):
    rex = re.compile(r'\{\:([a-z])\}')
    types = {'s': str, 'd': float}
    matches = rex.findall(template)
    if len(matches) != len(args):
        return f'expected {len(matches)} argument(s) but {len(args)} found'
    for match, arg in zip(matches, args):
        t = types[match[0]]
        if not isinstance(arg, t):
            return f'expected {t.__name__}, {type(arg).__name__} given'
    return True


@deal.pre(contract)
def format(template: str, *args) -> str:
    return template.format(*args)


@deal.has('io')
def example():
    # good
    print(format('{:s}', 'hello'))

    # bad
    print(format('{:s}'))               # not enough args
    print(format('{:s}', 'a', 'b'))     # too many args
    print(format('{:d}', 'a'))          # bad type


if __name__ == '__main__':
    print(format('{:s} {:s}', 'hello', 'world'))
