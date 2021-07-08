# built-in
import sys

# app
from .._cli import main


if __name__ == '__main__':
    sys.exit(main(['lint'] + sys.argv[1:]))
