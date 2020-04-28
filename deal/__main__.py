# built-in
import sys

# app
from ._cli import main


if __name__ == '__main__':
    exit(main(sys.argv[1:]))
