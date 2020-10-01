# built-in
import sys

# app
from .._cli._lint import lint_command


if __name__ == '__main__':
    sys.exit(lint_command(sys.argv[1:]))
