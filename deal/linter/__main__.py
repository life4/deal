import sys

from .._cli import main


sys.exit(main(['lint'] + sys.argv[1:]))
