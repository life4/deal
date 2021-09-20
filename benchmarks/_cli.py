from pathlib import Path

import yaml

from ._core import run_test


def main():
    path = Path(__file__).parent / 'tests.yaml'
    for group in yaml.safe_load(path.read_text()):
        print(group['name'])
        for item in group['items']:
            run_test(**item)
