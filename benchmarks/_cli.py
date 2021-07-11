from pathlib import Path

from ._core import run_test

import yaml


def main():
    path = Path(__file__).parent / 'tests.yaml'
    for group in yaml.safe_load(path.read_text()):
        print(group['name'])
        for item in group['items']:
            run_test(**item)
