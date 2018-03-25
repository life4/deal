#!/usr/bin/env python3
# -*- coding: utf-8 -*-

from setuptools import setup


setup(
    name='deal',
    version='2.0.0',

    author='orsinium',
    author_email='master_fess@mail.ru',

    description='Programming by contract library.',
    long_description=open('README.rst').read(),
    keywords=(
        'python contracts pre post inv invariant '
        'contracts-programming decorators functional-programming '
        'design-by-contract'),

    packages=['deal'],
    requires=[],

    url='https://github.com/orsinium/deal',
    download_url='https://github.com/orsinium/deal/tarball/master',

    license='GNU Lesser General Public License v3.0',
    classifiers=[
        'Development Status :: 5 - Production/Stable',
        'Environment :: Plugins',
        'Intended Audience :: Developers',
        'License :: OSI Approved :: GNU Lesser General Public License v3 or later (LGPLv3+)',
        'Programming Language :: Python',
        'Topic :: Software Development',
        'Topic :: Software Development :: Libraries :: Python Modules',
        'Topic :: Software Development :: Quality Assurance',
    ],
)
