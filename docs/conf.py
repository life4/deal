#!/usr/bin/env python3
import os
import sys
from datetime import date
from pathlib import Path

import sphinx_rtd_theme
from m2r2 import MdInclude, convert
from sphinx.application import Sphinx

import deal


sys.path.append(os.path.abspath('../'))
extensions = [
    'sphinx.ext.autodoc',
    'sphinx.ext.doctest',
    'sphinx.ext.todo',
    'sphinx.ext.coverage',
    'sphinx.ext.viewcode',
    'sphinx.ext.githubpages',
    'sphinx.ext.autosectionlabel',
    'myst_parser',
]

templates_path = ['_templates']
source_suffix = ['.rst', '.md']
master_doc = 'index'

project = 'Deal'
copyright = '{}, Gram (@orsinium)'.format(date.today().year)
author = 'Gram (@orsinium)'

version = ''
release = ''

language = None
exclude_patterns: list = []
todo_include_todos = True

pygments_style = 'sphinx'
html_theme = 'sphinx_rtd_theme'
html_theme_path = [sphinx_rtd_theme.get_html_theme_path()]
html_static_path = [str(Path(__file__).parent.parent / 'assets')]
html_logo = str(Path(__file__).parent.parent / 'logo.png')
html_theme_options = {
    'logo_only': True,
    'display_version': False,
    'style_external_links': False,
    'style_nav_header_background': '#2c3e50',
}


# -- Options for HTMLHelp output ------------------------------------------

# Output file base name for HTML help builder.
htmlhelp_basename = 'dealdoc'


# -- Options for LaTeX output ---------------------------------------------

# Grouping the document tree into LaTeX files. List of tuples
# (source start file, target name, title,
#  author, documentclass [howto, manual, or own class]).
latex_documents = [
    (master_doc, 'deal.tex', 'Deal Documentation',
     '@orsinium', 'manual'),
]


# -- Options for manual page output ---------------------------------------

# One entry per manual page. List of tuples
# (source start file, name, description, authors, manual section).
man_pages = [(master_doc, 'deal', 'Deal Documentation', [author], 1)]


# -- Options for Texinfo output -------------------------------------------

# Grouping the document tree into Texinfo files. List of tuples
# (source start file, target name, title, author,
#  dir menu entry, description, category)
texinfo_documents = [
    (master_doc, 'deal', 'Deal Documentation',
     author, 'Deal', 'One line description of project.', 'Miscellaneous'),
]

autosectionlabel_prefix_document = True
add_function_parentheses = False


def autodoc_process(app, what, name, obj, options, lines):
    if not lines:
        return None
    text = convert('\n'.join(lines))
    lines[:] = text.split('\n')


def autodoc_signature(
    app, what, name, obj, options,
    signature: str, return_annotation: str,
):
    sig = signature
    ret = return_annotation
    if sig:
        sig = sig.replace('deal._runtime._decorators.', '')
        sig = sig.replace('Union[Exception, Type[Exception]]', 'Exception')
    if ret:
        ret = ret.replace('deal._runtime._decorators.', '')
        ret = ret.replace('deal._runtime.dispatch.', '')
    return (sig, ret)


def setup(app: Sphinx):
    # from m2r2 source code to make `mdinclude` work
    app.add_config_value('no_underscore_emphasis', False, 'env')
    app.add_config_value('m2r_parse_relative_links', False, 'env')
    app.add_config_value('m2r_anonymous_references', False, 'env')
    app.add_config_value('m2r_disable_inline_math', False, 'env')
    app.add_config_value('m2r_use_mermaid', False, 'env')
    app.add_directive('mdinclude', MdInclude)

    app.connect('autodoc-process-docstring', autodoc_process)
    app.connect('autodoc-process-signature', autodoc_signature)

    deal.autodoc(app)
