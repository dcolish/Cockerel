# Cockerel Paver definitions
# helps to run dev servers

import os

from paver.easy import *


@task
@needs('bootstrap')
def setup():
    '''Setup the branch'''
    print "Ready to boot servers"


@task
@needs('clean_pyc')
def clean_all():
    for area in 'cockerel', 'coqd':
        for dir, _, files in os.walk(area):
            for fn in files:
                if fn.endswith('.pyc'):
                    path(dir + '/' + fn).unlink()


@task
def clean_pyc():
    """Remove orphaned .pyc files."""
    for area in 'cockerel', 'coqd':
        for dir, _, files in os.walk(area):
            sources = set(fn for fn in files if fn.endswith('.py'))
            for fn in files:
                if fn.endswith('.pyc') and fn[:-1] not in sources:
                    path(dir + '/' + fn).unlink()


@task
@needs('setup')
def run():
    pass
