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
def clean_pyc():
    """Remove orphaned .pyc files."""
    for area in 'idealist', 'test', 'test2':
        for dir, _, files in os.walk(area):
            sources = set(fn for fn in files if fn.endswith('.py'))
            for fn in files:
                if fn.endswith('.pyc') and fn[:-1] not in sources:
                    path(dir + '/' + fn).unlink()


@task
@needs('setup')
def run():
    pass
