"""
cockerel.webapp
---------------
Main instance of the webapp. All modules will be loaded from this file. To
add a new module you must import it here and register it.
"""
import logging
import os

from flask import g

from flaskext.markdown import Markdown

from cockerel.models import db

from cockerel.webapp import (
    admin,
    classes,
    frontend,
    lessons,
    prover,
    )
from cockerel.webapp.prover import ProverExtension


def update_config(app):
    """syncronizes the config with the g global request object"""
    g.config = app.config


def register_modules(app, mod_list):
    for x in mod_list:
        app.register_module(x)


def new_app(app, serialize=False):
    logging.basicConfig(level=logging.DEBUG)
    md = Markdown(app, extensions=['tables'])
    md.register_extension(ProverExtension)
    register_modules(app, [admin, classes, frontend, lessons, prover])
    app.secret_key = os.urandom(24)
    app.config['SQLALCHEMY_DATABASE_URI'] = 'sqlite:////tmp/test.db'
    app.config['COQD_HOST'] = 'localhost'
    app.config['COQD_PORT'] = 8003
    if serialize:
        app.config['serialize'] = serialize

    # XXX:dc: kind of a hack but I want to keep the db and the app seperate
    db.init_app(app)
    db.app = app

    return app
