"""
cockerel.webapp
---------------
Main instance of the webapp. All modules will be loaded from this file. To
add a new module you must import it here and register it.
"""
import logging
import os

from flask import Flask, g
from flaskext.sqlalchemy import SQLAlchemy
from flaskext.markdown import Markdown

logging.basicConfig(level=logging.DEBUG)

HOST = "localhost"
app = Flask(__name__)
db = SQLAlchemy(app)
md = Markdown(app, extensions=['tables'])

from .views.prover.mdx_prover import ProverExtension
md.register_extension(ProverExtension)

from .views.admin import admin
from .views.classes import classes
from .views.frontend import frontend
from .views.lessons import lessons
from .views.prover.prover import prover
from .utils import register_modules

register_modules(app, [admin, classes, frontend, lessons, prover])

app.secret_key = os.urandom(24)

app.config['SQLALCHEMY_DATABASE_URI'] = 'sqlite:////tmp/test.db'
app.config['COQD_HOST'] = 'localhost'
app.config['COQD_PORT'] = 8003

# see if the db exists, if not make it and initialize
if not os.path.exists(app.config.get('SQLALCHEMY_DATABASE_URI')):
    db.create_all()


def update_config():
    """syncronizes the config with the g global request object"""
    g.config = app.config

app.before_request(update_config)


def new_app(serialize):
    if serialize:
        app.config['serialize'] = serialize
    return app
