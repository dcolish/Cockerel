import logging
import os

from flask import Flask
from flaskext.sqlalchemy import SQLAlchemy
from flaskext.markdown import Markdown

logging.basicConfig(level=logging.DEBUG)

HOST = "localhost"
app = Flask(__name__)
db = SQLAlchemy(app)

Markdown(app)

from .views.admin import admin
from .views.classes import classes
from .views.frontend import frontend
from .views.lessons import lessons
from .views.prover import prover
from .util import register_modules

register_modules(app, [admin, classes, frontend, lessons, prover])

app.secret_key = os.urandom(24)

app.config['SQLALCHEMY_DATABASE_URI'] = 'sqlite:////tmp/test.db'

# see if the db exists, if not make it and initialize
if not os.path.exists(app.config.get('SQLALCHEMY_DATABASE_URI')):
    db.create_all()
