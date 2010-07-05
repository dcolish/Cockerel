import logging
import os

from flask import Flask
from flaskext.sqlalchemy import SQLAlchemy

logging.basicConfig(level=logging.DEBUG)

HOST = "localhost"
app = Flask(__name__)
db = SQLAlchemy(app)

from webapp.views.admin import admin
from webapp.views.frontend import frontend
from webapp.views.prover import prover
from webapp.util import register_modules

register_modules(app, [admin, frontend, prover])

app.secret_key = os.urandom(24)
app.config['SQLALCHEMY_DATABASE_URI'] = 'sqlite:////tmp/test.db'
