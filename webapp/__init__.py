import logging
import os

from flask import (
    Flask,
    g,
    session,
    redirect,
    render_template,
    request,
    url_for,
    )

from webapp.util import register_modules
from webapp.views.admin import admin
from webapp.views.frontend import frontend
from webapp.views.prover import prover

logging.basicConfig(level=logging.DEBUG)
HOST = "localhost"
app = Flask(__name__)
app.secret_key = os.urandom(24)

logging.debug("Registering Modules")
register_modules(app, [admin, frontend, prover])
