#
from flask import Flask

from admin import admin
from frontend import frontend
from classes import classes
from lessons import lessons
from prover import prover

app = Flask(__name__)

__all__ = ['admin', 'app', 'frontend', 'classes', 'lessons', 'prover']
