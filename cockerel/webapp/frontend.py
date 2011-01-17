from flask import (
    Module,
    render_template,
)

frontend = Module(__name__)


@frontend.route('/', methods=['GET'])
def index():
    # TODO: what do we need on the homepage?
    # How about notifications of new stuff added
    return render_template("base.html")
