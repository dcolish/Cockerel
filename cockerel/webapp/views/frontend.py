from flask import Module

frontend = Module(__name__)

@frontend.route('/', methods=['GET'])
def index():
    # TODO: what do we need on the homepage?
    return '''
<p>Hi luser~!</p>'''
