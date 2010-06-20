from json import JSONDecoder, JSONEncoder
import logging
from uuid import uuid4

import os
import telnetlib

from flask import Flask, session, render_template, request, url_for

logging.basicConfig(level=logging.DEBUG)


app = Flask(__name__)
app.secret_key = os.urandom(24)
HOST = "localhost"


@app.route('/', methods=['GET', 'POST'])
def prover():
    url_for('static', filename='site.css')
    site_css = '/static/site.css'
    proofst = None
    unprocessed = "(* Begin Your Proof Here *)"
    lineno = 0

    if request.method == 'POST':
        if not session.get('id'):
            session['id'] = uuid4()

        # splitlines will need to chew up blank lines
        # so we dont get into trouble

        if request.form.get('clear'):
            command = 'quit'
            processed = None
            proofscript = request.form.get('proofscript')
            commandlist = proofscript.splitlines()
            unprocessed = '\n'.join(commandlist)

        elif request.form.get('undo'):
            lineno = int(request.form.get('line')) - 1
            proofscript = request.form.get('proofscript')
            commandlist = proofscript.splitlines()
            processed = '\n'.join(commandlist[:lineno + 1])
            unprocessed = '\n'.join(commandlist[lineno + 2:])
            command = 'Undo.'

        else:
            lineno = int(request.form.get('line')) + 1
            proofscript = request.form.get('proofscript')
            commandlist = proofscript.splitlines()
            processed = '\n'.join(commandlist[:lineno + 1])
            unprocessed = '\n'.join(commandlist[lineno + 2:])
            command = commandlist[lineno]
            logging.debug('Sending %d : %s', lineno, command)

        # here is where we'll pass it to coqd
        if command:
            try:
                tn = telnetlib.Telnet(HOST, 8000)
                tn.write(JSONEncoder().encode(dict(userid=str(session['id']),
                                               command=command)))

                proofst = JSONDecoder().decode(tn.read_all())
                proofst = proofst.get('response', None)
            except Exception:
                logging.error("Connection to coqd failed")

        return render_template('prover.html',
                               processed=processed,
                               unprocessed=unprocessed,
                               proofst=proofst,
                               site_css=site_css,
                               lineno=lineno)
    else:
        return render_template('prover.html',
                               proofst=proofst,
                               processed=None,
                               unprocessed=unprocessed,
                               site_css=site_css,
                               lineno=lineno)


if __name__ == '__main__':
    app.debug = True
    app.run()
