from json import JSONDecoder, JSONEncoder
import logging
from uuid import uuid4

import telnetlib

from flask import Flask, session, render_template, request, url_for

logging.basicConfig(level=logging.DEBUG)


app = Flask(__name__)
app.secret_key = 'A0Zr98j/3yX R~XHH!jmN]LWX/,?RT'
HOST = "localhost"


@app.route('/', methods=['GET', 'POST'])
def index():
    url_for('static', filename='site.css')
    site_css = '/static/site.css'
    proofst = None
    proofscript = "(* Begin Your Proof Here *)"
    lineno = 0

    if request.method == 'POST':
        if not session.get('id'):
            session['id'] = uuid4()
        lineno = int(request.form.get('line')) + 1
        proofscript = request.form.get('proofscript')
        flatproof = proofscript.splitlines()
        logging.debug('Sending %d : %s', lineno, flatproof[lineno])

        # here is where we'll pass it to coqd
        if flatproof[lineno]:
            try:
                tn = telnetlib.Telnet(HOST, 8000)
                tn.write(JSONEncoder().encode(dict(userid=str(session['id']),
                                               command=flatproof[lineno])))

                proofst = JSONDecoder().decode(tn.read_all())
                proofst = proofst.get('response', None)
            except Exception:
                logging.error("Connection to coqd failed")

        return render_template('prover.html',
                               proofscript=proofscript,
                               proofst=proofst,
                               site_css=site_css,
                               lineno=lineno)
    else:
        return render_template('prover.html',
                               proofst=proofst,
                               proofscript=proofscript,
                               site_css=site_css,
                               lineno=lineno)


if __name__ == '__main__':
    app.debug = True
    
    app.run()
