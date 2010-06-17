from json import JSONDecoder, JSONEncoder
import logging
from uuid import uuid4

import telnetlib

from flask import Flask, session, render_template, request

logging.basicConfig(level=logging.DEBUG)


app = Flask(__name__)
app.secret_key = 'A0Zr98j/3yX R~XHH!jmN]LWX/,?RT'
HOST = "localhost"


@app.route('/', methods=['GET', 'POST'])
def index():
    # from pdb import set_trace; set_trace()
    proofst = None
    proofscript = "(* Begin Your Proof Here *)"
    lineno = 0

    if request.method == 'POST':
        if not session.get('id'):
            session['id'] = uuid4()
        lineno = int(request.form.get('line')) + 1
        proofscript = request.form.get('proofscript')
        flatproof = proofscript.splitlines()
        logging.debug('Script: %s', flatproof)
        logging.debug('Sending %d : %s', lineno, flatproof[lineno])
        # here is where we'll pass it to coqd
        if flatproof[lineno]:
            tn = telnetlib.Telnet(HOST, 8000)
            tn.write(JSONEncoder().encode(dict(userid=str(session['id']),
                                               command=flatproof[lineno])))
            proofst = JSONDecoder().decode(tn.read_all())
            proofst = proofst.get('response', None)
        return render_template('prover.html',
                               proofscript=proofscript,
                               proofst=proofst,
                               lineno=lineno)
    else:
        return render_template('prover.html',
                               proofst=proofst,
                               proofscript=proofscript,
                               lineno=lineno)


if __name__ == '__main__':
    app.debug = True
    app.run()
