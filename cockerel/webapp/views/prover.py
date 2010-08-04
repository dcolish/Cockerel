from json import JSONDecoder, JSONEncoder
import logging
import telnetlib
from uuid import uuid4

from flask import (
    g,
    Module,
    url_for,
    render_template,
    request,
    session,
    )

prover = Module(__name__)


def readscript(script):
    '''Chew up blank lines'''
    return [x for x in script.splitlines() if not x == '']


def formatscript(script, slice):
    commandlist = readscript(script)
    processed = '\\n'.join(commandlist[:slice])
    unprocessed = '\\n'.join(commandlist[slice:])
    return processed, unprocessed, commandlist


def ping_coqd():
    pass


@prover.route('/prover', methods=['GET', 'POST'])
def editor():
    proofst = None
    host = g.config.get('COQD_HOST')
    port = g.config.get('COQD_PORT')
    lineno = 0

    if request.method == 'POST':
        if not session.get('id'):
            session['id'] = uuid4()

        if request.form.get('clear'):
            command = 'quit'
            proofscript = request.form.get('proofscript')
            processed, unprocessed, commandlist = formatscript(proofscript, 0)
            processed = None

        elif request.form.get('undo'):
            lineno = 0 if lineno == 0 else int(request.form.get('line')) - 1
            proofscript = request.form.get('proofscript')
            processed, unprocessed, commandlist = formatscript(proofscript,
                                                               lineno)
            command = 'Undo.'

        else:
            lineno = int(request.form.get('line'))
            proofscript = request.form.get('proofscript')
            processed, unprocessed, commandlist = formatscript(proofscript,
                                                  lineno)
            command = commandlist[lineno]
            logging.debug('Sending %d : %s', lineno, command)
            lineno += 1
        # here is where we'll pass it to coqd
        if command:
            try:
                tn = telnetlib.Telnet(host, port)
                tn.write(JSONEncoder().encode(dict(userid=str(session['id']),
                                               command=command)))

                proofst = JSONDecoder().decode(tn.read_all())
                proofst = proofst.get('response', None)

            except Exception:
                lineno = lineno - 1 if lineno != 0 else 0
                logging.error("Connection to coqd failed")

        return render_template('prover/prover.html',
                               prover_url=url_for('editor'),
                               processed=processed,
                               unprocessed=unprocessed,
                               proofst=proofst,
                               lineno=lineno)
    else:
        # new proof session so set it up
        unprocessed = request.args.get('proof', "(* Begin Your Proof Here *)")
        return render_template('prover/prover.html',
                               prover_url=url_for('editor'),
                               proofst=proofst,
                               processed=None,
                               unprocessed=unprocessed,
                               lineno=lineno)
