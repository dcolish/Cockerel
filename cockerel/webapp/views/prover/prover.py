from json import JSONDecoder, JSONEncoder
from hashlib import sha1
import logging
import telnetlib
from uuid import uuid4

from flask import (
    g,
    Module,
    render_template,
    request,
    session,
    url_for,
    )

from cockerel.models.schema import Proof, Theorem
from cockerel.webapp.views.util import login_required

prover = Module(__name__)


class ProofException(Exception):
    """Identifier for proof exceptions"""
    pass


def readscript(script):
    """Chew up blank lines, and be a little lame about it"""
    return [x.strip() + '.' for x in script.strip().rsplit(r'.')
            if not x == u'']


def exec_cmd(command, session):
    host = g.config.get('COQD_HOST')
    port = g.config.get('COQD_PORT')

    try:
        tn = telnetlib.Telnet(host, port)
        tn.write(JSONEncoder().encode(dict(userid=str(session['id']),
                                           command=command)))

        if g.config.get('serialize'):
            proofst = JSONDecoder().decode(tn.read_all())
            data = proofst.get('response', None)
        else:
            data = tn.read_all()
        return data

    except Exception:
        logging.error("Connection to coqd failed")
        raise ProofException()


def get_proofscript(request):
    proofscript = request.form.get('proofscript')
    return formatscript(proofscript)


def formatscript(script):
    commandlist = readscript(script)
    theorem = commandlist[0]
    proof = '\\n'.join(commandlist[1:])
    return theorem, proof, commandlist


def hash_theorem(theorem):
    return sha1(theorem).hexdigest()


def ping_coqd():
    """check the coqd server is alive"""
    pass


@prover.route('/prover/', methods=['GET'])
@prover.route('/prover/<int:theorem_id>', methods=['GET', 'POST'])
@login_required
def editor(theorem_id=0):
    proofst = processed = None
    lineno = 0
    theorem = Theorem.query.filter_by(id=theorem_id).first()

    if theorem:
        theorem_text = theorem.text.rstrip()
        proof = Proof.query.filter_by(theorem=theorem).filter_by(
            user_id=g.user.id).first()

        if not proof:
            proof = ""

    else:
        theorem_text = proof = ""

    unprocessed = ''.join([theorem_text, proof])

    if request.method == 'POST':
        if not session.get('id'):
            session['id'] = uuid4()

        if request.form.get('clear'):
            processed, unprocessed, commandlist = get_proofscript(request)
            command = 'quit'
            processed = None
            unprocessed = '\\n'.join([theorem_text, unprocessed])

        elif request.form.get('undo'):
            lineno = 0 if lineno == 0 else int(request.form.get('line')) - 1
            processed, unprocessed, commandlist = get_proofscript(request)
            command = 'Undo.'

        else:
            lineno = int(request.form.get('line'))
            processed, unprocessed, commandlist = get_proofscript(request)
            command = commandlist[lineno]
            logging.debug('Sending %d : %s', lineno, command)
            lineno += 1

        # here is where we'll pass it to coqd
        if command:
            try:
                proofst = exec_cmd(command, session)
            except ProofException:
                lineno = lineno - 1 if lineno != 0 else 0

    return render_template('prover/prover.html',
                           prover_url=url_for('editor',
                                              theorem_id=theorem_id),
                           proofst=proofst,
                           processed=processed,
                           unprocessed=unprocessed,
                           lineno=lineno)
