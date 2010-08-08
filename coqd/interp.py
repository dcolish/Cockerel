from code import InteractiveConsole
from json import JSONDecoder, JSONEncoder
import readline
import logging
import telnetlib


def send(command):
    try:
        tn = telnetlib.Telnet('localhost', 8003)
        tn.write(JSONEncoder().encode(dict(userid=0,
                                           command=command)))
        proofst = JSONDecoder().decode(tn.read_all())
        proofst = proofst.get('response', None)
        print proofst
    except Exception:
        logging.error("Connection to coqd failed")

while True:
    try:
        prompt = raw_input(">>> ")
        send(prompt)
    except:
        pass
