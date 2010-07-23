from code import InteractiveConsole
from json import JSONDecoder, JSONEncoder
import logging
import telnetlib


def fee(command):
    try:
        tn = telnetlib.Telnet('localhost', 8003)
        tn.write(JSONEncoder().encode(dict(userid=0,
                                           command=command)))
        proofst = JSONDecoder().decode(tn.read_all())
        proofst = proofst.get('response', None)
        print proofst
    except Exception:
        logging.error("Connection to coqd failed")


foo = InteractiveConsole()
f = foo.raw_input(">>>")
fee(f)
