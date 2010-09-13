from argparse import ArgumentParser
from json import JSONDecoder, JSONEncoder
import readline
import logging
from sys import argv
import telnetlib


def send(command, serialize):
    try:
        tn = telnetlib.Telnet('localhost', 8003)
        tn.write(JSONEncoder().encode(dict(userid=0,
                                           command=command)))
        if serialize:
            proofst = JSONDecoder().decode(tn.read_all())
            proofst = proofst.get('response', None)
        else:
            proofst = tn.read_all()
        print proofst
    except Exception:
        logging.error("Connection to coqd failed")


def options(parser):
    parser.add_argument("--serialize", action="store_true",
                        default=False,
                        help="Serialize output to JSON")
    return parser


def main():
    """
    Setup and run coqd
    """
    parser = ArgumentParser(prog="Coqd", description="Options for Coqd",
                            version="Coqd 0.1")
    parser = options(parser)
    opts = parser.parse_args(argv[1:])

    while True:
        try:
            prompt = raw_input(">>> ")
            send(prompt, opts.serialize)
        except:
            pass

if __name__ == '__main__':
    main()
