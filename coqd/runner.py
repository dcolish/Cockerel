"""
Main entry points for coqd
"""
from argparse import ArgumentParser
from ConfigParser import SafeConfigParser
import logging
from sys import argv

from twisted.internet import reactor
from twisted.internet.protocol import Factory

from connserv import CoqProtocol


class Configurator(SafeConfigParser):
    """Responsible or coqd configuration"""
    def __init__(self, config_files):
        self.conf = SafeConfigParser()
        self.conf.read(config_files)


def options(parser):
    parser.add_argument("--module", dest="modules", action="append",
                        default=[],
                        help="load modules into coqd, more than one "
                        "can be specified",
                        )
    parser.add_argument("--version", action="version", version="%(prog)s 0.1")
    return parser


def main():
    """
    Setup and run coqd
    """
    parser = ArgumentParser(prog="Coqd", description="Options for Coqd")
    parser = options(parser)
    args = parser.parse_args(argv[1:])

    if args.modules:
        # XXX: actual module loading occurs here
        pass

    logging.info("Coq is starting... hold on")

    f = Factory()
    f.protocol = CoqProtocol
    reactor.listenTCP(8003, f)
    reactor.run()

if __name__ == '__main__':
    main()
