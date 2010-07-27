"""
Main entry points for coqd
"""
# from argparse import ArgumentParser
from optparse import OptionParser
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
    parser.add_option("--module", dest="modules", action="append",
                        default=[],
                        help="load modules into coqd, more than one "
                        "can be specified",
                        )

    return parser


def main():
    """
    Setup and run coqd
    """
    parser = OptionParser(prog="Coqd", description="Options for Coqd",
                          version="Coqd 0.1")
    parser = options(parser)
    opts, args = parser.parse_args(argv[1:])

    if opts.modules:
        # XXX: actual module loading occurs here
        pass

    logging.info("Coq is starting... hold on")

    f = Factory()
    f.protocol = CoqProtocol
    reactor.listenTCP(8003, f)
    reactor.run()

if __name__ == '__main__':
    main()
