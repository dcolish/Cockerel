"""
Runner
~~~~~~
Main entry points for coqd
"""
from argparse import ArgumentParser
# from optparse import OptionParser
from ConfigParser import SafeConfigParser
import logging
from sys import argv

from twisted.internet import reactor
from twisted.internet.protocol import ServerFactory

from connserv import CoqProtocol


class Configurator(SafeConfigParser):
    """Responsible for coqd configuration"""
    def __init__(self, config_files):
        self.conf = SafeConfigParser()
        self.conf.read(config_files)


class CoqFactory(ServerFactory):
    protocol = CoqProtocol

    def __init__(self, modules, serialize):
        self.modules = modules
        self.serialize = serialize


def options(parser):
    parser.add_argument("--module", dest="modules", action="append",
                        default=[],
                        help="load modules into coqd, more than one "
                        "can be specified",
                        )
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

    logging.info("Coq is starting... hold on")
    factory = CoqFactory(opts.modules, opts.serialize)
    reactor.listenTCP(8003, factory)
    reactor.run()
