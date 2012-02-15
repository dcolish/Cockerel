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


def main(modules, serialize):
    """
    Setup and run coqd
    """
    logging.info("Coq is starting... hold on")
    factory = CoqFactory(modules, serialize)
    reactor.listenTCP(8003, factory)
    reactor.run()

