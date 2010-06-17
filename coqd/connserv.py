from json import JSONDecoder, JSONEncoder

import logging
from multiprocessing import Pipe

from twisted.internet import reactor
from twisted.internet.protocol import Factory, Protocol

from base import CoqProc

logging.basicConfig(level=logging.DEBUG)


class CoqProtocol(Protocol):

    class ActiveConn(object):

        def __init__(self, userid):
            self.userid = userid
            self.here, self.there = Pipe(duplex=True)
            self.proc = CoqProc()
            self.proc.start()
            self.read()
            logging.debug("Coqtop Process started %s", self.proc)

        def read(self):
            res = None
            self.proc.run(self.there)
            if self.here.poll():
                res = self.here.recv()
                logging.debug("Received content from process")
            return {'userid': self.userid, 'response': res}

        def send(self, data):
            if self.proc.alive:
                logging.debug("sending stuff")
                self.here.send(data + " ")
                return True
            else:
                return False

    active_conns = {}

    def dataReceived(self, data):
        req_data = JSONDecoder().decode(data)
        logging.debug("Got: %s", req_data)
        if not req_data.get('command'):
            return JSONEncoder().encode({'userid': req_data.get('userid'),
                                         'response': ''})

        active_sess = self.active_conns.get(req_data.get('userid'))

        if not active_sess:
            userid = req_data.get('userid')
            active_sess = self.ActiveConn(userid)
            self.active_conns.update({active_sess.userid: active_sess})


        if not active_sess.send(req_data.get('command')):
            self.transport.loseConnection()


        resp_data = JSONEncoder().encode(active_sess.read())
        self.transport.write(resp_data)
        self.transport.loseConnection()

    def connectionLost(self, reason):
        if 'ConnectionDone' in ''.join(reason.parents):
            logging.debug("Connection closed cleanly")
        else:
            logging.debug("Connection didn't close correctly")
            raise reason


def main():
    f = Factory()
    f.protocol = CoqProtocol
    reactor.listenTCP(8000, f)
    reactor.run()

if __name__ == '__main__':
    main()
