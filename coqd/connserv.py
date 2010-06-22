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

        def quit(self):
            if self.proc.alive:
                return self.proc.terminate(True)

    active_conns = {}

    def dataReceived(self, data):
        req_data = JSONDecoder().decode(data)
        logging.debug("Got: %s", req_data)
        command = req_data.get('command')
        userid = req_data.get('userid')

        resp_data = self.process_command(userid, command)
        self.transport.write(resp_data)
        self.transport.loseConnection()

    def process_command(self, userid, command):
        if not command:
            resp_dict = {'userid': userid,
                         'response': ''}
        elif 'quit' == command:
            self.cleanup_session(userid)
            resp_dict = {'userid': userid,
                         'response': 'Exited'}
        else:
            active_sess = self.active_conns.get(userid)

            if not active_sess:
                active_sess = self.ActiveConn(userid)
                self.active_conns.update({active_sess.userid: active_sess})

            if not active_sess.send(command):
                logging.error("Command could not be sent")
                self.cleanup_session(userid)

            resp_dict = active_sess.read()

        return JSONEncoder().encode(resp_dict)

    def connectionLost(self, reason):
        if 'ConnectionDone' in ''.join(reason.parents):
            logging.debug("Connection closed cleanly")
        else:
            logging.debug("Connection didn't close correctly")
            raise reason

    def cleanup_session(self, userid):
        active_sess = self.active_conns.get(userid)
        if active_sess:
            active_sess.quit()
            del self.active_conns[userid]


def main():
    f = Factory()
    f.protocol = CoqProtocol
    reactor.listenTCP(8001, f)
    reactor.run()

if __name__ == '__main__':
    main()
