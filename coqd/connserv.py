"""
Connserv
~~~~~~~~
Server for Coq protocol. Clients can connect and request server sessions based
on a userid and a Coq command serialized into JSON::

  {"command":"", "userid":""}

 They then send commands and receive back JSON of
the schema::

  {'userid': self.userid, 'response': res}

"""
from json import JSONDecoder, JSONEncoder

import logging
from multiprocessing import Pipe

from twisted.internet.protocol import Protocol

from base import CoqProc
from parser.gram import parser

logging.basicConfig(level=logging.DEBUG)


class CoqProtocol(Protocol):
    """
    Implementation of the Coq Protocol which handles connection and
    disconnection of the server and roudtrips to and from the backend.
    """
    class ActiveConn(object):
        """
        Talks to the specific backend instance associated with a userid
        """
        def __init__(self, userid):
            self.userid = userid
            self.here, self.there = Pipe(duplex=True)
            self.proc = CoqProc()
            self.proc.start()
            self.read()
            logging.debug("Coqtop Process started %s", self.proc)

        def read(self):
            """poll results from the coqtop backend"""
            res = None
            self.proc.run(self.there)
            if self.here.poll():
                res = self.here.recv()
                logging.debug("Received content from process")
            return {'userid': self.userid, 'response': res}

        def send(self, data):
            """send results to our coqtop instance"""
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
        """
        Parse data we've recieved and send to proof engine
        Expects JSON will be in the schema {"command":"", "userid":""}
        """
        req_data = JSONDecoder().decode(data)
        logging.debug("Got: %s", req_data)
        command = req_data.get('command')
        userid = req_data.get('userid')
        resp_data = self.handle_command(userid, command)
        resp_data['response'] = self.do_parse(resp_data['response'])
        self.transport.write(JSONEncoder().encode(resp_data))
        self.transport.loseConnection()

    def do_parse(self, output):
        """Parse coqtop results and serialize"""
        logging.debug("Unformatted Output: %s" % output)
        output = ' '.join(output.splitlines())
        result = parser.parse(output)
        return result

    def handle_command(self, userid, command):
        """When a command is received send it to the specific backend for the
        given userid"""
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

        return resp_dict

    def connectionLost(self, reason):
        """When the connection closes log the exit status"""
        if 'ConnectionDone' in ''.join(reason.parents):
            logging.debug("Connection closed cleanly")
        else:
            logging.debug("Connection didn't close correctly")
            raise reason

    def cleanup_session(self, userid):
        """Close out sessions and remove the userid from the tracking table"""
        active_sess = self.active_conns.get(userid)
        if active_sess:
            active_sess.quit()
            del self.active_conns[userid]
