from multiprocessing import Pipe

from twisted.internet import reactor
from twisted.internet.protocol import Factory, Protocol

from base import CoqProc


class CoqProtocol(Protocol):

    def parse(res):
        

    def connectionMade(self):
        self.here, self.there = Pipe(duplex=True)
        self.proc = CoqProc()
        self.proc.start()
        self.proc.run(self.there)
        foo = self.here.recv()
        self.transport.write(foo)

    def dataReceived(self, data):
        res = ""
        self.here.send(data + " ")
        if not self.proc.alive:
            self.transport.loseConnection()

        self.proc.run(self.there)
        if self.here.poll():
            res = self.here.recv()
            self.parse(res)
        self.transport.write(res)

    def connectionLost(self, reason):
        if self.proc.alive:
            self.proc.terminate()

        self.here.close()

        if 'ConnectionDone' in ''.join(reason.parents):
            print "Connection closed cleanly"
        else:
            print "Connection didn't close correctly"
            raise reason


def main():
    f = Factory()
    f.protocol = CoqProtocol
    reactor.listenTCP(8000, f)
    reactor.run()

if __name__ == '__main__':
    main()
