from multiprocessing import Process, Pipe
from pexpect import spawn


class CockProc(Process):

    def start(self):
        self.process = spawn('coqtop', ['-emacs-U'])

    def run(self, conn):
        if conn.poll():
            cmd = conn.recv()
            self.process.send(cmd + "\n")
        self.process.expect('\<\/prompt\>')
        result = self.process.before + self.process.after + " "
        conn.send(result)


here, there = Pipe(duplex=True)

proc = CockProc()
proc.start()
proc.run(there)

while True:
    if here.poll():
        res = here.recv()
        command = raw_input(res + " ")
        here.send(command)
    proc.run(there)
