from multiprocessing import Process
from pexpect import spawn, EOF


class CoqProc(Process):

    def start(self):
        self.process = spawn('coqtop', ['-emacs-U'])

    def run(self, conn):
        try:
            if conn.poll():
                cmd = conn.recv()
                self.process.send(cmd + "\n")

            self.process.expect('\<\/prompt\>')
            result = self.process.before + self.process.after + " "

            conn.send(result)
        except EOF:
            self.process.close()
            conn.send("Closing Coqtop\n")

    @property
    def alive(self):
        return self.process.isalive()
