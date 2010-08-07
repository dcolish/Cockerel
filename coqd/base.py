"""
Base
~~~~~
Deals with Coq
"""
from multiprocessing import Process
from pexpect import spawn, EOF


class CoqProc(Process):
    """Handles the shell process conncetion"""
    def start(self):
        """Execs a new child for coqtop"""
        self.process = spawn('coqtop', ['-emacs-U'])

    def run(self, conn):
        """Attempts to connect with the fork and send a command"""
        cmd = ''
        try:
            if conn.poll():
                cmd = conn.recv()
                self.process.send(cmd + "\n")

            self.process.expect('\<\/prompt\>')
            # Strip out the cmd sent from the output
            result = self.process.before[len(cmd):] + self.process.after + " "
            conn.send(result)
        except EOF:
            self.process.close()
            conn.send("Closing Coqtop\n")

    @property
    def alive(self):
        return self.process.isalive()

    def terminate(self, Force=False):
        """Have the child terminate"""
        if Force:
            return self.process.terminate(True)
        else:
            return self.process.terminate(True)
