# from subprocess import Popen

from webapp import app

### coqd = Popen(["python", "coqd/connserv.py"])

app.debug = True
app.run()
