from flaskext.script import Manager, Server, Shell

from coqd.runner import main as coqd_main
from cockerel.webapp import app, db
from cockerel.models import schema


def _make_context():
    return dict(app=app, db=db, models=schema)


manager = Manager(app)
manager.add_command("shell", Shell(make_context=_make_context))
manager.add_command("runserver", Server())


@manager.command
def initdb():
    db.drop_all()
    db.create_all()


@manager.command
def runcoqd():
    coqd_main()


if __name__ == "__main__":
    manager.run()
