from flaskext.script import Manager, Server, Shell

from coqd.runner import main as coqd_main
from cockerel.webapp import app, new_app, db
from cockerel.models import schema


def _make_context():
    return dict(app=app, db=db, models=schema)


manager = Manager(new_app)
manager.add_command("shell", Shell(make_context=_make_context))
manager.add_command("runserver", Server())
manager.add_option('--serialize',  action="store_true",
                default=False, help="Serialize output to JSON")


@manager.command
def initdb():
    db.drop_all()
    db.create_all()


@manager.option('--serialize',  action="store_true",
                default=False,
                help="Serialize output to JSON")
def runcoqd(serialize):
    coqd_main()


if __name__ == "__main__":
    manager.run()
