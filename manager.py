from functools import partial
from flaskext.script import Manager, Server, Shell
from werkzeug import create_environ

from coqd.runner import main as coqd_main
from cockerel.webapp import app
from cockerel.utilities import new_app
from cockerel.models import db, schema


def _make_context():
    return dict(app=new_app(app), db=db, models=schema)


manager = Manager(partial(new_app, app))
manager.add_command("shell", Shell(make_context=_make_context))
manager.add_command("runserver", Server())
manager.add_option('--serialize',  action="store_true",
                default=False, help="Serialize output to JSON")


@manager.command
def initdb():
    # A request_context is required to use these helper functions
    with new_app(app).request_context(create_environ()):
        db.drop_all()
        db.create_all()


@manager.option("--module", dest="modules", action="append",
                default=[],
                help="load modules into coqd, more than one "
                "can be specified",
                )
@manager.option('--serialize',  action="store_true",
                default=False,
                help="Serialize output to JSON")
def runcoqd(modules, serialize):
    coqd_main(modules, serialize)


if __name__ == "__main__":
    manager.run()
