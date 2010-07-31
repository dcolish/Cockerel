from alfajor import WebBrowser
from nose import with_setup

from cockerel.webapp import db, app


browser = WebBrowser()
browser.configure_in_scope('default')


def setup():
    app.config['SQLALCHEMY_DATABASE_URI'] = 'sqlite://'
    db.create_all()


def teardown():
    db.session.remove()
    db.drop_all()


def testcase():
    def dec(f):
        return with_setup(setup, teardown)(f)
    return dec

testcase.__test__ = False
