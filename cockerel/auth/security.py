"""
Security
========

Inflate and set the users Identity. Works with `permission.Permissions` since
all roles will be added to an Identity and then checked before routing.
"""

from flask import g, session
from flaskext.principal import Identity


from pdxacm.webapp import principals
from pdxacm.models.schema import User


def check_user():
    g.identity = Identity(User.query.filter_by(
        username=session.get('username')))


@principals.identity_saver
def set_user(identity):
    g.identity = identity
    session['username'] = identity.username
