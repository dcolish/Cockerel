"""
Permissions
===========

Will specify what roles or attributes are needed to be held by an Identity for
it to access a resource. The resource can be anything within the application.
However, it should be restricted to page endpoints. Privileges which will be
integrated later will restrict the access to data in a more fine grained manner

"""
from flaskext.principal import (
    identity_loaded,
    Permission,
    RoleNeed,
    UserNeed,
    )


def permission(*roles):
    perm = Permission(RoleNeed('none'))
    for x in roles:
        perm = perm.union(x)
    return perm


class Permissions(dict):
    def __getattr__(self, attr):
        try:
            return self[attr]
        except:
            return super(self, dict).attr

    def __setattr__(self, attr, value):
        self[attr] = value

permissions = Permissions()

permissions.read = Permission(RoleNeed('read'))
permissions.insert = Permission(RoleNeed('insert'))
permissions.modify = Permission(RoleNeed('modify'))
permissions.delete = Permission(RoleNeed('delete'))
permissions.full_access = permission(permissions.delete, permissions.insert,
                                     permissions.modify, permissions.read)


@identity_loaded.connect
def set_owned_by(sender, identity):
    permissions.owned_by = Permission(UserNeed(identity.user))
    permissions.modify_own_content = permission(permissions.owned_by,
                                                permissions.full_access)
