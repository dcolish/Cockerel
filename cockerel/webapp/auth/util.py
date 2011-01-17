from functools import wraps
from flask import flash, g, request, redirect, url_for


def login_required(f):
    @wraps(f)
    def decorated_function(*args, **kwargs):
        if g.user is None:
            return redirect(url_for('admin.login', next=request.url))
        return f(*args, **kwargs)
    return decorated_function


def permissions(f, permissions):
    @wraps(f)
    def decorated_function(*args, **kwargs):
        if g.user is None:
            return redirect(url_for('admin.login', next=request.url))
        for perm in permissions:
            if perm in g.user.permissions:
                continue
            else:
                flash("You don't have permission to do that", "error")
                return redirect(url_for(request.referrer))
        return f(*args, **kwargs)
    return decorated_function



# def registration_required(f):
#     @wraps(f)
#     def decorated_function(*args, **kwargs):
#         if g.user is None:
#             return redirect(url_for('admin.login', next=request.url))
#         elif g.user in
