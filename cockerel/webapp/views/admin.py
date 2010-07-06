from flask import (
    g,
    Module,
    redirect,
    render_template,
    request,
    session,
    url_for,
)

from models.schema import db, User

admin = Module(__name__)


@admin.route('/login', methods=['GET', 'POST'])
def login():
    # simple session setting
    # TODO: make this do better auth
    if request.method == 'POST':
        user = User.query.filter_by(username=request.form['username']).first()
        if user.check_password(request.form['password']):
            g.user = user
            set_user()
            if request.args:
                return redirect(request.args.get('next'))
            else:
                return redirect(url_for('frontend.index'))
        else:
            errors = ['Bad password']
            return render_template("login.html", errors=errors)
    return render_template("admin/login.html",
                           **request.args)


@admin.route('/logout', methods=['GET'])
def logout():
    session.pop('username', None)
    return redirect(url_for('frontend.index'))


@admin.route('/signup', methods=['GET', 'POST'])
def signup():
    if request.method == 'POST':
        user = User(request.form['username'],
                   request.form['password'])
        db.session.add(user)
        db.session.commit()
        g.user = user
        check_user()
        return redirect(url_for('frontend.index'))
    return render_template("admin/signup.html")


def check_user():
    g.user = User.query.filter_by(
        username=session.get('username')).first()


def set_user():
    session['username'] = g.user.username


admin.before_app_request(check_user)
