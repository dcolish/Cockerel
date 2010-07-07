from flask import (
    g,
    Module,
    redirect,
    render_template,
    request,
    session,
    url_for,
)
from flatland.out.markup import Generator

from models.schema import db, User
from .forms.admin import LoginForm, SignupForm

admin = Module(__name__)


@admin.route('/login', methods=['GET', 'POST'])
def login():
    # simple session setting
    # TODO: make this do better auth
    if request.method == 'POST':
        form = LoginForm.from_flat(request.form)
        if form.validate():
            user = User.query.filter_by(
                username=request.form['username']).first()

            if user == None:
                form['username'].add_error(
                    'Username %s not found' % form['username'].value)
                gen = Generator()
                return render_template("admin/login.html", form=form, html=gen)

            if user.check_password(request.form['password']):
                g.user = user
                set_user()
                if request.args:
                    return redirect(request.args.get('next'))
                else:
                    return redirect(url_for('frontend.index'))
        else:
            gen = Generator()
            return render_template("admin/login.html", form=form, html=gen)
    form = LoginForm()
    gen = Generator()
    return render_template("admin/login.html",
                           form=form,
                           html=gen,
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
    form = SignupForm()
    gen = Generator()
    return render_template("admin/signup.html",
                           form=form,
                           html=gen)


def check_user():
    g.user = User.query.filter_by(
        username=session.get('username')).first()


def set_user():
    session['username'] = g.user.username


admin.before_app_request(check_user)
