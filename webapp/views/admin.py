from flask import (
    Module,
    redirect,
    request,
    session,
    url_for,
)

admin = Module(__name__)


@admin.route('/login', methods=['GET', 'POST'])
def login():
    # simple session setting
    # TODO: make this actually do auth
    if request.method == 'POST':
        session['username'] = request.form['username']
        return redirect(url_for('frontend.index'))
    return '''
        <form action="" method="post">
            <p><input type=text name=username>
            <p><input type=submit value=Login>
        </form>
    '''


@admin.route('/logout', methods=['GET'])
def logout():
    session.pop('username', None)
    return redirect(url_for('index'))


@admin.route('/signup', methods=['GET', 'POST'])
def signup():
    # TODO: add the ability to insert new users into db
    pass
