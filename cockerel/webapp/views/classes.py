from flask import (
    Module,
    redirect,
    render_template,
    request,
    url_for,
    )

from webapp.views.util import login_required

from models.schema import db, Classes

classes = Module(__name__)


@classes.route('/classes', methods=['GET'])
def index():
    classes = Classes.query.all()
    return render_template("classes/index.html", classes=classes)


@classes.route('/classes/add', methods=['GET', 'POST'])
@login_required
def add():
    if request.method == 'POST':
        class_section = Classes(request.form['classname'],
                                request.form['description'])
        db.session.add(class_section)
        db.session.commit()
        return redirect(url_for('classes.view',
                        class_id=class_section.id))

    return render_template('classes/add.html')


@classes.route('/classes/view/<int:class_id>', methods=['GET'])
def view(class_id):
    section = Classes.query.filter_by(id=class_id).first()
    return render_template('classes/view.html', class_section=section)
