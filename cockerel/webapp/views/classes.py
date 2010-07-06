from flask import (
    g,
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
        class_section = Classes(classname=request.form['classname'],
                                description=request.form['description'],
                                owner=g.user)
        db.session.add(class_section)
        db.session.commit()
        return redirect(url_for('classes.view',
                        class_id=class_section.id))

    return render_template('classes/add.html')


@classes.route('/classes/register/<int:class_id>', methods=['GET'])
@login_required
def register(class_id):
    if class_id and request.method == 'GET':
        section = Classes.query.filter_by(id=class_id).first()
        section.users.append(g.user)
        db.session.commit()
        return redirect(url_for('classes.view',
                                class_id=section.id))


@classes.route('/classes/view/<int:class_id>', methods=['GET'])
def view(class_id):
    section = Classes.query.filter_by(id=class_id).first()
    lessons = section.lessons
    if g.user in section.users:
        admin = False
        registered = True
        lessons = section.lessons
    elif section.owner == g.user:
        admin = registered = True
    else:
        admin = registered = False

    return render_template('classes/view.html',
                           admin=admin,
                           class_section=section,
                           lessons=lessons,
                           registered=registered)
