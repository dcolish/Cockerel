"""
classes.py
-----------------------------

Controller functions for classes. A class object allows you to add associated
lesson plans.
"""

from flask import (
    g,
    Module,
    redirect,
    render_template,
    request,
    url_for,
    )
from flatland.out.markup import Generator

from util import login_required

from cockerel.models.schema import db, Classes
from .forms.classes import AddEditClassForm

classes = Module(__name__)


@classes.route('/classes', methods=['GET'])
def index():
    """Shows all classes currently in the system"""
    classes = Classes.query.all()
    return render_template("/classes/index.html", classes=classes)


@classes.route('/classes/add', methods=['GET', 'POST'])
@login_required
def add():
    """Users can add classes if they are authenticated"""
    if request.method == 'POST':

        form = AddEditClassForm.from_flat(request.form)
        form.validate()
        class_section = Classes(form['classname'].value,
                                form['description'].value,
                                owner=g.user)
        db.session.add(class_section)
        db.session.commit()
        return redirect(url_for('classes.view',
                        class_id=class_section.id))

    form = AddEditClassForm()
    html = Generator()
    return render_template('classes/add.html',
                           form=form,
                           html=html)


@classes.route('/classes/edit/<int:class_id>', methods=['GET', 'POST'])
@login_required
def edit():
    """Make modifications to a class"""
    if request.method == 'POST':
        form = AddEditClassForm.from_flat(request.form)
        form.validate()
        class_section = Classes(form['classname'].value,
                                form['description'].value,
                                owner=g.user)
        db.session.add(class_section)
        db.session.commit()
        return redirect(url_for('classes.view',
                        class_id=class_section.id))

    form = AddEditClassForm()
    html = Generator()
    return render_template('classes/add.html',
                           form=form,
                           html=html)


@classes.route('/classes/register/<int:class_id>', methods=['GET'])
@login_required
def register(class_id):
    """As a student user, register for access to a class"""
    if class_id and request.method == 'GET':
        section = Classes.query.filter_by(id=class_id).first()
        section.users.append(g.user)
        db.session.commit()
        return redirect(url_for('classes.view',
                                class_id=section.id))


@classes.route('/classes/view/<int:class_id>', methods=['GET'])
def view(class_id):
    """View the lesson plans offered by a specific class. The user must be
    either the admin or registered for that class"""
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
