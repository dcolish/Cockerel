from flask import (
    Module,
    redirect,
    render_template,
    request,
    url_for,
    )
from flatland.out.markup import Generator

from webapp.views.util import login_required
from .forms.lessons import AddLessonForm
from models.schema import db, Classes, Lesson

lessons = Module(__name__)


@lessons.route('/lessons')
@login_required
def index():
    pass


@lessons.route('/lessons/add/<int:class_id>', methods=['GET', 'POST'])
@login_required
def add(class_id):
    if request.method == 'POST':
        form = AddLessonForm.from_flat(request.form)
        form.validate()
        section = Classes.query.filter_by(id=class_id).first()
        lesson = Lesson(lesson_name=form['lesson_name'].value,
                        value=form['text'].value)
        db.session.add(lesson)
        section.lessons.append(lesson)
        db.session.commit()
        return redirect(url_for('classes.view',
                                class_id=section.id))

    form = AddLessonForm()
    gen = Generator()
    return render_template('lessons/add.html',
                           class_id=class_id,
                           form=form,
                           gen=gen)


@lessons.route('/lessons/view/<int:lesson_id>')
@login_required
def view(lesson_id):
    lesson = Lesson.query.filter_by(id=lesson_id).first()
    return render_template('lessons/view.html',
                           lesson=lesson)
