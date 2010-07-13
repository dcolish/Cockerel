from flask import (
    flash,
    Module,
    redirect,
    render_template,
    request,
    url_for,
    )
from flatland.out.markup import Generator

from util import login_required
from .forms.lessons import EditLessonForm
from cockerel.models.schema import db, Classes, Lesson

lessons = Module(__name__)


@lessons.route('/lessons')
@login_required
def index():
    pass


@lessons.route('/lessons/add/<int:class_id>', methods=['GET', 'POST'])
@login_required
def add(class_id):
    if request.method == 'POST':
        form = EditLessonForm.from_flat(request.form)
        form.validate()
        section = Classes.query.filter_by(id=class_id).first()
        lesson = Lesson(lesson_name=form['lesson_name'].value,
                        text=form['text'].value)
        db.session.add(lesson)
        section.lessons.append(lesson)
        db.session.commit()
        flash('Your lesson plan has been successfully added', 'notification')
        return redirect(url_for('classes.view',
                                class_id=section.id))

    form = EditLessonForm()
    gen = Generator()
    return render_template('lessons/add.html',
                           class_id=class_id,
                           form=form,
                           html=gen)


@lessons.route('/lessons/edit/<int:lesson_id>', methods=['GET', 'POST'])
@login_required
# @permissions('admin')
def edit(lesson_id):
    lesson = Lesson.query.filter_by(id=lesson_id).first()
    if request.method == 'POST':
        # XXX: do the edit form processing
        form = EditLessonForm.from_flat(request.form)
        if form.validate():
            lesson.lesson_name = form['lesson_name'].value
            lesson.text = form['text'].value
            db.session.commit()
            return redirect(url_for('lessons.view',
                                    lesson_id=lesson.id))

    form = EditLessonForm.from_flat(lesson.__dict__)

    gen = Generator()
    return render_template('lessons/edit.html',
                           lesson=lesson,
                           form=form,
                           html=gen)


@lessons.route('/lessons/view/<int:lesson_id>')
@login_required
def view(lesson_id):
    lesson = Lesson.query.filter_by(id=lesson_id).first()
    return render_template('lessons/view.html',
                           lesson=lesson)
