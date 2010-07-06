from flask import (
    Module,
    redirect,
    render_template,
    request,
    url_for,
    )

from webapp.views.util import login_required

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
        section = Classes.query.filter_by(id=class_id).first()
        lesson = Lesson(request.form['lesson_name'],
                        request.form['text'])
        db.session.add(lesson)
        section.lessons.append(lesson)
        db.session.commit()
        return redirect(url_for('classes.view',
                                class_id=section.id))

    return render_template('lessons/add.html',
                           class_id=class_id)


@lessons.route('/lessons/view/<int:lesson_id>')
@login_required
def view(lesson_id):
    lesson = Lesson.query.filter_by(id=lesson_id).first()
    return render_template('lessons/view.html',
                           lesson=lesson)
