from flatland import Form, String
from flatland.validation import Present


# class AddLessonForm(Form):
#     lesson_name = String.using(label='Lesson Name',
#                                validators=[Present()])
#     text = String.using(label='Text',
#                         validators=[Present()])


class EditLessonForm(Form):
    lesson_name = String.using(label='Lesson Name',
                               validators=[Present()])
    text = String.using(label='Text',
                        validators=[Present()])
