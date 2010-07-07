from flatland import Form, String
from flatland.validation import Present


class AddClassForm(Form):
    name = "addClass"
    classname = String.using(label='Class Name',
                             validators=[Present()])
    description = String.using(label='Description',
                               validators=[Present()])
