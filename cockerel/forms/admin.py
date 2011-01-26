from flatland import Form, String
from flatland.validation import IsEmail, Present, LengthBetween, ValuesEqual


class LoginForm(Form):
    username = String.using(label='Username',
                            validators=[Present()])
    password = String.using(label='Password',
                            validators=[Present()])


class SignupForm(Form):
    username = String.using(label='Username',
                            validators=[Present()])
    password = String.using(
        label='Password',
        validators=[
            Present(),
            LengthBetween(5, 25),
            ValuesEqual('.', '../confirmPassword')])
    confirmPassword = String.using(label='Confirm Password',
                            validators=[Present()])
    email = String.using(label='Email',
                         validators=[Present(), IsEmail()])
    firstname = String.using(label='First Name',
                             validators=[Present()])
    lastname = String.using(label='Last Name',
                            validators=[Present()])
    output_schema = ['username', 'password', 'confirmPassword',
                     'email', 'firstname', 'lastname']
