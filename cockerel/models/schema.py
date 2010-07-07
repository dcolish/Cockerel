from werkzeug import generate_password_hash, check_password_hash
from webapp import db


user_classes = db.Table('user_classes', db.Model.metadata,
                     db.Column('user_id', db.Integer,
                               db.ForeignKey('users.id')),
                     db.Column('class_id', db.Integer,
                               db.ForeignKey('classes.id')))

lessons_classes = db.Table('lessons_classes', db.Model.metadata,
                           db.Column('lesson_id', db.Integer,
                                     db.ForeignKey('lessons.id')),
                           db.Column('class_id', db.Integer,
                                     db.ForeignKey('classes.id')))


class User(db.Model):
    __tablename__ = 'users'
    id = db.Column(db.Integer, primary_key=True)
    username = db.Column(db.String(80), unique=True)
    pw_hash = db.Column(db.String(80))
    email = db.Column(db.String(80))
    firstname = db.Column(db.String(80))
    lastname = db.Column(db.String(80))

    def __init__(self, username, password):
        self.username = username
        self.set_password(password)

    def set_password(self, password):
        self.pw_hash = generate_password_hash(password)

    def check_password(self, password):
        return check_password_hash(self.pw_hash, password)

    def __repr__(self):
        return '<User %r>' % self.username


class Classes(db.Model):
    __tablename__ = 'classes'
    id = db.Column(db.Integer, primary_key=True)
    classname = db.Column(db.String(80), unique=True)
    description = db.Column(db.String)
    owner_id = db.Column(db.Integer, db.ForeignKey('users.id'))

    owner = db.relationship('User', backref='owns')

    users = db.relationship('User',
                              secondary=user_classes,
                              backref='classes')

    def __init__(self, classname, description, owner):
        self.classname = classname
        self.description = description
        self.owner = owner

    def __repr__(self):
        return '<Class %r>' % self.classname


class Lesson(db.Model):
    __tablename__ = 'lessons'
    id = db.Column(db.Integer, primary_key=True)
    lesson_name = db.Column(db.String(80), unique=True)
    text = db.Column(db.String)

    classes = db.relationship('Classes',
                              secondary=lessons_classes,
                              backref='lessons')

    def __init__(self, lesson_name, text):
        self.lesson_name = lesson_name
        self.text = text

    def __repr__(self):
        return '<Lesson %s>' % self.lesson_name
