from werkzeug import generate_password_hash, check_password_hash
from webapp import db


class User(db.Model):
    __tablename__ = 'users'
    username = db.Column(db.String(80), primary_key=True)
    pw_hash = db.Column(db.String(80))

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
    id = db.Column('class_id', db.Integer, primary_key=True)
    classname = db.Column(db.String(80), unique=True)
    description = db.Column(db.String)

    def __init__(self, classname, description):
        self.classname = classname
        self.description = description

    def __repr(self):
        return '<Class %r>' % self.classname
