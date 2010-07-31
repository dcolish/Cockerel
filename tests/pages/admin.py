from tests.functional import browser
from tests.pages.base import Page


class Signup(Page):

    @property
    def offers_signup_form(self):
        return bool(browser.document.cssselect('form#f_signup'))

    @property
    def signup_form(self):
        return browser.document['form#f_signup']


class Login(Page):
    @property
    def offers_login_form(self):
        return bool(browser.document.cssselect('form#f_login'))

    @property
    def login_form(self):
        return browser.document['form#f_login']
