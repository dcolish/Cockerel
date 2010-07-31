from tests.functional import browser, testcase
from tests.pages.base import Page
from tests.pages.admin import Login


@testcase()
def test_login():
    browser.open('/')
    page = Page()
    assert page.offers_login_link
    page.click_login_link()
    page = Login()
    assert page.offers_login_form
    login = page.login_form
    login.fill(dict(username='test',
                    password='user'))
