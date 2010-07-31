from tests.functional import browser, testcase
from tests.pages.base import Page
from tests.pages.admin import Login, Signup


@testcase()
def test_signup():

    browser.open('/')
    page = Page()
    assert page.offers_signup_link
    page.click_signup_link()

    page = Signup()
    assert page.offers_signup_form
    foo = page.signup_form
    foo.fill(dict(username='yermom', password='foobar'))
    foo.submit()
    assert not page.offers_signup_link


