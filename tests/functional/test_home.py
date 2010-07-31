from tests.functional import browser, testcase
from tests.pages.base import Page


@testcase()
def test_home_loads():
    browser.open('/')
    page = Page()
    assert 'Cockerel' in page.title

    assert page.offers_signup_link
    assert page.offers_login_link
