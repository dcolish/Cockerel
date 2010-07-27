from tests.functional import browser
from tests.pages.home import Page


def test_home_loads():
    browser.open('/')
    page = Page()
    assert 'Cockerel' in page.title
