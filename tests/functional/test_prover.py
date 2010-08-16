from tests.pages.admin import Login
from tests.pages.prover import ProverPage
from tests.functional import browser, testcase


@testcase()
def test_prover_requires_login():
    browser.open('/prover')
    page = Login()
    assert page.offers_login_form
    login = page.login_form
    login.fill(dict(username='test',
                    password='user'))
    page.click_submit()
    page = ProverPage()
    assert page.offers_prover
