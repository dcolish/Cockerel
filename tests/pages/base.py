from tests.functional import browser


class Page(object):

    @property
    def title(self):
        return browser.document['#branding h1'][0].text_content

    @property
    def offers_login_link(self):
        return bool(browser.document.cssselect('#login'))

    @property
    def offers_signup_link(self):
        return bool(browser.document.cssselect('#signup'))

    def click_login_link(self):
        button = browser.document['#login']
        button.click('page')

    def click_signup_link(self):
        button = browser.document['#signup']
        button.click('page')

    def click_submit(self):
        button = browser.document["input[type='submit'][value='login']"][0]
        button.click('page')
