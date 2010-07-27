from tests.functional import browser


class Page(object):

    @property
    def title(self):
        return browser.document['#branding h1'][0].text_content
