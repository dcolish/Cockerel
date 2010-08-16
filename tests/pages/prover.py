from tests.functional import browser
from .base import Page


class ProverPage(Page):

    @property
    def offers_prover(self):
        return browser.document['#prover']
