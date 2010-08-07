"""
Prover Extension for Python-Markdown
=============================================

Added parsing of Theorems to Python-Markdown.

A simple example:

  <<<
  Goal True -> True.
  >>>
"""
from urllib import urlencode
import re
import markdown

from sqlalchemy.orm.exc import NoResultFound

from cockerel.webapp import db
from cockerel.models.schema import Theorem
from .prover import hash_theorem


class ProverExtension(markdown.Extension):
    """ Add definition lists to Markdown. """
    def extendMarkdown(self, md, md_globals):
        """ Add an instance of ProverPreprocessor to Markdown. """
        md.preprocessors.add('prover_block',
                             ProverPreprocessor(md),
                             '_begin')
        md.registerExtension(self)


class ProverPreprocessor(markdown.preprocessors.Preprocessor):
    """ Process Theorem. """

    RE = re.compile(r'(?P<begin>^<{3,})[ ]*\n(?P<theorem>.*?)'
                    '(?P<end>^>{3,})[ ]*$',
                    re.MULTILINE | re.DOTALL)
    WRAP = """
<a class="proofscript" href="/prover?{url}"><pre>{proof}</pre></a>"""

    def __init__(self, md):
        markdown.preprocessors.Preprocessor.__init__(self, md)

    def run(self, lines):
        text = "\n".join(lines)
        while 1:
            m = self.RE.search(text)
            if m:
                hash_value = hash_theorem(m.group('theorem'))
                try:
                    theorem = Theorem.query.filter_by(
                        hash_value=hash_value).one()
                except NoResultFound:
                    theorem = Theorem(text=m.group('theorem'),
                                      hash_value=hash_value)
                    db.session.add(theorem)
                    db.session.commit()
                proof = self.WRAP.format(
                    url=urlencode(dict(theorem=theorem.id)),
                    proof=self._escape(theorem.text))

                placeholder = self.markdown.htmlStash.store(proof, safe=True)
                text = '%s\n%s\n%s' % (text[:m.start()], placeholder,
                                      text[m.end():])
            else:
                break
        return text.split("\n")

    def _escape(self, txt):
        """ basic html escaping """
        txt = txt.replace('&', '&amp;')
        txt = txt.replace('<', '&lt;')
        txt = txt.replace('>', '&gt;')
        txt = txt.replace('"', '&quot;')
        return txt
