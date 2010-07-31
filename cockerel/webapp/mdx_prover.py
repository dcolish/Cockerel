"""
Prover Extension for Python-Markdown
=============================================

Added parsing of Theorems to Python-Markdown.

A simple example:

  <<<
  Goal True -> True.
  >>>
"""

import re
import markdown


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

    RE = re.compile(r'(?P<begin>^<{3,})[ ]*\n(?P<proofscript>.*?)'
                    '(?P<end>^>{3,})[ ]*$',
                    re.MULTILINE | re.DOTALL)
    WRAP = """<a class="proofscript" href="/prover"><pre>%s</pre></a>"""

    def __init__(self, md):
        markdown.preprocessors.Preprocessor.__init__(self, md)

    def run(self, lines):
        """ Match and store Fenced Code Blocks in the HtmlStash."""

        text = "\n".join(lines)
        while 1:
            m = self.RE.search(text)
            if m:
                proof = self.WRAP % (self._escape(m.group('proofscript')))

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
