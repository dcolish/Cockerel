import re
import markdown


def register_modules(app, mod_list):
    for x in mod_list:
        app.register_module(x)


class TheoremLinkExtension(markdown.Extension):

    def __init__(self):
        self.config = {
            'base_url': '/',
            'html_class': 'theorem',
            }

    def extendMarkdown(self, md, md_config):
        self.md = md
        THEOREM_LINK_RE = re.compile(
            r'^[ ]{0,3}(?P<theorem_name>[A-Za-z0-9_-]+):\s*(?P<theorem_body>.*)')
