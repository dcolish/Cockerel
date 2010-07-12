from pprint import PrettyPrinter

from coqd.parser.gram import parser
from json import JSONEncoder

from fixtures.general import proof_responses


pp = PrettyPrinter(indent=4)


def do_parse(s):
    s = ' '.join(s.splitlines())

    assert parser.parse(s)


def test_parsing():
    s = proof_responses

    for x in s:
        do_parse(x)
