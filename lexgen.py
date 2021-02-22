import json
import re

IGNORE = 'IGNORE'

class StringRule(object):
    is_regex = False
    def __init__(self, s):
        self.s = s

    def match(self, s, start):
        return len(self.s) if s.startswith(self.s, start) else None

class RegexRule(object):
    is_regex = True
    def __init__(self, s):
        self.s = s
        self.re = re.compile(s)

    def match(self, s, start):
        m = self.re.match(s, start)
        return m and len(m.group())


class Lexer(object):
    def __init__(self):
        self.examples = {}
        self.rules = [] # rule -> tok

    def to_json(self):
        rules = [(r.is_regex, r.s, tok) for r, tok in self.rules]
        return self.examples, rules

    def match(self, s, start):
        best = None
        bestlen = 0
        for rule, name in self.rules:
            m = rule.match(s, start)

            if m is None:
                continue

            if m > bestlen:
                best = name
                bestlen = m
        return bestlen, best

    def lex_file(self, s):
        p = 0
        while p < len(s):
            bestlen, best = self.match(s, p)
            if not bestlen:
                print s[p:p+10]

            assert bestlen
            if best != IGNORE:
                yield best, p, p + bestlen
            p += bestlen

def load_from_json(data):
    examples, rules = data
    lex = Lexer()
    lex.examples.update(examples)
    for is_regex, s, tok in rules:
        rule = RegexRule(s) if is_regex else StringRule(s)
        lex.rules.append((rule, tok))
    return lex


def load_from_lfile(src):
    lex = Lexer()

    lines = [l.strip() for l in src.split('\n') if l and l != '%%']
    for line in lines:
        re_raw, _, name_raw = line.rpartition(' ')
        name = json.loads(name_raw) if name_raw != ';' else IGNORE
        # print name, re_raw, TOKMAP.get(name)

        lex.rules.append((RegexRule(re_raw), name))
        lex.examples.setdefault(name, None)
    return lex



# data = open('../grammars/java7/java.l', 'r').read()
# lex = load_from_lfile(data)

# with open('lexer.json', 'w') as f:
#     json.dump(lex.to_json(), f, sort_keys=True, indent=2, separators=(',', ': '))
