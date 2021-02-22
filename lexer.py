import json
import re

lexes = json.load(open('lexer.json', 'r'))
lex_res = [(re.compile(pat, re.M), name) for pat, name in lexes]

def lex_file_raw(s):
    p = 0
    while p < len(s):
        best = None
        bestlen = 0
        for regex, name in lex_res:
            m = regex.match(s, p)
            if m is None:
                continue

            ml = len(m.group())
            if ml > bestlen:
                best = name
                bestlen = ml

        assert bestlen
        if best is not None:
            yield best, p, p + bestlen
        p += bestlen

# print sorted(name for pat, name in lexes)
