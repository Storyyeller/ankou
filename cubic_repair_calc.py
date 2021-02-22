import sys
sys.setrecursionlimit(22)

import fixpoint
import grammar_loader


g = grammar_loader.load_from_nimble_json('test.json')
g.pstats()
g.merge_toks()
g.pstats()
g.inline_singleton_rules()
g.pstats()
g.merge_toks()
g.pstats()
g.inline_singleton_rules()
g.pstats()
g.merge_toks()
g.pstats()
g.inline_singleton_rules()
g.pstats()
g.inline_single_use_rules()
g.pstats()
g.inline_left_binops()
g.pstats()
g.split_long_rules()
g.pstats()

import json
TOKMAP = g.tokmap
EOF = 'EOF'
with open('temp.txt', 'w') as f:
    for rn, pset in sorted(g.d.items()):
        f.write('\n{}:'.format(rn) + '\n')
        for prod in sorted(pset):
            s = 'empty' if not prod else ' '.join(prod)
            f.write('  ' + s + '\n')
    f.write('\n\nTOKMAP\n')
    f.write(json.dumps(TOKMAP))

class ChangeTree(object):
    def __init__(self, lhs, mid, rhs):
        self.lhs = lhs
        self.mid = mid
        self.rhs = rhs

        size = 1 if mid is not None else 0
        size += lhs.size if lhs is not None else 0
        size += rhs.size if rhs is not None else 0
        self.size = size

    def flatten(self, out):
        if self.lhs is not None:
            self.lhs.flatten(out)
        if self.mid is not None:
            out.append(self.mid)
        if self.rhs is not None:
            self.rhs.flatten(out)
EMPTY = ChangeTree(None, None, None)

def join(lhs, mid, rhs):
    if mid is None and lhs.size == 0:
        return rhs
    if mid is None and rhs.size == 0:
        return lhs
    return ChangeTree(lhs, mid, rhs)

def parse(src, tokens):
    def parse_sub(cb, args, best):
        rn, start, end = args
        assert 0 <= start <= end <= len(tokens)

        if rn == '':
            if start == end:
                return EMPTY

            hw = (end - start) // 2
            lhs = cb(('', start, start + hw))
            if lhs is None:
                return best
            rhs = cb(('', end - hw, end))
            if rhs is None:
                return best

            if (end - start) % 2:
                tok, tstart, tend = tokens[start + hw]
                mid = 'Delete', tstart, tend
            else:
                mid = None
            res = join(lhs, mid, rhs)
            return best if (best and best.size <= res.size) else res
        elif rn not in g.d:
            assert rn == rn.upper()
            matches = [i for i, (tok, _, _) in enumerate(tokens[start:end]) if tok == rn]
            if not matches:
                if start >= len(tokens):
                    insertpos = len(src)
                else:
                    insertpos = tokens[start][1]

                mid = 'Insert', insertpos, rn
                rhs = cb(('', start, end))
                if rhs is None:
                    return best
                res = join(EMPTY, mid, rhs)
            else:
                found_i = start + matches[0]
                lhs = cb(('', start, found_i))
                if lhs is None:
                    return best
                rhs = cb(('', found_i + 1, end))
                if rhs is None:
                    return best
                res = join(lhs, None, rhs)
            return best if (best and best.size <= res.size) else res
        else:
            for prod in sorted(g.d[rn]):
                if len(prod) <= 1:
                    new_rn = prod[0] if prod else ''
                    new = cb((new_rn, start, end))
                    if new is None:
                        continue
                    if best is None or new.size < best.size:
                        best = new
                else:
                    rn1, rn2 = prod
                    for split_i in range(start, end + 1):
                        lhs = cb((rn1, start, split_i))
                        if lhs is None or (best and best.size <= lhs.size):
                            continue

                        rhs = cb((rn2, split_i, end))
                        if rhs is None:
                            continue

                        new = join(lhs, None, rhs)
                        if best is None or new.size < best.size:
                            best = new
            return best

    return fixpoint.Fixpoint(parse_sub).eval(('^', 0, len(tokens)))

import time
from lexer import lex_file_raw
fname = 'java_corpus/s5.java'
src = open(fname, 'r').read().decode('utf8')
tokens = list(lex_file_raw(src))
print 'num tokens', len(tokens)

time0 = time.time()
optimal = parse(src, tokens)
print 'Found optimal solution score {} in {}'.format(optimal.size, time.time() - time0)
change_list2 = []
optimal.flatten(change_list2)
for change in change_list2[:16]:
    print change
