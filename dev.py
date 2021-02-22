import ast
import json
from collections import namedtuple, defaultdict, Counter
import itertools
import re

from dfa import DFA
from grammar_loader import load_from_nimble_json

###################################################################################
g = load_from_nimble_json('test.json')
# g = Grammar(x)
g.pstats()
g.merge_toks()
g.pstats()
g.inline_singleton_rules()
# print '!'*88
g.merge_toks()
g.pstats()
g.inline_singleton_rules()
g.merge_toks()
g.pstats()
g.inline_singleton_rules()
g.pstats()
g.inline_single_use_rules()
g.pstats()


TOKMAP = g.tokmap
with open('temp.txt', 'w') as f:
    for rn, pset in sorted(g.d.items()):
        f.write('\n{}:'.format(rn) + '\n')
        for prod in sorted(pset):
            s = 'empty' if not prod else ' '.join(prod)
            f.write('  ' + s + '\n')









class DFAGrammar(object):
    def __init__(self, prod_grammar):
        self.d = {
            rn: DFA().from_productions(pset).simplify() for rn, pset in prod_grammar.d.items()
        }

    def pstats(self):
        print 'num rules', len(self.d), 'num prods', sum(len(dfa.map) for dfa in self.d.values())

print 'converting to DFA grammar'
g = DFAGrammar(g)
g.pstats()

for rn, dfa in sorted(g.d.items()):
    g.d[rn] = dfa2 = dfa.remove_left_recursion(rn)
    if dfa2 is not dfa:
        # print 'removed left recursion in', rn
        dfa2.simplify()
g.pstats()

for rn, dfa in sorted(g.d.items()):
    g.d[rn] = dfa2 = dfa.remove_right_recursion(rn)
    if dfa2 is not dfa:
        # print 'removed right recursion in', rn
        dfa2.simplify()
g.pstats()


irreducible = {rn for rn, dfa in g.d.items() if any(rn in d for d in dfa.map.values())}
irreducible.add('^')
# irreducible.add('import_declaration')
# for rn in g.d:
#     if 'annotation' in rn or 'import' in rn or 'package' in rn:
#         irreducible.add(rn)
inline_candidates = set(g.d) - irreducible

num_inlined = 0
while inline_candidates:
    counts = Counter()
    for rn, dfa in g.d.items():
        for d in dfa.map.values():
            for t in d:
                counts[t] += 1

    keys = sorted(((counts[rn] - 1) * (len(g.d[rn].map) - 2), len(g.d[rn].map), rn) for rn in inline_candidates)
    score, _, rn = keys[0]
    # print 'inlining {} with score {}'.format(rn, score)
    inline_candidates.remove(rn)

    dfa = g.d.pop(rn)
    for rn2, dfa2 in g.d.items():
        old = dfa2
        dfa2 = dfa2.inline(rn, dfa)
        if dfa2 is not old:
            # print 'inlined {} into {}'.format(rn, rn2)
            dfa2 = dfa2.simplify()
            dfa2 = dfa2.remove_left_recursion(rn2).simplify()
            dfa2 = dfa2.remove_right_recursion(rn2).simplify()
            g.d[rn2] = dfa2

            if rn2 not in irreducible and any(rn2 in d for d in dfa2.map.values()):
                print '{} is now irreducible'.format(rn2)
                irreducible.add(rn2)
                inline_candidates.remove(rn2)
    num_inlined += 1
    # if num_inlined >= 91:
    #     break

print 'irreducible', ', '.join(sorted(irreducible))
print 'num inlined', num_inlined
g.pstats()

# for rn in sorted(irreducible):
#     dfa = g.d[rn]
#     while set(dfa.map[dfa.initial]) & irreducible:
#         bad = set(dfa.map[dfa.initial]) & irreducible
#         if rn in bad:
#             g.d[rn] = dfa = dfa.remove_left_recursion(rn).simplify()
#         else:
#             rn2 = min(bad)
#             g.d[rn] = dfa = dfa.inline(rn2, g.d[rn2]).simplify()

################################################################################
# trips = defaultdict(set)
# for rn, dfa in g.d.items():
#     for s, d in dfa.map.items():
#         for t, s2 in d.items():
#             trips[t].add((rn, s, s2))
# sets = {rn: frozenset(trips[rn]) for rn in irreducible if rn != '^'}
# pair = None
# for (rn1, set1), (rn2, set2) in itertools.combinations(sets.items(), 2):
#     if set1 <= set2:
#         print rn1, '<=', rn2
#         pair = rn1, rn2

# if pair is not None:
#     rn1, rn2 = pair
#     rn3 = '{}_or_{}'.format(rn1, rn2)
#     assert rn3 not in g.d

#     for rn, s, s2 in sets[rn1]:
#         dfa = g.d[rn]
#         dfa.remove_edge(s, rn1)
#         dfa.remove_edge(s, rn2)
#         dfa.add_edge(s, rn3, s2)

#     temp1 = '---1'
#     temp2 = '---2'
#     dfa = DFA().from_productions([(temp1,), (temp2,)])
#     dfa = dfa.inline(temp1, g.d[rn1])
#     dfa = dfa.inline(temp2, g.d[rn2])

#     del g.d[rn1]
#     g.d[rn3] = dfa.simplify()

#     irreducible.remove(rn1)
#     irreducible.add(rn3)

# g.pstats()

##############################################################################
import itertools
_id_count = itertools.count()
class LazySet(object):
    def __init__(self, *deps):
        self.id = next(_id_count)
        self.vals = set()
        self.deps = list(deps)

    def solve_sub(self, target, visited):
        if self in visited:
            return
        visited.add(self)

        target.update(self.vals)
        for dep in self.deps:
            dep.solve_sub(target, visited)

    def solve(self):
        if self.deps:
            self.solve_sub(self.vals, set())
            self.deps = None
        return self.vals

    def debug(self):
        part1 = ', '.join(sorted(self.vals))
        part2 = ', '.join(str(ls.id) for ls in self.deps)
        parts = [p for p in (part1, part2) if p]
        return '[{}]({})'.format(self.id, ' + '.join(parts))
##############################################################################

first_sets = {rn: LazySet() for rn in g.d}
for rn, dfa in g.d.items():
    fs = first_sets[rn]
    if dfa.initial in dfa.final:
        fs.vals.add('')

    for t, s2 in dfa.map[dfa.initial].items():
        if t in g.d:
            fs.deps.append(first_sets[t])
        else:
            fs.vals.add(t)

print 'first sets:'
for rn, fs in sorted(first_sets.items()):
    vals = set(fs.solve())
    print rn, '' in vals
    if '' in vals:
        assert rn == '^'
        vals.remove('')
    print '  ', ' '.join(sorted(vals))
first_sets = {rn: set(fs.solve()) for rn, fs in first_sets.items()}

##############################################################################

with open('temp2.txt', 'w') as f:
    for rn, dfa in sorted(g.d.items()):
        f.write('\n{}: ({}) -> {}\n'.format(rn, len(dfa.map), dfa.initial))

        for s in sorted(dfa.map):
            transitions = ', '.join(map('{0[0]} -> {0[1]}'.format, sorted(dfa.map[s].items())))
            f.write('  {}{}: {}\n'.format(s, '*' if s in dfa.final else '', transitions))

            temp = []
            for t in dfa.map[s]:
                if t == 'class_or_interface_type' and dfa.map[s].get('array_type') == dfa.map[s][t]:
                    continue
                if t in first_sets:
                    temp.extend(first_sets[t])
                else:
                    temp.append(t)
            temp2 = set(temp)
            if len(temp) > len(temp2):
                bad = sorted(t for t in temp2 if temp.count(t) > 1)
                f.write('  Conflict! {}\n'.format(', '.join(bad)))













# # Merge DFAs
# merged = DFA()
# init_map = {}
# for rn, dfa in sorted(g.d.items()):
#     other_states = sorted(dfa.map)
#     nmap = {os: merged.add_state() for os in other_states}
#     for os in other_states:
#         for t, os2 in dfa.map[os].items():
#             merged.add_edge(nmap[os], t, nmap[os2])
#         if os in dfa.final:
#             merged.final.add(nmap[os])
#     init_map[rn] = nmap[dfa.initial]
# merged.initial = init_map['^']

# print 'merged size', len(merged.map)
# replaced_map = merged.simplify2()
# print 'merged size', len(merged.map)
# init_map = {rn: replaced_map.get(s, s) for rn, s in init_map.items()}


# with open('temp3.txt', 'w') as f:
#     for rn, init in sorted(init_map.items()):
#         f.write('{}: {}\n'.format(rn, init))

#     for s in sorted(merged.map):
#         transitions = ', '.join(map('{0[0]} -> {0[1]}'.format, sorted(merged.map[s].items())))
#         f.write('  {}{}: {}\n'.format(s, '*' if s in merged.final else '', transitions))
#         # stack += sorted(merged.map[s].values(), reverse=True)


# ###################################################################################
# ostates = sorted(merged.map)
# nmap = {os: i for i, os in enumerate(ostates)}
# nmap = {os: os for i, os in enumerate(ostates)}

# start_state = nmap[init_map['^']]
# table = []
# for os in ostates:
#     while len(table) < os:
#         table.append(({}, [], False))

#     d = merged.map[os]
#     normal = {t: nmap[s2] for t, s2 in d.items() if t not in init_map}
#     pushes = sorted((nmap[init_map[t]], nmap[s2]) for t, s2 in d.items() if t in init_map)
#     table.append((normal, pushes, os in merged.final))
# # pop_states = sorted(map(nmap.get, merged.final))

# # print 'nmap', nmap

# with open('table.json', 'w') as f:
#     json.dump((TOKMAP, start_state, table), f, sort_keys=True, indent=2, separators=(',', ': '))


