import ast
from collections import namedtuple, defaultdict, Counter
import json
import re

import lexgen

def parse_indented(src):
    root = []
    stack = [(0, root)]

    for orig_line in src.split('\n'):
        line = orig_line.lstrip()
        if line.startswith('#') or not line.strip():
            continue

        indent = len(orig_line) - len(line)
        if indent > stack[-1][0]:
            last = stack[-1][1][-1]
            assert not last[1]
            stack.append((indent, last[1]))

        while indent < stack[-1][0]:
            stack.pop()

        stack[-1][1].append((line, []))
    return root




def load_from_nimble_json(fname):
    x = json.load(open(fname, 'r'), object_hook=lambda d: namedtuple('X', d.keys())(*d.values()))
    for i in range(len(x.rule_names)):
        if x.rule_names[i] is None:
            x.rule_names[i] = '_R{}'.format(i)
    for i in range(len(x.token_names)):
        if x.token_names[i] is None:
            x.token_names[i] = '_T{}'.format(i)

    g = Grammar()
    for ri, pids in enumerate(x.rules_prods):
        rn = str(x.rule_names[ri])
        g.d[rn] = new_prod_set = set()
        for pi in pids:
            prod = x.prods[pi]
            temp = []
            for tt in prod:
                if getattr(tt, 'Token', None) is not None:
                    temp.append(x.token_names[tt.Token])
                else:
                    temp.append(x.rule_names[tt.Rule])
            new_prod_set.add(tuple(map(str, temp)))
            # if 'type_argument' in rn or 'type_parameter' in rn:
            #     new_prod_set.clear()
            #     new_prod_set.add(('LOL',))
    g.prune_unreachable()
    return g

class RuleDef(object):
    def __init__(self, name, params):
        self.name = name
        self.params = params
        self.prods = []

    def split(self):
        param = self.params[0]
        assert re.match(r'\A[a-z]\w*\Z', param)
        colpar = ':{}'.format(param)
        colpareq = ':{}='.format(param)

        fruledef = RuleDef(self.name, self.params[1:])
        truledef = RuleDef(self.name + colpar, self.params[1:])
        for conditions, parts in self.prods:
            tparts = [s.replace(colpareq, colpar) for s in parts]
            fparts = [s.replace(colpareq, '') for s in parts]

            if param in conditions:
                conditions2 = [v for v in conditions if v != param]
                fruledef.prods.append((conditions2, fparts))
            else:
                fruledef.prods.append((conditions, fparts))
                truledef.prods.append((conditions, tparts))
        return fruledef, truledef

def load_from_text(fname):
    src = open(fname, 'r').read()
    indent_tree = parse_indented(src)


    lex = lexgen.Lexer()
    tok_rules = []
    ruledefs = []

    for line, children in indent_tree:
        if '=' in line:
            tok_name, _, rhs = line.partition('=')
            tok_name = tok_name.strip()
            rhs = rhs.strip()
            assert tok_name == tok_name.upper()

            example = priority = None
            is_regex = rhs.startswith('r')
            pattern = ast.literal_eval(rhs)
            assert isinstance(pattern, str)
            if not is_regex:
                example = pattern

            for line, children2 in children:
                assert not children2
                field, _, rhs = line.strip().partition(' ')
                rhs = ast.literal_eval(rhs)
                if field == 'example':
                    example = rhs
                elif field == 'priority':
                    priority = rhs
                else:
                    assert 0

            rule = lexgen.RegexRule(pattern) if is_regex else lexgen.StringRule(pattern)
            tok_rules.append((priority or 0, len(tok_rules), rule, tok_name))
            if example is not None:
                lex.examples[tok_name] = example
            # elif tok_name != 'IGNORE':
            #     lex.examples.setdefault(tok_name, None)
        else:
            params = line.rstrip(':').split(':')
            name = params.pop(0)
            current_rule = RuleDef(name, params)
            ruledefs.append(current_rule)

            for line, children2 in children:
                assert not children2
                toks = line.strip().split()
                conditions = []
                while toks[-1].startswith('!'):
                    conditions.append(toks.pop()[1:])

                if toks[-1] == '-':
                    toks.pop()
                current_rule.prods.append((conditions, toks))



    for _, _, rule, tok_name in sorted(tok_rules):
        lex.rules.append((rule, tok_name))
        if tok_name != 'IGNORE':
            lex.examples.setdefault(tok_name, None)

    terms = set()
    rules = []
    while ruledefs:
        rdef = ruledefs.pop()
        if rdef.params:
            ruledefs.extend(rdef.split())
        else:
            prods = [tuple(prod) for (conditions, prod) in rdef.prods]
            rules.append((rdef.name, prods))
            for prod in prods:
                terms.update(prod)

    rulenames = {rn for rn, _ in rules}
    assert len(rulenames) == len(rules)

    tokens = terms - rulenames
    print '{} nonterms, {} tokens'.format(len(rulenames), len(tokens))
    print ' '.join(sorted(tokens))
    print ' '.join(sorted(tokens - set(lex.examples)))
    assert all(t.upper() == t for t in tokens)


    for tok in tokens:
        assert lex.examples.get(tok), 'missing example for token ' + tok


    g = Grammar()
    for rn, rlist in rules:
        g.d[rn] = set(rlist)
    g.prune_unreachable()
    return lex, g


class Grammar(object):
    def __init__(self, tokmap=None, d=None):
        self.tokmap = tokmap or {}
        self.d = d or {} # term -> set(tuple(term))

    def clone(self):
        d = {rn: prods.copy() for rn, prods in self.d.items()}
        return Grammar(self.tokmap.copy(), d=d)

    def pstats(self):
        print 'num rules', len(self.d), 'num prods', sum(map(len, self.d.values()))

    def inline_singleton_rules(self):
        old_size = len(self.d)
        for rn in sorted(self.d):
            if len(self.d[rn]) != 1 or rn == '^':
                continue

            myprod = min(self.d[rn])
            if rn in myprod:
                continue

            del self.d[rn]
            for rn2, pset in self.d.items():
                pset2 = set()
                for prod in pset:
                    temp = []
                    for term in prod:
                        if term == rn:
                            temp.extend(myprod)
                        else:
                            temp.append(term)
                    assert rn not in temp
                    pset2.add(tuple(temp))
                self.d[rn2] = pset2
        return len(self.d) < old_size

    def inline_single_use_rules(self):
        old_size = len(self.d)
        uses = defaultdict(set)

        for rn, pset in self.d.items():
            for prod in pset:
                for i, t in enumerate(prod):
                    if t not in self.d:
                        continue
                    uses[t].add((rn, prod, i))
                    # assert prod[i] == t

        singletons = {rn for rn, useset in uses.items() if len(useset) <= 1}

        for rn in singletons:
            useset = uses[rn]
            assert len(useset) == 1

            rn2, prod, i = min(useset)
            # Don't inline if the target contains multiple nonterminals
            if sum(1 for t in prod if t in self.d) > 1:
                continue

            lhs = prod[:i]
            rhs = prod[i+1:]
            assert prod[i] == rn
            assert rn2 != rn
            # print 'inlining', rn2, prod, i

            prods2 = self.d[rn2]
            prods2.remove(prod)


            for sub_prod in self.d[rn]:
                new_prod = lhs + sub_prod + rhs
                # Update the use map
                for i, t in enumerate(sub_prod):
                    if t not in self.d:
                        continue
                    uses[t].remove((rn, sub_prod, i))
                    uses[t].add((rn2, new_prod, i + len(lhs)))
                    # print '  update uses', t, (rn, sub_prod, i), (rn2, new_prod, i + len(lhs))
                    assert new_prod[i + len(lhs)] == t
                prods2.add(new_prod)
                # print '  added', new_prod
            del self.d[rn]

        return len(self.d) < old_size

    def merge_toks(self):
        allterms = set()
        for pset in self.d.values():
            for prod in pset:
                allterms.update(prod)

        tokens = allterms - set(self.d)
        # print 'num tokens', len(tokens)

        tprods = {t: set() for t in tokens}
        DUMMY = ''
        assert DUMMY not in allterms

        for rn, pset in self.d.items():
            for prod in pset:
                for tok in set(prod) & tokens:
                    replaced = tuple(DUMMY if t == tok else t for t in prod)
                    tprods[tok].add((rn,) + replaced)


        keys = {}
        newmap = {}
        for tok, tpset in sorted(tprods.items()):
            key = tuple(sorted(tpset))
            # print tok, '::', key

            master = keys.setdefault(key, tok)
            if master != tok:
                newmap[tok] = master
                self.tokmap[tok] = master
                for k, v in self.tokmap.items():
                    if v == tok:
                        self.tokmap[k] = master


        if not newmap:
            return False
        print 'tokens {} -> {}'.format(len(tokens), len(tokens) - len(newmap))
        for k, v in sorted(newmap.items()):
            print '  {} -> {}'.format(k, v)

        for rn, pset in self.d.items():
            pset2 = set()
            for prod in pset:
                prod2 = tuple(newmap.get(t, t) for t in prod)
                pset2.add(prod2)
            self.d[rn] = pset2
        return True

    def inline_left_binops(self):
        # todo, check for bugs
        left_count = 0
        right_count = 0
        candidates = {}
        for rn, pset in self.d.items():
            temp = {p for p in pset if rn not in p}
            assert temp
            if len(temp) > 1:
                continue

            base_prod = min(temp)
            if len(base_prod) != 1 or base_prod[0] not in self.d:
                continue
            base = base_prod[0]

            pset = pset - temp
            if not pset or any(len(p) < 2 for p in pset):
                continue

            left_ops = []
            right_ops = []
            for prod in pset:
                mid = prod[1:-1]
                if rn in mid or base in mid:
                    break

                if prod[0] == rn and prod[-1] == base:
                    left_ops.append(mid)
                elif prod[0] == base and prod[-1] == rn:
                    right_ops.append(mid)

            if len(left_ops) == len(pset):
                candidates[rn] = base, left_ops
                left_count += 1
            elif len(right_ops) == len(pset):
                candidates[rn] = base, right_ops
                right_count += 1

        print 'binop candidates: left {} right {}'.format(left_count, right_count)
        inlined_count = 0
        for rn, (base, ops) in candidates.items():
            if base not in candidates:
                continue

            original_base = base
            ops = set(ops)
            while base in candidates:
                base2, ops2 = candidates[base]
                if any(base2 in op for op in ops):
                    break
                if any(rn in op for op in ops2):
                    break
                base = base2
                ops.update(ops2)

            assert not any(base in op for op in ops)
            assert not any(rn in op for op in ops)
            if base == original_base:
                continue

            print 'inlined into', rn
            pset2 = set()
            pset2.add((base,))
            for op in ops:
                pset2.add((rn,) + op + (base,))
            self.d[rn] = pset2
            inlined_count += 1

        if inlined_count:
            print 'inlined', inlined_count
            self.prune_unreachable()
        return inlined_count > 0

    def prune_unreachable(self):
        reached = set()
        stack = ['^']
        while stack:
            rn = stack.pop()
            if rn in reached:
                continue
            reached.add(rn)

            for prod in self.d[rn]:
                for t in prod:
                    if t in self.d and t not in reached:
                        stack.append(t)
        self.d = {rn: pset for rn, pset in self.d.items() if rn in reached}

    def right_to_left_recursion(self):
        count = 0
        for rn, prods in self.d.items():
            if any(rn in prod[:-1] for prod in prods):
                continue

            right_rules = [prod for prod in prods if prod and prod[-1] == rn]
            simple_rules = [prod for prod in prods if rn not in prod]
            assert len(right_rules) + len(simple_rules) == len(prods)
            if not right_rules:
                continue

            rn2 = rn + "'"
            new_prods = {(rn2,) + p for p in simple_rules}
            new_prods2 = {(rn2,) + p[:-1] for p in right_rules}
            new_prods2.add(())

            self.d[rn] = new_prods
            self.d[rn2] = new_prods2
            count += 1
        if count:
            print 'fixed right recursion', count


    # Unused
    def split_long_rules(self):
        original_rule_names = set(self.d)
        pending_rules = list(self.d)

        def make_rule(prod):
            if len(prod) <= 1:
                return prod

            rn = '-'.join(prod).lower()
            assert rn not in original_rule_names
            if rn not in self.d:
                self.d[rn] = {prod}
                pending_rules.append(rn)
            return (rn,)

        while pending_rules:
            rn = pending_rules.pop()
            prods = self.d[rn]

            bad_prods = [prod for prod in prods if len(prod) > 2]
            for prod in bad_prods:
                mid = len(prod) // 2
                lhs, rhs = prod[:mid], prod[mid:]

                prods.remove(prod)
                prods.add(make_rule(lhs) + make_rule(rhs))











