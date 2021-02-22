import ast
import json
from collections import namedtuple, defaultdict, Counter
import itertools
import re
import time

import grammar_loader
import lexgen
import lrgraph4




_id_count = itertools.count()
class LazySet(object):
    def __init__(self, item=None):
        self.id = next(_id_count)
        self.vals = set()
        self.deps = []

        self.item = item
        self.solved = None

    def solve_sub(self, outmap, visited, expl_stack):
        if self in visited:
            return
        visited.add(self)

        if self.item is not None:
            expl_stack = expl_stack + (self.item,)
        if self.solved is not None:
            for v, expls in self.solved.items():
                if v not in outmap:
                    outmap[v] = expl_stack + expls
            return

        for v in self.vals:
            if v not in outmap:
                outmap[v] = expl_stack
        for dep in self.deps:
            dep.solve_sub(outmap, visited, expl_stack)

    def solve(self):
        if self.solved is None:
            result = {}
            self.solve_sub(result, set(), ())
            self.solved = result
        return self.solved

    def debug(self):
        part1 = ', '.join(sorted(self.vals))
        part2 = ', '.join(str(ls.id) for ls in self.deps)
        parts = [p for p in (part1, part2) if p]
        return '[{}]({})'.format(self.id, ' + '.join(parts))



Rule = namedtuple('Rule', 'lhs prod')
Item = namedtuple('Item', 'rule pos tok advance')

def make_item(rule, pos):
    prod = rule.prod
    assert pos <= len(prod)
    if pos == len(prod):
        return Item(rule, pos, None, None)
    return Item(rule, pos, prod[pos], make_item(rule, pos+1))

def print_item(item):
    prod = item.rule.prod
    rhs = ' '.join(prod[:item.pos]) + ' *' + ' '.join(prod[item.pos:])
    return ('{}: {}'.format(item.rule.lhs, rhs))



class ItemSet(object):
    def __init__(self, num, items):
        self.id = num
        self.items = items
        self.edges = {} # term -> (pairs, iset2)



# g2 = grammar_loader.load_from_nimble_json('test.json')
# data = open('../grammars/java7/java.l', 'r').read()
# lex = lexgen.load_from_lfile(data)

# tokens_src = open('tokens.java', 'r').read()
# for example in tokens_src.split():
#     mlen, tok = lex.match(example + ' ', 0)
#     print 'match', example, mlen, tok
#     if tok is not None:
#         assert 0 < mlen <= len(example)
#         if not lex.examples.get(tok):
#             lex.examples[tok] = example[:mlen]

# with open('java.ankou', 'w') as f:
#     for rn, prods in sorted(g.d.items()):
#         f.write('{}:\n'.format(rn))
#         for prod in sorted(prods):
#             if not prod:
#                 f.write('    -\n')
#             else:
#                 f.write('    {}\n'.format(' '.join(prod)))
#         f.write('\n')
#     f.write('\n')
#     seen = {lexgen.IGNORE}
#     for rule, tok in lex.rules:
#         if rule.is_regex:
#             f.write('{} = r{}\n'.format(tok, repr(rule.s).replace('\\\\', '\\')))
#         else:
#             f.write('{} = {!r}\n'.format(tok, rule.s))
#         if tok not in seen and lex.examples.get(tok):
#             f.write('    example {!r}\n\n'.format(lex.examples[tok]))
#             seen.add(tok)





# g = grammar_loader.load_from_text('op_grammar.txt')
# g = grammar_loader.load_from_text('go_grammar2.txt')
lex, g = grammar_loader.load_from_text('cubiml_grammar.ankou')
# lex, g = grammar_loader.load_from_text('java.ankou')
# lex, g = grammar_loader.load_from_text('test_grammar.ankou')

print 'lex size', len(lex.examples), len(lex.rules)
g.pstats()
# while g.merge_toks() or g.inline_singleton_rules() or g.inline_single_use_rules() or g.inline_left_binops():
while g.merge_toks() or g.inline_singleton_rules() or g.inline_single_use_rules():
    g.pstats()
# g.right_to_left_recursion()
# g.pstats()




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


rulemap = {rn: [make_item(Rule(rn, prod), 0) for prod in sorted(prods)] for rn, prods in g.d.items()}
# rulemap = {rn: [make_item(Rule(rn, prod), 0) for prod in sorted(prods)] for rn, prods in grammar.items()}


first_sets = {}
def get_first(item):
    if item not in first_sets:
        first_sets[item] = temp = [False, LazySet(item=item)]

        if not item.tok:
            temp[0] = True
        elif item.tok not in rulemap:
            temp[1].vals.add(item.tok)
        else:
            empty = False
            for item2 in rulemap[item.tok]:
                empty2, set2 = get_first(item2)
                empty = empty or empty2
                temp[1].deps.append(set2)

            if empty:
                empty2, set2 = get_first(item.advance)
                temp[0] = empty2
                temp[1].deps.append(set2)
    # empty, first_set = first_sets[item]
    # print 'get_first', print_item(item), empty, first_set.debug()
    return first_sets[item]

item_sets = {}
def get_item_set(kernel):
    ikey = tuple(sorted([(i.rule, i.pos) for i, follow in kernel]))
    if ikey not in item_sets:
        # print 'new iset', len(item_sets), 'kernel'
        # for item, follow in kernel:
        #     print '  ', print_item(item), 'follow', follow.debug()
        # print

        stack = kernel[:]
        items = {}
        while stack:
            item, follow = stack.pop()
            # print 'item', print_item(item), 'follow', follow.debug()

            if item in items:
                items[item].deps.append(follow)
            else:
                follow_wrapped = LazySet(item=item)
                follow_wrapped.deps.append(follow)
                items[item] = follow_wrapped

                if item.tok in rulemap:
                    empty, first_set = get_first(item.advance)
                    for item2 in rulemap[item.tok]:
                        stack.append((item2, first_set))
                        if empty:
                            stack.append((item2, follow_wrapped))

        # print '\nitems'
        # for item, follow in items.items():
        #     print 'item', print_item(item), 'follow', follow.debug()

        item_sets[ikey] = iset = ItemSet(len(item_sets), items)
        # print 'inserted', ikey

        successors = defaultdict(list)
        for item, follow in sorted(items.items()):
            tok = item.tok
            if tok is not None:
                successors[tok].append((item, follow))

        for tok, pairs in sorted(successors.items()):
            pairs2 = [(item.advance, follow) for item, follow in pairs]
            iset2 = get_item_set(pairs2)
            for item, follow in pairs:
                temp = iset2.items[item.advance]
                iset2.items[item.advance].deps.append(follow)
                # print 'updated', temp.debug()
            iset.edges[tok] = pairs, iset2
    return item_sets[ikey]

t0 = time.time()
goal_follow = LazySet()
goal_follow.vals.add(EOF)
start_iset = get_item_set([(item, goal_follow) for item in rulemap['^']])
print 'item set generation', time.time() - t0

###################################################################################
conflict_count = 0
with open('templr.txt', 'w') as f:
    for iset in sorted(item_sets.values(), key=lambda iset:iset.id):
        f.write('State {}:\n'.format(iset.id))
        for item, follow in sorted(iset.items.items(), key=lambda t:(t[0].pos==0, t)):
            f.write('  {}\n'.format(print_item(item)))
            if 1 or not item.tok:
                f.write('    {{{}}}\n'.format(', '.join(sorted(follow.solve()))))

        f.write('\n')
        for tok, (pairs, iset2) in iset.edges.items():
            f.write('  {} => {}\n'.format(tok, iset2.id))

        f.write('\n')

        # check for conflicts
        actions = defaultdict(list)
        for tok, (pairs, iset2) in iset.edges.items():
            actions[tok].append(('Shift', iset2.id, ()))
        for item, follow in sorted(iset.items.items()):
            if item.tok is None:
                for tok, expls in follow.solve().items():
                    actions[tok].append(('Reduce', item.rule.lhs, item.pos, expls))

        for tok, alist in sorted(actions.items()):
            if len(alist) > 1:
                trimmed = [a[:-1] for a in alist]
                f.write('  Conflict! {} => {}\n'.format(tok, trimmed))

                if any(a[0] == 'Shift' for a in alist):
                    print 'Conflict', iset.id, tok, trimmed
                    for a in alist:
                        if a[-1]:
                            print '  ', a[:-1]
                        for eitem in a[-1]:
                            print '    ', print_item(eitem)
                conflict_count += 1
if conflict_count:
    print conflict_count, 'conflicts'
assert not conflict_count
print 'total lr generation', time.time() - t0

###################################################################################

import lrgraph4
lrg = lrgraph4.from_isets(start_iset, g.d)


# state_replace_map, sym_replace_map = lrg.simplify_dfa()
# with open('temp2.txt', 'w') as f:
#     for d in state_replace_map, sym_replace_map:
#         f.write('---\n')
#         for k, v in sorted(d.items()):
#             f.write('  {} => {}\n'.format(k, v))
# lrg.simplify_dfa()
# lrg = lrgraph3.super_prune(lrg)
# lrg.simplify_dfa()


# lrg = lrgraph4.from_isets(start_iset, g.d)
# with open('templr3.txt', 'w') as f:
#     for state in lrg.states.values():
#         f.write('State {}:\n'.format(state.id))
#         for tok, action in state.actions.items():
#             f.write('  {} => {} {} {}\n'.format(tok, *action))
#         f.write('\n')

#     for sym, gotos in lrg.gotos.items():
#         f.write('Goto {}:\n'.format(sym))
#         for tok, action in gotos.items():
#             f.write('  {} => {} {} {}\n'.format(tok, *action))
#         f.write('\n')


# state_replace_map, sym_replace_map = lrg.simplify_dfa()
# with open('temp3.txt', 'w') as f:
#     for d in state_replace_map, sym_replace_map:
#         f.write('---\n')
#         for k, v in sorted(d.items()):
#             f.write('  {} => {}\n'.format(k, v))



lrg.simplify_dfa()
# lrg.renumber()
with open('templr2.txt', 'w') as f:
    for q, state in sorted(lrg.states.items()):
        f.write('State {}:\n'.format(state.id))
        for tok, action in state.actions.items():
            f.write('  {} => {} {} {}\n'.format(tok, *action))
        f.write('\n')

    for sym, gotos in sorted(lrg.gotos.items()):
        f.write('Goto {}:\n'.format(sym))
        for tok, action in gotos.items():
            f.write('  {} => {} {} {}\n'.format(tok, *action))
        f.write('\n')


# lrg = lrg.super_prune()
# lrg = lrg.shiftless_reduction()
# lrg.simplify_dfa()
# lrg = lrgraph4.super_prune(lrg)
# lrg.simplify_dfa()




lrg.subsume_stack_symbols()
lrg.renumber()




# lrg.condense()

###################################################################################
# symbol_map = {}
# for state in sorted(lrg.states.values(), key=lambda state:state.id):
#     if state.push_symbol is None:
#         continue

#     goto_key = tuple(sorted(state.goto.items()))
#     if goto_key in symbol_map:
#         state.push_symbol = symbol_map[goto_key]
#     else:
#         symbol_map[goto_key] = state.push_symbol
####################################################################################

# lrg.renumber()
action_table = []
rev_action_table = []
for q in range(len(lrg.states)):
    state = lrg.states[q]
    assert q == state.id == len(action_table) == len(rev_action_table)

    actions = state.actions
    action_table.append(actions)

    rev_actions = defaultdict(set)
    for tok, action in actions.items():
        # if tok != 'EOF':
        #     rev_actions[action].add(tok)
        rev_actions[action].add(tok)
    rev_actions_list = sorted((min(toks), action, sorted(toks)) for action, toks in rev_actions.items())
    rev_action_table.append(rev_actions_list)

    # if state.has_push:
    #     # push_symbol = q
    #     # jump_table[push_symbol] = state.goto.copy()
    #     goto_key = tuple(sorted(state.goto.items()))
    #     if goto_key in jump_dedup_map:
    #         push_symbol = jump_dedup_map[goto_key]
    #     else:
    #         push_symbol = len(jump_table)
    #         jump_table.append(state.goto.copy())
    #         jump_dedup_map[goto_key] = push_symbol
    # else:
    #     push_symbol = None
    # push_table.append(push_symbol)

jump_table = [lrg.gotos[sym] for sym in range(len(lrg.gotos))]

###################################################################################
print 'num states {} stack symbols {}'.format(
    len(action_table),
    len(jump_table))

with open('lrtable.json', 'w') as f:
    # json.dump((TOKMAP, start_iset.id, table, stack_cost_map), f, sort_keys=True, indent=2, separators=(',', ': '))
    json.dump((TOKMAP, lrg.start_id, lrg.initial_symbol, action_table, rev_action_table, jump_table), f, sort_keys=True, indent=2, separators=(',', ': '))

# Generate lexer
with open('lexer.json', 'w') as f:
    json.dump(lex.to_json(), f, sort_keys=True, indent=2, separators=(',', ': '))


print 'done', time.time() - t0
# ../grmtools/target/debug/nimbleparse ../grammars/java7/java.l ../grammars/java7/java.y BoolizeTest3.java
