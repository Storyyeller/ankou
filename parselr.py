import collections
import heapq
import itertools
import json
import os
import re
import sys
import time


import completion_calc
# import cubic_repair_calc
from diff_printer import print_changes
# from lexer import lex_file_raw
import lexgen
import subsume

LRTable = collections.namedtuple('LRTable', 'TOKMAP, actions, rev_actions, jumps')

t0 = time.time()

lexdata = json.load(open('lexer.json', 'r'))
lex = lexgen.load_from_json(lexdata)

# TOKMAP, start_state, table, stack_cost_map = json.load(open('lrtable.json', 'r'))
TOKMAP, start_state, initial_symbol, action_table, rev_action_table, jump_table = json.load(open('lrtable.json', 'r'))
table = LRTable(TOKMAP, action_table, rev_action_table, jump_table)
print 'json load time', time.time() - t0

# start_stack = None
# if initial_symbol is not None:
#     start_stack = initial_symbol, start_stack

# pruned_rev_table = subsume.reduce_insertion_table(table)
pruned_rev_table = table.rev_actions


def lex_file(src):
    for tok, s, e in lex.lex_file(src):
        yield TOKMAP.get(tok, tok), s, e


ctable = completion_calc.generate_completion_table(table)
memo = {}
def get_completion(state):
    return completion_calc.get_completion(table, ctable, stack_pool, memo, state)


################################################################################
M = len(table.jumps) + 1
MAX_WORD = 0xFFFFFFFF
assert M < MAX_WORD
class StackPool(object):
    def __init__(self):
        self.stacks = [(0, 0)]
        self.d = {}

    def push(self, stack, x):
        x += 1
        assert 1 <= x < M

        i, top = stack
        top2 = top * M + x
        if top2 <= MAX_WORD:
            return i, top2

        # Otherwise we have to memoize the existing stack
        if stack not in self.d:
            i = len(self.stacks)
            self.stacks.append(stack)
            self.d[stack] = i
        else:
            i = self.d[stack]
        return i, x

    def pop(self, stack):
        i, top = stack
        assert 0 <= top <= MAX_WORD
        if top == 0:
            assert i > 0
            i, top = self.stacks[i]

        top2, x = divmod(top, M)
        return (i, top2), x - 1

    def flatten(self, stack):
        if stack == (0, 0):
            return ()
        stack, sym = self.pop(stack)
        return self.flatten(stack) + (sym,)



stack_pool = StackPool()
start_stack = 0, 0
if initial_symbol is not None:
    start_stack = stack_pool.push(start_stack, initial_symbol)






class Point(object):
    def __init__(self, state, changes, cost, beamw, last_delete):
        self.state = state
        self.changes = changes
        self.cost = cost
        self.beamw = beamw
        self.last_delete = last_delete

        self.priority = cost

    def pstate(self):
        state, stack = self.state
        return pstack2(stack) + [state]

    def _with(self, **kwargs):
        state = kwargs.pop('state', self.state)
        changes = kwargs.pop('changes', self.changes)
        cost = kwargs.pop('cost', self.cost)
        last_delete = kwargs.pop('last_delete', self.last_delete)
        assert not kwargs
        return Point(state, changes, cost, self.beamw, last_delete)

    def do_action(self, action):
        state, stack = self.state
        if action[0] == 'Shift':
            _, state, pushes = action
            for sym in pushes:
                stack = stack_pool.push(stack, sym)
            return self._with(state=(state, stack))
        else:
            assert action[0] == 'Reduce'
            _, jump_key, pop_count = action
            assert jump_key != '^'
            if pop_count is None:
                stack, sym = stack_pool.pop(stack)
            else:
                for _ in range(pop_count):
                    stack, _ = stack_pool.pop(stack)
                _, sym = stack_pool.pop(stack)

            jump_action = table.jumps[sym][jump_key]
            return self._with(state=(state, stack)).do_action(jump_action)

    def delete(self, trip):
        tok, start, end = trip
        changes = ('Delete', start, end), self.changes
        return self._with(changes=changes, cost=self.cost + 1, last_delete=tok)

    def shift(self, trip):
        tok, start, end = trip
        state, stack = self.state
        self = self._with(last_delete=None)
        action = table.actions[state].get(tok)
        if action is not None:
            if action[0] == 'Shift':
                return self.do_action(action)
            else:
                return self.do_action(action).shift(trip)


    def insert(self, position, insertable=None, debug=False, level=0):
        if debug:
            print '  ' * level, 'inserting for', self.pstate()
            print '  ' * level, '--', table.actions[self.state[0]]
            print '  ' * level, '---', table.rev_actions[self.state[0]]
            # print pruned_rev_table[self.state[0]]


        state, stack = self.state

        # for tok, action, toks in table.rev_actions[state]:
        for tok, action, toks in pruned_rev_table[state]:
            if self.last_delete in toks:
                if insertable is None or self.last_delete in insertable:
                    continue

            if tok == 'EOF' or insertable is not None and tok not in insertable:
                insertable2 = set(toks)
                if insertable is not None:
                    insertable2 &= insertable
                insertable2.discard('EOF')
                if not insertable2:
                    # print '  ' * level, 'skipping toks due to insertable', toks, insertable
                    continue
                tok = min(insertable2)
            assert tok != 'EOF'


            if action[0] == 'Shift':
                if debug:
                    print '  ' * level, self.pstate(), 'insert', tok
                changes = ('Insert', position, tok), self.changes
                yield self._with(changes=changes, cost=self.cost + 1, last_delete=None).do_action(action)
            else:
                assert action[0] == 'Reduce'
                _, rn, count = action
                assert rn != '^'

                if insertable is not None:
                    insertable_sub = insertable & set(toks)
                else:
                    insertable_sub = set(toks)

                if debug:
                    print '  ' * level, self.pstate(), 'reduce with', rn, count, ', '.join(sorted(insertable_sub))

                # don't add changes yet, that will be handled leter in the recursive insert() call
                point = self.do_action(action)
                for point2 in point.insert(position, insertable=insertable_sub, debug=debug, level=level+1):
                    # print '    yield', pstack(point2.state)
                    yield point2

START_POINT = Point((start_state, start_stack), None, 0, 0, None)

################################################################################
class FlatQueue(object):
    def __init__(self, offset):
        self.offset = offset
        self.flat = [[] for _ in range(4)]
        self.q = []
        # self.counter = 0

    def push(self, score, val):
        assert score >= self.offset
        diff = score - self.offset
        if diff < len(self.flat):
            self.flat[diff].append(val)
        else:
            # age = self.counter
            # self.counter += 1
            heapq.heappush(self.q, (score, val))

    def pop(self):
        while self.flat and not self.flat[0]:
            self.flat.pop(0)
            self.offset += 1

        if self.flat:
            return self.flat[0].pop()
        if not self.q:
            return None

        score, val = heapq.heappop(self.q)
        assert score >= self.offset
        return val






push_calls = [0]
def process_pos(max_beam, isize, prev_points, trip, debug=False):
    assert trip is None or trip[0] != 'EOF'
    counter = itertools.count(0)

    if prev_points:
        min_score = prev_points[0].priority
    else:
        min_score = 0

    q = FlatQueue(min_score)
    # q = []
    def push(point):
        push_calls[0] += 1
        priority = point.cost
        if isize <= 10:
        # if isize <= -10:
            completion = get_completion(point.state)
            assert completion is not None
            # priority += max(len(completion) - isize, 0)
            priority += max(completion - isize, 0)

        point.priority = priority
        # if debug:
        #     print 'pushing', point.priority, point.pstate()[-4:], pstack(point.changes)

        # priority = point.cost
        # heapq.heappush(q, (priority, next(counter), point))
        q.push(priority, point)

    if trip is not None:
        for point in prev_points:
            if debug:
                print 'old point', point.priority, point.pstate()[-4:], pstack(point.changes)
            point2 = point.shift(trip)
            if point2:
                # print 'shift', point.pstate(), '=>', pstack(point2.state)
                push(point2)
            push(point.delete(trip))
    else:
        push(START_POINT)

    out = []
    seen = set()
    # while q and len(out) < max_beam:
    while len(out) < max_beam:
    # while q and q[0][0] <= CLIMIT:
    # while 1:
        # _, _, point = heapq.heappop(q)
        point = q.pop()
        if point is None:
            break
        if point.priority > CLIMIT:
            break

        # if debug:
        #     # print 'popped', point.priority, point.pstate()[-4:], pstack(point.changes)
        #     print 'popped', point.priority, point.pstate(), pstack(point.changes)

        if point.state in seen:
            if debug:
                print 'already seen state'
            continue

        seen.add(point.state)
        out.append(point)
        point.beamw = max(point.beamw, len(out))

        position = 0 if trip is None else trip[2]
        for point2 in point.insert(position, debug=debug):
            if debug:
                print 'inserted', point2.priority, point2.pstate(), pstack(point2.changes)
            push(point2)
    return out



def pstack(stack, memo={}):
    if stack in memo:
        return memo[stack]

    if stack is None:
        res = []
    else:
        q, rest = stack
        res = [q] + pstack(rest)
    memo[stack] = res
    return res

def pstack2(stack, memo={}):
    if stack in memo:
        return memo[stack]

    if stack[1] == 0:
        res = [stack[0]] if stack[0] else []
    else:
        stack, sym = stack_pool.pop(stack)
        res = pstack2(stack) + [sym]
    memo[stack] = res
    return res




# for i in range(1, 22):
# for i in [1,7,10] + range(13,22):
for i in [9]:
    # fname = 'Model3.java'
    # fname = 'Model.java'
    # fname = 'Imports.java'
    # fname = 'HelloWorld.java'
    # fname = 'BoolizeTest.java'
    # fname = 'OpTest.java'
    # fname = 'java_corpus/s7.java'
    # fname = 'fixed_s7.java'
    # fname = 'java_corpus/s{}.java'.format(i)

    fname = 'test5.ml'
    src = open(fname, 'r').read().decode('utf8')
    tokens = list(lex_file(src))
    print fname, 'num tokens', len(tokens)

    # TOK_DISPLAY_MAP = {}
    # for tok, s, e in tokens:
    #     TOK_DISPLAY_MAP[tok] = src[s:e]

    CLIMIT = 3
    BEAM = 50
    time0 = time.time()

    counts = collections.Counter()
    worst = 0
    points = process_pos(BEAM, len(tokens), None, None, debug=0)
    for i, trip in enumerate(tokens):

        # points2 = process_pos(BEAM, len(tokens) - i - 1, points, trip)
        points2 = process_pos(BEAM, len(tokens) - i - 1, points, trip)

        worst = max(worst, len(points2))
        tok, s, e = trip
        tok_text = src[s:e]
        print i, tok, tok_text, '\t', [p.priority for p in points2[:20]]
        # print i, trip[0], len(points2), worst
        # print [(p.state[0], pstack(p.state[1])) for p in points2]
        # assert points2
        points = points2

        for p in points:
            counts[p.cost] += 1

        # if i == 42:
        #     for p in points:
        #         print '  ', p.priority, pstack(p.changes)
    print 'counts', [counts[c] for c in range(CLIMIT+1)], worst, push_calls
    print 'interned stacks', len(stack_pool.stacks)


    point = points[0]

    endpos = len(src)
    while get_completion(point.state) > 0:
        for point2 in point.insert(endpos):
            if get_completion(point2.state) < get_completion(point.state):
                break
        else:
            assert False
        point = point2


    # beam, point = pstates.best
    change_list = []
    changes = point.changes
    while changes is not None:
        change, changes = changes
        change_list.append(change)
    change_list = change_list[::-1]

    # completion
    # print 'point state', point.state[0], pstack(point.state[1])


    # completion = get_completion(point.state)
    # # print 'completion', completion
    # for t in completion:
    #     change_list.append(('Insert', endpos, t))


    # print 'Found solution score {} in {}'.format(len(change_list), time.time() - time0)
    for change in change_list[:16]:
        print change
    print print_changes(lex, src, change_list[:100])
    print 'Found solution score {} width {} in {}'.format(len(change_list), point.beamw, time.time() - time0)
    print

# time0 = time.time()
# optimal = cubic_repair_calc.parse(tokens)
# print 'Found optimal solution score {} in {}'.format(optimal.size, time.time() - time0)
# change_list2 = []
# optimal.flatten(change_list2)
# for change in change_list2[:16]:
#     print change
# print print_changes(src, change_list2[:100])


# assert len(change_list) >= len(change_list2)
# if len(change_list) > len(change_list2):
#     print 'Nonoptimal solution found!'


