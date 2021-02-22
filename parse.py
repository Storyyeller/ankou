import collections
import heapq
import itertools
import json
import os
import re
import sys
import time

lexes, start_state, table = json.load(open('table.json', 'r'))
lex_res = [(re.compile(pat, re.M), name) for pat, name in lexes]

################################################################
# Precompute completers
rmap = [collections.defaultdict(list) for _ in table]
push_map = collections.defaultdict(set)
final_states = []
for q, (normal, pushes, isfinal) in enumerate(table):
    if isfinal:
        final_states.append(q)

    for t, q2 in normal.items():
        rmap[q2][t].append(q)

    for start, ret in pushes:
        push_map[start].add(ret)
        rmap[ret][start].append(q)


push_map = {k: sorted(v) for k, v in push_map.items()}
stack = final_states[:]
completers = {q: () for q in final_states}

while stack:
    q2 = stack.pop()
    spost = completers[q2]
    # print 'processing [{}] len {}'.format(q2, len(spost))
    for t_or_sq, qs in rmap[q2].items():
        if t_or_sq in push_map:
            if t_or_sq not in completers:
                continue
            spre = completers[t_or_sq] + spost
        else:
            spre = (t,) + spost

        for q in qs:
            if q not in completers or len(completers[q]) > len(spre):
                # print 'decrementing', q, len(spre)
                completers[q] = spre
                stack.append(q)
                for temp in push_map.get(q, []):
                    if temp in completers:
                        stack.append(temp)
                        # print 'push map', temp
# print 'completers', completers
# assert len(completers) == len(table)
################################################################


def lex_file(s):
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


class Point(object):
    def __init__(self, state, changes=None, cost=0):
        self.state = state
        self.changes = changes
        self.cost = cost

    def delete(self, trip):
        tok, start, end = trip
        changes = ('Delete', start, end), self.changes
        return Point(self.state, changes, self.cost + 1)

    def shift(self, trip):
        tok, start, end = trip
        q, stack = self.state
        normal, pushes, pop = table[q]
        q2 = normal.get(tok)
        if q2 is not None:
            return Point((q2, stack), self.changes, self.cost)

    def insert(self, position):
        q, stack = self.state
        normal, pushes, pop = table[q]

        for tok, q2 in sorted(normal.items()):
            changes = ('Insert', position, tok), self.changes
            yield Point((q2, stack), changes, self.cost + 1)

    def stack_transitions(self):
        q, stack = self.state
        normal, pushes, pop = table[q]
        for target, ret in pushes:
            prev_cost = 0 if stack is None else stack[1]
            stack2 = ret, len(completers[ret]) + prev_cost, stack
            yield Point((target, stack2), self.changes, self.cost)

        if pop:
            if stack is not None:
                q2, _, stack2 = stack
                yield Point((q2, stack2), self.changes, self.cost)


def process_pos(max_beam, isize, prev_points, trip):
    counter = itertools.count(0)

    q = []
    def push(point):
        qstate, stack = point.state
        if qstate not in completers: #TODO
            return

        hcost = len(completers[qstate])
        if stack is not None:
            hcost += stack[1]

        priority = point.cost + max(hcost - isize, 0)
        heapq.heappush(q, (priority, next(counter), point))

    if trip is not None:
        for point in prev_points:
            push(point.delete(trip))
            point2 = point.shift(trip)
            if point2:
                push(point2)
    else:
        push(Point((start_state, None)))

    out = []
    seen = set()
    # while q and len(out) < max_beam:
    while q:
        _, _, point = heapq.heappop(q)
        if point.state in seen:
            continue
        if point.cost > 0:
            continue

        seen.add(point.state)
        out.append(point)
        for point2 in point.stack_transitions():
            push(point2)

        position = 0 if trip is None else trip[2]
        for point2 in point.insert(position):
            push(point2)
    return out





def print_changes(change_list):
    change_list = change_list[::-1]

    line_changes = []
    pos = 0
    for i, line in enumerate(src.splitlines(True)):
        pos2 = pos + len(line)

        change_count = 0
        offset = -pos
        line2 = line
        while change_list and change_list[-1][1] < pos2:
            change = change_list.pop()
            change_count += 1
            if change[0] == 'Insert':
                start, tok = change[1:]
                inserted = tok

                start += offset
                line2 = line2[:start] + inserted + line2[start:]
                offset += len(inserted)
            elif change[0] == 'Delete':
                start, end = change[1:]
                # print start, end, offset, line, line2
                # print repr(line2[start:end])

                start += offset
                end += offset
                line2 = line2[:start] + line2[end:]
                offset -= end - start
            else:
                assert 0

        line_changes.append((change_count, line, line2))
        pos = pos2

    out_parts = []
    for i, (change_count, line, line2) in enumerate(line_changes):
        if change_count:
            out_parts.append('- ' + line)
            out_parts.append('+ ' + line2)
        else:
            if i == 0 or not line_changes[i-1][0]:
                if i+1 == len(line_changes) or not line_changes[i+1][0]:
                    continue
            out_parts.append('  ' + line)

    return ''.join(out_parts)



def pstack(stack, memo={}):
    if stack in memo:
        return memo[stack]

    if stack is None:
        res = []
    else:
        q, _, rest = stack
        res = [q] + pstack(rest)
    memo[stack] = res
    return res

# fname = 'BoolizeTest.java'
fname = 'Model.java'
# fname = 'Imports.java'
src = open(fname, 'r').read()
tokens = list(lex_file(src))

BEAM = 50
time0 = time.time()

worst = 0
points = process_pos(BEAM, len(tokens), None, None)
for i, trip in enumerate(tokens):

    points2 = process_pos(BEAM, len(tokens) - i - 1, points, trip)

    worst = max(worst, len(points2))
    print i, trip[0], len(points2), worst
    print [(p.state[0], pstack(p.state[1])) for p in points2]


    assert points2
    points = points2

point = points[0]

# beam, point = pstates.best
change_list = []
changes = point.changes
while changes is not None:
    change, changes = changes
    change_list.append(change)
change_list = change_list[::-1]

# completion
print 'point state', point.state
endpos = len(src)
q, stack = point.state
for t in completers[q]:
    change_list.append(('Insert', endpos, t))
while stack is not None:
    q, _, stack = stack
    for t in completers[q]:
        change_list.append(('Insert', endpos, t))


print 'Found solution score {} in {}'.format(len(change_list), time.time() - time0)
for change in change_list[:10]:
    print change
print print_changes(change_list[:10])
print 'Found solution score {} in {}'.format(len(change_list), time.time() - time0)

