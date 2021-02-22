from collections import OrderedDict, defaultdict

import fixpoint

class CompletionDict(object):
    def __init__(self, d):
        self.d = d
        assert isinstance(d, OrderedDict)

    def set(self, k, v):
        old = self.d.get(k)
        # if old is None or len(v) < len(old) or (len(v) == len(old) and v < old):
        if old is None or v < old:
            d = self.d.copy()
            d[k] = v
            return CompletionDict(d)
        return self

    def to_row(self, include_zeros):
        accept = None
        row = []
        for (rn, pop_count), v in self.d.items():
            if rn == '^':
                assert accept is None
                accept = v
            elif pop_count > 0 or include_zeros:
                row.append((pop_count, rn, v))
        row.sort(reverse=True) # put higher pop counts first
        return accept, row
EMPTY_CDICT = CompletionDict(OrderedDict())

def generate_completion_table(lrtable):
    def state_cb(cb, args, best):
        stack, q = args
        if stack:
            # print 'cb', args
            first, stack = stack[0], stack[1:]
            jumps = lrtable.jumps[first]


            for (rn, pop_count), v in cb((stack, q)).d.items():
                assert pop_count is None
                if rn == '^':
                    best = best.set((rn, pop_count), v)
                    continue

                action = jumps[rn]
                # action = jumps.get(rn)
                # if action is None:
                #     print 'missing action', first, rn, jumps
                #     continue
                if action[0] == 'Shift':
                    _, q2, pushes = action
                    for k2, v2 in cb((tuple(pushes), q2)).d.items():
                        best = best.set(k2, v + v2)
                else:
                    assert action[0] == 'Reduce'
                    _, rn2, pop_count = action
                    assert pop_count is None
                    best = best.set((rn2, pop_count), v)
        else:
            # for tok, action, toks in lrtable.rev_actions[q]:
            for tok, action in lrtable.actions[q].items():
                if action[0] == 'Shift':
                    _, q2, pushes = action
                    for k2, v2 in cb((tuple(pushes), q2)).d.items():
                        # best = best.set(k2, (tok,) + v2)
                        best = best.set(k2, 1 + v2)
                else:
                    assert action[0] == 'Reduce'
                    _, rn2, pop_count = action
                    assert pop_count is None
                    # best = best.set((rn2, pop_count), ())
                    best = best.set((rn2, pop_count), 0)
        return best

    f = fixpoint.Fixpoint(state_cb, EMPTY_CDICT)
    level1_map = [f.eval(((), q)) for q in range(len(lrtable.actions))]

    level2_map = {}
    for jumps in lrtable.jumps:
        for action in jumps.values():
            if action[0] == 'Shift':
                _, q2, pushes = action
                pushes = tuple(pushes)
                # print 'eval', q2, pushes
                level2_map[q2, pushes] = f.eval((pushes, q2))
    return level1_map, level2_map


def get_completion_sub(lrtable, ctables, stack_pool, memo, stack, rn):
    assert rn != '^'
    try:
        return memo[stack, rn]
    except KeyError:
        level1_map, level2_map = ctables
        # print 'get_completion_sub', rn, stack_pool.flatten(stack)

        stack2, sym = stack_pool.pop(stack)
        action = lrtable.jumps[sym][rn]
        # print action
        if action[0] == 'Shift':
            _, q2, pushes = action
            pushes = tuple(pushes)

            # print 'l2 map', level2_map[q2, pushes].d

            best = None
            for (rn2, _), v in level2_map[q2, pushes].d.items():
                # print rn2, v
                if rn2 != '^':
                    v2 = get_completion_sub(lrtable, ctables, stack_pool, memo, stack2, rn2)
                    if v2 is None:
                        continue
                    v = v + v2
                # if best is None or len(v) < len(best):
                if best is None or v < best:
                    best = v
        else:
            _, rn2, _ = action
            best = get_completion_sub(lrtable, ctables, stack_pool, memo, stack2, rn2)

        assert best is not None
        memo[stack, rn] = best
        return best

def get_completion(lrtable, ctables, stack_pool, memo, state):
    level1_map, level2_map = ctables
    q, stack = state

    # print 'get_completion', q, stack_pool.flatten(stack)

    best = None
    for (rn, _), v in level1_map[q].d.items():
        # print rn, v
        if rn == '^':
            # if best is None or len(v) < len(best):
            if best is None or v < best:
                best = v
            continue
        v2 = get_completion_sub(lrtable, ctables, stack_pool, memo, stack, rn)
        if v2 is None:
            continue
        v = v + v2
        # if best is None or len(v) < len(best):
        if best is None or v < best:
            best = v
    return best

