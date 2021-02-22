import collections
import time

from fixpoint import Fixpoint
import graph_utils
from unionfind import UnionFind


class LRState2(object):
    def __init__(self, id, has_push, debug_key=None):
        self.id = id
        self.actions = collections.OrderedDict() # tok => ('Shift' id | 'Reduce' jump_key pop_count?)
        # self.shifts = [] # (set(tok), id)
        # self.reduces = [] # (set(tok), (jump_key, pop_count?))
        self.goto = collections.OrderedDict() # jump_key => ('Goto' id | 'Pop' jump_key)
        self.has_push = has_push
        self.debug_key = debug_key

class LRGraph2(object):
    def __init__(self, start_id, states):
        self.start_id = start_id
        self.states = states


def from_isets(start_iset, rule_names):
    smap = {}
    stack = [start_iset]
    while stack:
        iset = stack.pop()
        if iset.id in smap:
            continue

        # shifts = collections.defaultdict(set)
        smap[iset.id] = state = LRState2(iset.id, True)
        for term, (pairs, iset2) in sorted(iset.edges.items()):
            stack.append(iset2)
            if term in rule_names:
                assert term not in state.goto
                state.goto[term] = 'Goto', iset2.id
            else:
                assert term not in state.actions
                state.actions[term] = 'Shift', iset2.id
                # shifts[iset2.id].add(term)

        for item, follow in sorted(iset.items.items()):
            if item.tok is not None:
                continue

            action = 'Reduce', item.rule.lhs, item.pos
            follow = follow.solve()
            assert follow
            for tok in follow:
                assert tok not in state.actions
                state.actions[tok] = action

            # state.reduces.append((frozenset(follow), key))
        # state.shifts = [(frozenset(toks), q2) for q2, toks in shifts.items()]
        # state.shifts.sort()
        # state.reduces.sort()
    return LRGraph2(start_iset.id, smap)

###################################################################################
def super_prune(lrg):
    state_ids = sorted(lrg.states)
    push_ids = [q for q in state_ids if lrg.states[q].has_push]
    sym_set = set(push_ids)

    def stack_deps_cb(cb, q, best):
        best = set(best)
        state = lrg.states[q]
        for tok, action in state.actions.items():
            if action[0] == 'Shift':
                q2 = action[1]
                if q2 in sym_set:
                    best.add(q2)
                else:
                    best.update(cb(q2))

        for jump_key, action in state.goto.items():
            if action[0] == 'Goto':
                q2 = action[1]
                if q2 in sym_set:
                    best.add(q2)
                else:
                    best.update(cb(q2))
        return frozenset(best)
    f = Fixpoint(stack_deps_cb, frozenset())

    rdeps = {q: [] for q in push_ids}
    for q in push_ids:
        for q2 in f.eval(q):
            rdeps[q2].append(q)

    ###################################################################################
    feedback = []
    work = [(push_ids, rdeps, 0)]
    while work:
        states2, rdeps2, level = work.pop()
        sccs = graph_utils.tarjan(states2, rdeps2.get)

        for scc in sccs:
            if len(scc) == 1 and scc[0] not in rdeps2[scc[0]]:
                continue

            sset = set(scc)
            heads = [q for q in scc if not sset.issuperset(rdeps2[q])]
            print 'scc heads', level, len(scc), len(heads)
            assert heads
            feedback.extend(heads)
            sset.difference_update(heads)

            if sset:
                rdeps3 = {q: sset.intersection(v) for q, v in rdeps2.items()}
                work.append((sorted(sset), rdeps3, level + 1))
    print 'feedback', len(feedback), sorted(feedback)
    feedback_set = frozenset(feedback)
    ###################################################################################
    def overpops_cb(cb, q, best):
        best = set(best)
        state = lrg.states[q]
        stack_offset = 1 if state.has_push else 0

        deps1 = [action[1] for action in state.actions.values() if action[0] == 'Shift']
        deps2 = [jump[1] for jump in state.goto.values() if jump[0] == 'Goto']
        deps = deps1 + deps2

        for q2 in deps:
            for rn, pop_count in cb(q2):
                pop_count -= stack_offset
                if pop_count >= 0 and rn != '^':
                    best.add((rn, pop_count))

        for action in state.actions.values():
            if action[0] == 'Reduce':
                rn, pop_count = action[1:]
                assert pop_count is not None
                pop_count -= stack_offset
                if pop_count >= 0 and rn != '^':
                    best.add((rn, pop_count))

        return frozenset(best)
    f = Fixpoint(overpops_cb, frozenset())
    overpops = {q: f.eval(q) for q in feedback}
    # print 'overpops', overpops
    ###################################################################################
    lr_action_tables = {state.id: state.actions for state in lrg.states.values()}
    # for q in state_ids:
    #     state = lrg.states[q]

    #     actions = {}
    #     for toks, s2 in state.shifts:
    #         for tok in toks:
    #             assert tok not in actions
    #             actions[tok] = 'Shift', s2

    #     for follow, (rn, pop_count) in state.reduces:
    #         for tok in follow:
    #             assert tok not in actions, 'conflict!'
    #             actions[tok] = 'Reduce', rn, pop_count
    #     lr_action_tables[q] = actions
    ###################################################################################
    t0 = time.time()
    # WATCH_IDS = 0, 1, 241821, 241822, 188

    # map old (q, stack) -> new q
    new_state_ids = {}
    work = []
    def get_new_state_id(q, stack):
        try:
            return new_state_ids[q, stack]
        except KeyError:
            new_state_ids[q, stack] = val = len(new_state_ids)
            work.append((val, q, stack))
            if not val % 10000:
            # if val in WATCH_IDS:
                print 'new state', val, q, stack
            return val

    new_start_id = get_new_state_id(lrg.start_id, (lrg.start_id,))
    lrg2 = LRGraph2(new_start_id, {})
    action_tables = {}

    def get_new_action_noforget(q, stack, tok):
        action = lr_action_tables[q].get(tok)
        if action is None:
            return None
        if action[0] == 'Shift':
            q2 = action[1]
            stack2 = stack
            if q2 in sym_set:
                stack2 = (q2,) + stack2
            new_id2 = get_new_state_id(q2, stack2)
            return 'Shift', new_id2
        else:
            assert action[0] == 'Reduce'
            _, rn, pop_count = action
            if rn == '^':
                assert tok == 'EOF'
                return 'Reduce', '^', None
            elif pop_count >= len(stack):
                assert stack[-1] in feedback_set
                jump_key = '{}-{}'.format(rn, pop_count - len(stack))
                return 'Reduce', jump_key, None
            else:
                stack2 = stack[pop_count:]
                jump = lrg.states[stack2[0]].goto[rn]
                assert jump[0] == 'Goto'
                q2 = jump[1]
                if q2 in sym_set:
                    stack2 = (q2,) + stack2
                return get_new_action_noforget(q2, stack2, tok)

    while work:
        new_id, q, stack = work.pop()

        # has_push = q in feedback_set and len(stack) > 1
        has_push = any(sym in feedback_set for sym in stack[:-1])


        lrg2.states[new_id] = new_state = LRState2(new_id, has_push, debug_key=(q, stack))
        old_state = lrg.states[q]

        action_tables[new_id] = actions = {}
        if has_push:
            split_i = [i for i, sym in enumerate(stack[:-1]) if sym in feedback_set][0]
            new_stack = stack[:split_i+1]
            root = new_stack[-1]

            for tok in lr_action_tables[q]:
                action = get_new_action_noforget(q, new_stack, tok)
                if action is not None:
                    actions[tok] = action

            # print q, stack, overpops[q]
            for rn, pop_count in overpops[root]:
                jump_key = '{}-{}'.format(rn, pop_count)
                pop_count += len(new_stack) # account for top of stack being preserved when forgetting
                if pop_count >= len(stack):
                    jump_key2 = '{}-{}'.format(rn, pop_count - len(stack))
                    new_state.goto[jump_key] = 'Pop', jump_key2
                else:
                    stack2 = stack[pop_count:]
                    jump = lrg.states[stack2[0]].goto[rn]
                    assert jump[0] == 'Goto'
                    q2 = jump[1]
                    if q2 in sym_set:
                        stack2 = (q2,) + stack2
                    new_state.goto[jump_key] = 'Goto', get_new_state_id(q2, stack2)
        else:
            for tok in lr_action_tables[q]:
                action = get_new_action_noforget(q, stack, tok)
                if action is not None:
                    actions[tok] = action


    print 'done creating states', len(action_tables), time.time() - t0

    # Now reverse and flatten the action tables
    for new_id, actions in action_tables.items():
        new_state = lrg2.states[new_id]
        assert not new_state.actions
        for tok, action in sorted(actions.items()):
            new_state.actions[tok] = action
        # assert not new_state.shifts and not new_state.reduces

        # shifts = collections.defaultdict(set)
        # reduces = collections.defaultdict(set)
        # for tok, action in actions.items():
        #     if action[0] == 'Shift':
        #         shifts[action[1]].add(tok)
        #     else:
        #         assert action[0] == 'Reduce'
        #         assert action[2] is None
        #         reduces[action[1]].add(tok)

        # new_state.shifts = [(frozenset(toks), q2) for q2, toks in shifts.items()]
        # new_state.reduces = [(frozenset(toks), (jump_key, None)) for jump_key, toks in reduces.items()]
        # new_state.shifts.sort()
        # new_state.reduces.sort()

    return lrg2
