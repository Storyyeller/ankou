from collections import defaultdict

from dfa import PartitionRefinement
from fixpoint import Fixpoint
import graph_utils
from unionfind import UnionFind

class LRState(object):
    def __init__(self, id):
        self.id = id
        self.shift = {} # tok => id
        self.goto = {} # rn => id
        self.reduce = [] # (set(Tok), (rn, pop_count))
        self.push_symbol = id

    def renumber(self, imap):
        self.id = imap[self.id]
        if self.push_symbol is not None:
            self.push_symbol = imap[self.push_symbol]
        self.shift = {tok: imap[q2] for tok, q2 in self.shift.items()}
        self.goto = {rn: imap[q2] for rn, q2 in self.goto.items()}


class LRGraph(object):
    def __init__(self, start_id, states):
        self.start_id = start_id
        self.states = states

    def renumber(self, imap):
        self.start_id = imap[self.start_id]
        for q in self.states.values():
            q.renumber(imap)
        self.states = {q.id: q for q in self.states.values()}

    def condense(self):
        states = sorted(self.states.values(), key=lambda state:state.id)
        imap = {state.id: i for i, state in enumerate(states)}
        self.renumber(imap)


def from_isets(start_iset, rule_names):
    smap = {}
    stack = [start_iset]
    while stack:
        iset = stack.pop()
        if iset.id in smap:
            continue

        smap[iset.id] = state = LRState(iset.id)
        for term, (pairs, iset2) in iset.edges.items():
            stack.append(iset2)
            if term in rule_names:
                state.goto[term] = iset2.id
            else:
                state.shift[term] = iset2.id

        for item, follow in iset.items.items():
            if item.tok is not None:
                continue

            key = item.rule.lhs, item.pos
            follow = follow.solve()
            assert follow
            state.reduce.append((frozenset(follow), key))

    return LRGraph(start_iset.id, smap)

def hopcroft(lrg, debug=False):
    reduce_map = defaultdict(set)
    for state in lrg.states.values():
        for follow, key in state.reduce:
            for tok in follow:
                reduce_map[key, tok].add(state.id)

    allterms = set()
    rshift_map = {k: defaultdict(set) for k in lrg.states}
    for state in lrg.states.values():
        for term, q2 in state.shift.items() + state.goto.items():
            rshift_map[q2][term].add(state.id)
            allterms.add(term)

    partitions = PartitionRefinement(set(lrg.states))
    partitions.split({state.id for state in lrg.states.values() if state.push_symbol is None})
    if debug:
        print 'partitions', partitions.debug()

    for rset in reduce_map.values():
        partitions.split(rset)
        if debug:
            print 'partitions', partitions.debug()

    processed = set()
    worklist = list(partitions.sets)
    while worklist:
        wset = worklist.pop()
        key = frozenset(wset)
        if key in processed:
            continue
        processed.add(key)

        for t in allterms:
            rset = set()
            for s in key:
                rset.update(rshift_map[s][t])
            worklist.extend(map(set, partitions.split(rset)))
            if debug:
                print 'splitting', rset, 'from', key, t
                print 'partitions', partitions.debug()
                print 'worklist', map(sorted, worklist)

    groups = [part for part in partitions.sets if len(part) > 1]
    print len(groups), 'groups found'

    if groups:
        imap = {k: k for k in lrg.states}
        for group in groups:
            rep = min(group)
            group.discard(rep)
            for other in group:
                imap[other] = rep
                del lrg.states[other]
        # print 'group replace map', {k: v for k, v in imap.items() if k != v}
        lrg.renumber(imap)


def prune_pushes(lrg):
    assert all(state.push_symbol is None or state.push_symbol == state.id for state in lrg.states.values())
    stack_symbols = sorted(state.push_symbol for state in lrg.states.values() if state.push_symbol is not None)
    state_ids = sorted(lrg.states)

    fmap = defaultdict(set)
    rmap = defaultdict(set)
    for state in lrg.states.values():
        for term, q2 in state.shift.items() + state.goto.items():
            rmap[q2].add(state.id)
            fmap[state.id].add(q2)
    rmap = {q: sorted(rmap[q]) for q in state_ids}

    fmap = {q: sorted(fmap[q]) for q in state_ids}
    # sccs = graph_utils.tarjan(state_ids, fmap.get)
    # loops = []
    # for scc in sccs:
    #     print scc
    #     if len(scc) > 1:
    #         loops.extend(scc)
    # print 'bad', len(loops), len(state_ids), sorted(loops)



    def stack_rev_transition(cb, q, best):
        best = set(best)
        for q2 in rmap[q]:
            if q2 in stack_symbols:
                best.add(q2)
            else:
                best.update(cb(q2))
        return frozenset(best)
    f = Fixpoint(stack_rev_transition, frozenset())
    rev_stack_map = {q: f.eval(q) for q in state_ids}
    initial_sets = {q: ([q] if lrg.states[q].push_symbol is not None else sorted(f.eval(q))) for q in state_ids}

    uf = UnionFind()
    MUST_PUSH = lrg.start_id
    assert lrg.states[MUST_PUSH].push_symbol is not None

    wave_map = {}
    for q in state_ids:
        state = lrg.states[q]
        if not state.reduce:
            continue

        wave_map[q] = waves = [initial_sets[q]]
        assert waves[0]
        for follow, (rn, pop_count) in state.reduce:
            while len(waves) <= pop_count:
                new_wave = set()
                for pred in waves[-1]:
                    new_wave.update(rmap[pred])
                assert new_wave
                waves.append(sorted(new_wave))

            uf.union(MUST_PUSH, waves[pop_count][0])
            # if rn != '^':
            #     jump_targets = {lrg.states[wq].goto[rn] for wq in waves[pop_count]}
            #     if len(jump_targets) > 1:
            #         uf.union(MUST_PUSH, waves[pop_count][0])

        for wave in waves:
            first = wave[0]
            for wq in wave[1:]:
                uf.union(first, wq)

    # Now that the unioning is done, we have the new set of states that need push symbols
    new_push_states = {q for q in stack_symbols if uf.find(q) == uf.find(MUST_PUSH)}
    if len(new_push_states) == len(stack_symbols):
        return

    # Now apply the changes
    # inline_candidates = 0
    # inlines_performed = 0
    for q in state_ids:
        state = lrg.states[q]
        if q not in new_push_states:
            state.push_symbol = None

        if not state.reduce:
            continue

        waves = wave_map[q]
        push_waves = []
        # for wave in waves[:-1]:
        for i, wave in enumerate(waves):
            all_push = all(wq in new_push_states for wq in wave)
            any_push = any(wq in new_push_states for wq in wave)
            assert all_push or not any_push
            push_waves.append(1 if any_push else 0)

        new_reduce = []
        for follow, (rn, pop_count) in state.reduce:
            # jump_targets = set() if rn == '^' else {lrg.states[wq].goto[rn] for wq in waves[pop_count]}
            # if len(jump_targets) == 1 and sum(push_waves[:pop_count]) == 0:
            #     # Potentially convert the reduction to a regular jump
            #     inline_candidates += 1
            #     target = jump_targets.pop()
            #     target_state = lrg.states[target]
            #     # TODO: inline in more cases
            #     if target not in new_push_states and all(tok in target_state.shift for tok in follow):
            #         for tok in follow:
            #             assert tok not in state.shift
            #             state.shift[tok] = target_state.shift[tok]
            #         inlines_performed += 1
            #         continue

            assert push_waves[pop_count]
            pop_count = sum(push_waves[:pop_count])
            new_reduce.append((follow, (rn, pop_count)))
        state.reduce = new_reduce
    # print 'inline_candidates', inline_candidates, 'inlines_performed', inlines_performed




