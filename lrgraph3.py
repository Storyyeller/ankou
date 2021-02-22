import collections
import time

from dfa import DFA
import graph_utils
import hopcroft

class LRState3(object):
    def __init__(self, id, debug_key=None):
        self.id = id
        self.actions = collections.OrderedDict() # tok => ('Shift' id pushes | 'Reduce' jump_key pop_count?)
        self.debug_key = debug_key

class LRGraph3(object):
    def __init__(self):
        self.states = collections.OrderedDict()
        self.gotos = collections.OrderedDict() # stack_sym => jump_key => ('Shift' id pushes | 'Reduce' jump_key pop_count?)
        self.start_id = None
        self.initial_symbol = None
        self.debug_goto_keys = {}

    def map_ids(self, new_states, new_syms):
        for state in self.states.values():
            state.id = new_states.get(state.id, state.id)
            for key, action in state.actions.items():
                if action[0] == 'Shift':
                    type_, q2, pushes = action
                    pushes = tuple(new_syms.get(sym2, sym2) for sym2 in pushes)
                    state.actions[key] = type_, new_states.get(q2, q2), pushes
        for actions in self.gotos.values():
            for key, action in actions.items():
                if action[0] == 'Shift':
                    type_, q2, pushes = action
                    pushes = tuple(new_syms.get(sym2, sym2) for sym2 in pushes)
                    actions[key] = type_, new_states.get(q2, q2), pushes

        self.states = collections.OrderedDict((new_states.get(q, q), state) for q, state in self.states.items())
        self.gotos = collections.OrderedDict((new_syms.get(sym, sym), actions) for sym, actions in self.gotos.items())
        self.start_id = new_states.get(self.start_id, self.start_id)
        if self.initial_symbol is not None:
            self.initial_symbol = new_syms.get(self.initial_symbol, self.initial_symbol)

        for q, state in self.states.items():
            assert q == state.id

    def renumber(self):
        state_replace_map = {q: i for i, q in enumerate(self.states)}
        sym_replace_map = {q: i for i, q in enumerate(self.gotos)}
        self.map_ids(state_replace_map, sym_replace_map)
        assert sorted(self.states) == range(len(self.states))
        assert sorted(self.gotos) == range(len(self.gotos))

    def simplify_dfa(self):
        leaf_sets = collections.defaultdict(set)
        edges = {}

        def process_action_table(key, actions):
            leaves = []
            successors = {}
            for tok, action in sorted(actions.items()):
                if action[0] == 'Shift':
                    _, q2, pushes = action
                    successors[tok, None] = ('State', q2)
                    for i, sym in enumerate(pushes):
                        successors[tok, i] = ('Sym', sym)
                    leaves.append((tok, len(pushes)))
                else:
                    leaves.append((tok, action))
            leaf_sets[tuple(leaves)].add(key)
            edges[key] = successors

        for state in self.states.values():
            process_action_table(('State', state.id), state.actions)
        for k, actions in self.gotos.items():
            process_action_table(('Sym', k), actions)

        partitions = hopcroft.simplify(leaf_sets.values(), edges)
        state_replace_map = {}
        sym_replace_map = {}
        for s in partitions:
            if len(s) <= 1:
                continue

            type_, val = root = min(s)
            s.remove(root)
            assert all(p[0] == type_ for p in s)

            if type_ == 'State':
                for _, val2 in s:
                    state_replace_map[val2] = val
            else:
                assert type_ == 'Sym'
                for _, val2 in s:
                    sym_replace_map[val2] = val

        if not state_replace_map and not sym_replace_map:
            return

        print 'removing {} states, {} symbols'.format(len(state_replace_map), len(sym_replace_map))

        for q in state_replace_map:
            assert state_replace_map[q] != q
            del self.states[q]
        for sym in sym_replace_map:
            assert sym_replace_map[sym] != sym
            del self.gotos[sym]
        self.map_ids(state_replace_map, sym_replace_map)
        return state_replace_map, sym_replace_map

    def super_prune(self):
        return super_prune(self)

    def subsume_stack_symbols(self):
        old_count = len(self.gotos)
        work_list = self.gotos.items()
        self.gotos.clear()
        sym_replace_map = {}

        while work_list:
            old_key, actions = work_list.pop()
            merged = actions.copy()
            self.gotos[old_key] = merged

            for _, actions in work_list:
                if any(merged.get(k, v) != v for k, v in actions.items()):
                    continue
                merged.update(actions)

            remaining = []
            for sym, actions in work_list:
                if any(merged.get(k, v) != v for k, v in actions.items()):
                    remaining.append((sym, actions))
                else:
                    sym_replace_map[sym] = old_key
            work_list = remaining
        self.map_ids({}, sym_replace_map)
        print 'subsume_stack_symbols', old_count, '->', len(self.gotos)




def from_isets(start_iset, rule_names):
    lrg = LRGraph3()
    lrg.start_id = start_iset.id
    lrg.initial_symbol = start_iset.id

    stack = [start_iset]
    while stack:
        iset = stack.pop()
        if iset.id in lrg.states:
            continue

        lrg.states[iset.id] = state = LRState3(iset.id)
        lrg.gotos[iset.id] = gotos = collections.OrderedDict()
        for term, (pairs, iset2) in sorted(iset.edges.items()):
            stack.append(iset2)
            action = 'Shift', iset2.id, (iset2.id,)
            if term in rule_names:
                assert term not in gotos
                gotos[term] = action
            else:
                assert term not in state.actions
                state.actions[term] = action

        for item, follow in sorted(iset.items.items()):
            if item.tok is not None:
                continue

            action = 'Reduce', item.rule.lhs, item.pos
            follow = follow.solve()
            assert follow
            for tok in follow:
                assert tok not in state.actions
                state.actions[tok] = action
    return lrg

def super_prune(lrg):
    ###################################################################################
    # Construct the DFA of possible stacks
    epsilons = collections.defaultdict(set)

    dfa = DFA()
    dummy_state = dfa.add_state()
    dfa.final.add(dummy_state)

    state_map = {q: dfa.add_state() for q in lrg.states}
    sym_map = {q: dfa.add_state() for q in lrg.gotos}
    dfa.final.update(state_map.values())


    def process_actions(base_dfa_state, actions):
        for action in actions.values():
            if action[0] == 'Shift':
                _, q2, pushes = action
                dfa_state = base_dfa_state
                for sym in pushes:
                    if sym not in dfa.map[dfa_state]:
                        temp = dfa.add_state()
                        dfa.add_edge(dfa_state, sym, temp)
                        epsilons[temp].add(sym_map[sym])

                    dfa_state = dfa.map[dfa_state][sym]
                epsilons[dfa_state].add(state_map[q2])
            else:
                assert action[0] == 'Reduce'
                _, rn, pop_count = action

                # Add dummy edges for reduce actions to prevent states with incompatible
                # jump tables from being merged
                dummy_label = '{}-{}'.format(rn, pop_count)
                if dummy_label not in dfa.map[base_dfa_state]:
                    dfa.add_edge(base_dfa_state, dummy_label, dummy_state)



    for q, state in lrg.states.items():
        process_actions(state_map[q], state.actions)
    for sym, actions in lrg.gotos.items():
        process_actions(sym_map[sym], actions)

    dfa.initial = dfa.add_state()
    if lrg.initial_symbol is not None:
        dfa.add_edge(dfa.initial, lrg.initial_symbol, state_map[lrg.start_id])
        epsilons[state_map[lrg.start_id]].add(sym_map[lrg.initial_symbol])
    else:
        epsilons[dfa.initial].add(state_map[lrg.start_id])



    dfa = dfa.with_epsilon(epsilons).simplify()
    # dfa = dfa.with_epsilon(epsilons)
    print 'lr states {} lr gotos {} reduced stack dfa size {}'.format(len(lrg.states), len(lrg.gotos), len(dfa.map))
    ###################################################################################
    # Now choose a feedback set of DFA states
    rdeps = {s: set().union(*d.values()) for s, d in dfa.rmap.items()}
    assert len(rdeps) == len(dfa.map)

    feedback_set = set()
    work = [(set(dfa.map), rdeps, 0)]
    while work:
        states2, rdeps2, level = work.pop()
        sccs = graph_utils.tarjan(states2, rdeps2.get)

        for scc in sccs:
            if len(scc) == 1 and scc[0] not in rdeps2[scc[0]]:
                continue

            sset = set(scc)
            # heads = [q for q in scc if not sset.issuperset(rdeps2[q])]
            heads = [q for q in scc if not sset.issuperset(rdeps[q])]
            print 'scc heads', level, len(scc), len(heads)
            assert heads

            if len(heads) == 1:
                print '  ', heads, scc
                # for q in scc:
                #     print q, '->', dfa.map[q].items()

            # chosen = min(heads, key=lambda q:(-len(rdeps2[q]), q))
            # heads = [chosen]

            feedback_set.update(heads)
            sset.difference_update(heads)

            if sset:
                rdeps3 = {q: sset.intersection(rdeps2[q]) for q in sset}
                work.append((sset, rdeps3, level + 1))
    feedback_set.add(dfa.initial)
    print 'feedback', len(feedback_set), sorted(feedback_set)

    ###################################################################################
    # Now construct the new lrg
    t0 = time.time()
    lrg2 = LRGraph3()
    pending_states = [] # VirtualState
    root_reduces = {s: set() for s in feedback_set} # dfa root -> set((rn, pop_count))
    root_predecessors = {s: set() for s in feedback_set} # dfa root -> set(forgotten stack)
    pending_jumps = [] # (forgotten stack, (rn, pop_count))

    # WATCH_STACKS = {(0, 1023, 2)}
    def register_stack_transition(forgotten, new_dfa_state):
        if forgotten not in root_predecessors[new_dfa_state]:
            # if forgotten[1] in WATCH_STACKS:
            #     print 'register_stack_transition', forgotten, new_dfa_state
            root_predecessors[new_dfa_state].add(forgotten)
            for rpair in root_reduces[new_dfa_state]:
                pending_jumps.append((forgotten, rpair))

            if forgotten not in lrg2.gotos:
                lrg2.gotos[forgotten] = collections.OrderedDict()

    def register_pop(dfa_state, rpair):
        if rpair not in root_reduces[dfa_state]:
            # if dfa_state == 4:
            #     print 'register_pop', dfa_state, rpair
            root_reduces[dfa_state].add(rpair)
            for forgotten in root_predecessors[dfa_state]:
                pending_jumps.append((forgotten, rpair))

                rn, pop_count = rpair
                if pop_count is not None and pop_count < len(forgotten[1]):
                    assert rn in lrg.gotos[forgotten[1][-pop_count-1]]



    class VirtualState(object):
        def __init__(self, state, stack, dfa_state, dfa_stack):
            # print 'VirtualState', state, stack, dfa_state, dfa_stack
            assert len(stack) == len(dfa_stack)
            self.state = state
            self.stack = stack
            self.dfa_state = dfa_state
            self.dfa_stack = dfa_stack
            base_dfa_state = self.dfa_stack[0] if self.dfa_stack else self.dfa_state
            assert base_dfa_state in feedback_set or base_dfa_state == dfa.initial
            # if self.state == 3 and self.stack == [3]:
            #     print 'VirtualState', state, stack, dfa_state, dfa_stack

        def copy(self):
            return VirtualState(self.state, self.stack[:], self.dfa_state, self.dfa_stack[:])

        @property
        def new_id(self):
            base_dfa_state = self.dfa_stack[0] if self.dfa_stack else self.dfa_state
            return self.state, tuple(self.stack), base_dfa_state, self.dfa_state

        def push(self, sym):
            self.stack.append(sym)
            self.dfa_stack.append(self.dfa_state)
            self.dfa_state = dfa.map[self.dfa_state][sym]

        def perform_action(self, action):
            # attempts to perform a shift or reduce on the virtual state
            # if action is a reduce and virtual stack isn't big enough,
            # return a reduce action for the new automata
            # otherwise return just 'Shift'
            # (shift params to be determined by caller)
            if action is None:
                return None

            if action[0] == 'Shift':
                _, q2, pushes = action
                for sym in pushes:
                    self.push(sym)
                self.state = q2
                return 'Shift'
            else:
                assert action[0] == 'Reduce'
                _, rn, pop_count = action
                # The dfa state we would be in if we popped the entire stack
                base_dfa_state = self.dfa_stack[0] if self.dfa_stack else self.dfa_state
                assert base_dfa_state in feedback_set or base_dfa_state == dfa.initial

                if rn == '^':
                    assert tok == 'EOF'
                    return 'Reduce', '^', None
                elif pop_count is None:
                    if not self.stack:
                        register_pop(base_dfa_state, (rn, pop_count))
                        return action

                    sym = self.stack.pop()
                    self.dfa_state = self.dfa_stack.pop()
                    return self.perform_action(lrg.gotos[sym][rn])
                elif pop_count >= len(self.stack):
                    register_pop(base_dfa_state, (rn, pop_count - len(self.stack)))
                    jump_key = '{}-{}'.format(rn, pop_count - len(self.stack))
                    return 'Reduce', jump_key, None
                else:
                    for _ in range(pop_count):
                        sym = self.stack.pop()
                        self.dfa_state = self.dfa_stack.pop()

                    sym = self.stack[-1]
                    return self.perform_action(lrg.gotos[sym][rn])

        def get_new_action(self, old_action, tok):
            assert old_action is not None
            temp = self.perform_action(old_action)
            if temp != 'Shift':
                return temp

            if old_action[0] == 'Reduce':
                # We successfully performed the reduce using the virtual stack
                # so we now need to actually shift the token
                old_action2 = lrg.states[self.state].actions.get(tok)
                if old_action2 is None:
                    return None
                return self.get_new_action(old_action2, tok)
            else:
                return self.create_shift_action()

        def create_shift_action(self):
            # We're done performing actions - now constuct a shift action
            # to represent the cumulative changes.
            # print 'creating shift', self.stack, self.dfa_state, self.dfa_stack
            new_pushes = []
            last_root_i = 0
            for i in range(1, len(self.dfa_stack) + 1):
                dfa_state = self.dfa_state if i == len(self.dfa_stack) else self.dfa_stack[i]
                if dfa_state in feedback_set:
                    start_dfa_state = self.dfa_stack[last_root_i]
                    popped_stack = tuple(self.stack[last_root_i:i])
                    new_pushes.append((start_dfa_state, popped_stack, dfa_state))
                    register_stack_transition(new_pushes[-1], dfa_state)
                    # print 'forgetting', new_pushes[-1], dfa_state
                    last_root_i = i

            self.stack = self.stack[last_root_i:]
            self.dfa_stack = self.dfa_stack[last_root_i:]
            pending_states.append(self)
            return 'Shift', self.new_id, tuple(new_pushes)


    initial_vstate = VirtualState(lrg.start_id, [], dfa.initial, [])
    if lrg.initial_symbol is not None:
        lrg2.initial_symbol = initial_vstate.push(lrg.initial_symbol)
    lrg2.start_id = initial_vstate.new_id
    pending_states.append(initial_vstate)



    while pending_states or pending_jumps:
        while pending_states:
            vstate = pending_states.pop()
            new_id = vstate.new_id
            if new_id in lrg2.states:
                continue

            lrg2.states[new_id] = state = LRState3(new_id, debug_key=new_id)
            for tok, action in lrg.states[vstate.state].actions.items():
                new_action = vstate.copy().get_new_action(action, tok)
                if new_action is not None:
                    state.actions[tok] = new_action

        while pending_jumps:
            new_sym, (rn, pop_count) = pending_jumps.pop()
            start_dfa_state, stack, end_dfa_state = new_sym
            # print 'new_sym', new_sym
            # print 'rpair', rn, pop_count

            assert len(stack) >= 1
            assert start_dfa_state in feedback_set or start_dfa_state == dfa.initial
            assert end_dfa_state in feedback_set
            assert rn != '^'

            vstate = VirtualState(0, [], start_dfa_state, [])
            for sym in stack:
                vstate.push(sym)
            assert vstate.dfa_state == end_dfa_state

            action = vstate.perform_action(('Reduce', rn, pop_count))
            if action == 'Shift':
                action = vstate.create_shift_action()

            if pop_count is None:
                jump_key = rn
            else:
                jump_key = '{}-{}'.format(rn, pop_count)
            lrg2.gotos[new_sym][jump_key] = action

    print 'phase 2', time.time() - t0
    print 'flattened size', len(lrg2.states), len(lrg2.gotos)
    return lrg2
