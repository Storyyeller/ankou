from collections import namedtuple, defaultdict, Counter
import itertools

import hopcroft



ABSORB = 0
class DFA(object):
    def __init__(self):
        self.counter = itertools.count(ABSORB + 1)

        self.initial = ABSORB
        self.map = {}
        self.rmap = {}
        self.final = set()

    def add_state(self):
        i = next(self.counter)
        self.map[i] = {}
        self.rmap[i] = defaultdict(set)
        return i

    def add_edge(self, s1, t, s2):
        assert t not in self.map[s1]
        self.map[s1][t] = s2
        self.rmap[s2][t].add(s1)

    def remove_edge(self, s1, t):
        s2 = self.map[s1][t]
        del self.map[s1][t]
        self.rmap[s2][t].remove(s1)

    #########################################
    def from_productions(self, productions):
        assert not self.initial

        self.initial = self.add_state()
        for prod in sorted(productions):
            state = self.initial
            for t in prod:
                if t not in self.map[state]:
                    new = self.add_state()
                    self.add_edge(state, t, new)

                state = self.map[state][t]
            self.final.add(state)
        return self

    def with_epsilon(self, edges, debug=False):
        # transitive closure of epislon edges
        def expand_set(dset):
            temp = set(dset)
            for n2 in dset:
                if n2 in edges:
                    temp.update(edges[n2])
            return frozenset(temp)

        while edges:
            dirty = False
            for n1, dset in edges.items():
                temp = len(dset)
                dset = expand_set(dset)
                if len(dset) > temp:
                    edges[n1] = dset
                    dirty = True
            if not dirty:
                break

        new = DFA()

        initial_set = expand_set({self.initial})
        nmap = {initial_set: new.add_state()}
        new.initial = nmap[initial_set]

        stack = [initial_set]
        while stack:
            nset = stack.pop()
            state = nmap[nset]

            successors = defaultdict(set)
            for n in nset:
                for t, n2 in self.map[n].items():
                    successors[t].add(n2)

            for t, nset2 in sorted(successors.items()):
                nset2 = expand_set(nset2)
                if nset2 not in nmap:
                    nmap[nset2] = new.add_state()
                    stack.append(nset2)

                state2 = nmap[nset2]
                new.add_edge(state, t, state2)

            if nset & self.final:
                new.final.add(state)

        new.check()
        if debug:
            print 'we map', nmap
        return new

    def get_reachable(self):
        allnodes = set()
        stack = [self.initial]
        while stack:
            s = stack.pop()
            if s in allnodes:
                continue

            allnodes.add(s)
            stack.extend(self.map[s].values())
        return allnodes

    def simplify2(self, debug=False):
        self.check()

        allnodes = set(self.map)
        sets = hopcroft.simplify([self.final, allnodes - self.final], self.map)

        replaced_map = {}
        for part in sets:
            if len(part) > 1:
                rep = min(part)
                assert rep > ABSORB
                for other in part - {rep}:
                    replaced_map[other] = rep
                    # print other, '->', rep
                    for t, pset in self.rmap[other].items():
                        for pred in list(pset):
                            assert self.map[pred][t] == other
                            self.remove_edge(pred, t)
                            self.add_edge(pred, t, rep)

                    for t, s2 in self.map[other].items():
                        self.remove_edge(other, t)

                    del self.map[other]
                    del self.rmap[other]
                    self.final.discard(other)
                    if self.initial == other:
                        self.initial = rep
                    # print 'map', self.map
                    # print 'rmap', {s: {t: sorted(v) for t, v in dd.items()} for s, dd in self.rmap.items()}

                    if debug:
                        print 'in simpl', replaced_map
                        self.debug('?')

        # print 'reachable', sorted(self.get_reachable())
        # print 'found', sorted(self.map)
        # print 'map', self.map
        # print 'rmap', {s: {t: sorted(v) for t, v in dd.items()} for s, dd in self.rmap.items()}

        # assert len(self.get_reachable()) == len(self.map)
        self.check()
        return replaced_map

    def simplify(self, debug=False):
        nmap = self.simplify2(debug=debug)
        if debug:
            print 'simpl map', nmap
        return self

    def check(self):
        assert ABSORB not in self.map
        assert self.initial in self.map
        assert self.final <= set(self.map)
        for s1, d in self.map.items():
            for t, s2 in d.items():
                assert s1 in self.rmap[s2][t]

        for s2, d in self.rmap.items():
            for t, s1set in d.items():
                for s1 in s1set:
                    assert self.map[s1][t] == s2

    def remove_left_recursion(self, term):
        suc = self.map[self.initial].get(term)
        if suc is None:
            return self

        self.remove_edge(self.initial, term)
        edges = {fs: {suc} for fs in self.final}
        return self.with_epsilon(edges)

    def remove_right_recursion(self, term):
        preds = set()
        for fs in self.final:
            preds.update(self.rmap[fs][term])
        if not preds:
            return self

        for s in preds:
            self.remove_edge(s, term)

        edges = {s: {self.initial} for s in preds}
        return self.with_epsilon(edges)

    def inline(self, term, other, debug=False):
        assert self is not other

        preds = sorted(s for s, d in self.map.items() if term in d)
        if not preds:
            return self

        other_states = sorted(other.map)
        edges = {}
        for p in preds:
            suc = self.map[p][term]
            self.remove_edge(p, term)

            # Copy in the graph
            nmap = {oi: self.add_state() for oi in other_states}
            for oi, d in other.map.items():
                for t, oi2 in d.items():
                    self.add_edge(nmap[oi], t, nmap[oi2])

            edges[p] = {nmap[other.initial]}
            for ofs in other.final:
                edges[nmap[ofs]] = {suc}

            if debug:
                print p, 'nmap', nmap

        return self.with_epsilon(edges, debug=debug)

    def debug(self, rn='-'):
        print '\n{} -> {}'.format(rn, self.initial)
        for s, d in sorted(self.map.items()):
            suf = '*' if s in self.final else ''
            transitions = ', '.join('{} -> {}'.format(k, v) for k, v in sorted(d.items()))
            print '  {}{}: {}'.format(s, suf, transitions)


# tests
if __name__ == "__main__":
    dfa = DFA()
    dfa.initial = dfa.add_state()
    dfa.add_state()
    dfa.final.update([1,2])

    dfa.add_edge(1, 'a', 2)
    dfa.add_edge(2, 'a', 2)
    dfa.add_edge(2, 'b', 2)

    dfa.simplify()
    assert len(dfa.map) == 2
