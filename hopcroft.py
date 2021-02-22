import collections

class PartitionRefinement2(object):
    def __init__(self, initial_sets):
        self.sets = list(initial_sets)
        # Map each element to its index in the sets table
        self.si_map = {}
        for i, s in enumerate(self.sets):
            for x in s:
                self.si_map[x] = i

    def split(self, s):
        splitmap = {}
        for x in s:
            old_si = self.si_map[x]
            if old_si not in splitmap:
                splitmap[old_si] = len(self.sets)
                self.sets.append(set())
            new_si = splitmap[old_si]

            self.sets[old_si].remove(x)
            self.sets[new_si].add(x)
            self.si_map[x] = new_si

        res = []
        for old_si, new_si in splitmap.items():
            if not self.sets[new_si]:
                continue
            if not self.sets[old_si]:
                # We "split" the entire set into new set - move it back
                self.sets[new_si], self.sets[old_si] = self.sets[old_si], self.sets[new_si]
                for x in self.sets[old_si]:
                    self.si_map[x] = old_si
                continue
            res.append((old_si, new_si))

        while not self.sets[-1]:
            self.sets.pop()
        return res

    def debug(self):
        return sorted(sorted(s) for s in self.sets if s)

def simplify(initial_sets, edges):
    rev_edges = {k: collections.defaultdict(list) for k in edges}
    for k, v in edges.items():
        for tok, k2 in v.items():
            rev_edges[k2][tok].append(k)


    partitions = PartitionRefinement2(initial_sets)
    workset = set(range(len(initial_sets)))

    # for k in (38, 52):
    #     k = 'State', k
    #     si = partitions.si_map[k]
    #     print 'initial set for', k
    #     print si, partitions.sets[si]

    # v1 = 'State', 38
    # v2 = 'State', 52
    # hassplit = False

    while workset:
        si = workset.pop()

        predecessors = collections.defaultdict(set)
        for x in partitions.sets[si]:
            for tok, preds in rev_edges[x].items():
                predecessors[tok].update(preds)

        for tok, preds in predecessors.items():
            split_pairs = partitions.split(preds)
            # if not hassplit and partitions.si_map[v1] != partitions.si_map[v2]:
            #     print 'Split!', partitions.si_map[v1], partitions.si_map[v2]
            #     hassplit = True
            #     print 'split from', tok, preds


            for i1, i2 in split_pairs:
                set1 = partitions.sets[i1]
                set2 = partitions.sets[i2]
                # if (52 in set1 and 38 in set2) or (38 in set1 and 52 in set2):
                #     print 'split', set1, set2

                if i1 in workset:
                    workset.add(i2)
                else:
                    # choose the smaller of the two new sets to add to the work list
                    workset.add(min((i1, i2), key=lambda i:len(partitions.sets[i])))
    return partitions.sets
