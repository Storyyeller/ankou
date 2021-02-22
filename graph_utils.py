def tarjan(nodes, getdeps):
    sccs = []
    counter = 0
    index = {}
    lowlink = {}
    removed = set()
    subtree = []

    stack = [(n, False) for n in nodes]
    while stack:
        n, state = stack.pop()
        if not state:
            # before recursing
            if not n in index:
                id = counter
                counter += 1
                index[n] = lowlink[n] = id
                subtree.append(n)
                stack.append((n, True))
                for n2 in getdeps(n):
                    if not n2 in removed:
                        stack.append((n2, False))
        else:
            # after recursing
            i = index[n]
            for n2 in getdeps(n):
                if n2 in removed:
                    continue

                i2 = index[n2]
                if i2 <= i:
                    lowlink[n] = min(lowlink[n], i2)
                else:
                    lowlink[n] = min(lowlink[n], lowlink[n2])

            if lowlink[n] == i:
                scc = []
                while not scc or scc[-1] != n:
                    scc.append(subtree.pop())
                    removed.add(scc[-1])
                sccs.append(scc)
    return sccs
