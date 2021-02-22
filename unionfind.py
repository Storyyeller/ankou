# Classic union-find data structure except that we don't bother with weighting trees and singletons are implicit
class UnionFind(object):
    def __init__(self):
        self.d = {}

    def find(self, x):
        if x not in self.d:
            return x
        path = [x]
        while path[-1] in self.d:
            path.append(self.d[path[-1]])
        root = path.pop()
        for y in path:
            self.d[y] = root
        return root

    def union(self, x, x2):
        root1, root2 = self.find(x), self.find(x2)
        if root1 != root2:
            self.d[root2] = root1
