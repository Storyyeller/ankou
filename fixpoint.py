from collections import defaultdict

class SetStack(object):
    def __init__(self):
        self.stack = []
        self.s = set()

    def append(self, val):
        if val not in self.s:
            self.stack.append(val)
            self.s.add(val)

    def pop(self):
        v = self.stack.pop()
        self.s.remove(v)
        return v

    def extend(self, vals):
        for v in vals:
            self.append(v)

    def __len__(self):
        return len(self.stack)


class Fixpoint(object):
    def __init__(self, f, initial_val=None):
        self.f = f
        self.initial_val = initial_val

        self.stack = SetStack()
        self.vals = {}
        self.rdeps = defaultdict(list)
        self.last_del_vals = {} # k => k2 => last_val
        self.frozen = {}
        self.iter = 0

    def eval_sub(self, k):
        if k in self.frozen:
            return

        if k in self.vals:
            # first_time = False
            last_vals = self.last_del_vals[k]
            if all(self.vals[k2] == v for k2, v in last_vals.items()):
                return
        else:
            # first_time = True
            self.vals[k] = self.initial_val

        old_val = self.vals[k]
        dep_vals = {}
        self.last_del_vals[k] = dep_vals

        def cb(k2):
            # print 'dep', k, '->', k2
            if k2 in self.frozen:
                # print 'froze dep', k, '->', k2, '->', self.frozen[k2]
                return self.frozen[k2]

            if k2 not in self.vals:
                self.eval_sub(k2)
                if k2 in self.frozen:
                    # print 'froze dep', k, '->', k2, '->', self.frozen[k2]
                    return self.frozen[k2]

            dep_vals[k2] = val = self.vals[k2]
            # print 'var dep', k, '->', k2, '->', val
            return val

        res = self.f(cb, k, old_val)
        # print 'f({}) -> {} deps {}'.format(k, len(res) if res else None, len(deps))

        for k2 in dep_vals:
            self.rdeps[k2].append(k)

        if not dep_vals:
            self.frozen[k] = res

        if res != old_val:
            self.stack.extend(self.rdeps[k])
            self.rdeps[k] = []

        self.vals[k] = res
        if k in self.frozen:
            assert res == self.frozen[k]


    def eval(self, k):
        self.eval_sub(k)
        while self.stack:
            k2 = self.stack.pop()
            self.iter += 1
            self.eval_sub(k2)

        for k2, v in self.vals.items():
            assert self.frozen.get(k2, v) == v
            self.frozen[k2] = v

        # print 'eval', k, self.frozen[k]
        return self.frozen[k]






