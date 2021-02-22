from collections import OrderedDict, defaultdict

import fixpoint

def reduce_insertion_table(table):
    def subsumes(cb, args, best):
        assert isinstance(best, bool)
        if not best:
            return False

        # Return true if q1 accepts at least as many strings than q2
        q1, q2 = args
        if q1 == q2:
            return True

        for tok, action in table.actions[q2].items():
            action2 = table.actions[q1].get(tok)
            if action[0] == 'Reduce':
                if action2 != action:
                    return False
            else:
                assert action[0] == 'Shift'
                if action2 is None or action2[0] != 'Shift':
                    return False

                _, dest1, push1 = action
                _, dest2, push2 = action2
                if push1 != push2:
                    return False

                if not cb((dest1, dest2)):
                    return False
        return True

    f = fixpoint.Fixpoint(subsumes, initial_val=True)

    pruned_count = 0
    new_rev_table = []
    for q, row in enumerate(table.rev_actions):
        selected = [(q, ())]
        new_row = []
        for tok, action, toks in row:
            if action[0] == 'Shift':
                _, dest, pushes = action
                if any(pushes == pushes2 and f.eval((dest2, dest)) for dest2, pushes2 in selected):
                    # print 'pruning', q, tok, action
                    pruned_count += 1
                    continue
                selected.append((dest, pushes))
            new_row.append((tok, action, toks))
        new_rev_table.append(new_row)

    print 'pruned_count', pruned_count
    return new_rev_table

    # tcount = 0
    # fcount = 0
    # t0 = time.time()
    # last_print = time.time()

    # N = len(table.actions)
    # for i in range(N):
    #     for j in range(N):
    #         if i == j:
    #             continue

    #         if f.eval((i, j)):
    #             tcount += 1
    #         else:
    #             fcount += 1

    #         if time.time() > last_print + 1:
    #             last_print = time.time()
    #             print 'subsumes', tcount, fcount, last_print - t0


    #         # print N, i, j, f.eval((i, j))
    # print 'subsumes', tcount, fcount



# import collections
# import json
# import time

# LRTable = collections.namedtuple('LRTable', 'TOKMAP, actions, rev_actions, jumps')

# t0 = time.time()
# # TOKMAP, start_state, table, stack_cost_map = json.load(open('lrtable.json', 'r'))
# TOKMAP, start_state, initial_symbol, action_table, rev_action_table, jump_table = json.load(open('lrtable.json', 'r'))
# table = LRTable(TOKMAP, action_table, rev_action_table, jump_table)
# print 'json load time', time.time() - t0

# reduce_insertion_table(table)
# print 'total time', time.time() - t0



