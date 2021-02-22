import collections
import itertools
import json
import os
import re
import sys
import time

import lexgen


LRTable = collections.namedtuple('LRTable', 'TOKMAP, actions, rev_actions, jumps')

t0 = time.time()

lexdata = json.load(open('lexer.json', 'r'))
examples, rules = lexdata
# lex = lexgen.load_from_json(lexdata)

# TOKMAP, start_state, table, stack_cost_map = json.load(open('lrtable.json', 'r'))
TOKMAP, start_state, initial_symbol, action_table, rev_action_table, jump_table = json.load(open('lrtable.json', 'r'))
table = LRTable(TOKMAP, action_table, rev_action_table, jump_table)
print 'json load time', time.time() - t0


out = []
all_toks = set()
for is_regex, s, tok in rules:
    all_toks.add(TOKMAP.get(tok, tok))
all_toks.remove(lexgen.IGNORE)


EOF = 'EOF'
toks_used = set()
for actions in table.actions:
    toks_used.update(actions)
# toks_used.remove(EOF)

illegal_toks = sorted(all_toks - toks_used)
print 'Unused toks', illegal_toks
assert len(illegal_toks) <= 1

toks_flat = sorted(toks_used)
# toks_flat.append(EOF)
toks_flat += illegal_toks
toks_flat.append(lexgen.IGNORE)

tok_rmap = {tok: i for i, tok in enumerate(toks_flat)}

out.append('''// This file was generated by Ankou. Do not edit it directly.
#![allow(non_camel_case_types)]


#[derive(Copy, Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub enum TokTy {''');
for tok in toks_flat:
    out.append('    {} = {},'.format(tok, tok_rmap[tok]))
out.append('}')



out.append('pub static LEXER_RULES: [(bool, &str, TokTy); {}] = ['.format(len(rules)))
for row in rules:
    is_regex, s, tok = row
    if is_regex:
        s = r'\A' + s
        # s = s.replace('\\"', '"')

    root_tok = TOKMAP.get(tok, tok)
    out.append('    ({}, {}, TokTy::{}),'.format(json.dumps(is_regex), json.dumps(s), root_tok))
out.append('];')



examples2 = [None] * len(toks_used)
examples2[tok_rmap[EOF]] = '' # temp hack
for tok, example in sorted(examples.items()):
    root_tok = TOKMAP.get(tok, tok)
    toki = tok_rmap.get(root_tok)
    if toki is not None and toki < len(examples2):
        examples2[toki] = example
out.append('pub static LEXER_EXAMPLES: [&str; {}] = ['.format(len(examples2)))
for example in examples2:
    out.append('    {},'.format(json.dumps(example)))
out.append('];')




reduce_keys = set()
for actions in table.actions + table.jumps:
    for action in actions.values():
        if action[0] == 'Reduce':
            _, rn, _ = action
            if rn != '^':
                reduce_keys.add(rn)
reduce_keys = sorted(reduce_keys)
rk_rmap = {rn: i for i, rn in enumerate(reduce_keys)}
# print 'reduce_keys', reduce_keys



NSTATES = len(table.actions)
NSYMS = len(table.jumps)
NRKEYS = len(reduce_keys)
assert NSTATES <= 65536
assert NSYMS <= 65536
assert NRKEYS <= 65536
state_t = 'u8' if NSTATES <= 256 else 'u16'
sym_t = 'u8' if NSYMS <= 256 else 'u16'
rn_t = 'u8' if NRKEYS <= 256 else 'u16'

out.append('\n\n')
out.append('pub const NSYMS: usize = {};'.format(NSYMS))
out.append('pub type State = {};'.format(state_t))
out.append('pub type Sym = {};'.format(sym_t))
out.append('pub type ReduceKey = {};'.format(rn_t))
out.append('''
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum Action {
    Accept,
    Shift(State, &'static [Sym]),
    Reduce(ReduceKey),
}
use Action::*;
''')

# Number of tokens which the lexer may emit (i.e. not counting IGNORE)
NTOKS = tok_rmap[lexgen.IGNORE]

out.append('pub static ACTIONS: [[Option<Action>; {}]; {}] = ['.format(NTOKS, NSTATES))
for actions in table.actions:
    parts = ['None'] * NTOKS
    for tok, action in actions.items():
        tok_i = tok_rmap[tok]
        if action[0] == 'Shift':
            actcode = 'Shift({}, &{})'.format(*action[1:])
        elif action[0] == 'Reduce':
            if action[1] == '^':
                actcode = 'Accept'
            else:
                actcode = 'Reduce({})'.format(rk_rmap[action[1]])
        parts[tok_i] = 'Some({})'.format(actcode)
    out.append('    [{}],'.format(', '.join(parts)))
out.append('];')

out.append('pub static JUMPS: [[Option<Action>; {}]; {}] = ['.format(NRKEYS, NSYMS))
for actions in table.jumps:
    parts = ['None'] * NRKEYS
    for rn, action in actions.items():
        rn_i = rk_rmap[rn]
        if action[0] == 'Shift':
            actcode = 'Shift({}, &{})'.format(*action[1:])
        elif action[0] == 'Reduce':
            assert action[1] != '^'
            actcode = 'Reduce({})'.format(rk_rmap[action[1]])
        parts[rn_i] = 'Some({})'.format(actcode)
    out.append('    [{}],'.format(', '.join(parts)))
out.append('];')

out.append('pub const INITIAL_STATE: State = {};'.format(start_state))
out.append('pub const INITIAL_SYM: Sym = {};'.format(initial_symbol or 0))
# print 'toks used', sorted(toks_used)

# tok_int_map = {tok: i for i, tok in enumerate(sorted(toks_used))}
# ILLEGAL = len(tok_int_map) + 1
# IGNORE = len(tok_int_map) + 2


# rules2 = []



# data2 = ILLEGAL, IGNORE, rules2, examples2
# print 'data2', data2


# print '\n'.join(out)

with open('/home/rsg/ICS/cubiml-demo/src/ankou/generated.rs', 'w') as f:
    f.write('\n'.join(out))
