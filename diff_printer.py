import re

# from lexer import lex_file_raw
import sgr

# TOK_DISPLAY_MAP = {}
INSERT_COLOR = 'green'
DELETE_COLOR = 'red'
CONTEXT_LINES = 2

# tokens_src = open('tokens.java', 'r').read()
# for tok, s, e in lex_file_raw(tokens_src):
#     TOK_DISPLAY_MAP[tok] = tokens_src[s:e]


RSPACE_CHARS = 'abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_' + ';,-'
LSPACE_CHARS = 'abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_' + '-'


def print_changes(lex, src, change_list):
    change_list = change_list[::-1]
    src = src + '\n'

    line_changes = []
    pos = 0
    for i, line in enumerate(src.splitlines(True)):
        line_end_pos = pos + len(line)

        has_changes = False
        parts1 = []
        parts2 = []
        while change_list and change_list[-1][1] < line_end_pos:
            has_changes = True
            change = change_list.pop()
            cpos = change[1]

            if cpos > pos:
                parts1.append((None, src[pos:cpos]))
                parts2.append((None, src[pos:cpos]))
                pos = cpos


            if change[0] == 'Insert':
                _, _, tok = change
                # inserted = TOK_DISPLAY_MAP.get(tok, tok)
                inserted = lex.examples[tok]

                # print inserted, re.match(r'\A[a-zA-Z]\w*\Z', inserted)
                # if re.match(r'\A[a-zA-Z]\w*\Z', inserted):
                #     # Hack: make sure there are spaces around words
                #     if parts2 and re.match(r'\w', parts2[-1][-1][-1]):
                #         inserted = ' ' + inserted

                parts2.append((INSERT_COLOR, inserted))

            elif change[0] == 'Delete':
                _, _, end = change
                assert end > cpos
                parts1.append((DELETE_COLOR, src[cpos:end]))
                pos = end

        if pos < line_end_pos:
            parts1.append((None, src[pos:line_end_pos]))
            parts2.append((None, src[pos:line_end_pos]))
        pos = line_end_pos

        # temp hack - heuristic to insert spaces between tokens
        for i, (color, text) in enumerate(parts2):
            if color != INSERT_COLOR:
                continue
            assert has_changes
            assert text
            if text[0] in LSPACE_CHARS:
                if i > 0 and parts2[i-1][1][-1] in RSPACE_CHARS:
                    text = ' ' + text
            if text[-1] in RSPACE_CHARS:
                if i + 1 < len(parts2) and parts2[i+1][1][0] in LSPACE_CHARS:
                    text = text + ' '
            parts2[i] = color, text


        line_changes.append((has_changes, parts1, parts2))
    assert not change_list

    # if change_list:
    #     # line_changes.append((len(change_list), '\n', ' '.join(tok for _, _, tok in change_list[::-1]) + '\n'))
    #     line_changes.append((len(change_list), '\n',
    #         ' '.join(TOK_DISPLAY_MAP.get(tok, tok) for _, _, tok in change_list[::-1]) + '\n'))


    out_parts = []
    for i, (has_changes, parts1, parts2) in enumerate(line_changes):
        if has_changes:
            if any((color or text.strip()) for color, text in parts1):
                out_parts.append((DELETE_COLOR, '- '))
                out_parts.extend(parts1)
            if any((color or text.strip()) for color, text in parts2):
                out_parts.append((INSERT_COLOR, '+ '))
                out_parts.extend(parts2)
        else:
            assert parts1 == parts2
            window = max(0, i - CONTEXT_LINES), min(len(line_changes), i + 1 + CONTEXT_LINES)
            if any(line_changes[i2][0] for i2 in range(*window)):
                out_parts.append((None, '  '))
                out_parts.extend(parts1)

    out_parts = [(False, color, text) for color, text in out_parts]
    out_parts = list(sgr.coalesce(out_parts))
    # return sgr.to_html(out_parts)
    return sgr.to_ansi(out_parts)
    return ''.join(text for color, text in out_parts)
    # return ''.join(out_parts)
