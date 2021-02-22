import cgi

def coalesce(nodes):
    cur_bold = False
    cur_color = None
    cur_text = ''
    for bold, color, text in nodes:
        if (cur_bold == bold and cur_color == color) or not text.strip():
            cur_text += text
            continue

        if cur_text:
            yield (cur_bold, cur_color, cur_text)
        cur_bold, cur_color, cur_text = bold, color, text
    if cur_text:
        yield (cur_bold, cur_color, cur_text)

def decode_sub(s):
    bold = False
    color = None

    pos = 0
    while pos < len(s):
        temp = s.find('\x1b', pos)
        if temp != -1:
            if temp > pos:
                yield bold, color, s[pos:temp]

            pos = temp + 1
            assert s[pos] == '['
            pos += 1

            if s.startswith('0m', pos):
                bold = False
                color = None
                pos += 2
            elif s.startswith('1m', pos):
                bold = True
                pos += 2
            elif s.startswith('38;5;9m', pos):
                color = 'red'
                pos += 7
            elif s.startswith('38;5;12m', pos):
                color = 'blue'
                pos += 8
            else:
                assert 0
        else:
            yield bold, color, s[pos:]
            break

def to_html(nodes):
    out = ['<pre>']
    for bold, color, text in nodes:
        text = cgi.escape(text)
        classes = []

        if bold:
            classes.append('bold')
        if color is not None:
            classes.append(color)

        if classes:
            out.append('<span class="{}">'.format(' '.join(classes)))
            out.append(text)
            out.append('</span>'.format(' '.join(classes)))
        else:
            out.append(text)
    out.append('</pre>')
    return ''.join(out)

def to_ansi(nodes):
    cur_bold = False
    cur_color = None

    out = []
    for bold, color, text in nodes:
        if (cur_bold and not bold) or (cur_color and not color):
            out.append('\x1b[0m')
            cur_bold = False
            cur_color = None
        if bold and not cur_bold:
            out.append('\x1b[1m')
            cur_bold = True
        if color != cur_color:
            code = {
                'red': 9,
                'green': 10,
                'yellow': 11,
                'blue': 12,
            }[color]
            out.append('\x1b[38;5;{}m'.format(code))
            cur_color = color

        assert '\x1b' not in text
        out.append(text)

    if cur_color or cur_bold:
        out.append('\x1b[0m')
    return ''.join(out)




def decode(s):
    return to_html(decode_sub(s))

# data = open('out.html', 'r').read()
# print decode(data)
