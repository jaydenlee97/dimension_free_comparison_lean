"""Small fail-closed lexical helpers for the project's Lean source audits.

This is not a Lean parser; compilation remains mandatory. Comments and strings
are blanked without changing line positions, including nested block comments.
"""

def strip_comments(text):
    out = list(text)
    i = 0
    depth = 0
    while i < len(text):
        if depth:
            if text.startswith('/-', i):
                depth += 1
                out[i:i + 2] = '  '
                i += 2
            elif text.startswith('-/', i):
                depth -= 1
                out[i:i + 2] = '  '
                i += 2
            else:
                if text[i] != '\n':
                    out[i] = ' '
                i += 1
        elif text.startswith('/-', i):
            depth = 1
            out[i:i + 2] = '  '
            i += 2
        elif text.startswith('--', i):
            while i < len(text) and text[i] != '\n':
                out[i] = ' '
                i += 1
        elif text[i] == '"':
            out[i] = ' '
            i += 1
            closed = False
            while i < len(text):
                if text[i] == '\\':
                    out[i] = ' '
                    i += 1
                    if i < len(text):
                        if text[i] != '\n':
                            out[i] = ' '
                        i += 1
                elif text[i] == '"':
                    out[i] = ' '
                    i += 1
                    closed = True
                    break
                else:
                    if text[i] != '\n':
                        out[i] = ' '
                    i += 1
            if not closed:
                raise ValueError('unclosed string literal')
        else:
            i += 1
    if depth:
        raise ValueError('unclosed block comment')
    return ''.join(out)
