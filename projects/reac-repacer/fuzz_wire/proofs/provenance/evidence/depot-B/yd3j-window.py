#!/usr/bin/env python3
"""yd3j-window.py LIB TWIN TWIN_SHA256 : set the window end of b2_mod_cells_kept in LIB/B/YD3j.v to
page_up(common_flags_dont_use + 0x105) of the target's own unstripped twin (sha256 TWIN_SHA256).

The lemma's rows read common_flags up to the byte at common_flags_dont_use + 0x104, so the window ends at the page above
that cell (knock: 0x1300a8 + 0x105 -> 0x131000, the donor text's value). port_core moved the statement's copy by symbol,
to useCounts + 0xbc0, which is not that page, and derive_overrides_knockB.py's earlier rule gave the proof's copies the
same value. The script replaces that value with the page end in every code line of b2_mod_cells_kept (its statement and
its proof, to Qed.), refuses unless it finds it there at least once and nowhere else in the file's code. It then sets
the three comment phrases that state the window to the target's own values (knock's donor text states knock's): the
window `[lo, end)` in the note on the re-checked values and in the comment above the lemma, and `every row it keeps ends
by <a>`, where lo is the page of the writable PT_LOAD's start (the writable window's low end), end the page end above,
and a = common_flags_dont_use + 0x105, the end of the last cell the rows read. Run again on a file that already holds
these values, it changes nothing. One record line per changed line."""
import hashlib, re, sys
from elftools.elf.elffile import ELFFile

lib, twin, pin = sys.argv[1:4]
if hashlib.sha256(open(twin, 'rb').read()).hexdigest() != pin:
    sys.exit('yd3j-window: twin pin mismatch')
elf = ELFFile(open(twin, 'rb'))
syms = {s.name: s['st_value'] for s in elf.get_section_by_name('.symtab').iter_symbols() if s.name}
cf = syms['_ZN11__sanitizer21common_flags_dont_useE']
new = (cf + 0x105 + 0xfff) & ~0xfff
old = syms['_ZN11__sanitizerL9useCountsE'] + 0xbc0
lo = min(s['p_vaddr'] for s in elf.iter_segments() if s['p_type'] == 'PT_LOAD' and s['p_flags'] & 2) & ~0xfff
path = lib + '/B/YD3j.v'
lines = open(path).read().split('\n')


def code(t):
    """the line with comments blanked (nesting kept across lines)"""
    global depth
    out, i = [], 0
    while i < len(t):
        if t.startswith('(*', i):
            depth += 1; i += 2; out.append('  '); continue
        if depth and t.startswith('*)', i):
            depth -= 1; i += 2; out.append('  '); continue
        out.append(' ' if depth else t[i]); i += 1
    return ''.join(out)


depth = 0
codes = [code(l) for l in lines]
st = [i for i, c in enumerate(codes) if re.match(r'\s*Lemma b2_mod_cells_kept\b', c)]
if len(st) != 1:
    sys.exit('yd3j-window: %d statements of b2_mod_cells_kept' % len(st))
qed = next(i for i in range(st[0], len(codes)) if re.search(r'\bQed\.', codes[i]))
tok = lambda v: re.compile(r'(?<![\w.])%#x(?![\w.])' % v)
inside = [i for i in range(st[0], qed + 1) if tok(old).search(codes[i])]
outside = [i + 1 for i, c in enumerate(codes) if tok(old).search(c) and not st[0] <= i <= qed]
if outside:
    sys.exit('yd3j-window: %#x also in code lines %s outside b2_mod_cells_kept' % (old, outside))
if not inside:
    if not any(tok(new).search(codes[i]) for i in range(st[0], qed + 1)):
        sys.exit('yd3j-window: b2_mod_cells_kept holds neither %#x nor %#x' % (old, new))
    print('yd3j-window: b2_mod_cells_kept already ends its window at %#x' % new)
for i in inside:
    spans = [m.span() for m in tok(old).finditer(codes[i])]
    l = lines[i]
    for a, b in reversed(spans):
        l = l[:a] + '%#x' % new + l[b:]
    lines[i] = l
    print('B/YD3j.v:%d\t%#x -> %#x\tpage_up(common_flags_dont_use %#x + 0x105); was useCounts %#x + 0xbc0'
          % (i + 1, old, new, cf, syms['_ZN11__sanitizerL9useCountsE']))
# the comment phrases that state the window, each in a comment (checked), each with the target's values
H = r'0x[0-9a-f]+'
PHRASES = [(r"(window \[)(%s)(,\s*)(%s)(\))" % (H, H), lambda m: '%s%#x%s%#x%s' % (m[1], lo, m[3], new, m[5])),
           (r"(low end )(%s)(, as YD3g\.v:21-23; every row it keeps ends by )(%s)" % (H, H),
            lambda m: '%s%#x%s%#x' % (m[1], lo, m[3], cf + 0x105)),
           (r"(misses \[)(%s)(, )(%s)(\))" % (H, H), lambda m: '%s%#x%s%#x%s' % (m[1], lo, m[3], new, m[5]))]
text = '\n'.join(lines)
starts = [0]
for l in lines:
    starts.append(starts[-1] + len(l) + 1)
for pat, rep in PHRASES:
    ms = list(re.finditer(pat, text))
    if len(ms) != 1:
        sys.exit('yd3j-window: the comment phrase %r occurs %d times' % (pat, len(ms)))
    m = ms[0]
    ln = next(k for k in range(len(lines)) if starts[k + 1] > m.start())
    if codes[ln][m.start() - starts[ln]] != ' ':
        sys.exit('yd3j-window: the phrase at line %d is not in a comment' % (ln + 1))
    r = rep(m)
    if r != m[0]:
        text = text[:m.start()] + r + text[m.end():]
        print('B/YD3j.v:%d\tcomment %r -> %r' % (ln + 1, ' '.join(m[0].split()), ' '.join(r.split())))
open(path, 'w').write(text)
