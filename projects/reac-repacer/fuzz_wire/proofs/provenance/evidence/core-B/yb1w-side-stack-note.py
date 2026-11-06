#!/usr/bin/env python3
"""yb1w-side-stack-note.py LIB TWIN_B TWIN_B_SHA256 TWIN_A TWIN_A_SHA256 : empty the donor's side-stack note in
LIB/B/YB1w.v when this unit's images make it false.

The note came from fuzz_grant's released lib/B/YB1w.v with the relocation (port_core copies comments): `Image B links two
side-stack functions that image A does not: their rows are from fuzz_grant.asan-ubsan's symbols (address, address +
size).` There it stood above the rows of __asan_stack_malloc_6 and __asan_stack_free_6. It names the donor's binary, and
for this unit the relocation dropped both rows, because neither image links them. The script measures that on the two
unstripped twins (each checked by its sha256): the __asan_stack_(malloc|free)_N symbols image B links that image A does
not must be NONE, and the file must hold no row of a side-stack function that only image B links. Then the note's line
becomes an empty line, so no declaration moves and every YB1w.v:NNN citation stays true. It refuses unless the note
is exactly one whole line, a comment, and the file's code (comments blanked) is equal before and after. Run again on a
file without the note, it changes nothing. One record line per changed line."""
import hashlib, re, sys
from elftools.elf.elffile import ELFFile

NOTE = ("(* Image B links two side-stack functions that image A does not: their rows are from fuzz_grant.asan-ubsan's "
        "symbols (address, address + size). *)")
lib, twin_b, pin_b, twin_a, pin_a = sys.argv[1:6]


def side_stack(twin, pin):
    """the __asan_stack_(malloc|free)_N symbols the twin links, after its sha256 check"""
    if hashlib.sha256(open(twin, 'rb').read()).hexdigest() != pin:
        sys.exit('yb1w-side-stack-note: twin pin mismatch: %s' % twin)
    st = ELFFile(open(twin, 'rb')).get_section_by_name('.symtab')
    return {s.name for s in st.iter_symbols() if re.fullmatch(r'__asan_stack_(malloc|free)_\d+', s.name)}


def code(text):
    """TEXT with every comment blanked, nesting kept"""
    out, i, depth = [], 0, 0
    while i < len(text):
        if text.startswith('(*', i):
            depth += 1; out.append('  '); i += 2; continue
        if depth and text.startswith('*)', i):
            depth -= 1; out.append('  '); i += 2; continue
        out.append(text[i] if not depth or text[i] == '\n' else ' '); i += 1
    return ''.join(out)


only_b = sorted(side_stack(twin_b, pin_b) - side_stack(twin_a, pin_a))
if only_b:
    sys.exit('yb1w-side-stack-note: image B links side-stack functions image A does not: %s; the note may be true'
             % ', '.join(only_b))
path = lib + '/B/YB1w.v'
text = open(path).read()
rows = re.findall(r'\btfib_[AE]_\w*asan_stack_(?:malloc|free)_(\d+)\b', code(text))
lines = text.split('\n')
at = [i for i, l in enumerate(lines) if l == NOTE]
if not at:
    if NOTE in text:
        sys.exit('yb1w-side-stack-note: the note is not a whole line')
    print('yb1w-side-stack-note: B/YB1w.v holds no such note; nothing to change')
    sys.exit(0)
if len(at) != 1:
    sys.exit('yb1w-side-stack-note: the note occurs on %d lines' % len(at))
i = at[0]
lines[i] = ''
new = '\n'.join(lines)
if ' '.join(code(new).split()) != ' '.join(code(text).split()) or code(new).count('\n') != code(text).count('\n'):
    sys.exit('yb1w-side-stack-note: the code would change')
open(path, 'w').write(new)
print('B/YB1w.v:%d\tnote emptied\tno side-stack function is linked by image B only (both images link %s); the file '
      'keeps side-stack rows for __asan_stack_malloc_ %s only' % (i + 1, ', '.join(sorted(side_stack(twin_b, pin_b))),
                                                                 ', '.join(sorted(set(rows)))))
