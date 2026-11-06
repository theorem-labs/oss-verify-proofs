#!/usr/bin/env python3
"""closure_glue.py FILE... -- glue rule (E1), the ONE recorded mechanical rule for the Require-closure files (the
knock-only files AD3a..AD3k, AFk0g, AWalkFw0 and the knock-only kernel files): in their code, the names
YImgTop.IMG_LO / YImgTop.IMG_TOP are deleted from `unfold` lists (imgtop_rule.py; an emptied `unfold` is removed with
its `;` or `.`). Nothing else changes. Each file is rewritten in place; every site is printed as FILE:LINE: before ->
after, and the total. A site the rule cannot handle refuses (exit)."""
import difflib, os, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from imgtop_rule import strip_imgtop_unfold  # noqa: E402
from depot_classify import decomment  # noqa: E402

total = 0
for f in sys.argv[1:]:
    text = open(f).read()
    new, n = strip_imgtop_unfold(text)          # an `unfold` list may span lines
    if n:
        if decomment(new).count('YImgTop.IMG_') != decomment(text).count('YImgTop.IMG_') - n:
            sys.exit('closure_glue: %s: a deleted name sat in a comment' % f)
        a_, b_ = text.split('\n'), new.split('\n')
        for tag, i1, i2, j1, j2 in difflib.SequenceMatcher(None, a_, b_, autojunk=False).get_opcodes():
            if tag != 'equal':
                print('%s:%d: %s  ->  %s' % (f.split('/lib/')[-1], i1 + 1, ' / '.join(x.strip() for x in a_[i1:i2])[:200],
                                             ' / '.join(x.strip() for x in b_[j1:j2])[:200]))
        open(f, 'w').write(new)
    total += n
print('closure_glue: %d name(s) deleted from unfold lists' % total)
