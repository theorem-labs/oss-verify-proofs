#!/usr/bin/env python3
"""qcsplit-B.py STAGE STAGE_OUT OUT_PATCH: B-qcache.patch, the donor's `0x32dd0 beq a4,a1` case split in B/YFgg.v and
B/YFgh.v undone where the image does not need it.

The donor's postfix patch (commit dfa268302f2, proofs/libreac/fuzz_decode/provenance/core-reloc/B/postfix/B_YFgg.v.patch
and B_YFgh.v.patch, sha256 5ac4c18d5930 for the first) inserted 5 lines into each file: on libreac fuzz_decode.asan-ubsan
`&cache_ = A_QUAR + 160` and the thread's cache `T + t_qc` are equal mod 4096 (A_QUAR + 160 - t_qc = 0x9e000, page
aligned), so the symbolic executor keeps both sides of the branch and the equal one is refuted from the layout bound.
The rule, computed here from each image's own text (A_QUAR = A_ALLOCATOR + o_quar, B/YFl1.v and Reusable/YG0f.v;
t_qc, Reusable/YG0f.v): when (A_ALLOCATOR + o_quar + 160 - t_qc) mod 4096 is not 0, the executor decides the branch by
alignment and the inserted split has no goal to prove, as in fuzz_grant's released lib/B/YFgg.v / YFgh.v, which have no
such lines. The script prints both images' values (the donor's 0 is the control) and refuses (exit 1) when the target's
value is 0. It removes exactly the 5 inserted lines (the comment line the donor added with them included) from the
text without port_core's own provenance line; nothing else changes."""
import difflib, os, re, sys

stage, so, outp = sys.argv[1:4]
HEAD = re.compile(r'^\(\* Modified by Theorem Labs, \d{4}-\d{2}: copied from proofs/libreac/fuzz_decode/lib/')
BLOCK = [
    "(* 0x32dd0 beq a4,a1 (&cache_ = A_QUAR + 160 against the thread's cache T + t_qc): on this image A_QUAR + 160 = T + "
    "t_qc mod 4096, so the executor keeps both sides; the equal one puts the thread object at 0x9e000, inside the image, "
    "against zone3 of LYB. *)",
    'srr_branch_sh tfibtbl_rtG_ok HS.',
    '{ exfalso. clear - Hc DR LB R32. zbranch Hc. apply Z.eqb_eq in Hc. destruct LB as (ZT & _). clear - Hc ZT. zlia. }',
    'clear Hc. unfold YP06.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS.',
    'srr_run_sh tfibtbl_rtG_ok HS. meq0_acc SK0.']


def val(root, rel, name):
    m = re.search(r'Definition %s : Z := (0x[0-9a-f]+|\d+)\.' % name, open(os.path.join(root, rel)).read())
    return int(m.group(1), 0)


for who, root in (('libreac fuzz_decode.asan-ubsan (control, donor text)', stage), ('libdiginet fuzz_transport.asan-ubsan', so)):
    a, oq, tq = val(root, 'B/YFl1.v', 'A_ALLOCATOR'), val(root, 'Reusable/YG0f.v', 'o_quar'), val(root, 'Reusable/YG0f.v', 't_qc')
    r = (a + oq + 160 - tq) % 4096
    print(f'{who}: A_ALLOCATOR {a:#x} + o_quar {oq} + 160 - t_qc {tq} = {a + oq + 160 - tq:#x}; mod 4096 = {r}')
if r == 0:
    sys.exit('the target needs the split (value 0 mod 4096): no patch')
out = []
for rel in ('B/YFgg.v', 'B/YFgh.v'):
    lines = open(os.path.join(so, rel)).read().split('\n')
    h = [i for i, l in enumerate(lines) if HEAD.match(l)]
    assert len(h) <= 1, (rel, len(h))   # port_core 83f5203d2a2f writes no such line before --patch (item 92)
    text = lines[:h[0]] + lines[h[0] + 1:] if h else lines
    hits = [i for i in range(len(text) - len(BLOCK) + 1) if text[i:i + len(BLOCK)] == BLOCK]
    if len(hits) != 1:
        sys.exit(f'{rel}: the inserted block occurs {len(hits)} times (want 1)')
    new = text[:hits[0]] + text[hits[0] + len(BLOCK):]
    out += list(difflib.unified_diff([l + '\n' for l in text], [l + '\n' for l in new], fromfile=rel, tofile=rel, n=3))
    print(f'{rel}: the 5-line split removed at line {hits[0] + 1} (text without the provenance line)')
open(outp, 'w').write(''.join(out))
