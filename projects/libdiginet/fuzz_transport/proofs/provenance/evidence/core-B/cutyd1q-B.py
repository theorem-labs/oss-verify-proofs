#!/usr/bin/env python3
"""cutyd1q-B.py STAGE_OUT OUT.patch: B-yd1q-shape.patch for libdiginet/fuzz_transport's image-B core.

B/YD1q.v (the donor's, libreac/fuzz_decode lib/B) Requires `Reusable.YI16 YO08` and `A.DecodeShape`, and takes
`#[local] Existing Instance decode_shape.`. On this unit the image-A core's shape module is lib/A/TransportShape.v,
`#[export] Instance transport_shape : lib_shape := ag_shape kept_shape` (the image-A core's row TCA, 22:09Z), which A/AD1q.v takes by
`Require Import TransportShape` + `#[local] Existing Instance transport_shape.`. So YD1q.v Requires YI16 and
A.TransportShape as A/AD1q.v does, without the donor's dead Require of YO08 (cgif's GIF state text; YD1q.v uses none
of its names, as on decode; YO08.v and YI0j.v are not in --files). Code lines only; the inherited notice lines stay.
Each replaced line must occur exactly once; a fresh unified diff, -p0 from stage-out, 3 lines of context."""
import difflib, sys

so, out = sys.argv[1:3]
f = 'B/YD1q.v'
txt = open(f'{so}/{f}').read().splitlines(keepends=True)
REQ_OLD = ('Require Import YI16 YO08. From OssFuzzTheorems.Proofs.libdiginet.fuzz_transport.lib.A Require Import '
           'DecodeShape.')
REQ_NEW = ('Require Import YI16. From OssFuzzTheorems.Proofs.libdiginet.fuzz_transport.lib.A Require Import '
           'TransportShape.')
INST_OLD, INST_NEW = '#[local] Existing Instance decode_shape.', '#[local] Existing Instance transport_shape.'
new = list(txt)
for old, rep in ((REQ_OLD, REQ_NEW), (INST_OLD, INST_NEW)):
    hits = [i for i, l in enumerate(txt) if old in l and not l.lstrip().startswith('(*')]
    assert len(hits) == 1, (old, hits)
    new[hits[0]] = txt[hits[0]].replace(old, rep, 1)
    print(f'{f} line {hits[0] + 1}: {old!r} -> {rep!r}')
open(out, 'w').write(''.join(difflib.unified_diff(txt, new, f, f, n=3)))
