#!/usr/bin/env python3
"""kernel-depot-B.py HUB UNIT A_BEFORE A_AFTER BLIB FILE...: the empty-depot kernel hunks for the files an image-B core
keeps PER IMAGE in lib/B (YC5d YCbp YCbq YCe5: lib/Reusable in the image-A core and in knock's release, lib/B in a B
core because they state the image bounds).

The image-A core changes lib/Reusable/<f> from A_BEFORE (grant text, relocated) to A_AFTER (the empty-depot form). The
same change is applied to BLIB/B/<f> (grant's image-B text, relocated):
  - hunks that only add or drop comment lines are skipped (no lane writes a notice line into a copied file);
  - every other hunk is applied with 3 lines of context by position, zero fuzz (patch);
  - a hunk that only adds DepotCfg to a Require sentence fails in B (there the sentence names lib.B modules); it is
    applied as one sentence `From <mod>.lib.Reusable Require Import DepotCfg.` after the file's last Require sentence.
Exit 1 if any other hunk fails; prints per file the hunks applied."""
import difflib, os, re, shutil, subprocess, sys, tempfile

hub, unit, before, after, blib = sys.argv[1:6]
files = sys.argv[6:]
mod = f'OssFuzzTheorems.Proofs.reac_repacer.{unit}.lib'


def show(rev, path):
    r = subprocess.run(['git', 'show', f'{rev}:{path}'], cwd=hub, capture_output=True, text=True)
    if r.returncode:
        sys.exit(f'{rev}:{path} not found')
    return r.stdout


def is_comment(l):
    s = l[1:].strip()
    return s.startswith('(*') and s.endswith('*)')


def adds_depotcfg_only(h):
    m = [l for l in h[1:] if l[:1] == '-']
    p = [l for l in h[1:] if l[:1] == '+']
    return len(m) == len(p) == 1 and p[0][1:].replace(' DepotCfg', '') == m[0][1:]


tmp = tempfile.mkdtemp(prefix='kernel-depot-B-')
bad = 0
for f in files:
    a0 = show(before, f'proofs/reac-repacer/{unit}/lib/Reusable/{f}').split('\n')
    a1 = show(after, f'proofs/reac-repacer/{unit}/lib/Reusable/{f}').split('\n')
    d = list(difflib.unified_diff([l + '\n' for l in a0], [l + '\n' for l in a1], fromfile=f'B/{f}', tofile=f'B/{f}', n=3))
    hunks, cur = [], None
    for l in d[2:]:
        if l.startswith('@@'):
            cur = [l]; hunks.append(cur)
        else:
            cur.append(l)
    keep, req, skipped = [], [], 0
    for h in hunks:
        ch = [l for l in h[1:] if l[:1] in '+-']
        if all(is_comment(l) for l in ch):
            skipped += 1
        elif adds_depotcfg_only(h):
            req.append(h)
        else:
            keep.append(h)
    os.makedirs(f'{tmp}/B', exist_ok=True)
    shutil.copy(f'{blib}/B/{f}', f'{tmp}/B/{f}')
    pf = f'{tmp}/{f}.patch'
    open(pf, 'w').write(''.join(d[:2] + [l for h in keep for l in h]))
    r = subprocess.run(['patch', '--fuzz=0', '--forward', '--batch', '--no-backup-if-mismatch', '-p0', '-d', tmp, '-i', pf],
                       capture_output=True, text=True)
    if r.returncode:
        print(f'B/{f}: patch failed:\n{r.stdout}'); bad += 1; continue
    t = open(f'{tmp}/B/{f}').read()
    if req and 'DepotCfg' not in re.sub(r'\(\*.*?\*\)', '', t, flags=re.S):
        reqs = list(re.finditer(r'From\s+\S+\s+Require\s+(?:Import\s+|Export\s+)?[^.]*\.', t))
        end = reqs[-1].end()
        t = t[:end] + f'\nFrom {mod}.Reusable Require Import DepotCfg.' + t[end:]
    open(f'{blib}/B/{f}', 'w').write(t)
    print(f'B/{f}: {len(keep)} hunks applied, {len(req)} DepotCfg Require hunk(s) as one sentence, {skipped} comment-only skipped')
shutil.rmtree(tmp)
sys.exit(1 if bad else 0)
