#!/usr/bin/env python3
"""funnel.py -- classify donor_decimals.py rows into explained classes; print the unexplained rest.

Classes, in order:
  NOT-IN-DONOR    the value is no literal (hex or decimal) anywhere in cgif's released lib (--cgif-lib REF:PATH):
                  disco's own numeral that falls inside a cgif object by chance
  SIZE            power of two (+-64), multiple of 1000 or 1024: a size / geometry constant
  ODD-IN-CODE     an odd value inside cgif code: no instruction address (rv64g, 4-byte aligned)
  INSN-IMM        an operand of a decoded instruction (Jal / branch immediates are pc-relative offsets)
  LABEL           a direct argument of mcheck / FCheck / fail / spin / ISpin (port_addr_check 5033540ba83b:82-83)
  DISCO-POINTER   a value in a start-up state (AB0x / YB0x) that lies in a disco section at a disco object (start of a
                  disco function, or in disco's asan_globals descriptors): collected from disco's own run
  UNEXPLAINED     anything else (reported row by row)

This version takes every path as an argument (the image arguments are donor_decimals.py's); its output is the output
of the earlier version (sha256 940cb11df71e...) on the same inputs. Usage:

  funnel.py SCAN.tsv --cgif-lib REF:PATH --git GIT --kit KITDIR --donors-from DIR --cache DIR \\
      --cgif-image BUILD=ELF [...] --target-image BUILD=ELF:SYMS [...]
"""
import argparse, collections, csv, os, re, subprocess, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import donor_decimals as DD

ap = argparse.ArgumentParser()
DD.add_image_args(ap)
ap.add_argument('scan', help='a donor_decimals.py output TSV')
ap.add_argument('--cgif-lib', required=True, help="REF:PATH of cgif's released lib (its literal set)")
a = ap.parse_args()
DD.setup(a)
strip_comments = DD.strip_comments

rows = list(csv.DictReader(open(a.scan), delimiter='\t'))
cref, cpath = a.cgif_lib.split(':', 1)
files = subprocess.run(['git', '-C', a.git, 'ls-tree', '-r', '--name-only', cref, '--', cpath],
                       capture_output=True, text=True).stdout.split()
cg = set()
for f in files:
    if f.endswith('.v'):
        t = strip_comments(subprocess.run(['git', '-C', a.git, 'show', cref + ':' + f], capture_output=True, text=True).stdout)
        for m in re.finditer(r"(?<![\w.'])(0x[0-9a-fA-F]+|\d+)(?![\w.'])", t):
            cg.add(int(m.group(1), 0))


class Lazy(dict):
    """build -> image, made on first use (only the builds the rows name need an image argument)."""
    def __init__(self, make):
        super().__init__()
        self.make = make

    def __missing__(self, b):
        self[b] = self.make(b)
        return self[b]


C = Lazy(DD.cgif_image)
T = Lazy(lambda b: DD.target_image('disco', b))
LAB = re.compile(r'\b(mcheck|FCheck|fail|spin|ISpin)\b[^;]*$')


def cls(r):
    v, b, t = int(r['value']), r['image'], r['text']
    if v not in cg:
        return 'NOT-IN-DONOR'
    p = 1 << (v.bit_length() - 1)
    if min(abs(v - p), abs(v - 2 * p)) <= 64 or v % 1000 == 0 or v % 1024 == 0:
        return 'SIZE'
    if C[b].in_exec(v) and v % 4:
        return 'ODD-IN-CODE'
    if re.search(r'\b(Jal|Jalr|Branch|Beq|Bne|Blt|Bge|Bltu|Bgeu|Lui|Auipc)\b|decode_any', t):
        return 'INSN-IMM'
    i = t.find(r['value'])
    if LAB.search(t[max(0, i - 160):i]):
        return 'LABEL'
    rel = r['file'].split('/lib/')[1]
    if re.match(r'(A/AB|Reusable/YB)\d', rel):
        sec = T[b].sec(v)
        tc = DD.cover(T[b], v)
        if (sec and sec[0] == 'asan_globals') or (tc and tc[1] == v):
            return 'DISCO-POINTER'
    return 'UNEXPLAINED'


out = collections.defaultdict(list)
for r in rows:
    out[cls(r)].append(r)
for k in ('NOT-IN-DONOR', 'SIZE', 'ODD-IN-CODE', 'INSN-IMM', 'LABEL', 'DISCO-POINTER', 'UNEXPLAINED'):
    vals = collections.Counter(r['value'] for r in out[k])
    print(f'{k}\t{len(out[k])} rows\t{len(vals)} values')
print('--- UNEXPLAINED rows')
for r in out['UNEXPLAINED']:
    print('\t'.join([r['tree'], r['image'], r['file'].split('/lib/')[1] + ':' + r['line'], r['value'], r['hexv'], r['cgif'][:70],
                     r['target_same'], r['target_at_v'][:60], r['decl'], r['text'][:150]]))
