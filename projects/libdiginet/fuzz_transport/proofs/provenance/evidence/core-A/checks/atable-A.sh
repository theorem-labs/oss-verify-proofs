#!/bin/bash
# atable-A.sh WORK LIB OUT: item 2 of the TCA value lane, the core side of the atable check for the libdiginet/
# fuzz_transport image-A core relocation (asan pin e89be137db17). libdiginet/fuzz_decode's checks/atable-A.sh
# (sha256 e70b2029bec9; internal record) with the pins, names, paths and the argument list changed.
# atable (registry lineage tools/atable/1ce98fbad397; the start-up set 2026-10-30d carries it as e88affcf0526, whose field
# code is 1ce98fbad397's byte for byte: the two differ only in the notice / host-path blocks, their self-tests and a
# try/except round past_end) makes A/AB12.v, a start-up file; it reads its code fields from a symbol source, which may be
# the function table A/AB1w.v, a CORE file. The core carries the same fields itself: A/AB1w.v's `tfib_at_*` rows. Runs
# (`atable --fields`, the field table as JSON), each through the set's frozen-run.sh as D9 did:
#   donor     fuzz_grant.asan with its twin: every field must equal fuzz_grant's released A/AB12.v record and its released
#             A/AB1w.v tfib_at_* rows (the comparison's baseline)
#   twin      fuzz_transport.asan with its unstripped twin as the symbol source
#   ab1w      fuzz_transport.asan with WORK/stage-out/A/AB1w.v as the symbol source: every field must equal the twin run's
#   rows      WORK/stage-out/A/AB1w.v's tfib_at_* rows against the twin run's fields
#   plant-row a copy of AB1w.v whose tfib_at_x_memset is the donor's (WORK/stage/A/AB1w.v): the rows check must find
#             x_memset alone
#   plant-tab a copy of AB1w.v whose tfib_A_musl_memset / tfib_E_musl_memset are the donor's: the ab1w run on it must give
#             another x_memset than the twin's, or REFUSE
#   lib       LIB/A/AB12.v (the start-up layer the run's LIB holds; a STAND-IN at the old pin in the dry run) against the
#             twin fields: printed, not a gate of the core
#   1ce9      the same twin run with atable.py 1ce98fbad397 itself in place of e88affcf0526 (a copy of the set's bundle
#             with that one row changed, assembled in a temporary directory): its fields must equal the twin run's
# TFIB_TEXT_LO / TFIB_TEXT_N are A/AB12.v's alone (no core file states them); they are printed, not compared.
# Env: SET (default: values/tools/startup-set/2026-10-30d), BUNDLE (startup-set-2026-10-30d.tsv), AT1CE9 (atable.py
# 1ce98fbad397), P, PG, DON (defaults as decval.py; DON = fuzz_grant's released lib, normalised). Output: OUT/atable.txt.
set -uo pipefail
[ $# -eq 3 ] || { echo "usage: atable-A.sh WORK LIB OUT" >&2; exit 2; }
mkdir -p "$3" || exit 2
WORK=$(readlink -f "$1") LIB=$(readlink -f "$2") OUT=$(readlink -f "$3")
HERE=$(dirname "$(readlink -f "$0")")
SS=${SET:-$HERE/tools/startup-set/2026-10-30d}
BUNDLE=${BUNDLE:-startup-set-2026-10-30d.tsv}
AT1CE9=${AT1CE9:-$HERE/tools/atable/1ce98fbad397/atable.py}
P=${P:?set P to the fuzz_transport image tree (result/bin/, unstripped/)}
PG=${PG:?set PG to the fuzz_grant image tree}
DON=${DON:?set DON to the released fuzz_grant lib, normalised}
GB=$PG/bin/fuzz_grant/fuzz_grant.asan; GT=$PG/unstripped/fuzz_grant/fuzz_grant.asan
FB=$P/result/bin/fuzz_transport/fuzz_transport.asan; FT=$P/unstripped/fuzz_transport/fuzz_transport.asan
AT=$SS/frozen/atable.py.frozen-e88affcf0526
TAB=$WORK/stage-out/A/AB1w.v
for f in "$GB" "$GT" "$FB" "$FT" "$AT" "$AT1CE9" "$SS/$BUNDLE" "$TAB" "$WORK/stage/A/AB1w.v" "$DON/A/AB1w.v" "$DON/A/AB12.v"; do
  [ -f "$f" ] || { echo "atable-A: missing $f" >&2; exit 2; }
done
PINS=""
for x in "$GB:c2c7559b29bd" "$GT:57c26f993615" "$FB:e89be137db17" "$FT:86efc3a80314" "$AT:e88affcf0526" "$AT1CE9:1ce98fbad397"; do
  f=${x%:*} want=${x##*:} got=$(sha256sum < "$f" | cut -c1-12)
  [ "$got" = "$want" ] || { echo "atable-A: $(basename "$f") is $got, not the pinned $want" >&2; exit 2; }
  PINS="$PINS $(basename "$(dirname "$(dirname "$f")")")/$(basename "$f") $got;"
done
[ "$(awk -F'\t' '$1 == "atable.py" {print $2}' "$SS/$BUNDLE")" = e88affcf0526 ] || { echo "atable-A: $BUNDLE does not pin atable.py e88affcf0526" >&2; exit 2; }
SUMS=$(cd "$SS" && sha256sum -c --quiet SHA256SUMS 2>&1) || { echo "atable-A: the start-up set's SHA256SUMS do not check: $SUMS" >&2; exit 2; }
LIB12=$([ -f "$LIB/A/AB12.v" ] && echo "$LIB/A/AB12.v" || echo "")
fields() {   # fields NAME IMAGE SYMSRC [SETDIR BUNDLE]: atable --fields, the donor pair = fuzz_grant's image and released AB12
  local s=${4:-$SS} b=${5:-$SS/$BUNDLE}
  bash "$s/frozen-run.sh" "$b" atable.py "$2" "$3" --fields --side A \
    --prefix OssFuzzTheorems.Proofs.libdiginet.fuzz_transport.lib --donor-image "$GB" --donor-atable "$DON/A/AB12.v" \
    > "$OUT/$1.json" 2> "$OUT/$1.err"
  echo "rc=$?" >> "$OUT/$1.err"
}
# the plants, each in a copy; AB1w.v writes a tfib_A_ / tfib_E_ pair on one line, so a definition is matched inside its line
dv() { sed -n "s/.*\bDefinition $1 : Z := \(0x[0-9a-f]*\)\..*/\1/p" "$WORK/stage/A/AB1w.v"; }
DXM=$(dv tfib_at_x_memset) DA=$(dv tfib_A_musl_memset) DE=$(dv tfib_E_musl_memset)
[ -n "$DXM" ] && [ -n "$DA" ] && [ -n "$DE" ] || { echo "atable-A: WORK/stage/A/AB1w.v lacks tfib_at_x_memset / tfib_A_ / tfib_E_musl_memset" >&2; exit 2; }
mkdir -p "$OUT/plant-row" "$OUT/plant-tab"
sed "s/\bDefinition tfib_at_x_memset : Z := 0x[0-9a-f]*\./Definition tfib_at_x_memset : Z := $DXM./" "$TAB" > "$OUT/plant-row/AB1w.v"
sed -e "s/\bDefinition tfib_A_musl_memset : Z := 0x[0-9a-f]*\./Definition tfib_A_musl_memset : Z := $DA./" \
    -e "s/\bDefinition tfib_E_musl_memset : Z := 0x[0-9a-f]*\./Definition tfib_E_musl_memset : Z := $DE./" "$TAB" > "$OUT/plant-tab/AB1w.v"
[ "$(diff "$TAB" "$OUT/plant-row/AB1w.v" | grep -c '^>')" = 1 ] \
  && grep -q "Definition tfib_A_musl_memset : Z := $DA\." "$OUT/plant-tab/AB1w.v" && grep -q "Definition tfib_E_musl_memset : Z := $DE\." "$OUT/plant-tab/AB1w.v" \
  && [ "$(diff "$TAB" "$OUT/plant-tab/AB1w.v" | grep -c '^>')" -ge 1 ] \
  || { echo "atable-A: a plant did not change the expected lines" >&2; exit 2; }
# the 1ce98fbad397 set: the bundle with the atable.py row changed, the frozen copies linked, atable.py 1ce9 added
S2=$(mktemp -d); trap 'rm -rf "$S2"' EXIT
cp "$SS/frozen-run.sh" "$S2/"; mkdir -p "$S2/frozen"; ln -s "$SS/pautrlen" "$S2/pautrlen"
for f in "$SS"/frozen/*; do ln -s "$f" "$S2/frozen/$(basename "$f")"; done
cp "$AT1CE9" "$S2/frozen/atable.py.frozen-1ce98fbad397"
for f in "$SS"/*.py; do ln -s "$f" "$S2/$(basename "$f")"; done
sed 's/^atable\.py\te88affcf0526$/atable.py\t1ce98fbad397/' "$SS/$BUNDLE" > "$S2/bundle-1ce9.tsv"
fields donor "$GB" "$GT"
fields twin "$FB" "$FT"
fields ab1w "$FB" "$TAB"
fields plant-tab "$FB" "$OUT/plant-tab/AB1w.v"
fields twin-1ce9 "$FB" "$FT" "$S2" "$S2/bundle-1ce9.tsv"
python3 - "$OUT" "$TAB" "$OUT/plant-row/AB1w.v" "$DON/A/AB1w.v" "$DON/A/AB12.v" "$PINS" "$DXM" "$LIB12" > "$OUT/atable.txt" <<'PY'
import json, os, re, sys
out, tab, prow, dtab, dab12, pins, dxm, lib12 = sys.argv[1:]
num = lambda s: int(s, 0) if isinstance(s, str) else s
def js(name):
    t = open(os.path.join(out, name + '.json')).read()
    if not t.strip():
        return None
    return {k: ([num(x[0]) for x in v] if k == 'stops_more' else num(v[0])) for k, v in json.loads(t).items()}
def err(name):
    return [l for l in open(os.path.join(out, name + '.err')).read().splitlines() if not l.startswith('frozen-run')]
def bund(name):
    return [l.split(':', 1)[1].strip() for l in open(os.path.join(out, name + '.err')).read().splitlines() if l.startswith('frozen-run:   atable.py')]
def rows(path):           # A/AB1w.v's tfib_at_* rows
    t = open(path).read()
    r = {m.group(1): int(m.group(2), 0) for m in re.finditer(r'^Definition tfib_at_(\w+) : (?:Z|nat) := (0x[0-9a-fA-F]+|\d+)(?:%nat)?\.$', t, re.M)}
    m = re.search(r'^Definition tfib_at_stops_more : list Z := \((.*?) :: nil\)%list\.$', t, re.M)
    r['stops_more'] = [int(x, 0) for x in m.group(1).split(' :: ')] if m else None
    return r
def record(path):         # a released AB12.v's TFIB record and TFIB_TEXT pair
    t = open(path).read()
    body = t[t.index('{|'):t.index('|}')]
    r = {k: int(v, 0) for k, v in re.findall(r'(\w+) := (0x[0-9a-fA-F]+|\d+)', body)}
    r['stops_more'] = [int(x, 0) for x in re.search(r'stops_more := \[([^\]]*)\]', body).group(1).split(';')]
    for k in ('TFIB_TEXT_LO', 'TFIB_TEXT_N'):
        m = re.search(r'Definition %s : \w+ := (0x[0-9a-fA-F]+|\d+)\.' % k, t)
        if m:
            r[k] = int(m.group(1), 0)
    return r
def cmp(f, r):            # [(field, fields value, rows value)] that differ; stops: r's list must be f's first len(r) sites
    bad, extra = [], []
    for k, v in r.items():
        if k == 'stops_more':
            if v is None or f[k][:len(v)] != v:
                bad.append((k, f[k], v))
            extra = f[k][len(v or []):]
        elif f.get(k) != v:
            bad.append((k, f.get(k), v))
    return bad, extra
hx = lambda v: '[%s]' % ' '.join(map(hex, v)) if isinstance(v, list) else (hex(v) if isinstance(v, int) else str(v))
res = {}
print('# pins:%s atable e88affcf0526 through the 2026-10-30d set\'s frozen-run.sh (and 1ce98fbad397 for the cross-run); donor pair fuzz_grant.asan + its released A/AB12.v' % pins)
D, T, A, PT, T1 = js('donor'), js('twin'), js('ab1w'), js('plant-tab'), js('twin-1ce9')
for n in ('donor', 'twin', 'ab1w', 'plant-tab', 'twin-1ce9'):
    print('# %s (bundle atable.py %s)' % (n, ' '.join(bund(n))))
    print('\n'.join(l for l in err(n) if re.match(r'past-end|atable:|rc=', l)))
print('# compare')
bd, ed = cmp(D, record(dab12)); bd2, _ = cmp(D, rows(dtab))
res['donor'] = not bd and not bd2
print('donor: fuzz_grant fields vs its released A/AB12.v record: %d of %d differ%s; vs its released A/AB1w.v tfib_at_* rows: %d differ: %s' % (
    len(bd), len(record(dab12)), ''.join('; %s %s/%s' % (k, hx(a), hx(b)) for k, a, b in bd), len(bd2), 'PASS' if res['donor'] else 'FAIL'))
same = T is not None and A is not None and T == A
res['ab1w'] = same
print('ab1w: fuzz_transport fields from stage-out/A/AB1w.v vs from the twin: %s (%d fields)%s: %s' % (
    'equal' if same else 'DIFFER', len(T or {}), '' if same else ': ' + ', '.join(k for k in (T or {}) if T.get(k) != (A or {}).get(k)),
    'PASS' if same else 'FAIL'))
br, er = cmp(T, rows(tab))
res['rows'] = not br
print('rows: stage-out/A/AB1w.v tfib_at_* (%d rows) vs the twin fields: %d differ%s; stops_more: the %d listed = the image\'s first %d self-loops, '
      'atable appends %s (not in the core row): %s' % (len(rows(tab)), len(br), ''.join('; %s %s/%s' % (k, hx(a), hx(b)) for k, a, b in br),
                                                    len(rows(tab)['stops_more'] or []), len(rows(tab)['stops_more'] or []), hx(er), 'PASS' if res['rows'] else 'FAIL'))
s1 = T is not None and T1 is not None and T == T1
res['1ce9'] = s1
print('1ce9: the twin run with atable.py 1ce98fbad397 vs e88affcf0526: %s (%d fields): %s' % ('equal' if s1 else 'DIFFER', len(T1 or {}), 'PASS' if s1 else 'FAIL'))
print('not in the core: TFIB_TEXT_LO %s, TFIB_TEXT_N %d (A/AB12.v, start-up; no stage-out file states them)' % (hx(T['TFIB_TEXT_LO']), T['TFIB_TEXT_N']))
if lib12:
    bl, el = cmp(T, record(lib12))
    print('lib (not a gate of the core): LIB/A/AB12.v record vs the twin fields: %d of %d differ%s' % (
        len(bl), len(record(lib12)), ''.join('; %s %s/%s' % (k, hx(a), hx(b)) for k, a, b in bl)))
print('# controls')
bp, _ = cmp(T, rows(prow))
ok = [k for k, _, _ in bp] == ['x_memset'] and bp[0][2] == int(dxm, 0)
print('plant-row: tfib_at_x_memset -> %s (the donor\'s): %d row(s) differ (%s): %s' % (
    dxm, len(bp), ', '.join('%s %s/%s' % (k, hx(a), hx(b)) for k, a, b in bp), 'PASS' if ok else 'FAIL'))
refused = [l for l in err('plant-tab') if 'REFUSED' in l or 'NOT EMITTED' in l]
diff = [k for k in T if PT is not None and T.get(k) != PT.get(k)]
ok2 = bool(refused) or 'x_memset' in diff
print('plant-tab: tfib_A_ / tfib_E_musl_memset -> the donor\'s: %s: %s' % (
    ('atable ' + refused[0]) if refused else ('fields differ from the twin run in %s (x_memset %s)' % (', '.join(diff) or 'none', hx(PT.get('x_memset')) if PT else '-')),
    'PASS' if ok2 else 'FAIL'))
sys.exit(0 if res['donor'] and res['ab1w'] and res['rows'] and res['1ce9'] and ok and ok2 else 1)
PY
echo "rc=$?" >> "$OUT/atable.txt"
cat "$OUT/atable.txt"
