#!/usr/bin/env python3
"""rule_acej.py -- the allocation-trace universe A/ACej.v (B/YCej.v) against a fresh gen_traces.py run on our pinned
image + twin, and the triage of the value gate's flagged rows of that file.

    rule_acej.py --file F.v --rel lib/A/ACej.v --gen GEN.v --pin PIN --twin TWIN --kit KIT --donor-pin DPIN
                 --donor-twin DTWIN --rows RUN.gen.tsv --out-rows R.tsv --out-check C.tsv

GEN.v is gen_traces.py's output for our image (every caller of the malloc / free interceptors); the --ipc values it
was run with are measured here as well: the return address of the second GetCurrentPc call (the Unwind branch of
GET_STACK_TRACE_MALLOC) in ___interceptor_malloc / ___interceptor_free.
Checks:
  IPC          the two singletons of Tfib_universe are those return addresses (measured by decoding the interceptors)
  TRACES-GEN   TRACES_main and TRACES_target_run of the file equal gen_traces' TRACES_main / TRACES_target_run
  UNIVERSE     Tfib_universe = the two singletons ++ TRACES_main ++ TRACES_target_run, i.e. the prefix closure of the
               kept traces (the file's own comment says why only the driver's traces are kept: C5)
  NO-FP        main and target_run never set s0 from sp, so the fast unwinder stops after the call site (2-entry traces)
Every flagged row of these files is a donor numeral with no ported value (UNPAIRED-SOURCE): it is resolved in the donor
image (FUNC + offset) and reported with what our image has for that function.
"""
import argparse
import collections
import csv
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import imgfacts  # noqa: E402

LISTDEF = re.compile(r"Definition\s+(\w+)\s*:\s*list \(list Z\)\s*:=\s*(.*?)\.\s*(?=\n|$)", re.S)


def parse(text):
    """{name: [tuple]} of every `Definition N : list (list Z) := ...` (literal lists and `++` of names)."""
    text = re.sub(r'\(\*.*?\*\)', ' ', text, flags=re.S)
    out = {}
    for m in LISTDEF.finditer(text):
        name, body = m.group(1), m.group(2)
        acc = []
        for part in body.split('++'):
            part = part.strip()
            if part.startswith('['):
                acc += [tuple(int(x, 16) for x in re.findall(r'0x[0-9a-fA-F]+', t))
                        for t in re.findall(r'\[([^\[\]]*)\]', part)]
            elif part in out:
                acc += out[part]
            else:
                raise ValueError(f'{name}: cannot read {part[:40]!r}')
        out[name] = acc
    return out


def ipc_of(img, kit):
    sys.path.insert(0, kit)
    import rvelf  # noqa: E402
    gcp = {v for v, z, t in img.byname.get('_ZN11__sanitizer10StackTrace12GetCurrentPcEv', [])}
    out = {}
    for nm in ('___interceptor_malloc', '___interceptor_free'):
        v, z, t = next(x for x in img.byname[nm] if x[2] == 'STT_FUNC')
        o = img.file_off(v)
        c = rvelf.Code(img.data[o:o + z], v)
        rets = [pc + c.lens[k] for k, pc in enumerate(c.pcs) if c.sens[k] and c.sens[k][0] == 'jal'
                and c.sens[k][1] in gcp]
        out[nm] = rets
    return out


def no_fp(img, kit, fn):
    """True when FUNC fn never makes s0 a frame pointer: no `addi s0, sp, k`, `c.addi4spn s0, sp, k` or `c.mv s0, sp`."""
    sys.path.insert(0, kit)
    import rvelf  # noqa: E402
    v, z, t = next(x for x in img.byname[fn] if x[2] == 'STT_FUNC')
    o = img.file_off(v)
    c = rvelf.Code(img.data[o:o + z], v)
    for k in range(len(c.pcs)):
        w = c.raws[k]
        if c.lens[k] == 4 and (w & 0x707f) == 0x13 and ((w >> 7) & 31) == 8 and ((w >> 15) & 31) == 2:
            return False
        if c.lens[k] == 2 and (w & 0xe003) == 0x0 and ((w >> 2) & 7) == 0 and w != 0:
            return False
        if c.lens[k] == 2 and (w & 0xf003) == 0x8002 and ((w >> 7) & 31) == 8 and ((w >> 2) & 31) == 2:
            return False
    return True


def closure(traces):
    s = set()
    for t in traces:
        for j in range(1, len(t) + 1):
            s.add(tuple(t[:j]))
    return s


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    for o in ('--file', '--rel', '--gen', '--pin', '--twin', '--kit', '--donor-file', '--donor-pin', '--donor-twin',
              '--rows', '--out-rows', '--out-check', '--out-ctl'):
        ap.add_argument(o, required=True)
    a = ap.parse_args()
    img = imgfacts.Img(a.pin, a.twin, a.kit)
    dimg = imgfacts.Img(a.donor_pin, a.donor_twin, a.kit)
    F, G = parse(open(a.file).read()), parse(open(a.gen).read())
    DF = parse(open(a.donor_file).read())
    ipc = ipc_of(img, a.kit)
    im, ifr = ipc['___interceptor_malloc'][-1], ipc['___interceptor_free'][-1]
    nofp = {fn: no_fp(img, a.kit, fn) for fn in ('main', 'target_run')}

    def evaluate(F):
        checks = []
        sing = sorted(t for t in F['Tfib_universe'] if len(t) == 1)
        checks.append(('IPC', sing == sorted([(im,), (ifr,)]),
                       f'singletons {[hex(t[0]) for t in sing]}; ___interceptor_malloc GetCurrentPc returns '
                       f'{[hex(x) for x in ipc["___interceptor_malloc"]]}, ___interceptor_free '
                       f'{[hex(x) for x in ipc["___interceptor_free"]]}: the recorded pc is the second (Unwind branch)'))
        for fn in ('main', 'target_run'):
            k = f'TRACES_{fn}'
            same = sorted(F.get(k, [])) == sorted(G.get(k, []))
            checks.append(('TRACES-GEN', same, f'{k}: file {[tuple(hex(x) for x in t) for t in F.get(k, [])]} '
                                               f'{"=" if same else "!="} gen_traces '
                                               f'{[tuple(hex(x) for x in t) for t in G.get(k, [])]}'))
            checks.append(('NO-FP', nofp[fn], f'{fn} has {"no" if nofp[fn] else "an"} s0 := sp + k: the fast '
                                              f'unwinder {"stops" if nofp[fn] else "continues"} after its call site'))
        kept = F.get('TRACES_main', []) + F.get('TRACES_target_run', [])
        uni = set(F['Tfib_universe'])
        want = closure(kept) | {(im,), (ifr,)}
        checks.append(('UNIVERSE', uni == want and len(uni) == len(F['Tfib_universe']),
                       f'Tfib_universe has {len(F["Tfib_universe"])} traces = prefix closure of the {len(kept)} kept '
                       f'traces ({len(want)}); gen_traces finds {len(G["Tfib_universe"])} traces in '
                       f'{len([k for k in G if k.startswith("TRACES_")])} calling functions of the image, of which the '
                       f'file keeps main and target_run'))
        return checks

    checks = evaluate(F)
    others = sorted(k[len('TRACES_'):] for k in G if k.startswith('TRACES_') and k not in ('TRACES_main',
                                                                                         'TRACES_target_run'))
    with open(a.out_check, 'w') as fh:
        for c in checks:
            fh.write(f'{a.rel}\t{c[0]}\t{"OK" if c[1] else "FAIL"}\t{c[2]}\n')
        fh.write(f'{a.rel}\tNOT-KEPT\tINFO\tgen_traces callers not in the file: {", ".join(others)}\n')
    allok = all(c[1] for c in checks)
    # controls: every numeral of the file's kept traces, value + 4 and the donor file's value at the same list,
    # trace and position; the file-level checks must refuse each
    ctl = []
    sing = [t for t in F['Tfib_universe'] if len(t) == 1]
    for k in ('TRACES_main', 'TRACES_target_run'):
        for i, t in enumerate(F[k]):
            for j, v in enumerate(t):
                dl = DF.get(k, [])
                dvs = dl[i][j] if i < len(dl) and j < len(dl[i]) else None
                for kind, w in (('plus4', v + 4), ('donor', dvs)):
                    if w is None:
                        ctl.append((a.rel, k, f'{i}.{j}', hex(v), kind, 'n/a'))
                        continue
                    F2 = dict(F)
                    F2[k] = [tuple(w if (ii, jj) == (i, j) else x for jj, x in enumerate(tt))
                             for ii, tt in enumerate(F[k])]
                    F2['Tfib_universe'] = sing + F2['TRACES_main'] + F2['TRACES_target_run']
                    ok = all(c[1] for c in evaluate(F2))
                    ctl.append((a.rel, k, f'{i}.{j}', hex(v), kind, 'accepted' if ok else 'refused'))
    dsing = sorted(t[0] for t in DF.get('Tfib_universe', []) if len(t) == 1)
    for i, t in enumerate(sorted(sing)):
        for kind, w in (('plus4', t[0] + 4), ('donor', dsing[i] if i < len(dsing) else None)):
            if w is None:
                continue
            F2 = dict(F)
            F2['Tfib_universe'] = [(w,) if s == t else s for s in sing] + F['TRACES_main'] + F['TRACES_target_run']
            ok = all(c[1] for c in evaluate(F2))
            ctl.append((a.rel, 'Tfib_universe', f'singleton{i}', hex(t[0]), kind, 'accepted' if ok else 'refused'))
    with open(a.out_ctl, 'w') as fh:
        for c in ctl:
            fh.write('\t'.join(c) + '\n')
    base = os.path.basename(a.rel)
    rows = [r for r in csv.reader(open(a.rows), delimiter='\t') if r and r[5] == base]
    out = []
    for r in rows:
        if r[11]:
            out.append(r + ['OPEN', 'a ported value; not expected in this file', 'OPEN', '-', '-', '-'])
            continue
        dv = int(r[10], 16)
        f = dimg.func_of(dv)
        fname = f[2] if f else None
        ours = [x for x in img.byname.get(fname, []) if x[2] == 'STT_FUNC'] if fname else []
        gk = f'TRACES_{fname}'
        if fname in ('___interceptor_malloc', '___interceptor_free'):
            what = (f'the donor interceptor\'s recorded pc; ours is {hex(im) if "malloc" in fname else hex(ifr)} '
                    f'(IPC check)')
        elif not ours:
            what = f'our twin has no FUNC {fname}: this donor caller has no counterpart'
        elif fname in ('main', 'target_run'):
            what = f'our {fname}\'s traces are the file\'s TRACES_{fname} (TRACES-GEN check)'
        elif gk in G:
            what = (f'gen_traces finds {len(G[gk])} trace(s) from our {fname}; the file keeps only main / target_run '
                    f'(its own comment: the trace store admits every other trace against an allocator event, C5)')
        else:
            what = f'our {fname} calls neither interceptor (gen_traces lists no trace for it)'
        meas = (f'dst_value empty: {a.rel} holds no numeral for the donor {r[7].split()[-1]} entry {dv:#x} = '
                f'{fname + "+" + hex(dv - f[0]) if f else "no FUNC"} in the donor image; {what}. File-level: '
                + '; '.join(f'{c[0]} {"OK" if c[1] else "FAIL"}' for c in checks))
        out.append(r + ['DONOR-TRACE-NOT-PORTED', meas, 'OK' if allok else 'OPEN', '-', '-', '-'])
    with open(a.out_rows, 'w') as fh:
        for r in out:
            fh.write('\t'.join(r) + '\n')
    print(a.rel, img.describe(), [(c[0], c[1]) for c in checks])
    print('rows', collections.Counter((r[16], r[18]) for r in out).most_common())
    print('controls', sorted(collections.Counter((c[4], c[5]) for c in ctl).items()))


if __name__ == '__main__':
    main()
