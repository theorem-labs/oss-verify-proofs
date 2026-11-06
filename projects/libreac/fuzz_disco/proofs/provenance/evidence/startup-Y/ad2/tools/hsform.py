#!/usr/bin/env python3
"""hsform.py -- turn the collector dumps (colrun.py Pass1/Pass2 build logs) into the donor's files:

  hsform.py hs  LOG OUT.v --header DONOR_AB01.v [--ns-from NS --ns-to NS] [--modified TEXT] [--name HS_tfib]
      HSDUMPHOLES / HSDUMP (Pass2) -> the donor's A/AB01.v form: one `HS_tfib_i_kn : list kentry` per hole (hole 0 literal,
      every later hole a `seg BASE_kn i n ++ [...]` delta against the earlier hole with the fewest literal entries, ties to
      the lowest index; the deltas are difflib.SequenceMatcher(autojunk=False) opcodes: equal -> seg, insert/replace ->
      literal, delete -> nothing), `HS_tfib_i : acs` with the kn list named, HS_tfib_list, HS_tfib, HS_tfib_In,
      HS_tfib_length.  This is the rule the donor's AB01 follows: it reproduces all 49 of its deltas (see README).
  hsform.py js  LOG OUT.v --header DONOR_AB03.v [...] [--name JS_tfib_band]
      JSDUMP (Pass1) -> the donor's A/AB03.v form.
  hsform.py expand DONOR_AB01.v OUT.json
      the donor's AB01 expanded to plain kn lists (for comparisons).

--header: the first lines of the donor file up to (not including) the first `Definition`, copied; --ns FROM=TO (repeatable, in order) rewrites
module paths; --modified appends a `(* Modified by Theorem Labs, 2026-10: TEXT *)` line after the existing header comments.
"""
import argparse, difflib, json, re, sys


def split_top(body, sep=';'):
    elems, depth, cur = [], 0, []
    for ch in body:
        if ch in '[({':
            depth += 1
        elif ch in '])}':
            depth -= 1
        if ch == sep and depth == 0:
            elems.append(''.join(cur).strip()); cur = []
        else:
            cur.append(ch)
    t = ''.join(cur).strip()
    if t:
        elems.append(t)
    return elems


def match_close(s, i):
    """s[i] is an opening bracket; return the index just past its matching closer"""
    depth = 0
    for k in range(i, len(s)):
        ch = s[k]
        if ch in '[({':
            depth += 1
        elif ch in '])}':
            depth -= 1
            if depth == 0:
                return k + 1
    raise ValueError('unbalanced')


def norm(s):
    return ' '.join(s.split())


QUAL = re.compile(r'(?<![\w.])((?:ALUW?|M|MW)_[A-Z]+)\b')


def qualify(s):
    """the donor's files spell Instr's ALU/MD operation constructors qualified (Instr.ALU_ADD, Instr.M_MUL); Coq prints
    them bare in the collector's context. Same terms, the donor's spelling."""
    return QUAL.sub(r'Instr.\1', s)


TIMING = re.compile(r'proofs/\S+\.vo \(real: [^)]*\)\n')


PASS = None   # set by --pass: only the part of the log after `ROCQ compile .../<PASS>.v` (up to the next ROCQ compile)


def readlog(log):
    """the build log; make -O TIMED=1 can splice a `FILE.vo (real: ...)` line into the middle of a long printed term:
    cut it out (it is an insertion, nothing is lost). A log holding several passes is cut to the one --pass names:
    dump_list takes the FIRST marker, so without the cut a log with Pass1 and Pass2 would give Pass1's dump."""
    s = TIMING.sub('', open(log, errors='replace').read())
    if PASS:
        m = list(re.finditer(r'ROCQ compile \S*/%s\.v' % re.escape(PASS), s))
        if not m:
            sys.exit('hsform: no `ROCQ compile .../%s.v` line in %s' % (PASS, log))
        s = s[m[-1].end():]
        n = re.search(r'\nROCQ compile ', s)
        s = s[:n.start()] if n else s
    return s


def dump_list(log, marker, typ):
    s0 = readlog(log)
    i = s0.index('%s = 0' % marker)
    s = s0[i:]
    i = s.index('= [') + 2
    j = s.index('     : ' + typ)
    body = s[i:j].strip()
    assert body.startswith('[') and body.endswith(']'), body[-80:]
    return split_top(qualify(norm(body[1:-1])))


def holes_of(log):
    s0 = readlog(log)
    t = s0[s0.index('HSDUMPHOLES = 0'):]
    t = t[t.index('= [') + 3:]
    body = t[:t.index(']')].strip()
    return [int(x.strip().replace('%nat', '')) for x in body.split(';')] if body else []


def state_parts(term):
    """term = `{| a_ss := SS pc [regs] [log] [kn] nxt; ... |}` -> (prefix, kn elements, suffix) with the kn list cut out"""
    k = term.index('a_ss := SS ')
    p = k + len('a_ss := SS ')
    m = re.match(r'\(?-?\d+\)?\s*', term[p:])
    p += m.end()
    for _ in range(2):           # regs, log
        assert term[p] == '[', term[p:p + 40]
        p = match_close(term, p)
        while term[p] == ' ':
            p += 1
    assert term[p] == '[', term[p:p + 40]
    q = match_close(term, p)
    kn = split_top(term[p + 1:q - 1]) if term[p + 1:q - 1].strip() else []
    return term[:p], kn, term[q:]


def header(path, ns_from, ns_to, modified):
    out = []
    for line in open(path).read().split('\n'):
        if line.startswith('Definition'):
            break
        for f_, t_ in (ns_from or []):
            line = line.replace(f_, t_)
        out.append(line)
    if modified:
        last = max(i for i, l in enumerate(out) if l.startswith('(*'))
        out.insert(last + 1, '(* Modified by Theorem Labs, 2026-10: %s *)' % modified)
    return out


def pieces(base, bl, nl):
    sm = difflib.SequenceMatcher(None, bl, nl, autojunk=False)
    out = []
    for tag, i1, i2, j1, j2 in sm.get_opcodes():
        if tag == 'equal':
            out.append(('seg', base, i1, i2 - i1))
        elif tag in ('replace', 'insert'):
            if out and out[-1][0] == 'lit':
                out[-1] = ('lit', out[-1][1] + nl[j1:j2])
            else:
                out.append(('lit', nl[j1:j2]))
    return out


def render_kn(name, ps):
    lines = []
    for idx, p in enumerate(ps):
        pre = '' if idx == 0 else '++ '
        if p[0] == 'seg':
            lines.append('%sseg %s_%d_kn %d %d' % (pre, name, p[1], p[2], p[3]))
        else:
            lines.append('%s[%s]' % (pre, '; '.join(p[1])))
    return '\n'.join(lines) + '.'


def donor_states(path, name='HS_tfib'):
    """the donor's AB01 as {h: (prefix, kn list, suffix)}, kn expanded from its seg deltas"""
    txt = open(path).read()
    ex = expand_kn(txt, name)
    out = {}
    for m in re.finditer(r'Definition %s_(\d+) : acs := (.*?)\.\n' % name, txt):
        h = int(m.group(1)); t = m.group(2); k = '%s_%d_kn' % (name, h)
        i = t.index(k)
        out[h] = (t[:i], ex[h], t[i + len(k):])
    return out


def kimg_gate(kn, image, label):
    """the KImg gate (from the byte-identity analysis of fuzz_state's start-up state, section 2): `KImg lo hi`
    says the image bytes in [lo, hi) are unchanged (kentry_ok, donor YK0e.v:560), so a KWord / KFill / KZero of the SAME
    list at an absolute address inside it must carry the image's own bytes there, or the list contradicts itself and
    everything proved from it is vacuous. Returns (overlaps, contradictions); the caller fails the run on any
    contradiction."""
    from elftools.elf.elffile import ELFFile
    e = ELFFile(open(image, 'rb'))
    segs = [(g['p_vaddr'], g['p_filesz'], g['p_memsz'], g.data()) for g in e.iter_segments() if g['p_type'] == 'PT_LOAD']

    def byte(a):
        for va, fs, ms, d in segs:
            if va <= a < va + ms:
                return d[a - va] if a - va < fs else 0
        return None
    kimg = sorted((int(a), int(b)) for a, b in (re.match(r'KImg (\d+) (\d+)$', x).groups() for x in kn if x.startswith('KImg ')))
    ov, bad = 0, []
    for x in kn:
        m = re.match(r'KWord \{\| a_base := ELit 0; a_off := (\d+) \|\} (\d+) \(ELit (-?\d+)\)$', x)
        if m:
            lo, w, v = int(m.group(1)), int(m.group(2)), int(m.group(3)) % (1 << 64)
            vals = lambda a, lo=lo, v=v: (v >> (8 * (a - lo))) & 0xff
            hi = lo + w
        else:
            m = re.match(r'KFill \{\| a_base := ELit 0; a_off := (\d+) \|\} \(ELit (\d+)\) (\d+)$', x)
            m2 = re.match(r'KZero \{\| a_base := ELit 0; a_off := (\d+) \|\} \(ELit (\d+)\)$', x)
            if m:
                lo, hi, b = int(m.group(1)), int(m.group(1)) + int(m.group(2)), int(m.group(3))
                vals = lambda a, b=b: b
            elif m2:
                lo, hi = int(m2.group(1)), int(m2.group(1)) + int(m2.group(2))
                vals = lambda a: 0
            else:
                continue
        for klo, khi in kimg:
            if klo < hi and lo < khi:
                ov += 1
                olo, ohi = max(lo, klo), min(hi, khi)
                if ohi - olo > 1 << 20:
                    bad.append((x[:80], klo, khi, 'overlap too large to compare'))
                    continue
                if any(byte(a) != vals(a) for a in range(olo, ohi)):
                    bad.append((x[:80], klo, khi, 'value differs from the image'))
    if bad:
        sys.stderr.write('hsform: KImg GATE FAILED in %s: %d contradictions, first %s\n' % (label, len(bad), bad[:3]))
    return ov, len(bad)


def provenance_gates(a, states_kn, label, pcs=None):
    """the pin gate and the malloc_context_size gate, for a unit file (README "Gates"). Returns the header lines."""
    if not a.image:
        if a.modified:
            sys.exit('hsform: a unit file (--modified) needs --image <the pinned original ELF>')
        return []
    import pins
    prov = pins.provenance(a.image, a.twin)        # REFUSES unless --image is a pinned original
    lines = [prov] if a.modified else []
    if a.names:
        from af0m import Mem, state_bytes
        cf = [int(l.split()[0], 16) for l in open(a.names) if l.split() and l.split()[-1] == '_ZN11__sanitizer21common_flags_dont_useE']
        if cf:
            mem = Mem(a.image)
            mcs = {state_bytes(kn, mem)(cf[0] + 36, 4) for kn in states_kn}
            if mcs != {30}:
                sys.exit('hsform: REFUSED: malloc_context_size (common_flags %#x + 36) reads %s in the %s, not 30: the run read '
                         'the toolchain-N image, not the original' % (cf[0], sorted(mcs, key=str), label))
            print('hsform: mcs gate PASS (common_flags %#x + 36 = 30 in all %d %s)' % (cf[0], len(states_kn), label))
            if a.modified:
                lines.append('(* malloc_context_size: common_flags %#x + 36 reads 30 in all %d %s (the originals; the toolchain-N '
                             'image reads 1) *)' % (cf[0], len(states_kn), label))
    elif a.modified:
        sys.exit('hsform: a unit file (--modified) needs --names <the unit nm file> for the malloc_context_size gate')
    # GATE arrival at main: cgif's check accepts a hole state wherever it is taken (it does not test the arrival pc), so a
    # short tail or a probe input hands off before main and passes; AD2i (pc ch = TFIB_MAIN) breaks only later.
    if pcs is not None and label == 'hand-off states':
        main = a.main
        if main is None and a.names:
            mm = [int(l.split()[0], 16) for l in open(a.names) if l.split() and l.split()[-1] == 'main']
            main = mm[0] if mm else None
        if main is None:
            if a.modified:
                sys.exit('hsform: a unit file needs --main <pc> or --names (its `main` symbol) for the arrival gate')
        else:
            off = sorted({p for p in pcs if p != main})
            if off:
                sys.exit('hsform: REFUSED: %d of %d hand-off states do not arrive at main %#x (they sit at %s): the tail is '
                         'short (plantail.py probe) or this is a probe input' % (sum(1 for p in pcs if p != main), len(pcs), main,
                                                                                  ', '.join('%#x' % p for p in off[:4])))
            print('hsform: arrival gate PASS (all %d hand-off states at main %#x)' % (len(pcs), main))
            if a.modified:
                lines.append('(* arrival: all %d hand-off states at main %#x *)' % (len(pcs), main))
    # GATE descriptor-array fill (a short tail fails no run): __asan_register_globals ends with
    # PoisonShadow(globals, n * 64, 0xf9), so every state at main must hold 0xf9 on all n*64/8 shadow cells of the unit's
    # asan_globals section (n from its own descriptor table, start from its own section header). A state taken before
    # that poison (a tail one XMemset pair short, or a probe input) lacks it.
    from af0m import Mem, state_bytes, descriptors
    meta, mlen, gl = descriptors(a.image)
    if mlen and label == 'hand-off states':
        mem = Mem(a.image)
        sh0 = (meta >> 3) + 0x7FFF8000
        for i, kn in enumerate(states_kn):
            rd = state_bytes(kn, mem)
            bad = [k for k in range(mlen // 8) if rd(sh0 + k, 1) != 0xF9]
            if bad:
                sys.exit('hsform: REFUSED: state %d does not hold the descriptor-array poison (%d of %d cells at %#x are not 0xf9, '
                         'first %#x): the run handed off before __asan_register_globals finished - the tail is short '
                         '(plantail.py probe) or this is a probe input, not a final state' % (i, len(bad), mlen // 8, sh0, sh0 + bad[0]))
        print('hsform: descriptor-array gate PASS (%d cells of 0xf9 at %#x = shadow of asan_globals %#x, n = %d, in all %d states)'
              % (mlen // 8, sh0, meta, len(gl), len(states_kn)))
        if a.modified:
            lines.append('(* descriptor-array poison: %d cells of 0xf9 at %#x (asan_globals %#x, %d descriptors) in all %d %s *)'
                         % (mlen // 8, sh0, meta, len(gl), len(states_kn), label))
    return lines


def cmd_hs(a):
    holes = holes_of(a.log)
    if not holes:
        sys.exit('hsform: 0 holes: the pass reached no PHandoff (every leaf is a spin, a merge or a failure). Nothing is '
                 'written. Read the failure leaves in the log (label 10000 + 100 * code + plan-node kind; COLA.pkind in '
                 'coq/ColA.v) and the probe (plantail.py) for the node the plan lacks.')
    elems = dump_list(a.log, 'HSDUMP', 'list (option acs)')
    assert len(holes) == len(elems), (len(holes), len(elems))
    got = {}
    for h, e in zip(holes, elems):
        if not e.startswith('Some'):
            sys.exit('hole %d: state is %s' % (h, e[:60]))
        term = e[len('Some'):].strip()
        if term.startswith('(') and term.endswith(')'):
            term = term[1:-1].strip()
        got[h] = state_parts(term)
    n = a.nholes or (max(holes) + 1)
    filled = {}
    if a.fill_from:
        dst = donor_states(a.fill_from, a.name)
    for h in range(n):
        if h in got:
            continue
        if a.fill_from:
            got[h] = dst[h]; filled[h] = 'donor'
        elif a.fill == 'nearest' and a.allow_fill:
            r = max(x for x in holes if x < h) if any(x < h for x in holes) else min(holes)
            got[h] = got[r] if r in holes else None; filled[h] = r
        else:
            sys.exit('hsform: hole %d was not walked. A COMMITTED file must hold the run\'s own state for every hole its '
                     'consumer quantifies over (A/AB1n.v tfib_startup_T1), so filling is NOT the default: collect the '
                     'missing holes (ColA collects both arms of the mmap nodes) or pass --fill nearest --allow-fill for a '
                     'probe input only.' % h)
    if a.image:
        tot = 0
        for h in sorted(set(holes)):
            ov, nb = kimg_gate(got[h][1], a.image, 'hole %d' % h)
            tot += nb
        print('hsform: KImg gate over %d collected states: %s' % (len(set(holes)), 'PASS' if not tot else '%d CONTRADICTIONS' % tot))
        if tot:
            sys.exit(1)
    holes = list(range(n))
    kns = [got[h][1] for h in holes]; prefs = [got[h][0] for h in holes]; sufs = [got[h][2] for h in holes]
    nm = a.name
    out = header(a.header, [x.split('=', 1) for x in a.ns], None, a.modified)
    out[len(out):] = []
    gl = provenance_gates(a, [got[h][1] for h in sorted(set(holes)) if got[h] is not None], 'hand-off states',
                          [int(re.search(r'SS \(?(\d+)', got[h][0]).group(1)) for h in sorted(set(holes)) if got[h] is not None])
    last = max(i for i, l in enumerate(out) if l.startswith('(*'))
    out[last + 1:last + 1] = gl
    out.append('Definition seg (l : list kentry) (i n : Z) : list kentry := firstn (Z.to_nat n) (skipn (Z.to_nat i) l).')
    stats = []
    for h in holes:
        if h == 0:
            body = '[%s].' % '; '.join(kns[0])
            stats.append((0, None, len(kns[0])))
        else:
            best = None
            for b in range(h):
                ps = pieces(b, kns[b], kns[h])
                nlit = sum(len(p[1]) for p in ps if p[0] == 'lit')
                if best is None or nlit < best[0]:
                    best = (nlit, b, ps)
            body = render_kn(nm, best[2])
            stats.append((h, best[1], best[0]))
        out.append('Definition %s_%d_kn : list kentry :=\n%s' % (nm, h, body))
        out.append('Definition %s_%d : acs := %s%s_%d_kn%s.' % (nm, h, prefs[h], nm, h, sufs[h]))
    out.append('Definition %s_list : list acs :=\n[%s].' % (nm, '; '.join('%s_%d' % (nm, h) for h in holes)))
    out.append('Definition %s (h : nat) : option acs := nth_error %s_list h.' % (nm, nm))
    out.append('Lemma %s_In : forall h ch, %s h = Some ch -> In ch %s_list.' % (nm, nm, nm))
    out.append('Proof. intros h ch H. unfold %s in H. exact (nth_error_In _ _ H). Qed.' % nm)
    out.append('Lemma %s_length : length %s_list = %d%%nat.' % (nm, nm, len(holes)))
    out.append('Proof. reflexivity. Qed.')
    open(a.out, 'w').write('\n'.join(out) + '\n')
    json.dump({'holes': len(holes), 'reached': sorted(set(holes) - set(filled)), 'filled': {str(k): v for k, v in filled.items()},
               'kn_lengths': [len(k) for k in kns], 'bases': stats}, open(a.out + '.json', 'w'))
    print('hsform: wrote %s: %d hand-off states (%d reached by the checker, %d filled: %s), kn lengths %d..%d' % (
        a.out, len(holes), len(holes) - len(filled), len(filled), sorted(set(filled.values()), key=str), min(map(len, kns)), max(map(len, kns))))


def cmd_js(a):
    elems = dump_list(a.log, 'JSDUMP', 'list (option acs)')
    assert len(elems) == 1, len(elems)
    e = elems[0]
    if not e.startswith('Some'):
        sys.exit('join state is %s' % e[:60])
    term = e[len('Some'):].strip()
    if term.startswith('(') and term.endswith(')'):
        term = term[1:-1].strip()
    out = header(a.header, [x.split('=', 1) for x in a.ns], None, a.modified)
    gl = provenance_gates(a, [state_parts(term)[1]], 'join state')
    last = max(i for i, l in enumerate(out) if l.startswith('(*'))
    out[last + 1:last + 1] = gl
    if a.image:
        _, kn_js, _ = state_parts(term)
        ov, nb = kimg_gate(kn_js, a.image, 'join state')
        print('hsform: KImg gate over the join state: %s (%d KImg overlaps, all with the image\'s own bytes)' % ('PASS' if not nb else 'FAILED', ov))
        if nb:
            sys.exit(1)
    if a.qualify_kinds:
        q = a.qualify_kinds
        term = re.sub(r'am_kind := (K[A-Z]+)', lambda m: 'am_kind := %s.%s' % (q, m.group(1)), term)
        term = re.sub(r'a_fd := (Fd[A-Za-z]+)', lambda m: 'a_fd := %s.%s' % (q, m.group(1)), term)
    out.append('Definition %s : acs := %s.' % (a.name, term))
    open(a.out, 'w').write('\n'.join(out) + '\n')
    print('hsform: wrote %s (join state, %d bytes)' % (a.out, len(term)))


def expand_kn(txt, name='HS_tfib'):
    """{h: kn list} of a donor-form AB01 text, its seg deltas expanded"""
    parsed = {}
    for m in re.finditer(r'Definition %s_(\d+)_kn : list kentry :=\n(.*?)\.\n(?=Definition)' % name, txt, re.S):
        body = norm(m.group(2))
        ps, depth, cur, i = [], 0, '', 0
        while i < len(body):
            ch = body[i]
            if ch in '[({':
                depth += 1
            elif ch in '])}':
                depth -= 1
            if depth == 0 and body.startswith(' ++ ', i):
                ps.append(cur); cur = ''; i += 4; continue
            cur += ch; i += 1
        ps.append(cur)
        r = []
        for p in ps:
            mm = re.fullmatch(r'seg %s_(\d+)_kn (\d+) (\d+)' % name, p.strip())
            r.append(('seg', int(mm.group(1)), int(mm.group(2)), int(mm.group(3))) if mm else ('lit', split_top(p.strip()[1:-1])))
        parsed[int(m.group(1))] = r
    ex = {}

    def go(k):
        if k not in ex:
            res = []
            for p in parsed[k]:
                res += go(p[1])[p[2]:p[2] + p[3]] if p[0] == 'seg' else p[1]
            ex[k] = res
        return ex[k]
    for k in parsed:
        go(k)
    return ex


def cmd_expand(a):
    ex = expand_kn(open(a.ab01).read())
    json.dump({str(k): v for k, v in sorted(ex.items())}, open(a.out, 'w'))
    print('hsform: expanded %d kn lists' % len(ex))


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest='cmd', required=True)
    for c in ('hs', 'js'):
        p = sub.add_parser(c)
        p.add_argument('log'); p.add_argument('out'); p.add_argument('--header', required=True)
        p.add_argument('--ns', action='append', default=[], help='FROM=TO module-path rewrite of the header, applied in order')
        p.add_argument('--modified', default=None)
        p.add_argument('--name', default='HS_tfib' if c == 'hs' else 'JS_tfib_band')
        p.add_argument('--pass', dest='pass_', default=None, help='the driver file whose output to read (Pass1 / Pass2) when the log holds several')
        p.add_argument('--image', default=None, help='the unit\'s ELF: the pin gate and the KImg gate (each fails the run)')
        p.add_argument('--twin', default=None, help='the unstripped twin of --image (its sha256 goes into the header)')
        p.add_argument('--names', default=None, help='the unit\'s nm file: the malloc_context_size gate and `main`')
        p.add_argument('--main', type=lambda x: int(x, 0), default=None, help='the unit\'s main pc (default: nm `main`)')
        if c == 'hs':
            p.add_argument('--nholes', type=int, default=None, help='hole count of the plan (its PHandoff indices are 0..N-1)')
            p.add_argument('--allow-fill', action='store_true', help='permit --fill nearest (probe inputs only, never a committed file)')
            p.add_argument('--fill', default=None, choices=[None, 'nearest'],
                           help='a hole the checker never reaches gets the state of the nearest reached hole below it')
            p.add_argument('--fill-from', default=None, help='take unreached holes from this donor-form AB01 (reproduction test)')
        else:
            p.add_argument('--qualify-kinds', default=None, help='spell mkind constructors MOD.KRW etc. (the donor AB03 spells APC.)')
    p = sub.add_parser('expand'); p.add_argument('ab01'); p.add_argument('out')
    a = ap.parse_args()
    global PASS
    PASS = getattr(a, 'pass_', None)
    {'hs': cmd_hs, 'js': cmd_js, 'expand': cmd_expand}[a.cmd](a)


if __name__ == '__main__':
    main()
