#!/usr/bin/env python3
"""Relocate an fm (fuzz_manifest) lib/A route file into libreac/fuzz_disco (target disco-A or disco-Y).

Mechanical half only: module-path rewrites, identifier renames, numeral substitution from a
port_addr_check predict table, `Local` on fm's zify flag override, the YImgTop zify hook.  Every rewrite applies to
code only: fm's comments (nested `(* *)`) stay verbatim.  The header line is supplied by the caller.
New version of the G9 tool's reloc.py of record (sha256 7692f99a06175a15337fe3e2c1b3a86ad93bcbcf722e638d06db0d5bc63c1347):
the git repository is the environment variable HUB instead of a constant, and comments name no worker or branch;
the code that writes relocated text is unchanged.
"""
import os, re, sys, json, subprocess, functools

SRCPFX = 'OssFuzzTheorems.Proofs.omx_clap_core.fuzz_manifest.'
DSTPFX = 'OssFuzzTheorems.Proofs.libreac.fuzz_disco.'
HUB = os.environ.get('HUB') or sys.exit('reloc.py: set HUB to a git repository that holds the fm commits')
DEFAULT_SRC_REF = '0ddf65fd8cc'    # the fm extended route, a fast-forward of the first route 3e35620c52e
SRC_REF = DEFAULT_SRC_REF
SRC_LIB = 'proofs/omx-clap-core/fuzz_manifest/lib'
DST_UNIT = 'proofs/libreac/fuzz_disco'

# ---- disco configuration ---------------------------------------------------------------------------
# fm lib.A module (path relative to lib.A) -> disco module (path relative to DSTPFX), both images.
COMMON = {
    'FMsnprintfShared': 'lib.Rt.SnShared',     # landed
    'FMsnprintfSx':     'lib.Rt.SnSx',         # landed
    'FMupoison':        'lib.Rt.SnUpoison',    # landed
    'FMsnprintfPf':     'lib.Rt.PfFacts',      # landed
    'FMgxaSeamDef':     'lib.Rt.SnFF',         # commit 46a3286d296
    'FMgxaSeamFF':      'lib.Rt.SnFF',         # commit 46a3286d296
}
# class (a) route files: no numeral, no core name, no record, and no per-image module that defines constants (Bz/A/IcptSpec
# is per image: its StrFun Require defines find_byte, which each image has).  One copy at lib/A serves both images;
# assemble refuses a NEUTRAL file that Requires a per-image module defining constants.  FMpfStep, FMpfArmPdSeam,
# FMgxaSeam02x, FMpfArmPlluSeam: fm 0ddf65fd8cc (a ruling of record, measured twice).
NEUTRAL = {'Bz.A.I_pcxgram', 'FMgxaSeamNormG', 'FMgxaSeamPf', 'FMsnprintfVa',
           'FMpfStep', 'FMpfArmPdSeam', 'FMgxaSeam02x', 'FMpfArmPlluSeam'}
# fm modules whose disco counterpart does not carry fm's names: the tool refuses to guess.
STOP = {
    'FMgxa_mem':  "names differ: fm FMgxa_mem.copy_ready/set_ready = disco lib/<img>/RT_gxa_calls_mem.copy_ready/"
                  "set_ready; fm memcpy_stack_contract_A/memset_stack_contract_A (at A_img) = disco "
                  "lib/<img>/RT_gxa_calls_mem_vf.memcpy_stack_contract_Avf/_Avf (Y: _Bvf); map each use by hand",
    'Bz.A.I_strncmpw': 'no twin: strncmp / strncasecmp are absent from both disco images (P0 README; '
                       'FMrt_pre drops its use)',
    'FMPstat': 'fm statics footprint; dropped with the FMH_Base subset (P8-*-base stop item)',
}
# PLAN.md section 2 (b): A-core module -> Y-core module (lib.Reusable), Y only.
YCORE = {'AB1v': 'YB1v', 'AB1w': 'YB1w', 'AE20': 'YE20', 'AE22': 'YE22', 'AE2p': 'YE2p', 'AE2y': 'YE2y',
         'AE34': 'YE34', 'AE39': 'YE39', 'AE3a': 'YE3a', 'AE3d': 'YE3d', 'AE3e': 'YE3e', 'AE3f': 'YE3f',
         'AE3g': 'YE3g', 'AE3i': 'YE3i', 'AE6g': 'YE6g', 'AE7f': 'YE7f', 'AF0l': 'YF0l', 'AF0m': 'YF0m',
         'AF0x': 'YF0x', 'AFhy': 'YFhy', 'AFl0': 'YFl0', 'AFl3': 'YFl3', 'AB1q': 'YB1q'}
# identifiers renamed in every file (word match): disco's musl memset tfib name
COMMON_IDENT = [('tfib_A_musl_memset', 'tfib_A_memset_libc')]
# fm's global zify flag override leaks into every importer; disco keeps it inside the file (`Local`).
ZIFY_FLAG = re.compile(r'^Ltac (Zify\.zify_convert_to_euclidean_division_equations_flag ::= constr:\(false\)\.)', re.M)
# disco's AF0x / YF0x define TFIB_IMG_END / TFIB_IMG_LO as YImgTop names, not numerals: files that use them get disco's
# hook (AF0x.v:21), after their last Require, since a later Require (Lib.FP) resets the hook globally.
IMG_NAMES = re.compile(r'\bTFIB_IMG_(?:END|LO)\b')
IMG_HOOK = '#[local] Ltac Zify.zify_pre_hook ::= try unfold YImgTop.IMG_TOP, YImgTop.IMG_LO in *.'

TARGETS = {
    'disco-A': {
        'image': 'fuzz_disco.asan', 'imgdir': 'lib.A', 'pathdir': 'lib/A',
        'rename': {'RT_IImgA': 'lib.CJ.RL.I.RecAsanVfA', 'RT_IImgA_ok': 'lib.A.RT_IImgA_ok',
                   'RT_gxa_inst': 'lib.A.RT_gxa_inst',
                   'FMgxa_bzcj': 'lib.A.RT_gxa_bridge_seam'},   # R-5
        'vsnmod': 'lib.CJ.RL.I.RecAsanA',
        # fm RT_IImgA record names -> disco names: (fm name, disco module, disco name)
        'record': [('A_img_vsn', 'RecAsanA', 'N_img_asan'), ('A_sym_vsn', 'RecAsanA', 'N_sym_asan'),
                   ('A_exact_vsn', 'RecAsanA', 'N_exact_asan'),
                   ('A_img', 'RecAsanVfA', 'N_img_asan_vf'), ('A_sym', 'RecAsanVfA', 'N_sym_asan_vf'),
                   ('A_exact', 'RecAsanVfA', 'N_exact_asan_vf')],
        'core': {},
    },
    'disco-Y': {
        'image': 'fuzz_disco.asan-ubsan', 'imgdir': 'lib.B', 'pathdir': 'lib/B',
        'rename': {'RT_IImgA': 'lib.CJ.RL.I.RecAsanVfB', 'RT_IImgA_ok': 'lib.B.RT_IImgB_ok',
                   'RT_gxa_inst': 'lib.B.RT_gxa_inst',
                   'FMgxa_bzcj': 'lib.B.RT_gxa_bridge_seam'},   # R-5
        'vsnmod': 'lib.CJ.RL.I.RecAsanB',
        'record': [('A_img_vsn', 'RecAsanB', 'N_img_asan_ubsan'), ('A_sym_vsn', 'RecAsanB', 'N_sym_asan_ubsan'),
                   ('A_exact_vsn', 'RecAsanB', 'N_exact_asan_ubsan'),
                   ('A_img', 'RecAsanVfB', 'N_img_asan_ubsan_vf'), ('A_sym', 'RecAsanVfB', 'N_sym_asan_ubsan_vf'),
                   ('A_exact', 'RecAsanVfB', 'N_exact_asan_ubsan_vf')],
        'core': {k: 'lib.Reusable.' + v for k, v in YCORE.items()},
    },
}
# Gaps the run met (module -> reason); the caller reports them.
NOTES = {}
CFG = TARGETS['disco-A']


def set_target(name):
    global CFG
    CFG = TARGETS[name]
    NOTES.clear()


def set_src_ref(ref):
    """The fm commit the route files are read from (default DEFAULT_SRC_REF)."""
    global SRC_REF
    SRC_REF = ref


def fm_modules():
    """Every fm module under lib/A at SRC_REF, dotted, relative to lib.A."""
    return _fm_modules(SRC_REF)


@functools.lru_cache(maxsize=None)
def _fm_modules(ref):
    out = subprocess.run(['git', '-C', HUB, 'ls-tree', '-r', '--name-only', ref, SRC_LIB + '/A/'],
                         check=True, capture_output=True, text=True, env=dict(os.environ, GIT_NO_LAZY_FETCH='1')).stdout
    return {p[len(SRC_LIB) + 3:-2].replace('/', '.') for p in out.split() if p.endswith('.v')}


def fm_text(rel):
    """fm text of lib/A/<rel>.v at SRC_REF."""
    return subprocess.run(['git', '-C', HUB, 'show', '%s:%s/A/%s.v' % (SRC_REF, SRC_LIB, rel)], check=True,
                          capture_output=True, text=True, env=dict(os.environ, GIT_NO_LAZY_FETCH='1')).stdout


def dest_of(mod):
    """fm lib.A module (dotted, relative to lib.A) -> disco module (dotted, relative to DSTPFX)."""
    if mod in STOP:
        NOTES[mod] = 'STOP: ' + STOP[mod]
    if mod in COMMON:
        return COMMON[mod]
    if mod in CFG['rename']:
        return CFG['rename'][mod]
    if mod in CFG['core']:
        return CFG['core'][mod]
    if mod in NEUTRAL:
        return 'lib.A.' + mod
    if mod.startswith('Ox.'):
        return 'lib.' + mod          # disco's Ox modules are lib/Ox, one copy for both images
    return CFG['imgdir'] + '.' + mod


def split_mod(path):
    """Dotted path under lib.A (relative) -> (module, rest): the longest prefix that is an fm file."""
    parts = path.split('.')
    for k in range(len(parts), 0, -1):
        if '.'.join(parts[:k]) in fm_modules():
            return '.'.join(parts[:k]), parts[k:]
    return path, []


def uses_vsn(text):
    return any(re.search(r'\b%s\b' % n, text) for n, m, _ in CFG['record'] if m.startswith('RecAsan') and n.endswith('_vsn'))


_CT = re.compile(r'\(\*|\*\)|"')


def segments(text):
    """`text` cut into (in_comment, piece) runs: comments are `(* ... *)`, nested; a `"` string outside them is code."""
    out, depth, start, instr = [], 0, 0, False
    for m in _CT.finditer(text):
        t, a = m.group(0), m.start()
        if instr:
            instr = t != '"'
        elif depth == 0:
            if t == '"':
                instr = True
            elif t == '(*':
                if a > start:
                    out.append((False, text[start:a]))
                start, depth = a, 1
        elif t == '(*':
            depth += 1
        elif t == '*)':
            depth -= 1
            if depth == 0:
                out.append((True, text[start:m.end()]))
                start = m.end()
    if start < len(text):
        out.append((depth > 0, text[start:]))
    return out


def code_text(text):
    """`text` with every comment character except newlines blanked, so lines and columns stay where they were."""
    return ''.join(re.sub(r'[^\n]', ' ', s) if c else s for c, s in segments(text))


def on_code(text, fn):
    """`fn` applied to the code runs of `text` only; comments are copied unchanged."""
    return ''.join(s if c else fn(s) for c, s in segments(text))


def numeral_re(v):
    """A whole literal `v`: 0xa1d78 does not match inside 0xa1d780, 4096 not inside 40960."""
    return re.compile(r'(?<![0-9A-Za-z_])%s(?![0-9A-Za-z_])' % re.escape(v))


def split_requires(text):
    """Rewrite every `From <fm path> Require [Import|Export] names.` statement (in code, not in comments)."""
    code = code_text(text).split('\n')
    vsn = uses_vsn('\n'.join(code))
    out = []
    lines = text.split('\n')
    i = 0
    while i < len(lines):
        s = lines[i]
        if code[i].startswith('From ') and ' Require' in code[i]:
            stmt, cstmt = [s], [code[i]]
            while not cstmt[-1].rstrip().endswith('.'):
                i += 1
                stmt.append(lines[i])
                cstmt.append(code[i])
            joined = ' '.join(x.strip() for x in cstmt)
            m = re.match(r'From\s+([A-Za-z0-9_.]+)\s+Require\s+(Import\s+|Export\s+)?(.*)\.$', joined)
            if not m or not m.group(1).startswith(SRCPFX):
                out.extend(stmt)
                i += 1
                continue
            base = m.group(1)[len(SRCPFX):]
            kw = (m.group(2) or '').strip()
            names = m.group(3).split()
            if base != 'lib.A' and not base.startswith('lib.A.'):
                stmt[0] = stmt[0].replace(m.group(1), DSTPFX + base, 1)
                out.extend(stmt)
            else:
                sub = base[len('lib.A'):].lstrip('.')
                groups = []
                for n in names:
                    full = (sub + '.' + n) if sub else n
                    d = dest_of(full).rsplit('.', 1)
                    targets = [d]
                    if full == 'RT_IImgA' and vsn:
                        targets = [CFG['vsnmod'].rsplit('.', 1), d]
                    for db, dn in targets:
                        if groups and groups[-1][0] == db:
                            groups[-1][1].append(dn)
                        else:
                            groups.append((db, [dn]))
                if len(groups) == 1 and groups[0][1] == names:
                    stmt[0] = stmt[0].replace(m.group(1), DSTPFX + groups[0][0], 1)
                    out.extend(stmt)
                else:
                    new = [l for d, ns in groups for l in render(DSTPFX + d, kw, ns)]
                    notes = [p for c, p in segments('\n'.join(stmt)) if c]
                    if notes:      # fm's comments inside the statement stay, after it
                        new[-1] += ' ' + ' '.join(notes)
                    out.extend(new)
            i += 1
            continue
        out.append(s)
        i += 1
    return '\n'.join(out)


def render(newbase, kw, names):
    return ['From %s Require%s %s.' % (newbase, (' ' + kw) if kw else '', ' '.join(names))]


def rec_name(name):
    for n, m, d in CFG['record']:
        if n == name:
            return m, d
    return None


def rewrite_qualified(text):
    """Fully qualified `OssFuzzTheorems.Proofs.omx_clap_core.fuzz_manifest.lib...` references."""
    def sub(m):
        path = m.group(1).split('.')
        if len(path) >= 3 and path[0] == 'lib' and path[1] == 'A':
            mod, rest = split_mod('.'.join(path[2:]))
            if mod == 'RT_IImgA' and rest and rec_name(rest[0]):
                rm, rn = rec_name(rest[0])
                return DSTPFX + 'lib.CJ.RL.I.' + rm + '.' + '.'.join([rn] + rest[1:])
            return DSTPFX + '.'.join([dest_of(mod)] + rest)
        return DSTPFX + '.'.join(path)
    return re.sub(re.escape(SRCPFX) + r'(lib(?:\.[A-Za-z0-9_]+)*)', sub, text)


# `Module RTA := <fm>.lib.A.RT_IImgA.`: record names used through the alias (`RTA.A_img`) are renamed too.
RECORD_ALIAS = re.compile(r'\bModule\s+([A-Za-z_][A-Za-z0-9_\']*)\s*:=\s*(?:%s)?(?:lib\.A\.)?RT_IImgA\s*\.(?![\w.])'
                          % re.escape(SRCPFX))


def rewrite_names(text, had_record, aliases=()):
    """Short-qualified module names and identifiers."""
    if had_record:
        # RT_IImgA.<record name> first (it may name the vsn record), then aliases of RT_IImgA, then bare record names.
        def q(m):
            r = rec_name(m.group(1))
            return '%s.%s' % r if r else m.group(0)
        text = re.sub(r'\bRT_IImgA\.([A-Za-z0-9_]+)\b', q, text)
        vf = CFG['rename']['RT_IImgA'].rsplit('.', 1)[1]       # the module the alias now names
        for x in aliases:
            def qa(m, x=x):
                r = rec_name(m.group(1))
                return m.group(0) if not r else '%s.%s' % (x if r[0] == vf else r[0], r[1])
            text = re.sub(r'(?<![.\w])%s\.([A-Za-z0-9_]+)\b' % re.escape(x), qa, text)
        for n, _, d in CFG['record']:
            text = re.sub(r'(?<![.\w])%s\b' % re.escape(n), d, text)
    for a, b in COMMON_IDENT:
        text = re.sub(r'\b%s\b' % re.escape(a), b, text)
    # `FMupoison.ARU_frame`-style short-qualified uses of renamed modules (RT_IImgA is the record, above).
    for a, b in list(COMMON.items()) + list(CFG['rename'].items()):
        if a != 'RT_IImgA':
            text = re.sub(r'(?<![.\w])%s\.(?!v\b)' % re.escape(a), b.rsplit('.', 1)[1] + '.', text)
    for a, b in CFG['core'].items():
        # `AE2y.foo` qualified uses; `AE2y.v:12` file references in comments stay fm's.
        text = re.sub(r'\b%s\.(?!v\b)' % re.escape(a), b.rsplit('.', 1)[1] + '.', text)
    return text


def place_header(lines, header):
    """The relocation note is the first line; fm's own header follows it."""
    return [header] + lines


def add_img_hook(text):
    """IMG_HOOK on its own line after the end of the last Require statement of the code."""
    code = code_text(text).split('\n')
    last, i = None, 0
    while i < len(code):
        if re.match(r'\s*(?:From\s+\S+\s+)?Require\b', code[i]):
            while not code[i].rstrip().endswith('.') and i + 1 < len(code):
                i += 1
            last = i
        i += 1
    lines = text.split('\n')
    at = 0 if last is None else last + 1
    return '\n'.join(lines[:at] + [IMG_HOOK] + lines[at:])


def apply_numerals(text, numerals):
    """Numeral substitutions {fm line: [(old, new)]}; line numbers are port_addr_check's, i.e. fm's own.  Whole
    literals in code only (never inside comments)."""
    lines, code = text.split('\n'), code_text(text).split('\n')
    for ln, pairs in numerals.items():
        idx = ln - 1
        # port_addr_check gives one MAPS row per occurrence, so a numeral written twice on a line arrives as two equal
        # pairs: each distinct pair is applied once, to every occurrence.  A moved literal is masked in `code`, so a
        # later pair whose fm value equals this new value does not move it again.
        for old, new in dict.fromkeys(map(tuple, pairs)):
            hits = list(numeral_re(old).finditer(code[idx]))
            if not hits:
                raise SystemExit('numeral %s not in the code of line %d: %s' % (old, ln, lines[idx]))
            for m in reversed(hits):
                lines[idx] = lines[idx][:m.start()] + new + lines[idx][m.end():]
                code[idx] = code[idx][:m.start()] + '\x01' * len(new) + code[idx][m.end():]
    return '\n'.join(lines)


def relocate(text, numerals, header):
    text = apply_numerals(text, numerals)
    code = code_text(text)
    had_record = bool(re.search(r'\bRT_IImgA\b', code))
    if had_record:
        for n in ('KV', 'KV3', 'A_iv', 'A_sym_vsn_agree'):
            if re.search(r'(?<![.\w])%s\b' % n, code):
                NOTES['RT_IImgA.' + n] = ('CHECK: fm record name with no disco rename (KV / KV3 are defined in '
                                         'lib/CJ/RL/I/IImgA.v / IImgB.v; Require Import that module)')
    aliases = RECORD_ALIAS.findall(code)
    text = split_requires(text)
    text = on_code(text, lambda s: ZIFY_FLAG.sub(r'Local Ltac \1', rewrite_names(rewrite_qualified(s), had_record, aliases)))
    if IMG_NAMES.search(code):
        if re.search(r'zify_pre_hook\s*::=', code):
            NOTES['zify_pre_hook'] = 'CHECK: fm sets its own zify_pre_hook; add the YImgTop unfold to it by hand'
        else:
            text = add_img_hook(text)
    return '\n'.join(place_header(text.split('\n'), header))


if __name__ == '__main__':
    target, src, dst, hdr, numf = sys.argv[1:6]
    set_target(target)
    numerals = {}
    if numf != '-':
        raw = json.load(open(numf))
        numerals = {int(k): v for k, v in raw.items()}
    txt = open(src).read() if os.path.exists(src) else fm_text(src)
    open(dst, 'w').write(relocate(txt, numerals, open(hdr).read().rstrip('\n')))
    for k, v in NOTES.items():
        print('%s: %s' % (k, v), file=sys.stderr)
