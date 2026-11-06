#!/usr/bin/env python3
"""Relocate an fm (fuzz_manifest) lib/A route file into libreac/fuzz_disco (target disco-A or disco-Y).

Mechanical half only: module-path rewrites, identifier renames, numeral substitution from a
port_addr_check predict table.  The header line is supplied by the caller.
New version of the first G9 tool version's reloc.py (sha256 4506c4099b4536ea1f376792e35bba29f248a62715069fc956fc06bee41fe9fb):
the git repository is the environment variable HUB instead of a constant, and comments name no worker or branch;
the code that writes relocated text is unchanged.
"""
import os, re, sys, json, subprocess, functools

SRCPFX = 'OssFuzzTheorems.Proofs.omx_clap_core.fuzz_manifest.'
DSTPFX = 'OssFuzzTheorems.Proofs.libreac.fuzz_disco.'
HUB = os.environ.get('HUB') or sys.exit('reloc.py: set HUB to a git repository that holds the fm commits')
SRC_REF = '3e35620c52e'
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
# class (a) route files: no numeral, no core name, no record.  One copy at lib/A serves both images.
NEUTRAL = {'Bz.A.I_pcxgram', 'Bz.A.IcptSpec', 'FMgxaSeamNormG', 'FMgxaSeamPf', 'FMsnprintfVa'}
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


@functools.lru_cache(maxsize=None)
def fm_modules():
    """Every fm module under lib/A, dotted, relative to lib.A."""
    out = subprocess.run(['git', '-C', HUB, 'ls-tree', '-r', '--name-only', SRC_REF, SRC_LIB + '/A/'],
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


def split_requires(text):
    """Rewrite every `From <fm path> Require [Import|Export] names.` statement."""
    vsn = uses_vsn(text)
    out = []
    lines = text.split('\n')
    i = 0
    while i < len(lines):
        s = lines[i]
        if s.startswith('From ') and ' Require' in s:
            stmt = [s]
            while not stmt[-1].rstrip().endswith('.'):
                i += 1
                stmt.append(lines[i])
            joined = ' '.join(x.strip() for x in stmt)
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
                    for d, ns in groups:
                        out.extend(render(DSTPFX + d, kw, ns))
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


def rewrite_names(text, had_record):
    """Short-qualified module names and identifiers."""
    if had_record:
        # RT_IImgA.<record name> first (it may name the vsn record), then bare record names.
        def q(m):
            r = rec_name(m.group(1))
            return '%s.%s' % r if r else m.group(0)
        text = re.sub(r'\bRT_IImgA\.([A-Za-z0-9_]+)\b', q, text)
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


def relocate(text, numerals, header):
    # numerals first: their line numbers are port_addr_check's, i.e. fm's own
    lines = text.split('\n')
    for ln, pairs in numerals.items():
        idx = ln - 1
        for old, new in pairs:
            if old not in lines[idx]:
                raise SystemExit('numeral %s not on line %d: %s' % (old, ln, lines[idx]))
            lines[idx] = lines[idx].replace(old, new)
    text = '\n'.join(lines)
    had_record = bool(re.search(r'\bRT_IImgA\b', text))
    if had_record:
        for n in ('KV', 'KV3', 'A_iv', 'A_sym_vsn_agree'):
            if re.search(r'(?<![.\w])%s\b' % n, text):
                NOTES['RT_IImgA.' + n] = ('CHECK: fm record name with no disco rename (KV / KV3 are defined in '
                                         'lib/CJ/RL/I/IImgA.v / IImgB.v; Require Import that module)')
    text = split_requires(text)
    text = rewrite_qualified(text)
    text = rewrite_names(text, had_record)
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
