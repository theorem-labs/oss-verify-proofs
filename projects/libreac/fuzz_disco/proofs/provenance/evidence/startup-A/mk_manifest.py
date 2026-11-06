#!/usr/bin/env python3
"""mk_manifest.py -- write MANIFEST beside this script: one line per file of this directory, `PATH KIND SHA256 ROLE`.

The kinds and roles are the tables below; the sha256 is computed. Refuses (exit 1) when a file has no row or a row has
no file, so the MANIFEST names every file exactly once, and when tools.sha256 (the tools run.sh checks in TOOLS) is
not exactly the table TOOLS below or a tool TOOLS cites as indexed as found is not its version in the table FOUND, so
the citations and the check cannot disagree."""
import hashlib
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
L = 'proofs/libreac/fuzz_disco/lib/A/'
SET = 'startup-set 2026-10-30d'


# The registry commit that indexes the tool versions below as found (INDEXED AS FOUND, not reviewed and not of record).
REG = '5fd6732f0003'
PLAN = 'tools/startup-cited/binmatch_plan/7f058fcb8e4a/'
# The tool versions this directory cites that the registry indexes as found: sha12 -> (file, sha256, its directory at
# REG). Each directory is read from the registry's tree at REG; each sha256 is checked against its SHA256SUMS there.
FOUND = {
    '26b51331c25a': ('af0m.py', '26b51331c25a8275e5b28fbd67167f0848af8e762ed00b0f66a44c8cb87d1393',
                     'tools/startup-cited/af0m/26b51331c25a/'),
    '2ac2dbe25a9a': ('af0m.py', '2ac2dbe25a9a96b6209aa84ebf5c81b63d50612da990ba2430f07b241694f4f2',
                     'tools/startup-cited/af0m/2ac2dbe25a9a/'),
    '7b569be5151f': ('atable.py', '7b569be5151fa55d9a3614ea8418e11bd8d3e6b5b896888467ae74bb866611ec',
                     'tools/startup-cited/atable/7b569be5151f/'),
    'b9aa677211b7': ('atable.py', 'b9aa677211b7968b070dfddc6792653179fdc4859e5a3fc80cf62af6876d7ab9',
                     'tools/startup-cited/atable/b9aa677211b7/'),
    'a28d0565b394': ('binmatch_disco.py', 'a28d0565b3947ecb8581fb745f642e43444a30713bd3abf98dbdaf4f7719bfa6',
                     'tools/startup-cited/binmatch_disco/a28d0565b394/'),
    '7f058fcb8e4a': ('binmatch_plan.py', '7f058fcb8e4a7be403353c77d4f6520b1345453d406fd8d20f172c51124967da', PLAN),
    '064874159929': ('imgref.py', '0648741599291f104c33284cc01fa08f6d69c8947155c406837be6c5d022252c', PLAN),
    'e4a621daca9f': ('discoscratch.py', 'e4a621daca9f514ccb6288fd32810f49015f2d3f8c8dfbdd0949dbc5818d6df2',
                     'tools/startup-cited/discoscratch/e4a621daca9f/'),
    'c188421f4cf5': ('gen_ad1k.py', 'c188421f4cf5274d5cadc608712321619a615e5548373f87be420965cab832b3',
                     'tools/startup-cited/gen_ad1k/c188421f4cf5/'),
    'e7605673f1ef': ('gen_ad2.py', 'e7605673f1ef5c72fe08e0c78338072fbbd8fd0549cfebd93e863397b3917e1a',
                     'tools/startup-cited/gen_ad2/e7605673f1ef/'),
    '59966c883510': ('gen_traces.py', '59966c88351063828f3118687401542cb3d9512b4e218916c1b930fbdc1d0a8f',
                     'tools/startup-cited/gen_traces/59966c883510/'),
    '4be76b651fc5': ('hsform.py', '4be76b651fc5999d8c1a49680487d58396aa8708e4a330d0600ff4b64f4f4157',
                     'tools/startup-cited/hsform/4be76b651fc5/'),
    '563d9c175a38': ('itabranges.py', '563d9c175a38878d9b75e9318c718cff2284c96d18ea2a16cf5c0648cf6e1fca',
                     'tools/startup-cited/itabranges/563d9c175a38/'),
    '9065ddfc51f1': ('pins.py', '9065ddfc51f10f2d55272a6acac3e902f166c1ddf745de2c65fb68e8dfc655d7',
                     'tools/startup-cited/pins/9065ddfc51f1/'),
    'c0b1a83c00ff': ('pins.py', 'c0b1a83c00ff6fe3efb3a7f3eb7aae0f575d83ed8022687ed52cd18c0899cbc1',
                     'tools/startup-cited/pins/c0b1a83c00ff/'),
    'cedbc91e2ed2': ('plantail.py', 'cedbc91e2ed2612fc3702b03aa97085866af72bf06ccacd1723f67f1de814780',
                     'tools/startup-cited/plantail/cedbc91e2ed2/'),
    '81803218fe79': ('resolve_code.py', '81803218fe79932a07aa3422ff95e35208212d3b870871543062ba6beb67e6a5',
                     'tools/startup-cited/resolve_code/81803218fe79/'),
    'ad652b019e6d': ('run_disco_A.sh', 'ad652b019e6d994f7f68ebc3ad0489e99afacd9c5c7e3d5229853eb4a71f7d2d',
                     'tools/startup-cited/run_disco_A.sh/ad652b019e6d/'),
    '8915f4c25050': ('run_textrange.sh', '8915f4c2505097676a56d58309af26f413911e125c63bed79090a7f74fed60c9',
                     'tools/startup-cited/run_textrange.sh/8915f4c25050/'),
    'db7fa393c85e': ('zifyhook.py', 'db7fa393c85e5f444c01d0fa819e8c7789967198454d4718175bb3dbf42cf0d5',
                     'tools/startup-cited/zifyhook/db7fa393c85e/'),
}


def found(*versions):
    """tool versions of one registry directory that the registry indexes as found, in the registry's form"""
    names, shas, dirs = zip(*(FOUND[v] for v in versions))
    assert len(set(dirs)) == 1, versions
    what = ('copy as found, not of record: the tools that produced the AB05 plan body, ' if dirs[0] == PLAN else
            'indexed as found, not of record: ')
    return '%s (%s%s at registry commit %s, sha256 %s)' % (' and '.join(names), what, dirs[0], REG,
                                                           ', '.join(s[:12] for s in shas))


def cite(path, sha, version):
    """a tool run here in the registry's form: of record (its version), or (version None) indexed as found"""
    if version is None:
        return found(sha[:12])
    return '%s (%s, sha256 %s; internal record)' % (os.path.basename(path), version, sha[:12])


# The tools run.sh runs, at their paths under TOOLS: path -> (sha256, version (None: indexed as found, in FOUND), what
# it does, how it runs).
RUN = 'run.sh runs it'
TOOLS = {
    'startup-set/hsform.py': ('9747a6731b7e880424c82db23dcbac391c2e440c1320562341e693cc70c1a65a', SET,
                              'forms AB03 (js) and AB01 (hs) from the collector dumps, with the pin, KImg, '
                              'malloc_context_size, arrival and descriptor-array gates', RUN),
    'startup-set/plantail.py': ('f8aa639d5cc7a5bae8879bca935e2df53fd77ecb83cc180316ec466fd77251af', SET,
                                'inserts AB05\'s measured tail (46 memset pairs before main in every arm)', RUN),
    'startup-set/atable.py': ('e88affcf052695f4a51c4333b548205f44c0b51558a1e98b7149d2b85211a434', SET,
                              'writes AB12 and its field table', 'drivers/run_atable.py runs it'),
    'startup-set/gen_ad2.py': ('3665ff2a7926c5c8651ef392aac2f0d218c59745c79b7534ab6f8e61efce737d', SET,
                               'writes AD2i, AD2j, the report and the gate table (it reads the twin listing itself)', RUN),
    'startup-set/gen_ad1k.py': ('2a6885e5c27f9f7238c80a032e9227d136a04b62e1cdfe7dd0da233b66078c0e', SET,
                                'restates AD1k\'s chunk literals from the generated AD2j', 'drivers/run_gen_ad1k.py runs it'),
    'startup-set/pins.py': ('4778073f01be27d903d4afa8820ba6407c521e11d5de200e635a2a2346491498', SET,
                            'the pin gate and the provenance stamp line', 'drivers/run_pins.py runs it; hsform imports it'),
    'startup-set/keyset.py': ('38b229c6ad08f99262962f32c1b8083cf10d92022ca18cde5589fc7fd9c2f729', SET,
                              'the keyed-table row-set gate (it reads the twin listing itself)', RUN),
    'startup-set/af0m.py': ('f8201f503394bdb67ec56d35c8e9fa93242e85425f25e9a46ced9a083f4aa19d', SET,
                            'module hsform imports', 'imported'),
    'startup-set/jtsites.py': ('5ff0133afe207cb7df2bca4951faad718f2145b2ee16208e4d1f672dbfc94b39', SET,
                               'module af0m imports', 'imported'),
    'startup-set/wh8.py': ('fe8327d6bb7e13663a6df49f1fb64ed76427e81cad265f93ab87453f53cc2f22', SET,
                           'the w_H8 rules gen_ad2 imports', 'imported'),
    'plan/itabranges.py': ('563d9c175a38878d9b75e9318c718cff2284c96d18ea2a16cf5c0648cf6e1fca', None,
                           'writes AB05\'s ranges line by the text rule (0x30eac, 112639 words)', RUN),
    'plan/pautrlen/rvdis.py': ('acc3b31392a5cb56d92b6abbc7dd396e0f4b6bb738c467696126e20164bcfd5b', SET,
                               'the disassembler module itabranges imports from pautrlen/ beside itself', 'imported'),
    'plan/binmatch_plan.py': ('7f058fcb8e4a7be403353c77d4f6520b1345453d406fd8d20f172c51124967da', None,
                              'rewrites the donor plan\'s code addresses by the function pairing and its 4 data addresses '
                              'by code references', 'drivers/run_binmatch_plan.py runs it'),
    'plan/imgref.py': ('0648741599291f104c33284cc01fa08f6d69c8947155c406837be6c5d022252c', None,
                       'the ELF reader and code-reference oracle binmatch_plan imports from beside itself', 'imported'),
    'traces/gen_traces.py': ('59966c88351063828f3118687401542cb3d9512b4e218916c1b930fbdc1d0a8f', None,
                             'writes the allocation-trace universe (20 traces, 12 call sites, 3 functions)',
                             'drivers/run_gen_traces.py runs it'),
    'traces/resolve_code.py': ('81803218fe79932a07aa3422ff95e35208212d3b870871543062ba6beb67e6a5', None,
                               'module gen_traces imports from beside itself (sym_ranges, text_code)', 'imported'),
    'traces/rvelf.py': ('23152d9ca11cb6287ab13e27265103520e7fb9c3816093c893f68a23f5c7dd5b',
                        'pg-reloc-portcore e0e94a04094b', 'the ELF / RV64 decoder gen_traces, resolve_code and '
                        'call_sites.py import', 'imported'),
}
COLA = cite('coq/ColA.v', 'd198e5a14160538277fcaf78fa92e581774b9e092ff389a00c4c1aed07315b79', SET)

HEAD = [
    '# evidence/startup-A: how the image-A start-up data of fuzz_disco is re-derived: %s{AB01,AB03,AB05,AB12,AD2i,AD2j,'
    'AD1k,ACej}.v. proves no function (kind: measurement).' % L,
    '# One line per file: path (relative to this directory), kind, sha256, role. kind: script = a script written for '
    'this evidence (a driver, a check, an extract); input = a file a script reads; table = a per-value table a script '
    'writes; gate = a gate or comparison record a script writes. Written by mk_manifest.py.',
    '# Re-run: bash run.sh REPO IMAGE DONOR_IMAGE TOOLS OUT, with REPO a checkout of this tree, the two released images '
    'fuzz_disco.asan (sha256 5e39150dd810...) and cgif_file_fuzzer.asan (sha256 7093581aab04...) of index/binaries.tsv, '
    'and TOOLS a directory holding the tools run here at the paths tools.sha256 names. It checks every tool\'s sha256, '
    'regenerates every table and gate record under tables/ (cmp) and compares each regenerated .v file with the shipped '
    'one (the compare.py records under tables/, cmp). Measured on 2026-10-31: every comparison holds.',
    '# Tools: not shipped here, cited. Of record (internal record): the start-up set 2026-10-30d (hsform, plantail, '
    'atable, gen_ad2, gen_ad1k, pins, keyset, af0m, jtsites, wh8, pautrlen/rvdis) and rvelf (pg-reloc-portcore '
    'e0e94a04094b). The others: %s; %s; %s; %s. tools.sha256 has each one\'s path and sha256. No tool is edited: what a '
    'run here needs that a tool does not do (read the twin listing where it read the twin, take an input where it names '
    'a host path) is done by a driver under drivers/, which imports the tool unchanged from TOOLS, replaces the one '
    'function or constant, and runs the tool\'s own __main__ block. The unstripped twin is not shipped: '
    'twin/fuzz_disco.asan.syms carries the symbol facts the tools read.'
    % (found('563d9c175a38'), found('7f058fcb8e4a', '064874159929'), found('59966c883510'), found('81803218fe79')),
    '# Every tool tools.sha256 names, and ColA.v, is kept byte-equal at its former path in this directory on the '
    'internal records ref records/libreac-fuzz_disco-1031-tool-copies.',
    '# What ships beyond the tools\' output (the compare.py records): the notice line 4 of AB01, AB03, AB05 (the set\'s '
    'hsform refuses that text, it names the collector\'s lane); AB05\'s module paths; AB12\'s six header lines and its '
    'stops_more (12 of the image\'s 13 self-loops, the 13th 0x6eca0 left out under the KEEP ruling for start-up tables; '
    'TFIB_TEXT_N 112639 is the tool\'s value); the lia hook line of AD2i (line 17) and AD1k (line 16), the text %s '
    'writes; whether that tool or a hand edit wrote it is not recorded (no numeral); AD2i\'s w_H8 notice, '
    'H1_8 comment and two proof steps (written by hand at the commit; no numeral); ACej\'s template text and its three '
    'harness contexts 0x80c04, 0x80c28, 0x80e50 (the return addresses of the harness calls: traces/call_sites.py lists '
    'them).' % found('db7fa393c85e'),
    '# Read, not derived here: %sAF0m.v (owned cells; evidence/core-A) by atable --cells, gen_ad2 and gen_ad1k, and '
    '%sAB1h.v (segments) by gen_ad2; both give the shipped outputs. No derivation to re-run: AB1m and its parts (the '
    'donor\'s statement text; its numerals are checker inputs the kernel evaluates), and the hand numerals of AB13, AB1h, '
    'AB1k, AD1g (kernel computations over the image; base text from the core relocation, evidence/core-A).' % (L, L),
    '# Not re-run here: the collector build that printed the dumps (needs the donor tree built on a build VM); the '
    'function pairing plan/binmatch.cgif.asan.json (made from both images and the twin by %s, not shipped). Gate '
    'records of earlier runs are not shipped: the gates are re-run on the released images in evidence/gates-A.'
    % found('a28d0565b394'),
]

ROWS = {
    'run.sh': ('script', 'Checks the tools in TOOLS against tools.sha256, then re-derives AB01, AB03 (hsform), '
               'AB05 (binmatch_plan, itabranges, plantail), AB12 (atable), AD2i, AD2j (gen_ad2), AD1k (gen_ad1k), the '
               'provenance stamp (pins) and ACej\'s traces (gen_traces) from this directory, the repository and the two '
               'released images, and compares every result: tables by cmp, .v files by compare.py against %s*.v. The '
               'tools that read the twin or name a host path run through their drivers (drivers/). Optional TWIN / '
               'COLLECTOR_LOG / PROBE_LOG re-run the two extracts.' % L),
    'tools.sha256': ('input', 'The tools run.sh runs, as `sha256  path` lines (sha256sum -c form) for their paths '
                     'under TOOLS: ' + '; '.join('%s = %s: %s, %s' % (p, cite(p, s, v), what, how)
                                                 for p, (s, v, what, how) in sorted(TOOLS.items())) + '.'),
    'compare.py': ('script', 'Writes the comparison record of a regenerated file with the shipped one: per differing hunk '
                   'the line ranges, the sha256 of each side and the numerals found on one side only (no line text).'),
    'resolve_imgtop.py': ('script', 'Writes the copy of %sAF0m.v that the set\'s gen_ad1k reads: its one YImgTop.IMG_TOP '
                          'citation replaced by 0x5fe000 from lib/Reusable/YImgTop.v (gen_ad1k evaluates numerals only).'
                          % L),
    'mk_manifest.py': ('script', 'Writes this MANIFEST (kinds and roles from its tables, sha256 computed; refuses when '
                       'tools.sha256 is not its table of the tools run.sh runs, when that table and its table of the '
                       'versions the registry indexes as found disagree, or when a version of the latter is not cited).'),
    'twin/twin_symbols.py': ('script', 'Extract script of the unstripped twin (rule for host binaries): writes the twin\'s '
                             'symbol table as an nm -S listing, after checking that PT_LOAD 2 to 4 of twin and pin are '
                             'byte-equal and PT_LOAD 1 differs only in ELF header section fields and the build-id note.'),
    'twin/fuzz_disco.asan.syms': ('input', 'Symbol facts of the unstripped twin sha256 ec656cf105cb... of fuzz_disco.asan '
                                  '(pin sha256 5e39150dd810...; 2234 symbols); the drivers give the tools it where they '
                                  'read the twin. The twin b8aac6eee6a6... of the v1.9.0 unstripped set has the same '
                                  '.symtab (same listing below its first line).'),
    'collector/extract_dumps.py': ('script', 'Extract script of the collector build logs (rule for collector logs): keeps '
                                   'the ROCQ compile lines and the named dumps, nothing else.'),
    'collector/pass12.dumps.1': ('input', 'Part 1 of 2 (the file size cap; run.sh joins them with cat) of the '
                                 'collector\'s pass 1 and pass 2 dumps (JSDUMP: the join state; HSDUMPHOLES, HSDUMP: the 50 '
                                 'hand-off states, one per line) from its build log (sha256 4a8d52b4f930..., 6051740 bytes), '
                                 'which hsform reads for AB03 and AB01. The collector is %s; its build on the donor tree '
                                 '(run by %s; drivers by colrun.py 59778df6f00b, image-A inputs by %s, the plan = run.sh\'s '
                                 'AB05) printed the dumps; re-derivable only by that build (build VM, about 1 h on 48 '
                                 'cores).' % (COLA, found('8915f4c25050'), found('e4a621daca9f'))),
    'collector/pass12.dumps.2': ('input', 'Part 2 of 2 of the collector\'s dumps (the rest of HSDUMP).'),
    'collector/probe.dumps': ('input', 'The collector\'s tail probe dump (TAILDUMP: 46 memset stops 0x99b74, then main '
                              '0x80aa4) from its build log (sha256 f09b971f8a5d...): the 46 of AB05\'s tail.'),
    'plan/binmatch.cgif.asan.json': ('input', 'The function pairing of the donor image and fuzz_disco.asan (1245 identical '
                                     'functions by masked code) that binmatch_plan reads.'),
    'plan/funcs.asan.tsv': ('input', 'fuzz_disco.asan\'s function table with its donor pairing, which imgref reads.'),
    'traces/call_sites.py': ('script', 'Lists every direct call (jal ra) of named functions with its return address: '
                             'the return addresses ACej\'s three harness contexts are (0x80c04, 0x80c28, 0x80e50) and '
                             'those gen_traces takes as arguments (--fp 0x80e40; --ipc: the second GetCurrentPc call of '
                             'each interceptor, 0x53680 and 0x53520). Written for this evidence: no script of record '
                             'listed them. It imports %s from TOOLS.' % cite('rvelf.py', TOOLS['traces/rvelf.py'][0],
                                                                         TOOLS['traces/rvelf.py'][1])),
    'drivers/twinlist.py': ('script', 'Module the drivers import, written for this evidence: reads the twin symbol listing '
                            '(its header names the twin\'s and the pinned image\'s sha256; its t/T/w/W rows are exactly '
                            'the functions), imports a tool from TOOLS (STARTUP_TOOLS, set by run.sh) and runs '
                            'the tool\'s own __main__ block with the given arguments.'),
    'drivers/run_atable.py': ('script', 'Driver of %s, unchanged, written for this evidence: atable\'s SymSource gets the '
                              'listing\'s functions (t/T/w/W rows, nonzero address, the first of each name) where it read '
                              'the twin\'s STT_FUNC symbols, and the check that the listing\'s header names the image\'s '
                              'sha256 stands for its PT_LOAD comparison of twin and image.'
                              % cite('atable.py', *TOOLS['startup-set/atable.py'][:2])),
    'drivers/run_gen_ad1k.py': ('script', 'Driver of %s, unchanged, written for this evidence: its all_symbols gets the '
                                'listing\'s rows (value, size, name, in .symtab order) where it read the twin\'s .symtab '
                                '(the stdio FILEs and the object that holds FILE.buf).'
                                % cite('gen_ad1k.py', *TOOLS['startup-set/gen_ad1k.py'][:2])),
    'drivers/run_pins.py': ('script', 'Driver of %s, unchanged, written for this evidence: the stamp line names the twin '
                            'sha256 the listing\'s header gives where pins hashes the twin file; it refuses to run without '
                            'OSSV_BINARIES_TSV, so pins never falls back on its host-path index constant.'
                            % cite('pins.py', *TOOLS['startup-set/pins.py'][:2])),
    'drivers/run_gen_traces.py': ('script', 'Driver of %s, unchanged, written for this evidence: imports the rvelf.py and '
                                  'resolve_code.py beside it in TOOLS first and checks it, so nothing loads from the host '
                                  'directory gen_traces names as a constant (KIT); resolve_code\'s sym_ranges gets the '
                                  'listing\'s functions (t/T/w/W rows, nonzero size) where it read the twin\'s sized '
                                  'STT_FUNC symbols.' % cite('gen_traces.py', *TOOLS['traces/gen_traces.py'][:2])),
    'drivers/run_binmatch_plan.py': ('script', 'Driver of %s, both unchanged, written for this evidence: sets their '
                                     'five host-path constants (BM; CGIF, DISCO, DISCO_DEBUG, FUNCS) to its arguments; '
                                     'imgref gets the listing\'s symbols and the image\'s own section table where it read '
                                     'the twin (they only name addresses in the printed evidence), after a check that the '
                                     'listing\'s header names the image\'s sha256.'
                                     % found('7f058fcb8e4a', '064874159929')),
    'tables/call_sites.tsv': ('table', 'call_sites.py\'s calls: callee, caller, call pc, return address.'),
    'tables/AB01.hs.json': ('table', 'hsform\'s per-hole record of the 50 hand-off states (50 reached, 0 filled, kn list '
                            'lengths); byte-equal to the record of the run of record.'),
    'tables/AB12.fields.json': ('table', 'atable --fields: every AB12 value with the image fact it is read from (13 '
                                'stops_more entries).'),
    'tables/A.report.record': ('table', 'The record of gen_ad2\'s report (A.report, sha256 e56c1151d7c2; internal record, '
                               'which run.sh checks): the report without its two w_H8 notes, which name the sources of the '
                               'rules as the tool\'s own text has them and say: AD2i gets Hypothesis H1_8 and the unit '
                               'discharges it (no YWH8.v beside the core; no discharge file written); the w_H8 precheck '
                               'holds: 50 states, 660 non-stack a_vis entries all page-aligned, STK_P in every state with '
                               'in_vis missing both bands, in_sh reaching kHighShadowEnd, in_sh start = sliverb end, '
                               'sliverb start 512-aligned. The rest: main, the state atom indices, the 80 regions and '
                               'their chunks, the 17 twin checks.'),
    'tables/A.gate.md': ('gate', 'gen_ad2\'s gate table: every chunk justified in all 50 states, 80 regions ordered and '
                         'disjoint; byte-equal to the record of the run of record.'),
    'tables/AD1k.sites.md': ('table', 'gen_ad1k\'s 22 AD1k sites and the generated region each cites; byte-equal to the '
                             'record of the earlier run with the set\'s gen_ad1k.'),
    'tables/keyset.txt': ('gate', 'The row-set gate of the set (keyset check) on the shipped AB12.v and AD2j.v: x_* fields, '
                          'image fields, 80 regions, 16 anchor roles PASS; stops_more PASS with the 13th self-loop 0x6eca0 '
                          'declared excluded (KEEP ruling).'),
}


def by(path):
    return cite(path, *TOOLS[path][:2])


def ad(tool, *imports):
    """who wrote a shipped AD file: a tool of the run of run_disco_A.sh, the versions it imports, and the stamp"""
    imp = [found(v) for v in imports]
    return ('written by %s, with the %s and %s it imports, in the run of %s, and stamped by %s'
            % (found(tool), ', '.join(imp[:-1]), imp[-1], found('ad652b019e6d'), found('9065ddfc51f1')))


# The tools that wrote each shipped file, and what this directory's run regenerates it with. AB01 / AB03: two hsform
# versions write byte-equal files from the collector log (both re-run on 2026-10-31 with the arguments of the run of
# run_textrange.sh); the second one and its af0m are not in the registry and are cited by sha256 until they are.
AB0 = ('the same body as %s, with the %s and %s it imports, writes from the collector log (and as %s, with the %s and '
       '%s it imports, writes in the run of %s); which run wrote the shipped file is not recorded; regenerated here by %s'
       % (found('4be76b651fc5'), found('26b51331c25a'), found('c0b1a83c00ff'),
          'hsform.py (sha256 78f5b415e120; internal record)', 'af0m.py (sha256 2877b9c3cafd; internal record)',
          found('9065ddfc51f1'), found('8915f4c25050'), by('startup-set/hsform.py')))
HOOK = ('the text %s writes; whether that tool or a hand edit wrote it is not recorded (no numeral)'
        % found('db7fa393c85e'))
CMP = {
    'AB01': (AB0, 'shipped = output + notice line 4 (no numeral)'),
    'AB03': (AB0, 'shipped = output + notice line 4 (no numeral)'),
    'AB05': ('written by %s, %s --rule text and %s insert --count 46; regenerated here by the first three and %s'
             % (found('7f058fcb8e4a', '064874159929'), found('563d9c175a38'), found('cedbc91e2ed2'),
                by('startup-set/plantail.py')),
             'shipped = output + notice line 4 and its module paths (no numeral)'),
    'AB12': ('body written by %s, re-emitted by %s and TFIB_TEXT_N then set back to 112639 by hand (its header\'s '
             'override record); regenerated here by %s'
             % (found('7b569be5151f'), found('b9aa677211b7'), by('startup-set/atable.py')),
             'shipped = output + header lines 1-6 (comments) and stops_more without 0x6eca0 (KEEP)'),
    'AD2i': (ad('e7605673f1ef', '4be76b651fc5', '2ac2dbe25a9a') + '; regenerated here by '
             + by('startup-set/gen_ad2.py') + ' and ' + by('startup-set/pins.py'),
             'shipped = output + w_H8 notice, two proof steps and the H1_8 comment by hand, and lia hook line 17, '
             + HOOK),
    'AD2j': (ad('e7605673f1ef', '4be76b651fc5', '2ac2dbe25a9a') + '; regenerated here by '
             + by('startup-set/gen_ad2.py') + ' and ' + by('startup-set/pins.py'), 'byte-equal'),
    'AD1k': (ad('c188421f4cf5', 'e7605673f1ef', '4be76b651fc5', '2ac2dbe25a9a') + '; regenerated here by '
             + by('startup-set/gen_ad1k.py') + ' and ' + by('startup-set/pins.py'),
             'shipped = output + lia hook line 16, ' + HOOK),
    'ACej': ('data written on 2026-10-28 by a gen_traces.py whose version is not recorded, then recast by hand; '
             + by('traces/gen_traces.py') + ' here writes the data of the generated ACej.v of commit cf21fc306562 byte '
             'for byte', 'output = the trace data; shipped = it in the template text + 3 harness contexts 0x80c04, '
             '0x80c28, 0x80e50'),
}
for k, (who, diff) in CMP.items():
    ROWS['tables/%s.cmp.tsv' % k] = ('gate', 'compare.py record of the regenerated %s.v with %s%s.v (the shipped file: '
                                     '%s): %s.' % (k, L, k, who, diff))


def main():
    files = []
    for d, ds, fs in os.walk(HERE):
        ds[:] = [x for x in ds if x != '__pycache__']
        for f in fs:
            p = os.path.relpath(os.path.join(d, f), HERE)
            if p != 'MANIFEST':
                files.append(p)
    files.sort()
    missing = [p for p in files if p not in ROWS]
    extra = [p for p in ROWS if p not in files]
    if missing or extra:
        sys.exit('mk_manifest: no row for %s; no file for %s' % (missing, extra))
    listed = sorted(tuple(line.split('  ', 1)[::-1]) for line in open(os.path.join(HERE, 'tools.sha256')).read().split('\n')
                    if line)
    if listed != sorted((p, v[0]) for p, v in TOOLS.items()):
        sys.exit('mk_manifest: tools.sha256 is not the table TOOLS of the tools run.sh runs')
    for p, (s, v, what, how) in TOOLS.items():
        if v is None and FOUND.get(s[:12], ())[:2] != (os.path.basename(p), s):
            sys.exit('mk_manifest: %s sha256 %s is not its version in the table FOUND' % (p, s))
    out = list(HEAD)
    for p in files:
        kind, role = ROWS[p]
        out.append('%s %s %s %s' % (p, kind, hashlib.sha256(open(os.path.join(HERE, p), 'rb').read()).hexdigest(), role))
    text = '\n'.join(out) + '\n'
    uncited = [v for v in FOUND if v not in text]
    if uncited:
        sys.exit('mk_manifest: FOUND has versions no line cites: %s' % uncited)
    open(os.path.join(HERE, 'MANIFEST'), 'w').write(text)
    print('mk_manifest: %d files; %d tools run here and %d versions indexed as found cited'
          % (len(files), len(TOOLS), len(FOUND)))


if __name__ == '__main__':
    main()
