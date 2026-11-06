#!/usr/bin/env python3
"""Write the slice's MANIFEST.md: a `# ` title line, then one table row per file of the slice (path, sha256, role).
Usage: mk_slice_manifest.py SLICE_DIR"""
import hashlib, os, sys

root = sys.argv[1]
TITLE = ('provenance/evidence/core-recheck: re-check of plugin-hostd/fuzz_command\'s port_core-relocated core '
         '(value gate port_addr_check 3d2eee813cce with controls, re-run on 0d24592683b6 and 205a90fd19b8, d9e0589898fd --dry diff, '
         'roundconst v2, count recompute, GOT, codeptr, symbol sweep)')
DIRS = {
    '.': 'record',
    'gate': 'value gate runs of record (port_addr_check 3d2eee813cce): command, INPUTS USED and counts per run, controls, plants',
    'gate/mechanical': 'first triage pass of the flagged rows of runs RA and RB (rule script, settled rows, generated-file list, flag classes)',
    'triage-A': 'measured triage of the open flagged rows of run RA (image A core) and its rule scripts and controls',
    'triage-B': 'measured triage of the open flagged rows of run RB (image B core) and of the relay view RAB, rule scripts, controls',
    'gen-cells': 'measured triage of the flagged rows of the generated cell / chunk / region files (AF0m, AE3i, AD2j and B twins) and whole-file measurements',
    'gen-states': 'measured triage of the flagged rows of the generated start-up states, trace universe and function table (AB01, AB03, ACej, AB1w and B twins)',
    'false-equal': 'second check of every row of the gate\'s false-EQUAL classes (SAME-CONTENT, INSN-SAME, ROUND-CONSTANT-SAME)',
    'got-codeptr': 'GOT-cell check of every .got numeral, with its planted control; codeptr 12348302dfd2 runs, controls and triage',
    'got-codeptr/codeptr': 'codeptr 12348302dfd2 runs, controls, limit measurement and triage scripts',
    'sweep': 'donor symbol + offset against our symbol + offset for every address-valued paired numeral, triage, controls',
    'roundconst': 'roundconst gate v2 32b39f3b34e9: runs, controls, plants, triage of every non-SAME row',
    'roundconst/main': 'roundconst v2 run summaries and --moved rows',
    'roundconst/plants': 'roundconst v2 planted controls',
    'counts': 'recompute from our images of every image-derived count and section / segment bound',
    'd9e0': 'port_core d9e0589898fd --dry re-run of the two re-runnable sets and the classification of every differing row',
    'd9e0/runs': 'the d9e0 --dry runs of this check: command, file lists, logs, exit codes',
    'rt-reusable': 'value gate and triage of the runtime relocations (lib/A/Rt, lib/B/Rt) and of lib/Reusable',
    'rt-reusable/runs': 'gate run summaries and FLAGGED lines of the runtime and lib/Reusable runs and their donor-on-donor controls',
    'rerun-0d24': 're-run of value gates RA and RB and planted controls PA / PB on port_addr_check 0d24592683b6 over the inputs of record: summaries, FLAGGED lines, verdict-by-verdict comparison with 3d2eee813cce on the same inputs, measured triage of every changed row',
    'rerun-0d24/scripts': 'scripts of the 0d24592683b6 re-run: gate wrapper, run drivers, row comparison, triage of the changed rows',
    'rerun-205a': 're-run of value gates RA and RB and planted controls PA / PB on port_addr_check 205a90fd19b8 over the inputs of record: identity check with 0d24592683b6, summaries, FLAGGED lines, verdict-by-verdict comparison with 0d24592683b6 on the same inputs, measured triage of every changed row and of every STALE-DONOR-CODE-POINTER row',
    'rerun-205a/scripts': 'scripts of the 205a90fd19b8 re-run: gate wrapper (the 0d24 record\'s), sequential run driver, input and identity checks, row comparison, triage of the changed rows, plant and moved-page checks',
    'scripts': 'scripts of the record itself (inventory, gate wrapper, this manifest writer)',
}
FILE_ROLES = {
    'REPORT.md': 'the result: findings, every part with counts and controls, the tools\' named limits',
    'INVENTORY.md': 'which files came from which port_core run (or other tool), with which inputs, and the route of each set',
    'inventory.tsv': 'per .v file directly in lib/A (A*.v), lib/B (Y*.v), lib/A/Rt, lib/B/Rt, lib/Reusable (not lib/Reusable\'s 4 files in R/ and Z/): set, route, sha256 at the checked and merged trees and in the run output',
    'code-values.tsv': 'the wrong values in proof code found by this check, with their measurement (for a code commit)',
    'measured-rows.tsv': 'measured rows for wrong values in comment text (none found: header only)',
    'internal-texts.md': 'the texts of this slice that were restated or moved out for the internal record: per file its internal record entry (commit, path, sha256), its role, and what changed; then the corrections made after the cleaning',
    'gen-cells/triage-rows.A.tsv': 'triage rows of the generated cell / chunk / region files, image A part (the part README calls it triage-rows.tsv; split by image for the 5 MiB file cap)',
    'gen-cells/triage-rows.B.tsv': 'triage rows of the generated cell / chunk / region files, image B part (split as above)',
    'gen-states/triage-rows.A.tsv': 'triage rows of the generated start-up states, traces and function table, image A part (the part README calls it triage-rows.tsv; split by image for the 5 MiB file cap)',
    'gen-states/triage-rows.B.tsv': 'triage rows of the generated start-up states, traces and function table, image B part (split as above)',
    'roundconst/rows.A.tsv': 'every non-SAME roundconst v2 row with its measured reason, image A part (the part README calls it rows.tsv; split by image key for the 5 MiB file cap)',
    'roundconst/rows.B.tsv': 'every non-SAME roundconst v2 row with its measured reason, image-key B part (runs rc-B and rc-U; split as above)',
}
rows = []
for dp, dn, fn in os.walk(root):
    dn.sort()
    for f in sorted(fn):
        p = os.path.relpath(os.path.join(dp, f), root)
        if p == 'MANIFEST.md':
            continue
        d = os.path.dirname(p) or '.'
        role = FILE_ROLES.get(p) or DIRS[d]
        rows.append((p, hashlib.sha256(open(os.path.join(dp, f), 'rb').read()).hexdigest(), role))
rows.sort()
out = ['# ' + TITLE, '',
       'One owner. Every file below is part of this record; `REPORT.md` is the entry point. Paths are relative to this '
       'directory; files of the unit are named relative to its proof root (lib/...).', '',
       '| file | sha256 | role |', '|---|---|---|']
out += ['| %s | %s | %s |' % r for r in rows]
open(os.path.join(root, 'MANIFEST.md'), 'w').write('\n'.join(out) + '\n')
print(len(rows), 'files')
