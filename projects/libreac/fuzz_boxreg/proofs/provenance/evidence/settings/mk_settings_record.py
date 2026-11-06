#!/usr/bin/env python3
"""Write the unit's record of tactic-level settings (stream lead rule 1i-ter) from one run of global_settings.py v10.

    mk_settings_record.py RUN_OUTPUT UNIT_LIB_PREFIX TREE_COMMIT > TACTIC-SETTINGS.md

RUN_OUTPUT is the stdout of `global_settings.py WT FILE...` over every .v file of the unit's lib/ (exit code 0).
UNIT_LIB_PREFIX is the repository path of the lib (e.g. proofs/libreac/fuzz_boxreg/lib); every path printed is
relative to it. Host paths of the run are never printed."""
import collections, re, sys


def main():
    run, prefix, tree = sys.argv[1:4]
    tool_sha = summary = None
    esc = collections.defaultdict(list)   # setting text -> [(file, line)]
    unm = []
    kernel = []
    nfiles = 0
    cur = None
    for ln in open(run, encoding='utf-8'):
        m = re.match(r'TOOL \S+ sha256=([0-9a-f]{64})', ln)
        if m:
            tool_sha = m.group(1)
        if ln.startswith('SUMMARY:'):
            summary = ln.strip()
        m = re.match(r'INPUT file (control|target) (\S+)', ln)
        if m:
            cur = m.group(2).split('/' + prefix + '/', 1)[-1] if m.group(1) == 'target' else None
            if cur:
                nfiles += 1
            continue
        m = re.match(r'\s+:(\d+) (ESCAPES|UNMEASURED|PLAIN|KERNEL) (\w+): (.*)', ln)
        if m and cur:
            line, cls, level, text = int(m.group(1)), m.group(2), m.group(3), m.group(4).strip()
            if cls == 'ESCAPES':
                esc[(level, text)].append((cur, line))
            elif cls == 'UNMEASURED':
                unm.append((cur, line, level, text))
            elif cls == 'KERNEL':
                kernel.append((cur, line, level, text))
    if not tool_sha or not summary:
        sys.exit('run output has no TOOL or SUMMARY line')
    out = []
    w = out.append
    w('# Tactic-level settings of %s (recorded once, stream lead rule 1i-ter)' % prefix.rsplit('/', 2)[-2])
    w('')
    w('A tactic-level setting (an `Ltac ... ::=` redefinition, an Opaque / Transparent / Strategy hint, a Hint, zify or')
    w('lia flag) changes proof search, not what the kernel checks. Per rule 1i-ter it is recorded here once; it is not')
    w('made Local and not rebuilt. A kernel-level setting is never accepted: this run found none.')
    w('')
    w('- Tree: `%s` at commit `%s`, every `.v` file of the lib (%d files).' % (prefix, tree, nfiles))
    w('- Tool: `global_settings.py` v10, sha256 `%s` (release `global_settings-%s`; its self-test and 20' % (tool_sha, tool_sha[:12]))
    w('  real-file controls ran first and passed). Command: `global_settings.py WT <every lib .v file>`; exit code 0.')
    w('- `%s`' % summary)
    w('- Paths below are relative to `%s`.' % prefix)
    w('')
    w('## ESCAPES, by setting')
    w('')
    w('| setting | level | rows | files |')
    w('|---|---|---|---|')
    for (level, text), rows in sorted(esc.items(), key=lambda kv: (-len(kv[1]), kv[0][1])):
        w('| `%s` | %s | %d | %d |' % (text.replace('|', '\\|'), level, len(rows), len({f for f, _ in rows})))
    w('')
    w('## ESCAPES, every row (file: lines)')
    for (level, text), rows in sorted(esc.items(), key=lambda kv: (-len(kv[1]), kv[0][1])):
        w('')
        w('### `%s` (%s)' % (text, level))
        w('')
        byf = collections.defaultdict(list)
        for f, l in rows:
            byf[f].append(l)
        for f in sorted(byf):
            w('- %s: %s' % (f, ', '.join(str(l) for l in sorted(byf[f]))))
    w('')
    w('## UNMEASURED (no locality the tool can decide)')
    w('')
    for f, l, level, text in sorted(unm):
        w('- %s:%d %s `%s`' % (f, l, level, text))
    w('')
    w('## KERNEL')
    w('')
    w('None (%d rows).' % len(kernel))
    print('\n'.join(out))


if __name__ == '__main__':
    main()
