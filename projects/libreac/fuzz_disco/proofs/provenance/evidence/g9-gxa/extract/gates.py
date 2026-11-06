#!/usr/bin/env python3
"""Clean per-value tables of the gate records of the G9 layer and of the GXA / Bz memory layers. Each subcommand reads
its record (the files given as arguments, nothing else) and writes one tab-separated table to standard output: only
the values a reader checks, no comment text, no narrative, no path of the machine the record was made on. Tables
built here name the two fuzz_disco images A (asan) and B (asan-ubsan); a record that calls image B `Y` is mapped.

  gates.py numeral-audit AUDIT_JSON
      The rows the independent audit of the P0 numeral table flagged for a second look (its raw output, audit.json):
      check, fm file, fm value, image, disco value, what the audit measured there.
  gates.py numerals-rest NUMERALS_REST_MD
      The P0 numerals left unresolved and the decision on each (the table of numerals-rest.md).
  gates.py call-sites SITE_CHECK_MD RECHECK_A_MD RECHECK_B_MD
      The snprintf call sites of both images (site-check.md) with the call pcs and the verdicts of the two
      independent re-measurements; the format address, its length and its end must be the same in all three records.
  gates.py record-rows RECHECK_OUT
      The effective exact rows of the GXA image records at the vfprintf body on both images (part 1 of recheck.out):
      override or base row, key, value, the section and symbol at the value, the row's role.
  gates.py old-vs-fixed OLD_VS_FIXED_TSV
      The recorded table of every numeral whose output differs between the first and the fixed G9 tool, without its
      comment lines (its data rows are kept as recorded; it calls image B `Y`).
  gates.py alreloc-moves NUMERAL_MOVES_TSV
      The numerals the image-A memcpy-side walk move rewrote, with their reverse resolution; the header line is
      replaced by plain column names, the data rows are kept as recorded.
  gates.py addrcheck-A MEMSET_DIR TABLE_DIR
      The address checker outputs of image A against the fuzz_reply donor files (the memset walk files in MEMSET_DIR,
      the A table and its call contracts in TABLE_DIR), one table, the checked file in the first column.
  gates.py addrcheck-B TWINS_DIR
      The address checker outputs of the image-B twins against their image-A files (TWINS_DIR), one table.
  gates.py inventory-B INVENTORY_MD
      The inventory of the image-B twins: per file its class, blobs and twin comparisons, and per moved numeral its
      A value, B value, symbol + offset in image A and lines.
"""
import json
import re
import sys

IMG = {'A': 'A', 'Y': 'B'}
# the address checker's output columns (port_addr_check.py COLS)
PAC_COLS = ['verdict', 'kernel_checked', 'image', 'src_file', 'src_line', 'dst_file', 'dst_line', 'sentence', 'idx',
            'kind', 'src_value', 'dst_value', 'src_class', 'src_res', 'dst_res', 'note']
# addrcheck-A: (checked file, directory argument, record file name)
CHECKS_A = [('lib/A/Bz/A/I_memsetw.v', 0, 'pac-I_memsetw.tsv'), ('lib/A/Bz/A/I_imemset.v', 0, 'pac-I_imemset.tsv'),
            ('lib/A/RT_gxa_mem_Tbl.v', 1, 'pac-RT_gxa_mem_Tbl.tsv'),
            ('lib/A/RT_gxa_calls_mem.v', 1, 'pac-RT_gxa_calls_mem.tsv')]
# addrcheck-B: the twins (record file lib_B_<path with / as _>.v.tsv), then the contracts (renamed runs)
TWINS_B = ['Bz/A/F_memset', 'Bz/A/I_amemcpy', 'Bz/A/I_amemcpyw', 'Bz/A/I_amemcpyw2', 'Bz/A/I_consts', 'Bz/A/I_imemset',
           'Bz/A/I_memcpy', 'Bz/A/I_memcpyw', 'Bz/A/I_memcpyw2', 'Bz/A/I_memsetw', 'Bz/A/R_isPoisoned', 'Bz/A/R_m2s',
           'Bz/A/R_memiszero', 'Bz/A/R_small', 'Bz/Lib/ImageA', 'Prog/memcpy', 'Prog/memcpy_c', 'Prog/memcpy_same',
           'Prog/memcpy_same_c', 'Prog/memset_c', 'RT_mem_bz', 'R_memset', 'RT_gxa_bridge', 'RT_gxa_mem_Tbl']
CHECKS_B = ([('lib/B/%s.v' % p, 'lib_B_%s.v.tsv' % p.replace('/', '_')) for p in TWINS_B]
            + [('lib/B/RT_gxa_calls_mem.v', 'lib_B_RT_gxa_calls_mem.v.ren.tsv'),
               ('lib/CJ/RL/I/RecAsanB.v', 'lib_CJ_RL_I_RecAsanB.v.ren.tsv')])


def die(msg):
    sys.exit('gates.py: ' + msg)


def emit(rows):
    for r in rows:
        if any('\t' in c or '\n' in c for c in r):
            die('a cell holds a tab or a newline: %r' % (r,))
    sys.stdout.write(''.join('\t'.join(r) + '\n' for r in rows))


def lines_of(path):
    return open(path, encoding='utf-8').read().split('\n')


def md_cells(line):
    """the cells of one markdown table line: they are separated by ' | ' (a bare '|' inside a cell, as in |s|, is text)"""
    return [c.strip().replace('\\|', '|').replace('`', '') for c in re.split(r' \| ', line.strip()[1:-1])]


def md_table(path, head):
    """the body rows of the first markdown table whose header line starts with `head`, as lists of clean cells"""
    ls = lines_of(path)
    i = next((k for k, l in enumerate(ls) if l.startswith(head)), None)
    if i is None:
        die('%s: no table headed %r' % (path, head))
    width = len(md_cells(ls[i]))
    out = []
    for l in ls[i + 2:]:
        if not l.startswith('|'):
            break
        cells = md_cells(l)
        if len(cells) != width:
            die('%s: a row of the table %r has %d cells, not %d' % (path, head, len(cells), width))
        out.append(cells)
    return out


def numeral_audit(path):
    rows = [['check', 'file (fm lib)', 'fm value', 'image', 'disco value', 'what the audit measured']]
    for check, found in json.load(open(path)).items():
        for r in found:
            f, v, im = r[0], r[1], IMG[r[2]]
            if check == 'C6-end-slide':
                dv, what = '-', '%s: fm end of %s; disco end of %s' % (r[3], ' / '.join(r[5]), ' / '.join(r[7]))
            elif check == 'C4-bound-not-a-seg-bound':
                dv, what = r[3], r[4]
            elif check == 'C2-anon-bytes-differ':
                dv, what = r[3], '%s; %s: fm bytes %s, disco bytes %s' % (r[7], r[4], r[5], r[6])
            else:
                die('%s: unknown check %s' % (path, check))
            rows.append([check, f, v, im, dv, what])
    emit(rows)


def numerals_rest(path):
    body = md_table(path, '| file | numeral |')
    if any(r[4] != 'DROP' for r in body):
        die('%s: a row is not DROP' % path)
    emit([['file (fm lib)', 'numeral', 'fm meaning', 'defining name', 'verdict', 'drops with it', 'measured']] + body)


def call_sites(site, rec_a, rec_b):
    s = md_table(site, '| # | source line |')
    a = md_table(rec_a, '| # | pc (jal) |')
    b = md_table(rec_b, '| # | pc (fn) |')
    if not ([r[0] for r in s] == [r[0] for r in a] == [r[0] for r in b]):
        die('the three records list different sites')
    rows = [['site', 'source line', 'fmt addr', 'fmt text', '|fmt|', 'end', '%s args', 'A call pc', 'B call pc',
             'P-range', 'P-ne', 'P-slack', 'P-amem', 'A re-measurement', 'B re-measurement']]
    for rs, ra, rb in zip(s, a, b):
        text, n = ra[3].rsplit(' / ', 1)
        if not (rs[2] == ra[2].split()[0] == rb[2] and rs[3] == n == rb[4] and rs[4] == rb[5]):
            die('site %s: the records differ in the format address, length or end' % rs[0])
        rows.append([rs[0], rs[1], rs[2], text, rs[3], rs[4], rs[7], ra[1], rb[1].split()[0], rs[5], rs[6], rs[8],
                     rs[9], ra[11], rb[11]])
    emit(rows)


def record_rows(path):
    rows = [['image', 'row', 'key', 'value', 'section', 'what is at the value', 'role']]
    img = None
    pat = re.compile(r'  (base|override)\s+key (0x[0-9a-f]+) -> (0x[0-9a-f]+)  \[(.*?)\s*\]  (.*?)   role: (.*)$')
    for l in lines_of(path):
        if l.startswith('PART 2'):
            break
        m = re.match(r'IMAGE (\S+) ', l)
        if m:
            img = IMG[m.group(1)]
            continue
        m = pat.match(l)
        if m:
            role = m.group(6)
            rows.append([img, m.group(1), hex(int(m.group(2), 16)), hex(int(m.group(3), 16)), m.group(4), m.group(5),
                         '-' if role == '?' else role])
    if len(rows) == 1:
        die('%s: no record row' % path)
    emit(rows)


def old_vs_fixed(path):
    body = [l for l in lines_of(path) if l and not l.startswith('#')]
    if not body[0].startswith('image\tfile (fm lib/A)\tline\tfm value\told output\tnew output\treason'):
        die('%s: unexpected header' % path)
    if any(len(l.split('\t')) != 7 for l in body):
        die('%s: a row has not 7 fields' % path)
    emit([l.split('\t') for l in body])


def alreloc_moves(path):
    ls = [l for l in lines_of(path) if l]
    if not ls[0].startswith('file\tline\told\tnew\trule\treverse-provenance'):
        die('%s: unexpected header' % path)
    body = [l.split('\t') for l in ls[1:]]
    if any(len(r) != 6 for r in body):
        die('%s: a row has not 6 fields' % path)
    emit([['file (fm lib)', 'line', 'fm value', 'A value', 'rule', 'reverse resolution']] + body)


def pac_table(checks):
    rows = [['checked file'] + [c for c in PAC_COLS if c != 'image']]
    for label, path in checks:
        ls = [l for l in lines_of(path) if l]
        if ls[0].split('\t') != PAC_COLS:
            die('%s: not an address checker output' % path)
        for l in ls[1:]:
            r = l.split('\t')
            if len(r) != len(PAC_COLS) or r[2] != 'A':
                die('%s: unexpected row %r' % (path, l))
            rows.append([label] + r[:2] + r[3:])
    emit(rows)


def inventory_b(path):
    inv = md_table(path, '| lib/B file | class |')
    moved = {}
    for l in lines_of(path):
        m = re.match(r'- (lib/B/\S+\.v) \((\d+) occurrences\): (.*)$', l.replace('`', ''))
        if m:
            vals = re.findall(r'(0x[0-9a-f]+|\d+) -> (0x[0-9a-f]+|\d+) \((.*?); l\.([0-9,]+)\)', m.group(3))
            if sum(len(x[3].split(',')) for x in vals) != int(m.group(2)):
                die('%s: %s lists not %s occurrences' % (path, m.group(1), m.group(2)))
            moved[m.group(1)] = vals
    twin = lambda c: re.sub(r' =$', ' same', re.sub(r' \u2260$', ' differs', c))
    rows = [['lib/B file', 'class', 'numerals changed', 'B blob', 'A donor blob', 'twin at 63064ea86fe',
             'twin at 4c529cf6485', 'A value', 'B value', 'symbol + offset in image A', 'lines']]
    for f, cls, n, bb, ab, t1, t2 in inv:
        vals = moved.pop(f, [])
        if sum(len(x[3].split(',')) for x in vals) != int(n):
            die('%s: %s changes %s numerals, its list says otherwise' % (path, f, n))
        head = [f, cls, n, bb, ab, twin(t1), twin(t2)]
        rows += [head + list(x) for x in vals] or [head + ['-'] * 4]
    if moved:
        die('%s: numerals listed for files not in the inventory: %s' % (path, ', '.join(moved)))
    emit(rows)


def main(a):
    cmds = {'numeral-audit': (numeral_audit, 1), 'numerals-rest': (numerals_rest, 1), 'call-sites': (call_sites, 3),
            'record-rows': (record_rows, 1), 'old-vs-fixed': (old_vs_fixed, 1), 'alreloc-moves': (alreloc_moves, 1),
            'addrcheck-A': (lambda c, d: pac_table([(f, '%s/%s' % ((c, d)[k], n)) for f, k, n in CHECKS_A]), 2),
            'addrcheck-B': (lambda y: pac_table([(f, '%s/%s' % (y, n)) for f, n in CHECKS_B]), 1),
            'inventory-B': (inventory_b, 1)}
    if not a or a[0] not in cmds or len(a) - 1 != cmds[a[0]][1]:
        sys.exit(__doc__)
    cmds[a[0]][0](*a[1:])


if __name__ == '__main__':
    main(sys.argv[1:])
