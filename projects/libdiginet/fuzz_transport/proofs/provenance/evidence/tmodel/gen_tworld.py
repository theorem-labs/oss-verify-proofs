#!/usr/bin/env python3
"""Generate lib/TModel/TWorld.v (build-independent world of fuzz_transport's harness model) from the layout TSVs
(LAYOUT_DIR/{globals,structs}.plain.tsv). Checks the ubsan TSVs give the same offsets.
usage: gen_tworld.py OUT LAYOUT_DIR   (LAYOUT_DIR holds {globals,structs}.{plain,ubsan}.tsv)"""
import csv, os, sys, collections
if len(sys.argv) != 3:
    sys.exit('usage: gen_tworld.py OUT LAYOUT_DIR')
L = os.path.join(sys.argv[2], '')
def rows(f): return list(csv.DictReader(open(L + f), delimiter='\t'))
G = {b: {r['name']: r for r in rows(f'globals.{b}.tsv') if r['section'] == '.bss'} for b in ('plain', 'ubsan')}
S = {b: collections.defaultdict(list) for b in ('plain', 'ubsan')}
for b in S:
    for r in rows(f'structs.{b}.tsv'): S[b][r['type_label']].append(r)
basep = min(int(r['addr'], 16) for r in G['plain'].values()); baseu = min(int(r['addr'], 16) for r in G['ubsan'].values())
for n in G['plain']:
    assert int(G['plain'][n]['addr'], 16) - basep == int(G['ubsan'][n]['addr'], 16) - baseu, n
    assert G['plain'][n]['size'] == G['ubsan'][n]['size'], n
assert {k: [(r['member'], r['offset'], r['size']) for r in v] for k, v in S['plain'].items()} == \
       {k: [(r['member'], r['offset'], r['size']) for r in v] for k, v in S['ubsan'].items()}
end = max(int(r['addr'], 16) + int(r['size']) for r in G['plain'].values()) - basep
TYPE = {'M': 'M', 'OW': 'OW', 'GOT': 'GOT', 'g_s': 'struct diginet_session', 'g_cfg': 'struct diginet_session_config',
        'g_cmd': 'struct tagged'}
PFX = {'M': 'M', 'OW': 'OW', 'GOT': 'GOT', 'g_s': 'S', 'g_cfg': 'Cfg', 'g_cmd': 'Cmd', 'g_q': 'Q'}
out = []
w = out.append
w('(* Modified by Theorem Labs, 2026-10: new file, the world of the fuzz_transport harness model (build-independent). *)')
w('(* The 17 writable globals of fuzz/fuzz_transport.c lie in one .bss region of %#x bytes, at the same' % end)
w('   offsets in the plain image (base %#x) and the ubsan image (base %#x). A world is that region as a' % (basep, baseu))
w('   byte list; every global, struct member and array element is read and written at a literal offset.')
w('   Generated from the DWARF of both images; every offset below was checked equal in both. *)')
w('From Stdlib Require Import ZArith List Bool.')
w('From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.')
w('Import ListNotations.')
w('Open Scope Z_scope.')
w('')
w('Definition W_LEN : Z := %#x.' % end)
w('Definition W_BASE_PLAIN : Z := %#x.' % basep)
w('Definition W_BASE_UBSAN : Z := %#x.' % baseu)
w('')
w('Definition sub (bs : list byte) (k : Z) (n : nat) : list byte := firstn n (skipn (Z.to_nat k) bs).')
w('Definition u_at (bs : list byte) (k : Z) (n : nat) : Z := bytes_le_to_Z (sub bs k n).')
w('Definition s32_at (bs : list byte) (k : Z) : Z := bv_swrap 32 (u_at bs k 4).')
w('Definition upd (bs : list byte) (k : Z) (v : list byte) : list byte :=')
w('  firstn (Z.to_nat k) bs ++ v ++ skipn (Z.to_nat k + length v) bs.')
w('Definition put (n : nat) (v : Z) : list byte := Z_to_le_bytes n v.')
w('Definition zs (l : list byte) : list Z := map bv_unsigned l.')
w('Definition bs (l : list Z) : list byte := map (Z_to_bv 8) l.')
w('')
w('(* ---- the globals: offset in the world and size ---- *)')
for n, r in sorted(G['plain'].items(), key=lambda kv: int(kv[1]['addr'], 16)):
    w('Definition OFF_%s : Z := %#x.  Definition SZ_%s : Z := %s.' % (n, int(r['addr'], 16) - basep, n, r['size']))
w('')
def scalar(ctype):
    if '[' in ctype: return None
    return 's' if ctype.strip() in ('int', 'enum diginet_sum_mode') or ctype.startswith('enum') else 'u'
def emit(label, base_expr, pfx, idx_args):
    for r in S['plain'][label]:
        m, off, sz, ct = r['member'], int(r['offset']), int(r['size']), r['ctype_label']
        name = pfx + '_' + m
        if ct.startswith('struct <anon:'):
            sub_label = ct[len('struct <anon:'):-1]
            if r['array_len']:
                n = int(r['array_len']); esz = sz // n
                emit(sub_label, f'({base_expr} + {off} + {esz} * i_{m})', name, idx_args + [f'i_{m}'])
                w(f'Definition {name}_ESZ : Z := {esz}.  Definition {name}_N : Z := {n}.')
            else:
                emit(sub_label, f'({base_expr} + {off})', name, idx_args)
            continue
        if ct.startswith('struct '):
            st = ct.split('[')[0]
            if st in S['plain'] and st != label and not r['array_len']:
                emit(st, f'({base_expr} + {off})', name, idx_args); continue
            if st in S['plain'] and r['array_len']:
                n = int(r['array_len']); esz = sz // n
                emit(st, f'({base_expr} + {off} + {esz} * i_{m})', name, idx_args + [f'i_{m}'])
                w(f'Definition {name}_ESZ : Z := {esz}.  Definition {name}_N : Z := {n}.')
                continue
        args = ''.join(f' ({a} : Z)' for a in idx_args)
        call = ''.join(f' {a}' for a in idx_args)
        if r['array_len'] and ('uint8_t' in ct or 'char' in ct):
            w(f'Definition A_{name}{args} : Z := {base_expr} + {off}.')
            w(f'Definition {name} (B : list byte){args} : list byte := sub B (A_{name}{call}) {sz}.')
            w(f'Definition set_{name} (B : list byte){args} (v : list byte) : list byte := upd B (A_{name}{call}) v.')
        elif r['array_len']:
            n = int(r['array_len']); esz = sz // n
            w(f'Definition A_{name}{args} (i : Z) : Z := {base_expr} + {off} + {esz} * i.')
            g = 's32_at B' if scalar(ct.split('[')[0]) == 's' and esz == 4 else f'fun k => u_at B k {esz}'
            w(f'Definition {name} (B : list byte){args} (i : Z) : Z := ' + (f's32_at B (A_{name}{call} i).' if g.startswith('s32') else f'u_at B (A_{name}{call} i) {esz}.'))
            w(f'Definition set_{name} (B : list byte){args} (i v : Z) : list byte := upd B (A_{name}{call} i) (put {esz} v).')
        else:
            k = scalar(ct)
            w(f'Definition A_{name}{args} : Z := {base_expr} + {off}.')
            if k == 's' and sz == 4:
                w(f'Definition {name} (B : list byte){args} : Z := s32_at B (A_{name}{call}).')
            else:
                w(f'Definition {name} (B : list byte){args} : Z := u_at B (A_{name}{call}) {sz}.')
            w(f'Definition set_{name} (B : list byte){args} (v : Z) : list byte := upd B (A_{name}{call}) (put {sz} v).')
for g, lab in TYPE.items():
    w(f'(* ---- {g} ({lab}) ---- *)')
    if g == 'g_cmd':
        esz = int(G['plain'][g]['size']) // 1024
        w(f'Definition Cmd_ESZ : Z := {esz}.  Definition Cmd_N : Z := 1024.')
        emit(lab, f'(OFF_g_cmd + {esz} * i)', 'Cmd', ['i'])
    else:
        emit(lab, f'OFF_{g}', PFX[g], [])
    w('')
w('(* ---- g_q (unsigned[1024]) and the scalars ---- *)')
w('Definition Q_at (B : list byte) (i : Z) : Z := u_at B (OFF_g_q + 4 * i) 4.')
w('Definition set_Q_at (B : list byte) (i v : Z) : list byte := upd B (OFF_g_q + 4 * i) (put 4 v).')
for n, sz, sg in (('g_now', 8, 'u'), ('g_raw', 4, 's'), ('g_last_counter', 4, 'u'), ('g_rx_send', 4, 'u'),
                  ('g_ncmd', 4, 'u'), ('g_nq', 4, 'u'), ('g_rx', 8, 'u'), ('g_rx_len', 8, 'u'), ('g_rx_fail', 4, 's'),
                  ('g_rx_times', 4, 's')):
    assert int(G['plain'][n]['size']) == sz, n
    get = f's32_at B OFF_{n}' if sg == 's' else f'u_at B OFF_{n} {sz}'
    w(f'Definition {n} (B : list byte) : Z := {get}.')
    w(f'Definition set_{n} (B : list byte) (v : Z) : list byte := upd B OFF_{n} (put {sz} v).')
w('(* g_fail_next: the int was shrunk by the compiler to ONE byte holding 0 or 1 (DWARF value expression');
w('   DW_OP_deref_size 1 ... stack_value); the model reads and writes that byte. *)')
assert int(G['plain']['g_fail_next']['size']) in (1, 4)
w('Definition g_fail_next (B : list byte) : Z := u_at B OFF_g_fail_next 1.')
w('Definition set_g_fail_next (B : list byte) (v : Z) : list byte := upd B OFF_g_fail_next (put 1 v).')
open(sys.argv[1], 'w').write('\n'.join(out) + '\n')
print('lines', len(out), 'W_LEN', hex(end))
