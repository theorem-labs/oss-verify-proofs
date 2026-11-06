#!/usr/bin/env python3
"""Position-abstract listing of a RISC-V program-code range (one slot per 4-byte instruction), in the
lib/A/Prog/<Unit>List.v form of libreac/fuzz_decode's released DecodeList.v / DecodeSyms.v / DecodeAddr.v.

Rules (each checked by the listing's PAImg certificate, pi_check, against the image):
  * every word is PW w, except:
  * jal rd, T with rd <> x0           -> PCall S rd        (S = the symbol at T)
  * jal x0, T with T a symbol outside the jump's own function -> PTail S (a tail call; other jumps stay PW)
  * auipc rd, imm                      -> PHi rd j          (j counts the auipc slots in order; hi[j] = its value)
  * the first instruction after an auipc that reads its rd, when it is an integer load or an addi with rs1 = rd and
    nothing in between writes rd or transfers control:
      ld/lw/.. rd', imm(rd)             -> PLdHi rd' rd j (A_OBJ i) 0 SZ sg
      addi rd', rd, imm                 -> PAddHi rd' rd j (A_OBJ i) 0
    where obj[i] = hi[j] + imm (objects numbered by first use, in slot order; EXTRA objects appended after them).
Inputs: the pinned image (the words), its unstripped twin (the symbol names; its words must equal the image's), the
first listed function and the symbol just past the listed code, and the objects appended after the used ones.
Checked: run on libreac/fuzz_decode's pinned fuzz_decode.asan with that unit's released names, the renderer below
reproduces its released DecodeSyms.v, DecodeAddr.v and DecodeList.v byte for byte.
"""
import struct

def sext(v, bits):
    v &= (1 << bits) - 1
    return v - (1 << bits) if v >> (bits - 1) else v

def zcanon(x):
    return x % (1 << 64)

class Img:
    def __init__(self, path):
        from elftools.elf.elffile import ELFFile
        self.f = ELFFile(open(path, 'rb'))
        self.segs = [s for s in self.f.iter_segments() if s['p_type'] == 'PT_LOAD']
    def word(self, a):
        for s in self.segs:
            if s['p_vaddr'] <= a and a + 4 <= s['p_vaddr'] + s['p_filesz']:
                d = s.data()
                o = a - s['p_vaddr']
                return struct.unpack('<I', d[o:o + 4])[0]
        raise KeyError(hex(a))

LOADS = {0: ('SZ1', True), 1: ('SZ2', True), 2: ('SZ4', True), 3: ('SZ8', True),
         4: ('SZ1', False), 5: ('SZ2', False), 6: ('SZ4', False)}

def fields(w):
    return dict(op=w & 0x7f, rd=(w >> 7) & 31, f3=(w >> 12) & 7, rs1=(w >> 15) & 31, rs2=(w >> 20) & 31,
                iimm=sext(w >> 20, 12))

def jimm(w):
    v = (((w >> 31) & 1) << 20) | (((w >> 12) & 0xff) << 12) | (((w >> 20) & 1) << 11) | (((w >> 21) & 0x3ff) << 1)
    return sext(v, 21)

def reads(w):
    F = fields(w); op = F['op']
    if op in (0x37, 0x17, 0x6f):
        return set()
    if op in (0x33, 0x3b, 0x63, 0x23, 0x2f):
        return {F['rs1'], F['rs2']}
    if op == 0x27:
        return {F['rs1']}
    return {F['rs1']}  # I-type, fp loads, 0x53 (conservative), system

def writes_int(w):
    F = fields(w); op = F['op']
    if op in (0x23, 0x27, 0x63, 0x07):
        return None
    return F['rd']

def is_ctl(w):
    return (w & 0x7f) in (0x63, 0x6f, 0x67)

def listing(img, base, nslots, symname, entries, extra_objs):
    words = [img.word(base + 4 * k) for k in range(nslots)]
    for k, w in enumerate(words):
        if w & 3 != 3:
            raise SystemExit('compressed instruction at 0x%x' % (base + 4 * k))
    slots = [None] * nslots
    his = []
    uses = {}  # slot -> (kind, rd', rs, j, target, sz, sg)
    syms = []
    for k, w in enumerate(words):
        pc = base + 4 * k
        F = fields(w)
        if F['op'] == 0x6f:
            t = zcanon(pc + jimm(w))
            if F['rd'] != 0:
                if t not in symname:
                    raise SystemExit('call at 0x%x to 0x%x: no symbol' % (pc, t))
                slots[k] = ('PCall', symname[t], F['rd'])
            elif t in symname:
                lo = max(a for a in entries if a <= pc)
                hi = min([a for a in entries if a > pc] + [base + 4 * nslots])
                if not (lo <= t < hi):
                    slots[k] = ('PTail', symname[t])
        elif F['op'] == 0x17:
            j = len(his)
            v = zcanon(pc + sext((w >> 12) << 12, 32))
            his.append(v)
            slots[k] = ('PHi', F['rd'], j)
            rd = F['rd']
            for m in range(k + 1, nslots):
                u = words[m]; G = fields(u)
                if rd in reads(u):
                    if G['op'] == 0x03 and G['rs1'] == rd and G['f3'] in LOADS:
                        sz, sg = LOADS[G['f3']]
                        uses[m] = ('PLdHi', G['rd'], rd, j, zcanon(v + G['iimm']), sz, sg)
                    elif G['op'] == 0x13 and G['f3'] == 0 and G['rs1'] == rd:
                        uses[m] = ('PAddHi', G['rd'], rd, j, zcanon(v + G['iimm']))
                    break
                if writes_int(u) == rd or is_ctl(u):
                    break
    objs = []
    for k in range(nslots):
        if k in uses:
            if slots[k] is not None:
                raise SystemExit('slot %d both' % k)
            t = uses[k][4]
            if t not in objs:
                objs.append(t)
            slots[k] = uses[k]
    for t in extra_objs:
        objs.append(t)
    for k, s in enumerate(slots):
        if s is not None and s[0] in ('PCall', 'PTail') and s[1] not in syms:
            syms.append(s[1])
    return words, slots, his, objs, syms

def render_slot(w, s, objs, pre):
    if s is None:
        return 'PW 0x%x' % w
    if s[0] == 'PCall':
        return 'PCall %s%s (%d%%bv : reg)' % (pre, s[1], s[2])
    if s[0] == 'PTail':
        return 'PTail %s%s' % (pre, s[1])
    if s[0] == 'PHi':
        return 'PHi (%d%%bv : reg) %d' % (s[1], s[2])
    if s[0] == 'PLdHi':
        return 'PLdHi (%d%%bv : reg) (%d%%bv : reg) %d (A_OBJ %d) 0x0 %s %s' % (s[1], s[2], s[3], objs.index(s[4]), s[5], 'true' if s[6] else 'false')
    if s[0] == 'PAddHi':
        return 'PAddHi (%d%%bv : reg) (%d%%bv : reg) %d (A_OBJ %d) 0x0' % (s[1], s[2], s[3], objs.index(s[4]))
    raise ValueError(s)


HDR_DATA = ("(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data "
            "blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to "
            "this file. *)")


def hdr_list(project):
    return ("(* This file states or restates instruction words of the task's compiled program (third-party object code: %s "
            "and the harness, compiled with the memory-checking runtime) for use in the proofs - see NOTICE. No Anthropic "
            "licence header is applied to this file. *)" % project)


def render(P):
    """The three files (syms, addr, list) as text, in the released form of fuzz_decode's DecodeSyms.v / DecodeAddr.v /
    DecodeList.v."""
    syms = [HDR_DATA,
            "(* The names the listing of %s's program code calls: the memory-checking" % P['img'],
            "   runtime's entries, the wrappers' trampolines, and the program functions that",
            "   have their own contract. *)",
            "From Stdlib Require Import ZArith.",
            "Inductive %s : Type :=" % P['ty']]
    syms += ["| %s%s" % (P['cp'], s) for s in P['syms']]
    syms[-1] += "."
    u = P['unit']
    addr = [HDR_DATA,
            "(* The addresses %s gives the listing's names, objects and auipc values." % P['img'],
            "   The PAImg instance of this image checks them against the image. The objects",
            "   past the ones the slots build are the cells the walks read through a GOT",
            "   word: __asan_shadow_memory_dynamic_address (the shadow base) and",
            "   __asan_option_detect_stack_use_after_return. *)",
            "From %s Require Import PaTable." % P['pre'],
            "From %s Require Import %s." % (P['pre'], P['ModSyms']),
            "From Stdlib Require Import ZArith List.",
            "Import ListNotations.",
            "Open Scope Z_scope.",
            "Definition %s_text : Z := 0x%x." % (u, P['base']),
            "Definition %s_sigma (s : %s) : Z :=" % (u, P['ty']),
            "match s with"]
    addr += ["| %s%s => 0x%x" % (P['cp'], s, P['sigma'][s]) for s in P['syms']]
    addr += ["end.", "Definition %s_obj (i : nat) : Z :=" % u, "match i with"]
    addr += ["| %d%%nat => 0x%x" % (i, v) for i, v in enumerate(P['objs'])]
    addr += ["| _ => 0", "end.", "Definition %s_hi (j : nat) : Z :=" % u, "match j with"]
    addr += ["| %d%%nat => 0x%x" % (i, v) for i, v in enumerate(P['his'])]
    addr += ["| _ => 0", "end.",
             "Definition %s_nobj : nat := %d%%nat." % (u, len(P['objs'])),
             "Definition %s_nhi : nat := %d%%nat." % (u, len(P['his']))]
    lst = [hdr_list(P['project']),
           "(* %s's program code as a position-abstract listing: one slot per" % P['img'],
           "   4-byte instruction from the entry function's address upwards. *)",
           "From %s Require Import PaTable." % P['pre'],
           "From %s Require Import %s." % (P['pre'], P['ModSyms']),
           "From Stdlib Require Import ZArith List.",
           "From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.",
           "From LinuxProcessSemantics.Riscv Require Import Prelude Instr.",
           "Import ListNotations.",
           'Local Set Warnings "-abstract-large-number".',
           "Open Scope bv_scope. Open Scope Z_scope."]
    lst += ["Definition AF_%s : Z := 0x%x." % (n, o) for n, o in P['funcs']]
    lst += ["Definition %s_nslots : nat := %d%%nat." % (u, P['nslots']),
            "Definition %s_listing : ptable %s := [" % (u, P['ty'])]
    body = [render_slot(w, s, P['objs'], P['cp']) for w, s in zip(P['words'], P['slots'])]
    lst += [b + ";" for b in body[:-1]] + [body[-1], "]."]
    return '\n'.join(syms) + '\n', '\n'.join(addr) + '\n', '\n'.join(lst) + '\n'


def ident(name):
    return name.replace('.', '_')


def main():
    import argparse
    from elftools.elf.elffile import ELFFile
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('image', help='the pinned image (the words of the listing are read from it)')
    ap.add_argument('unstripped', help='its unstripped twin (symbol names only; its words must equal the image\'s)')
    ap.add_argument('--first', required=True, help='symbol of the first listed function')
    ap.add_argument('--end', required=True, help='symbol just past the listed code')
    ap.add_argument('--extra', nargs='*', default=[], help='symbols of the objects appended after the used ones')
    ap.add_argument('--pre', required=True, help='Rocq module prefix of lib.A.Prog')
    ap.add_argument('--img', required=True); ap.add_argument('--project', required=True)
    ap.add_argument('--unit', required=True); ap.add_argument('--ty', required=True); ap.add_argument('--cp', required=True)
    ap.add_argument('--mod-syms', required=True); ap.add_argument('--outdir', required=True)
    ap.add_argument('--out', nargs=3, required=True, help='file names: syms addr list')
    a = ap.parse_args()
    fu = ELFFile(open(a.unstripped, 'rb'))
    names = {}
    for s in fu.get_section_by_name('.symtab').iter_symbols():
        if s['st_value'] and s.name and not s.name.startswith('$'):
            names.setdefault(s['st_value'], []).append((s.name, s['st_info']['type']))
    byname = {n: v for v, l in names.items() for n, _ in l}
    base, end = byname[a.first], byname[a.end]
    img, twin = Img(a.image), Img(a.unstripped)
    nslots = (end - base) // 4
    for k in range(nslots):
        if img.word(base + 4 * k) != twin.word(base + 4 * k):
            raise SystemExit('image and twin differ at 0x%x' % (base + 4 * k))
    funcs = sorted((v, n) for v, l in names.items() if base <= v < end for n, t in l if t == 'STT_FUNC')

    def pick(t):
        ns = [n for n, ty in names.get(t, []) if ty == 'STT_FUNC'] or [n for n, _ in names.get(t, [])]
        if len(ns) > 1:
            tr = [n for n in ns if n.startswith('__interceptor_trampoline_')]
            if len(tr) != 1:
                raise SystemExit('ambiguous names at 0x%x: %s' % (t, ns))
            return tr[0]
        if not ns:
            raise SystemExit('no symbol at 0x%x' % t)
        return ns[0]
    symname = {}
    for k in range(nslots):
        w = img.word(base + 4 * k)
        if w & 0x7f == 0x6f:
            t = zcanon(base + 4 * k + jimm(w))
            if t in names:
                symname[t] = ident(pick(t))
    words, slots, his, objs, syms = listing(img, base, nslots, symname, [v for v, _ in funcs],
                                            [byname[x] for x in a.extra])
    sigma = {n: t for t, n in symname.items()}
    P = dict(pre=a.pre, img=a.img, project=a.project, unit=a.unit, ty=a.ty, cp=a.cp, ModSyms=a.mod_syms, base=base,
             nslots=nslots, funcs=[(ident(n), v - base) for v, n in funcs], words=words, slots=slots, his=his,
             objs=objs, syms=syms, sigma=sigma)
    for name, text in zip(a.out, render(P)):
        open('%s/%s' % (a.outdir, name), 'w').write(text)


if __name__ == '__main__':
    main()
