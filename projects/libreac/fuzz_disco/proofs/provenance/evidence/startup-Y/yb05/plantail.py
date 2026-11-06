#!/usr/bin/env python3
"""plantail.py -- complete a relocated start-up plan's tail for a unit whose asan_globals table differs from the donor's.

  plantail.py probe  --lib LIB --dir ZReplyA --out-dir ZStartColR --main 0x81e4c [--iters 40]
  plantail.py probef --lib LIB --img IMAGEMOD --dir ZReplyA --out-dir ZStartColF --main 0x81e4c [--tail-tokens XMemset]
  plantail.py insert --plan PLAN.v --main 0x81e4c --nodes XMemset[,XMemset,...] [--count N]
  plantail.py insert --plan PLAN.v --main 0x81e4c --replace-tail --from-probe PROBEF.log [--tail-tokens XMemset]
  plantail.py globals IMAGE                      # the image's asan_globals descriptor count

Why. `__asan_register_globals` poisons each descriptor's redzone; a poison large enough to leave the inline path calls
__asan_memset, and x_memset is in STOPS (lib/YK09.v:2706), so the plan's last `PRun [main]` stops THERE and not at main.
The donor's plan (cgif, 3 descriptors) ends with four `PX XMemset [] (PRun [] ...)` pairs; a unit with a different
descriptor table needs a different number of them. The count is NOT a function of the descriptor count (fuzz_reply's 27
descriptors need ONE more pair than cgif's 3, MEASURED: tools/startup/runs/replyA/probe.log), because whether a poison
leaves the inline path depends on the region's size and alignment. So the number is MEASURED per image, by `probe`:

  probe   writes <LIB>/<out-dir>/Probe.v, which iterates, from each collected hand-off state, "apply the summary of the
          routine the state stopped in, then run to `main` OR to the next routine of STOPS", and prints the pc after each
          step (the run MUST carry STOPS: with `main` alone it walks straight through the registration loop). Build it (cgb rmake) and
          read the pc list: every pc before `main` is one missing pair, and its value names the routine (x_memset,
          x_imemset, ...) through the unit's atable.
  insert  puts the nodes in front of every final `PRun [main]` of the plan. `--nodes` takes the start-up command's spelling,
          `XMemset*64,PMmap,XMemset*113`: a summary token repeated, or `PMmap` for the registration's own mmap arm
          (the ODR-indicator path's DenseMap bucket allocation), which opens the same two parentheses as a summary pair.
          A negative pc in the probe's list is an ECALL the plan has no node for: that is where a PMmap goes.
  globals prints the descriptor count (asan_globals section size / 64) — a report number, not the rule's input.
  drop-registration  0 descriptors (knock): remove the registration arm (loop head .. the arm's final PRun [main]) from
          every arm. Regression: knock's ab05.before.v -> ab05.after.v byte for byte (the knock port's armcut.py, whose
          certificate on knock.asan returned COk with cgif's own startup_shape, runs/cert.log).

The ODR arm (probef + insert --replace-tail). A descriptor with an odr_indicator sends __asan_register_globals through
the DenseMap find-or-insert, whose first bucket allocation is an mmap ECALL (decode: internal_mmap+4 0x63d40 from
MmapOrDie; scene: just before a descriptor memset). A run halts AT an ecall (an ecall is never in the itab), so the
PRun before the next PX stops there and the PX fails (failure leaf 10321), or, when the ecall comes after the plan's
last pair, the hand-off state sits at the ecall with a3..a7 havocked by PHavoc. Neither state tells WHERE in the
registration the ecall falls, so the tail is measured from its start:

  probef  writes <LIB>/<out-dir>/{PlanF,ProbeF,ColA}.v. PlanF.v is the plan with every arm's TAIL cut: the tail is the
          maximal run of `(PRun [] (PX T [] ` pairs (T in --tail-tokens) and PMmap arms `(PRun [] (PMmap (PRun []
          (PSpin )) ` in front of the final `PRun [main] (PHavoc .. (PHandoff h))`; the run and the hand-off become
          `(PRun [main] (PContra ))`, so the collector's FAILURE leaf of every arm (10306) is the un-havocked state at the
          registration's first stop. ProbeF.v recomputes COLA.collect on PlanF as Pass2.v does (follow = true, the plan's
          own join state), takes COLA.fail_leaves and iterates from each: a stop in a summary routine prints `TX <node>
          <pc>` and applies node_x, an ecall prints `TMmap <pc> <ra>` and takes node_mmap2g's GRANTED child (the child
          the checker follows, YA0c.v:236-270), each followed by a run to `main` or the next routine of STOPS, until
          `TMain`. The token list IS the whole tail: TX x = one `(PRun [] (PX x [] ` pair, TMmap = one PMmap arm, keyed
          on the ecall site the run met.
  insert --replace-tail strips each arm's tail (the same definition) and writes the given nodes in its place, closing
          two parentheses per node after `(PHandoff h)`. `--from-probe LOG` reads the nodes from ProbeF's log and refuses
          unless every leaf is a cut leaf (10306), every list ends in TMain, all lists give the same nodes, every node is
          in --tail-tokens or PMmap, and the log's PROBEF_CUT equals the cut signature of PLAN (same plan outside the
          tails, same main, same --tail-tokens). Re-running it on its own output changes nothing.

Donor check: on cgif the probe's first pc is already `main`, so `insert --count 0` leaves A/AB05.v unchanged (its tail is
the donor's four pairs). fuzz_reply.asan: one pair at x_memset. An image with no descriptors at all (fuzz_knock:
__asan_register_elf_globals returns early) is NOT yet tested.
"""
import argparse, collections, hashlib, os, re, sys

PROBE = '''(* GENERATED by tools/startup/plantail.py probe (start-up tools): the summaries the plan's tail still needs *)
From %(ns)s Require YZ00.
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From LinuxProcessSemantics.Riscv Require Import Instr.
From %(img)s Require Import %(imgleaf)s.
From %(nscore)s Require Import YK0c YK09 YA01 YA0c YA02 YA0h.
From %(nsdir)s Require Import %(tab)s %(segs)s %(xn)s %(plan)s %(hs)s.
From %(nsout)s Require Import ColA.
Import ListNotations. Import AX2. Import APC. Import APG.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Definition IT0 : itab := mk_itab_ranges TSEGS %(planname)s_ranges.
Definition MAIN : Z := %(main)s.
(* the summary of the routine the state stopped in, by its atable entry *)
Definition node_of (cs : acs) : option xnode :=
let p := pc cs in
if Z.eqb p (x_memset TFIB) then Some XMemset
else if Z.eqb p (x_imemset TFIB) then Some XIMemset
else if Z.eqb p (x_memcpy TFIB) then Some XMemcpy
else if Z.eqb p (x_imemcpy TFIB) then Some XIMemcpy
else if Z.eqb p (x_memiszero TFIB) then Some XMemIsZero
else if Z.eqb p (x_istrncpy TFIB) then Some XIStrncpy
else None.
Definition cont (cs : acs) : option acs := run_block_gc TSEGS IT0 NX0G 0 400000 (MAIN :: STOPS TFIB) cs.
Definition step (cs : acs) : option acs :=
match node_of cs with
| Some x => match node_x TSEGS TFIB NX0G x [] cs with Some c => cont c | None => None end
| None =>
    (* an ecall the plan has no node for: take the mmap arm's GRANTED child, as the checker's PMmap does
       (the ODR-indicator path's DenseMap bucket allocation) *)
    if is_ecall_at TSEGS cs then
      match node_mmap2g TFIB NX0G YA02.LIMIT cs with Some (_, csb) => cont csb | None => None end
    else None
end.
Fixpoint iter (n : nat) (cs : acs) : list Z :=
match n with
| O => [pc cs]
| S n' => if Z.eqb (pc cs) MAIN then [pc cs] else
          (if is_ecall_at TSEGS cs then (- pc cs) else pc cs) ::
          match step cs with Some c => iter n' c | None => [-1] end
end.
Definition TAILDUMP := 0.
Print TAILDUMP.
Time Eval vm_compute in (List.map (fun h => match %(hsname)s h with Some c => iter %(iters)d c | None => [-2] end)
  (List.seq 0 %(nholes)d)).
'''

PROBEF = '''(* GENERATED by tools/startup/plantail.py probef (start-up tools): the plan's whole registration tail, measured
   from the collector's failure leaves of PlanF.v (the plan with every arm's tail cut at its start) -- not part of the proof *)
From %(ns)s Require YZ00.
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From LinuxProcessSemantics.Riscv Require Import Instr.
From %(img)s Require Import %(imgleaf)s.
From %(nscore)s Require Import YK0c YK09 YA01 YA0c YA02 YA0h.
From %(nsdir)s Require Import %(tab)s %(segs)s %(xn)s.
From %(nsout)s Require Import ColA PlanF.
Import ListNotations. Import AX2. Import APC. Import APG.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Definition IT0 : itab := mk_itab_ranges TSEGS %(planname)s_ranges.
Definition MAIN : Z := %(main)s.
Inductive ptok : Type :=
| TX (x : xnode) (p : Z)      (* stopped in routine x at pc p: one (PRun [] (PX x [] ..)) pair *)
| TMmap (p : Z) (ra : expr)   (* an ecall at pc p (return address ra) that node_mmap2g takes: one PMmap arm *)
| TMain                       (* main reached: the tail is complete *)
| TStop (p : Z)               (* stopped at pc p, neither in a summary routine nor at an ecall *)
| TFailX (p : Z)              (* node_x refused the summary at pc p *)
| TFailMmap (p : Z)           (* node_mmap2g refused the ecall at pc p *)
| TFailRun (p : Z)            (* the run from pc p failed *)
| TFuel (p : Z).              (* the iteration bound ran out at pc p *)
(* the summary of the routine the state stopped in, by its atable entry *)
Definition node_of (cs : acs) : option xnode :=
let p := pc cs in
if Z.eqb p (x_memset TFIB) then Some XMemset
else if Z.eqb p (x_imemset TFIB) then Some XIMemset
else if Z.eqb p (x_memcpy TFIB) then Some XMemcpy
else if Z.eqb p (x_imemcpy TFIB) then Some XIMemcpy
else if Z.eqb p (x_memiszero TFIB) then Some XMemIsZero
else if Z.eqb p (x_istrncpy TFIB) then Some XIStrncpy
else None.
(* the run of the next node: (PRun [] ..) stops at STOPS or an ecall; the final (PRun [main] ..) also at main *)
Definition cont (cs : acs) : option acs := run_block_gc TSEGS IT0 NX0G 0 400000 (MAIN :: STOPS TFIB) cs.
Fixpoint iter (n : nat) (cs : acs) : list ptok :=
match n with
| O => [TFuel (pc cs)]
| S n' =>
  if Z.eqb (pc cs) MAIN then [TMain] else
  match node_of cs with
  | Some x =>
      TX x (pc cs) ::
      match node_x TSEGS TFIB NX0G x [] cs with
      | Some c => match cont c with Some c' => iter n' c' | None => [TFailRun (pc c)] end
      | None => [TFailX (pc cs)]
      end
  | None =>
      if is_ecall_at TSEGS cs then
        (* the PMmap arm: the checker follows the GRANTED child (YA0c.v check, PMmap) *)
        TMmap (pc cs) (List.nth (S O) (s_regs (a_ss cs)) (ELit 0)) ::
        match node_mmap2g TFIB NX0G YA02.LIMIT cs with
        | Some (_, csb) => match cont csb with Some c' => iter n' c' | None => [TFailRun (pc csb)] end
        | None => [TFailMmap (pc cs)]
        end
      else [TStop (pc cs)]
  end
end.
(* Pass2.v's collection, on the cut plan: each arm ends in a failure leaf (10306) at the registration's first stop *)
Time Definition LVF : list (nat * acs) := Eval vm_compute in
  (COLA.collect TSEGS IT0 TFIB NX0G YA02.LIMIT (XNG TSEGS tfib_XN1) XE0 XB0 0 400000 true 3000 None (init_acs_of_g TFIB) %(planname)s []).
Eval vm_compute in (List.length LVF).
Eval vm_compute in (List.map COLA.leaf_sum LVF).
Set Printing Width 4000000. Set Printing Depth 1000000.
Definition PROBEF_CUT : Z := %(cut)d.
Print PROBEF_CUT.
Definition PROBEF := 0.
Print PROBEF.
Time Eval vm_compute in (List.map (fun p => (fst p, iter %(iters)d (snd p))) (COLA.fail_leaves LVF)).
'''


SIDE_NAMES = {'A': dict(tab='AB12', segs='AB1h', xn='AB1l', plan='AB05', hs='AB01', dir='ZReplyA'),
              'B': dict(tab='YB12', segs='YB1h', xn='YB1l', plan='YB05', hs='YB01', dir='ZReplyB')}


def side_names(a):
    """fill the side's donor file names (each overridable) and return the template names shared by probe and probef"""
    for k, v in SIDE_NAMES[a.side].items():
        if getattr(a, k, 'absent') is None:
            setattr(a, k, v)
    return dict(ns=a.ns, nscore=(a.ns_core or a.ns), nsdir=(a.ns_dir or (a.ns + '.' + a.dir)),
                nsout=(a.ns_out or (a.ns + '.' + a.out_dir)),
                img=a.img.rsplit('.', 1)[0], imgleaf=a.img.rsplit('.', 1)[1], dir=a.dir, outdir=a.out_dir,
                tab=a.tab, segs=a.segs, xn=a.xn, plan=a.plan, planname=a.planname, main=a.main, iters=a.iters)


def write_if_differs(path, text):
    """write only when the content differs: a rewritten .v (even with the same bytes) makes make rebuild what Requires it"""
    if os.path.exists(path) and open(path).read() == text:
        return False
    open(path, 'w').write(text)
    return True


def write_cola(out, ns):
    # the probe drivers Require ColA from their own directory: write it there (a runner whose drivers sit elsewhere hit this)
    col = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'coq', 'ColA.v')).read().replace('@NS@', ns)
    cpath = os.path.join(out, 'ColA.v')
    if write_if_differs(cpath, col):
        print('plantail: wrote %s (it differed: every Pass*.vo in %s will be rebuilt)' % (cpath, out))


def cmd_probe(a):
    d = side_names(a)
    d.update(hs=a.hs, hsname=a.hsname, nholes=a.nholes)
    out = os.path.join(a.lib, a.out_dir)
    os.makedirs(out, exist_ok=True)
    open(os.path.join(out, 'Probe.v'), 'w').write(PROBE % d)
    write_cola(out, a.ns)
    print('plantail: wrote %s/{Probe,ColA}.v (main %s, %d holes)' % (out, a.main, a.nholes))


def parse_nodes(spec):
    """`--nodes XMemset*64,PMmap,XMemset*113` (the start-up command's spelling): a summary token repeated, or PMmap for the
    registration's own mmap arm (the ODR-indicator path's DenseMap bucket allocation)"""
    out = []
    for item in (spec or '').split(','):
        if not item:
            continue
        name, _, cnt = item.partition('*')
        out += [name.strip()] * (int(cnt) if cnt else 1)
    return out


# the donor's own arm text: the refused child is closed inline, the granted one continues, so a PMmap opens exactly two
# parentheses that stay open - the same as a (PRun [] (PX ... )) pair
MMAP = '(PRun []\n(PMmap\n(PRun []\n(PSpin  ))\n'


def node_text(n):
    return MMAP if n == 'PMmap' else '(PRun []\n(PX %s []\n' % n


# ---- the registration tail of an arm, shared by probef (cut) and insert --replace-tail (strip and re-emit) ----
# One arm ends  <prefix> <tail> (PRun [main]\n(PHavoc [..]%nat\n(PHandoff h  )))..  where <tail> is the maximal run of
# tail nodes: `(PRun [] (PX T [] ` pairs with T in --tail-tokens, and PMmap arms (MMAP). Each tail node leaves two
# parentheses open, closed in the run after (PHandoff h), as are the final PRun and PHavoc.
CUT_LABEL = 10306          # ColA's failz 3 PContra = 10000 + 100 * 3 + pkind PContra (6): the cut leaf of every arm


def parse_tokens(spec):
    toks = [t.strip() for t in (spec or '').split(',') if t.strip()]
    if not toks or 'PMmap' in toks:
        sys.exit('plantail: --tail-tokens takes summary tokens (e.g. XMemset); PMmap arms always belong to the tail')
    return toks


def tail_rx(main, tokens):
    alts = '|'.join(re.escape(node_text(t)) for t in tokens + ['PMmap'])
    return re.compile(r'(?<=\n)((?:%s)*)(\(PRun \[%s\]\n\(PHavoc [^\n]*\n\(PHandoff \d+\s*\))(\)+)' % (alts, re.escape(main)))


def tail_nodes(seg, tokens):
    """the node list of a matched tail run"""
    out, i = [], 0
    texts = [(t, node_text(t)) for t in tokens + ['PMmap']]
    while i < len(seg):
        t, s = next((t, s) for t, s in texts if seg.startswith(s, i))
        out.append(t)
        i += len(s)
    return out


def rewrite_tails(txt, main, tokens, repl, what):
    """apply repl(match, old_nodes) -> replacement text to every arm's tail + final run + hand-off + closing parens;
    returns (new text, [old node list per arm])"""
    rx = tail_rx(main, tokens)
    n_final = len(re.findall(r'\(PRun \[%s\]\n\(PHavoc ' % re.escape(main), txt))
    ms = list(rx.finditer(txt))
    if not ms:
        sys.exit('plantail: no final `(PRun [%s] (PHavoc .. (PHandoff h))` in %s' % (main, what))
    if len(ms) != n_final:
        sys.exit('plantail: %s has %d final `(PRun [%s] (PHavoc `, only %d of them directly followed by (PHandoff h): '
                 'refusing to rewrite a tail whose end is not the hand-off' % (what, n_final, main, len(ms)))
    olds = [tail_nodes(m.group(1), tokens) for m in ms]
    it = iter(olds)
    return rx.sub(lambda m: repl(m, next(it)), txt), olds


def parens(m, n, what):
    if n < 0:
        sys.exit('plantail: %s: the parentheses after `%s` close fewer nodes than the tail opens'
                 % (what, m.group(2).split('\n')[-1]))
    return ')' * n


def cut_text(txt, main, tokens, what):
    """the plan with every arm's tail and hand-off replaced by (PRun [main] (PContra )): the collector's failure leaf of
    the arm is then the un-havocked state at the registration's first stop (or at main)"""
    return rewrite_tails(txt, main, tokens, lambda m, old: '(PRun [%s]\n(PContra  ))' % main
                         + parens(m, len(m.group(3)) - 2 * len(old) - 2, what), what)


def cut_signature(cut):
    """PROBEF_CUT: identifies the plan outside its tails (and main, and the tail definition) that a ProbeF log measured"""
    return int(hashlib.sha256(cut.encode()).hexdigest()[:15], 16)


def spell(nodes):
    """the start-up command's spelling of a node list: XMemset*4,PMmap,XMemset*2"""
    out = []
    for n in nodes:
        if out and out[-1][0] == n:
            out[-1][1] += 1
        else:
            out.append([n, 1])
    return ','.join(n if c == 1 else '%s*%d' % (n, c) for n, c in out)


def cmd_probef(a):
    d = side_names(a)
    tokens = parse_tokens(a.tail_tokens)
    planfile = a.planfile or os.path.join(a.lib, a.dir, a.plan + '.v')
    cut, olds = cut_text(open(planfile).read(), a.main, tokens, planfile)
    d.update(cut=cut_signature(cut))
    out = os.path.join(a.lib, a.out_dir)
    os.makedirs(out, exist_ok=True)
    hdr = ('(* GENERATED by tools/startup/plantail.py probef from %s: every arm\'s tail (%s, PMmap) and hand-off cut to '
           '(PRun [%s] (PContra )); scratch, never committed *)\n' % (os.path.basename(planfile), ','.join(tokens), a.main))
    wrote = [n for n, t in (('PlanF.v', hdr + cut), ('ProbeF.v', PROBEF % d)) if write_if_differs(os.path.join(out, n), t)]
    write_cola(out, a.ns)
    print('plantail: %s/{PlanF,ProbeF,ColA}.v (%s rewritten): %d arms cut, PROBEF_CUT %d; the tails cut: %s'
          % (out, ', '.join(wrote) or 'none', len(olds), d['cut'],
             '; '.join('%d x [%s]' % (c, s) for s, c in collections.Counter(spell(o) for o in olds).items())))


def split_top(s, sep):
    """split s at the separators that are outside (), []"""
    out, depth, cur = [], 0, []
    for ch in s:
        if ch in '([':
            depth += 1
        elif ch in ')]':
            depth -= 1
        if ch == sep and depth == 0:
            out.append(''.join(cur).strip())
            cur = []
        else:
            cur.append(ch)
    if ''.join(cur).strip():
        out.append(''.join(cur).strip())
    return out


def strip_outer(s, o, c):
    s = s.strip()
    if not (s.startswith(o) and s.endswith(c)):
        raise ValueError(s[:80])
    return s[1:-1]


def read_probef(path, tokens):
    """ProbeF's log -> (nodes, PROBEF_CUT, ecall sites); refuses anything but one complete tail shared by every arm"""
    lines = [l for l in open(path).read().split('\n')
             if not re.match(r'^\S+\.vo \(real: ', l) and not l.startswith('Finished transaction')]
    t = '\n'.join(lines)
    mc = re.search(r'^PROBEF_CUT = (\d+)$', t, re.M)
    mp = re.search(r'^PROBEF = 0$', t, re.M)
    if mc is None or mp is None:
        sys.exit('plantail: %s is not a ProbeF log (no PROBEF_CUT / PROBEF markers)' % path)
    if len(re.findall(r'^PROBEF = 0$', t, re.M)) > 1:
        sys.exit('plantail: %s holds several ProbeF outputs (one make run, several targets): cut it per target' % path)
    j = t.find('= [', mp.end())
    if j < 0:
        sys.exit('plantail: %s: no token list after the PROBEF marker (did ProbeF.vo finish?)' % path)
    depth = 0
    for k in range(j + 2, len(t)):
        depth += {'[': 1, ']': -1}.get(t[k], 0)
        if depth == 0:
            break
    else:
        sys.exit('plantail: %s: the token list after the PROBEF marker is cut off' % path)
    leaves = []
    for item in split_top(strip_outer(t[j + 2:k + 1], '[', ']'), ';'):
        lab, lst = split_top(strip_outer(item, '(', ')'), ',')
        leaves.append((int(lab.replace('%nat', '')), [' '.join(x.split()) for x in split_top(strip_outer(lst, '[', ']'), ';')]))
    if not leaves:
        sys.exit('plantail: %s: ProbeF collected no failure leaf (no arm reached the cut)' % path)
    other = collections.Counter((lab, toks[0] if toks else '') for lab, toks in leaves if lab != CUT_LABEL)
    if other:
        sys.exit('plantail: %s: failure leaves BEFORE the tail start (label, first token: count): %s. The plan fails '
                 'before its tail; if the stop is an ecall inside the registration, widen --tail-tokens'
                 % (path, '; '.join('%d, %s: %d' % (l, f, c) for (l, f), c in other.items())))
    lists, sites = collections.Counter(), collections.Counter()
    for lab, toks in leaves:
        if not toks or toks[-1] != 'TMain':
            sys.exit('plantail: %s: a probe list ends in %s, not TMain (TFuel: raise --iters; TStop / TFail*: the tail '
                     'needs a node plantail does not emit)' % (path, toks[-1] if toks else 'nothing'))
        nodes = []
        for tok in toks[:-1]:
            mx, mm = re.match(r'TX (\w+) (\d+)$', tok), re.match(r'TMmap (\d+) (.*)$', tok)
            if mx:
                nodes.append(mx.group(1))
            elif mm:
                nodes.append('PMmap')
                sites[(int(mm.group(1)), mm.group(2))] += 1
            else:
                sys.exit('plantail: %s: unexpected probe token %r' % (path, tok))
        lists[tuple(nodes)] += 1
    if len(lists) != 1:
        sys.exit('plantail: %s: the arms need DIFFERENT tails (%s); one tail text cannot serve them'
                 % (path, '; '.join('%d x [%s]' % (c, spell(n)) for n, c in lists.items())))
    nodes = list(next(iter(lists)))
    bad = sorted(set(nodes) - set(tokens) - {'PMmap'})
    if bad:
        sys.exit('plantail: %s: the tail meets %s, outside --tail-tokens %s: pass them in --tail-tokens (and rerun probef)'
                 % (path, ','.join(bad), ','.join(tokens)))
    return nodes, int(mc.group(1)), len(leaves), sites


def cmd_replace(a):
    tokens = parse_tokens(a.tail_tokens)
    txt = open(a.plan).read()
    if a.count is not None or (a.from_probe is None) == (a.nodes is None):
        sys.exit('plantail: --replace-tail takes exactly one of --nodes / --from-probe, and no --count')
    if a.from_probe:
        nodes, sig, nleaves, sites = read_probef(a.from_probe, tokens)
        mine = cut_signature(cut_text(txt, a.main, tokens, a.plan)[0])
        if sig != mine:
            sys.exit('plantail: %s measured a different plan (PROBEF_CUT %d; %s outside its tails with main %s and '
                     '--tail-tokens %s gives %d): rerun probef on this plan' % (a.from_probe, sig, a.plan, a.main,
                                                                               ','.join(tokens), mine))
        print('plantail: %s: %d arms, one tail [%s]; ecall sites (pc, ra: arms): %s' % (
            a.from_probe, nleaves, spell(nodes),
            '; '.join('%#x, %s: %d' % (p, ra, c) for (p, ra), c in sorted(sites.items())) or 'none'))
    else:
        nodes = parse_nodes(a.nodes)
        bad = sorted(set(nodes) - set(tokens) - {'PMmap'})
        if bad:
            sys.exit('plantail: --nodes %s: %s not in --tail-tokens %s' % (a.nodes, ','.join(bad), ','.join(tokens)))
    ins = ''.join(node_text(x) for x in nodes)
    txt2, olds = rewrite_tails(txt, a.main, tokens, lambda m, old: ins + m.group(2)
                               + parens(m, len(m.group(3)) - 2 * len(old) + 2 * len(nodes), a.plan), a.plan)
    was = '; '.join('%d x [%s]' % (c, s) for s, c in collections.Counter(spell(o) for o in olds).items())
    if txt2 == txt:
        print('plantail: %d tails of %s already [%s]: unchanged' % (len(olds), a.plan, spell(nodes)))
        return
    open(a.plan, 'w').write(txt2)
    print('plantail: %d tails of %s replaced: was %s; now [%s]' % (len(olds), a.plan, was, spell(nodes)))


def cmd_insert(a):
    if a.replace_tail:
        return cmd_replace(a)
    if a.from_probe:
        sys.exit('plantail: --from-probe reads ProbeF\'s WHOLE tail: use it with --replace-tail')
    txt = open(a.plan).read()
    nodes = parse_nodes(a.nodes if a.nodes is not None else 'XMemset')
    if a.count is not None:
        base = nodes or ['XMemset']
        nodes = base * a.count if len(base) == 1 else base[:a.count]
    pat = re.compile(r'\(PRun \[%s\]\n\(PHavoc ' % re.escape(a.main))
    n = len(pat.findall(txt))
    if n == 0:
        sys.exit('plantail: no final `PRun [%s]` before a PHavoc in %s' % (a.main, a.plan))
    if not nodes:
        print('plantail: nothing to insert (%d tails, %s unchanged)' % (n, a.plan))
        return
    ins = ''.join(node_text(x) for x in nodes)
    txt2 = pat.sub(lambda m: ins + m.group(0), txt)
    extra = ')' * (2 * len(nodes))
    txt2 = re.sub(r'(\(PHandoff \d+\s*\))(\)+)', lambda m: m.group(1) + m.group(2) + extra, txt2)
    open(a.plan, 'w').write(txt2)
    print('plantail: %d tails of %s got %d nodes (%s)' % (
        n, a.plan, len(nodes), ', '.join('%s x%d' % (k, v) for k, v in collections.Counter(nodes).items())))


def cmd_drop_registration(a):
    """0 asan_globals descriptors: remove the registration arm (the knock port's armcut.py, adopted and generalised).
    The image's __asan_register_elf_globals returns early, so every node the donor's plan spends inside the registration
    has no counterpart. In each arm the span from the CUT START up to, NOT including, the arm's final `PRun [main]` is
    removed with its unclosed parentheses.
    CUT START: by default the registration loop head - the `PRun [HEAD]` whose next node is `PForget []` (cgif 0x3e574 =
    __asan_register_globals + 0x130). `--cut-from REGEX` moves it earlier, for an image whose registration-only prefix is
    longer (knock's extended cut: the two `PX XIMemset` pairs, the `PRun [0x71928]`, the `PBump 500` and the `PCase2`
    split that only exists to separate the registration's two outcomes). The regex is matched INSIDE each arm, between
    the arm's start and its final `PRun [main]`; the EARLIEST match wins.
    A cut that swallows a `PCase2` removes one of its two PHandoff leaves, so the plan's SHAPE changes (cgif's
    startup_shape pairs holes as SAlt2); the tool lists the lost holes and REFUSES unless --allow-shape-change is given,
    because the shape is what A/AB1n.v's consumer quantifies over."""
    txt = open(a.plan).read()
    MAIN = 'PRun [%s]' % a.main
    if a.cut_from:
        pat = re.compile(a.cut_from)
    else:
        heads = sorted(set(re.findall(r'PRun \[(0x[0-9a-f]+)\]\n\(PForget \[\]', txt)))
        if a.head:
            heads = [a.head]
        if len(heads) != 1:
            sys.exit('plantail: drop-registration: the loop head is not unique (%s); give --head or --cut-from' % heads)
        pat = re.compile(r'PRun \[%s\]' % re.escape(heads[0]))
        print('plantail: cut start = the registration loop head %s' % heads[0])
    n_arms = txt.count(MAIN)
    if n_arms == 0:
        sys.exit('plantail: no `%s` in %s' % (MAIN, a.plan))
    cut, lost = 0, []
    pos = 0
    while True:
        k = txt.find(MAIN, pos)
        if k < 0:
            break
        m = None
        for mm in pat.finditer(txt, pos, k):
            m = mm; break
        if m is None:
            pos = k + 1
            continue
        i = m.start()
        j = k - 1
        while txt[j] in ' \n':
            j -= 1
        if txt[j] != '(':
            sys.exit('plantail: %s at %d is not opened by "(" (found %r)' % (MAIN, k, txt[j]))
        dead = txt[i:j + 1]
        lost += re.findall(r'PHandoff (\d+)', dead)
        net = dead.count('(') - dead.count(')')
        if net < 1:
            sys.exit('plantail: the span at %d opens %d parentheses' % (i, net))
        mc = re.compile(r'\(PHandoff \d+\s*(\)+)').search(txt, k)
        if not mc or len(mc.group(1)) <= net:
            sys.exit('plantail: no closing run of more than %d ")" after the PHandoff at %d' % (net, k))
        txt = txt[:mc.start(1)] + mc.group(1)[net:] + txt[mc.end(1):]
        txt = txt[:i] + txt[j + 1:]
        cut += 1
        pos = i
    if lost and not a.allow_shape_change:
        sys.exit('plantail: REFUSED: the cut removes %d PHandoff leaves (holes %s): the plan\'s SHAPE changes, and '
                 'A/AB1n.v quantifies over it. Re-run with --allow-shape-change once the unit has decided what its shape '
                 'becomes.' % (len(lost), sorted(set(int(x) for x in lost))))
    if txt.count('(') != txt.count(')'):
        sys.exit('plantail: unbalanced result: %d "(" vs %d ")"' % (txt.count('('), txt.count(')')))
    open(a.out or a.plan, 'w').write(txt)
    print('plantail: drop-registration: %d of %d arms cut (main %s)%s; wrote %s'
          % (cut, n_arms, a.main, '' if not lost else '; holes removed: %s' % sorted(set(int(x) for x in lost)), a.out or a.plan))


def split_children(txt, i):
    """txt[i] opens a node; return the spans of its parenthesised children at depth 1"""
    depth, k, kids = 0, i, []
    while k < len(txt):
        c = txt[k]
        if c == '(':
            depth += 1
            if depth == 2:
                start = k
        elif c == ')':
            depth -= 1
            if depth == 1:
                kids.append((start, k + 1))
            if depth == 0:
                return kids, k + 1
        k += 1
    raise ValueError('unbalanced from %d' % i)


def cmd_collapse_case(a):
    """0-descriptor images: a PCase2 that only separates the REGISTRATION's two outcomes has no counterpart when the
    image registers nothing, so the node is replaced by ONE of its arms. This DELETES the other arm's PHandoff, i.e. the
    plan's shape loses a hole per node - legitimate exactly when the unit lacks a node kind the donor has (the start-up
    tools' ruling, 2026-10-29), never to make a failing run pass. --match selects the nodes (default: every PCase2 whose node
    text contains --marker, e.g. PBump 500 just above it); --keep 1|2 picks the arm."""
    txt = open(a.plan).read()
    out, pos, n, lost = [], 0, 0, []
    while True:
        i = txt.find('(PCase2', pos)
        if i < 0:
            out.append(txt[pos:]); break
        kids, end = split_children(txt, i)
        if len(kids) < 2:
            out.append(txt[pos:i + 7]); pos = i + 7; continue
        kids = kids[-2:]        # a PCase2's parenthesised children are (expr) arm1 arm2: the arms are the last two
        node = txt[i:end]
        if a.match and not re.search(a.match, node):
            out.append(txt[pos:i + 7]); pos = i + 7; continue
        if a.keep == 0:          # auto: keep the arm that does NOT contain --match (the registration marker)
            has0 = bool(re.search(a.match, txt[kids[0][0]:kids[0][1]]))
            has1 = bool(re.search(a.match, txt[kids[1][0]:kids[1][1]]))
            if has0 == has1:
                out.append(txt[pos:i + 7]); pos = i + 7; continue
            keep, drop = (kids[1], kids[0]) if has0 else (kids[0], kids[1])
        else:
            keep = kids[0] if a.keep == 1 else kids[1]
            drop = kids[1] if a.keep == 1 else kids[0]
        lost += re.findall(r'PHandoff (\d+)', txt[drop[0]:drop[1]])
        out.append(txt[pos:i]); out.append(txt[keep[0]:keep[1]])
        pos = end; n += 1
    txt2 = ''.join(out)
    if txt2.count('(') != txt2.count(')'):
        sys.exit('plantail: unbalanced result: %d "(" vs %d ")"' % (txt2.count('('), txt2.count(')')))
    if lost and not a.allow_shape_change:
        sys.exit('plantail: REFUSED: collapsing %d PCase2 nodes removes holes %s; the plan\'s SHAPE changes. Re-run with '
                 '--allow-shape-change (legitimate only when the unit lacks a node kind the donor has).'
                 % (n, sorted(set(int(x) for x in lost))))
    open(a.out or a.plan, 'w').write(txt2)
    print('plantail: collapse-case: %d PCase2 nodes replaced by arm %d; holes removed: %s; wrote %s'
          % (n, a.keep, sorted(set(int(x) for x in lost)), a.out or a.plan))


def cmd_drop_nodes(a):
    """remove single-child plan nodes from every arm, with their matching parenthesis: knock's EXTENDED 0-descriptor cut
    is exactly this on top of drop-registration - `PRun [0x71928]` and `PBump 500` have no counterpart on an image that
    registers nothing (the knock port's ab05-arm-removed-ext.diff: 9 hunks, those two openers and two closers per arm, the PCase2
    KEPT). --match is a regex for the node head right after '('; each match's opener line and its matching ')' go."""
    txt = open(a.plan).read()
    pat = re.compile(r'\((%s)' % a.match)
    n = 0
    while True:
        m = pat.search(txt)
        if not m:
            break
        i = m.start()
        depth, k = 0, i
        while k < len(txt):
            if txt[k] == '(':
                depth += 1
            elif txt[k] == ')':
                depth -= 1
                if depth == 0:
                    break
            k += 1
        else:
            sys.exit('plantail: unbalanced from %d' % i)
        nl = txt.index('\n', i) + 1
        txt = txt[:k] + txt[k + 1:]
        txt = txt[:i] + txt[nl:]
        n += 1
    if n == 0:
        # a mistyped regex used to be a silent no-op (`0 nodes removed`, the plan written unchanged): nothing was cut
        sys.exit('plantail: REFUSED: drop-nodes: --match %r matches no node of %s - nothing would be removed' % (a.match, a.plan))
    if a.expect is not None and n != a.expect:
        sys.exit('plantail: REFUSED: drop-nodes: --match %r matched %d nodes, --expect %d' % (a.match, n, a.expect))
    if txt.count('(') != txt.count(')'):
        sys.exit('plantail: unbalanced result')
    open(a.out or a.plan, 'w').write(txt)
    print('plantail: drop-nodes: %d nodes matching %r removed with their parentheses%s; wrote %s'
          % (n, a.match, '' if a.expect is None else ' (= --expect)', a.out or a.plan))


def cmd_pin_cells(a):
    """WITNESS cells as literal KWords in every hand-off state (the knock port): before each `PHandoff h` put
    `PJoin (ELit 0) ADDR W`, the checker's own node (donor YA0c.v:210 -> node_join, YK09.v:1002; the collector mirrors it,
    coq/ColA.v:96). node_join reads the W bytes at ADDR with know_lookup - a written KWord byte or a KImg byte, which reads
    the IMAGE - and ADDS `KWord (SA (ELit 0) ADDR) W (ELit v)`; it refuses (the run fails) unless every byte is known as a
    literal. So a cell the run never writes (knock's ___asan_globals_registered, decided before only by the .bss zero
    under a KImg range) and the high bytes of an 8-byte cell whose low bytes start-up wrote become ONE witnessed literal
    at main, with the value kn_read already gave: no emitted table value changes. --cell ADDR/W, W in 1..8, repeatable."""
    txt = open(a.plan).read()
    cells = []
    for c in a.cell:
        ad, w = c.split('/')
        ad, w = int(ad, 0), int(w)
        if not 1 <= w <= 8:
            sys.exit('plantail: pin-cells: %s: node_join takes 1..8 bytes' % c)
        cells.append((ad, w))
    if len(set(cells)) != len(cells):
        sys.exit('plantail: pin-cells: a cell is given twice: %s' % a.cell)
    have = [c for c in cells if re.search(r'PJoin \(ELit 0\) (%#x|%d) %d ' % (c[0], c[0], c[1]), txt)]
    if have:
        sys.exit('plantail: pin-cells: the plan already joins %s' % ['%#x/%d' % c for c in have])

    def wrap(m):
        s = m.group(0)
        for ad, w in reversed(cells):
            s = 'PJoin (ELit 0) %#x %d (%s)' % (ad, w, s)
        return s
    new, n = re.subn(r'PHandoff \d+', wrap, txt)
    if a.holes is not None and n != a.holes:
        sys.exit('plantail: pin-cells: %d PHandoff nodes, expected %d' % (n, a.holes))
    if new.count('(') != new.count(')'):
        sys.exit('plantail: pin-cells: unbalanced result')
    open(a.out or a.plan, 'w').write(new)
    print('plantail: pin-cells: %d PHandoff nodes each preceded by %d PJoin (%s); wrote %s'
          % (n, len(cells), ', '.join('%#x/%d' % c for c in cells), a.out or a.plan))



def cmd_globals(a):
    from elftools.elf.elffile import ELFFile
    e = ELFFile(open(a.image, 'rb'))
    s = e.get_section_by_name('asan_globals')
    if s is None:
        print('%s: no asan_globals section (0 descriptors)' % a.image)
        return
    print('%s: asan_globals %#x bytes, %d descriptors (64 bytes each)' % (a.image, s['sh_size'], s['sh_size'] // 64))


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest='cmd', required=True)
    def common(p):
        p.add_argument('--lib', required=True); p.add_argument('--ns', default='OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib')
        p.add_argument('--img', required=True)
        p.add_argument('--side', default='A', choices=['A', 'B'], help='the donor file names: A = AB12/AB1h/AB1l/AB05/AB01 '
                       'in ZReplyA, B = YB12/YB1h/YB1l/YB05/YB01 in ZReplyB (each overridable below)')
        p.add_argument('--dir', default=None)
        p.add_argument('--tab', default=None); p.add_argument('--segs', default=None); p.add_argument('--xn', default=None)
        p.add_argument('--plan', default=None); p.add_argument('--planname', default='startup_plan_tfib')
        p.add_argument('--main', required=True)
        p.add_argument('--ns-core', default=None, help='namespace of the core files (YK*, YA*); a SPLIT library passes its '
                       'Reusable namespace here')
        p.add_argument('--ns-dir', default=None, help='namespace of --dir (default <ns>.<dir>)')
        p.add_argument('--ns-out', default=None, help='namespace of --out-dir (default <ns>.<out-dir>)')
    p = sub.add_parser('probe')
    common(p)
    p.add_argument('--out-dir', default='ZStartColR'); p.add_argument('--hs', default=None)
    p.add_argument('--hsname', default='HS_tfib')
    p.add_argument('--iters', type=int, default=40); p.add_argument('--nholes', type=int, default=50)
    p = sub.add_parser('probef', help='the whole tail from the collector\'s failure leaves of the tail-cut plan')
    common(p)
    p.add_argument('--out-dir', default='ZStartColF', help='driver directory under LIB (give the probe its own: a '
                   'rewritten ColA.v there rebuilds every Pass*.vo beside it)')
    p.add_argument('--planfile', default=None, help='the plan to cut (default LIB/<dir>/<plan>.v)')
    p.add_argument('--iters', type=int, default=400, help='bound on the probe\'s steps per arm (each tail node is one)')
    p.add_argument('--tail-tokens', default='XMemset', help='summary tokens whose pairs form the tail with PMmap arms')
    p = sub.add_parser('insert')
    p.add_argument('--plan', required=True); p.add_argument('--main', required=True)
    p.add_argument('--nodes', default=None, help='default XMemset (front insertion); with --replace-tail the whole tail, '
                   '"" for none')
    p.add_argument('--count', type=int, default=None)
    p.add_argument('--replace-tail', action='store_true', help='strip every arm\'s tail (--tail-tokens pairs and PMmap '
                   'arms before the final PRun [main]) and write --nodes / --from-probe in its place')
    p.add_argument('--from-probe', default=None, help='ProbeF log: its tail (with --replace-tail)')
    p.add_argument('--tail-tokens', default='XMemset')
    p = sub.add_parser('globals'); p.add_argument('image')
    p = sub.add_parser('drop-nodes', help='remove single-child nodes (and their parentheses) from every arm')
    p.add_argument('--plan', required=True); p.add_argument('--match', required=True); p.add_argument('--out', default=None)
    p.add_argument('--expect', type=int, default=None, help='the node count the cut must remove (knock: 60); another count refuses')
    p = sub.add_parser('pin-cells', help='witness cells as literal KWords at every hand-off (a PJoin before each PHandoff)')
    p.add_argument('--plan', required=True); p.add_argument('--cell', action='append', required=True, metavar='ADDR/W')
    p.add_argument('--holes', type=int, default=None, help='the PHandoff count the plan must have (knock: 50)')
    p.add_argument('--out', default=None)
    p = sub.add_parser('collapse-case', help='0 descriptors: replace a registration-only PCase2 by one of its arms')
    p.add_argument('--plan', required=True); p.add_argument('--keep', type=int, default=0, choices=[0, 1, 2],
                   help='0 = keep the arm that does NOT contain --match (the registration marker); 1 or 2 = that arm')
    p.add_argument('--match', default=None, help='regex the PCase2 node must contain')
    p.add_argument('--allow-shape-change', action='store_true'); p.add_argument('--out', default=None)
    p = sub.add_parser('drop-registration', help='0 descriptors: remove the registration arm from every arm of the plan')
    p.add_argument('--plan', required=True); p.add_argument('--main', required=True)
    p.add_argument('--head', default=None, help='the loop head pc (default: the PRun whose next node is PForget [])')
    p.add_argument('--cut-from', default=None, help='regex for the cut start inside each arm (earliest match wins)')
    p.add_argument('--allow-shape-change', action='store_true', help='permit a cut that removes PHandoff leaves')
    p.add_argument('--out', default=None)
    a = ap.parse_args()
    {'probe': cmd_probe, 'probef': cmd_probef, 'insert': cmd_insert, 'globals': cmd_globals,
     'drop-registration': cmd_drop_registration, 'collapse-case': cmd_collapse_case, 'drop-nodes': cmd_drop_nodes,
     'pin-cells': cmd_pin_cells}[a.cmd](a)


if __name__ == '__main__':
    main()
