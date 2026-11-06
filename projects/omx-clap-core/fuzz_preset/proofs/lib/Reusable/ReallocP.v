(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_rgb_fuzzer/lib/ReallocP.v at 82e315ce20c (cold/c-asan-realloc-primary; no cgif_file_fuzzer copy there; the C5 trace premise), with its module paths changed by its own module map (YN05 -> YM05, YG0h -> YG0f, YA0l -> YA0n). *)
(* The realloc statements over section variables, for any harness whose model is the YG00 form.

   [arealloc_realizes_allP] is the realloc contract for 1 <= n < nmax and a live old block;
   [arealloc_null_realizesP] is realloc(NULL, n).  The malloc tree [mt], the free tree [ft], the call
   precondition [cpre], the regime premise [rpre], the size bound [nmax], the live-bytes bound [lmax], the
   realization relation [areal], the leaves [rleaf] / [mleaf] and the trace universe [U] are section variables,
   so that a harness instantiates them with its own predicates.  ReallocAll.v instantiates them at cgif_rgb's
   (mt = malloc, ft = free, nmax = MALLOC_MAX, lmax = LIVE_MAX).

   When the call returns NULL, the post also gives [mt_refused]: granted traces (gflag = true, the form
   amreal_SRr04 exports) along which the entry step [ft PNull] returns in S1 and the inner [mt n] returns PNull
   from S1.  A caller that has room refutes that arm with its malloc model's success lemma.

   This file imports only the model (YG00, YG01), the call layer (YG0d), the layout and world modules, YK11 and
   the RunCeil module.  The same text compiles in a cgif_file_fuzzer core with this module map:
   YN05 -> YM05, YG0h -> YG0f, YA0l -> YA0n, namespace cgif_rgb_fuzzer -> cgif_file_fuzzer. *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0n YG00 YG01 YG0f YG0d.
Import ListNotations.
Open Scope Z_scope.

(* The realloc tree over a malloc tree [mt] and a free tree [ft]: the entry's [ft PNull], [mt n], and on success
   [ft] of the old block.  At [mt = YG00.malloc], [ft = YG00.free] it is cgif_rgb's YG0f.realloc_tree. *)
Definition realloc_tree_with (mt : Z -> list Z -> M sptr) (ft : sptr -> list Z -> M unit)
(p : sptr) (n : Z) (tr : list Z) : M sptr :=
YG00.bind (ft PNull tr) (fun _ =>
YG00.bind (mt n tr) (fun q =>
match q with
| PNull => YG00.ret PNull
| _ => YG00.bind (ft p tr) (fun _ => YG00.ret q)
end)).

(* realloc(NULL, n): the entry step, then the malloc tree. *)
Definition realloc_null_tree_with (mt : Z -> list Z -> M sptr) (ft : sptr -> list Z -> M unit)
(n : Z) (tr : list Z) : M sptr :=
YG00.bind (ft PNull tr) (fun _ => mt n tr).

(* Every kernel answer in the trace was granted (cgif_file's YG0d.gflag; cgif_rgb's YG0d has none). *)
Fixpoint gflag (trc : list (kreq * Z)) : bool :=
match trc with [] => true | (q, z) :: trc' => (progz q z && gflag trc')%bool end.

(* The refusal witness: along granted traces, the entry step [ft PNull] returns in S1 from S, and [mt n] returns
   PNull in S' from S1. *)
Definition mt_refused (mt : Z -> list Z -> M sptr) (ft : sptr -> list Z -> M unit)
(n : Z) (tr : list Z) (S S' : astate) : Prop :=
exists S1 trc1 trc2, apath (ft PNull tr S) trc1 (tt, S1) /\ gflag trc1 = true /\
apath (mt n tr S1) trc2 (PNull, S') /\ gflag trc2 = true.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section p.
Variable segs : list Segment.
Variable B : asyms.
(* The trace premise on the stack trace and the state (cgif: in the universe; fuzz_state: C5 with a margin for
   realloc's three ticks). *)
Variable U : list Z -> astate -> Prop.
Variable mt : Z -> list Z -> M sptr.
Variable ft : sptr -> list Z -> M unit.
Variable cpre : alayout -> astate -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> list (Z * Z * Z) -> Prop.
Variable rpre : astate -> Z -> Prop.
(* The size bound and the live-bytes bound (cgif: MALLOC_MAX, LIVE_MAX). *)
Variable nmax : Z.
Variable lmax : Z.
Variable areal : forall R : Type, itree astate R -> world segs -> config -> (R -> world segs -> config -> Prop) -> Prop.
Variable rleaf : alayout -> astate -> world segs -> bvmap 5 word -> (word -> option byte) -> Model ->
sptr -> Z -> Z -> sptr * astate -> world segs -> config -> Prop.
Variable mleaf : alayout -> astate -> world segs -> bvmap 5 word -> (word -> option byte) -> Model ->
Z -> sptr * astate -> world segs -> config -> Prop.

Definition arealloc_realizes_allP (pc pc0 : Z) : Prop :=
forall ly S W regs mem md p n_old n ch,
cpre ly S W regs mem md ch -> rpre S n ->
In (p, n_old) (blocks S) -> getr regs 10 = w64 (sptr_addr B ly p) -> getr regs 11 = w64 n ->
1 <= n < nmax -> blocks_bytes S + n <= lmax ->
U (call_trace ly pc0 regs ch) S ->
areal _ (realloc_tree_with mt ft p n (call_trace ly pc0 regs ch) S) W
(cfg_at segs pc regs mem md)
(fun r W' c' => rleaf ly S W regs mem md p n_old n r W' c' /\
(fst r = PNull -> mt_refused mt ft n (call_trace ly pc0 regs ch) S (snd r))).

Definition arealloc_null_realizesP (pc pc0 : Z) : Prop :=
forall ly S W regs mem md n ch,
cpre ly S W regs mem md ch -> rpre S n ->
getr regs 10 = w64 0 -> getr regs 11 = w64 n ->
1 <= n < nmax -> blocks_bytes S + n <= lmax ->
U (call_trace ly pc0 regs ch) S ->
areal _ (realloc_null_tree_with mt ft n (call_trace ly pc0 regs ch) S) W
(cfg_at segs pc regs mem md)
(fun r W' c' => mleaf ly S W regs mem md n r W' c' /\
(fst r = PNull -> mt_refused mt ft n (call_trace ly pc0 regs ch) S (snd r))).
End p.
End d.
