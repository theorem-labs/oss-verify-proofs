(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: made for LPS 727298f3 from the start-up constants of B/ne.v, B/nf.v and B/Start3.v: the start-up states that B/n0.v records, computed in the build per CONFIG_RSEQ, each run's leaf from the computed start state and each recorded cut and exit state by Lib/Relaunch.v's rule, the exit and hand-off states keyed on the leaves of the source that reaches them. *)
(* The start-up chain of B/ne.v (Start1), B/nf.v (Start2) and B/Start3.v, made per CONFIG_RSEQ.
   At LPS 727298f3 the start state depends on the flag ([StartStates.S_ctor r]: the auxv is
   [auxv_size r] bytes), so the states B/n0.v records for the old start state are made again in
   the build, for [r = false] ([X_0]) and [r = true] ([X_1]), [X r] selecting between them:
   - a state a run reaches and its consumer compares by equality is the run's own leaf from the
     computed start state (the run of the recorded check, from the state before it);
   - a restated state is its rule applied to the computed state (reg 10 := 2^47 - 1, and for
     [S_hm] reg 15 := the next fresh variable, as [state_diff] showed for the recorded pair);
   - a cut or exit state of a recorded CFG check ([Z1], [Z2], [E_s2], [T_hm2], [E_s3], [E_k7])
     is the recorded state relaunched over the computed start state (Lib/Relaunch.v).
   B/n0.v's recorded states are read here only as the relaunch rule's input and as the
   fallback a failed run returns (the check lemmas of B/StartRegen.v then fail). *)
From Stdlib Require Import ZArith NArith List Bool PArith.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymCFG SymHeap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA CFGA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform Relaunch.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require StartStates n0 n1.
(* LPS 727298f3: the branch conditions and ALU operations of the facts below (BC_EQ, ALU_AND, ..). *)
From LinuxProcessSemantics.Riscv Require Import Instr.
Import ListNotations.
Open Scope Z_scope.

Definition leaf1 (o : option (list leaf)) (d : sstate) : sstate :=
  match o with Some [l] => lf_state l | _ => d end.
Definition leafA1 (o : option (list leafA)) (d : axst) : axst :=
  match o with Some [l] => la_state l | _ => d end.
Definition opt_ss (o : option sstate) (d : sstate) : sstate :=
  match o with Some s => s | None => d end.
Definition set_sv (l : list sv) (i : nat) (v : sv) : list sv := firstn i l ++ v :: skipn (S i) l.
Definition with_regs (S : sstate) (regs : list sv) (nxt : positive) : sstate :=
  mkSS (ss_pc S) regs (ss_fregs S) (ss_fcsr S) (ss_resv S) (ss_objs S) (ss_facts S) nxt (ss_lenient S).

Definition SHB : Z := 0x7fff8000.
Definition axS (S : sstate) : axst := mkAX S [] (SLit SHB).

(* The recorded start state the old run began from (the relaunch rule's [R]). *)
Definition S_ctor_x_rec : sstate := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n0.Start1States.S_ctor_x.

Module Start1R.

Definition ECALL_MMAP : Z := 0x706a0.
Definition ZHEAD : Z := 0x7030c.
Definition HMCUT : Z := 0x71554.
Definition xf1 : list xform :=
  [XSplit 6%nat (SLit 1563520); XSplit 7%nat (SLit 1567616); XSplit 8%nat (SLit 1571712)].
Definition F1x : list sprop := [SPUle (SVar 1%positive) (SVar 4%positive); SPUle (SVar 1%positive) (SVar 6%positive)].

Definition S_ctor_x_0 : sstate := Eval vm_compute in
  opt_ss (apply_xforms (add_facts F1x (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.StartStates.S_ctor false)) xf1) S_ctor_x_rec.
Definition S_ctor_x_1 : sstate := Eval vm_compute in
  opt_ss (apply_xforms (add_facts F1x (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.StartStates.S_ctor true)) xf1) S_ctor_x_rec.
Definition S_ctor_x (r : bool) : sstate := if r then S_ctor_x_1 else S_ctor_x_0.

Definition L_hm_0 : sstate := Eval vm_compute in
  leaf1 (sym_run segsA 4000%nat [HMCUT] S_ctor_x_0 true) OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n0.Start1States.L_hm.
Definition L_hm_1 : sstate := Eval vm_compute in
  leaf1 (sym_run segsA 4000%nat [HMCUT] S_ctor_x_1 true) OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n0.Start1States.L_hm.
Definition L_hm (r : bool) : sstate := if r then L_hm_1 else L_hm_0.

(* [S_hm] is [L_hm] restated: reg 10 := 2^47 - 1 and reg 15 := the next fresh variable. *)
Definition restate_hm (L : sstate) : sstate :=
  with_regs L (set_sv (set_sv (ss_regs L) 10 (SLit (2 ^ 47 - 1))) 15 (SVar (ss_next L))) (Pos.succ (ss_next L)).
Definition S_hm_0 : sstate := Eval vm_compute in restate_hm L_hm_0.
Definition S_hm_1 : sstate := Eval vm_compute in restate_hm L_hm_1.
Definition S_hm (r : bool) : sstate := if r then S_hm_1 else S_hm_0.

Definition E_b2_S_0 : sstate := Eval vm_compute in
  leaf1 (sym_run segsA 4000%nat [ECALL_MMAP] S_hm_0 true) OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n0.Start1States.E_b2_S.
Definition E_b2_S_1 : sstate := Eval vm_compute in
  leaf1 (sym_run segsA 4000%nat [ECALL_MMAP] S_hm_1 true) OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n0.Start1States.E_b2_S.
Definition E_b2_S (r : bool) : sstate := if r then E_b2_S_1 else E_b2_S_0.
Definition E_b2 (r : bool) : axst := axS (E_b2_S r).
Definition S_b2ok (r : bool) : axst := axS (S_ret_lit (E_b2_S r) 2147446784).
Definition S_b2fail (r : bool) : axst := axS (S_ret_lit (E_b2_S r) enomem_ret).

Definition SPINb2_0 : axst := Eval vm_compute in
  leafA1 (sym_runA segsA 400%nat [418892] (S_b2fail false) true) OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n0.Start1States.SPINb2.
Definition SPINb2_1 : axst := Eval vm_compute in
  leafA1 (sym_runA segsA 400%nat [418892] (S_b2fail true) true) OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n0.Start1States.SPINb2.
Definition SPINb2 (r : bool) : axst := if r then SPINb2_1 else SPINb2_0.
Definition SPINb2_S (r : bool) : sstate := ax_S (SPINb2 r).

Definition E_b3_0 : axst := Eval vm_compute in
  leafA1 (sym_runA segsA 3000%nat [ECALL_MMAP] (S_b2ok false) true) OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n0.Start1States.E_b3.
Definition E_b3_1 : axst := Eval vm_compute in
  leafA1 (sym_runA segsA 3000%nat [ECALL_MMAP] (S_b2ok true) true) OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n0.Start1States.E_b3.
Definition E_b3 (r : bool) : axst := if r then E_b3_1 else E_b3_0.
Definition E_b3_S (r : bool) : sstate := ax_S (E_b3 r).
Definition S_b3ok (r : bool) : axst := axS (S_ret_lit (E_b3_S r) 2415882240).
Definition S_b3fail (r : bool) : axst := axS (S_ret_lit (E_b3_S r) enomem_ret).

Definition SPINb3_0 : axst := Eval vm_compute in
  leafA1 (sym_runA segsA 400%nat [418912] (S_b3fail false) true) OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n0.Start1States.SPINb3.
Definition SPINb3_1 : axst := Eval vm_compute in
  leafA1 (sym_runA segsA 400%nat [418912] (S_b3fail true) true) OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n0.Start1States.SPINb3.
Definition SPINb3 (r : bool) : axst := if r then SPINb3_1 else SPINb3_0.
Definition SPINb3_S (r : bool) : sstate := ax_S (SPINb3 r).

Definition E_b4_0 : axst := Eval vm_compute in
  leafA1 (sym_runA segsA 3000%nat [ECALL_MMAP] (S_b3ok false) true) OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n0.Start1States.E_b4.
Definition E_b4_1 : axst := Eval vm_compute in
  leafA1 (sym_runA segsA 3000%nat [ECALL_MMAP] (S_b3ok true) true) OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n0.Start1States.E_b4.
Definition E_b4 (r : bool) : axst := if r then E_b4_1 else E_b4_0.
Definition E_b4_S (r : bool) : sstate := ax_S (E_b4 r).
Definition S_b4ok (r : bool) : axst := axS (S_ret_lit (E_b4_S r) 2201439137792).
Definition S_b4fail (r : bool) : axst := axS (S_ret_lit (E_b4_S r) enomem_ret).

Definition SPINb4_0 : axst := Eval vm_compute in
  leafA1 (sym_runA segsA 400%nat [418932] (S_b4fail false) true) OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n0.Start1States.SPINb4.
Definition SPINb4_1 : axst := Eval vm_compute in
  leafA1 (sym_runA segsA 400%nat [418932] (S_b4fail true) true) OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n0.Start1States.SPINb4.
Definition SPINb4 (r : bool) : axst := if r then SPINb4_1 else SPINb4_0.
Definition SPINb4_S (r : bool) : sstate := ax_S (SPINb4 r).

(* The cut states of the loops at [ZHEAD]: relaunched from the start pair. *)
Definition Z1_0 : axst := Eval vm_compute in
  relaunchA S_ctor_x_rec S_ctor_x_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n0.Start1States.Z1.
Definition Z1_1 : axst := Eval vm_compute in
  relaunchA S_ctor_x_rec S_ctor_x_1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n0.Start1States.Z1.
Definition Z1 (r : bool) : axst := if r then Z1_1 else Z1_0.
Definition Z1_S (r : bool) : sstate := ax_S (Z1 r).
Definition Z2_0 : axst := Eval vm_compute in
  relaunchA S_ctor_x_rec S_ctor_x_0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n0.Start1States.Z2.
Definition Z2_1 : axst := Eval vm_compute in
  relaunchA S_ctor_x_rec S_ctor_x_1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n0.Start1States.Z2.
Definition Z2 (r : bool) : axst := if r then Z2_1 else Z2_0.
Definition Z2_S (r : bool) : sstate := ax_S (Z2 r).
(* The exit state of check1, and below each later hand-off state: remade by the same rule keyed on
   the leaves of the recorded source that reaches it and of its computed counterpart
   ([Lib/Relaunch.v]'s [relaunch_src]; the run moves start words through memory and registers). *)
Definition G1 : positive := 26%positive.
Definition FUEL1 : nat := (12 * 1000)%nat.
Definition cutpcs1 : list Z := [ZHEAD; ECALL_MMAP].
Definition S_b4ok_rec : axst := axS (S_ret_lit (ax_S OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n0.Start1States.E_b4) 2201439137792).
Definition srcs1_rec : list axst :=
  [S_b4ok_rec; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n0.Start1States.Z1; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n0.Start1States.Z2].
Definition srcs1 (r : bool) : list axst := [S_b4ok r; Z1 r; Z2 r].
Definition E_s2_0 : axst := Eval vm_compute in
  relaunch_src segsA FUEL1 cutpcs1 G1 srcs1_rec (srcs1 false) OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n0.Start1States.E_s2.
Definition E_s2_1 : axst := Eval vm_compute in
  relaunch_src segsA FUEL1 cutpcs1 G1 srcs1_rec (srcs1 true) OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n0.Start1States.E_s2.
Definition E_s2 (r : bool) : axst := if r then E_s2_1 else E_s2_0.
Definition E_s2_S (r : bool) : sstate := ax_S (E_s2 r).

Definition cuts1 (r : bool) : list axst := [S_b4ok r; Z1 r; Z2 r].
Definition exits1 (r : bool) : list axst := [E_s2 r].

End Start1R.

Module Start2R.
Import Start1R.

Definition SPIN_MMAPORDIE : Z := 0x6bf18.
Definition FUEL2 : nat := (70 * 1000)%nat.
Definition G2 : positive := 28%positive.
Definition MF2 : sprop :=
  SPNot (SPBranch BC_EQ (SAlu ALU_AND (SAlu ALU_OR (SLit 288) (SAlu ALU_ADD (SVar 1%positive) (SLit (-584)))) (SLit 15)) (SLit 0)).

Definition S_s2x (r : bool) : axst :=
  ax_add_facts [MF2] (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.StartNodes.eager_ok (E_s2 r) 65536 28%positive).
Definition S_s2x_S (r : bool) : sstate := ax_S (S_s2x r).
Definition S_s2fail (r : bool) : axst := axS (S_ret_lit (ax_S (E_s2 r)) enomem_ret).

Definition SPIN5_0 : axst := Eval vm_compute in
  leafA1 (sym_runA segsA 400%nat [SPIN_MMAPORDIE] (S_s2fail false) true) OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n0.Start2States.SPIN5.
Definition SPIN5_1 : axst := Eval vm_compute in
  leafA1 (sym_runA segsA 400%nat [SPIN_MMAPORDIE] (S_s2fail true) true) OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n0.Start2States.SPIN5.
Definition SPIN5 (r : bool) : axst := if r then SPIN5_1 else SPIN5_0.
Definition SPIN5_S (r : bool) : sstate := ax_S (SPIN5 r).

Definition S_s2x_rec : axst :=
  ax_add_facts [MF2] (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.StartNodes.eager_ok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n0.Start1States.E_s2 65536 28%positive).
Definition T_hm2_0 : axst := Eval vm_compute in
  relaunch_src segsA FUEL2 [HMCUT; ECALL_MMAP] G2 [S_s2x_rec] [S_s2x false] OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n0.Start2States.T_hm2.
Definition T_hm2_1 : axst := Eval vm_compute in
  relaunch_src segsA FUEL2 [HMCUT; ECALL_MMAP] G2 [S_s2x_rec] [S_s2x true] OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n0.Start2States.T_hm2.
Definition T_hm2 (r : bool) : axst := if r then T_hm2_1 else T_hm2_0.
Definition T_hm2_S (r : bool) : sstate := ax_S (T_hm2 r).

(* [S_hm2] is [T_hm2] restated: reg 10 := 2^47 - 1. *)
Definition restate_hm2 (T : sstate) : sstate :=
  with_regs T (set_sv (ss_regs T) 10 (SLit (2 ^ 47 - 1))) (ss_next T).
Definition S_hm2 (r : bool) : axst := ax_setS (T_hm2 r) (restate_hm2 (T_hm2_S r)).
Definition S_hm2_S (r : bool) : sstate := ax_S (S_hm2 r).

Definition S_hm2_rec : axst :=
  ax_setS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n0.Start2States.T_hm2
          (restate_hm2 (ax_S OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n0.Start2States.T_hm2)).
Definition E_s3_0 : axst := Eval vm_compute in
  relaunch_src segsA FUEL2 [HMCUT; ECALL_MMAP] G2 [S_hm2_rec] [S_hm2 false] OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n0.Start2States.E_s3.
Definition E_s3_1 : axst := Eval vm_compute in
  relaunch_src segsA FUEL2 [HMCUT; ECALL_MMAP] G2 [S_hm2_rec] [S_hm2 true] OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n0.Start2States.E_s3.
Definition E_s3 (r : bool) : axst := if r then E_s3_1 else E_s3_0.
Definition E_s3_S (r : bool) : sstate := ax_S (E_s3 r).

End Start2R.

Module Start3R.
Import Start1R Start2R.

Definition FUEL3 : nat := (160 * 1000)%nat.
Definition G3 : positive := 29%positive.

Definition S_s3x (r : bool) : axst :=
  OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.StartNodes.eager_ok (E_s3 r) 0x38e000 29%positive.
Definition S_s3x_S (r : bool) : sstate := ax_S (S_s3x r).
Definition S_s3fail (r : bool) : axst := axS (S_ret_lit (ax_S (E_s3 r)) enomem_ret).

Definition SPIN6_0 : axst := Eval vm_compute in
  leafA1 (sym_runA segsA 400%nat [SPIN_MMAPORDIE] (S_s3fail false) true) OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n0.Start3States.SPIN6.
Definition SPIN6_1 : axst := Eval vm_compute in
  leafA1 (sym_runA segsA 400%nat [SPIN_MMAPORDIE] (S_s3fail true) true) OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n0.Start3States.SPIN6.
Definition SPIN6 (r : bool) : axst := if r then SPIN6_1 else SPIN6_0.
Definition SPIN6_S (r : bool) : sstate := ax_S (SPIN6 r).

Definition S_s3x_rec : axst :=
  OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.StartNodes.eager_ok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n0.Start2States.E_s3 0x38e000 29%positive.
Definition E_k7_0 : axst := Eval vm_compute in
  relaunch_src segsA FUEL3 [HMCUT; ECALL_MMAP] G3 [S_s3x_rec] [S_s3x false] OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n0.Start3States.E_k7.
Definition E_k7_1 : axst := Eval vm_compute in
  relaunch_src segsA FUEL3 [HMCUT; ECALL_MMAP] G3 [S_s3x_rec] [S_s3x true] OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n0.Start3States.E_k7.
Definition E_k7 (r : bool) : axst := if r then E_k7_1 else E_k7_0.
Definition E_k7_S (r : bool) : sstate := ax_S (E_k7 r).

End Start3R.
