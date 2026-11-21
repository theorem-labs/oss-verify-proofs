(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: made for LPS 727298f3 from the start-up states of A/Start4States.v, A/e4.v (Start4FailStates) and A/e5.v (Start4FailCut): segment 4's states computed in the build per CONFIG_RSEQ from segment 3's computed exit (A/StartRegenS.v), each run's leaf by the run from the computed state before it and each other state by the recorded module's own rule. *)
(* Segment 4 of the start-up chain (A/e9.v Start4, A/e6.v Start4Fail), made per CONFIG_RSEQ.
   A/Start4States.v, A/e4.v (Start4FailStates) and A/e5.v (Start4FailCut) compute segment 4's
   states in the build from A/e0.v's recorded exit of segment 3 ([E_k7]).  At LPS 727298f3 that
   exit depends on the flag (A/StartRegenS.v [Start3R.E_k7 r]), so each of those states is made
   again here from [E_k7 r], by the same definition:
   - a state the recorded module computes ([Eval vm_compute]: a run's leaf, a restatement, an
     object move or split) is computed for [r = false] ([X_0]) and [r = true] ([X_1]), [X r]
     selecting between them; a run's leaf is the run from the computed state before it;
   - a state the recorded module writes as a term of earlier states is that term over the
     computed ones ([X r]).
   Every state here is reached by a run or a fixed rule from the start state, so no recorded cut
   or exit state is relaunched (Lib/Relaunch.v is not needed).  The definitions that do not
   depend on the start state (addresses, fact lists, object shapes, [leaf1], [fail_state], ...)
   are the recorded modules' own; A/StartRegen2.v proves the runs and facts per value. *)
From Stdlib Require Import ZArith NArith List Bool PArith.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymCall Glue3 SymHeap SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts e2 StartDefsA Start4States e4 e5 StartRegenS.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.StartALib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start4States.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Start4FailStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e5.Start4FailCut.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Module Start4R.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartRegenS.Start3R.

Definition S_k7ok (r : bool) : axst :=
  axA (add_facts F7 (S_after (ax_S (E_k7 r)) (SVar 29%positive) (ss_objs (ax_S (E_k7 r))) 31%positive)).
Definition E_k8_0 : axst := Eval vm_compute in
  leaf1 (S_k7ok false) (sym_runA segsA 3000%nat [ECALL_MMAP] (S_k7ok false) true).
Definition E_k8_1 : axst := Eval vm_compute in
  leaf1 (S_k7ok true) (sym_runA segsA 3000%nat [ECALL_MMAP] (S_k7ok true) true).
Definition E_k8 (r : bool) : axst := if r then E_k8_1 else E_k8_0.
Definition SPIN7_0 : axst := Eval vm_compute in
  leaf1 (fail_state (E_k7 false)) (sym_runA segsA 200%nat [SPIN_RAR] (fail_state (E_k7 false)) true).
Definition SPIN7_1 : axst := Eval vm_compute in
  leaf1 (fail_state (E_k7 true)) (sym_runA segsA 200%nat [SPIN_RAR] (fail_state (E_k7 true)) true).
Definition SPIN7 (r : bool) : axst := if r then SPIN7_1 else SPIN7_0.
Definition E_k8x_0 : axst := Eval vm_compute in
  (axA (add_facts F8x (restate_S ps8 (ax_S (E_k8 false))))).
Definition E_k8x_1 : axst := Eval vm_compute in
  (axA (add_facts F8x (restate_S ps8 (ax_S (E_k8 true))))).
Definition E_k8x (r : bool) : axst := if r then E_k8x_1 else E_k8x_0.
Definition S_k8ok (r : bool) : axst :=
  axA (S_after (ax_S (E_k8x r)) ri30 ((ss_objs (ax_S (E_k8x r))) ++ [objRI]) 31%positive).
Definition L8mx_0 : axst := Eval vm_compute in
  leaf1 (withX0 (S_k8ok false)) (sym_runA segsA 3000%nat [MEMSET; ECALL_MMAP] (withX0 (S_k8ok false)) true).
Definition L8mx_1 : axst := Eval vm_compute in
  leaf1 (withX0 (S_k8ok true)) (sym_runA segsA 3000%nat [MEMSET; ECALL_MMAP] (withX0 (S_k8ok true)) true).
Definition L8mx (r : bool) : axst := if r then L8mx_1 else L8mx_0.
Definition L8m_0 : axst := Eval vm_compute in
  (noX (L8mx false)).
Definition L8m_1 : axst := Eval vm_compute in
  (noX (L8mx true)).
Definition L8m (r : bool) : axst := if r then L8m_1 else L8m_0.
Definition M8 (r : bool) : axst :=
  axA (add_facts F8m (set_objs (ax_S (L8m r)) ((ss_objs (ax_S (L8m r))) ++ [objShRI]))).
Definition E_k9_0 : axst := Eval vm_compute in
  leaf1 (M8 false) (sym_runA segsA 3000%nat [ECALL_MMAP] (M8 false) true).
Definition E_k9_1 : axst := Eval vm_compute in
  leaf1 (M8 true) (sym_runA segsA 3000%nat [ECALL_MMAP] (M8 true) true).
Definition E_k9 (r : bool) : axst := if r then E_k9_1 else E_k9_0.
Definition S_k9ok (r : bool) : axst :=
  axA (add_facts F9 (S_after (ax_S (E_k9 r)) (SVar 32%positive) (ss_objs (ax_S (E_k9 r))) 33%positive)).
Definition E_k10_0 : axst := Eval vm_compute in
  leaf1 (S_k9ok false) (sym_runA segsA 3000%nat [ECALL_MMAP] (S_k9ok false) true).
Definition E_k10_1 : axst := Eval vm_compute in
  leaf1 (S_k9ok true) (sym_runA segsA 3000%nat [ECALL_MMAP] (S_k9ok true) true).
Definition E_k10 (r : bool) : axst := if r then E_k10_1 else E_k10_0.
Definition SPIN9_0 : axst := Eval vm_compute in
  leaf1 (fail_state (E_k9 false)) (sym_runA segsA 200%nat [SPIN_RAR] (fail_state (E_k9 false)) true).
Definition SPIN9_1 : axst := Eval vm_compute in
  leaf1 (fail_state (E_k9 true)) (sym_runA segsA 200%nat [SPIN_RAR] (fail_state (E_k9 true)) true).
Definition SPIN9 (r : bool) : axst := if r then SPIN9_1 else SPIN9_0.
Definition S_k10ok (r : bool) : axst :=
  axA (add_facts F10 (S_after (ax_S (E_k10 r)) (SVar 33%positive) ((ss_objs (ax_S (E_k10 r))) ++ [mmap_obj 33%positive 4096]) 34%positive)).
Definition E_k11_0 : axst := Eval vm_compute in
  leaf1 (S_k10ok false) (sym_runA segsA 3000%nat [ECALL_MMAP] (S_k10ok false) true).
Definition E_k11_1 : axst := Eval vm_compute in
  leaf1 (S_k10ok true) (sym_runA segsA 3000%nat [ECALL_MMAP] (S_k10ok true) true).
Definition E_k11 (r : bool) : axst := if r then E_k11_1 else E_k11_0.
Definition SPIN10_0 : axst := Eval vm_compute in
  leaf1 (fail_state (E_k10 false)) (sym_runA segsA 200%nat [SPIN_MMAPORDIE] (fail_state (E_k10 false)) true).
Definition SPIN10_1 : axst := Eval vm_compute in
  leaf1 (fail_state (E_k10 true)) (sym_runA segsA 200%nat [SPIN_MMAPORDIE] (fail_state (E_k10 true)) true).
Definition SPIN10 (r : bool) : axst := if r then SPIN10_1 else SPIN10_0.
Definition S_k11ok (r : bool) : axst :=
  axA (add_facts F11 (S_after (ax_S (E_k11 r)) (SVar 34%positive) ((ss_objs (ax_S (E_k11 r))) ++ [mmap_obj 34%positive 65536]) 35%positive)).
Definition S_k11c (r : bool) (hi : bool) : axst :=
  axA (add_facts [CLS11 hi] (ax_S (S_k11ok r))).
Definition SPIN11_0 : axst := Eval vm_compute in
  leaf1 (fail_state (E_k11 false)) (sym_runA segsA 200%nat [SPIN_MMAPORDIE] (fail_state (E_k11 false)) true).
Definition SPIN11_1 : axst := Eval vm_compute in
  leaf1 (fail_state (E_k11 true)) (sym_runA segsA 200%nat [SPIN_MMAPORDIE] (fail_state (E_k11 true)) true).
Definition SPIN11 (r : bool) : axst := if r then SPIN11_1 else SPIN11_0.
Definition L11mx_lo_0 : axst := Eval vm_compute in
  (run_to 3000%nat [MEMSET; ECALL_MMAP] (withX0 (S_k11c false false))).
Definition L11mx_lo_1 : axst := Eval vm_compute in
  (run_to 3000%nat [MEMSET; ECALL_MMAP] (withX0 (S_k11c true false))).
Definition L11mx_lo (r : bool) : axst := if r then L11mx_lo_1 else L11mx_lo_0.
Definition L11mx_hi_0 : axst := Eval vm_compute in
  (run_to 3000%nat [MEMSET; ECALL_MMAP] (withX0 (S_k11c false true))).
Definition L11mx_hi_1 : axst := Eval vm_compute in
  (run_to 3000%nat [MEMSET; ECALL_MMAP] (withX0 (S_k11c true true))).
Definition L11mx_hi (r : bool) : axst := if r then L11mx_hi_1 else L11mx_hi_0.
Definition L11mx (r : bool) (hi : bool) : axst :=
  if hi then (L11mx_hi r) else (L11mx_lo r).
Definition L11m_lo_0 : axst := Eval vm_compute in
  (noX (L11mx_lo false)).
Definition L11m_lo_1 : axst := Eval vm_compute in
  (noX (L11mx_lo true)).
Definition L11m_lo (r : bool) : axst := if r then L11m_lo_1 else L11m_lo_0.
Definition L11m_hi_0 : axst := Eval vm_compute in
  (noX (L11mx_hi false)).
Definition L11m_hi_1 : axst := Eval vm_compute in
  (noX (L11mx_hi true)).
Definition L11m_hi (r : bool) : axst := if r then L11m_hi_1 else L11m_hi_0.
Definition L11m (r : bool) (hi : bool) : axst :=
  if hi then (L11m_hi r) else (L11m_lo r).
Definition T1_11_lo_0 : sstate := Eval vm_compute in
  (move_obj_last (ax_S (L11m_lo false)) 13).
Definition T1_11_lo_1 : sstate := Eval vm_compute in
  (move_obj_last (ax_S (L11m_lo true)) 13).
Definition T1_11_lo (r : bool) : sstate := if r then T1_11_lo_1 else T1_11_lo_0.
Definition T1_11_hi_0 : sstate := Eval vm_compute in
  (move_obj_last (ax_S (L11m_hi false)) 13).
Definition T1_11_hi_1 : sstate := Eval vm_compute in
  (move_obj_last (ax_S (L11m_hi true)) 13).
Definition T1_11_hi (r : bool) : sstate := if r then T1_11_hi_1 else T1_11_hi_0.
Definition T1_11 (r : bool) (hi : bool) : sstate :=
  if hi then (T1_11_hi r) else (T1_11_lo r).
Definition T2_11_lo_0 : sstate := Eval vm_compute in
  (match split_obj_at (T1_11_lo false) 15 (SLit 512) with Some S' => S' | None => (T1_11_lo false) end).
Definition T2_11_lo_1 : sstate := Eval vm_compute in
  (match split_obj_at (T1_11_lo true) 15 (SLit 512) with Some S' => S' | None => (T1_11_lo true) end).
Definition T2_11_lo (r : bool) : sstate := if r then T2_11_lo_1 else T2_11_lo_0.
Definition T2_11_hi_0 : sstate := Eval vm_compute in
  (match split_obj_at (T1_11_hi false) 15 (SLit 512) with Some S' => S' | None => (T1_11_hi false) end).
Definition T2_11_hi_1 : sstate := Eval vm_compute in
  (match split_obj_at (T1_11_hi true) 15 (SLit 512) with Some S' => S' | None => (T1_11_hi true) end).
Definition T2_11_hi (r : bool) : sstate := if r then T2_11_hi_1 else T2_11_hi_0.
Definition T2_11 (r : bool) (hi : bool) : sstate :=
  if hi then (T2_11_hi r) else (T2_11_lo r).
Definition M11 (r : bool) (hi : bool) : axst :=
  axA (add_facts F11m (set_objs (T2_11 r hi) ((firstn 16%nat (ss_objs (T2_11 r hi))) ++ [objShB6]))).
Definition E_k12c_lo_0 : axst := Eval vm_compute in
  (run_to 6000%nat [ECALL_MMAP] (M11 false false)).
Definition E_k12c_lo_1 : axst := Eval vm_compute in
  (run_to 6000%nat [ECALL_MMAP] (M11 true false)).
Definition E_k12c_lo (r : bool) : axst := if r then E_k12c_lo_1 else E_k12c_lo_0.
Definition E_k12c_hi_0 : axst := Eval vm_compute in
  (run_to 6000%nat [ECALL_MMAP] (M11 false true)).
Definition E_k12c_hi_1 : axst := Eval vm_compute in
  (run_to 6000%nat [ECALL_MMAP] (M11 true true)).
Definition E_k12c_hi (r : bool) : axst := if r then E_k12c_hi_1 else E_k12c_hi_0.
Definition E_k12c (r : bool) (hi : bool) : axst :=
  if hi then (E_k12c_hi r) else (E_k12c_lo r).
Definition E_k12_0 : axst := Eval vm_compute in
  (drop_last_obj (E_k12c_hi false)).
Definition E_k12_1 : axst := Eval vm_compute in
  (drop_last_obj (E_k12c_hi true)).
Definition E_k12 (r : bool) : axst := if r then E_k12_1 else E_k12_0.
Definition E_k12d_0 : axst := Eval vm_compute in
  (axA (drop_fact (CLS11 true) (ax_S (E_k12 false)))).
Definition E_k12d_1 : axst := Eval vm_compute in
  (axA (drop_fact (CLS11 true) (ax_S (E_k12 true)))).
Definition E_k12d (r : bool) : axst := if r then E_k12d_1 else E_k12d_0.

Definition F0 (r : bool) : axst :=
  fail_state (E_k8x r).
Definition RUN1_0 : option (list leafA) := Eval vm_compute in
  sym_runA segsA FUEL1 [PC_OUT; PC_SPIN] (F0 false) true.
Definition RUN1_1 : option (list leafA) := Eval vm_compute in
  sym_runA segsA FUEL1 [PC_OUT; PC_SPIN] (F0 true) true.
Definition RUN1 (r : bool) : option (list leafA) := if r then RUN1_1 else RUN1_0.
Definition L1a (r : bool) : axst :=
  (match RUN1 r with Some l0 => (match l0 with nil => F0 r | cons l l1 => la_state l end) | None => F0 r end).
Definition L1b (r : bool) : axst :=
  (match RUN1 r with Some l0 => (match l0 with nil => F0 r | cons l1 l2 => (match l2 with nil => F0 r | cons l l3 => la_state l end) end) | None => F0 r end).

Definition C2_facts (r : bool) : list sprop :=
  [SPUle (SLit 1) vP; SPUle vP (SLit 12)] ++ ss_facts (ax_S (F0 r)).
Definition C2_objs (r : bool) : list sobj :=
  upd_obj0 (fun o : sobj => set_dflt DUnknown (set_cell_val (-592) e_cur (drop_cells (-396) (-376) (drop_cells (-936) (-696) (drop_sym_cells o))))) (ss_objs (ax_S (L1a r))).
Definition C2 (r : bool) : axst :=
  axA (mkSS PC_OUT (setregs (ss_regs (ax_S (L1a r))) [(11%nat, vP); (13%nat, e_cur); (14%nat, e_nbp); (16%nat, SVar 32%positive); (17%nat, SVar 33%positive)]) (ss_fregs (ax_S (L1a r))) (ss_fcsr (ax_S (L1a r))) (ss_resv (ax_S (L1a r))) (C2_objs r) (C2_facts r) 34%positive false).
Definition RUN2_0 : option (list leafA) := Eval vm_compute in
  sym_runA segsA FUEL2 [PC_OUT; PC_SPIN] (C2 false) true.
Definition RUN2_1 : option (list leafA) := Eval vm_compute in
  sym_runA segsA FUEL2 [PC_OUT; PC_SPIN] (C2 true) true.
Definition RUN2 (r : bool) : option (list leafA) := if r then RUN2_1 else RUN2_0.
Definition E_spin (r : bool) : axst :=
  (match RUN2 r with Some l0 => (match l0 with nil => C2 r | cons l l1 => la_state l end) | None => C2 r end).
Definition L2b (r : bool) : axst :=
  (match RUN2 r with Some l0 => (match l0 with nil => C2 r | cons l1 l2 => (match l2 with nil => C2 r | cons l l3 => la_state l end) end) | None => C2 r end).
Definition L2c (r : bool) : axst :=
  (match RUN2 r with Some l0 => (match l0 with nil => C2 r | cons l1 l2 => (match l2 with nil => C2 r | cons l3 l4 => (match l4 with nil => C2 r | cons l l5 => la_state l end) end) end) | None => C2 r end).

End Start4R.
