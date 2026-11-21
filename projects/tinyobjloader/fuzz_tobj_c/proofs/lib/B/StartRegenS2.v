(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: made for LPS 727298f3 from the start-up states of B/n1.v (Start4States): each state of the fourth start-up segment computed in the build per CONFIG_RSEQ from segment 3's exit in B/StartRegenS.v, by the producer B/n1.v applies to its recorded input. *)
(* The fourth start-up segment (B/ng.v Start4), made per CONFIG_RSEQ.  Every state it reads
   comes from segment 3's exit [Start3R.E_k7 r] (B/StartRegenS.v) by runs and fixed rules, so
   each is made again here, for [r = false] ([X_0]) and [r = true] ([X_1]), [X r] selecting
   between them, by the producer of B/n1.v's Start4States, which made it from the recorded
   [E_k7]: a run's leaf is [leaf1] (or [run_to]) of the run from the computed state before it,
   and a restated, moved or split state is the recorded rule applied to the computed one.  A
   definition Start4States writes as a term over its states is the same term over the per-flag
   states; the [hi]-indexed ones are [X r hi].  Start4States' state-free constants and rules
   ([F7], [ps8], [CLS11], [objRI], ...) are read from it unchanged.  No CFG check of this segment
   has a recorded exit, so no state here is relaunched; each is checked by the run lemmas of
   B/StartRegen2.v.  The failed-mmap path of this segment (B/ne.v Start4FailStates, B/ng.v
   Start4FailCut) is made in B/StartRegenS2b.v, since B/ng.v also holds this segment's proof. *)
From Stdlib Require Import ZArith NArith List Bool PArith.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymCFG SymCall SymHeap SymObj SymFrame Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import StartDefsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n8 n1 StartRegenS.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Module Start4R.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.StartALib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Start4States.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.StartRegenS.Start3R.

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
  axA (add_facts F8x (restate_S ps8 (ax_S (E_k8 false)))).
Definition E_k8x_1 : axst := Eval vm_compute in
  axA (add_facts F8x (restate_S ps8 (ax_S (E_k8 true)))).
Definition E_k8x (r : bool) : axst := if r then E_k8x_1 else E_k8x_0.
Definition S_k8ok (r : bool) : axst :=
  axA (S_after (ax_S (E_k8x r)) ri30 (ss_objs (ax_S (E_k8x r)) ++ [objRI]) 31%positive).
Definition L8mx_0 : axst := Eval vm_compute in
  leaf1 (withX0 (S_k8ok false)) (sym_runA segsA 3000%nat [MEMSET; ECALL_MMAP] (withX0 (S_k8ok false)) true).
Definition L8mx_1 : axst := Eval vm_compute in
  leaf1 (withX0 (S_k8ok true)) (sym_runA segsA 3000%nat [MEMSET; ECALL_MMAP] (withX0 (S_k8ok true)) true).
Definition L8mx (r : bool) : axst := if r then L8mx_1 else L8mx_0.
Definition L8m_0 : axst := Eval vm_compute in
  noX (L8mx false).
Definition L8m_1 : axst := Eval vm_compute in
  noX (L8mx true).
Definition L8m (r : bool) : axst := if r then L8m_1 else L8m_0.
Definition M8 (r : bool) : axst :=
  axA (add_facts F8m (set_objs (ax_S (L8m r)) (ss_objs (ax_S (L8m r)) ++ [objShRI]))).
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
  axA (add_facts F10 (S_after (ax_S (E_k10 r)) (SVar 33%positive) (ss_objs (ax_S (E_k10 r)) ++ [mmap_obj 33%positive 4096]) 34%positive)).
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
  axA (add_facts F11 (S_after (ax_S (E_k11 r)) (SVar 34%positive) (ss_objs (ax_S (E_k11 r)) ++ [mmap_obj 34%positive 65536]) 35%positive)).
Definition S_k11c (r hi : bool) : axst := axA (add_facts [CLS11 hi] (ax_S (S_k11ok r))).
Definition SPIN11_0 : axst := Eval vm_compute in
  leaf1 (fail_state (E_k11 false)) (sym_runA segsA 200%nat [SPIN_MMAPORDIE] (fail_state (E_k11 false)) true).
Definition SPIN11_1 : axst := Eval vm_compute in
  leaf1 (fail_state (E_k11 true)) (sym_runA segsA 200%nat [SPIN_MMAPORDIE] (fail_state (E_k11 true)) true).
Definition SPIN11 (r : bool) : axst := if r then SPIN11_1 else SPIN11_0.
Definition L11mx_lo_0 : axst := Eval vm_compute in
  run_to 3000%nat [MEMSET; ECALL_MMAP] (withX0 (S_k11c false false)).
Definition L11mx_lo_1 : axst := Eval vm_compute in
  run_to 3000%nat [MEMSET; ECALL_MMAP] (withX0 (S_k11c true false)).
Definition L11mx_lo (r : bool) : axst := if r then L11mx_lo_1 else L11mx_lo_0.
Definition L11mx_hi_0 : axst := Eval vm_compute in
  run_to 3000%nat [MEMSET; ECALL_MMAP] (withX0 (S_k11c false true)).
Definition L11mx_hi_1 : axst := Eval vm_compute in
  run_to 3000%nat [MEMSET; ECALL_MMAP] (withX0 (S_k11c true true)).
Definition L11mx_hi (r : bool) : axst := if r then L11mx_hi_1 else L11mx_hi_0.
Definition L11mx (r hi : bool) : axst := if hi then L11mx_hi r else L11mx_lo r.
Definition L11m_lo_0 : axst := Eval vm_compute in
  noX (L11mx false false).
Definition L11m_lo_1 : axst := Eval vm_compute in
  noX (L11mx true false).
Definition L11m_lo (r : bool) : axst := if r then L11m_lo_1 else L11m_lo_0.
Definition L11m_hi_0 : axst := Eval vm_compute in
  noX (L11mx false true).
Definition L11m_hi_1 : axst := Eval vm_compute in
  noX (L11mx true true).
Definition L11m_hi (r : bool) : axst := if r then L11m_hi_1 else L11m_hi_0.
Definition L11m (r hi : bool) : axst := if hi then L11m_hi r else L11m_lo r.
Definition T1_11_lo_0 : sstate := Eval vm_compute in
  move_obj_last (ax_S (L11m false false)) 13.
Definition T1_11_lo_1 : sstate := Eval vm_compute in
  move_obj_last (ax_S (L11m true false)) 13.
Definition T1_11_lo (r : bool) : sstate := if r then T1_11_lo_1 else T1_11_lo_0.
Definition T1_11_hi_0 : sstate := Eval vm_compute in
  move_obj_last (ax_S (L11m false true)) 13.
Definition T1_11_hi_1 : sstate := Eval vm_compute in
  move_obj_last (ax_S (L11m true true)) 13.
Definition T1_11_hi (r : bool) : sstate := if r then T1_11_hi_1 else T1_11_hi_0.
Definition T1_11 (r hi : bool) : sstate := if hi then T1_11_hi r else T1_11_lo r.
Definition T2_11_lo_0 : sstate := Eval vm_compute in
  match split_obj_at (T1_11 false false) 15 (SLit 512) with Some S' => S' | None => T1_11 false false end.
Definition T2_11_lo_1 : sstate := Eval vm_compute in
  match split_obj_at (T1_11 true false) 15 (SLit 512) with Some S' => S' | None => T1_11 true false end.
Definition T2_11_lo (r : bool) : sstate := if r then T2_11_lo_1 else T2_11_lo_0.
Definition T2_11_hi_0 : sstate := Eval vm_compute in
  match split_obj_at (T1_11 false true) 15 (SLit 512) with Some S' => S' | None => T1_11 false true end.
Definition T2_11_hi_1 : sstate := Eval vm_compute in
  match split_obj_at (T1_11 true true) 15 (SLit 512) with Some S' => S' | None => T1_11 true true end.
Definition T2_11_hi (r : bool) : sstate := if r then T2_11_hi_1 else T2_11_hi_0.
Definition T2_11 (r hi : bool) : sstate := if hi then T2_11_hi r else T2_11_lo r.
Definition M11 (r hi : bool) : axst :=
  axA (add_facts F11m (set_objs (T2_11 r hi) (firstn 16 (ss_objs (T2_11 r hi)) ++ [objShB6]))).
Definition E_k12c_lo_0 : axst := Eval vm_compute in
  run_to 6000%nat [ECALL_MMAP] (M11 false false).
Definition E_k12c_lo_1 : axst := Eval vm_compute in
  run_to 6000%nat [ECALL_MMAP] (M11 true false).
Definition E_k12c_lo (r : bool) : axst := if r then E_k12c_lo_1 else E_k12c_lo_0.
Definition E_k12c_hi_0 : axst := Eval vm_compute in
  run_to 6000%nat [ECALL_MMAP] (M11 false true).
Definition E_k12c_hi_1 : axst := Eval vm_compute in
  run_to 6000%nat [ECALL_MMAP] (M11 true true).
Definition E_k12c_hi (r : bool) : axst := if r then E_k12c_hi_1 else E_k12c_hi_0.
Definition E_k12c (r hi : bool) : axst := if hi then E_k12c_hi r else E_k12c_lo r.
Definition E_k12_0 : axst := Eval vm_compute in
  drop_last_obj (E_k12c false true).
Definition E_k12_1 : axst := Eval vm_compute in
  drop_last_obj (E_k12c true true).
Definition E_k12 (r : bool) : axst := if r then E_k12_1 else E_k12_0.
Definition E_k12d_0 : axst := Eval vm_compute in
  axA (drop_fact (CLS11 true) (ax_S (E_k12 false))).
Definition E_k12d_1 : axst := Eval vm_compute in
  axA (drop_fact (CLS11 true) (ax_S (E_k12 true))).
Definition E_k12d (r : bool) : axst := if r then E_k12d_1 else E_k12d_0.

End Start4R.
