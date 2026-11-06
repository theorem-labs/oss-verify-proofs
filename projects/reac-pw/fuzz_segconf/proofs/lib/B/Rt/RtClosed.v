(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin sha256 c3796c0b38f3): the closing file of the core's
   runtime rows that image B's walks name, in the place and the role of plugin-hostd/fuzz_command's
   lib/B/Rt/RtClosed.v (origin/ossv/recipes bf33659295b7): each proved runtime contract of image B restated with its
   `AR_laws tfibsegs B` premise discharged by the core's law proof (lib/B/YG0q.v AR_laws_ok, generic in the segment
   list and the record) and its entry stated at image B's listing term (lib/B/Prog/SegInstB.v pc_<x>A, by
   computation), so that only the per-binary record `SegBSyms B` (lib/B/YF0m.v) remains:
     __asan_set_shadow_00 / _f5 / _f8 (lib/B/Rt/RtShadowProof.v), __asan_stack_malloc_0 / _1 / _3 / _5
     (lib/B/Rt/RtSM0.v, RtSM1.v, RtSM3.v, RtSM5.v), __asan_stack_free_5 (lib/B/Rt/RtSF5.v; its rodata list reads the
     .rodata word 0x10338 = 0xf5f5f5f5f5f5f5f5 as a record constant, lib/B/YF0m.v's row), __asan_memcpy /
     __asan_memset (lib/B/Rt/RtLAsanMemcpy.v, RtLAsanMemset.v, at the record's code field, ts_code).
   Each theorem stays generic in the floating-point state and the run ceiling.
   proves no function (kind: merge; the core's runtime rows from their proved contracts). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YB1v YF0l YF0m.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtShadow RtStack.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require RtShadowProof RtSM0 RtSM1 RtSM3 RtSM5 RtSF5
  RtLAsanMemcpy RtLAsanMemset.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegInstB.
Local Open Scope Z_scope.

Section closed. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
(* image B's per-binary record (lib/B/YF0m.v) *)
Hypothesis HB : SegBSyms B.

(* __asan_set_shadow_00 / _f5 / _f8: RtShadowProof's entries SS00_ENTRY / SSF5_ENTRY / SSF8_ENTRY are the listing's *)
Theorem seg_set_shadow_00_closed : aset_shadow_realizes tfibsegs B SegInstB.pc_set_shadow_00A 0.
Proof.
replace SegInstB.pc_set_shadow_00A with RtShadowProof.SS00_ENTRY by (vm_compute; reflexivity).
exact (RtShadowProof.cmd_set_shadow_00 B (YG0q.AR_laws_ok tfibsegs B) HB).
Qed.
Theorem seg_set_shadow_f5_closed : aset_shadow_realizes tfibsegs B SegInstB.pc_set_shadow_f5A 0xf5.
Proof.
replace SegInstB.pc_set_shadow_f5A with RtShadowProof.SSF5_ENTRY by (vm_compute; reflexivity).
exact (RtShadowProof.cmd_set_shadow_f5 B (YG0q.AR_laws_ok tfibsegs B) HB).
Qed.
Theorem seg_set_shadow_f8_closed : aset_shadow_realizes tfibsegs B SegInstB.pc_set_shadow_f8A 0xf8.
Proof.
replace SegInstB.pc_set_shadow_f8A with RtShadowProof.SSF8_ENTRY by (vm_compute; reflexivity).
exact (RtShadowProof.cmd_set_shadow_f8 B (YG0q.AR_laws_ok tfibsegs B) HB).
Qed.

(* __asan_stack_malloc_0 / _1 / _3 / _5 (whole-frame classes) *)
Theorem seg_stack_malloc0_closed : astack_malloc_realizes tfibsegs B 0.
Proof. exact (RtSM0.cmd_stack_malloc0_contract B (YG0q.AR_laws_ok tfibsegs B) HB). Qed.
Theorem seg_stack_malloc1_closed : astack_malloc_realizes tfibsegs B 1.
Proof. exact (RtSM1.cmd_stack_malloc1_contract B (YG0q.AR_laws_ok tfibsegs B) HB). Qed.
Theorem seg_stack_malloc3_closed : astack_malloc_realizes tfibsegs B 3.
Proof. exact (RtSM3.cmd_stack_malloc3_contract B (YG0q.AR_laws_ok tfibsegs B) HB). Qed.
Theorem seg_stack_malloc5_closed : astack_malloc_realizes tfibsegs B 5.
Proof. exact (RtSM5.cmd_stack_malloc5_contract B (YG0q.AR_laws_ok tfibsegs B) HB). Qed.

(* __asan_stack_free_5 (whole-frame shadow): RtSF5's entry is the listing's *)
Theorem seg_stack_free5_closed : astack_free_cls_realizes tfibsegs B SegInstB.pc_stack_free_5A 5.
Proof.
replace SegInstB.pc_stack_free_5A with 0x3ecc4 by (vm_compute; reflexivity).
exact (RtSF5.cmd_stack_free5_contract B (YG0q.AR_laws_ok tfibsegs B) HB).
Qed.

(* __asan_memcpy / __asan_memset: the record's code field (ts_code) is lib/B/YF0l.v's Tfib_code, whose
   pc_asan_memcpy / pc_asan_memset are the listing's *)
Theorem seg_asan_memcpy_closed : aintrin_realizes tfibsegs B OCpy SegInstB.pc_memcpyA.
Proof.
pose proof (RtLAsanMemcpy.cmd_asan_memcpy B (YG0q.AR_laws_ok tfibsegs B) HB) as H.
rewrite (ts_code B HB) in H.
replace SegInstB.pc_memcpyA with (pc_asan_memcpy Tfib_code) by (vm_compute; reflexivity).
exact H.
Qed.
Theorem seg_asan_memset_closed : aintrin_realizes tfibsegs B OSet SegInstB.pc_memsetA.
Proof.
pose proof (RtLAsanMemset.cmd_asan_memset B (YG0q.AR_laws_ok tfibsegs B) HB) as H.
rewrite (ts_code B HB) in H.
replace SegInstB.pc_memsetA with (pc_asan_memset Tfib_code) by (vm_compute; reflexivity).
exact H.
Qed.
End closed.

Print Assumptions seg_set_shadow_00_closed.
Print Assumptions seg_set_shadow_f5_closed.
Print Assumptions seg_set_shadow_f8_closed.
Print Assumptions seg_stack_malloc0_closed.
Print Assumptions seg_stack_malloc1_closed.
Print Assumptions seg_stack_malloc3_closed.
Print Assumptions seg_stack_malloc5_closed.
Print Assumptions seg_stack_free5_closed.
Print Assumptions seg_asan_memcpy_closed.
Print Assumptions seg_asan_memset_closed.
