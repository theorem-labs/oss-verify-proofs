(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim FPSteps FrmInv. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6FrmScan0_u5 Pm6FrmScan1_u5 Pm6FrmScan2_u5 Pm6FrmScan3_u5 Pm6FrmScan4_u5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module Pm6FrmInv.
Abbreviation SEGS := Ubsan.M.loaded_segments.

Lemma text_safe : FrmInv.text_safe SEGS.
Proof.
  intros s Hin Hx.
  change SEGS with [Ubsan_segment_000; Ubsan_segment_001; Ubsan_segment_002; Ubsan_segment_003] in Hin.
  cbn [In] in Hin. destruct Hin as [<- | Hin].
  { vm_compute in Hx. discriminate. }
  destruct Hin as [<- | Hin].
  { split; [vm_compute; reflexivity|]. intros a Ha.
    change (Z.of_N (seg_base Ubsan_segment_001)) with 0x3a000 in Ha. change (Z.of_N (seg_size Ubsan_segment_001)) with 0x8a000 in Ha.
    destruct (Z_lt_le_dec a 0x5a000); [apply (FrmInv.range_all_sound _ _ _ Pm6FrmScan0_u5.chunk); lia|].
    destruct (Z_lt_le_dec a 0x7a000); [apply (FrmInv.range_all_sound _ _ _ Pm6FrmScan1_u5.chunk); lia|].
    destruct (Z_lt_le_dec a 0x9a000); [apply (FrmInv.range_all_sound _ _ _ Pm6FrmScan2_u5.chunk); lia|].
    destruct (Z_lt_le_dec a 0xba000); [apply (FrmInv.range_all_sound _ _ _ Pm6FrmScan3_u5.chunk); lia|].
    apply (FrmInv.range_all_sound _ _ _ Pm6FrmScan4_u5.chunk); lia. }
  destruct Hin as [<- | Hin].
  { vm_compute in Hx. discriminate. }
  destruct Hin as [<- | []].
  { vm_compute in Hx. discriminate. }
Qed.

(* [comment removed for export] *)
Theorem msteps_fp_ok : forall (fx fx' : FPState) R pc M rom R' pc' M' rom',
  msteps SEGS (@mkst fx R pc M rom) (@mkst fx' R' pc' M' rom') -> FrmInv.fp_ok fx -> FrmInv.fp_ok fx'.
Proof. exact (FrmInv.msteps_fp_ok SEGS text_safe). Qed.

Theorem step_frm_zero : forall ms ms', RiscvSemantics.step SEGS ms = MachineOk ms' -> frm_zero (ms_fcsr ms) -> frm_zero (ms_fcsr ms').
Proof. exact (FrmInv.step_frm_zero SEGS text_safe). Qed.

Theorem msteps_frm_zero : forall ms ms', msteps SEGS ms ms' -> frm_zero (ms_fcsr ms) -> frm_zero (ms_fcsr ms').
Proof. exact (FrmInv.msteps_frm_zero SEGS text_safe). Qed.
End Pm6FrmInv.
