(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim FPSteps FrmInv Pm6FrmScan0 Pm6FrmScan1 Pm6FrmScan2 Pm6FrmScan3 Pm6FrmScan4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module Pm6FrmInv.
Abbreviation SEGS := Plain.M.loaded_segments.

Lemma text_safe : FrmInv.text_safe SEGS.
Proof.
  intros s Hin Hx.
  change SEGS with [Plain_segment_000; Plain_segment_001; Plain_segment_002; Plain_segment_003] in Hin.
  cbn [In] in Hin. destruct Hin as [<- | Hin].
  { vm_compute in Hx. discriminate. }
  destruct Hin as [<- | Hin].
  { split; [vm_compute; reflexivity|]. intros a Ha.
    change (Z.of_N (seg_base Plain_segment_001)) with 0x39000 in Ha. change (Z.of_N (seg_size Plain_segment_001)) with 0x87000 in Ha.
    destruct (Z_lt_le_dec a 0x59000); [apply (FrmInv.range_all_sound _ _ _ Pm6FrmScan0.chunk); lia|].
    destruct (Z_lt_le_dec a 0x79000); [apply (FrmInv.range_all_sound _ _ _ Pm6FrmScan1.chunk); lia|].
    destruct (Z_lt_le_dec a 0x99000); [apply (FrmInv.range_all_sound _ _ _ Pm6FrmScan2.chunk); lia|].
    destruct (Z_lt_le_dec a 0xb9000); [apply (FrmInv.range_all_sound _ _ _ Pm6FrmScan3.chunk); lia|].
    apply (FrmInv.range_all_sound _ _ _ Pm6FrmScan4.chunk); lia. }
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
