(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim FPSteps FrmInv Pm8FrmScan0 Pm8FrmScan1 Pm8FrmScan2 Pm8FrmScan3 Pm8FrmScan4 Pm8FrmScan5 Pm8FrmScan6 Pm8FrmScan7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module Pm8FrmInv.
Abbreviation SEGS := Asan.M.loaded_segments.

Lemma text_safe : FrmInv.text_safe SEGS.
Proof.
  intros s Hin Hx.
  change SEGS with [Asan_segment_000; Asan_segment_001; Asan_segment_002; Asan_segment_003] in Hin.
  cbn [In] in Hin. destruct Hin as [<- | Hin].
  { vm_compute in Hx. discriminate. }
  destruct Hin as [<- | Hin].
  { split; [vm_compute; reflexivity|]. intros a Ha.
    change (Z.of_N (seg_base Asan_segment_001)) with 0x58000 in Ha. change (Z.of_N (seg_size Asan_segment_001)) with 0xf4000 in Ha.
    destruct (Z_lt_le_dec a 0x78000); [apply (FrmInv.range_all_sound _ _ _ Pm8FrmScan0.chunk); lia|].
    destruct (Z_lt_le_dec a 0x98000); [apply (FrmInv.range_all_sound _ _ _ Pm8FrmScan1.chunk); lia|].
    destruct (Z_lt_le_dec a 0xb8000); [apply (FrmInv.range_all_sound _ _ _ Pm8FrmScan2.chunk); lia|].
    destruct (Z_lt_le_dec a 0xd8000); [apply (FrmInv.range_all_sound _ _ _ Pm8FrmScan3.chunk); lia|].
    destruct (Z_lt_le_dec a 0xf8000); [apply (FrmInv.range_all_sound _ _ _ Pm8FrmScan4.chunk); lia|].
    destruct (Z_lt_le_dec a 0x118000); [apply (FrmInv.range_all_sound _ _ _ Pm8FrmScan5.chunk); lia|].
    destruct (Z_lt_le_dec a 0x138000); [apply (FrmInv.range_all_sound _ _ _ Pm8FrmScan6.chunk); lia|].
    apply (FrmInv.range_all_sound _ _ _ Pm8FrmScan7.chunk); lia. }
  destruct Hin as [<- | Hin].
  { vm_compute in Hx. discriminate. }
  destruct Hin as [<- | []].
  { vm_compute in Hx. discriminate. }
Qed.

Theorem msteps_fp_ok : forall (fx fx' : FPState) R pc M rom R' pc' M' rom',
  msteps SEGS (@mkst fx R pc M rom) (@mkst fx' R' pc' M' rom') -> FrmInv.fp_ok fx -> FrmInv.fp_ok fx'.
Proof. exact (FrmInv.msteps_fp_ok SEGS text_safe). Qed.

Theorem step_frm_zero : forall ms ms', RiscvSemantics.step SEGS ms = MachineOk ms' -> frm_zero (ms_fcsr ms) -> frm_zero (ms_fcsr ms').
Proof. exact (FrmInv.step_frm_zero SEGS text_safe). Qed.

Theorem msteps_frm_zero : forall ms ms', msteps SEGS ms ms' -> frm_zero (ms_fcsr ms) -> frm_zero (ms_fcsr ms').
Proof. exact (FrmInv.msteps_frm_zero SEGS text_safe). Qed.
End Pm8FrmInv.
