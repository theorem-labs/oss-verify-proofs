(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim FPSteps FrmInv. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10FrmScan0_u Pm10FrmScan1_u Pm10FrmScan2_u Pm10FrmScan3_u Pm10FrmScan4_u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module Pm10FrmInv.
Abbreviation SEGS := Ubsan.M.loaded_segments.

Lemma text_safe : FrmInv.text_safe SEGS.
Proof.
  intros s Hin Hx.
  change SEGS with [Ubsan_segment_000; Ubsan_segment_001; Ubsan_segment_002; Ubsan_segment_003] in Hin.
  cbn [In] in Hin. destruct Hin as [<- | Hin].
  { vm_compute in Hx. discriminate. }
  destruct Hin as [<- | Hin].
  { split; [vm_compute; reflexivity|]. intros a Ha.
    change (Z.of_N (seg_base Ubsan_segment_001)) with 0x39000 in Ha. change (Z.of_N (seg_size Ubsan_segment_001)) with 0x84000 in Ha.
    destruct (Z_lt_le_dec a 0x58000); [apply (FrmInv.range_all_sound _ _ _ Pm10FrmScan0_u.chunk); lia|].
    destruct (Z_lt_le_dec a 0x78000); [apply (FrmInv.range_all_sound _ _ _ Pm10FrmScan1_u.chunk); lia|].
    destruct (Z_lt_le_dec a 0x98000); [apply (FrmInv.range_all_sound _ _ _ Pm10FrmScan2_u.chunk); lia|].
    destruct (Z_lt_le_dec a 0xb8000); [apply (FrmInv.range_all_sound _ _ _ Pm10FrmScan3_u.chunk); lia|].
    apply (FrmInv.range_all_sound _ _ _ Pm10FrmScan4_u.chunk); lia. }
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
End Pm10FrmInv.
