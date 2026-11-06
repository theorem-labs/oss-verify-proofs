(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim FPSteps FrmInv Pm9FrmScan0 Pm9FrmScan1 Pm9FrmScan2 Pm9FrmScan3 Pm9FrmScan4 Pm9FrmScan5 Pm9FrmScan6 Pm9FrmScan7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module Pm9FrmInv.
Abbreviation SEGS := AsanUbsan.M.loaded_segments.

Lemma text_safe : FrmInv.text_safe SEGS.
Proof.
  intros s Hin Hx.
  change SEGS with [AsanUbsan_segment_000; AsanUbsan_segment_001; AsanUbsan_segment_002; AsanUbsan_segment_003] in Hin.
  cbn [In] in Hin. destruct Hin as [<- | Hin].
  { vm_compute in Hx. discriminate. }
  destruct Hin as [<- | Hin].
  { split; [vm_compute; reflexivity|]. intros a Ha.
    change (Z.of_N (seg_base AsanUbsan_segment_001)) with 0x58000 in Ha. change (Z.of_N (seg_size AsanUbsan_segment_001)) with 0xf6000 in Ha.
    destruct (Z_lt_le_dec a 0x78000); [apply (FrmInv.range_all_sound _ _ _ Pm9FrmScan0.chunk); lia|].
    destruct (Z_lt_le_dec a 0x98000); [apply (FrmInv.range_all_sound _ _ _ Pm9FrmScan1.chunk); lia|].
    destruct (Z_lt_le_dec a 0xb8000); [apply (FrmInv.range_all_sound _ _ _ Pm9FrmScan2.chunk); lia|].
    destruct (Z_lt_le_dec a 0xd8000); [apply (FrmInv.range_all_sound _ _ _ Pm9FrmScan3.chunk); lia|].
    destruct (Z_lt_le_dec a 0xf8000); [apply (FrmInv.range_all_sound _ _ _ Pm9FrmScan4.chunk); lia|].
    destruct (Z_lt_le_dec a 0x118000); [apply (FrmInv.range_all_sound _ _ _ Pm9FrmScan5.chunk); lia|].
    destruct (Z_lt_le_dec a 0x138000); [apply (FrmInv.range_all_sound _ _ _ Pm9FrmScan6.chunk); lia|].
    apply (FrmInv.range_all_sound _ _ _ Pm9FrmScan7.chunk); lia. }
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
End Pm9FrmInv.
