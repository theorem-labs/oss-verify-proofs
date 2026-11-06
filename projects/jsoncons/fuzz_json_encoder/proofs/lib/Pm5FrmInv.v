(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim FPSteps FrmInv Pm5FrmScan0 Pm5FrmScan1 Pm5FrmScan2 Pm5FrmScan3 Pm5FrmScan4 Pm5FrmScan5 Pm5FrmScan6 Pm5FrmScan7 Pm5FrmScan8.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module Pm5FrmInv.
Abbreviation SEGS := AsanUbsan.M.loaded_segments.

Lemma text_safe : FrmInv.text_safe SEGS.
Proof.
  intros s Hin Hx.
  change SEGS with [AsanUbsan_segment_000; AsanUbsan_segment_001; AsanUbsan_segment_002; AsanUbsan_segment_003] in Hin.
  cbn [In] in Hin. destruct Hin as [<- | Hin].
  { vm_compute in Hx. discriminate. }
  destruct Hin as [<- | Hin].
  { split; [vm_compute; reflexivity|]. intros a Ha.
    change (Z.of_N (seg_base AsanUbsan_segment_001)) with 0x59000 in Ha. change (Z.of_N (seg_size AsanUbsan_segment_001)) with 0x105000 in Ha.
    destruct (Z_lt_le_dec a 0x79000); [apply (FrmInv.range_all_sound _ _ _ Pm5FrmScan0.chunk); lia|].
    destruct (Z_lt_le_dec a 0x99000); [apply (FrmInv.range_all_sound _ _ _ Pm5FrmScan1.chunk); lia|].
    destruct (Z_lt_le_dec a 0xb9000); [apply (FrmInv.range_all_sound _ _ _ Pm5FrmScan2.chunk); lia|].
    destruct (Z_lt_le_dec a 0xd9000); [apply (FrmInv.range_all_sound _ _ _ Pm5FrmScan3.chunk); lia|].
    destruct (Z_lt_le_dec a 0xf9000); [apply (FrmInv.range_all_sound _ _ _ Pm5FrmScan4.chunk); lia|].
    destruct (Z_lt_le_dec a 0x119000); [apply (FrmInv.range_all_sound _ _ _ Pm5FrmScan5.chunk); lia|].
    destruct (Z_lt_le_dec a 0x139000); [apply (FrmInv.range_all_sound _ _ _ Pm5FrmScan6.chunk); lia|].
    destruct (Z_lt_le_dec a 0x159000); [apply (FrmInv.range_all_sound _ _ _ Pm5FrmScan7.chunk); lia|].
    destruct (Z_lt_le_dec a 0x15d000); [apply (FrmInv.range_all_sound _ _ _ Pm5FrmScan8.chunk); lia|].
    assert (C9 : FrmInv.range_all (FrmInv.addr_ok SEGS) 0x15d000 4096%positive = true) by (vm_cast_no_check (eq_refl true)).
    apply (FrmInv.range_all_sound _ _ _ C9); lia. }
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
End Pm5FrmInv.
