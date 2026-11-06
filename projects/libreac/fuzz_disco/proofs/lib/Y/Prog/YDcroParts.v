(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_stamp_headamp on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACam.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACbf.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACf6.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v, with its module paths and module names changed; 419 of its 458 lines of code are new or changed and 1239 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/DiscoYEntProC.v; 21 of its 51 lines of code are new or changed and 428 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0m YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YP0l YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC8i YC44 YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC1i YCbf YCj1 YCja YCjr YRo.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YB1v YXcalls YCbj.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import
disco_table_c disco_classify_c hunt_c SightModel reac_master_only_cadence_ns_c reac_rate_snap_c
reac_frame_clean_len_c slot_inv slot_frame reac_hunt_verdict_name_c disco_box_name_model.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import DiscoYEntryInv DiscoYEntBodyStmt.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
#[local] Notation PI := (@PB_tfib rc).
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
Section h.
Variable B : asyms.

Definition dcro_of (Q : world SEGS -> (word -> option byte) -> Prop) : Prop :=
  AR_laws SEGS B -> d_ro_hyps (PI := PI) B ->
  forall ly S W m md, AR SEGS B ly S W m md ->
  arodata_okP SEGS (@pa_relro_lo _ _ PI) (@pa_relro_hi _ _ PI) B (aview SEGS (w_H W) m) -> Q W m.

Definition dcro_strs_stmt : Prop := dcro_of (fun W m => dimg_strs (PI := PI) W m /\ dimg_tj (PI := PI) W m).
Definition dcro_tjs_stmt : Prop := dcro_of (fun W m => rbn_img (PI := PI) W m /\ tjson_scalar_img (PI := PI) W m).
Definition dcro_ro_stmt : Prop := dcro_of (fun W m => dimg_ro (PI := PI) W m /\ dimg_rates (PI := PI) W m).
Definition dcro_hobs_stmt : Prop := dcro_of (fun W m => dimg_hobs (PI := PI) W m /\ dimg_verdict (PI := PI) W m).

Lemma dcro_compose :
  dcro_strs_stmt -> dcro_tjs_stmt -> dcro_ro_stmt -> dcro_hobs_stmt ->
  dimg_consts_of_ro_stmt (PI := PI) B.
Proof.
intros HS HT HR HH LAWS DRO ly S W m md HAR HOK.
destruct (HS LAWS DRO ly S W m md HAR HOK) as [S1 S2].
destruct (HT LAWS DRO ly S W m md HAR HOK) as [T1 T2].
destruct (HR LAWS DRO ly S W m md HAR HOK) as [R1 R2].
destruct (HH LAWS DRO ly S W m md HAR HOK) as [H1 H2].
unfold dimg_consts. tauto.
Qed.

End h.
End d.
