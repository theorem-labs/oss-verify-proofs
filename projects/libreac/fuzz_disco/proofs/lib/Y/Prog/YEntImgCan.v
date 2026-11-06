(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_stamp_headamp on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACam.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACbf.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACf6.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v, with its module paths and module names changed; 419 of its 458 lines of code are new or changed and 1239 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/DiscoYEntProC.v; 21 of its 51 lines of code are new or changed and 428 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/YDcroParts.v; 15 of its 40 lines of code are new or changed and 26 lines of the source are left out. *)
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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YF0m YE2k YD1u YD2l YCbj.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import
disco_table_c disco_classify_c hunt_c SightModel reac_master_only_cadence_ns_c reac_rate_snap_c
reac_frame_clean_len_c slot_inv slot_frame reac_hunt_verdict_name_c disco_box_name_model.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import DiscoYEntryInv DiscoYEntBodyStmt.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section d. Context {rc : YM05.RunCeil}.
#[local] Notation PI := YCbj.PB_tfib.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).

Lemma de_kcan_tfib : ak_can_got YE2k.tfib_K = FF_got_canary /\ ak_canary YE2k.tfib_K = FF_canary.
Proof. split; reflexivity. Qed.

Lemma de_ail_of_syms : forall B, YF0m.TfibSyms B ->
  asink_img_laws (SK := YE2k.tfib_sink_head) SEGS B YE2k.tfib_K.
Proof. intros B HB. exact (YD1u.tfib_AIL B HB). Qed.

Lemma d_can_hyps_of_syms : forall B, YF0m.TfibSyms B ->
  d_can_hyps (SK := YE2k.tfib_sink_head) (PI := PI) B YE2k.tfib_K.
Proof. intros B HB. exact (conj (de_ail_of_syms B HB) (proj2 de_kcan_tfib)). Qed.

Lemma de_ail_tfib : asink_img_laws (SK := YE2k.tfib_sink_head) SEGS YD2l.TfibB YE2k.tfib_K.
Proof. exact (de_ail_of_syms YD2l.TfibB YD2l.TfibB_syms). Qed.

Lemma d_can_hyps_tfib : d_can_hyps (SK := YE2k.tfib_sink_head) (PI := PI) YD2l.TfibB YE2k.tfib_K.
Proof. exact (d_can_hyps_of_syms YD2l.TfibB YD2l.TfibB_syms). Qed.

End d.
