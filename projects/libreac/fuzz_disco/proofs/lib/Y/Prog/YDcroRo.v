(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_stamp_headamp on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACam.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACbf.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACf6.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v, with its module paths and module names changed; 733 of its 792 lines of code are new or changed and 1219 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/DiscoYEntR27.v, with its module paths changed; 545 of its 616 lines of code are new or changed and 721 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/DiscoYEntBody.v; 24 of its 49 lines of code are new or changed and 591 lines of the source are left out. *)
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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop YO0f.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YP0l YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC8i YC44 YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC1i YCbf YCj1 YCja YCjr YRo.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YB1v YXcalls YCbj.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import
disco_table_c disco_classify_c hunt_c SightModel reac_master_only_cadence_ns_c reac_rate_snap_c
reac_frame_clean_len_c slot_inv slot_frame reac_hunt_verdict_name_c disco_box_name_model.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import DiscoYEntryInv DiscoYEntBodyStmt.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import YDcroParts YDcroLib.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section s. Context {rc : YM05.RunCeil}. Context {SK : YI16.sink_head}.
Variable B : asyms.

Theorem dcro_ro : dcro_ro_stmt B.
Proof.
unfold dcro_ro_stmt, dcro_of. intros LAWS DRO ly S W m md HAR HOK.
destruct DRO as (DRU & GM & HV).
assert (CTX : dro_ctx B ly S W m md).
{ unfold dro_ctx. split; [exact HAR|]. split; [exact HOK|]. split; [exact DRU|]. split; [exact GM | exact HV]. }
pose proof (d_word_b B ly S W m md CTX) as MKW.
pose proof (d_garr8_b B ly S W m md CTX) as MKG.
unfold dimg_ro, dimg_rates.
rewrite !(d_val_obj 26%nat 0xa06a0 ltac:(lia) eq_refl), !(d_val_obj 27%nat 0x21220 ltac:(lia) eq_refl),
  !(d_val_obj 20%nat 0xa0660 ltac:(lia) eq_refl), !(d_val_obj 15%nat 0x21000 ltac:(lia) eq_refl),
  !(d_val_obj 16%nat 0x21020 ltac:(lia) eq_refl), !(d_val_obj 19%nat 0x21120 ltac:(lia) eq_refl),
  !(d_val_obj 28%nat 0x21240 ltac:(lia) eq_refl), !(d_val_obj 29%nat 0x21260 ltac:(lia) eq_refl),
  !(d_val_obj 30%nat 0x21280 ltac:(lia) eq_refl), !(d_val_obj 65%nat 0x21680 ltac:(lia) eq_refl),
  !(d_val_hi 99%nat 0xfcc8 eq_refl), !(d_val_hi 98%nat 0xfcc4 eq_refl).
repeat match goal with |- _ /\ _ => split end.
1-6, 22-23: apply MKW; vm_compute; reflexivity.
1-14: apply d_rom_b; vm_compute; reflexivity.
apply MKG; vm_compute; reflexivity.
Qed.

End s.
