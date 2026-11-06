(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_stamp_headamp on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACam.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACbf.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACf6.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v, with its module paths and module names changed; 733 of its 792 lines of code are new or changed and 1219 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/DiscoYEntR27.v, with its module paths changed; 545 of its 616 lines of code are new or changed and 721 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/DiscoYEntBody.v; 53 of its 78 lines of code are new or changed and 591 lines of the source are left out. *)
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

Theorem dcro_strs : dcro_strs_stmt B.
Proof.
unfold dcro_strs_stmt, dcro_of. intros LAWS DRO ly S W m md HAR HOK.
destruct DRO as (DRU & GM & HV).
assert (CTX : dro_ctx B ly S W m md).
{ unfold dro_ctx. split; [exact HAR|]. split; [exact HOK|]. split; [exact DRU|]. split; [exact GM | exact HV]. }
pose proof (d_rostr_of B ly S W m md CTX) as MK.
pose proof (d_word_b B ly S W m md CTX) as MKW.
pose proof (d_rbn_stem_of B ly S W m md CTX) as MKS.
pose proof (d_rbn_lit_of B ly S W m md CTX) as MKL.
pose proof (d_rdok_b B ly S W m md CTX) as MKR.
split.
- unfold dimg_strs.
  rewrite !(d_val_obj 4%nat 0x21060 ltac:(lia) eq_refl), !(d_val_obj 5%nat 0x21080 ltac:(lia) eq_refl),
    !(d_val_obj 6%nat 0x210a0 ltac:(lia) eq_refl), !(d_val_obj 7%nat 0x210c0 ltac:(lia) eq_refl),
    !(d_val_obj 8%nat 0x210e0 ltac:(lia) eq_refl), !(d_val_obj 9%nat 0x21100 ltac:(lia) eq_refl),
    !(d_val_obj 10%nat 0x20f80 ltac:(lia) eq_refl), !(d_val_obj 11%nat 0x20fc0 ltac:(lia) eq_refl),
    !(d_val_obj 66%nat 0x21180 ltac:(lia) eq_refl), !(d_val_obj 67%nat 0x21160 ltac:(lia) eq_refl),
    !(d_val_obj 14%nat 0x20fe0 ltac:(lia) eq_refl), !(d_val_obj 15%nat 0x21000 ltac:(lia) eq_refl),
    !(d_val_obj 16%nat 0x21020 ltac:(lia) eq_refl), !(d_val_obj 18%nat 0x21040 ltac:(lia) eq_refl),
    !(d_val_obj 17%nat 0x10370 ltac:(lia) eq_refl).
  repeat (split; [apply MK; vm_compute; reflexivity|]).
  split; [apply MKW; vm_compute; reflexivity | apply d_rom_b; vm_compute; reflexivity].
- unfold dimg_tj.
  rewrite !(d_val_obj 39%nat 0x21340 ltac:(lia) eq_refl), !(d_val_obj 40%nat 0x213c0 ltac:(lia) eq_refl),
    !(d_val_obj 41%nat 0x213e0 ltac:(lia) eq_refl), !(d_val_obj 42%nat 0x21360 ltac:(lia) eq_refl),
    !(d_val_obj 43%nat 0x21320 ltac:(lia) eq_refl), !(d_val_obj 44%nat 0x21300 ltac:(lia) eq_refl),
    !(d_val_obj 45%nat 0x212e0 ltac:(lia) eq_refl), !(d_val_obj 46%nat 0x21400 ltac:(lia) eq_refl),
    !(d_val_obj 47%nat 0x21480 ltac:(lia) eq_refl), !(d_val_obj 48%nat 0x214c0 ltac:(lia) eq_refl),
    !(d_val_obj 49%nat 0x21420 ltac:(lia) eq_refl), !(d_val_obj 50%nat 0x21440 ltac:(lia) eq_refl),
    !(d_val_obj 51%nat 0x21500 ltac:(lia) eq_refl), !(d_val_obj 52%nat 0x21520 ltac:(lia) eq_refl),
    !(d_val_obj 53%nat 0x214e0 ltac:(lia) eq_refl), !(d_val_obj 54%nat 0x21540 ltac:(lia) eq_refl),
    !(d_val_obj 55%nat 0x21560 ltac:(lia) eq_refl), !(d_val_obj 17%nat 0x10370 ltac:(lia) eq_refl).
  split.
  + unfold rbn_img.
    rewrite !(d_val_obj 26%nat 0xa06a0 ltac:(lia) eq_refl), !(d_val_obj 27%nat 0x21220 ltac:(lia) eq_refl),
      !(d_val_obj 28%nat 0x21240 ltac:(lia) eq_refl), !(d_val_obj 29%nat 0x21260 ltac:(lia) eq_refl),
      !(d_val_obj 30%nat 0x21280 ltac:(lia) eq_refl).
    exists 0x211c0, 0x211e0, 0x21200.
    split; [reflexivity|].
    split; [exact (d_in_img_b 0xa06a0 24 ltac:(vm_compute; reflexivity))|].
    split; [exact (proj1 (MKR 0xa06a0 24 ltac:(vm_compute; reflexivity)))|].
    do 3 (split; [apply MKW; vm_compute; reflexivity|]).
    do 4 (split; [apply MKS; vm_compute; reflexivity|]).
    do 2 (split; [apply MKL; vm_compute; reflexivity|]).
    apply MKL; vm_compute; reflexivity.
  + repeat (split; [apply MK; vm_compute; reflexivity|]).
    split; [apply MKW; vm_compute; reflexivity | apply d_rom_b; vm_compute; reflexivity].
Qed.

End s.
