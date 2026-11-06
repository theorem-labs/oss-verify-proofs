(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the contract and walk of kind_of_link1 on fuzz_grant.asan, written for libreac/fuzz_grant: the entry seat, the walk loop and the return are adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v and proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v; the contract and the branch lemmas are new. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/KindOfLink1.v, with its module paths and module names changed; 58 of its 174 lines of code are new or changed and 53 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/KindOfLink1.v, with its module paths and module names changed; 28 of its 51 lines of code are new or changed and 151 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC44 YC8g YC8i.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YB1v YCbj YRo.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import CtrlParseCut.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require ClassifyCoreRom.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

Lemma cp_bcast_val0 : tfib_val0 (A_OBJ OBJ_BCAST) = 0x215a0.
Proof. vm_compute. reflexivity. Qed.

Lemma cp_bcast_glob : In (0x215a0, 7) tfib_globs.
Proof. unfold tfib_globs. repeat (first [left; reflexivity | right]). Qed.

Lemma cp_HG15_tfib : In (@pa_val _ lib_both3_0_listing PB_tfib (A_OBJ OBJ_BCAST), 7) tfib_globs.
Proof. cbn [pa_val PB_tfib]. rewrite cp_bcast_val0. exact cp_bcast_glob. Qed.

Lemma cp_HBC_RNG_tfib : YImgTop.IMG_LO + 64 <= @pa_val _ lib_both3_0_listing PB_tfib (A_OBJ OBJ_BCAST) /\
  @pa_val _ lib_both3_0_listing PB_tfib (A_OBJ OBJ_BCAST) + 6 + 64 <= YImgTop.IMG_TOP.
Proof. cbn [pa_val PB_tfib]. rewrite cp_bcast_val0. unfold YImgTop.IMG_LO, YImgTop.IMG_TOP. lia. Qed.

Lemma cp_HBC_VAL_tfib : forall B : asyms, tfib_ro_unowned B ->
  forall (H : word -> bool) mem,
  arodata_okP (@pa_segs _ lib_both3_0_listing PB_tfib) (@pa_relro_lo _ lib_both3_0_listing PB_tfib)
    (@pa_relro_hi _ lib_both3_0_listing PB_tfib) B (aview (@pa_segs _ lib_both3_0_listing PB_tfib) H mem) ->
  forall i, 0 <= i < 6 ->
  aview (@pa_segs _ lib_both3_0_listing PB_tfib) H mem (@pa_val _ lib_both3_0_listing PB_tfib (A_OBJ OBJ_BCAST) + i) = Some 255.
Proof.
intros B TRO H mem HR i Hi. cbn [pa_segs pa_val pa_relro_lo pa_relro_hi PB_tfib] in *. rewrite cp_bcast_val0.
assert (U : ro_unowned B 0x215a0 7).
{ apply tfib_ro_unowned_at; [exact TRO|]. unfold tfib_ro_ranges. apply in_or_app. left. exact cp_bcast_glob. }
assert (RS : ClassifyCoreRom.ro_span 0x215a0 (0x215a0 + 6) = true) by (vm_compute; reflexivity).
destruct (U (0x215a0 + i) ltac:(lia)) as [Ho He].
rewrite (HR (0x215a0 + i) (ClassifyCoreRom.ro_span_in _ _ _ _ RS (0x215a0 + i) ltac:(lia)) Ho He).
assert (Hc : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5) by lia.
destruct Hc as [ -> | [ -> | [ -> | [ -> | [ -> | -> ] ] ] ] ]; vm_compute; reflexivity.
Qed.
End d.
