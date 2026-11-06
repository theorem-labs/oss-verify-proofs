(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the contract and walk of kind_of_link1 on fuzz_grant.asan, written for libreac/fuzz_grant: the entry seat, the walk loop and the return are adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v and proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v; the contract and the branch lemmas are new. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/KindOfLink1.v, with its module paths and module names changed; 58 of its 174 lines of code are new or changed and 53 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/KindOfLink1.v, with its module paths and module names changed; 70 of its 100 lines of code are new or changed and 144 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/DiscoYEntExitPostPf.v, with its module paths and module names changed; 35 of its 60 lines of code are new or changed and 75 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YB1v YD2l YXcalls YCbj.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YRoClose.
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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import DiscoYEntryInv DiscoYEntBodyStmt.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Rt Require Import SnprintfConsts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import DiscoYEntryShapes.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Lemma tfib_snp_cr_free_b : forallb (YRoClose.ro_range_b TfibB) snp_cr = true.
Proof. vm_compute. reflexivity. Qed.

Lemma tfib_de_snp_un : forall a, Exists (in_zr a) snp_cr ->
  ~ Exists (in_zr a) (as_owned_static TfibB) /\ ~ (as_errno TfibB <= a < as_errno TfibB + 4).
Proof.
intros a Ha. apply Exists_exists in Ha as ([lo n] & Hr & Ha).
pose proof (proj1 (Forall_forall _ _) (YRoClose.ro_unowned_of_b TfibB snp_cr tfib_snp_cr_free_b) (lo, n) Hr) as U.
cbn [fst snd] in U. unfold in_zr in Ha. cbn [fst snd] in Ha. exact (U a Ha).
Qed.

Lemma tfib_de_mc_un : forall a, MC_CONSTS_LO <= a < MC_CONSTS_HI ->
  ~ Exists (in_zr a) (as_owned_static TfibB) /\ ~ (as_errno TfibB <= a < as_errno TfibB + 4).
Proof.
intros a Ha.
assert (HIN : In (0x10368, 32) tfib_ro_ranges).
{ unfold tfib_ro_ranges. apply in_or_app. right. unfold tfib_ro_extra. cbn [In].
  repeat (first [left; reflexivity | right]). }
apply (tfib_ro_unowned_at TfibB 0x10368 32 YRoClose.tfib_ro_unowned_tfib HIN a).
unfold MC_CONSTS_LO, MC_CONSTS_HI in Ha. lia.
Qed.

Section r. Context {rc : YM05.RunCeil}.
#[local] Notation PI := PB_tfib.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).

Lemma tfib_de_snp_ro : forall a, Exists (in_zr a) snp_cr ->
  in_roP SEGS (@pa_relro_lo _ lib_both3_0_listing PI) (@pa_relro_hi _ lib_both3_0_listing PI) a.
Proof. intros a Ha. left. exact (snp_cr_in_rom a Ha). Qed.

Lemma tfib_de_mc_ro : forall a, MC_CONSTS_LO <= a < MC_CONSTS_HI ->
  in_roP SEGS (@pa_relro_lo _ lib_both3_0_listing PI) (@pa_relro_hi _ lib_both3_0_listing PI) a.
Proof.
intros a Ha. apply tfib_de_snp_ro. apply Exists_exists. exists (0x10368, 32). split.
- unfold snp_cr. cbn [In]. repeat (first [left; reflexivity | right]).
- unfold in_zr, MC_CONSTS_LO, MC_CONSTS_HI in *. cbn [fst snd]. lia.
Qed.

Lemma tfib_d_ro_hyps : d_ro_hyps (PI := PI) TfibB.
Proof. exact YRoClose.tfib_ro_hyps. Qed.
End r.
