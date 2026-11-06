(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/YZ03.v and lib/Halts_tfib.v (the donor's asan-ubsan composition) for fuzz_manifest, in the form proofs/libreac/fuzz_decode/lib/A/AsanTop.v Section b states it; the image-B twin of lib/A/FMTop.v. *)
(* fuzz_manifest's two ASan+UBSan statements from the image-B ASan side TFIB_TB (lib/B/FMTfibTB.v):
   - asan_ubsan_agrees: shape_strong_equiv_efs_relim (Reusable/YM09.v) over the plain build's proved realization of
     SPECX at 2^34 (FMPlain.fm_plain_rz, at ag_shape checksum_shape, shared with image A), the statement's plain
     budget premise, TFIB_TB, and t_eq of the two SPECX (FMTop.SPECX_ag_t_eq: same LIBK);
   - asan_ubsan_halts: halts_budgets_of_srealizes (Reusable/HaltsKitB.v) over TFIB_TB, with exits 0 and 2 from
     ZTraceSpec.checksum_SPECX_exits_allowed (FMTop.SPECX_checksum_shape_ok).
   The plain side, the budget lemmas and the SPECX lemmas are image A's (lib/A/FMTop.v); only the image differs. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.omx_clap_core.fuzz_manifest Require Statements Images.
From OSSVerify.omx_clap_core.fuzz_manifest.images Require Plain AsanUbsan.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
  YK11 YK15 YK18 YM02 YM09 YO05 YO09 YO06 HaltsKitB.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest Require Import lib.Agree lib.AgreeShape lib.ZTraceSpec.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMPlain FMTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMTfibTB.
Import ListNotations.
Open Scope Z_scope.
#[local] Existing Instance YK11.fx0.

Section b.
Hypothesis TFIBB : TFIB_TB.

Theorem fm_asan_ubsan_agrees : Statements.asan_ubsan_agrees.
Proof.
  unfold Statements.asan_ubsan_agrees, agrees_in.
  intros en_s [sp' brk' mb' rnd'] inp Hens Hent Hinp SWB.
  pose proof (fm_plain_rz en_s inp Hens Hinp) as HP.
  destruct en_s as [sp brk mb rnd].
  pose proof (valid_input_va_size _ Hinp) as Hsv48.
  unfold Images.asan_ubsan in Hent.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent. destruct Hent as [Hsp' [Hbrk' [Hmb' Hfit']]].
  exact (shape_strong_equiv_efs_relim SanitizerBudgets.lim_source ShippedBudgets.lim_source SanitizerBudgets.lim_target
    Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs sp brk mb rnd
    tfibsegsB0 AsanUbsan.M.init_pc AsanUbsan.M.phdrs sp' brk' mb' rnd'
    (SPECX (LS:=ag_shape checksum_shape) inp) (SPECX (LS:=checksum_shape) inp) inp
    asan_lim_source_le SWB HP (TFIBB sp' brk' mb' rnd' inp Hsp' Hbrk' Hmb' Hfit' Hinp) (SPECX_ag_t_eq inp)).
Qed.

Theorem fm_asan_ubsan_halts : Statements.asan_ubsan_halts.
Proof.
  unfold Statements.asan_ubsan_halts, Images.asan_ubsan.
  change (halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source Exits.ok_or_refused
    (mkImage tfibsegsB0 AsanUbsan.M.init_pc AsanUbsan.M.phdrs)).
  apply (halts_budgets_of_srealizes forced_only_cfg Exits.ok_or_refused tfibsegsB0 AsanUbsan.M.init_pc
    AsanUbsan.M.phdrs target_alloc_limit ShippedBudgets.lim_source lim_source_le_target (forced_only_cfg_least _)).
  intros sp brk mb rnd inp Hen Hinp. exists (SPECX (LS:=checksum_shape) inp). split.
  - pose proof (valid_input_va_size _ Hinp) as Hsv48.
    rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hen. destruct Hen as [Hsp [Hbrk [Hmb Hfit]]].
    exact (TFIBB sp brk mb rnd inp Hsp Hbrk Hmb Hfit Hinp).
  - exact (SPECX_checksum_shape_ok inp).
Qed.
End b.

Theorem fm_asan_ubsan_agrees_of_tfib : TFIB_TB -> Statements.asan_ubsan_agrees.
Proof. exact fm_asan_ubsan_agrees. Qed.

Theorem fm_asan_ubsan_halts_of_tfib : TFIB_TB -> Statements.asan_ubsan_halts.
Proof. exact fm_asan_ubsan_halts. Qed.
