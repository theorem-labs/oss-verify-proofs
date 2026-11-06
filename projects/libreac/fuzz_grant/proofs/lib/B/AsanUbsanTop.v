(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/YZ03.v (agreement) and lib/Halts_tfib.v (halting), cgif_file's ASan+UBSan route, for fuzz_grant, by way of fuzz_grant's lib/A/AsanTop.v and Section b of fuzz_decode's lib/A/AsanTop.v: the plain side, the budget lemmas and the source re-limit kit are those of lib/A/AsanTop.v, the halting corollary takes srealizes, module paths changed. *)
(* Modified by Theorem Labs, 2026-10: moved from lib/A/AsanUbsanTop.v (a working branch b01a93fbf7f) to lib/B, so that lib/A stays grant image A's accepted tree; module path lib.A -> lib.B, and its Require of GrantTFIBB with it. *)
(* fuzz_grant's two ASan+UBSan statements from the ASan+UBSan side TFIB_TB (GrantTFIBB.v), in the form of lib/A/AsanTop.v
   for the ASan statements:
   - asan_ubsan_agrees: shape_strong_equiv_efs_relim (Reusable/YM09.v, with Reusable/RelimCut.v) over the plain build's
     proved realization of SPECX at 2^34 (AsanTop.v grant_plain_rz), the statement's plain budget premise, TFIB_TB and
     t_eq_refl;
   - asan_ubsan_halts: halts_budgets_of_srealizes (Reusable/HaltsKitB.v) over TFIB_TB and SPECX_shape_ok
     (HaltsSpecG.v). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.libreac.fuzz_grant Require Statements Images.
From OSSVerify.libreac.fuzz_grant.images Require Plain AsanUbsan.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YK15 YK18 YM05 YM09 YO09 YO06 HaltsKitB.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A Require Import GrantShape.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import GrantTFIBB.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A Require Import HaltsSpecG AsanTop.
Import ListNotations.
Open Scope Z_scope.
#[local] Existing Instance YK11.fx0.

Section b.
Hypothesis TFIBB : TFIB_TB.

Theorem grant_asan_ubsan_agrees_of_tfib : Statements.asan_ubsan_agrees.
Proof.
  unfold Statements.asan_ubsan_agrees, agrees_in.
  intros en_s [sp' brk' mb' rnd'] inp Hens Hent Hinp SWB.
  pose proof (grant_plain_rz en_s inp Hens Hinp) as HP.
  destruct en_s as [sp brk mb rnd].
  pose proof (valid_input_va_size _ Hinp) as Hsv48.
  unfold Images.asan_ubsan in Hent.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent. destruct Hent as [Hsp' [Hbrk' [Hmb' Hfit']]].
  exact (shape_strong_equiv_efs_relim SanitizerBudgets.lim_source ShippedBudgets.lim_source SanitizerBudgets.lim_target
    Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs sp brk mb rnd
    grantsegsB0 AsanUbsan.M.init_pc AsanUbsan.M.phdrs sp' brk' mb' rnd'
    (SPECX (LS:=grant_shape) inp) (SPECX (LS:=grant_shape) inp) inp
    asan_lim_source_le SWB HP (TFIBB sp' brk' mb' rnd' inp Hsp' Hbrk' Hmb' Hfit' Hinp) (t_eq_refl _)).
Qed.

Theorem grant_asan_ubsan_halts_of_tfib : Statements.asan_ubsan_halts.
Proof.
  unfold Statements.asan_ubsan_halts, Images.asan_ubsan.
  change (halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source Exits.ok_or_refused
    (mkImage grantsegsB0 AsanUbsan.M.init_pc AsanUbsan.M.phdrs)).
  apply (halts_budgets_of_srealizes forced_only_cfg Exits.ok_or_refused grantsegsB0 AsanUbsan.M.init_pc
    AsanUbsan.M.phdrs target_alloc_limit ShippedBudgets.lim_source lim_source_le_target (forced_only_cfg_least _)).
  intros sp brk mb rnd inp Hen Hinp. exists (SPECX (LS:=grant_shape) inp). split.
  - pose proof (valid_input_va_size _ Hinp) as Hsv48.
    rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hen. destruct Hen as [Hsp [Hbrk [Hmb Hfit]]].
    exact (TFIBB sp brk mb rnd inp Hsp Hbrk Hmb Hfit Hinp).
  - exact (SPECX_shape_ok inp).
Qed.
End b.
