(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: taken from an earlier draft of this file (not built there); for the build, Core
   Shapes is imported (agrees_in, as lib/A/AsanAgreesTop.v imports it), the plain realization preset_plain_rz is
   imported from its own file (lib/A/PresetPlainRz.v) and the budget lemma is proved here (the asan-ubsan twin of
   lib/A/AsanAgreesTop.v asan_lim_source_le), in place of importing the asan agreement top, which the draft imported
   as lib/A/AsanTop.v (in this tree that top is lib/A/AsanAgreesTop.v; lib/A/AsanTop.v is the asan_halts top). *)
(* fuzz_preset's asan_ubsan_agrees from the asan-ubsan side TFIB_T_AU (PresetTFIBAU.v), in the form of
   proofs/cgif/cgif_file_fuzzer/lib/YZ03.v:31-53 / YZ05.v (the donor's asan-ubsan agreement; its lib/A/AZ03.v is the
   asan twin) and of the released projects/libreac/fuzz_grant/proofs/lib/A/AsanTop.v:
   shape_strong_equiv_efs_relim (Reusable/YM09.v) over the plain build's proved realization of SPECX at 2^34
   (preset_plain_rz, lib/A/PresetPlainRz.v), the statement's plain budget premise (the 2^31 run is never refused, so by
   A/RelimCut.v the 2^34 one is cut-free), TFIB_T_AU (given the same premise, the unit owner's ruling of 2026-10-28
   20:25Z: the agrees TFIB takes the plain no-refusal premise at Budgets.Asan.lim_source and the top passes the
   statement's SWB) and t_eq_refl. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.omx_clap_core.fuzz_preset Require Statements Images.
From OSSVerify.omx_clap_core.fuzz_preset.images Require Plain AsanUbsan.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK15 YK18 YM09 YO06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require ZTraceSpec.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PresetPlainRz.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import PresetTFIBAU.
Import ListNotations.
Open Scope Z_scope.
#[local] Existing Instance YK11.fx0.

Lemma asan_ubsan_lim_source_le : SanitizerBudgets.lim_source <= ShippedBudgets.lim_source.
Proof. unfold SanitizerBudgets.lim_source, sanitizer_source_limit, ShippedBudgets.lim_source, source_alloc_limit. cbn. lia. Qed.

Section au.
Hypothesis TFIB_AU : TFIB_T_AU.

Theorem preset_asan_ubsan_agrees_of_tfib : Statements.asan_ubsan_agrees.
Proof.
  unfold Statements.asan_ubsan_agrees, agrees_in.
  intros en_s [sp' brk' mb' rnd'] inp Hens Hent Hinp SWB.
  pose proof (preset_plain_rz en_s inp Hens Hinp) as HP.
  pose proof (TFIB_AU sp' brk' mb' rnd' inp en_s) as HT.
  destruct en_s as [sp brk mb rnd].
  pose proof (valid_input_va_size _ Hinp) as Hsv48.
  unfold Images.asan_ubsan in Hent.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent. destruct Hent as [Hsp' [Hbrk' [Hmb' Hfit']]].
  exact (shape_strong_equiv_efs_relim SanitizerBudgets.lim_source ShippedBudgets.lim_source SanitizerBudgets.lim_target
    Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs sp brk mb rnd
    presetsegsAU AsanUbsan.M.init_pc AsanUbsan.M.phdrs sp' brk' mb' rnd'
    (SPECX (LS:=ZTraceSpec.checksum_shape) inp) (SPECX (LS:=ZTraceSpec.checksum_shape) inp) inp
    asan_ubsan_lim_source_le SWB HP (HT Hsp' Hbrk' Hmb' Hfit' Hinp SWB) (t_eq_refl _)).
Qed.
End au.
