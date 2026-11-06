(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/A/AZ03.v for fuzz_preset: the plain side is fuzz_preset's proved realization (A/PresetPlainRz.v, built as its lib/AgreePresetH.v and lib/Theorems.v build the plain side of the ubsan agreement, at checksum_shape), TFIB_T takes the statement's plain no-refusal premise (PresetTFIB.v), module paths changed. *)
(* fuzz_preset's ASan agreement from the ASan side TFIB_T (PresetTFIB.v), in the form of
   proofs/cgif/cgif_file_fuzzer/lib/A/AZ03.v: shape_strong_equiv_efs_relim (Reusable/YM09.v) over the plain build's
   proved realization of SPECX at 2^34 (A/PresetPlainRz.v preset_plain_rz: lib/AgreeTop.v plain_rz_of_contracts_R
   with the proved plain HALTS slot AgreePresetH.preset_plain_halts_slot, at checksum_shape), the statement's plain
   budget premise, TFIB_T (given the same premise) and t_eq_refl.
   The plain side is used only AT 2^34: plain_rz_of_contracts_R is fuzz_preset's released theorem at
   Budgets.Standard.lim_source = 2^34, where it discharges src0_realizes_specX's premise SRC_LIM_MIN <= lim with
   SRC_LIM_MIN_le_source (Reusable/YM0b.v:10, SRC_LIM_MIN = 2^34). A/RelimCut.v carries it down to the statement's
   2 GiB premise: a budget refusal at the larger limit is one at the smaller limit, so a plain run never refused at
   2^31 is cut-free at 2^34 (cut_free_of_relim), and YM09.v moves the agreement from 2^34 to 2^31
   (sefb_relim_source). Nothing in this file uses the plain side below 2^34. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.omx_clap_core.fuzz_preset Require Statements Images.
From OSSVerify.omx_clap_core.fuzz_preset.images Require Plain Asan.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
  YK11 YK15 YK18 YM05 YM0b YM09 YO09 YO06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PresetPlainRz PresetTFIB.
Import ListNotations.
Open Scope Z_scope.
#[local] Existing Instance YK11.fx0.

Lemma asan_lim_source_le : SanitizerBudgets.lim_source <= ShippedBudgets.lim_source.
Proof. unfold SanitizerBudgets.lim_source, sanitizer_source_limit, ShippedBudgets.lim_source, source_alloc_limit. cbn. lia. Qed.

Section a.
Hypothesis TFIB : TFIB_T.

Theorem preset_asan_agrees_of_tfib : Statements.asan_agrees.
Proof.
  unfold Statements.asan_agrees, agrees_in.
  intros en_s [sp' brk' mb' rnd'] inp Hens Hent Hinp SWB.
  pose proof (preset_plain_rz en_s inp Hens Hinp) as HP.
  destruct en_s as [sp brk mb rnd].
  pose proof (valid_input_va_size _ Hinp) as Hsv48.
  unfold Images.asan in Hent.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent. destruct Hent as [Hsp' [Hbrk' [Hmb' Hfit']]].
  exact (shape_strong_equiv_efs_relim SanitizerBudgets.lim_source ShippedBudgets.lim_source SanitizerBudgets.lim_target
    Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs sp brk mb rnd
    presetsegs0 Asan.M.init_pc Asan.M.phdrs sp' brk' mb' rnd'
    (SPECX (LS:=checksum_shape) inp) (SPECX (LS:=checksum_shape) inp) inp
    asan_lim_source_le SWB HP
    (TFIB sp' brk' mb' rnd' inp (mkEntry sp brk mb rnd) Hsp' Hbrk' Hmb' Hfit' Hinp SWB) (t_eq_refl _)).
Qed.
End a.
