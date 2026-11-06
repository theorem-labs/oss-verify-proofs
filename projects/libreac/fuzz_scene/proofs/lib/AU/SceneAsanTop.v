(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/A/AZ03.v (and its fuzz_grant form,
   a working branch's lib/A/AsanTop.v) for fuzz_scene's asan-ubsan image: the plain side is fuzz_scene's released
   realization (lib/SceneAsanBase.v), module paths changed. Split out of lib/A/SceneAsanTop.v (2026-10-29): the text
   below is that file's asan-ubsan half, unchanged. *)
(* fuzz_scene's asan_ubsan_agrees and asan_ubsan_halts, from ONE ASan-side obligation, in the form of
   proofs/cgif/cgif_file_fuzzer/lib/A/AZ03.v:
   - ASAN_UBSAN_T: from every valid start, the ASan+UBSan build realizes, with no cut (Reusable/YK18.v srealizes),
     the trace set SPECX at the shape of the released agreement (AZ03.v:20-26 TFIB_T);
   - the plain side is the released plain realization of SPECX at 2^34 (lib/SceneAsanBase.v scene_plain_rz), used
     unchanged;
   - shape_strong_equiv_efs_relim (Reusable/YM09.v) brings the plain side down to the statements' 2^31 plain budget,
     whose premise gives the plain run's cut-freedom (lib/RelimCut.v).
   This file Requires nothing from lib/A and no asan image module. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.libreac.fuzz_scene Require Statements Images.
From OSSVerify.libreac.fuzz_scene.images Require Plain AsanUbsan.
From OSSVerify.Proofs.libreac.fuzz_scene.lib Require AgreeScene.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
  YK11 YK15 YK18 YM05 YM02 YM0b YM09 YO0i YO0f YO0g YO0x YO0d YO05 YO0j YO0m YO03 YO09 YO06 YO04 YO0o
  YH00 YH02 YI06 YI14 YI16 YI5b YI5c YL01 YL0g YL0i YL0k YL0s YL0j YN03 YN2b YN33 YP09 DriverSlots HaltsKitB.
From OSSVerify.Proofs.libreac.fuzz_scene.lib Require Import
  ZImage ZTraceSpec AllocSlots AllocRoom ZComplete ZAllocator Contract FrameAPI FrameSlotG
  Agree AgreeTop AgreeZlib AgreeShape.
From OSSVerify.Proofs.libreac.fuzz_scene.lib Require Import HaltsSpecS SceneAsanBase.
Import ListNotations.
Open Scope Z_scope.
#[local] Existing Instance YK11.fx0.

Definition ASAN_UBSAN_T : Prop :=
  forall sp brk mbase rnd inp,
  valid_sp sp -> valid_brk AsanUbsan.M.loaded_segments brk -> valid_mmap_base mbase ->
  entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
  srealizes AsanUbsan.M.loaded_segments
    (init_config AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs sp brk mbase rnd
       target_alloc_limit inp)
    (SPECX (LS:=scene_shape) inp).

Theorem asan_ubsan_agrees_of_asan_side : ASAN_UBSAN_T -> Statements.asan_ubsan_agrees.
Proof.
  intros TFIB. unfold Statements.asan_ubsan_agrees, agrees_in.
  intros en_s [sp' brk' mb' rnd'] inp Hens Hent Hinp SWB.
  pose proof (scene_plain_rz en_s inp Hens Hinp) as HP.
  destruct en_s as [sp brk mb rnd].
  pose proof (valid_input_va_size _ Hinp) as Hsv48.
  unfold Images.asan_ubsan in Hent.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent. destruct Hent as [Hsp' [Hbrk' [Hmb' Hfit']]].
  exact (shape_strong_equiv_efs_relim SanitizerBudgets.lim_source ShippedBudgets.lim_source SanitizerBudgets.lim_target
    Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs sp brk mb rnd
    AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs sp' brk' mb' rnd'
    (SPECX (LS:=scene_shape) inp) (SPECX (LS:=scene_shape) inp) inp
    asan_lim_source_le SWB HP (TFIB sp' brk' mb' rnd' inp Hsp' Hbrk' Hmb' Hfit' Hinp) (t_eq_refl _)).
Qed.

(* The halting statement (Budgets.Standard.lim_source) from the same obligation, as cgif_file_fuzzer's
   lib/Halts_tfib.v does: halts_budgets_of_srealizes (Reusable/HaltsKitB.v) over ASAN_UBSAN_T and SPECX_shape_ok
   (lib/HaltsSpecS.v). *)
Theorem asan_ubsan_halts_of_asan_side : ASAN_UBSAN_T -> Statements.asan_ubsan_halts.
Proof.
  intros TFIB. unfold Statements.asan_ubsan_halts, Images.asan_ubsan.
  change (halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source Exits.ok_or_refused
    (mkImage AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs)).
  apply (halts_budgets_of_srealizes forced_only_cfg Exits.ok_or_refused AsanUbsan.M.loaded_segments
    AsanUbsan.M.init_pc AsanUbsan.M.phdrs target_alloc_limit ShippedBudgets.lim_source lim_source_le_target
    (forced_only_cfg_least _)).
  intros sp brk mb rnd inp Hen Hinp. exists (SPECX (LS:=scene_shape) inp). split.
  - pose proof (valid_input_va_size _ Hinp) as Hsv48.
    rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hen. destruct Hen as [Hsp [Hbrk [Hmb Hfit]]].
    exact (TFIB sp brk mb rnd inp Hsp Hbrk Hmb Hfit Hinp).
  - exact (SPECX_shape_ok inp).
Qed.

Print Assumptions asan_ubsan_agrees_of_asan_side.
Print Assumptions asan_ubsan_halts_of_asan_side.
