(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/YZ03.v and lib/Halts_tfib.v (through a Theorem Labs lane's proofs/libreac/fuzz_grant/lib/A/AsanTop.v, a working branch 0bed23e5b69, and its fuzz_ctrl image-A twin lib/A/AsanTop.v) for fuzz_ctrl's ASan+UBSan image: the plain side is fuzz_ctrl's proved realization (A/CtrlPlainRz.v, at ag_shape checksum_shape), the halting corollary takes srealizes, module paths changed. *)
(* fuzz_ctrl's two ASan+UBSan statements from the ASan+UBSan side TFIB_T_B (CtrlTFIB_B.v), in the form of
   projects/cgif/cgif_file_fuzzer/proofs/lib/YZ03.v (agreement) and lib/Halts_tfib.v (halting):
   - asan_ubsan_agrees: shape_strong_equiv_efs_relim (Reusable/YM09.v) over the plain build's proved realization of SPECX
     at 2^34 (A/CtrlPlainRz.v ctrl_plain_rz: lib/AgreeTop.v plain_rz_of_contracts_R over the closed plain slot of the ubsan
     agreement, Prog/Seg/Slot.v slot_of_lemmas, at ag_shape checksum_shape), the statement's plain budget premise, TFIB_T_B and t_eq_refl;
   - asan_ubsan_halts: halts_budgets_of_srealizes (Reusable/HaltsKitB.v) over TFIB_T_B and SPECX_shape_ok (A/HaltsSpecC.v,
     which names no image). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.libreac.fuzz_ctrl Require Statements Images.
From OSSVerify.libreac.fuzz_ctrl.images Require Plain AsanUbsan.
(* The core copies (lib.Reusable.X, lib.X), by full path: lib/B and lib/B/Reusable hold image B's copies of many of
   these, and the theorems this file applies (A/CtrlPlainRz.v, Reusable/YM09.v, Reusable/HaltsKitB.v, A/HaltsSpecC.v,
   B/CtrlTFIB_B.v) are stated over the core copies. *)
Require Import
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK15
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK18
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM02
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM0b
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM09
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO0i
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO0f
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO0g
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO0x
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO0d
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO05
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO0j
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO0m
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO03
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO06
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO04
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO0o
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YH00
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YH02
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI06
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI14
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI16
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI5b
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI5c
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YL01
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YL0g
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YL0i
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YL0k
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YL0s
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YL0j
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YN03
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YN2b
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YN33
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YP09
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.DriverSlots
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.HaltsKitB.
Require Import
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.ZImage
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.ZTraceSpec
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.AllocSlots
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.AllocRoom
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.ZComplete
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.ZAllocator
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Contract
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.FrameAPI
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.FrameSlotG
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.FrameProof
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.SlotTopG
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Agree
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.AgreeTop
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.AgreeZlib
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.AgreeShape
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.SlotAgree.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import CtrlPlainRz HaltsSpecC.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import CtrlTFIB_B.
(* Modified by Theorem Labs, 2026-10: the plain build's sink instances (Reusable/YI5b.v, YI5c.v, Required above for the plain side) and their ubsan copies (U/Reusable/YI5b.v, YI5c.v, loaded here through AgreeShape) are removed from instance search (#[global]: also for every file that loads this one), so a sink instance left implicit in an ASan composition here cannot be found; full paths, because both copies are loaded here (a Theorem Labs lane step 3; fuzz_boxreg's form, a working branch 12834cac4ca lib/A/Prog/BoxPa.v:21). *)
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI5b OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI5c OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable.YI5b OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable.YI5c.
#[global] Remove Hints OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI5b.src0_sink_head OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI5c.src0_sink OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI5c.src0_sink_laws OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable.YI5b.src0_sink_head OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable.YI5c.src0_sink OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable.YI5c.src0_sink_laws : typeclass_instances.
Import ListNotations.
Open Scope Z_scope.
#[local] Existing Instance YK11.fx0.

Lemma asan_lim_source_le_b : SanitizerBudgets.lim_source <= ShippedBudgets.lim_source.
Proof. unfold SanitizerBudgets.lim_source, sanitizer_source_limit, ShippedBudgets.lim_source, source_alloc_limit. cbn. lia. Qed.

Lemma lim_source_le_target_b : ShippedBudgets.lim_source <= target_alloc_limit.
Proof. unfold ShippedBudgets.lim_source, source_alloc_limit, target_alloc_limit. cbn. lia. Qed.

Section b.
Hypothesis TFIB : TFIB_T_B.

Theorem ctrl_asan_ubsan_agrees_of_tfib : Statements.asan_ubsan_agrees.
Proof.
  unfold Statements.asan_ubsan_agrees, agrees_in.
  intros en_s [sp' brk' mb' rnd'] inp Hens Hent Hinp SWB.
  pose proof (ctrl_plain_rz en_s inp Hens Hinp) as HP.
  destruct en_s as [sp brk mb rnd].
  pose proof (valid_input_va_size _ Hinp) as Hsv48.
  unfold Images.asan_ubsan in Hent.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent. destruct Hent as [Hsp' [Hbrk' [Hmb' Hfit']]].
  exact (shape_strong_equiv_efs_relim SanitizerBudgets.lim_source ShippedBudgets.lim_source SanitizerBudgets.lim_target
    Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs sp brk mb rnd
    ctrlsegs0_b AsanUbsan.M.init_pc AsanUbsan.M.phdrs sp' brk' mb' rnd'
    (SPECX (LS:=ag_shape checksum_shape) inp) (SPECX (LS:=ag_shape checksum_shape) inp) inp
    asan_lim_source_le_b SWB HP (TFIB sp' brk' mb' rnd' inp Hsp' Hbrk' Hmb' Hfit' Hinp) (t_eq_refl _)).
Qed.

Theorem ctrl_asan_ubsan_halts_of_tfib : Statements.asan_ubsan_halts.
Proof.
  unfold Statements.asan_ubsan_halts, Images.asan_ubsan.
  change (halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source Exits.ok_or_refused
    (mkImage ctrlsegs0_b AsanUbsan.M.init_pc AsanUbsan.M.phdrs)).
  apply (halts_budgets_of_srealizes forced_only_cfg Exits.ok_or_refused ctrlsegs0_b AsanUbsan.M.init_pc
    AsanUbsan.M.phdrs target_alloc_limit ShippedBudgets.lim_source lim_source_le_target_b (forced_only_cfg_least _)).
  intros sp brk mb rnd inp Hen Hinp. exists (SPECX (LS:=ag_shape checksum_shape) inp). split.
  - pose proof (valid_input_va_size _ Hinp) as Hsv48.
    rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hen. destruct Hen as [Hsp [Hbrk [Hmb Hfit]]].
    exact (TFIB sp brk mb rnd inp Hsp Hbrk Hmb Hfit Hinp).
  - exact (SPECX_shape_ok inp).
Qed.
End b.
