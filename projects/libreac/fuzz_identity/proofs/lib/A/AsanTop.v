(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from projects/cgif/cgif_file_fuzzer/proofs/lib/A/AZ03.v and lib/Halts_tfib.v for fuzz_identity: the plain side is fuzz_identity's proved realization (built as its lib/AgreeFrame.v builds it, from lib/Prog/Seg/Agree.v plain_slot_ag, at identity_shape), the halting corollary takes srealizes, module paths changed. *)
(* fuzz_identity's two ASan statements from the ASan side TFIB_T (IdentityTFIB.v), in the form of
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AZ03.v (agreement) and lib/Halts_tfib.v (halting):
   - asan_agrees: shape_strong_equiv_efs_relim (Reusable/YM09.v) over the plain build's proved realization of SPECX
     at 2^34 (lib/PlainRz.v identity_plain_rz, from lib/AgreeTop.v plain_rz_of_contracts_R with the plain entry-function contract of the ubsan agreement,
     Prog/Seg/Agree.v plain_slot_ag, at identity_shape), the statement's plain budget premise, TFIB_T and t_eq_refl;
   - asan_halts: halts_budgets_of_srealizes (Reusable/HaltsKitB.v) over TFIB_T and SPECX_shape_ok (HaltsSpecI.v). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.libreac.fuzz_identity Require Statements Images.
From OSSVerify.libreac.fuzz_identity.images Require Plain Asan.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
  YK11 YK15 YK18 YM05 YM02 YM0b YM09 YO0i YO0f YO0g YO0x YO0d YO05 YO0j YO0m YO03 YO09 YO06 YO04 YO0o
  YH00 YH02 YI06 YI14 YI16 YI5b YI5c YL01 YL0g YL0i YL0k YL0s YL0j YN03 YN2b YN33 YP09 DriverSlots HaltsKitB.
(* Root copy ON PURPOSE (for ctrlgate): lib.ZImage / lib.ZTraceSpec are the PLAIN side's image and trace spec,
   which the agrees composition needs (plain_slot_ag / identity_plain_rz over Images.plain). The ASan side never takes the plain
   instances implicitly: the library shape is passed explicitly (identity_shape), the sink head explicitly with @, and the plain
   sink instances are removed from resolution (lib/A/Prog/SkGuardCheck.v, whose controls fire). *)
Require Import
  OSSVerify.Proofs.libreac.fuzz_identity.lib.ZImage
  OSSVerify.Proofs.libreac.fuzz_identity.lib.ZTraceSpec
  OSSVerify.Proofs.libreac.fuzz_identity.lib.AllocSlots
  OSSVerify.Proofs.libreac.fuzz_identity.lib.AllocRoom
  OSSVerify.Proofs.libreac.fuzz_identity.lib.ZComplete
  OSSVerify.Proofs.libreac.fuzz_identity.lib.ZAllocator
  OSSVerify.Proofs.libreac.fuzz_identity.lib.Contract
  OSSVerify.Proofs.libreac.fuzz_identity.lib.FrameAPI
  OSSVerify.Proofs.libreac.fuzz_identity.lib.FrameSlotG
  OSSVerify.Proofs.libreac.fuzz_identity.lib.FrameProof
  OSSVerify.Proofs.libreac.fuzz_identity.lib.SlotTopG
  OSSVerify.Proofs.libreac.fuzz_identity.lib.Agree
  OSSVerify.Proofs.libreac.fuzz_identity.lib.AgreeTop
  OSSVerify.Proofs.libreac.fuzz_identity.lib.AgreeZlib
  OSSVerify.Proofs.libreac.fuzz_identity.lib.SlotAgree.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.Seg Require Agree.
Module SAg := OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.Seg.Agree.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A Require Import IdentityTFIB HaltsSpecI.
From OSSVerify.Proofs.libreac.fuzz_identity.lib Require Import PlainRz.
Import ListNotations.
Open Scope Z_scope.
#[local] Existing Instance YK11.fx0.

Section a.
Hypothesis TFIB : TFIB_T.

Theorem identity_asan_agrees_of_tfib : Statements.asan_agrees.
Proof.
  unfold Statements.asan_agrees, agrees_in.
  intros en_s [sp' brk' mb' rnd'] inp Hens Hent Hinp SWB.
  pose proof (identity_plain_rz en_s inp Hens Hinp) as HP.
  destruct en_s as [sp brk mb rnd].
  pose proof (valid_input_va_size _ Hinp) as Hsv48.
  unfold Images.asan in Hent.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent. destruct Hent as [Hsp' [Hbrk' [Hmb' Hfit']]].
  exact (shape_strong_equiv_efs_relim SanitizerBudgets.lim_source ShippedBudgets.lim_source SanitizerBudgets.lim_target
    Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs sp brk mb rnd
    identsegs0 Asan.M.init_pc Asan.M.phdrs sp' brk' mb' rnd'
    (SPECX (LS:=identity_shape) inp) (SPECX (LS:=identity_shape) inp) inp
    asan_lim_source_le SWB HP (TFIB sp' brk' mb' rnd' inp Hsp' Hbrk' Hmb' Hfit' Hinp) (t_eq_refl _)).
Qed.

Theorem identity_asan_halts_of_tfib : Statements.asan_halts.
Proof.
  unfold Statements.asan_halts, Images.asan.
  change (halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source Exits.ok_or_refused
    (mkImage identsegs0 Asan.M.init_pc Asan.M.phdrs)).
  apply (halts_budgets_of_srealizes forced_only_cfg Exits.ok_or_refused identsegs0 Asan.M.init_pc Asan.M.phdrs
    target_alloc_limit ShippedBudgets.lim_source lim_source_le_target (forced_only_cfg_least _)).
  intros sp brk mb rnd inp Hen Hinp. exists (SPECX (LS:=identity_shape) inp). split.
  - pose proof (valid_input_va_size _ Hinp) as Hsv48.
    rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hen. destruct Hen as [Hsp [Hbrk [Hmb Hfit]]].
    exact (TFIB sp brk mb rnd inp Hsp Hbrk Hmb Hfit Hinp).
  - exact (SPECX_shape_ok inp).
Qed.
End a.
