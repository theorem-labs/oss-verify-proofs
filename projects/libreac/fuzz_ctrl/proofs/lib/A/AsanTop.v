(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/A/AZ03.v and lib/Halts_tfib.v (through a Theorem Labs lane's proofs/libreac/fuzz_grant/lib/A/AsanTop.v, a working branch 0bed23e5b69) for fuzz_ctrl: the plain side is fuzz_ctrl's proved realization (A/CtrlPlainRz.v, at ag_shape checksum_shape), the halting corollary takes srealizes, module paths changed. *)
(* fuzz_ctrl's two ASan statements from the ASan side TFIB_T (CtrlTFIB.v), in the form of
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AZ03.v (agreement) and lib/Halts_tfib.v (halting):
   - asan_agrees: shape_strong_equiv_efs_relim (Reusable/YM09.v) over the plain build's proved realization of SPECX
     at 2^34 (A/CtrlPlainRz.v ctrl_plain_rz: lib/AgreeTop.v plain_rz_of_contracts_R over the closed plain slot of the ubsan
     agreement, Prog/Seg/Slot.v slot_of_lemmas, at ag_shape checksum_shape), the statement's plain budget premise, TFIB_T and t_eq_refl;
   - asan_halts: halts_budgets_of_srealizes (Reusable/HaltsKitB.v) over TFIB_T and SPECX_shape_ok (HaltsSpecC.v). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.libreac.fuzz_ctrl Require Statements Images.
From OSSVerify.libreac.fuzz_ctrl.images Require Plain Asan.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import
  YK11 YK15 YK18 YM05 YM02 YM0b YM09 YO0i YO0f YO0g YO0x YO0d YO05 YO0j YO0m YO03 YO09 YO06 YO04 YO0o
  YH00 YH02 YI06 YI14 YI16 YI5b YI5c YL01 YL0g YL0i YL0k YL0s YL0j YN03 YN2b YN33 YP09 DriverSlots HaltsKitB.
From OSSVerify Require Import
  Proofs.libreac.fuzz_ctrl.lib.ZImage Proofs.libreac.fuzz_ctrl.lib.ZTraceSpec Proofs.libreac.fuzz_ctrl.lib.AllocSlots Proofs.libreac.fuzz_ctrl.lib.AllocRoom Proofs.libreac.fuzz_ctrl.lib.ZComplete Proofs.libreac.fuzz_ctrl.lib.ZAllocator Proofs.libreac.fuzz_ctrl.lib.Contract Proofs.libreac.fuzz_ctrl.lib.FrameAPI Proofs.libreac.fuzz_ctrl.lib.FrameSlotG Proofs.libreac.fuzz_ctrl.lib.FrameProof Proofs.libreac.fuzz_ctrl.lib.SlotTopG
  Proofs.libreac.fuzz_ctrl.lib.Agree Proofs.libreac.fuzz_ctrl.lib.AgreeTop Proofs.libreac.fuzz_ctrl.lib.AgreeZlib Proofs.libreac.fuzz_ctrl.lib.AgreeShape Proofs.libreac.fuzz_ctrl.lib.SlotAgree.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import CtrlPlainRz CtrlTFIB HaltsSpecC.
(* Modified by Theorem Labs, 2026-10: the plain build's sink instances (Reusable/YI5b.v, YI5c.v, Required above for the plain side) and their ubsan copies (U/Reusable/YI5b.v, YI5c.v, loaded here through AgreeShape) are removed from instance search, so a sink instance left implicit in an ASan composition here cannot be found; #[global] is deliberate export: #[local] does not reach files that Require this top (two Theorem Labs lanes measured), and the guard must hold for any future consumer, so it is exported in lockstep with image B's top; settings v6 lists Remove Hints under HINTS (report-only), so the settings rule is met; full paths, because both copies are loaded here and the short form was measured to be a no-op (a Theorem Labs lane step 3; fuzz_boxreg's form, a working branch 12834cac4ca lib/A/Prog/BoxPa.v:21). *)
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI5b OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI5c OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable.YI5b OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable.YI5c.
#[global] Remove Hints OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI5b.src0_sink_head OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI5c.src0_sink OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YI5c.src0_sink_laws OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable.YI5b.src0_sink_head OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable.YI5c.src0_sink OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable.YI5c.src0_sink_laws : typeclass_instances.
Import ListNotations.
Open Scope Z_scope.
#[local] Existing Instance YK11.fx0.

Lemma asan_lim_source_le : SanitizerBudgets.lim_source <= ShippedBudgets.lim_source.
Proof. unfold SanitizerBudgets.lim_source, sanitizer_source_limit, ShippedBudgets.lim_source, source_alloc_limit. cbn. lia. Qed.

Lemma lim_source_le_target : ShippedBudgets.lim_source <= target_alloc_limit.
Proof. unfold ShippedBudgets.lim_source, source_alloc_limit, target_alloc_limit. cbn. lia. Qed.

Section a.
Hypothesis TFIB : TFIB_T.

Theorem ctrl_asan_agrees_of_tfib : Statements.asan_agrees.
Proof.
  unfold Statements.asan_agrees, agrees_in.
  intros en_s [sp' brk' mb' rnd'] inp Hens Hent Hinp SWB.
  pose proof (ctrl_plain_rz en_s inp Hens Hinp) as HP.
  destruct en_s as [sp brk mb rnd].
  pose proof (valid_input_va_size _ Hinp) as Hsv48.
  unfold Images.asan in Hent.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent. destruct Hent as [Hsp' [Hbrk' [Hmb' Hfit']]].
  exact (shape_strong_equiv_efs_relim SanitizerBudgets.lim_source ShippedBudgets.lim_source SanitizerBudgets.lim_target
    Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs sp brk mb rnd
    ctrlsegs0 Asan.M.init_pc Asan.M.phdrs sp' brk' mb' rnd'
    (SPECX (LS:=ag_shape checksum_shape) inp) (SPECX (LS:=ag_shape checksum_shape) inp) inp
    asan_lim_source_le SWB HP (TFIB sp' brk' mb' rnd' inp Hsp' Hbrk' Hmb' Hfit' Hinp) (t_eq_refl _)).
Qed.

Theorem ctrl_asan_halts_of_tfib : Statements.asan_halts.
Proof.
  unfold Statements.asan_halts, Images.asan.
  change (halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source Exits.ok_or_refused
    (mkImage ctrlsegs0 Asan.M.init_pc Asan.M.phdrs)).
  apply (halts_budgets_of_srealizes forced_only_cfg Exits.ok_or_refused ctrlsegs0 Asan.M.init_pc Asan.M.phdrs
    target_alloc_limit ShippedBudgets.lim_source lim_source_le_target (forced_only_cfg_least _)).
  intros sp brk mb rnd inp Hen Hinp. exists (SPECX (LS:=ag_shape checksum_shape) inp). split.
  - pose proof (valid_input_va_size _ Hinp) as Hsv48.
    rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hen. destruct Hen as [Hsp [Hbrk [Hmb Hfit]]].
    exact (TFIB sp brk mb rnd inp Hsp Hbrk Hmb Hfit Hinp).
  - exact (SPECX_shape_ok inp).
Qed.
End a.
