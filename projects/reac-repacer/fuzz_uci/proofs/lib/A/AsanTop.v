(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/A/AZ03.v and lib/Halts_tfib.v for fuzz_decode, by way of fuzz_grant's lib/A/AsanTop.v: the plain side is fuzz_decode's proved realization (built as its lib/AgreeFrame.v builds it for the ubsan agreement, with the plain slot contract of lib/Prog/LLVMFuzzerTestOneInput_gfr.v, at decode_shape), the halting corollary takes srealizes, module paths changed. *)
(* Modified by Theorem Labs: made from libreac/fuzz_decode proofs/libreac/fuzz_decode/lib/A/AsanTop.v for reac-repacer/fuzz_uci's ASan image: Section b (the ASan+UBSan image, lib/B's) dropped; the plain realization is lib/UciAsanShared.v's uci_plain_rz, the shape fuzz_uci's checksum_shape (lib/ZTraceSpec.v) in place of decode_shape, TFIB_T and SPECX_shape_ok are lib/A/UciTFIB.v's and lib/A/UciHaltsSpec.v's; module paths changed. *)
(* fuzz_uci's two ASan statements from the ASan side TFIB_T (UciTFIB.v), in the form of
   proofs/cgif/cgif_file_fuzzer/lib/A/AZ03.v (agreement) and lib/Halts_tfib.v (halting):
   - asan_agrees: shape_strong_equiv_efs_relim (Reusable/YM09.v) over the plain build's proved realization of SPECX
     (lib/UciAsanShared.v uci_plain_rz, at checksum_shape), the statement's plain budget premise, TFIB_T and t_eq_refl;
   - asan_halts: halts_budgets_of_srealizes (Reusable/HaltsKitB.v) over TFIB_T and SPECX_shape_ok (UciHaltsSpec.v). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.reac_repacer.fuzz_uci Require Statements Images.
From OSSVerify.reac_repacer.fuzz_uci.images Require Plain Asan.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import
  YK11 YK15 YK18 YM05 YM09 YO09 YO06 HaltsKitB.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib Require Import ZTraceSpec UciAsanShared.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A Require Import UciTFIB UciHaltsSpec.
Import ListNotations.
Open Scope Z_scope.
#[local] Existing Instance YK11.fx0.

Module USt := OSSVerify.reac_repacer.fuzz_uci.Statements.
Module UIm := OSSVerify.reac_repacer.fuzz_uci.Images.
Module UPl := OSSVerify.reac_repacer.fuzz_uci.images.Plain.

Section a.
Hypothesis TFIB : TFIB_T.

Theorem uci_asan_agrees_of_tfib : USt.asan_agrees.
Proof.
  unfold USt.asan_agrees, agrees_in.
  intros en_s [sp' brk' mb' rnd'] inp Hens Hent Hinp SWB.
  pose proof (uci_plain_rz en_s inp Hens Hinp) as HP.
  destruct en_s as [sp brk mb rnd].
  pose proof (valid_input_va_size _ Hinp) as Hsv48.
  unfold UIm.asan in Hent.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent. destruct Hent as [Hsp' [Hbrk' [Hmb' Hfit']]].
  exact (shape_strong_equiv_efs_relim SanitizerBudgets.lim_source ShippedBudgets.lim_source SanitizerBudgets.lim_target
    UPl.M.loaded_segments UPl.M.init_pc UPl.M.phdrs sp brk mb rnd
    ucisegs0 UAs.M.init_pc UAs.M.phdrs sp' brk' mb' rnd'
    (SPECX (LS:=checksum_shape) inp) (SPECX (LS:=checksum_shape) inp) inp
    asan_lim_source_le SWB HP (TFIB sp' brk' mb' rnd' inp Hsp' Hbrk' Hmb' Hfit' Hinp) (t_eq_refl _)).
Qed.

Theorem uci_asan_halts_of_tfib : USt.asan_halts.
Proof.
  unfold USt.asan_halts, UIm.asan.
  change (halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source Exits.ok_or_refused
    (mkImage ucisegs0 UAs.M.init_pc UAs.M.phdrs)).
  apply (halts_budgets_of_srealizes forced_only_cfg Exits.ok_or_refused ucisegs0 UAs.M.init_pc UAs.M.phdrs
    target_alloc_limit ShippedBudgets.lim_source lim_source_le_target (forced_only_cfg_least _)).
  intros sp brk mb rnd inp Hen Hinp. exists (SPECX (LS:=checksum_shape) inp). split.
  - pose proof (valid_input_va_size _ Hinp) as Hsv48.
    rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hen. destruct Hen as [Hsp [Hbrk [Hmb Hfit]]].
    exact (TFIB sp brk mb rnd inp Hsp Hbrk Hmb Hfit Hinp).
  - exact (SPECX_shape_ok inp).
Qed.
End a.
