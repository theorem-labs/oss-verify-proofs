(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/YZ03.v (agreement) and lib/Halts_tfib.v (halting) (c8557374ad2e), in the form of a Theorem Labs lane's proofs/libreac/fuzz_grant/lib/A/AsanTop.v (a working branch c2edc13c0fa), for fuzz_state's ASan+UBSan image: the plain side is fuzz_state's released realization at 2^34 (lib/FSPlain.v), module paths changed. *)
(* fuzz_state's two asan_ubsan statements from the ASan+UBSan side TFIB_T_B (lib/B/FSTfibB.v):
   - asan_ubsan_agrees: shape_strong_equiv_efs_relim (Reusable/YM09.v) over the plain build's proved realization of
     SPECX at 2^34 (lib/FSPlain.v fs_plain_rz), the statement's plain budget premise, TFIB_T_B and t_eq_refl;
   - asan_ubsan_halts: halts_budgets_of_srealizes (Reusable/HaltsKitB.v) over TFIB_T_B and SPECX_shape_ok
     (lib/FSHaltsSpec.v).
   Named open input: TFIB_T_B (Section hypothesis TFIBB); its open obligations are listed in lib/B/FSTfibB.v.
   The plain side uses fuzz_state's released, proved, slot-named plain-chain files unchanged (lead ruling 20:34Z via
   a Theorem Labs lane: "plain side from the unit's own released proofs"; condition: a Theorem Labs lane's premise and
   byte-identity check of the 23 files against fuzz_state's original images, (internal) section 4.8). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.omx_clap_core.fuzz_state Require Statements Images.
From OSSVerify.omx_clap_core.fuzz_state.images Require Plain AsanUbsan.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
  YK11 YK15 YK18 YM05 YM09 YO09 YO06 HaltsKitB.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require Import Agree AgreeTop AgreeShape ZTraceSpec
  FSPlain FSHaltsSpec.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import FSTfibB.
Import ListNotations.
Open Scope Z_scope.
#[local] Existing Instance YK11.fx0.

Section b.
Hypothesis TFIBB : TFIB_T_B.

Theorem fs_asan_ubsan_agrees_of_tfib : Statements.asan_ubsan_agrees.
Proof.
  unfold Statements.asan_ubsan_agrees, agrees_in.
  intros en_s [sp' brk' mb' rnd'] inp Hens Hent Hinp SWB.
  pose proof (fs_plain_rz en_s inp Hens Hinp) as HP.
  destruct en_s as [sp brk mb rnd].
  pose proof (valid_input_va_size _ Hinp) as Hsv48.
  unfold Images.asan_ubsan in Hent.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent. destruct Hent as [Hsp' [Hbrk' [Hmb' Hfit']]].
  exact (shape_strong_equiv_efs_relim SanitizerBudgets.lim_source ShippedBudgets.lim_source SanitizerBudgets.lim_target
    Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs sp brk mb rnd
    fsbsegs0 AsanUbsan.M.init_pc AsanUbsan.M.phdrs sp' brk' mb' rnd'
    (SPECX (LS:=ag_shape checksum_shape) inp) (SPECX (LS:=ag_shape checksum_shape) inp) inp
    FSTop.asan_lim_source_le SWB HP (TFIBB sp' brk' mb' rnd' inp Hsp' Hbrk' Hmb' Hfit' Hinp) (t_eq_refl _)).
Qed.

Theorem fs_asan_ubsan_halts_of_tfib : Statements.asan_ubsan_halts.
Proof.
  unfold Statements.asan_ubsan_halts, Images.asan_ubsan.
  change (halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source Exits.ok_or_refused
    (mkImage fsbsegs0 AsanUbsan.M.init_pc AsanUbsan.M.phdrs)).
  apply (halts_budgets_of_srealizes forced_only_cfg Exits.ok_or_refused fsbsegs0 AsanUbsan.M.init_pc AsanUbsan.M.phdrs
    target_alloc_limit ShippedBudgets.lim_source FSTop.lim_source_le_target (forced_only_cfg_least _)).
  intros sp brk mb rnd inp Hen Hinp. exists (SPECX (LS:=ag_shape checksum_shape) inp). split.
  - pose proof (valid_input_va_size _ Hinp) as Hsv48.
    rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hen. destruct Hen as [Hsp [Hbrk [Hmb Hfit]]].
    exact (TFIBB sp brk mb rnd inp Hsp Hbrk Hmb Hfit Hinp).
  - exact (SPECX_shape_ok inp).
Qed.
End b.

Check fs_asan_ubsan_agrees_of_tfib.
Check fs_asan_ubsan_halts_of_tfib.
Print Assumptions fs_asan_ubsan_agrees_of_tfib.
Print Assumptions fs_asan_ubsan_halts_of_tfib.
