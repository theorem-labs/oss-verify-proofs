(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch's validity hypotheses; the reader fact of the output channels; walks over the binary's segments lifted to the run's segment list). *)
(* [comment removed for export] *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgP ImgU.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LibIface ShapeAlg ShapeEF Spec SpecNoKill RefMainClosed UbMainClosed.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require RefLim.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import RomStable.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition image_P : Image := mkImage ImgP.M.loaded_segments ImgP.M.init_pc ImgP.M.phdrs.
Definition image_U : Image := mkImage ImgU.M.loaded_segments ImgU.M.init_pc ImgU.M.phdrs.

Theorem ubsan_base : lib_stmt_P -> lib_stmt_U -> strong_universal_error_free_T image_P image_U.
Proof.
  intros HLP HLU [rsp rbrk rmb rrnd] [asp abrk amb arnd] inp Hens Hent Hvalid.
  (* [comment removed for export] *)
  pose proof (valid_input_va_size _ Hvalid) as Hsv48.
  pose proof (valid_input_launch _ Hvalid) as Hvl.
  pose proof (valid_input_channel_reader _ Hvalid) as Hcr.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hens. rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent.
  destruct Hens as (Hrsp & Hrbrk & Hrmb & Hrfit & Hrlau). destruct Hent as (Hasp & Habrk & Hamb & Hafit & Halau).
  destruct Hvalid as (Hargv & Henvp & Hfs & _).
  apply (shape_strong_equiv_ef _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (spec (in_argv inp) (in_fs inp))).
  - eapply run_init; [reflexivity|].
    exact (RefMainClosed.ref_realizes_spec_closed (AL:=RefLim.SrcLim) HLP rsp rbrk rmb rrnd inp Hrsp Hrbrk Hrfit Hargv Henvp Hfs Hvl Hrlau Hcr).
  - eapply run_init; [reflexivity|].
    exact (UbMainClosed.ref_realizes_spec_closed HLU asp abrk amb arnd inp Hasp Habrk Hafit Hargv Henvp Hfs Hvl Halau Hcr).
Qed.

(* [comment removed for export] *)
Theorem ubsan_base_abort : lib_stmt_P -> lib_stmt_U ->
  strong_universal_error_free_T_budgets_abort ShippedBudgets.lim_source ShippedBudgets.lim_target image_P image_U.
Proof.
  intros HLP HLU [rsp rbrk rmb rrnd] [asp abrk amb arnd] inp Hens Hent Hvalid _.
  pose proof (valid_input_abort_va_size _ Hvalid) as Hsv48.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hens. rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent.
  destruct Hens as (Hrsp & Hrbrk & Hrmb & Hrfit & Hrlau). destruct Hent as (Hasp & Habrk & Hamb & Hafit & Halau).
  destruct Hvalid as (Hargv & Henvp & Hfs & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hvl & Hcr & _).
  unfold strong_equiv_error_free_budgets_abort, ShippedBudgets.lim_source, ShippedBudgets.lim_target.
  apply (shape_strong_equiv_ef_abort _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (spec (in_argv inp) (in_fs inp))).
  - eapply run_init; [reflexivity|].
    exact (RefMainClosed.ref_realizes_spec_closed (AL:=RefLim.SrcLim) HLP rsp rbrk rmb rrnd inp Hrsp Hrbrk Hrfit Hargv Henvp Hfs Hvl Hrlau Hcr).
  - eapply run_init; [reflexivity|].
    exact (UbMainClosed.ref_realizes_spec_closed HLU asp abrk amb arnd inp Hasp Habrk Hafit Hargv Henvp Hfs Hvl Halau Hcr).
  - apply spec_no_kill.
Qed.
