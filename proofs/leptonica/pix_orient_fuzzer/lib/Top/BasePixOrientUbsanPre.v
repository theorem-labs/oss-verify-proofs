(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Plain.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec ShapeAlg ShapeEF Hoare AllocIface.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import Spec.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23FuzzIface O23Main.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23FuzzIface V23Main.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section Pre.
  (* [comment removed for export] *)
  Context {ALs : AllocLayout} {CLs : CallocLayout} {ASRs : @AllocSure ALs CLs}.
  Hypothesis PINs : @O23Main.pins ALs.
  Hypothesis FZs : @O23FuzzIface.fuzz_call_contract ALs CLs ASRs.
  (* [comment removed for export] *)
  Context {ALu : AllocLayout} {CLu : CallocLayout} {ASRu : @AllocSure ALu CLu}.
  Hypothesis PINu : @V23Main.pins ALu.
  Hypothesis FZu : @V23FuzzIface.fuzz_call_contract ALu CLu ASRu.

  Theorem pix_orient_ubsan_pre :
    strong_universal_error_free_T_scfg_budgets (alloc_only_cfg false) ShippedBudgets.lim_source ShippedBudgets.lim_target
      (mkImage Plain.M.loaded_segments Plain.M.init_pc
               Plain.M.phdrs)
      (mkImage Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs).
  Proof.
    intros [sps brks mbs draws] [spt brkt mbt drawt] inp Hvs Hvt Hvi _.
    pose proof (valid_input_va_size _ Hvi) as Hsv.
    rewrite (valid_entry_sv48 _ _ _ Hsv) in Hvs. rewrite (valid_entry_sv48 _ _ _ Hsv) in Hvt.
    destruct Hvs as (Hsps & Hbrks & _ & Hfits). destruct Hvt as (Hspt & Hbrkt & _ & Hfitt).
    destruct Hvi as (Hva & Hve & _).
    apply (shape_strong_equiv_ef _ _ _ sps brks mbs draws ShippedBudgets.lim_source
             _ _ _ spt brkt mbt drawt ShippedBudgets.lim_target (spec (in_argv inp) (in_fs inp)) inp).
    - apply (@O23Main.ref_realizes_spec_pins ALs CLs ASRs PINs FZs); try assumption.
      unfold ShippedBudgets.lim_source, source_alloc_limit. apply Z.le_refl.
    - apply (@V23Main.ref_realizes_spec_pins ALu CLu ASRu PINu FZu); try assumption.
      unfold ShippedBudgets.lim_target, target_alloc_limit. cbn. lia.
  Qed.
End Pre.
