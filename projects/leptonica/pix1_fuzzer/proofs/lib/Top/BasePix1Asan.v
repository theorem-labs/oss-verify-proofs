(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (pix1_asan_pre runs the source against the run's segment list (the image plus the vDSO pair) through RomStable.run_init, with valid_input's channel-reader and launch facts; s3s_closed given TopA's topA_runseg; imports). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From OSSVerify.leptonica.pix1_fuzzer.images Require Import Plain.
From OSSVerify.leptonica.pix1_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common Require Import PropExec ShapeAlg ShapeEF Hoare AllocIface CfgStep.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Mallocng Require Import MallocLayout MallocAllocLayout AllocBase AllocCalloc AllocSure.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.CliDriver Require Import Spec.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.O22 Require Import O22Drv1.
Import O22Drv1.O22FuzzIface.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.O22 Require Import O22Main.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.O22 Require Import O22Kit.
Import O22Kit.O22MallocLayout. Import O22Kit.O22Alloc. Import O22Kit.O22Sure.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.O22 Require Import O22Tail.
Import O22Tail.O22Pins. Import O22Tail.O22LeptPinsI.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.K5.Spec Require Canon Prog.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.K5.Top Require TopLevelA.
Require OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.K5.A22.TopA_final.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Top Require Import SpecCanonBridge.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Cfg Require Import RomStable.
Import ListNotations.

Section Pre.
  Context {ALs : AllocLayout} {CLs : CallocLayout} {ASRs : @AllocSure ALs CLs}.
  Hypothesis PINs : @O22Main.pins ALs.
  Hypothesis FZs : @O22Drv1.O22FuzzIface.fuzz_call_contract ALs CLs ASRs.
  Hypothesis S3A : TopLevelA.S3s_stmt Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs.

  Theorem pix1_asan_pre :
    strong_universal_error_free_T_scfg_budgets (alloc_only_cfg false) ShippedBudgets.lim_source ShippedBudgets.lim_target
      (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs)
      (mkImage Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs).
  Proof.
    intros [sps brks mbs draws] ent inp Hvs Hvt Hvi _.
    destruct (TopLevelA.T_canon _ _ _ S3A ent inp Hvt Hvi) as [HtrT HerrT].
    pose proof (valid_input_va_size _ Hvi) as Hsv.
    rewrite (valid_entry_sv48 _ _ _ Hsv) in Hvs.
    destruct Hvs as (Hsps & Hbrks & _ & Hfits & Hlaus).
    pose proof (valid_input_channel_reader _ Hvi) as Hrd. pose proof (valid_input_launch _ Hvi) as Hvl.
    destruct Hvi as (Hva & Hve & _).
    (* the run reads the binary against its segments and the vDSO pair: [RomStable.run_init] *)
    assert (Hsrc : realizes (run_segments Plain.M.loaded_segments inp sps mbs)
                     (init_config (run_segments Plain.M.loaded_segments inp sps mbs)
                        Plain.M.init_pc Plain.M.phdrs
                        sps brks mbs draws ShippedBudgets.lim_source inp)
                     (spec (in_argv inp) (in_fs inp))).
    { apply run_init; [reflexivity |].
      apply (@O22Main.ref_realizes_spec_pins ALs CLs ASRs PINs FZs); try assumption.
      unfold ShippedBudgets.lim_source, source_alloc_limit. apply Z.le_refl. }
    split; [| split].
    - cbn. eapply realizes_no_error; exact Hsrc.
    - exact HerrT.
    - intro tr. cbn [run_scfg bh_traces]. change (alloc_only_cfg false) with kit_cfg.
      rewrite (realizes_obs_iff _ _ _ Hsrc tr).
      rewrite (spec_canonT (in_argv inp) (in_fs inp) tr).
      symmetry. exact (HtrT tr).
  Qed.
End Pre.

Theorem strong_universal_error_free_pix1_fuzzer_asan :
  strong_universal_error_free_T_scfg_budgets (alloc_only_cfg false) ShippedBudgets.lim_source ShippedBudgets.lim_target
    (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs)
    (mkImage Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs).
Proof.
  exact (@pix1_asan_pre _ _ s22_sure O22Tail.O22Pins.s22_pins (s22_fuzz_call s22_sure) (OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.K5.A22.TopA_final.s3s_closed OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.K5.A22.TopA.topA_runseg)).
Qed.
