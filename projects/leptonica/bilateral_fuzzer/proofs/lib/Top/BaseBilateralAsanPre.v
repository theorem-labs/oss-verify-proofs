(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From OSSVerify.leptonica.bilateral_fuzzer.images Require Import Plain.
From OSSVerify.leptonica.bilateral_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec ShapeAlg ShapeEF Hoare AllocIface CfgStep.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import Spec.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.O2 Require Import O2FuzzIface O2Main.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Spec Require Canon Prog.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Top Require TopLevelA.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Top Require Import SpecCanonBridge.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Section Pre.
  Context {ALs : AllocLayout} {CLs : CallocLayout} {ASRs : @AllocSure ALs CLs}.
  Hypothesis PINs : @O2Main.pins ALs.
  Hypothesis FZs : @O2FuzzIface.fuzz_call_contract ALs CLs ASRs.
  Hypothesis S3A : TopLevelA.S3s_stmt Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs.

  Theorem bilateral_asan_pre :
    strong_universal_error_free_T_scfg_budgets (alloc_only_cfg false) SanitizerBudgets.lim_source SanitizerBudgets.lim_target
      (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs)
      (mkImage Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs).
  Proof.
    intros [sps brks mbs draws] ent inp Hvs Hvt Hvi Hwb.
    destruct (TopLevelA.T_canon _ _ _ S3A ent inp Hvt Hvi) as [HtrT HerrT].
    pose proof (valid_input_va_size _ Hvi) as Hsv.
    rewrite (valid_entry_sv48 _ _ _ Hsv) in Hvs.
    destruct Hvs as (Hsps & Hbrks & _ & Hfits).
    destruct Hvi as (Hva & Hve & _).
    assert (Hsrc : realizes Plain.M.loaded_segments
                     (init_config Plain.M.loaded_segments
                        Plain.M.init_pc Plain.M.phdrs
                        sps brks mbs draws SanitizerBudgets.lim_source inp)
                     (spec (in_argv inp) (in_fs inp))).
    { apply (@O2Main.ref_realizes_spec_pins ALs CLs ASRs PINs FZs); try assumption. apply Z.le_refl. }
    destruct (realizes_source_within_budget _ _ _ _ _ _ _ _ _ _ Hsrc Hwb) as [Hef Htr].
    split; [| split].
    - exact Hef.
    - exact HerrT.
    - intro tr. cbn [run_scfg bh_traces]. change (alloc_only_cfg false) with kit_cfg.
      pose proof (Htr tr) as Htr'. cbn [run_scfg bh_traces] in Htr'.
      rewrite Htr'.
      rewrite (spec_canonT (in_argv inp) (in_fs inp) tr).
      symmetry. exact (HtrT tr).
  Qed.
End Pre.
