(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: shape_strong_equiv_sef_AS states both realizes premises over run_segments, which both_triple_lim reaches from the binaries' own segments through RomStable.run_init and AS.RomStable.srun_init; both_triple_lim also reads valid_launch, entry_launch_ok_va and valid_input_recorded_kernel, destructs valid_input's seventeen conjuncts and ProcInput's new fields, and passes the execfn, the kernel build and the launch premises to a_boot; the launch's channel-reader and SIGPIPE-terminal flags come from valid_input's conjuncts, and its SIGPIPE-default flag is passed to a_boot. *)
(* [comment removed for export] *)
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Ox.S150_002.   (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.cjson.cjson_read_fuzzer.images Require Import AsanUbsan.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg ShapeEF ShapeSpec TopUbsan.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Glue Require Import Top04.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import BImg AMainEntry ABoot.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require ShapeAlg SpinAlg BothPlanImages AsanInit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Cfg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require RomStable.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require RomStable.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Local Notation psegs := OSSVerify.cjson.cjson_read_fuzzer.images.Plain.M.loaded_segments (only parsing).
Local Notation ppc := OSSVerify.cjson.cjson_read_fuzzer.images.Plain.M.init_pc (only parsing).
Local Notation pph := OSSVerify.cjson.cjson_read_fuzzer.images.Plain.M.phdrs (only parsing).

Definition BOTH : Image :=
  mkImage AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs.

(* [comment removed for export] *)
Theorem shape_strong_equiv_sef_AS :
  forall source_segs rpc rph rsp rbrk rmb rrnd (rlim : Z)
         target_segs apc aph asp abrk amb arnd (alim : Z)
         (T : TSet) (inp : ProcInput),
  realizes (run_segments source_segs inp rsp rmb)
    (init_config (run_segments source_segs inp rsp rmb) rpc rph rsp rbrk rmb rrnd rlim inp) T ->
  AS.SpinAlg.srealizes (run_segments target_segs inp asp amb)
    (init_config (run_segments target_segs inp asp amb) apc aph asp abrk amb arnd alim inp) T ->
  error_free (run_scfg ACFG (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
  /\ error_free (run_scfg ACFG (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp)
  /\ trace_equiv (bh_traces (run_scfg ACFG (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp))
                 (bh_traces (run_scfg ACFG (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp)).
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim T inp Hsource Htarget.
  split; [| split].
  - cbn. eapply realizes_no_error; exact Hsource.
  - cbn. eapply AS.SpinAlg.srealizes_no_error; exact Htarget.
  - intro tr. cbn.
    rewrite (realizes_obs_iff (run_segments source_segs inp rsp rmb) _ T Hsource tr).
    rewrite (AS.SpinAlg.srealizes_obs_iff (run_segments target_segs inp asp amb) _ T Htarget tr).
    reflexivity.
Qed.

(* [comment removed for export] *)
Lemma both_triple_lim : a_main_stmt -> forall (lim : Z), (OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KInv2.drv_limit <= lim)%Z ->
  forall en_source en_target inp,
    valid_entry SRC0 en_source inp -> valid_entry BOTH en_target inp -> valid_input inp ->
    error_free (run_scfg ACFG SRC0 lim en_source inp)
    /\ error_free (run_scfg ACFG BOTH target_alloc_limit en_target inp)
    /\ trace_equiv (bh_traces (run_scfg ACFG SRC0 lim en_source inp)) (bh_traces (run_scfg ACFG BOTH target_alloc_limit en_target inp)).
Proof.
  intros HA lim Hlim [rsp rbrk rmb rrnd] [asp abrk amb arnd] inp Hens Hent Hinp.
  apply (shape_strong_equiv_sef_AS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (spec04 (in_argv inp) (in_fs inp))).
  - (* LPS 08b1429: the run starts over run_segments; the walks are over the binaries' own segments *)
    apply RomStable.run_init; [reflexivity | exact (plain_realizes04_lim lim Hlim rsp rbrk rmb rrnd inp Hens Hinp)].
  - apply AS.RomStable.srun_init; [reflexivity |].
    pose proof (valid_input_va_size _ Hinp) as Hsv48.
    rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent.
    destruct Hent as [Hsp [Hbrk [Hmb [Hfit Hlau]]]].
    (* [comment removed for export] *)
    pose proof (valid_input_launch _ Hinp) as Hlaunch.
    (* BY NAME, and ABOVE the destruct that consumes Hinp - order is load-bearing.
       valid_input_recorded_kernel (75d69e00:Run.v:5666-5667) gives
       in_kernel inp = recorded_kernel (in_kernel inp), the LAST of valid_input's seventeen
       conjuncts (:4583-4596).  AsanInit builds its Section input with (recorded_kernel kb)
       at :135-137, so a_boot concludes about (recorded_kernel kern) while the goal carries
       plain kern; this is the one fact that reconciles them. *)
    pose proof (valid_input_recorded_kernel _ Hinp) as Hkern.
    (* valid_input went 15 -> 17 conjuncts and this pattern was written for 15.  Of the two
       insertions only slot 5 (fs_image_real inp = true) shifts a NAMED position; slot 13
       (valid_launch) falls inside the trailing _.  Slot 5 is an EQUATION where the old
       pattern asked for the conjunction (Huid & _), so it could not type-check - KNOWN RED
       BY CONSTRUCTION, never a silent mis-binding.  The port is exactly one underscore,
       derived from the definition rather than guessed at a slot. *)
    destruct Hinp as (Hargv & Henvp & Hfs & _ & _ & (Huid & _) & _ & _ & Hhw & _ & Hvs & _ & _ & Hcrd & Hspt & _).
    destruct inp as [argv envp ifs stdin uid gid groups net nof sigm hw abt vs urnd tmp kern xfn crd spd spt].
    cbn [in_argv in_envp in_fs in_image_fs in_tmp in_uid in_hwcap in_va_size in_kernel in_channel_reader in_sigpipe_terminal] in *.
    subst vs crd spt.
    rewrite Hkern in Hlaunch, Hlau |- *.
    exact (a_boot HA asp abrk amb arnd argv envp ifs stdin uid gid hw groups net nof sigm abt urnd tmp xfn kern spd
             Hsp Hbrk Hmb Hargv Henvp Hfs Hfit Huid Hhw Hlaunch Hlau).
Qed.

(* [comment removed for export] *)
Theorem both_base_of : a_main_stmt -> strong_universal_error_free_T_scfg ACFG SRC0 BOTH.
Proof.
  intros HA en_source en_target inp Hens Hent Hinp.
  refine (both_triple_lim HA source_alloc_limit _ en_source en_target inp Hens Hent Hinp).
  unfold OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KInv2.drv_limit, source_alloc_limit. lia.
Qed.

(* [comment removed for export] *)
Theorem both_base_of_budgets : a_main_stmt ->
  strong_universal_error_free_T_scfg_budgets ACFG source_alloc_limit target_alloc_limit SRC0 BOTH.
Proof. intros HA. apply strong_universal_error_free_T_scfg_budgets_of_scfg. exact (both_base_of HA). Qed.

(* [comment removed for export] *)
Theorem both_base_of_san : a_main_stmt ->
  strong_universal_error_free_T_scfg_budgets ACFG sanitizer_source_limit target_alloc_limit SRC0 BOTH.
Proof.
  intros HA en_source en_target inp Hens Hent Hinp _.
  exact (both_triple_lim HA sanitizer_source_limit sanitizer_limit_ok en_source en_target inp Hens Hent Hinp).
Qed.
