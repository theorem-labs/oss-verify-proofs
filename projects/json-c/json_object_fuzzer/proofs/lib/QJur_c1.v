(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the walk over run_segments segs inp sp mbase, lifted by RomStable.run_init and srun_init, in place of the loaded segments, for binaries with no vDSO image; the launch premise entry_launch_ok_va on src_realizes_at, src_realizes_wb_at and tgt_srealizes_at, read from valid_entry's Sv48 form). *)

From Stdlib Require Import NArith List ZArith Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBxa. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9ox.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9ox.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1lV.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Cfg Require RomStable.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* LPS 727298f3: [run_scfg] runs over the run's segment list from the start configuration over it *)
Lemma srealizes_error_free : forall segs pc ph sp brk0 mb rnd lim inp T,
Q1lV.srealizes (run_segments segs inp sp mb) (init_config (run_segments segs inp sp mb) pc ph sp brk0 mb rnd lim inp) T ->
error_free (run_scfg (alloc_only_cfg false) (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp).
Proof. intros. cbn. eapply Q1lV.srealizes_no_error. eassumption. Qed.

Lemma srealizes_traces_iff : forall segs pc ph sp brk0 mb rnd lim inp T tr,
Q1lV.srealizes (run_segments segs inp sp mb) (init_config (run_segments segs inp sp mb) pc ph sp brk0 mb rnd lim inp) T ->
bh_traces (run_scfg (alloc_only_cfg false) (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp) tr <-> T tr.
Proof. intros. cbn. apply Q1lV.srealizes_obs_iff. assumption. Qed.

Lemma srealizes_not_killed : forall segs pc ph sp brk0 mb rnd lim inp T,
Q1lV.srealizes (run_segments segs inp sp mb) (init_config (run_segments segs inp sp mb) pc ph sp brk0 mb rnd lim inp) T ->
kill_free T ->
~ dies_by_signal (run_scfg (alloc_only_cfg false) (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp).
Proof.
intros segs pc ph sp brk0 mb rnd lim inp T Hrz Hkf (tr & sig & fs & Htr & Hin).
apply (srealizes_traces_iff segs pc ph sp brk0 mb rnd lim inp T tr Hrz) in Htr.
exact (Hkf tr Htr sig fs Hin).
Qed.

Section TopGlueA.
Variables (src_segs : list Segment) (src_pc : N) (src_ph : PhdrInfo).
Variables (tgt_segs : list Segment) (tgt_pc : N) (tgt_ph : PhdrInfo).

Definition SRC : Image := mkImage src_segs src_pc src_ph.
Definition TGT : Image := mkImage tgt_segs tgt_pc tgt_ph.

Variable SPEC : ProcInput -> TSet.
Hypothesis spec_kill_free : forall inp, kill_free (SPEC inp).
(* LPS 727298f3: neither binary carries a vDSO segment of its own; the run appends the pair
   ([RomStable.run_init] / [srun_init] lift a walk over the binary's segments to the run) *)
Hypothesis src_novdso : vdso_image src_segs = None.
Hypothesis tgt_novdso : vdso_image tgt_segs = None.

(* LPS 727298f3: the launch fact is the statement's own valid_entry's fifth conjunct
   ([Run.valid_entry_sv48]) *)
Definition src_realizes_wb_at (LS : Z) : Prop :=
forall sp brk mbase rnd (inp : ProcInput),
valid_sp sp -> valid_brk src_segs brk -> valid_mmap_base mbase ->
entry_stack_fits sp (in_argv inp) (in_envp inp) ->
entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp ->
valid_input_either inp ->
source_within_budget_scfg (alloc_only_cfg false) LS SRC (mkEntry sp brk mbase rnd) inp ->
realizes src_segs
(init_config src_segs src_pc src_ph sp brk mbase rnd LS inp)
(SPEC inp).

Definition src_realizes_at (LS : Z) : Prop :=
forall sp brk mbase rnd (inp : ProcInput),
valid_sp sp -> valid_brk src_segs brk -> valid_mmap_base mbase ->
entry_stack_fits sp (in_argv inp) (in_envp inp) ->
entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp ->
valid_input_either inp ->
realizes src_segs
(init_config src_segs src_pc src_ph sp brk mbase rnd LS inp)
(SPEC inp).

Definition tgt_srealizes_at (LT : Z) : Prop :=
forall sp brk mbase rnd (inp : ProcInput),
valid_sp sp -> valid_brk tgt_segs brk -> valid_mmap_base mbase ->
entry_stack_fits sp (in_argv inp) (in_envp inp) ->
entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp ->
valid_input_either inp ->
Q1lV.srealizes tgt_segs
(init_config tgt_segs tgt_pc tgt_ph sp brk mbase rnd LT inp)
(SPEC inp).

Lemma src_realizes_wb_of : forall LS, src_realizes_at LS -> src_realizes_wb_at LS.
Proof. intros LS H sp brk mbase rnd inp Hsp Hbrk Hmb Hfit Hlau Hei _. exact (H sp brk mbase rnd inp Hsp Hbrk Hmb Hfit Hlau Hei). Qed.

Theorem strong_universal_error_free_budgets_abort_of_mixed_wb : forall LS LT,
src_realizes_wb_at LS -> tgt_srealizes_at LT ->
strong_universal_error_free_T_scfg_budgets_abort (alloc_only_cfg false) LS LT SRC TGT.
Proof.
intros LS LT src_realizes tgt_srealizes.
intros [rsp rbrk rmb rrnd] [asp abrk amb arnd] inp Hens Hent Hinp Hwb.
pose proof (valid_input_abort_va_size _ Hinp) as H48.
rewrite (valid_entry_sv48 _ _ _ H48) in Hens. rewrite (valid_entry_sv48 _ _ _ H48) in Hent.
destruct Hens as [Hrsp [Hrbrk [Hrmb [Hrfit Hrlau]]]]. destruct Hent as [Hasp [Habrk [Hamb [Hafit Hal]]]].
pose proof (valid_input_either_of_valid_input_abort _ Hinp) as Hei.
pose proof (RomStable.run_init src_segs inp rsp rmb src_pc src_ph rbrk rrnd LS _ src_novdso
  (src_realizes rsp rbrk rmb rrnd inp Hrsp Hrbrk Hrmb Hrfit Hrlau Hei Hwb)) as RS.
pose proof (RomStable.srun_init tgt_segs inp asp amb tgt_pc tgt_ph abrk arnd LT _ tgt_novdso
  (tgt_srealizes asp abrk amb arnd inp Hasp Habrk Hamb Hafit Hal Hei)) as RT.
unfold strong_equiv_error_free_budgets_scfg_abort, error_free_unkilled.
split; [| split]; [split | split | ].
- exact (realizes_error_free _ _ _ _ _ _ _ _ _ _ RS).
- exact (realizes_not_killed _ _ _ _ _ _ _ _ _ _ RS (spec_kill_free inp)).
- exact (srealizes_error_free _ _ _ _ _ _ _ _ _ _ RT).
- exact (srealizes_not_killed _ _ _ _ _ _ _ _ _ _ RT (spec_kill_free inp)).
- intro tr.
rewrite (realizes_traces_iff _ _ _ _ _ _ _ _ _ _ tr RS).
rewrite (srealizes_traces_iff _ _ _ _ _ _ _ _ _ _ tr RT).
reflexivity.
Qed.

Theorem strong_universal_error_free_budgets_abort_of_mixed_at : forall LS LT,
src_realizes_at LS -> tgt_srealizes_at LT ->
strong_universal_error_free_T_scfg_budgets_abort (alloc_only_cfg false) LS LT SRC TGT.
Proof.
intros LS LT HS HT. apply strong_universal_error_free_budgets_abort_of_mixed_wb; [apply src_realizes_wb_of; exact HS| exact HT].
Qed.

Corollary strong_universal_error_free_sanitizer_abort_of_mixed :
src_realizes_at sanitizer_source_limit -> tgt_srealizes_at target_alloc_limit ->
strong_universal_error_free_T_scfg_budgets_abort (alloc_only_cfg false) SanitizerBudgets.lim_source SanitizerBudgets.lim_target SRC TGT.
Proof. apply strong_universal_error_free_budgets_abort_of_mixed_at. Qed.

Section Pinned.
Hypothesis src_realizes : src_realizes_at source_alloc_limit.
Hypothesis tgt_srealizes : tgt_srealizes_at target_alloc_limit.

Theorem strong_universal_error_free_of_mixed : strong_universal_error_free_T_scfg (alloc_only_cfg false) SRC TGT.
Proof.
intros [rsp rbrk rmb rrnd] [asp abrk amb arnd] inp Hens Hent Hinp.
pose proof (valid_input_va_size _ Hinp) as H48.
rewrite (valid_entry_sv48 _ _ _ H48) in Hens. rewrite (valid_entry_sv48 _ _ _ H48) in Hent.
destruct Hens as [Hrsp [Hrbrk [Hrmb [Hrfit Hrlau]]]]. destruct Hent as [Hasp [Habrk [Hamb [Hafit Hal]]]].
pose proof (valid_input_either_of_valid_input _ Hinp) as Hei.
pose proof (RomStable.run_init src_segs inp rsp rmb src_pc src_ph rbrk rrnd source_alloc_limit _ src_novdso
  (src_realizes rsp rbrk rmb rrnd inp Hrsp Hrbrk Hrmb Hrfit Hrlau Hei)) as RS.
pose proof (RomStable.srun_init tgt_segs inp asp amb tgt_pc tgt_ph abrk arnd target_alloc_limit _ tgt_novdso
  (tgt_srealizes asp abrk amb arnd inp Hasp Habrk Hamb Hafit Hal Hei)) as RT.
unfold strong_equiv_error_free_scfg.
split; [| split].
- exact (realizes_error_free _ _ _ _ _ _ _ _ _ _ RS).
- exact (srealizes_error_free _ _ _ _ _ _ _ _ _ _ RT).
- intro tr.
rewrite (realizes_traces_iff _ _ _ _ _ _ _ _ _ _ tr RS).
rewrite (srealizes_traces_iff _ _ _ _ _ _ _ _ _ _ tr RT).
reflexivity.
Qed.
End Pinned.
End TopGlueA.
