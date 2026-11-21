(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch's validity hypotheses; the process input's new fields; the start-up taken per CONFIG_RSEQ value; the reader fact of the output channels; the mapping ledger's reserved ranges and mmap base; the SIGPIPE disposition; walks over the binary's segments lifted to the run's segment list). *)
(* [comment removed for export] *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgP ImgB ImgSame.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec ShapeAlg SpinAlg Spec SpecNoKill ShapeEF ShapeEFS
  AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanLibNode AsanPlan AsanPlanSound AsanPlanImages BothPlanImages AsanPlanImagesInit
  AsanInit AsanStartup BothTableL BothLibTab BothStartup AsanNodesArg AsanNodesIO AsanMainLib AsanShape AsanMainDefs BothMainDefs BothMain BothMainClosed AsanNodesRP.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import RomStable.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

(* [comment removed for export] *)
Record both_certs : Type := BOTH_CERTS {
  ac_IT0 : itab;                                  (* [comment removed for export] *)
  ac_IT0_ok : itab_sound BSEGS ac_IT0;            (* [comment removed for export] *)
  ac_HS : nat -> option acs;                      (* [comment removed for export] *)
  ac_plan : Z -> plan;                            (* LPS 727298f3: per CONFIG_RSEQ value *)
  ac_shape : Z -> shape;                          (* LPS 727298f3: per CONFIG_RSEQ value *)
  ac_KC0 : nat; ac_BFUEL : nat; ac_FUEL : nat;
  ac_TT0 : nat -> option (acs * plan * shape);      (* [comment removed for export] *)
  ac_TT0_ok : AP.tails_ok0 BSEGS ac_IT0 BOTHL NX0 AsanInit.LIMIT ac_TT0 ac_KC0;   (* [comment removed for export] *)
  ac_cert : forall r, 0 <= r <= 1 ->
    check BSEGS ac_IT0 BOTHL NX0 AsanInit.LIMIT (RPN.xn BSEGS BOTHL NX0 RPN.RP_BOTH) XE0 XB0 XL0 ac_HS HL0 ac_TT0 ac_KC0 ac_BFUEL ac_FUEL None (both_initL_r r) (ac_plan r) = COk (ac_shape r);
  ac_all_holes : forall r, all_holes (ac_shape r) = true;
  ac_noblob : forall h ch, ac_HS h = Some ch -> acs_noblob ch = true;   (* [comment removed for export] *)
  ac_KCm : nat; ac_BFUELm : nat; ac_FUELm : nat;  (* [comment removed for export] *)
  ac_ITm : itab;                                  (* [comment removed for export] *)
  ac_ITm_ok : itab_sound BSEGS ac_ITm;
  ac_TTm : nat -> option (acs * plan * shape);      (* [comment removed for export] *)
  ac_TTm_ok : tails_all_ok ac_KCm ac_BFUELm ac_FUELm ac_ITm ac_TTm;   (* [comment removed for export] *)
  ac_TREE : nat -> nat -> mtree;                  (* [comment removed for export] *)
  ac_TREES : forall h ch i, ac_HS h = Some ch -> (i < 6)%nat ->
               mtree_ok ac_KCm ac_BFUELm ac_FUELm ac_ITm ac_TTm 0 0 (HSA ac_HS h) (root_class i) (ac_TREE h i) = true
}.

(* [comment removed for export] *)
Record both_obls : Type := BOTH_OBLS {
  ao_LINV : (word -> option byte) -> Prop;
  ao_linv : LINV_STMT_B ao_LINV;      (* [comment removed for export] *)
  ao_xall : XALL_STMT_B ao_LINV;      (* [comment removed for export] *)
  ao_xlib : XLIB_STMT_B ao_LINV;      (* [comment removed for export] *)
  ao_xarg : XARG_STMT_B ao_LINV;      (* [comment removed for export] *)
  ao_xrp : XRP_STMT_B ao_LINV         (* [comment removed for export] *)
}.


Definition plain_stmt_B : Prop :=   (* [comment removed for export] *)
  forall (sp brk mbase : word) (rdraw : EntryDraw) (inp : ProcInput),
    valid_sp sp -> valid_brk ImgP.M.loaded_segments brk -> entry_stack_fits sp (in_argv inp) (in_envp inp) ->
    valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) ->
    valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase rdraw) inp -> in_channel_reader inp = true ->
    realizes ImgP.M.loaded_segments
      (init_config ImgP.M.loaded_segments ImgP.M.init_pc ImgP.M.phdrs sp brk mbase rdraw sanitizer_source_limit inp)
      (spec (in_argv inp) (in_fs inp)).

Section Top.
  Hypothesis HPLAIN : plain_stmt_B.
  Variable O : both_obls.
  Variable C : both_certs.

  (* [comment removed for export] *)
  Lemma both_side : forall (asp abrk amb : word) (arnd : EntryDraw) (inp : ProcInput),
    valid_sp asp -> valid_brk ImgB.M.loaded_segments abrk -> valid_mmap_base amb ->
    entry_stack_fits asp (in_argv inp) (in_envp inp) ->
    valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_id (in_uid inp) -> valid_hwcap (in_hwcap inp) ->
    in_va_size inp = Sv48 ->
    in_channel_reader inp = true -> in_sigpipe_terminal inp = false ->
    in_kernel inp = recorded_kernel (in_kernel inp) ->
    valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry asp abrk amb arnd) inp ->
    srealizes ImgB.M.loaded_segments
      (init_config ImgB.M.loaded_segments ImgB.M.init_pc ImgB.M.phdrs asp abrk amb arnd target_alloc_limit inp)
      (spec (in_argv inp) (in_fs inp)).
  Proof.
    intros asp abrk amb arnd inp Hasp Habrk Hamb Hafit Hargv Henvp Huid Hhw Hva Hcr Hst Hk Hvl Hlau.
    destruct inp as [argv envp ifs stdin uid gid groups net nofile sigmask hw abort va ur tmp kern execfn cr sd st].
    cbn in *. subst va cr st.
    (* LPS 727298f3: the SIGPIPE disposition [sd] is free in [valid_input_abort]; the start-up
       holds at either value ([AsanInit.inp] takes it). *)
    exact (both_realizes_spec_closed (ao_LINV O) (ao_linv O) (ao_xall O) (ao_xlib O) (ao_xarg O) (ao_xrp O) asp arnd abrk amb argv envp (fs_seed_tmp ifs tmp) stdin uid gid hw nofile sigmask abort sd groups net ur Hasp Habrk Hamb Hargv Henvp Hafit Huid Hhw ImgB.M.init_pc eq_refl kern execfn Hk Hvl Hlau (ac_IT0 C) (ac_IT0_ok C) (ac_HS C) (ac_plan C) (ac_shape C) (ac_KC0 C) (ac_BFUEL C) (ac_FUEL C) (ac_TT0 C) (ac_cert C) (ac_TT0_ok C) (ac_all_holes C) (ac_noblob C) (ac_KCm C) (ac_BFUELm C) (ac_FUELm C) (ac_ITm C) (ac_TTm C) (ac_ITm_ok C) (ac_TTm_ok C) (ac_TREE C) (ac_TREES C)).
  Qed.

  (** NO KERNEL PREMISE.  At LPS 75d69e00 the kernel fact the start-up needs is the LAST
      conjunct of [valid_input_abort] itself -- [in_kernel inp = recorded_kernel (in_kernel inp)]
      ([Run.valid_input_abort_recorded_kernel]) -- which pins eight fields at [default_kernel]'s
      values and leaves thp, aslr, guard, rnd_bits and rseq FREE. *)
  Theorem both_top_abort :
    strong_universal_error_free_T_budgets_abort SanitizerBudgets.lim_source SanitizerBudgets.lim_target image_P image_B.
  Proof.
    intros [rsp rbrk rmb rrnd] [asp abrk amb arnd] inp Hens Hent Hvalid _.
    pose proof (valid_input_abort_recorded_kernel _ Hvalid) as Hk.
    pose proof (valid_input_abort_va_size _ Hvalid) as Hsv48.
    rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hens. rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent.
    destruct Hens as (Hrsp & Hrbrk & Hrmb & Hrfit & Hrlau). destruct Hent as (Hasp & Habrk & Hamb & Hafit & Halau).
    destruct Hvalid as (Hargv & Henvp & Hfs & _ & _ & [Huid Hgid] & _ & _ & Hhw & _ & Hva & _ & Hvl & Hcr & Hst & _).
    unfold strong_equiv_error_free_budgets_abort, SanitizerBudgets.lim_source, SanitizerBudgets.lim_target.
    apply (shape_strong_equiv_efs_abort _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (spec (in_argv inp) (in_fs inp))).
    - eapply run_init; [reflexivity|].
      exact (HPLAIN rsp rbrk rmb rrnd inp Hrsp Hrbrk Hrfit Hargv Henvp Hfs Hvl Hrlau Hcr).
    - eapply srun_init; [reflexivity|].
      exact (both_side asp abrk amb arnd inp Hasp Habrk Hamb Hafit Hargv Henvp Huid Hhw Hva Hcr Hst Hk Hvl Halau).
    - apply spec_no_kill.
  Qed.
End Top.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
