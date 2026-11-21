(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: changed as0_tgt_of_run, as0_tgt_stmt, msgpack_enc_asan_final_abort and 1 more; added vie_parts; taken in part from projects/jsoncons/fuzz_bigint/proofs/lib/BigintTopA.v, 24 lines within its lines 15-116. *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BMode. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0055. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require FrmInit. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.BMode OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037.DivergeSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlgX OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0055.ShapeEF OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063.Spec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063.BigintSpec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.LibIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0055.KillFree OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.FrmInit.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0258. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require MsgpackEncFinalS. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0258. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0258.Ns0DrvMain OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.MsgpackEncFinalS.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0117. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132.AsanInitK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0117.Na0DefsK.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Common.Cfg Require SRomStable.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section FPX_1.
#[local] Existing Instance PropExec.fx0.

(* [Run.valid_input_either]'s clauses, read by type and not by position (the predicate gained
   clauses at LPS 727298f3, so a positional pattern would bind the wrong fact); the SIGPIPE
   disposition is not among them: it is free and is passed on as the launch's [sdf]. *)
Lemma vie_parts : forall inp, valid_input_either inp ->
  valid_argv (in_argv inp) /\ valid_envp (in_envp inp) /\ valid_fs (in_fs inp)
  /\ valid_creds inp /\ valid_hwcap (in_hwcap inp) /\ in_va_size inp = Sv48
  /\ in_channel_reader inp = true /\ in_sigpipe_terminal inp = false.
Proof.
  intros inp H. red in H.
  repeat match goal with G : _ /\ _ |- _ => destruct G end.
  repeat match goal with |- _ /\ _ => split end; assumption.
Qed.

(* The target's run over [Run.run_segments] (the binary's segments with the run's vDSO pair),
   from an input of [Run.valid_input_either], with the launch facts of [Run.valid_entry_va]'s
   fifth conjunct and [valid_launch]; both published binders give them. *)
Definition as0_tgt_stmt (scfg : SpuriousCfg) : Prop :=
  forall sp brk mbase (rdraw : EntryDraw) (inp : ProcInput),
    valid_sp sp -> valid_brk Asan.M.loaded_segments brk -> valid_mmap_base mbase ->
    entry_stack_fits sp (in_argv inp) (in_envp inp) ->
    entry_launch_ok_va Sv48 (mkEntry sp brk mbase rdraw) inp -> valid_launch inp ->
    valid_input_either inp ->
    srealizes (run_segments Asan.M.loaded_segments inp sp mbase) scfg
      (init_config (run_segments Asan.M.loaded_segments inp sp mbase) Asan.M.init_pc Asan.M.phdrs
         sp brk mbase rdraw target_alloc_limit inp)
      (spec (in_argv inp) (in_fs inp)).

Lemma as0_tgt_of_run : forall scfg,
  (forall sp brk0 mbase (rdraw : EntryDraw) (argv envp : list (list byte)) (fs : Fs.Fs) (stdin : InputStream) (uid gid hw : word) (groups : list word)
          (net : NetQueue) (nofile sigmask : word) (abrt : bool) (ur : InputStream) (kb : KernelBuild) (execfn : list byte) (sdf : bool),
      valid_sp sp -> valid_brk ASEGS0 brk0 -> valid_mmap_base mbase -> valid_argv argv -> valid_envp envp -> entry_stack_fits sp argv envp ->
      entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) (AsanInitK.inp argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf) ->
      valid_launch (AsanInitK.inp argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf) ->
      valid_id uid -> valid_hwcap hw -> valid_fs fs ->
      srealizes ASEGS0 scfg (init_config ASEGS0 Asan.M.init_pc APH0 sp brk0 mbase rdraw AsanInitK.LIMIT
                                   (AsanInitK.inp argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf))
                (spec argv fs)) ->
  as0_tgt_stmt scfg.
Proof.
  intros scfg RUN sp brk mbase rdraw inp Hsp Hbrk Hmb Hfit Hlau Hvl Hvi.
  (* the walk over the binary's own segments lifts to the run's ([vdso_image] of them is [None]) *)
  apply (SRomStable.srun_init scfg Asan.M.loaded_segments inp sp mbase _ _ _ _ _ _ eq_refl).
  destruct (vie_parts inp Hvi) as (Hva & Hve & Hvfs & Hcreds & Hhw & Hsv & Hchrd & Hspt).
  pose proof (valid_input_either_recorded_kernel inp Hvi) as Hker. clear Hvi.
  destruct inp as [argv envp fs0 stdin0 uid gid groups net nofile sigmask hw abt va ur tmp kb exfn chrd spd spt].
  cbn [in_argv in_envp in_uid in_hwcap in_va_size in_fs in_image_fs in_tmp in_kernel
       in_channel_reader in_sigpipe_default in_sigpipe_terminal] in *.
  subst va chrd spt.
  destruct Hcreds as [Hu _]. cbn [in_uid] in Hu.
  (* the kernel of record: the input's build is [recorded_kernel] of itself, the place
     [AsanInitK.inp] writes [recorded_kernel kb] *)
  rewrite Hker in Hlau, Hvl |- *.
  exact (RUN sp brk mbase rdraw argv envp (fs_seed_tmp fs0 tmp)
             stdin0 uid gid hw groups net nofile sigmask abt ur kb exfn spd
             Hsp Hbrk Hmb Hva Hve Hfit Hlau Hvl Hu Hhw Hvfs).
Qed.

(* [comment removed for export] *)
Lemma SRC_on_2g : open_S -> Ns0DrvMain.src_realizes_stmt2 (bmK := bm_on_inst) cfg0 SanitizerBudgets.lim_source.
Proof. intros OS. exact (msgpack_enc_src_at (bmK := bm_on_inst) SanitizerBudgets.lim_source OS (or_introl eq_refl)). Qed.

(* [comment removed for export] *)
Theorem msgpack_enc_asan_final_abort :
  open_S -> as0_tgt_stmt cfg0 ->
  strong_universal_error_free_T_scfg_budgets_abort cfg0 SanitizerBudgets.lim_source SanitizerBudgets.lim_target
    (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs)
    (mkImage Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs).
Proof.
  intros OS TGT0.
  pose proof (SRC_on_2g OS) as SRC0.
  intros [rsp rbrk rmb rrnd] [asp abrk amb arnd] inp Hens Hent Hvalid Hsw.
  pose proof (valid_input_abort_va_size _ Hvalid) as Hsv48.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hens. rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent.
  destruct Hens as [Hrsp [Hrbrk [Hrmb [_ Hrlau]]]]. destruct Hent as [Hasp [Habrk [Hamb [Hafit Halau]]]].
  assert (Hvl : valid_launch inp) by (red in Hvalid; tauto).
  (* [valid_input_abort] is the published binder: the [valid_input_either] premise comes from it *)
  pose proof (valid_input_either_of_valid_input_abort inp Hvalid) as Hvi.
  destruct (vie_parts inp Hvi) as (Hargv & Henvp & Hfs & Hcreds & _ & _ & Hrd & _).
  specialize (SRC0 rsp rbrk rmb rrnd inp Hrsp Hrbrk Hrmb Hvl Hrlau Hargv Henvp Hfs Hcreds Hrd).
  specialize (TGT0 asp abrk amb arnd inp Hasp Habrk Hamb Hafit Halau Hvl Hvi).
  (* [comment removed for export] *)
  pose proof (top_of_guarded _ _ _ _ _ _ _ _ _ _ _ (SRomStable.frm_safe_run_segments _ inp rsp rmb frm_safe_Ms0)
                (srealizes_bm_transfer _ _ _ _ SRC0 ltac:(exact Hsw))) as SRC. clear SRC0.
  pose proof (top_of_guarded _ _ _ _ _ _ _ _ _ _ _ (SRomStable.frm_safe_run_segments _ inp asp amb frm_safe_Ma0) TGT0) as TGT. clear TGT0.
  unfold SanitizerBudgets.lim_source, SanitizerBudgets.lim_target in *.
  split; [| split].
  - eapply srealizes_error_free_unkilled; [exact SRC | apply kill_free_spec].
  - eapply srealizes_error_free_unkilled; [exact TGT | apply kill_free_spec].
  - intro tr.
    rewrite (srealizes_traces_iff cfg0 _ _ _ _ _ _ _ _ _ _ tr SRC).
    rewrite (srealizes_traces_iff cfg0 _ _ _ _ _ _ _ _ _ _ tr TGT).
    reflexivity.
Qed.

(* [comment removed for export] *)
Theorem msgpack_enc_asan_final_scfg :
  open_S -> as0_tgt_stmt cfg0 ->
  strong_universal_error_free_T_scfg cfg0
    (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs)
    (mkImage Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs).
Proof.
  intros OS TGT0.
  pose proof (msgpack_enc_src OS) as SRC0.
  intros [rsp rbrk rmb rrnd] [asp abrk amb arnd] inp Hens Hent Hvalid.
  pose proof (valid_input_va_size _ Hvalid) as Hsv48.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hens. rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent.
  destruct Hens as [Hrsp [Hrbrk [Hrmb [_ Hrlau]]]]. destruct Hent as [Hasp [Habrk [Hamb [Hafit Halau]]]].
  pose proof (valid_input_launch _ Hvalid) as Hvl.
  pose proof (valid_input_either_of_valid_input inp Hvalid) as Hvi.
  destruct (vie_parts inp Hvi) as (Hargv & Henvp & Hfs & Hcreds & _ & _ & Hrd & _).
  pose proof (top_of_guarded _ _ _ _ _ _ _ _ _ _ _ (SRomStable.frm_safe_run_segments _ inp rsp rmb frm_safe_Ms0)
                (SRC0 rsp rbrk rmb rrnd inp Hrsp Hrbrk Hrmb Hvl Hrlau Hargv Henvp Hfs Hcreds Hrd)) as SRC.
  pose proof (top_of_guarded _ _ _ _ _ _ _ _ _ _ _ (SRomStable.frm_safe_run_segments _ inp asp amb frm_safe_Ma0)
                (TGT0 asp abrk amb arnd inp Hasp Habrk Hamb Hafit Halau Hvl Hvi)) as TGT.
  split; [| split].
  - eapply srealizes_error_free; exact SRC.
  - eapply srealizes_error_free; exact TGT.
  - intro tr.
    rewrite (srealizes_traces_iff cfg0 _ _ _ _ _ _ _ _ _ _ tr SRC).
    rewrite (srealizes_traces_iff cfg0 _ _ _ _ _ _ _ _ _ _ tr TGT).
    reflexivity.
Qed.

End FPX_1.
