(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: for LPS 727298f3, the top reads valid_input_either's clauses by type (vie_parts) in place of a positional destruct, the launch facts and the channel reader come from the premises, the run reads the binary's segments with the vDSO appended (lifted by SRomStable.srun_init), and the main phase takes the launch's kernel build, SIGPIPE disposition and the run's CONFIG_RSEQ flag. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Plain.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import ShapeAlg DivergeSim SpinAlg SpinAlgX ShapeEF Spec BigintSpec HeapIface LibIface.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.CJ.Bridge Require Import HeapInst0 HeapClosed.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import Src0DrvLibL Src0DrvG Src0DrvMain Src0HeapBridge BigintTop2 L5Top BigintFinal KillFree BigintBaseH BigintBaseS0.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import AsanAcct HeapIfaceA IcptIfaceAB0 LibIfaceA AsanInitK Bo0DefsK Bo0MainPhaseA.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require PropExec.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.Common.Cfg Require SRomStable.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section FPX_1.
#[local] Existing Instance PropExec.fx0.

(* [comment removed for export] *)
(* [Run.valid_input_either]'s clauses, read BY TYPE and not by position.  The
   predicate has fifteen conjuncts ([c0dd863a:theories/LinuxProcessSem/Run.v:4746-4757]), so a positional pattern can bind the wrong
   fact while still typechecking; destructing to depth and splitting to depth,
   as the model's own [valid_input_either_of_valid_input] does, reads each
   clause by its type.  [repeat split] is
   guarded for the reason given there: [valid_urandom] is coinductive.
   [in_sigpipe_default] is not among the clauses: the predicate leaves the
   launch's SIGPIPE disposition free ([727298f3:theories/LinuxProcessSem/
   Run.v:4636-4642]), and [as0_tgt_of_run] passes the input's own value. *)
Lemma vie_parts : forall inp, valid_input_either inp ->
  valid_argv (in_argv inp) /\ valid_envp (in_envp inp) /\ valid_fs (in_fs inp)
  /\ valid_creds inp /\ valid_hwcap (in_hwcap inp) /\ in_va_size inp = Sv48
  /\ in_channel_reader inp = true /\ in_sigpipe_terminal inp = false.
Proof.
  intros inp H. red in H.
  repeat match goal with G : _ /\ _ |- _ => destruct G end.
  repeat match goal with |- _ /\ _ => split end; assumption.
Qed.

(* [comment removed for export] *)
(* The input hypothesis is [Run.valid_input_either]: the clauses the two abort
   stances share, so both [valid_input] and [valid_input_abort] imply it
   ([valid_input_either_of_valid_input], [..._of_valid_input_abort]).  It
   carries the [State.ProcInput] fields [AsanInitK.inp] must match -- the
   kernel of record, the channel reader and the SIGPIPE death declaration ([in_sigpipe_terminal]).  The
   premise is discharged from the binder of the published statement below. *)
Definition as0_tgt_stmt (scfg : SpuriousCfg) : Prop :=
  forall sp brk mbase (rdraw : EntryDraw) (inp : ProcInput),
    valid_sp sp -> valid_brk AsanUbsan.M.loaded_segments brk -> valid_mmap_base mbase ->
    entry_stack_fits sp (in_argv inp) (in_envp inp) ->
    (* [Run.valid_entry_va]'s fifth conjunct and [valid_input_either]'s
       [valid_launch], both in the published binder: at LPS 727298f3 they pin the
       launch's stack block, which the ASan startup reads *)
    entry_launch_ok_va Sv48 (mkEntry sp brk mbase rdraw) inp -> valid_launch inp ->
    valid_input_either inp ->
    (* LPS 08b1429: the run reads the binary's segments with the run's vDSO appended
       ([Run.run_segments]); [SRomStable.srun_init] lifts the walk over the binary's own
       segments ([vdso_image] of them is [None] by computation), as [Src0DrvMain] does *)
    srealizes (run_segments AsanUbsan.M.loaded_segments inp sp mbase) scfg
      (init_config (run_segments AsanUbsan.M.loaded_segments inp sp mbase) AsanUbsan.M.init_pc AsanUbsan.M.phdrs sp brk mbase rdraw target_alloc_limit inp)
      (spec (in_argv inp) (in_fs inp)).

(* [comment removed for export] *)
Lemma as0_tgt_of_run : forall scfg,
  (forall sp brk0 mbase (rdraw : EntryDraw) (argv envp : list (list byte)) (fs : Fs.Fs) (stdin : InputStream) (uid gid hw : word) (groups : list word)
          (net : NetQueue) (nofile sigmask : word) (abrt sdf : bool) (ur : InputStream) (kb : KernelBuild) (execfn : list byte),
      valid_sp sp -> valid_brk ASEGS0 brk0 -> valid_mmap_base mbase -> valid_argv argv -> valid_envp envp -> entry_stack_fits sp argv envp ->
      entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) (AsanInitK.inp argv envp fs stdin uid gid hw groups net nofile sigmask abrt sdf ur kb execfn) ->
      valid_launch (AsanInitK.inp argv envp fs stdin uid gid hw groups net nofile sigmask abrt sdf ur kb execfn) ->
      valid_id uid -> valid_hwcap hw -> valid_fs fs ->
      srealizes ASEGS0 scfg (init_config ASEGS0 AsanUbsan.M.init_pc APH0 sp brk0 mbase rdraw AsanInitK.LIMIT
                                   (AsanInitK.inp argv envp fs stdin uid gid hw groups net nofile sigmask abrt sdf ur kb execfn))
                (spec argv fs)) ->
  as0_tgt_stmt scfg.
Proof.
  intros scfg RUN sp brk mbase rdraw inp Hsp Hbrk Hmb Hfit Hlau Hvl Hvi.
  apply (SRomStable.srun_init scfg AsanUbsan.M.loaded_segments inp sp mbase _ _ _ _ _ _ eq_refl).
  destruct (vie_parts inp Hvi) as (Hva & Hve & Hvfs & Hcreds & Hhw & Hsv & Hchrd & Hspt).
  pose proof (valid_input_either_recorded_kernel inp Hvi) as Hker. clear Hvi.
  destruct inp as [argv envp fs0 stdin0 uid gid groups net nofile sigmask hw abt va ur tmp kb exfn chrd spd spt].
  cbn [in_argv in_envp in_uid in_hwcap in_va_size in_fs in_image_fs in_tmp in_kernel
       in_channel_reader in_sigpipe_default in_sigpipe_terminal] in *.
  subst va chrd spt.
  destruct Hcreds as [Hu _]. cbn [in_uid] in Hu.
  (* the kernel of record: the statement's build is [recorded_kernel] of itself,
     which is the sixteenth place [AsanInitK.inp] writes. *)
  rewrite Hker in Hlau, Hvl |- *.
  (* [spd], the launch's SIGPIPE disposition, is the place [AsanInitK.inp]
     takes as its [sdf]: the run's own value, which nothing pins. *)
  exact (RUN sp brk mbase rdraw argv envp (fs_seed_tmp fs0 tmp)
             stdin0 uid gid hw groups net nofile sigmask abt spd ur kb exfn
             Hsp Hbrk Hmb Hva Hve Hfit Hlau Hvl Hu Hhw Hvfs).
Qed.

(* [comment removed for export] *)
Theorem fuzz_bigint_both_final_abort :
  as0_tgt_stmt cfg0 ->
  strong_universal_error_free_T_scfg_budgets_abort cfg0 ShippedBudgets.lim_source ShippedBudgets.lim_target
    (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs)
    (mkImage AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs).
Proof.
  intros TGT.
  pose proof (src0_realizes_spec_heap cfg0 eq_refl eq_refl
                (fun sp => L5Top.L5TOP.TopLay (HeapInst0.L0 (bv_unsigned sp)))
                (fun sp => L5Top.L5TOP.TopLS (HeapInst0.L0 (bv_unsigned sp)))
                drv_lib_layout_top0 (LIB0_of_divide OPMOD1_src0_ok OPMOD2_src0_ok) budget0) as SRC.
  intros [rsp rbrk rmb rrnd] [asp abrk amb arnd] inp Hens Hent Hvalid _.
  pose proof (valid_input_abort_va_size _ Hvalid) as Hsv48.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hens. rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent.
  destruct Hens as [Hrsp [Hrbrk [Hrmb [_ Hrlau]]]]. destruct Hent as [Hasp [Habrk [Hamb [Hafit Halau]]]].
  assert (Hvl : valid_launch inp) by (red in Hvalid; tauto).
  (* [valid_input_abort] is the published statement's own binder, so the
     [valid_input_either] premise is discharged from it and not invented. *)
  pose proof (valid_input_either_of_valid_input_abort inp Hvalid) as Hvi.
  destruct (vie_parts inp Hvi) as (Hargv & Henvp & Hfs & Hcreds & _ & _ & Hrd & _).
  specialize (SRC rsp rbrk rmb rrnd inp Hrsp Hrbrk Hrmb Hvl Hrlau Hargv Henvp Hfs Hcreds Hrd).
  specialize (TGT asp abrk amb arnd inp Hasp Habrk Hamb Hafit Halau Hvl Hvi).
  unfold ShippedBudgets.lim_source, ShippedBudgets.lim_target.
  split; [| split].
  - eapply srealizes_error_free_unkilled; [exact SRC | apply kill_free_spec].
  - eapply srealizes_error_free_unkilled; [exact TGT | apply kill_free_spec].
  - intro tr.
    rewrite (srealizes_traces_iff cfg0 _ _ _ _ _ _ _ _ _ _ tr SRC).
    rewrite (srealizes_traces_iff cfg0 _ _ _ _ _ _ _ _ _ _ tr TGT).
    reflexivity.
Qed.

(* [comment removed for export] *)
Theorem fuzz_bigint_both_base_abort_modulo :
  forall (L : asan_layout) (C : asan_statics_cells) (IL : icpt_layout) (Lay : lib_layoutA) (LSt : asan_run -> LibIface.lib_statics) (BUDGET : Z),
    2 ^ 34 <= BUDGET -> BUDGET <= 2 ^ 39 - 2 ^ 35 ->
    inst_ok_stmt cfg0 L C BUDGET -> free_null_stmt cfg0 L BUDGET -> h4e_stmt BUDGET -> icpt_ok_stmt cfg0 L IL BUDGET -> lib_ok_stmt cfg0 L C IL Lay LSt -> dla_ok_stmt cfg0 L C IL -> drv_consts_stmt L C IL ->
    drv_main_stmt cfg0 L C IL Lay LSt -> usage_stmt cfg0 ->
    strong_universal_error_free_T_scfg_budgets_abort cfg0 ShippedBudgets.lim_source ShippedBudgets.lim_target
      (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs)
      (mkImage AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs).
Proof.
  intros L C IL Lay LSt BUDGET B1 B2 H1 H1n H2 H3 H4 H5 H6 H7 H8.
  apply fuzz_bigint_both_final_abort. apply as0_tgt_of_run.
  intros sp brk0 mbase rdraw argv envp fs stdin uid gid hw groups net nofile sigmask abrt sdf ur kb execfn Hsp Hbrk Hmb Hva Hve Hfit Hlau Hvl Huid Hhw Hvfs.
  (* [Bo0MainPhaseA]'s section binds the CONFIG_RSEQ flag [r] and ties it by [HRZ];
     the run's own flag discharges it *)
  eapply (as0_realizes_spec_run cfg0 eq_refl eq_refl L C IL Lay LSt BUDGET B1 B2 H1 H1n H2 H3 H4 H5 H6 H7 H8);
    first [eassumption | reflexivity].
Qed.

End FPX_1.
