(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import ShapeAlg.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import ITree Nodes.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require Import TopLevel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import HaltsTrace.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Cfg.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_HaltsShape () := "C4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic7f_equalC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List8nil_consC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib4Init9Datatypes3appC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufI59OSSVerify5KrLib2AS8ShapeAlg8realizes00C1?~~~~~~~~~~~~~~~i59OSSVerify5KrLib4LibA:HaltsShape6mreach00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00C59OSSVerify5KrLib2AS8ShapeAlg7node_okC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to01I4ELinuxProcessSemantics?LinuxProcessSem3Run5sstep00I47Corelib4Init5Logic2eq00I47Corelib4Init5Logic2ex00K47Corelib4Init5Logic2ex01K47Corelib4Init5Logic2eq01k59OSSVerify5KrLib4LibA:HaltsShape6mreach02C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem3Run9cfg_modelC4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedK47Corelib4Init9Datatypes6option02C47Corelib4Init5Logic3notk59OSSVerify5KrLib4LibA:HaltsShape6mreach01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8ShapeAlg4t_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8ShapeAlg<realizes_indC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00I4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to00I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00C59OSSVerify5KrLib2AS8ShapeAlg4TSetC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib2AS8ShapeAlg8realizes01C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00K47Corelib7Numbers7BinNums8positive03C4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsK47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes6option01I47Corelib4Init9Datatypes4prod00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C4ELinuxProcessSemantics?LinuxProcessSem3Run?mi_account_stepK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingC4ELinuxProcessSemantics?LinuxProcessSem3RunKmi_account_step_model_frameC4ELinuxProcessSemantics?LinuxProcessSem5State4m_fdC4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC4ELinuxProcessSemantics?LinuxProcessSem5State4m_ioC4ELinuxProcessSemantics?LinuxProcessSem5State6m_fsysC4ELinuxProcessSemantics?LinuxProcessSem5State6m_procC4ELinuxProcessSemantics?LinuxProcessSem5State5m_limC4ELinuxProcessSemantics?LinuxProcessSem5State=procst_haltedC47Corelib4Init5Logic9False_indK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C4ELinuxProcessSemantics?LinuxProcessSem3Run9sys_inputC4ELinuxProcessSemantics?LinuxProcessSem5StateGsyscall_effect_accessesC4ELinuxProcessSemantics?LinuxProcessSem5StateJmaterialize_model_accessesC4ELinuxProcessSemantics?LinuxProcessSem3Run<apply_effectC4ELinuxProcessSemantics?LinuxProcessSem5StatePmaterialize_model_accesses_frameC4ELinuxProcessSemantics?LinuxProcessSem5State8m_killedK47Corelib4Init5Logic3and01K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02K4ELinuxProcessSemantics?LinuxProcessSem5Monad7outcome02C4ELinuxProcessSemantics?LinuxProcessSem5Specs<syscall_specK4ELinuxProcessSemantics?LinuxProcessSem5State5event03K47Corelib4Init9Datatypes4list02K4ELinuxProcessSemantics?LinuxProcessSem5State5event04I47Corelib4Init5Logic2or00K47Corelib4Init9Datatypes4prod01K4ELinuxProcessSemantics?LinuxProcessSem5Monad7outcome01C4ELinuxProcessSemantics?LinuxProcessSem3Run@advance_past_svcI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I4ELinuxProcessSemantics?LinuxProcessSem5State7FdState00I4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00I4ELinuxProcessSemantics?LinuxProcessSem5State8LimState00I4ELinuxProcessSemantics?LinuxProcessSem5State9ProcState00I4ELinuxProcessSemantics?LinuxProcessSem5State7IoState00I4ELinuxProcessSemantics?LinuxProcessSem5State7FsState00K4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to02K47Corelib4Init5Logic4True01I4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect00I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00I4ELinuxProcessSemantics?LinuxProcessSem3Run4star00C46Stdlib5Lists4List2InI4ELinuxProcessSemanticsEEquivalenceDefinition8MustExit?must_exit_in_at00C4ELinuxProcessSemantics?LinuxProcessSem3Run8star_oneC4ELinuxProcessSemantics?LinuxProcessSem3Run:star_transC47Corelib4Init5Logic6eq_symC47Corelib4Init5Logic8eq_transc59OSSVerify5KrLib4LibA:HaltsShapeAsstep_into_haltedC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9app_assocK4ELinuxProcessSemanticsEEquivalenceDefinition8MustExit?must_exit_in_at01K4ELinuxProcessSemanticsEEquivalenceDefinition8MustExit?must_exit_in_at02c59OSSVerify5KrLib4LibA:HaltsShape:mreach_indC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run4star01c59OSSVerify5KrLib4LibA:HaltsShape?realizes_mreachC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS8ShapeAlgBrealizes_star_onlyC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4LibA:HaltsShape@mreach_must_exitC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemanticsEEquivalenceDefinition8MustExitCmust_exit_in_at_cfg00C4ELinuxProcessSemanticsEEquivalenceDefinition8MustExitLmust_exit_in_at_cfg_may_failc59OSSVerify5KrLib4LibA:HaltsShapeBrealizes_must_exitC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C4ELinuxProcessSemantics?LinuxProcessSem3Run<may_fail_cfgC59OSSVerify5KrLib4LibA:HaltsTraceDtree_traces_exit_anyC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA:HaltsTraceEtree_traces_no_killevC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8TopLevel;tree_tracesC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5ITree5itree00C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3iffI59OSSVerify5KrLib3Lib5Nodes4node00C1?~~~~~~~~~~~~~~~C5ELinuxProcessSemanticsEEquivalenceDefinition<HaltsAllowed7AnyExit5codes".
Import ListNotations.

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
Inductive mreach : config -> Prop :=
| mr_halted : forall c, m_halted (cfg_model c) <> None -> mreach c
| mr_run : forall c,
    (exists evs st, sstep_cfg segs ACFG c evs st) ->
    (forall evs st, sstep_cfg segs ACFG c evs st -> exists c', st = SNext c') ->
    (forall evs c', sstep_cfg segs ACFG c evs (SNext c') -> mreach c') ->
    mreach c.

Lemma realizes_mreach : forall c T, realizes segs c T -> mreach c.
Proof using Type.
  intros c T H; induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq].
  - destruct Hnode as [Hcomp Hsound]. apply mr_run.
    + exists (evs i0), (SNext (nx i0)). apply Hcomp.
    + intros e st Hss. destruct (Hsound e st Hss) as (i & -> & ->). exists (nx i). reflexivity.
    + intros e c' Hss. destruct (Hsound e (SNext c') Hss) as (i & -> & E). injection E as ->. apply IH.
  - apply mr_halted. exact Hh.
  - exact IH.
Qed.

(* [comment removed for export] *)
Lemma sstep_into_halted : forall c evs c',
  sstep_cfg segs ACFG c evs (SNext c') -> m_halted (cfg_model c') <> None ->
  (exists evs0 code, evs = evs0 ++ [ExitEv code (m_fs (cfg_model c'))]
                     /\ m_halted (cfg_model c') = Some code /\ m_killed (cfg_model c') = None)
  \/ (exists evs0 sig, evs = evs0 ++ [KillEv sig (m_fs (cfg_model c'))]).
Proof using Type.
  intros c evs c' H Hh. inversion H; subst; cbn [cfg_model] in *.
  - exfalso. apply Hh. match goal with Ha : mi_account_step _ _ _ = MachineOk _ |- _ =>
      destruct (mi_account_step_model_frame _ _ _ _ _ Ha) as (_ & _ & _ & _ & _ & Hp & _) end.
    unfold m_halted in *. rewrite Hp. assumption.
  - exfalso. apply Hh. match goal with Hm : materialize_model_accesses _ _ = Some _ |- _ =>
      destruct (materialize_model_accesses_frame _ _ _ Hm) as (_ & _ & _ & _ & _ & Hp & _) end.
    unfold m_halted in *. rewrite Hp. assumption.
  - left. eexists _, _. split; [reflexivity|]. split; assumption.
  - right. eexists _, _. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma mreach_must_exit : forall (S : list word) c0 tr c,
  star_cfg segs ACFG c0 tr c -> m_halted (cfg_model c) = None -> mreach c ->
  (forall tr1 sig fs c1, star_cfg segs ACFG c0 (tr1 ++ [KillEv sig fs]) c1 -> False) ->
  (forall tr1 code fs c1, star_cfg segs ACFG c0 (tr1 ++ [ExitEv code fs]) c1 -> In code S) ->
  must_exit_in_at_cfg ACFG segs S c.
Proof using Type.
  intros S c0 tr c Hstar Hh Hm NK CS. revert tr Hstar Hh.
  induction Hm as [c Hh' | c Hex Hsafe Hall IH]; intros tr Hstar Hh; [congruence|].
  apply must_exit_in_at_cfg_running.
  - exact Hh.
  - exact Hex.
  - intros evs Hss. destruct (Hsafe evs SError Hss) as (c' & Hc'). discriminate.
  - intros evs c' Hss.
    pose proof (star_cfg_trans segs ACFG _ _ _ _ _ Hstar (star_cfg_one segs ACFG _ _ _ Hss)) as Hstar'.
    destruct (m_halted (cfg_model c')) as [code|] eqn:Hh2.
    + destruct (sstep_into_halted c evs c' Hss ltac:(congruence))
        as [(evs0 & code' & -> & Hcode & Hk) | (evs0 & sig & ->)].
      * rewrite app_assoc in Hstar'. apply (must_exit_in_at_cfg_halted _ _ _ _ code'); [exact Hcode | exact (CS _ _ _ _ Hstar') | exact Hk].
      * rewrite app_assoc in Hstar'. destruct (NK _ _ _ _ Hstar').
    + exact (IH evs c' Hss (tr ++ evs) Hstar' Hh2).
Qed.

(* [comment removed for export] *)
Theorem realizes_must_exit : forall (S : list word) c T,
  realizes segs c T ->
  m_halted (cfg_model c) = None ->
  (forall tr sig fs, ~ T (tr ++ [KillEv sig fs])) ->
  (forall tr code fs, T (tr ++ [ExitEv code fs]) -> In code S) ->
  must_exit_in_at_cfg ACFG segs S c.
Proof using Type.
  intros S c T HR Hh NK CS.
  apply (mreach_must_exit S c [] c (star_cfg_refl _ _ _) Hh (realizes_mreach c T HR)).
  - intros tr1 sig fs c1 Hstar. exact (NK _ _ _ (realizes_star_only segs c T HR _ _ Hstar)).
  - intros tr1 code fs c1 Hstar. exact (CS _ _ _ (realizes_star_only segs c T HR _ _ Hstar)).
Qed.

(* [comment removed for export] *)
Corollary realizes_must_exit_cfg : forall (S : list word) c T,
  realizes segs c T -> m_halted (cfg_model c) = None ->
  (forall tr sig fs, ~ T (tr ++ [KillEv sig fs])) ->
  (forall tr code fs, T (tr ++ [ExitEv code fs]) -> In code S) ->
  must_exit_in_at_cfg ACFG segs S c.
Proof using Type. intros. eapply realizes_must_exit; eauto. Qed.

(* [comment removed for export] *)
Theorem realizes_must_exit_tree : forall {R : Type} (t : itree node R) mo c T,
  realizes segs c T -> m_halted (cfg_model c) = None ->
  (forall tr, T tr <-> tree_traces t mo tr) ->
  must_exit_in_at_cfg ACFG segs AnyExit.codes c.
Proof using Type.
  intros R t mo c T HR Hh HT. apply (realizes_must_exit AnyExit.codes c T HR Hh).
  - intros tr sig fs H. apply HT in H. exact (tree_traces_no_killev t mo tr sig fs H).
  - intros tr code fs H. apply HT in H. exact (tree_traces_exit_any t mo tr code fs H).
Qed.

End WithSegs.
