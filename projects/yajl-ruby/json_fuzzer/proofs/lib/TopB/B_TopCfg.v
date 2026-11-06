(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import base.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling PropExec MState Mem Cells Frame Arr Nodes NodesCfg InitMem RunInit Images.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import AImages AImageFacts ExecA LazyModel NodesA ImplRzA Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim StdioBase Stdio.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass AsanState AsanLayout AsanOps AsanFakeStack AsanPS AsanRep AsanKern AsanClient AsanBudget AsanBudget2 AsanDepot AsanGap AsanSlack.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import B_base B_alloc_iface B_iface B_iface5x BF_unwind BF_fakestack_rep B_live B_policy5 B_budget5 B_slack5 B_bundle B_benv5 B_init5 B_instD5 B_inst5 BDrv_ctx BDrv_A BDrv_E BF_alloc_iface BF_free_iface BF_mallocT2 BF_reallocT BF_freeT2 BF_dput_iface.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Top Require Import SpecT GlueCfg RunInitCfg R_TopCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.TopB Require Import B_MainMS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
#[warnings="-notation-for-abbreviation"] Notation mem := (word -> option byte).

(* [comment removed for export] *)
(* [comment removed for export] *)

Section RC__1.
Context {RC__ : RunCeiling}.
#[local] Notation gpv := (Z_to_bv 64 0x10800).
#[local] Notation tpv := (Z_to_bv 64 0x5e1550).
End RC__1.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section TopB.

  (* [comment removed for export] *)
  Hypothesis B_MAIN_REACH : forall (en : ExecEntry) (inp : ProcInput) (T : TSet),
    let RC := rc_of en in
    valid_entry (mkImage bsegs b_init_pc b_phdrs) en inp -> valid_input inp -> T [] ->
    (forall (E0 : aenv) (FSB0 : Z) (PL0 : fs_plumb) (HR0 : list (Z * Z)) (L0 RES0 : list (word * word)) (EB0 : Z)
            (FULL : mem) (model : Model) (ms : machine_state),
        env0_ok5 E0 -> pl0_ok5 E0 PL0 -> main_facts5 FULL model E0 FSB0 PL0 HR0 L0 RES0 EB0 ->
        m_fs model = in_fs inp -> m_fds model = dfds_std ->
        main_ms (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en) FULL ms ->
        realizes_cfg acfg bsegs (mkCfg ms model) T) ->
    realizes_cfg acfg bsegs
      (init_config bsegs b_init_pc b_phdrs (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en) target_alloc_limit inp) T.

  (* [comment removed for export] *)
  #[local] Notation uanchorc := (BF_unwind.uanchor bsegs).
  (* [comment removed for export] *)
  Hypothesis ALLOC : forall (RC__ : RunCeiling) E0 FSB0 PL0 HR0 L0 RES0 EB0,
    env0_ok5 E0 -> pl0_ok5 E0 PL0 -> Forall (fun iv => fst iv <= snd iv) HR0 /\ A0_pages HR0 <= 8192 -> 0 <= EB0 <= 2^32 ->
    zlen (ae_keys0 E0) <= 1000 /\ 0 <= ae_frames0 E0 <= 4096 -> gw_sizes (RES0 ++ L0) <= 2^46 /\ (length (RES0 ++ L0) <= 256)%nat ->
    l0_ok5 E0 L0 RES0 ->
    allocate_srz_stmt E0 FSB0 HR0 L0 RES0 EB0 PL0.
  (* [comment removed for export] *)
  Hypothesis DEALLOC : forall (RC__ : RunCeiling) E0 FSB0 PL0 HR0 L0 RES0 EB0,
    env0_ok5 E0 -> pl0_ok5 E0 PL0 -> Forall (fun iv => fst iv <= snd iv) HR0 /\ A0_pages HR0 <= 8192 -> 0 <= EB0 <= 2^32 ->
    zlen (ae_keys0 E0) <= 1000 /\ 0 <= ae_frames0 E0 <= 4096 -> gw_sizes (RES0 ++ L0) <= 2^46 /\ (length (RES0 ++ L0) <= 256)%nat ->
    l0_ok5 E0 L0 RES0 ->
    dealloc_srz_stmt E0 FSB0 HR0 L0 RES0 EB0 PL0.
  (* [comment removed for export] *)
  Lemma W_malloc : forall (RC__ : RunCeiling) E0 FSB0 PL0 HR0 L0 RES0 EB0,
    env0_ok5 E0 -> pl0_ok5 E0 PL0 -> Forall (fun iv => fst iv <= snd iv) HR0 /\ A0_pages HR0 <= 8192 -> 0 <= EB0 <= 2^32 ->
    zlen (ae_keys0 E0) <= 1000 /\ 0 <= ae_frames0 E0 <= 4096 -> gw_sizes (RES0 ++ L0) <= 2^46 /\ (length (RES0 ++ L0) <= 256)%nat ->
    l0_ok5 E0 L0 RES0 ->
    amalloc_rz_stmt bsegs ACONSTS aps (AHKc E0 FSB0 PL0 HR0 L0 RES0 EB0) aps_so (amalloc_rel E0) aps_credit acharge uanchorc.
  Proof. intros. eapply malloc_contract; eauto. Qed.
  Lemma W_free : forall (RC__ : RunCeiling) E0 FSB0 PL0 HR0 L0 RES0 EB0,
    env0_ok5 E0 -> pl0_ok5 E0 PL0 -> Forall (fun iv => fst iv <= snd iv) HR0 /\ A0_pages HR0 <= 8192 -> 0 <= EB0 <= 2^32 ->
    zlen (ae_keys0 E0) <= 1000 /\ 0 <= ae_frames0 E0 <= 4096 -> gw_sizes (RES0 ++ L0) <= 2^46 /\ (length (RES0 ++ L0) <= 256)%nat ->
    l0_ok5 E0 L0 RES0 ->
    afree_rz_stmt bsegs ACONSTS aps (AHKc E0 FSB0 PL0 HR0 L0 RES0 EB0) aps_so (afree_rel E0) aps_credit arefund uanchorc.
  Proof. intros. eapply free_contract; eauto using DEALLOC. Qed.
  Lemma W_realloc : forall (RC__ : RunCeiling) E0 FSB0 PL0 HR0 L0 RES0 EB0,
    env0_ok5 E0 -> pl0_ok5 E0 PL0 -> Forall (fun iv => fst iv <= snd iv) HR0 /\ A0_pages HR0 <= 8192 -> 0 <= EB0 <= 2^32 ->
    zlen (ae_keys0 E0) <= 1000 /\ 0 <= ae_frames0 E0 <= 4096 -> gw_sizes (RES0 ++ L0) <= 2^46 /\ (length (RES0 ++ L0) <= 256)%nat ->
    l0_ok5 E0 L0 RES0 ->
    arealloc_rz_stmt bsegs ACONSTS aps (AHKc E0 FSB0 PL0 HR0 L0 RES0 EB0) aps_so (arealloc_rel E0) aps_credit acharge arefund uanchorc.
  Proof. intros. eapply realloc_contract; eauto using DEALLOC. Qed.
  Lemma W_realloc0 : forall (RC__ : RunCeiling) E0 FSB0 PL0 HR0 L0 RES0 EB0,
    env0_ok5 E0 -> pl0_ok5 E0 PL0 -> Forall (fun iv => fst iv <= snd iv) HR0 /\ A0_pages HR0 <= 8192 -> 0 <= EB0 <= 2^32 ->
    zlen (ae_keys0 E0) <= 1000 /\ 0 <= ae_frames0 E0 <= 4096 -> gw_sizes (RES0 ++ L0) <= 2^46 /\ (length (RES0 ++ L0) <= 256)%nat ->
    l0_ok5 E0 L0 RES0 ->
    arealloc_null_rz_stmt bsegs ACONSTS aps (AHKc E0 FSB0 PL0 HR0 L0 RES0 EB0) aps_so (arealloc_rel E0) aps_credit acharge uanchorc.
  Proof. intros. eapply realloc_null_contract; eauto using DEALLOC. Qed.

  (* [comment removed for export] *)
  Lemma b_main_rz : forall (en : ExecEntry) (inp : ProcInput),
    let RC := rc_of en in
    valid_entry (mkImage bsegs b_init_pc b_phdrs) en inp -> valid_input inp ->
    forall (E0 : aenv) (FSB0 : Z) (PL0 : fs_plumb) (HR0 : list (Z * Z)) (L0 RES0 : list (word * word)) (EB0 : Z)
           (FULL : mem) (model : Model) (ms : machine_state),
      env0_ok5 E0 -> pl0_ok5 E0 PL0 -> main_facts5 FULL model E0 FSB0 PL0 HR0 L0 RES0 EB0 ->
      m_fs model = in_fs inp -> m_fds model = dfds_std ->
      main_ms (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en) FULL ms ->
      realizes_cfg acfg bsegs (mkCfg ms model) (spec (in_argv inp) (in_fs inp)).
  Proof.
    intros en inp RC VE VI E0 FSB0 PL0 HR0 L0 RES0 EB0 FULL model ms ENV0 PL0OK MF MOFS MOFD MM.
    destruct (valid_entry_unpack _ _ _ _ _ VE VI) as (VSP & VBRK & _ & EFIT).
    destruct (valid_input_unpack _ VI) as (VA & VEN & _ & _).
    assert (RCSP : rc_sp = bv_unsigned (en_sp en)) by reflexivity.
    pose proof (MF_HR0_ok _ _ _ _ _ _ _ _ _ MF) as HR0_ok. pose proof (MF_EB0_ok _ _ _ _ _ _ _ _ _ MF) as EB0_ok.
    pose proof (MF_ENV_depot _ _ _ _ _ _ _ _ _ MF) as ENV_depot. pose proof (MF_HS_tot _ _ _ _ _ _ _ _ _ MF) as HS_tot.
    pose proof (MF_L0_ok _ _ _ _ _ _ _ _ _ MF) as L0_ok.
    set (D := DREC E0 FSB0 PL0 HR0 L0 RES0 EB0).
    assert (DI : a_drv_iface bsegs ACONSTS AFMTS D).
    { subst D. apply (B_inst5.DI E0 FSB0 PL0 HR0 L0 RES0 EB0 ENV0 PL0OK HS_tot);
        [apply W_malloc| apply W_free| apply W_realloc| apply W_realloc0]; assumption. }
    assert (DIx : a_drv_iface5x bsegs ACONSTS D).
    { subst D. exact (B_inst5.DIx5 E0 FSB0 PL0 HR0 L0 RES0 EB0 ENV0 PL0OK HS_tot). }
    destruct (AHK_birth5 FULL model E0 FSB0 PL0 HR0 L0 RES0 EB0 MF) as (AH0 & SO0 & CR0).
    eapply (a_main_spec (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en) VSP RCSP EFIT VA VEN D DI DIx
              model (in_fs inp) MOFS MOFD (aps_init E0 FSB0) ms).
    destruct MM as (t0 & t1 & t2 & a3 & a4 & a5 & a6 & a7 & s4 & s5 & s6 & s7 & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6 & F & fc & Ems & STK & MI & IMG & STAT & FRM).
    unfold AENTRY. exists t0, t1, t2, a3, a4, a5, a6, a7, s4, s5, s6, s7, s8, s9, s10, s11, t3, t4, t5, t6, F, fc, FULL.
    split; [exact Ems|]. split; [exact STK|]. split; [exact MI|]. split; [exact IMG|]. split; [exact STAT|]. split; [exact FRM|].
    split; [exact AH0|]. split; [exact SO0|]. subst D. cbn [p_AHEAD DREC]. apply AHEAD_init.
  Qed.

  Theorem B_realizes_spec_cfg :
    realizes_spec_cfg acfg bsegs b_init_pc b_phdrs target_alloc_limit (fun inp => spec (in_argv inp) (in_fs inp)).
  Proof.
    apply realizes_spec_cfg_intro. intros en inp VE VI.
    apply (B_MAIN_REACH en inp (spec (in_argv inp) (in_fs inp)) VE VI (spec_nil _ _)).
    intros E0 FSB0 PL0 HR0 L0 RES0 EB0 FULL model ms ENV0 PL0OK MF MOFS MOFD MM.
    exact (b_main_rz en inp VE VI E0 FSB0 PL0 HR0 L0 RES0 EB0 FULL model ms ENV0 PL0OK MF MOFS MOFD MM).
  Qed.
End TopB.
