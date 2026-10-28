(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim StrFun Stdio SjModel AtpModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTape.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Atp_h_defs.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow Sj_num_adefs Sj_num_fc_top6.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface2 RT_iface3 RT_iface5 RT_state RT_rep RT_artfacts RT_rtf RT_cli RT_livefresh RT_win TopA_iodefs. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import D_defs D_kit D_clx D_libiface D_auxv Sj_rtf Sj_akit Sj_acps Sj_hkit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_new Sj_stage1_defs Sj_stage1 Sj_h_alloc Sj_h_dtor Sj_h_deldtor Sj_h_setmd Sj_stage2_iface Sj_stage2_world Sj_stage2_closed. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_num_iface Sj_num_fc_stmt Sj_num_closed. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_stage2_numaw Sj_stage2_numow Sj_stage2_numrw. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_fzwA Atp_parseA Atp_pid_s1zA Atp_pid_parse0A Atp_createA Atp_setcapA Atp_activewA Atp_activeA Atp_defsA Atp_h_defsA Atp_pidiA Atp_pidA Atp_pid0A Atp_pdtorA Pj_defsA Pj_os_defsA El_defsA El_phasesA El_frontA El_topA El_tailA El_vecA El_dispA El_parsekA El_parse3A Pj_os_ctorA Pj_loc_topA Pj_mciRTA El_osdtorA El_sncA El_snc2A El_sitesA El_osdtorA El_arm0A El_arm1A El_arm5A El_armaccA El_arm19A El_arm20A El_arm21A El_arm22A El_arm23A El_arm24A El_arm25A El_arm26A El_arm28A El_arm30A El_arm31A.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A.Shadow.GWf.
Open Scope Z_scope.

Lemma outside_el_lib_fp : forall a, outside LIB_FP a -> outside EL_LIB_FP a.
Proof.
  intros a H. unfold EL_LIB_FP. pose proof H as H'. unfold LIB_FP in H'. cbn [outside app] in H' |- *.
  unfold EL_UNW_A, EL_EHG_A, EL_TPLOC_A, TPV_A.
  destruct H' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & U & E & T & _).
  induction LIB_FP as [|[l h] L IH]; cbn [outside]; [repeat split; try exact I; lia|].
  cbn [outside] in H. destruct H as [H1 H2]. split; [exact H1| exact (IH H2)].
Qed.

Lemma fuzz_one_cps_of_E : forall (RT : rt_sig) (LIB : mem -> Prop), fuzz_one_cpsE RT LIB -> fuzz_one_cps RT LIB.
Proof.
  intros RT LIB H Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m d bs lo.
  intros. specialize (H Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m d bs lo).
  eapply cps_conseq; [eapply H; eassumption| intros c Hc; exact Hc|].
  intros c [(Σ' & HA & REST) FR]. split; [| exact FR]. exists Σ'. split; [| exact REST].
  eapply ASTA_conseq; [exact HA|]. intros ms (m' & RS & RA & PR & LB). exists m'. split; [exact RS|]. split; [exact RA|]. split; [| exact LB].
  intros x Hx Ho. exact (PR x Hx (outside_el_lib_fp _ Ho)).
Qed.

Lemma cli_vt_dpi : forall m, cli_ro m -> vt_dpi m.
Proof. intros m H. apply (cli_ro_at m); [exact H| cli_in]. Qed.

Lemma cli_os_ro : forall m, cli_ro m -> pj_os_roA m.
Proof. intros m H. unfold pj_os_roA. split; [| split; [| split]]; (apply (cli_ro_at m); [exact H| cli_in]). Qed.

Section ClientEl.
Hypothesis RC2 : rt_contracts2 RTA.
Hypothesis RC5 : rt_contracts5 RTA.

Hypothesis WCLI : forall c Σ m, ARTW RTA (rc5_win RTA RC5) c Σ m -> cli_ro m.

Definition rta_af : art_facts RTA := rta_art_facts.
Definition rta_rc : rt_contracts RTA := rc2_rt RTA RC2.
Definition rta_rtf : rt_contracts_f RTA := rtf_of_rt RTA rta_rc.

Definition WA : Z -> rts RTA -> mem -> Prop := ARTW RTA (rc5_win RTA RC5).

Hypothesis X22 : forall PMc pcs, throw_siteB RTA PMc WA 22 pcs.
Hypothesis X23 : forall PMc, throw_siteB RTA PMc WA 23 0xb2fb4.
Hypothesis X24 : forall PMc, throw_siteB RTA PMc WA 24 EL_SITE_END_B.
Hypothesis DUMP : forall PMc, dump_cpsA RTA PMc.

Definition SNCW : sncW_stmt RTA := sncW_of_icontractB RTA (rc5_strncasecmp RTA RC5).
Definition SNC0 : snc0_stmt RTA := snc0_of_icontract0B RTA (rc5_strncasecmp0 RTA RC5).

Definition rta_new1 : new_cps RTA e_new_nt := new_nt_ok RTA rta_af (rf_malloc RTA rta_rtf).
Definition rta_newa : new_cps RTA e_newarr_nt := newarr_nt_ok RTA rta_af (rf_malloc RTA rta_rtf).
Definition rta_dela : del_cps RTA e_delarr := delarr_ok RTA rta_af (rf_free RTA rta_rtf).
Definition rta_del1 : del_cps RTA e_del := del_ok RTA rta_af (rf_free RTA rta_rtf).

Lemma rta_fca : forall PMc, fdfs_only PMc -> mat_stable PMc -> fca_stmt RTA PMc.
Proof. exact (fca_closed RTA rta_af rta_rtf). Qed.
Lemma rta_slowfa : slowfa_cps RTA.
Proof. exact (slowfa_closed RTA rta_af rta_rtf rta_fca). Qed.
Lemma rta_pffa : pffa_cps RTA.
Proof. exact (pffa_closed RTA rta_af rta_rtf rta_fca). Qed.
Lemma rta_numa : numa_stmt RTA.
Proof. exact (numa_world RTA rta_af rta_slowfa rta_pffa). Qed.
Lemma rta_numo : numo_stmt RTA.
Proof. exact (numo_world RTA rta_af rta_slowfa rta_pffa). Qed.
Lemma rta_rootnum : rootnum_stmt RTA.
Proof. exact (rootnum_world RTA rta_af rta_rtf rta_slowfa rta_pffa (fun Σ m HA => rta_got_nothrow Σ m HA) rta_live_fresh). Qed.
Lemma rta_stage2at : stage2at_cps RTA.
Proof. exact (stage2at_closed RTA rta_af rta_rtf rta_numa rta_numo rta_rootnum). Qed.
Lemma rta_stage1 : stage1_cps RTA.
Proof. exact (stage1_ok RTA rta_af (rf_asan_memcpy RTA rta_rtf)). Qed.
Lemma rta_parse : parse_cps RTA.
Proof. exact (parse_ok RTA rta_af rta_stage1 rta_stage2at). Qed.
Lemma rta_create : create_cps RTA.
Proof.
  exact (create_ok RTA rta_af rta_new1 (rf_asan_memset RTA rta_rtf)
           (setcap_ok RTA rta_af rta_newa (fun Σ m HA => rta_got_nothrow Σ m HA))
           (setmd_ok RTA rta_af rta_newa (fun Σ m HA => rta_got_nothrow Σ m HA))
           (fun Σ m HA => rta_got_nothrow Σ m HA) (fun Σ m HA => rta_vt_dpi Σ m HA)).
Qed.
Lemma rta_alloc : allocate_cps RTA.
Proof. exact (allocate_ok RTA rta_af rta_newa (fun Σ m HA => rta_got_nothrow Σ m HA)). Qed.
Lemma rta_docd : docdtor_cps RTA.
Proof. exact (docdtor_ok RTA rta_af rta_dela). Qed.
Lemma rta_deld : deldtor_cps RTA.
Proof. exact (deldtor_ok RTA rta_af rta_dela rta_del1). Qed.

Lemma rta_pid : pid_cps RTA sj_lib.
Proof. exact (pid_ok RTA rta_af rta_rtf rta_parse rta_alloc rta_create (fun Σ m HA => rta_vt_dpi Σ m HA) (fun Σ m HA => rta_vt_impl Σ m HA)). Qed.
Lemma rta_pid0 : pid0_cps RTA sj_lib.
Proof.
  exact (pid0_ok RTA rta_af rta_rtf (parse0_ok RTA rta_af (stage1z_ok RTA rta_af (rf_asan_memcpy RTA rta_rtf))) rta_alloc rta_create
           (fun Σ m HA => rta_vt_dpi Σ m HA) (fun Σ m HA => rta_vt_impl Σ m HA)).
Qed.
Lemma rta_pdtor : pdtor_cps RTA (pdone RTA).
Proof. exact (pdtor_ok RTA rta_af rta_docd rta_deld (fun Σ m HA => rta_vt_dpi Σ m HA)). Qed.

Section Win.
Variable c : Z.
Let SW : rt_sig := rt_sigW RTA (WA c).
Definition w_af : art_facts SW := w_facts RTA (rc5_win RTA RC5) c.
Definition w_rcw : rt_contracts SW := w_rc RTA (rc5_win RTA RC5) c.
Definition w_rc2w : rt_contracts2 SW := w_rc2 RTA (rc5_win RTA RC5) c.
Definition w_rtfw : rt_contracts_f SW := rtf_of_rt SW w_rcw.
Lemma w_vt_dpi : forall Σ m, ART SW Σ m -> vt_dpi m.
Proof. intros Σ m HA. exact (cli_vt_dpi m (WCLI c Σ m HA)). Qed.
Lemma w_pdtor : pdtor_cps SW (pdone SW).
Proof.
  exact (pdtor_ok SW w_af (docdtor_ok SW w_af (delarr_ok SW w_af (rf_free SW w_rtfw)))
           (deldtor_ok SW w_af (delarr_ok SW w_af (rf_free SW w_rtfw)) (del_ok SW w_af (rf_free SW w_rtfw))) w_vt_dpi).
Qed.
End Win.

Theorem rta_loc : forall PMc, loc_get_cpsA RTA PMc.
Proof. intros PMc. pose proof (loc_get_okA RTA rta_af rta_rc rta_memcmp_inner PMc) as H. unfold loc_get_cpsA in *. intros; eapply H; eassumption. Qed.
Theorem rta_ctor : forall PMc, ctor_cpsA RTA PMc OSFRESHA.
Proof.
  intros PMc. pose proof (fun FDO MST => ctor_okA RTA rta_af rta_rc PMc FDO MST (fun Σ m HA => cli_os_ro m (rta_cli_ro Σ m HA)) (rta_loc PMc)) as H.
  unfold ctor_cpsA in *. intros; eapply H; eassumption.
Qed.
Theorem rta_osdtor : forall PMc, osdtor_cps2A RTA PMc.
Proof. intros PMc. exact (osdtor_okA RTA rta_af rta_rc PMc (fun Σ m HA => cli_os_ro m (rta_cli_ro Σ m HA))). Qed.

Lemma rta_arms : forall PMc a, el_liveA a = true -> arm_cpsA RTA PMc WA a.
Proof.
  intros PMc a Ha. unfold el_liveA in Ha.
  apply andb_prop in Ha. destruct Ha as [Ha N27]. apply andb_prop in Ha. destruct Ha as [H0 H32]. apply Z.leb_le in H0. apply Z.ltb_lt in H32.
  assert (A27 : a <> 27) by (intros ->; discriminate N27).
  assert (C : a = 0 \/ a = 1 \/ a = 2 \/ a = 3 \/ a = 4 \/ a = 5 \/ a = 6 \/ a = 7 \/ a = 8 \/ a = 9 \/ a = 10 \/ a = 11 \/ a = 12 \/ a = 13 \/ a = 14 \/ a = 15
              \/ a = 16 \/ a = 17 \/ a = 18 \/ a = 19 \/ a = 20 \/ a = 21 \/ a = 22 \/ a = 23 \/ a = 24 \/ a = 25 \/ a = 26 \/ a = 28 \/ a = 29 \/ a = 30 \/ a = 31) by lia.
  clear N27 H0 H32 A27.
  decompose [or] C; subst a;
    [ exact (arm0_okA RTA rta_af PMc WA)| exact (arm1_okA RTA rta_af rta_rc PMc WA)| exact (arm2_okA RTA rta_af rta_rc PMc WA)
    | exact (arm3_okA RTA rta_af PMc WA)| exact (arm4_okA RTA rta_af PMc WA)| exact (arm5_okA RTA rta_af rta_rc PMc WA)
    | exact (arm6_okA RTA rta_af PMc WA)| exact (arm7_okA RTA rta_af PMc WA)| exact (arm8_okA RTA rta_af PMc WA)
    | exact (arm9_okA RTA rta_af PMc WA)| exact (arm10_okA RTA rta_af PMc WA)| exact (arm11_okA RTA rta_af PMc WA)
    | exact (arm12_okA RTA rta_af rta_rc PMc WA)| exact (arm13_okA RTA rta_af PMc WA)| exact (arm14_okA RTA rta_af PMc WA)
    | exact (arm15_okA RTA rta_af PMc WA)| exact (arm16_okA RTA rta_af PMc WA)| exact (arm17_okA RTA rta_af PMc WA)
    | exact (arm18_okA RTA rta_af PMc WA)| exact (arm19_okA RTA rta_af rta_rc PMc WA)| exact (arm20_okA RTA rta_af rta_rc PMc WA)| exact (arm21_okA RTA rta_af rta_rc PMc WA)
    | exact (arm22_okA RTA rta_af rta_rc PMc WA (X22 PMc))
    | exact (arm23_okA RTA rta_af PMc WA (X23 PMc))| exact (arm24_okA RTA rta_af rta_rc PMc WA (X24 PMc))
    | exact (arm25_okA RTA rta_af rta_rc RC2 PMc WA)| exact (arm26_okA RTA rta_af RC2 PMc WA)| exact (arm28_okA RTA rta_af rta_rc PMc WA)
    | exact (arm29_okA RTA rta_af rta_rc RC2 PMc WA)| exact (arm30_okA RTA rta_af rta_rc RC2 SNCW SNC0 PMc WA)
    | exact (arm31_okA RTA rta_af PMc (rta_ctor PMc) (DUMP PMc) (rta_osdtor PMc) WA) ].
Qed.

Theorem rta_fuzz_one_el : fuzz_one_cps RTA el_libA.
Proof.
  apply fuzz_one_cps_of_E.
  exact (fuzz_one_elA RTA rta_af rta_rc WA (w_exit RTA (rc5_win RTA RC5))
           (el_vec_ok RTA rta_af RC2)
           (el_parse_ok RTA rta_af RC2 rta_pid rta_pid0 (fun Σ m HA => rta_got_nothrow Σ m HA))
           (fun PMc => el_disp_ok RTA rta_af WA PMc)
           (el_tailP_ok RTA rta_af rta_pdtor)
           (el_tail2_ok RTA rta_af rta_rc RC2)
           (fun c => el_tailP_ok (rt_sigW RTA (WA c)) (w_af c) (w_pdtor c))
           (fun c => el_tail2_ok (rt_sigW RTA (WA c)) (w_af c) (w_rcw c) (w_rc2w c))
           rta_arms).
Qed.
End ClientEl.
