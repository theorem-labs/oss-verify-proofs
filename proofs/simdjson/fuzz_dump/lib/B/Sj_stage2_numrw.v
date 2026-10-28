(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList SjNumber.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout RT_iface D_defs D_kit D_clx Sj_akit Sj_acps Sj_hkit Sj_rtf Sj_num_iface Sj_num_akit Sj_new
  Sj_stage2_defs Sj_stage2_main Sj_stage2_world Sj_stage2_numw Sj_stage2_numrw0
  Sj_stage2_numkit Sj_stage2_numkit2 Sj_stage2_numkit2b Sj_stage2_numkit3 Sj_stage2_numr_defs Sj_stage2_numr_defs3 Sj_stage2_numr1 Sj_stage2_numr6 Sj_stage2_numr0 Sj_stage2_numr.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition live_fresh (RT : rt_sig) : Prop :=
  forall Σ m p n l, ART RT Σ m -> rt_live RT Σ = (p, n) :: l -> 0 < n -> forall e, In e l -> fst e <> p.

Section RootW.
  Variable RT : rt_sig.
  Hypothesis AF : art_facts RT.
  Variable PMc : Model -> Prop.
  Hypothesis FDO : fdfs_only PMc.
  Hypothesis MST : mat_stable PMc.
  Variable E0 : s2env.
  Hypothesis OK0 : env_ok E0.

  Hypothesis HT1 : Z.of_nat (length (e_tws E0)) = 1%Z.
  Variable K : config -> Prop.
  Variable w : WD RT.
  Hypothesis F0 : rootw_facts RT E0 w.
  Notation rl := (e_len E0 - e_off E0 0).
  Notation cc := (e_len E0 - e_off E0 0 + 64).
  Notation live0 := (rt_live RT (snd w)).
  Notation frames0 := (rt_frames RT (snd w)).
  Local Ltac ul := cbv delta [SEGTOP_A STACK_WIN USTACK_TOP RT_STACK NUMA_STACK NUMA_CREDIT] in *; lia.

  Definition rinv (CP : Z) (mB : mem) (ΣB : rts RT) (cr : Z) : Prop :=
    ART RT ΣB mB /\ rt_live RT ΣB = (CP, cc) :: live0 /\ rt_frames RT ΣB = frames0 /\ rt_sp0 RT ΣB = rt_sp0 RT (snd w) /\
    rt_credit RT (snd w) - mcost cc - cr <= rt_credit RT ΣB /\
    rt_pres_fp live0 frames0 (bv_unsigned (e_sp E0)) (s2_X0 E0) (wm RT w) mB /\ 0 < CP /\ CP mod 16 = 0.

  Lemma off0_range : 0 <= e_off E0 0 <= e_len E0.
  Proof using OK0. apply (off_bound E0 OK0 0). pose proof (n_bound E0 OK0). lia. Qed.

  Lemma old_client : forall CP mB ΣB cr a, rinv CP mB ΣB cr -> aclient live0 frames0 (bv_unsigned (e_sp E0)) a ->
    ~ (e_lo E0 <= a < bv_unsigned (e_sp E0)) /\ ~ (CP <= a < CP + cc) /\ aclient (rt_live RT ΣB) (rt_frames RT ΣB) (e_spa E0) a.
  Proof using AF OK0 F0.
    intros CP mB ΣB cr a (ARTB & LVB & FRB & SPB & _ & _ & CP0 & _) Ha.
    destruct F0 as [[NART _ _ NWIN _ NTOP _ _ _] _ _ _ _].
    pose proof off0_range as HO. pose proof (ok_spa _ OK0) as HSPA.
    split; [| split].
    - destruct (aclient_split_c RT AF (snd w) (wm RT w) _ a NART Ha) as [H|H]; lia.
    - apply (newchunk_apart RT AF (snd w) ΣB mB CP cc (bv_unsigned (e_sp E0)) a ARTB LVB FRB SPB); [lia | lia | exact Ha].
    - eapply aclient_mono; [exact Ha | | | lia].
      + intros e He. rewrite LVB. right. exact He.
      + intros e He. rewrite FRB. exact He.
  Qed.

  Lemma rinv_client : forall CP mB ΣB cr x, rinv CP mB ΣB cr -> s2_region E0 x \/ CP <= x < CP + cc ->
    aclient (rt_live RT ΣB) (rt_frames RT ΣB) (e_spa E0) x.
  Proof using F0.
    intros CP mB ΣB cr x (_ & LVB & FRB & _) [H|H].
    - destruct F0 as [[_ _ _ _ _ _ _ _ NCL] _ _ _ _]. eapply aclient_mono; [exact (NCL x H) | | | lia].
      + intros e He. rewrite LVB. right. exact He.
      + intros e He. rewrite FRB. exact He.
    - right; right; left. exists CP, cc. split; [rewrite LVB; left; reflexivity | exact H].
  Qed.

  Lemma rinv_art : forall CP mB ΣB cr m1, rinv CP mB ΣB cr -> munch (s2_W (env_at E0 mB)) mB m1 -> wmono bsegs mB m1 -> ART RT ΣB m1.
  Proof using AF OK0 F0.
    intros CP mB ΣB cr m1 RI MU WM. pose proof RI as (ARTB & _ & _ & SPB & _).
    destruct F0 as [[_ _ _ NWIN _ NTOP _ _ _] _ _ _ _]. s2_env OK0.
    apply (art_client_write RT AF ΣB mB m1 (e_lo E0) ARTB ltac:(rewrite SPB; exact NWIN)); [| exact WM].
    apply (agree_of_munch _ mB m1 _ MU). intros x NC.
    assert (CL : forall y, s2_region E0 y -> aclient (rt_live RT ΣB) (rt_frames RT ΣB) (e_lo E0) y).
    { intros y Hy. eapply aclient_mono; [exact (rinv_client CP mB ΣB cr y RI (or_introl Hy)) | auto | auto | lia]. }
    unfold s2_W. cbn [env_at e_lo e_sp e_THIS e_TAPE e_tcap e_SBUF e_scap e_OC e_IA e_FF outside].
    repeat split; try exact I; intro HI; apply NC.
    - left. unfold USTACK_TOP in *. lia.
    - apply CL. unfold s2_region. right; left. lia.
    - apply CL. unfold s2_region. do 5 right; left. lia.
    - apply CL. unfold s2_region. do 6 right; left. lia.
    - apply CL. unfold s2_region. do 7 right; left. lia.
    - apply CL. unfold s2_region. do 8 right; left. lia.
    - apply CL. unfold s2_region. do 9 right. lia.
  Qed.

  Lemma rinv_docsh : forall CP mB ΣB cr m1, rinv CP mB ΣB cr -> munch (s2_W (env_at E0 mB)) mB m1 ->
    agree_on (fun x => shad (e_DOC E0) <= x < shad (e_DOC E0) + 3) (wm RT w) m1.
  Proof using F0.
    intros CP mB ΣB cr m1 (_ & _ & _ & _ & _ & PFP & _) MU a Ha.
    destruct F0 as [_ _ _ _ DSH]. destruct (DSH _ Ha) as (CLa & LOa & OUTa).
    rewrite (MU a).
    - exact (PFP a (CLa _) OUTa).
    - unfold s2_W. cbn [env_at e_lo e_sp e_THIS e_TAPE e_tcap e_SBUF e_scap e_OC e_IA e_FF outside].
      unfold s2_X0 in OUTa. cbn [outside] in OUTa. split; [lia | exact OUTa].
  Qed.

  Lemma rinv_shz : forall CP mB ΣB cr, rinv CP mB ΣB cr -> a_shz (env_at E0 mB).
  Proof using AF OK0 F0.
    intros CP mB ΣB cr RI m1 MU WM. cbn [env_at e_m0] in MU, WM.
    pose proof (rinv_art CP mB ΣB cr m1 RI MU WM) as ART1. pose proof (rinv_docsh CP mB ΣB cr m1 RI MU) as AGD.
    destruct RI as (_ & LVB & FRB & _). destruct F0 as [_ _ _ SHZf _].
    assert (SA : shz_all E0 m1).
    { apply (SHZf ΣB m1 ART1); [intros e He; rewrite LVB; right; exact He | exact FRB | exact AGD]. }
    exact SA.
  Qed.

  Lemma rinv_cp_ok : forall CP mB ΣB cr, rinv CP mB ΣB cr -> cp_ok (env_at E0 mB) CP.
  Proof using AF OK0 F0.
    intros CP mB ΣB cr RI. pose proof RI as (ARTB & LVB & FRB & SPB & _ & _ & CP0 & _).
    pose proof off0_range as HO. pose proof (rtxt_blen E0 HO) as RB.
    assert (INP : In (CP, cc) (rt_live RT ΣB)) by (rewrite LVB; left; reflexivity).
    pose proof (af_live_range RT AF ΣB mB CP cc ARTB INP) as (_ & P1 & _). rewrite SPB in P1.
    destruct F0 as [[NART _ _ NWIN _ _ _ _ NCL] _ _ _ _]. s2_env OK0.
    unfold cp_ok. change (rtxt (env_at E0 mB)) with (rtxt E0). rewrite RB. cbn [env_at e_lo e_TAPE e_tcap].
    split; [exact CP0|]. split; [lia|].
    assert (D : e_TAPE E0 + 8 * e_tcap E0 <= CP \/ CP + cc <= e_TAPE E0).
    { apply intervals_apart; [lia | lia |]. intros x Hx.
      apply (newchunk_apart RT AF (snd w) ΣB mB CP cc (e_spa E0) x ARTB LVB FRB SPB); [lia | lia |].
      apply NCL. unfold s2_region. do 5 right; left. lia. }
    lia.
  Qed.

  Lemma rinv_cp_shz : forall CP mB ΣB cr, rinv CP mB ΣB cr -> cp_shz (env_at E0 mB) CP.
  Proof using AF OK0 F0.
    intros CP mB ΣB cr RI m1 MU WM. cbn [env_at e_m0] in MU, WM.
    pose proof (rinv_art CP mB ΣB cr m1 RI MU WM) as ART1.
    destruct RI as (_ & LVB & _ & _ & _ & _ & CP0 & CP16).
    pose proof off0_range as HO. pose proof (rtxt_blen E0 HO) as RB.
    assert (INP : In (CP, cc) (rt_live RT ΣB)) by (rewrite LVB; left; reflexivity).
    assert (P8 : CP mod 8 = 0) by (clear - CP16; Z.div_mod_to_equations; lia).
    pose proof (shz_live RT AF ΣB m1 CP cc ART1 INP P8) as SL.
    change (rtxt (env_at E0 mB)) with (rtxt E0). rewrite RB.
    apply (shz_sub m1 CP (8 * (cc / 8))); [exact SL | lia |]. Z.div_mod_to_equations. lia.
  Qed.

  Definition okstep (m m' : mem) : Prop :=
    forall a : word, aclient live0 frames0 (bv_unsigned (e_sp E0)) (bv_unsigned a) -> outside (s2_X0 E0) (bv_unsigned a) -> m' a = m a.

  Lemma rinv_step : forall CP mB ΣB cr mB' ΣB' cr', rinv CP mB ΣB cr -> ART RT ΣB' mB' ->
    rt_live RT ΣB' = rt_live RT ΣB -> rt_frames RT ΣB' = rt_frames RT ΣB -> rt_sp0 RT ΣB' = rt_sp0 RT ΣB ->
    rt_credit RT ΣB - (cr' - cr) <= rt_credit RT ΣB' -> okstep mB mB' -> rinv CP mB' ΣB' cr'.
  Proof.
    intros CP mB ΣB cr mB' ΣB' cr' (_ & LVB & FRB & SPB & CRB & PFP & CP0 & CP16) ART' LV' FR' SP' CR' OKS.
    split; [exact ART'|]. split; [rewrite LV'; exact LVB|]. split; [rewrite FR'; exact FRB|]. split; [rewrite SP'; exact SPB|].
    split; [lia|]. split; [| split; [exact CP0 | exact CP16]].
    intros a H1 H2. rewrite (OKS a H1 H2). exact (PFP a H1 H2).
  Qed.

  Lemma ok_munch : forall CP mB ΣB cr m1, rinv CP mB ΣB cr -> munch (s2_W (env_at E0 mB)) mB m1 -> okstep mB m1.
  Proof using AF OK0 F0.
    intros CP mB ΣB cr m1 RI MU a H1 H2. apply MU.
    destruct (old_client CP mB ΣB cr _ RI H1) as (NS & _ & _).
    unfold s2_W. cbn [env_at e_lo e_sp e_THIS e_TAPE e_tcap e_SBUF e_scap e_OC e_IA e_FF outside].
    unfold s2_X0 in H2. cbn [outside] in H2. split; [exact NS | exact H2].
  Qed.

  Lemma ok_pres : forall CP mB ΣB cr m m', rinv CP mB ΣB cr -> rt_pres (rt_live RT ΣB) (rt_frames RT ΣB) (e_spa E0) m m' -> okstep m m'.
  Proof using AF OK0 F0.
    intros CP mB ΣB cr m m' RI PR a H1 _. destruct (old_client CP mB ΣB cr _ RI H1) as (_ & _ & CL). exact (PR a CL).
  Qed.

  Lemma ok_pres_ex : forall CP mB ΣB cr d n m m', rinv CP mB ΣB cr -> rt_pres_ex (rt_live RT ΣB) (rt_frames RT ΣB) (e_spa E0) d n m m' ->
    ((CP <= d /\ d + n <= CP + cc) \/ (e_lo E0 <= d /\ d + n <= bv_unsigned (e_sp E0))) -> okstep m m'.
  Proof using AF OK0 F0.
    intros CP mB ΣB cr d n m m' RI PR HD a H1 _. destruct (old_client CP mB ΣB cr _ RI H1) as (NS & NC & CL).
    apply (PR a CL). lia.
  Qed.

  Lemma ok_trans : forall m1 m2 m3, okstep m1 m2 -> okstep m2 m3 -> okstep m1 m3.
  Proof. intros m1 m2 m3 A B a H1 H2. rewrite (B a H1 H2). exact (A a H1 H2). Qed.

  Hypothesis RTF : rt_contracts_f RT.

  Lemma w_art : forall m1, munch (s2_W (env_at E0 (wm RT w))) (wm RT w) m1 -> wmono bsegs (wm RT w) m1 -> ART RT (snd w) m1.
  Proof using AF OK0 F0.
    intros m1 MU WM. destruct F0 as [[NART _ _ NWIN _ NTOP _ _ NCL] _ _ _ _]. s2_env OK0.
    apply (art_client_write RT AF (snd w) (wm RT w) m1 (e_lo E0) NART NWIN); [| exact WM].
    apply (agree_of_munch _ (wm RT w) m1 _ MU). intros x NC.
    assert (CL : forall y, s2_region E0 y -> aclient live0 frames0 (e_lo E0) y).
    { intros y Hy. eapply aclient_mono; [exact (NCL y Hy) | auto | auto | lia]. }
    unfold s2_W. cbn [env_at e_lo e_sp e_THIS e_TAPE e_tcap e_SBUF e_scap e_OC e_IA e_FF outside].
    repeat split; try exact I; intro HI; apply NC.
    - left. unfold USTACK_TOP in *. lia.
    - apply CL. unfold s2_region. right; left. lia.
    - apply CL. unfold s2_region. do 5 right; left. lia.
    - apply CL. unfold s2_region. do 6 right; left. lia.
    - apply CL. unfold s2_region. do 7 right; left. lia.
    - apply CL. unfold s2_region. do 8 right; left. lia.
    - apply CL. unfold s2_region. do 9 right. lia.
  Qed.

  Lemma root_new :
    (forall CP m2 Σ2, rinv CP m2 Σ2 0 -> rpro_ret1_k (env_at E0 m2) (aevt RT PMc Σ2 K) CP) ->
    rpro_new_k (env_at E0 (wm RT w)) (aevt RT PMc (snd w) K).
  Proof using AF FDO MST OK0 F0 RTF.
    intros HK. unfold rpro_new_k. intros until m1. intros HM. apply evt_done.
    pose proof F0 as [[NART NFR NCR NWIN NROOM NTOP NTP NBUF NCL NFNZ] RLIVE RCRED _ _].
    pose proof off0_range as HO. s2_env OK0.
    assert (EU : bv_unsigned (Z_to_bv 64 (e_spa E0)) = e_spa E0) by (apply unsigned_lit; lia).
    assert (HAL16 : e_spa E0 mod 16 = 0) by (pose proof (ok_al_spa _ OK0) as A32; clear - A32; Z.div_mod_to_equations; lia).
    pose proof HM as HM0. s2_open_mem HM. wE_norm.
    pose proof (w_art m1 MU WM) as ART1.
    eapply (aevt_rt RT PMc); [ | exact FRM | ].
    - cbn [env_at e_sp e_spa e_gp e_tp e_len e_off e_IDX e_TAPE e_BUF e_FF e_bs e_idxs].
      eapply (newarr_nt_ok RT AF (rf_malloc RT RTF) (snd w) PMc) with (n := cc) (lo := e_lo E0); rewrite ?EU; try eassumption; try lia; try reflexivity.
      + pose proof (mcost_mono cc (e_len E0 + 64) ltac:(lia)). unfold NUMA_CREDIT in *. lia.
      + ul.
    - intros c (Σ2 & CP & HA & LV2 & FR2 & SP2 & CR2 & CP0 & CP16 & CPT).
      exists Σ2. eexists. split; [exact HA|].
      intros ms' (m2 & RS & RAF & PR & WRC & ACC) F0'. rewrite EU in RAF, PR. destruct RAF as (ART2 & MI2 & WM2 & ST2).
      assert (RI1 : rinv CP m1 (snd w) 0 -> False \/ True) by (intros; right; exact I).

      assert (OKM : okstep (wm RT w) m1).
      { intros a H1 H2. apply MU.
        destruct (aclient_split_c RT AF (snd w) (wm RT w) _ _ NART H1) as [HH|HH];
          (unfold s2_X0 in H2; cbn [outside] in H2; cbn [outside]; split; [lia | exact H2]). }
      assert (RI2 : rinv CP m2 Σ2 0).
      { split; [exact ART2|]. split; [exact LV2|]. split; [exact FR2|]. split; [exact SP2|]. split; [lia|].
        split; [| split; [exact CP0 | exact CP16]].
        intros a H1 H2. rewrite (PR a). { exact (OKM a H1 H2). }
        eapply aclient_mono; [exact H1 | auto | auto | lia]. }

      assert (HM2 : MEMI (env_at E0 m2) (e_nxt0 E0) [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; CB 8 j152; CB 8 j160; CB 8 j168; C8 (Z_to_bv 64 (e_TAPE E0)); C8 (Z_to_bv 64 (e_TAPE E0 + 8)); C8 (Z_to_bv 64 (e_IDX E0 + 4)); CB 8 j200; CB 8 j272; CB 8 j288; CB 8 j304] [] fc m2).
      { eapply (MEMI_transport E0 (wm RT w) m1 m2); [exact OK0 | | | exact HM0 | | exact MI2 | exact ST2 | exact FRM];
          [repeat constructor | reflexivity |].
        intros a Ha. apply PR. exact (NCL _ Ha). }
      revert F0'. apply (ret_st_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 ms' (fun ms => frm0 (ms_fcsr ms) -> aevt RT PMc Σ2 K ms) RS).
      intros q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F' fc' F0'. cbn [ms_fcsr] in F0'.
      rewrite (ret_pc_even 0xb7254) by (first [lia | reflexivity]).
      apply (aevt_evt RT AF PMc MST).
      pose proof (HK CP m2 Σ2 RI2) as KR. unfold rpro_ret1_k in KR.
      eapply evt_eq; [| eapply KR; eapply (MEMI_transport E0 m2 m2 m2); [exact OK0 | | | exact HM2 | | exact MI2 | exact ST2 | exact F0'];
                          [repeat constructor | reflexivity | intros a _; reflexivity]].
      reflexivity.
  Qed.

  Lemma wr_at_sub' : forall (mx : mem) a n a' n', wr_at bsegs mx a n -> a <= a' -> a' + n' <= a + n -> 0 <= a' -> wr_at bsegs mx a' n'.
  Proof.
    intros mx a n a' n' (A0 & A1 & H) H1 H2 H3. split; [exact H3|]. split; [lia|]. intros i Hi.
    replace (a' + i) with (a + (a' - a + i)) by lia. apply H. lia.
  Qed.

  Lemma rl_pos : 0 < rl.
  Proof using OK0. pose proof (n_bound E0 OK0) as HN. pose proof (off_lt_len _ _ (ok_s1 _ OK0) 0 ltac:(lia)). lia. Qed.

  Lemma copy_munch : forall CP mB ΣB cr m1, rinv CP mB ΣB cr -> munch (s2_W (env_at E0 mB)) mB m1 -> agree_on (fun x => CP <= x < CP + cc) mB m1.
  Proof using AF OK0 F0.
    intros CP mB ΣB cr m1 RI MU a Ha. apply MU.
    pose proof (rinv_cp_ok CP mB ΣB cr RI) as (_ & CLO & _). change (rtxt (env_at E0 mB)) with (rtxt E0) in CLO.
    rewrite (rtxt_blen E0 off0_range) in CLO. cbn [env_at e_lo] in CLO.
    pose proof RI as (ARTB & LVB & FRB & SPB & _).
    destruct F0 as [[_ _ _ NWIN _ _ _ _ NCL] _ _ _ _]. s2_env OK0.
    assert (AP : forall y, s2_region E0 y -> ~ (CP <= y < CP + cc)).
    { intros y Hy. apply (newchunk_apart RT AF (snd w) ΣB mB CP cc (e_spa E0) y ARTB LVB FRB SPB); [lia | lia | exact (NCL y Hy)]. }
    unfold s2_W. cbn [env_at e_lo e_sp e_THIS e_TAPE e_tcap e_SBUF e_scap e_OC e_IA e_FF outside].
    repeat split; try exact I; intro HI.
    - lia.
    - apply (AP (bv_unsigned a)); [unfold s2_region; right; left; lia | exact Ha].
    - apply (AP (bv_unsigned a)); [unfold s2_region; do 5 right; left; lia | exact Ha].
    - apply (AP (bv_unsigned a)); [unfold s2_region; do 6 right; left; lia | exact Ha].
    - apply (AP (bv_unsigned a)); [unfold s2_region; do 7 right; left; lia | exact Ha].
    - apply (AP (bv_unsigned a)); [unfold s2_region; do 8 right; left; lia | exact Ha].
    - apply (AP (bv_unsigned a)); [unfold s2_region; do 9 right; lia | exact Ha].
  Qed.

  Lemma buf_tail : forall (m1 : mem), bytes_at bsegs m1 (e_BUF E0) (padded_bytes (e_bs E0)) -> bytes_at bsegs m1 (e_BUF E0 + e_off E0 0) (zbytes (rtxt E0)).
  Proof using OK0.
    intros m1 H. pose proof off0_range as HO. unfold padded_bytes in H.
    rewrite <- (firstn_skipn (Z.to_nat (e_off E0 0)) (e_bs E0)) in H. fold (rtxt E0) in H.
    unfold zbytes in H. rewrite map_app in H. rewrite <- app_assoc in H.
    apply bytes_at_app in H. destruct H as [_ H]. apply bytes_at_app in H. destruct H as [H _].
    rewrite length_map, length_firstn in H. unfold blen in HO.
    replace (Z.of_nat (Nat.min (Z.to_nat (e_off E0 0)) (length (e_bs E0)))) with (e_off E0 0) in H by lia.
    exact H.
  Qed.

  Lemma call_ok_of : forall ΣB (m1 : mem), rt_sp0 RT ΣB = rt_sp0 RT (snd w) -> stk bsegs m1 (e_lo E0) (e_spa E0) ->
    call_ok RT ΣB m1 (Z_to_bv 64 (e_spa E0)) (e_lo E0).
  Proof using OK0 F0.
    intros ΣB m1 SPB ST. destruct F0 as [[_ _ _ NWIN NROOM NTOP _ _ _] _ _ _ _]. s2_env OK0.
    assert (EU : bv_unsigned (Z_to_bv 64 (e_spa E0)) = e_spa E0) by (apply unsigned_lit; lia).
    assert (HAL16 : e_spa E0 mod 16 = 0) by (pose proof (ok_al_spa _ OK0) as A32; clear - A32; Z.div_mod_to_equations; lia).
    unfold call_ok. rewrite EU, SPB. split; [exact ST|]. split; [exact NWIN|]. split; [ul|]. split; [ul | exact HAL16].
  Qed.

  Lemma root_memcpy : forall CP mB ΣB, rinv CP mB ΣB 0 ->
    (forall m3, rinv CP m3 ΣB 0 -> bytes_at bsegs m3 CP (zbytes (rtxt E0)) -> rpro_ret2_k (env_at E0 m3) (aevt RT PMc ΣB K) CP) ->
    rpro_memcpy_k (env_at E0 mB) (aevt RT PMc ΣB K) CP.
  Proof using AF FDO MST OK0 F0 RTF.
    intros CP mB ΣB RI HK. unfold rpro_memcpy_k. intros until m1. intros HM. apply evt_done.
    pose proof F0 as [[NART NFR NCR NWIN NROOM NTOP NTP (pb & nb & PIN & PB8 & PLO & PHI) NCL] RLIVE RCRED _ _].
    pose proof RI as (ARTB & LVB & FRB & SPB & CRB & PFP & CP0 & CP16).
    pose proof off0_range as HO. pose proof rl_pos as HRL. s2_env OK0.
    assert (EU : bv_unsigned (Z_to_bv 64 (e_spa E0)) = e_spa E0) by (apply unsigned_lit; lia).
    pose proof HM as HM0. s2_open_mem HM. wE_norm.
    pose proof (rinv_art CP mB ΣB 0 m1 RI MU WM) as ART1.
    pose proof (buf_tail m1 BUFRO) as SRC.
    assert (LEN : Z.of_nat (length (zbytes (rtxt E0))) = rl) by (rewrite zbytes_length; pose proof (rtxt_blen E0 HO) as RB; unfold blen in RB; exact RB).
    assert (INC : In (CP, cc) (rt_live RT ΣB)) by (rewrite LVB; left; reflexivity).
    assert (INB : In (pb, nb) (rt_live RT ΣB)) by (rewrite LVB; right; exact PIN).
    pose proof (af_live_range RT AF ΣB m1 CP cc ART1 INC) as (_ & CHI & _). rewrite SPB in CHI.
    destruct (af_acc_live RT AF ΣB m1 CP cc ART1 INC) as [WRC ACC]. destruct (af_acc_live RT AF ΣB m1 pb nb ART1 INB) as [_ ACB].
    assert (APB : e_BUF E0 + e_off E0 0 + rl <= CP \/ CP + cc <= e_BUF E0 + e_off E0 0).
    { assert (D : e_BUF E0 + e_len E0 <= CP \/ CP + cc <= e_BUF E0).
      { destruct (intervals_apart (e_BUF E0) (e_len E0) CP cc ltac:(lia) ltac:(lia)) as [D|D]; [| left; exact D | right; exact D].
        intros x Hx. apply (newchunk_apart RT AF (snd w) ΣB m1 CP cc (e_spa E0) x ART1 LVB FRB SPB); [lia | lia |].
        apply NCL. unfold s2_region. do 4 right; left. lia. }
      lia. }
    eapply (aevt_memcpy RT RTF PMc FDO MST ΣB K) with (d := CP) (s := e_BUF E0 + e_off E0 0) (bs := zbytes (rtxt E0)) (lo := e_lo E0);
      rewrite ?LEN; try reflexivity; try eassumption; try lia.
    -
      split; [intros _; split|].
      + apply (acc_sub bsegs m1 pb nb); [exact ACB | lia | lia].
      + left. exists pb, nb. split; [exact INB | lia].
      + left. lia.
    -
      split; [intros _; split| split].
      + apply (acc_sub bsegs m1 CP cc); [exact ACC | lia | lia].
      + left. exists CP, cc. split; [exact INC | lia].
      + intros i Hi. rewrite EU. apply (rinv_client CP mB ΣB 0 _ RI). right. lia.
      + apply (wr_at_sub' m1 CP cc); [exact WRC | lia | lia | lia].
    - exact (call_ok_of ΣB m1 SPB ST).
    -
      intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m3 F0' RAF PR BY.
      rewrite EU in RAF, PR. destruct RAF as (ART3 & MI3 & WM3 & ST3).
      assert (RI3 : rinv CP m3 ΣB 0).
      { apply (rinv_step CP mB ΣB 0 m3 ΣB 0 RI ART3 eq_refl eq_refl eq_refl ltac:(lia)).
        apply (ok_trans mB m1 m3); [exact (ok_munch CP mB ΣB 0 m1 RI MU)|].
        apply (ok_pres_ex CP mB ΣB 0 CP rl m1 m3 RI PR). left. lia. }
      rewrite (ret_pc_even 0xb7290) by (first [lia | reflexivity]).
      apply (aevt_evt RT AF PMc MST).
      pose proof (HK m3 RI3 BY) as KR. unfold rpro_ret2_k in KR.
      eapply evt_eq; [| eapply KR; eapply (MEMI_transport E0 mB m1 m3); [exact OK0 | | | exact HM0 | | exact MI3 | exact ST3 | exact F0'];
                          [repeat constructor | reflexivity |]].
      + reflexivity.
      + intros a Ha. apply PR; [exact (rinv_client CP mB ΣB 0 _ RI (or_introl Ha))|].
        assert (AP : ~ (CP <= bv_unsigned a < CP + cc)).
        { apply (newchunk_apart RT AF (snd w) ΣB m1 CP cc (e_spa E0) _ ART1 LVB FRB SPB); [lia | lia | exact (NCL _ Ha)]. }
        lia.
  Qed.

  Lemma root_memset : forall CP mB ΣB, rinv CP mB ΣB 0 -> bytes_at bsegs mB CP (zbytes (rtxt E0)) ->
    (forall m4, rinv CP m4 ΣB 0 -> bytes_at bsegs m4 CP (zbytes (crs (rtxt E0))) -> numr_entry_k (env_at E0 m4) (aevt RT PMc ΣB K) CP) ->
    rpro_memset_k (env_at E0 mB) (aevt RT PMc ΣB K) CP.
  Proof using AF FDO MST OK0 F0 RTF.
    intros CP mB ΣB RI CPY HK. unfold rpro_memset_k. intros until m1. intros HM. apply evt_done.
    pose proof F0 as [[NART NFR NCR NWIN NROOM NTOP NTP NBUF NCL NFNZ] RLIVE RCRED _ _].
    pose proof RI as (ARTB & LVB & FRB & SPB & CRB & PFP & CP0 & CP16).
    pose proof off0_range as HO. pose proof rl_pos as HRL. s2_env OK0.
    assert (EU : bv_unsigned (Z_to_bv 64 (e_spa E0)) = e_spa E0) by (apply unsigned_lit; lia).
    pose proof HM as HM0. s2_open_mem HM. wE_norm.
    pose proof (rinv_art CP mB ΣB 0 m1 RI MU WM) as ART1.
    assert (LEN : Z.of_nat (length (zbytes (rtxt E0))) = rl) by (rewrite zbytes_length; pose proof (rtxt_blen E0 HO) as RB; unfold blen in RB; exact RB).
    assert (INC : In (CP, cc) (rt_live RT ΣB)) by (rewrite LVB; left; reflexivity).
    pose proof (af_live_range RT AF ΣB m1 CP cc ART1 INC) as (_ & CHI & _). rewrite SPB in CHI.
    destruct (af_acc_live RT AF ΣB m1 CP cc ART1 INC) as [WRC ACC].

    assert (CPY1 : bytes_at bsegs m1 CP (zbytes (rtxt E0))).
    { apply (bytes_at_agree bsegs mB m1 CP _ CPY). eapply agree_sub; [exact (copy_munch CP mB ΣB 0 m1 RI MU)|]. intros x Hx. cbv beta in *. lia. }
    eapply (aevt_memset RT RTF PMc FDO MST ΣB K) with (d := CP + rl) (n := 64) (cb := Z_to_bv 8 32) (lo := e_lo E0);
      try reflexivity; try eassumption; try lia.
    - split; [intros _; split| split].
      + apply (acc_sub bsegs m1 CP cc); [exact ACC | lia | lia].
      + left. exists CP, cc. split; [exact INC | lia].
      + intros i Hi. rewrite EU. apply (rinv_client CP mB ΣB 0 _ RI). right. lia.
      + apply (wr_at_sub' m1 CP cc); [exact WRC | lia | lia | lia].
    - exact (call_ok_of ΣB m1 SPB ST).
    - intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m4 F0' RAF PR BY.
      rewrite EU in RAF, PR. destruct RAF as (ART4 & MI4 & WM4 & ST4).
      assert (RI4 : rinv CP m4 ΣB 0).
      { apply (rinv_step CP mB ΣB 0 m4 ΣB 0 RI ART4 eq_refl eq_refl eq_refl ltac:(lia)).
        apply (ok_trans mB m1 m4); [exact (ok_munch CP mB ΣB 0 m1 RI MU)|].
        apply (ok_pres_ex CP mB ΣB 0 (CP + rl) 64 m1 m4 RI PR). left. lia. }
      assert (CPY4 : bytes_at bsegs m4 CP (zbytes (crs (rtxt E0)))).
      { unfold crs, zbytes. rewrite map_app, map_repeat. apply bytes_at_app. split.
        - apply (bytes_at_agree bsegs m1 m4 CP _ CPY1). intros a Ha. cbv beta in Ha. rewrite LEN in Ha.
          apply PR; [apply (rinv_client CP mB ΣB 0 _ RI); right; lia | lia].
        - fold (zbytes (rtxt E0)). rewrite LEN. exact BY. }
      rewrite (ret_pc_even 0xb72b4) by (first [lia | reflexivity]).
      apply (aevt_evt RT AF PMc MST).
      pose proof (HK m4 RI4 CPY4) as KR. unfold numr_entry_k in KR.
      eapply evt_eq; [| eapply KR; split; [| exact CPY4]; eapply (MEMI_transport E0 mB m1 m4); [exact OK0 | | | exact HM0 | | exact MI4 | exact ST4 | exact F0'];
                          [repeat constructor | reflexivity |]].
      + reflexivity.
      + intros a Ha. apply PR; [exact (rinv_client CP mB ΣB 0 _ RI (or_introl Ha))|].
        assert (AP : ~ (CP <= bv_unsigned a < CP + cc)).
        { apply (newchunk_apart RT AF (snd w) ΣB m1 CP cc (e_spa E0) _ ART1 LVB FRB SPB); [lia | lia | exact (NCL _ Ha)]. }
        lia.
  Qed.

  Variable good : WD RT -> Z -> Prop.
  Hypothesis HG : good w 0.
  Hypothesis GROOT : g_root RT E0 good.
  Hypothesis LFRESH : live_fresh RT.
  Notation wE := (Sj_stage2_main.wE E0 (WD RT) (wm RT)).
  Notation wQ := (Sj_stage2_world.wQ RT PMc K).

  Lemma root_del_gen : forall CP mB ΣB cr, rinv CP mB ΣB cr -> cr <= NUMA_CREDIT ->
    forall (RA : Z), (0 <= RA < 2^64)%Z -> (RA mod 2 = 0)%Z ->
    forall (nxt : word) (sl : list cell) (sc : list (bool * Z)), Forall (fun c => csize c = 8%nat) sl -> length sl = 29%nat ->
    forall (t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMI (env_at E0 mB) nxt sl sc fc m1 ->
    (forall (w'' : WD RT) (v t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32),
        good w'' 1 -> MEMI (wE w'') nxt sl sc fc' (wm RT w'') ->
        wQ w'' (MS (mkR (Z_to_bv 64 RA) (Z_to_bv 64 (e_spa E0)) (e_gp E0) (e_tp E0) t0' t1' t2' (e_sp E0) s1 v a1' a2' a3' a4' a5' a6' a7'
                         s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F' (Z_to_bv 64 RA) fc' None (wm RT w'') (seg_rom bsegs))) ->
    aevt RT PMc ΣB K (MS (mkR (Z_to_bv 64 RA) (Z_to_bv 64 (e_spa E0)) (e_gp E0) (e_tp E0) t0 t1 t2 (e_sp E0) s1 (Z_to_bv 64 CP) a1 a2 a3 a4 a5 a6 a7
                           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x10ac6c) fc None m1 (seg_rom bsegs)).
  Proof using AF FDO MST OK0 F0 RTF HG GROOT LFRESH.
    intros CP mB ΣB cr RI HCR RA HRA HRA2 nxt sl sc HCS HLS t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 HM HK.
    pose proof F0 as [[NART NFR NCR NWIN NROOM NTOP NTP NBUF NCL NFNZ] RLIVE RCRED _ _].
    pose proof RI as (ARTB & LVB & FRB & SPB & CRB & PFP & CP0 & CP16).
    pose proof off0_range as HO. pose proof rl_pos as HRL. s2_env OK0.
    assert (EU : bv_unsigned (Z_to_bv 64 (e_spa E0)) = e_spa E0) by (apply unsigned_lit; lia).
    assert (HMU : munch (s2_W (env_at E0 mB)) mB m1 /\ wmono bsegs mB m1 /\ frm0 fc /\ mem_inv bsegs m1 /\ stk bsegs m1 (e_lo E0) (e_spa E0)).
    { destruct HM as (FRM & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MI & MU & WM & ST & _).
      split; [exact MU|]. split; [exact WM|]. split; [exact FRM|]. split; [exact MI| exact ST]. }
    destruct HMU as (MU & WM & FRM & MI & ST).
    pose proof (rinv_art CP mB ΣB cr m1 RI MU WM) as ART1.
    assert (INC : In (CP, cc) (rt_live RT ΣB)) by (rewrite LVB; left; reflexivity).
    eapply (aevt_rt RT PMc); [ | exact FRM | ].
    - eapply (delarr_ok RT AF (rf_free RT RTF) ΣB PMc) with (p := CP) (n := cc) (lo := e_lo E0); try eassumption; try reflexivity.
      + exact (call_ok_of ΣB m1 SPB ST).
      + unfold unwind_ok. rewrite EU. right; right. lia.
    - intros c (Σ8 & v & HA & LV8 & FR8 & SP8 & CR8).
      exists Σ8. eexists. split; [exact HA|].
      intros ms' (m8 & RS & RAF & PR) F0'. rewrite EU in RAF, PR. destruct RAF as (ART8 & MI8 & ST8).
      assert (LV80 : rt_live RT Σ8 = live0).
      { rewrite LV8, LVB. apply live_remove_hd. exact (LFRESH ΣB mB CP cc live0 ARTB LVB ltac:(lia)). }
      rewrite LV80, FRB in PR.

      assert (HG8 : good (m8, Σ8) 1).
      { apply (GROOT w (m8, Σ8) HG). unfold wroot. cbn [snd fst wm].
        split; [exact ART8|]. split; [| split; [rewrite FR8; exact FRB | split; [exact LV80 | split; [rewrite SP8; exact SPB |]]]].
        - intros a H1 H2. rewrite (PR a).
          + rewrite (ok_munch CP mB ΣB cr m1 RI MU a H1 H2). exact (PFP a H1 H2).
          + eapply aclient_mono; [exact H1 | auto | auto | lia].
        - pose proof (mcost_mono cc (e_len E0 + 64) ltac:(lia)). lia. }
      revert F0'. apply (ret_st_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m8 ms' (fun ms => frm0 (ms_fcsr ms) -> aevt RT PMc Σ8 K ms) RS).
      intros q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F' fc' F0'. cbn [ms_fcsr] in F0'.
      rewrite (ret_pc_even RA HRA HRA2).
      refine (HK (m8, Σ8) v q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F' fc' HG8 _).
      eapply (MEMI_transport E0 mB m1 m8); [exact OK0 | exact HCS | exact HLS | exact HM | | exact MI8 | exact ST8 | exact F0'].
      intros a Ha. apply PR. exact (NCL _ Ha).
  Qed.

  Lemma root_del_gen_g : forall ws : list Z, forall CP mB ΣB cr, rinv CP mB ΣB cr -> cr <= NUMA_CREDIT ->
    forall (RA : Z), (0 <= RA < 2^64)%Z -> (RA mod 2 = 0)%Z ->
    forall (nxt : word) (sl : list cell) (sc : list (bool * Z)), Forall (fun c => csize c = 8%nat) sl -> length sl = 29%nat ->
    forall (t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMI (gapp (env_at E0 mB) ws []) nxt sl sc fc m1 ->
    (forall (w'' : WD RT) (v t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32),
        good w'' 1 -> MEMI (gapp (wE w'') ws []) nxt sl sc fc' (wm RT w'') ->
        wQ w'' (MS (mkR (Z_to_bv 64 RA) (Z_to_bv 64 (e_spa E0)) (e_gp E0) (e_tp E0) t0' t1' t2' (e_sp E0) s1 v a1' a2' a3' a4' a5' a6' a7'
                         s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F' (Z_to_bv 64 RA) fc' None (wm RT w'') (seg_rom bsegs))) ->
    aevt RT PMc ΣB K (MS (mkR (Z_to_bv 64 RA) (Z_to_bv 64 (e_spa E0)) (e_gp E0) (e_tp E0) t0 t1 t2 (e_sp E0) s1 (Z_to_bv 64 CP) a1 a2 a3 a4 a5 a6 a7
                           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x10ac6c) fc None m1 (seg_rom bsegs)).
  Proof using AF FDO MST OK0 F0 RTF HG GROOT LFRESH.
    intros ws CP mB ΣB cr RI HCR RA HRA HRA2 nxt sl sc HCS HLS t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 HM HK.
    pose proof F0 as [[NART NFR NCR NWIN NROOM NTOP NTP NBUF NCL NFNZ] RLIVE RCRED _ _].
    pose proof RI as (ARTB & LVB & FRB & SPB & CRB & PFP & CP0 & CP16).
    pose proof off0_range as HO. pose proof rl_pos as HRL. s2_env OK0.
    assert (EU : bv_unsigned (Z_to_bv 64 (e_spa E0)) = e_spa E0) by (apply unsigned_lit; lia).
    assert (HMU : munch (s2_W (env_at E0 mB)) mB m1 /\ wmono bsegs mB m1 /\ frm0 fc /\ mem_inv bsegs m1 /\ stk bsegs m1 (e_lo E0) (e_spa E0)).
    { destruct HM as (FRM & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MI & MU & WM & ST & _).
      split; [exact MU|]. split; [exact WM|]. split; [exact FRM|]. split; [exact MI| exact ST]. }
    destruct HMU as (MU & WM & FRM & MI & ST).
    pose proof (rinv_art CP mB ΣB cr m1 RI MU WM) as ART1.
    assert (INC : In (CP, cc) (rt_live RT ΣB)) by (rewrite LVB; left; reflexivity).
    eapply (aevt_rt RT PMc); [ | exact FRM | ].
    - eapply (delarr_ok RT AF (rf_free RT RTF) ΣB PMc) with (p := CP) (n := cc) (lo := e_lo E0); try eassumption; try reflexivity.
      + exact (call_ok_of ΣB m1 SPB ST).
      + unfold unwind_ok. rewrite EU. right; right. lia.
    - intros c (Σ8 & v & HA & LV8 & FR8 & SP8 & CR8).
      exists Σ8. eexists. split; [exact HA|].
      intros ms' (m8 & RS & RAF & PR) F0'. rewrite EU in RAF, PR. destruct RAF as (ART8 & MI8 & ST8).
      assert (LV80 : rt_live RT Σ8 = live0).
      { rewrite LV8, LVB. apply live_remove_hd. exact (LFRESH ΣB mB CP cc live0 ARTB LVB ltac:(lia)). }
      rewrite LV80, FRB in PR.

      assert (HG8 : good (m8, Σ8) 1).
      { apply (GROOT w (m8, Σ8) HG). unfold wroot. cbn [snd fst wm].
        split; [exact ART8|]. split; [| split; [rewrite FR8; exact FRB | split; [exact LV80 | split; [rewrite SP8; exact SPB |]]]].
        - intros a H1 H2. rewrite (PR a).
          + rewrite (ok_munch CP mB ΣB cr m1 RI MU a H1 H2). exact (PFP a H1 H2).
          + eapply aclient_mono; [exact H1 | auto | auto | lia].
        - pose proof (mcost_mono cc (e_len E0 + 64) ltac:(lia)). lia. }
      revert F0'. apply (ret_st_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m8 ms' (fun ms => frm0 (ms_fcsr ms) -> aevt RT PMc Σ8 K ms) RS).
      intros q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F' fc' F0'. cbn [ms_fcsr] in F0'.
      rewrite (ret_pc_even RA HRA HRA2).
      refine (HK (m8, Σ8) v q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F' fc' HG8 _).
      eapply (MEMI_transport (gapp E0 ws []) mB m1 m8); [apply env_ok_gapp; exact OK0 | exact HCS | exact HLS | exact HM | | exact MI8 | exact ST8 | exact F0'].
      intros a Ha. apply PR. exact (NCL _ Ha).
  Qed.

  Lemma crs_stop : forall t, nth_error (zbytes (crs t)) (Z.to_nat (blen t)) = Some (Z_to_bv 8 32).
  Proof.
    intros t. unfold blen. rewrite Nat2Z.id. rewrite nth_error_zbytes by (unfold crs; rewrite length_app, repeat_length; lia).
    unfold crs. rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity.
  Qed.

  Lemma root_call_gen : forall (entry r1 r0 RA : Z), numwa_cps RT entry r1 r0 -> (0 <= RA < 2^64)%Z -> (RA mod 2 = 0)%Z ->
    forall CP mB ΣB, rinv CP mB ΣB 0 ->
    forall (nxt : word) (sc : list (bool * Z)) (c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 c112 c120 c128 c136 c144 c152 c160 c168 c176 c184 c192 c200 c272 c288 : cell) (j304 : list byte),
    Forall (fun c => csize c = 8%nat) [c0; c8; c16; c24; c32; c40; c48; c56; c64; c72; c80; c88; c96; c104; c112; c120; c128; c136; c144; c152; c160; c168; c176; c184; c192; c200; c272; c288] ->
    forall (t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMI (env_at E0 mB) nxt [c0; c8; c16; c24; c32; c40; c48; c56; c64; c72; c80; c88; c96; c104; c112; c120; c128; c136; c144; c152; c160; c168; c176; c184; c192; c200; c272; c288; CB 8 j304] sc fc m1 ->
    bytes_at bsegs m1 CP (zbytes (crs (rtxt E0))) ->
    (forall m6 Σ6 (flag : bool) (v : word) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32),
        rinv CP m6 Σ6 NUMA_CREDIT ->
        MEMI (env_at E0 m6) nxt [c0; c8; c16; c24; c32; c40; c48; c56; c64; c72; c80; c88; c96; c104; c112; c120; c128; c136; c144; c152; c160; c168; c176; c184; c192; c200; c272; c288; C8 v] sc fc' m6 ->
        bytes_at bsegs m6 CP (zbytes (crs (rtxt E0))) ->
        aevt RT PMc Σ6 K (MS (mkR (Z_to_bv 64 RA) (Z_to_bv 64 (e_spa E0)) (e_gp E0) (e_tp E0) t0' t1' t2' s0 s1 (Z_to_bv 64 (if flag then r1 else r0)) a1' a2' a3' a4' a5' a6' a7'
                                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F' (Z_to_bv 64 RA) fc' None m6 (seg_rom bsegs))) ->
    aevt RT PMc ΣB K (MS (mkR (Z_to_bv 64 RA) (Z_to_bv 64 (e_spa E0)) (e_gp E0) (e_tp E0) t0 t1 t2 s0 s1 (Z_to_bv 64 CP) (Z_to_bv 64 (e_spa E0 + 304)) a2 a3 a4 a5 a6 a7
                           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 entry) fc None m1 (seg_rom bsegs)).
  Proof using AF FDO MST OK0 F0.
    intros entry r1 r0 RA HC HRA HRA2 CP mB ΣB RI nxt sc c0 c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 c88 c96 c104 c112 c120 c128 c136 c144 c152 c160 c168 c176 c184 c192 c200 c272 c288 j304 HCS.
    intros t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 HM CPB HK.
    pose proof F0 as [[NART NFR NCR NWIN NROOM NTOP NTP NBUF NCL NFNZ] RLIVE RCRED _ _].
    pose proof RI as (ARTB & LVB & FRB & SPB & CRB & PFP & CP0 & CP16).
    pose proof off0_range as HO. pose proof rl_pos as HRL. pose proof (rtxt_blen E0 HO) as RB. pose proof (crs_blen (rtxt E0)) as CBL. s2_env OK0.
    assert (EU : bv_unsigned (Z_to_bv 64 (e_spa E0)) = e_spa E0) by (apply unsigned_lit; lia).
    assert (HAL16 : e_spa E0 mod 16 = 0 /\ (e_spa E0 + 304) mod 8 = 0).
    { pose proof (ok_al_spa _ OK0) as A32. clear - A32. split; Z.div_mod_to_equations; lia. }
    assert (P8 : CP mod 8 = 0) by (clear - CP16; Z.div_mod_to_equations; lia).
    pose proof HM as HM0.
    s2_open_mem HM. wE_norm.
    pose proof (rinv_art CP mB ΣB 0 m1 RI MU WM) as ART1.
    assert (INC : In (CP, cc) (rt_live RT ΣB)) by (rewrite LVB; left; reflexivity).

    repeat match goal with H : Forall _ (_ :: _) |- _ => let E8 := fresh "E8" in inversion H as [|? ? E8 H']; clear H; subst; rename H' into HCS' end.
    lazymatch type of FR with rw_cells _ _ _ ?l => rewrite (app_removelast_last (CB 0 []) (l := l)) in FR by discriminate end.
    cbn [removelast last] in FR. apply rw_cells_app in FR. destruct FR as [FRa FRb].
    lazymatch type of FRb with rw_cells _ _ (_ + Z.of_nat ?sz) _ =>
      assert (SZ : Z.of_nat sz = 304) by (cbn [cells_size csize]; repeat match goal with H : csize _ = 8%nat |- _ => rewrite H end; reflexivity) end.
    rewrite SZ in FRb.
    pose proof (mcost_mono cc (e_len E0 + 64) ltac:(lia)) as MM.
    unfold aevt. intros T c Hc Hk.
    apply (HC ΣB PMc (Z_to_bv 64 RA) (Z_to_bv 64 (e_spa E0)) (e_gp E0) (e_tp E0) t0 t1 t2 s0 s1 (Z_to_bv 64 CP) (Z_to_bv 64 (e_spa E0 + 304)) a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 CP 0 (blen (rtxt E0)) (e_spa E0 + 304) (e_lo E0) CP cc (zbytes (crs (rtxt E0)))
             (Z_to_bv 8 32) j304 FDO MST (f_equal (Z_to_bv 64) (eq_sym (Z.add_0_r CP))) eq_refl NTP FRM) with (T := T) (c := c);
      rewrite ?EU, ?FRB, ?SPB; try assumption; try lia; try ul.
    { apply crs_stop. }
    { reflexivity. }
    intros c' (Σ6 & HA & EFR & ELV & ESP & ECR).
    destruct (ASTA_unpack RT Σ6 PMc _ c' HA) as (ms' & (m6 & v & flag & RS & F0' & RAF & PR & OUTC) & HA').
    destruct RAF as (ART6 & MI6 & WM6 & ST6).
    rewrite <- ?FRB in EFR, PR. rewrite <- ?SPB in ESP.
    assert (RI6 : rinv CP m6 Σ6 NUMA_CREDIT).
    { apply (rinv_step CP mB ΣB 0 m6 Σ6 NUMA_CREDIT RI ART6 ELV EFR ESP ltac:(lia)).
      apply (ok_trans mB m1 m6); [exact (ok_munch CP mB ΣB 0 m1 RI MU)|].
      apply (ok_pres_ex CP mB ΣB 0 (e_spa E0 + 304) 8 m1 m6 RI PR). right. lia. }
    assert (AP : forall x, s2_region E0 x -> ~ (CP <= x < CP + cc)).
    { intros x Hx. apply (newchunk_apart RT AF (snd w) ΣB m1 CP cc (e_spa E0) x ART1 LVB FRB SPB); [lia | lia | exact (NCL x Hx)]. }
    assert (HM6 : MEMI (env_at E0 m6) nxt [c0; c8; c16; c24; c32; c40; c48; c56; c64; c72; c80; c88; c96; c104; c112; c120; c128; c136; c144; c152; c160; c168; c176; c184; c192; c200; c272; c288; C8 v] sc fc m6).
    { eapply (MEMI_transport_out E0 mB m1 m6); [exact OK0 | repeat constructor; assumption | exact HM0 | | exact OUTC | exact MI6 | exact ST6 | exact FRM].
      intros a [H1 H2]. apply PR; [exact (rinv_client CP mB ΣB 0 _ RI (or_introl H1)) | exact H2]. }
    assert (CPB6 : bytes_at bsegs m6 CP (zbytes (crs (rtxt E0)))).
    { apply (bytes_at_agree bsegs m1 m6 CP _ CPB). intros a Ha. cbv beta in Ha. rewrite CBL, RB in Ha.
      pose proof (rinv_cp_ok CP mB ΣB 0 RI) as (_ & CLO & _). change (rtxt (env_at E0 mB)) with (rtxt E0) in CLO. rewrite RB in CLO. cbn [env_at e_lo] in CLO.
      apply PR; [apply (rinv_client CP mB ΣB 0 _ RI); right; lia | lia]. }
    destruct RS as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F' & fc' & ->).
    cbn [ms_fcsr] in F0'. rewrite (ret_pc_even RA HRA HRA2) in HA'.
    refine (HK m6 Σ6 flag v t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' RI6 _ CPB6 T c' HA' Hk).
    eapply (MEMI_transport E0 m6 m6 m6); [exact OK0 | repeat constructor; assumption | reflexivity | exact HM6 | intros a _; reflexivity | exact MI6 | exact ST6 | exact F0'].
  Qed.

  Hypothesis KC : forall w' v r, good w' 1 -> num_word v -> docend_k (gapp (wE w') [v; r] []) (wQ w') (mkst 1 0 3 0 []).
  Hypothesis GSHZ : g_shz RT E0 good.
  Hypothesis GKX : g_kx RT PMc E0 K good.
  Hypothesis HSLOWF : slowfa_cps RT.
  Hypothesis HPFF : pffa_cps RT.
  Hypothesis AFC : forall Σ m, ART RT Σ m -> cli_got_nothrow m.

  Lemma w_delC : forall CP mB ΣB cr, rinv CP mB ΣB cr -> cr <= NUMA_CREDIT -> rdelC_k (env_at E0 mB) (aevt RT PMc ΣB K) CP.
  Proof using AF FDO MST OK0 HT1 F0 RTF HG GROOT LFRESH KC GSHZ GKX.
    intros CP mB ΣB cr RI HCR. unfold rdelC_k. intros until m1. intros HM HR HTP HL3. apply evt_done.
    eapply (root_del_gen CP mB ΣB cr RI HCR 0xbcc54 ltac:(lia) eq_refl); [ | | exact HM | ]; [repeat constructor | reflexivity |].
    intros w'' v t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' HG'' HM''.
    apply (aevt_evt RT AF PMc MST).
    pose proof (seg_numr_retC (wE w'') (env_at_ok E0 _ OK0) (GSHZ w'' 1 HG'') (wQ w'') (GKX w'' 1 (e_tws E0) (e_sbs E0) HG'')
                  ltac:(intros H3; exfalso; clear - H3 HT1; unfold Sj_stage2_main.wE in H3; cbn [e_tws env_at] in H3; lia)) as KR. unfold rretC_k in KR.
    eapply evt_eq; [| eapply (KR r tp); [exact HM'' | exact HR | exact HTP | exact HL3]]. reflexivity.
  Qed.

  Lemma w_delC3 : forall (v r : Z) CP mB ΣB cr, num_word v -> rinv CP mB ΣB cr -> cr <= NUMA_CREDIT -> rdelC_k (gapp (env_at E0 mB) [v; r] []) (aevt RT PMc ΣB K) CP.
  Proof using AF FDO MST OK0 F0 RTF HG GROOT LFRESH KC GSHZ GKX.
    intros v r CP mB ΣB cr Hv RI HCR. unfold rdelC_k. intros until m1. intros HM HR HTP HL3. apply evt_done.
    eapply (root_del_gen_g [v; r] CP mB ΣB cr RI HCR 0xbcc54 ltac:(lia) eq_refl); [ | | exact HM | ]; [repeat constructor | reflexivity |].
    intros w'' v0 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' HG'' HM''.
    apply (aevt_evt RT AF PMc MST).
    pose proof (seg_numr_retC (gapp (wE w'') [v; r] []) (env_ok_gapp _ _ _ (env_at_ok E0 _ OK0)) (GSHZ w'' 1 HG'') (wQ w'') (GKX w'' 1 (e_tws E0 ++ [v; r]) (e_sbs E0 ++ []) HG'')
                  (fun _ => KC w'' v r HG'' Hv)) as KR. unfold rretC_k in KR.
    eapply evt_eq; [| eapply (KR r0 tp); [exact HM'' | exact HR | exact HTP | exact HL3]]. reflexivity.
  Qed.

  Lemma w_delB : forall CP mB ΣB cr, rinv CP mB ΣB cr -> cr <= NUMA_CREDIT -> rdelB_k (env_at E0 mB) (aevt RT PMc ΣB K) CP.
  Proof using AF FDO MST OK0 F0 RTF HG GROOT LFRESH GSHZ GKX.
    intros CP mB ΣB cr RI HCR. unfold rdelB_k. intros until m1. intros HM HERR. apply evt_done.
    destruct HM as (nxt & sc & HM). do 28 (let j := fresh "j" in destruct HM as (j & HM)).
    eapply (root_del_gen CP mB ΣB cr RI HCR 0xbcc34 ltac:(lia) eq_refl); [ | | exact HM | ]; [repeat constructor | reflexivity |].
    intros w'' v' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' HG'' HM''.
    apply (aevt_evt RT AF PMc MST).
    pose proof (seg_numr_retB (wE w'') (env_at_ok E0 _ OK0) (GSHZ w'' 1 HG'') (wQ w'') (GKX w'' 1 (e_tws E0) (e_sbs E0) HG'')) as KR. unfold rretB_k in KR.
    eapply evt_eq; [| eapply (KR err); [unfold MEMX; do 30 eexists; exact HM'' | exact HERR]]. reflexivity.
  Qed.

  Lemma w_delA : forall CP mB ΣB cr, rinv CP mB ΣB cr -> cr <= NUMA_CREDIT -> rdelAc_k (env_at E0 mB) (aevt RT PMc ΣB K) CP.
  Proof using AF FDO MST OK0 F0 RTF HG GROOT LFRESH GSHZ GKX.
    intros CP mB ΣB cr RI HCR. unfold rdelAc_k. intros until m1. intros HM. apply evt_done.
    destruct HM as (nxt & sc & HM). do 29 (let j := fresh "j" in destruct HM as (j & HM)).
    eapply (root_del_gen CP mB ΣB cr RI HCR 0xb73b0 ltac:(lia) eq_refl); [ | | exact HM | ]; [repeat constructor | reflexivity |].
    intros w'' v' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' HG'' HM''.
    apply (aevt_evt RT AF PMc MST).
    pose proof (seg_numr_retA (wE w'') (env_at_ok E0 _ OK0) (GSHZ w'' 1 HG'') (wQ w'') (GKX w'' 1 (e_tws E0) (e_sbs E0) HG'')) as KR. unfold rretA_k in KR.
    eapply evt_eq; [| eapply KR; unfold MEMXJ; do 31 eexists; exact HM'']. reflexivity.
  Qed.

  Let s0 : st := mkst 0 0 1 0 [].

  Lemma w_slow : forall CP mB ΣB, rinv CP mB ΣB 0 -> numr_slowcall_k (env_at E0 mB) (aevt RT PMc ΣB K) CP s0.
  Proof using AF FDO MST OK0 HT1 F0 RTF HG GROOT LFRESH KC GSHZ GKX HSLOWF.
    intros CP mB ΣB RI. unfold numr_slowcall_k. intros until m1. intros [HM CPB]. apply evt_done.
    change (rtxt (env_at E0 mB)) with (rtxt E0) in CPB.
    eapply (root_call_gen 0xee144 9 0 0xbda54 HSLOWF ltac:(lia) eq_refl CP mB ΣB RI); [ | exact HM | exact CPB | ]; [repeat constructor |].
    intros m6 Σ6 flag v t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' RI6 HM6 CPB6.
    apply (aevt_evt RT AF PMc MST).
    pose proof (seg_numr_after_slow (env_at E0 m6) (env_at_ok E0 _ OK0) (rinv_shz CP m6 Σ6 _ RI6) CP (rinv_cp_ok CP m6 Σ6 _ RI6) (rinv_cp_shz CP m6 Σ6 _ RI6)
                  (aevt RT PMc Σ6 K) (if flag then 9 else 0) v ltac:(destruct flag; [left | right]; reflexivity) HT1
                  (fun v' r' Hv => w_delC3 v' r' CP m6 Σ6 _ Hv RI6 ltac:(lia))) as KR.
    unfold numr_slowret_k in KR.
    eapply evt_eq; [| eapply KR; split; [exact HM6 | exact CPB6]]. reflexivity.
  Qed.

  Lemma w_fb : forall CP mB ΣB, rinv CP mB ΣB 0 -> numr_fbcall_k (env_at E0 mB) (aevt RT PMc ΣB K) CP s0.
  Proof using AF FDO MST OK0 HT1 F0 RTF HG GROOT LFRESH KC GSHZ GKX HPFF.
    intros CP mB ΣB RI. unfold numr_fbcall_k. intros until m1. intros [HM CPB]. apply evt_done.
    change (rtxt (env_at E0 mB)) with (rtxt E0) in CPB.
    eapply (root_call_gen 0xee248 0 1 0xbe0fc HPFF ltac:(lia) eq_refl CP mB ΣB RI); [ | exact HM | exact CPB | ]; [repeat constructor |].
    intros m6 Σ6 flag v t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' RI6 HM6 CPB6.
    apply (aevt_evt RT AF PMc MST).
    pose proof (seg_numr_after_fb (env_at E0 m6) (env_at_ok E0 _ OK0) (rinv_shz CP m6 Σ6 _ RI6) CP (rinv_cp_ok CP m6 Σ6 _ RI6) (rinv_cp_shz CP m6 Σ6 _ RI6)
                  (aevt RT PMc Σ6 K) (if flag then 0 else 1) v ltac:(destruct flag; [left | right]; reflexivity) HT1 (w_delC CP m6 Σ6 _ RI6 ltac:(lia))
                  (fun v' r' Hv => w_delC3 v' r' CP m6 Σ6 _ Hv RI6 ltac:(lia))) as KR.
    unfold numr_fbret_k in KR.
    eapply evt_eq; [| eapply KR; split; [exact HM6 | exact CPB6]]. reflexivity.
  Qed.

  Theorem rootnum_in_w : rootprim_k (wE w) (wQ w) 0xb71f8.
  Proof using AF FDO MST OK0 HT1 F0 RTF HG GROOT LFRESH KC GSHZ GKX HSLOWF HPFF AFC.
    unfold rootprim_k. intros until m1. intros HM.
    assert (HMW : munch (s2_W (env_at E0 (wm RT w))) (wm RT w) m1 /\ wmono bsegs (wm RT w) m1).
    { destruct HM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MU & WM & _ & _). split; [exact MU | exact WM]. }
    pose proof (AFC (snd w) m1 (w_art m1 (proj1 HMW) (proj2 HMW))) as GOT.
    eapply (seg_numr_pro1 (wE w) (env_at_ok E0 _ OK0) (GSHZ w 0 HG) (wQ w)); [ | exact GOT | exact HM ].
    apply root_new. intros CP m2 Σ2 RI2.
    pose proof RI2 as (ART2 & LV2 & _ & SP2 & _ & _ & CP0 & _).
    assert (CPR : 0 < CP < 2^47).
    { assert (INC : In (CP, cc) (rt_live RT Σ2)) by (rewrite LV2; left; reflexivity).
      pose proof (af_live_range RT AF Σ2 m2 CP cc ART2 INC) as (_ & P1 & _). pose proof (af_sp0_range RT AF Σ2 m2 ART2) as SPR.
      pose proof rl_pos. ul. }
    apply (seg_numr_pro2 (env_at E0 m2) (env_at_ok E0 _ OK0) (rinv_shz CP m2 Σ2 _ RI2) (aevt RT PMc Σ2 K) CP CPR).
    apply (root_memcpy CP m2 Σ2 RI2). intros m3 RI3 BY3.
    apply (seg_numr_pro3 (env_at E0 m3) (env_at_ok E0 _ OK0) (rinv_shz CP m3 Σ2 _ RI3) (aevt RT PMc Σ2 K) CP CPR).
    apply (root_memset CP m3 Σ2 RI3 BY3). intros m4 RI4 CPY4.
    exact (seg_numr (env_at E0 m4) (env_at_ok E0 _ OK0) (rinv_shz CP m4 Σ2 _ RI4) CP (rinv_cp_ok CP m4 Σ2 _ RI4) (rinv_cp_shz CP m4 Σ2 _ RI4) (aevt RT PMc Σ2 K)
             HT1 (w_delA CP m4 Σ2 0 RI4 ltac:(unfold NUMA_CREDIT; lia)) (w_delB CP m4 Σ2 0 RI4 ltac:(unfold NUMA_CREDIT; lia)) (w_delC CP m4 Σ2 0 RI4 ltac:(unfold NUMA_CREDIT; lia))
             (fun v r Hv => w_delC3 v r CP m4 Σ2 0 Hv RI4 ltac:(unfold NUMA_CREDIT; lia))
             (w_slow CP m4 Σ2 RI4) (w_fb CP m4 Σ2 RI4)).
  Qed.
End RootW.

Lemma rootw_facts_ghost : forall RT E0 tws sbs w, rootw_facts RT E0 w -> rootw_facts RT (s2_ghost E0 tws sbs) w.
Proof.
  intros RT E0 tws sbs w [N L C S D]. constructor; [destruct N; constructor; assumption | exact L | exact C | exact S | exact D].
Qed.

Theorem rootnum_world : forall RT, art_facts RT -> rt_contracts_f RT -> slowfa_cps RT -> pffa_cps RT ->
  (forall Σ m, ART RT Σ m -> cli_got_nothrow m) -> live_fresh RT -> rootnum_stmt RT.
Proof.
  intros RT AF RTF HSL HPF AFC LF PMc FDO MST E0 OK0 K good GSHZ GMONO GKX GNUM GSTEP GROOTF GROOT w h0 HG HNUM KC.
  exact (rootnum_in_w RT AF PMc FDO MST (s2_ghost E0 [h0] []) (env_ok_ghost _ _ _ OK0) eq_refl K w (rootw_facts_ghost RT E0 [h0] [] w (GROOTF w HG))
           RTF good HG GROOT LF KC GSHZ GKX HSL HPF AFC).
Qed.
