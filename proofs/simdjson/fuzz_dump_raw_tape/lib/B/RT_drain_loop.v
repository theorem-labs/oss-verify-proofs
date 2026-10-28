(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS MState.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout RT_iface D_defs R_cache_defs R_prim_defs R_glue_defs R_m2s R_prim_kit R_thread R_depot_defs R_quar_defs R_qrec_defs R_qrecycle R_qdorec R_qcbrec RT_state RT_rep RT_frame RT_freelift RT_geo0 RT_fkit RT_freestate RT_drain_defs RT_drain_led RT_drain_start RT_drain_kit RT_drain_geo RT_drain_ldefs RT_drain_art4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A.Shadow.GW}.
Lemma dl_cps_ex : forall (P : rtsA -> config -> Prop) (phi : rtsA -> Prop) (Q : config -> Prop),
  (forall x, phi x -> cps bsegs (P x) Q) -> cps bsegs (fun cf => exists x, P x cf /\ phi x) Q.
Proof. intros P phi Q H T cf (x & HP & Hphi) Hk. exact (H x Hphi T cf HP Hk). Qed.

Lemma dl_evt : forall (Σk : rtsA) (PMc : Model -> Prop) (Pm Q : machine_state -> Prop), mat_stable PMc ->
  (forall ms, Pm ms -> evt bsegs Q ms) -> cps bsegs (ASTA RTA Σk PMc Pm) (ASTA RTA Σk PMc Q).
Proof. intros Σk PMc Pm Q MST H. exact (ast_evt bsegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σk) _ _ _ (fl_ASTA_mat_stable Σk PMc MST) H). Qed.

Lemma geo_of_wfP : forall Σ P, rt_wfP Σ P -> geo_ok Σ.
Proof. intros Σ P (H1 & H2 & _ & H4 & _ & H6 & _). exact (conj H1 (conj H2 (conj H4 H6))). Qed.

Lemma hqb_of_wfP : forall Σ P, rt_wfP Σ P ->
  Forall (fun b => exists j, nth_error (r_st (pr Σ 24)) j = Some CkBatch /\ fst b = p_abeg (l_SB (lay Σ)) 24 j) (ql Σ ++ qg Σ).
Proof.
  intros Σ P (_ & _ & _ & _ & (_ & _ & _ & Q4 & _) & _). unfold qallP in Q4. rewrite app_assoc in Q4. apply Forall_app in Q4. exact (proj1 Q4).
Qed.

Section DLoop.
Variable p : dlp.
#[local] Notation Σ0 := (dl_Σ0 p).
#[local] Notation usp := (dl_usp p).
#[local] Notation lo := (dl_lo p).
#[local] Notation PMc := (dl_PMc p).
#[local] Notation C := (dl_usp p - 2288).
#[local] Notation T := (l_T (lay (dl_Σ0 p))).
#[local] Notation SB := (l_SB (lay (dl_Σ0 p))).
#[local] Notation FIN := (dl_fin p).
Hypothesis MST : mat_stable (dl_PMc p).
Hypothesis HLO : l_ACEIL (lay (dl_Σ0 p)) <= dl_lo p.
Hypothesis HLO2 : dl_lo p + 0x4000 <= dl_usp p + -2208.
Hypothesis HSP : dl_usp p <= 2 ^ 47.
Hypothesis HG0 : geo_ok (dl_Σ0 p).

Hypothesis ITEM : forall (j : list byte) (Σk : rtsA) (b : Z) (ib : nat) (ents : list (Z * Z)) (i : nat) (rest : list batch),
  (i < length ents)%nat -> rt_wfP Σk ((b, skipn i ents) :: rest) -> dl_sig p Σk ->
  nth_error (r_st (pr Σk 24)) ib = Some CkBatch -> b = p_abeg (l_SB (lay Σk)) 24 ib ->
  cps bsegs (ASTA RTA Σk PMc (dl_Q p j b ents i rest Σk))
    (fun cf => exists Σk' : rtsA, ASTA RTA Σk' PMc (dl_N p j b ents i rest Σk') cf
       /\ (rt_wfP Σk' ((b, skipn (S i) ents) :: rest) /\ dl_sig p Σk' /\ nth_error (r_st (pr Σk' 24)) ib = Some CkBatch)).
Hypothesis BATCH : forall (j : list byte) (Σk : rtsA) (b : Z) (ib : nat) (ents : list (Z * Z)) (rest : list batch),
  rt_wfP Σk ((b, []) :: rest) -> dl_sig p Σk ->
  nth_error (r_st (pr Σk 24)) ib = Some CkBatch -> b = p_abeg (l_SB (lay Σk)) 24 ib ->
  cps bsegs (ASTA RTA Σk PMc (dl_D p j b ents rest Σk))
    (fun cf => exists Σk' : rtsA, ASTA RTA Σk' PMc (dl_B p j rest Σk') cf /\ (rt_wfP Σk' rest /\ dl_sig p Σk')).

Lemma dl_nums : 0 < SB /\ SB_ok (l_ACEIL (lay Σ0)) SB /\ r24 SB + 2 ^ 32 <= lo /\ 0x6ce000 <= lo /\ lo + 0x400 <= C - 112
  /\ C + 32 <= 2 ^ 47 /\ 0 <= T + 208 < 2 ^ 64 /\ 0 <= usp - 2128 < 2 ^ 64 /\ l_ACEIL (lay Σ0) <= lo.
Proof using HLO HLO2 HSP HG0.
  pose proof (dk_geo Σ0 HG0) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
  pose proof (g_prb Σ0 HG0) as (P1 & P2 & P3).
  pose proof (g_grant Σ0 HG0 T 4096 ltac:(unfold startup_grants; right; right; left; reflexivity)) as (T1 & T2 & T3 & T4 & T5).
  assert (HSB : SB_ok (l_ACEIL (lay Σ0)) SB).
  { pose proof (dg_ok Σ0 HG0) as (_ & X & _). exact X. }
  pose proof HSB as (S1 & S2 & S3 & S4). unfold r24, kHighShadowEnd, SEGTOP_A in *.
  repeat split; try assumption; lia.
Qed.

Lemma dl_bslot : forall Σk ib, geo_ok Σk -> lay Σk = lay Σ0 -> nth_error (r_st (pr Σk 24)) ib = Some CkBatch ->
  0 < p_abeg SB 24 ib /\ p_abeg SB 24 ib + 8192 <= lo /\ r24 SB <= p_abeg SB 24 ib /\ p_abeg SB 24 ib + 8192 <= r24 SB + 2 ^ 32.
Proof using HLO HLO2 HSP HG0.
  intros Σk ib HG El Hib. pose proof dl_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9).
  pose proof (dk_slot_in Σk HG 24 ib _ ltac:(lia) Hib) as (S1 & S2 & S3 & S4 & S5 & S6). rewrite El in *.
  change (ClassSize 24) with 8192 in *. unfold rb, r24, kUserCap in *. repeat split; lia.
Qed.

Lemma dl_mem_step : forall j Σk rest rest' (m m' : mem) (W : list ivl), dl_mem p j Σk rest m -> geo_ok Σk -> dl_sig p Σk ->
  live_wf Σk -> depot_ok (dep Σk) (l_DNB (lay Σk)) (l_SSB (lay Σk)) (l_ACEIL (lay Σk)) ->
  Forall (fun b => exists j, nth_error (r_st (pr Σk 24)) j = Some CkBatch /\ fst b = p_abeg (l_SB (lay Σk)) 24 j) (ql Σk ++ qg Σk) ->
  Forall (fun iv => lo <= fst iv /\ snd iv <= C + 32) W -> munch W m m' -> wmono bsegs m m' -> mem_inv bsegs m' ->
  stk bsegs m' lo (C - 112) ->
  drec_mem m' C SB j (T + 208) (usp - 2128) (Z_to_bv 64 0x5b600) (dl_r0 p) (dl_r1 p) (dl_r2 p) (dl_r3 p) (dl_r4 p)
    (dl_r5 p) (dl_r6 p) (dl_r7 p) (dl_r8 p) (dl_r9 p) rest' ->
  dl_mem p j Σk rest' m'.
Proof using HLO HLO2 HSP HG0.
  intros j Σk rest rest' m m' W (A & MI & ST & WM0 & RP & FR & QR) HG (El & Elv & Efr & _) Hlive Hdep HQB HW MU WM MI' ST' (FR' & _ & QR').
  pose proof dl_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9).
  assert (HL : l_ACEIL (lay Σk) <= lo) by (rewrite El; exact N9).
  split; [exact (artc_stk Σk m m' W lo (C + 32) HG HL HW A Hdep HQB MU WM)|].
  split; [exact MI'|]. split; [exact ST'|]. split; [destruct WM0 as (G & WG & HGo); exists G; split; [exact (wmono_out_wmono G _ m m' WG WM) | exact HGo]|].
  split; [|split; [exact FR' | exact QR']].
  pose proof (client_stk Σk m m' W lo (C + 32) HG HL ltac:(lia) HW Hlive MU) as RP'. rewrite Elv, Efr in RP'.
  intros a Ha. rewrite (RP' a Ha). exact (RP a Ha).
Qed.

Lemma dl_drec : forall j Σk rest (m : mem), dl_mem p j Σk rest m -> lay Σk = lay Σ0 ->
  drec_mem m C SB j (T + 208) (usp - 2128) (Z_to_bv 64 0x5b600) (dl_r0 p) (dl_r1 p) (dl_r2 p) (dl_r3 p) (dl_r4 p)
    (dl_r5 p) (dl_r6 p) (dl_r7 p) (dl_r8 p) (dl_r9 p) rest.
Proof.
  intros j Σk rest m (A & _ & _ & _ & _ & FR & QR) El. split; [exact FR|]. split; [|exact QR].
  pose proof (proj1 (proj1 A)) as (IC1 & _). rewrite El in IC1.
  apply (proj1 (rwc_app bsegs m _ [C8 (Z_to_bv 64 SB)] [C8 (Z_to_bv 64 0xffffffff); C8 (Z_to_bv 64 (RIS_of SB))])) in IC1.
  exact (proj1 IC1).
Qed.

Lemma dl_batch_of : forall Σk b ents rest, rt_wfP Σk ((b, ents) :: rest) ->
  exists ib, nth_error (r_st (pr Σk 24)) ib = Some CkBatch /\ b = p_abeg (l_SB (lay Σk)) 24 ib.
Proof.
  intros Σk b ents rest (_ & _ & _ & _ & (_ & _ & _ & Q4 & _) & _). unfold qallP in Q4.
  assert (Hb : In (b, ents) (ql Σk ++ qg Σk ++ (b, ents) :: rest)) by (apply in_app_iff; right; apply in_app_iff; right; left; reflexivity).
  destruct (proj1 (Forall_forall _ _) Q4 _ Hb) as (ib & Hib & Eb). exists ib. split; [exact Hib | exact Eb].
Qed.

Lemma dl_from_N : forall k j Σk b ib ents i rest, length ents = (S i + k)%nat ->
  rt_wfP Σk ((b, skipn (S i) ents) :: rest) -> dl_sig p Σk ->
  nth_error (r_st (pr Σk 24)) ib = Some CkBatch -> b = p_abeg (l_SB (lay Σk)) 24 ib ->
  cps bsegs (ASTA RTA Σk PMc (dl_N p j b ents i rest Σk))
    (fun cf => exists Σk' : rtsA, ASTA RTA Σk' PMc (dl_B p j rest Σk') cf /\ (rt_wfP Σk' rest /\ dl_sig p Σk')).
Proof using MST HLO HLO2 HSP HG0 ITEM BATCH.
  induction k as [|k IH]; intros j Σk b ib ents i rest Hlen HWP HS Hib Eb.
  -
    assert (Hsk : skipn (S i) ents = []) by (apply skipn_all2; lia).
    rewrite Hsk in HWP.
    eapply (cps_seq bsegs); [|exact (BATCH j Σk b ib ents rest HWP HS Hib Eb)].
    apply (dl_evt Σk PMc _ _ MST).
    intros ms (ra0 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m & -> & DM & QB).
    pose proof dl_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9).
    pose proof (geo_of_wfP _ _ HWP) as HG. pose proof HS as (El & _).
    pose proof (dl_bslot Σk ib HG El Hib) as (B1 & B2 & B3 & B4). rewrite El in Eb. subst b.
    pose proof DM as (_ & MI & ST & _).
    eapply evt_mono; [apply (drec_next_deal_spec ra0 (dl_gp p) (Z_to_bv 64 tpA) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (dl_s10 p) (dl_s11 p)
                               t3 t4 t5 t6 (dl_F p) (dl_fc p) m (l_ACEIL (lay Σ0)) C SB lo (T + 208) (usp - 2128) j
                               (Z_to_bv 64 0x5b600) (dl_r0 p) (dl_r1 p) (dl_r2 p) (dl_r3 p) (dl_r4 p) (dl_r5 p) (dl_r6 p) (dl_r7 p)
                               (dl_r8 p) (dl_r9 p) _ ents rest i)|].
    1: lia. 1: exact B3. 1: exact B4. 1: exact N2. 1: lia. 1: exact (dl_drec j Σk rest m DM El). 1: exact QB. 1: exact ST. 1: exact N3.
    1: lia. 1: lia. 1: exact MI.
    intros ms' (t0' & t1' & t2' & a4' & a5' & a6' & a7' & s6' & s7' & s8' & s9' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & DM' & QB' & ST').
    exists t0', t1', t2', a4', a5', a6', a7', s6', s7', s8', s9', t3', t4', t5', t6', m'. split; [reflexivity|]. split; [|exact QB'].
    pose proof HWP as (_ & _ & Hlive & _ & _ & _ & _ & Hdep & _).
    exact (dl_mem_step j Σk rest rest m m' [] DM HG HS Hlive Hdep (hqb_of_wfP _ _ HWP) (Forall_nil _) MU WM MI' ST' DM').
  -
    pose proof HS as (El & _).
    eapply (cps_seq bsegs); [| eapply (cps_seq bsegs); [exact (ITEM j Σk b ib ents (S i) rest ltac:(lia) HWP HS Hib Eb)|]].
    + apply (dl_evt Σk PMc _ _ MST).
      intros ms (ra0 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m & -> & DM & QB).
      pose proof dl_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9).
      pose proof (geo_of_wfP _ _ HWP) as HG.
      pose proof (dl_bslot Σk ib HG El Hib) as (B1 & B2 & B3 & B4). rewrite El in Eb. subst b.
      pose proof DM as (_ & MI & ST & _).
      eapply evt_mono; [apply (drec_next_qcb_spec ra0 (dl_gp p) (Z_to_bv 64 tpA) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (dl_s10 p) (dl_s11 p)
                                 t3 t4 t5 t6 (dl_F p) (dl_fc p) m C SB lo (T + 208) (usp - 2128) j
                                 (Z_to_bv 64 0x5b600) (dl_r0 p) (dl_r1 p) (dl_r2 p) (dl_r3 p) (dl_r4 p) (dl_r5 p) (dl_r6 p) (dl_r7 p)
                                 (dl_r8 p) (dl_r9 p) _ ents rest i)|].
      1: lia. 1: exact B1. 1: exact B2. 1: exact (dl_drec j Σk rest m DM El). 1: exact QB. 1: exact ST. 1: lia. 1: lia. 1: exact MI.
      intros ms' (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & DM' & QB' & ST').
      exists t0', t1', t2', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'. split; [reflexivity|]. split; [|exact QB'].
      pose proof HWP as (_ & _ & Hlive & _ & _ & _ & _ & Hdep & _).
      exact (dl_mem_step j Σk rest rest m m' [] DM HG HS Hlive Hdep (hqb_of_wfP _ _ HWP) (Forall_nil _) MU WM MI' ST' DM').
    + apply dl_cps_ex. intros Σk' (HWP' & HS' & Hib').
      pose proof HS' as (El' & _).
      exact (IH j Σk' b ib ents (S i) rest ltac:(lia) HWP' HS' Hib' ltac:(rewrite El', <- El; exact Eb)).
Qed.

Lemma dl_from_Q0 : forall j Σk b ib ents rest, ents <> [] -> rt_wfP Σk ((b, ents) :: rest) -> dl_sig p Σk ->
  nth_error (r_st (pr Σk 24)) ib = Some CkBatch -> b = p_abeg (l_SB (lay Σk)) 24 ib ->
  cps bsegs (ASTA RTA Σk PMc (dl_Q p j b ents 0 rest Σk))
    (fun cf => exists Σk' : rtsA, ASTA RTA Σk' PMc (dl_B p j rest Σk') cf /\ (rt_wfP Σk' rest /\ dl_sig p Σk')).
Proof using MST HLO HLO2 HSP HG0 ITEM BATCH.
  intros j Σk b ib ents rest Hne HWP HS Hib Eb. pose proof HS as (El & _).
  destruct ents as [|e es]; [congruence|].
  eapply (cps_seq bsegs); [exact (ITEM j Σk b ib (e :: es) 0 rest ltac:(cbn; lia) HWP HS Hib Eb)|].
  apply dl_cps_ex. intros Σk' (HWP' & HS' & Hib'). pose proof HS' as (El' & _).
  exact (dl_from_N (length es) j Σk' b ib (e :: es) 0 rest ltac:(cbn; lia) HWP' HS' Hib' ltac:(rewrite El', <- El; exact Eb)).
Qed.

Lemma dl_from_B : forall j rest Σk, rt_wfP Σk rest -> dl_sig p Σk -> cps bsegs (ASTA RTA Σk PMc (dl_B p j rest Σk)) FIN.
Proof using MST HLO HLO2 HSP HG0 ITEM BATCH.
  intros j. induction rest as [|[b ents] rest IH]; intros Σk HWP HS; pose proof HS as (El & _);
    pose proof (geo_of_wfP _ _ HWP) as HG; pose proof HWP as (_ & _ & Hlive & _ & _ & _ & _ & Hdep & _);
    pose proof dl_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9).
  -
    eapply (cps_seq bsegs).
    + apply (dl_evt Σk PMc _ (dl_R p Σk) MST).
      intros ms (ra0 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s4 & s6 & s7 & s8 & s9 & t3 & t4 & t5 & t6 & m & -> & DM).
      pose proof DM as (A & MI & ST & WM0 & RP & _).
      eapply evt_mono; [apply (drec_loop_ret_spec ra0 (dl_gp p) (Z_to_bv 64 tpA) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9
                                 (dl_s10 p) (dl_s11 p) t3 t4 t5 t6 (dl_F p) (dl_fc p) m C SB lo (T + 208) (usp - 2128) j
                                 (Z_to_bv 64 0x5b600) (dl_r0 p) (dl_r1 p) (dl_r2 p) (dl_r3 p) (dl_r4 p) (dl_r5 p) (dl_r6 p) (dl_r7 p)
                                 (dl_r8 p) (dl_r9 p))|].
      1: exact (dl_drec j Σk [] m DM El). 1: exact ST. 1: lia. 1: exact N4. 1: exact N6. 1: exact MI.
      intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & QR' & ST').
      exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'. split; [reflexivity|].
      assert (HL : l_ACEIL (lay Σk) <= lo) by (rewrite El; exact N9).
      split; [exact (artc_stk Σk m m' [] lo (C + 32) HG HL (Forall_nil _) A Hdep (hqb_of_wfP _ _ HWP) MU WM)|].
      split; [exact MI'|]. split; [exact ST'|].
      split; [destruct WM0 as (G & WG & HGo); exists G; split; [exact (wmono_out_wmono G _ m m' WG WM) | exact HGo]|]. split; [|exact QR'].
      pose proof (client_stk Σk m m' [] lo (C + 32) HG HL ltac:(lia) (Forall_nil _) Hlive MU) as RP'.
      pose proof HS as (_ & Elv & Efr & _). rewrite Elv, Efr in RP'.
      intros a Ha. rewrite (RP' a Ha). exact (RP a Ha).
    + intros T0 cf Hcf Hk. apply Hk. exists Σk. split; [exact Hcf | split; [exact HWP | exact HS]].
  - destruct (dl_batch_of Σk b ents rest HWP) as (ib & Hib & Eb).
    pose proof (dl_bslot Σk ib HG El Hib) as (B1 & B2 & B3 & B4).
    assert (QW : qwf SB ((b, ents) :: rest)) by (pose proof (qwf_of_wfP _ _ HWP) as X; rewrite El in X; exact X).
    assert (QB : RT_state.qbytes ((b, ents) :: rest) <= 2 ^ 40) by (destruct HWP as (_ & _ & _ & _ & (_ & _ & X & _) & _); exact X).
    rewrite qbytes_eq in QB.
    destruct ents as [|e es].
    +
      eapply (cps_seq bsegs); [| eapply (cps_seq bsegs); [exact (BATCH j Σk b ib [] rest HWP HS Hib Eb)|]].
      * apply (dl_evt Σk PMc _ _ MST).
        intros ms (ra0 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s4 & s6 & s7 & s8 & s9 & t3 & t4 & t5 & t6 & m & -> & DM).
        pose proof DM as (_ & MI & ST & _).
        eapply evt_mono; [apply (drec_loop_deal_spec ra0 (dl_gp p) (Z_to_bv 64 tpA) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9
                                   (dl_s10 p) (dl_s11 p) t3 t4 t5 t6 (dl_F p) (dl_fc p) m (l_ACEIL (lay Σ0)) C SB lo (T + 208) (usp - 2128)
                                   j (Z_to_bv 64 0x5b600) (dl_r0 p) (dl_r1 p) (dl_r2 p) (dl_r3 p) (dl_r4 p) (dl_r5 p) (dl_r6 p)
                                   (dl_r7 p) (dl_r8 p) (dl_r9 p) b rest)|].
        1: exact QW. 1: lia. 1: exact N2. 1: lia. 1: exact (dl_drec j Σk _ m DM El). 1: exact ST. 1: exact N3. 1: lia. 1: lia. 1: exact MI.
        intros ms' (t0' & t1' & t2' & a4' & a5' & a6' & a7' & s6' & s7' & s8' & s9' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & DM' & QB' & ST').
        exists t0', t1', t2', a4', a5', a6', a7', s6', s7', s8', s9', t3', t4', t5', t6', m'. split; [reflexivity|]. split; [|exact QB'].
        exact (dl_mem_step j Σk _ rest m m' [(C, C + 32)] DM HG HS Hlive Hdep (hqb_of_wfP _ _ HWP)
                 ltac:(repeat constructor; cbn [fst snd]; lia) MU WM MI' ST' DM').
      * apply dl_cps_ex. intros Σk' (HWP' & HS'). exact (IH Σk' HWP' HS').
    +
      eapply (cps_seq bsegs); [| eapply (cps_seq bsegs); [exact (dl_from_Q0 j Σk b ib (e :: es) rest ltac:(discriminate) HWP HS Hib Eb)|]].
      * apply (dl_evt Σk PMc _ _ MST).
        intros ms (ra0 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s4 & s6 & s7 & s8 & s9 & t3 & t4 & t5 & t6 & m & -> & DM).
        pose proof DM as (_ & MI & ST & _).
        eapply evt_mono; [apply (drec_loop_qcb_spec ra0 (dl_gp p) (Z_to_bv 64 tpA) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9
                                   (dl_s10 p) (dl_s11 p) t3 t4 t5 t6 (dl_F p) (dl_fc p) m C SB lo (T + 208) (usp - 2128)
                                   j (Z_to_bv 64 0x5b600) (dl_r0 p) (dl_r1 p) (dl_r2 p) (dl_r3 p) (dl_r4 p) (dl_r5 p) (dl_r6 p)
                                   (dl_r7 p) (dl_r8 p) (dl_r9 p) b (e :: es) rest)|].
        1: discriminate. 1: exact QW. 1: lia. 1: exact N1. 1: exact (dl_drec j Σk _ m DM El). 1: exact ST. 1: exact N3. 1: lia. 1: lia. 1: exact MI.
        intros ms' (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & DM' & QB' & ST').
        exists t0', t1', t2', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'. split; [reflexivity|]. split; [|exact QB'].
        exact (dl_mem_step j Σk _ rest m m' [(C, C + 32)] DM HG HS Hlive Hdep (hqb_of_wfP _ _ HWP)
                 ltac:(repeat constructor; cbn [fst snd]; lia) MU WM MI' ST' DM').
      * apply dl_cps_ex. intros Σk' (HWP' & HS'). exact (IH Σk' HWP' HS').
Qed.

End DLoop.

End GWIN.
