(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep Frame.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim SjModel PjModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjTape SjTapeList SjTapeTile SjPjSer.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface RT_iface2 RT_iface3 D_defs D_kit D_clx D_libiface I_lkit
     D_rlkit Sj_akit Sj_acps Sj_hkit Sj_num_akit Atp_hkit5A Pj_rtkA Pj_defsA Pj_cpsA Pj_ser_defsA Pj_ser_kitA Pj_ser_callsA Pj_ser_dispA Pj_ser_loopA Pj_ser_proA Pj_ser_epiA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Lemma cells_bytes_map_C1 : forall l : list byte, cells_bytes (map C1 l) = l.
Proof. induction l as [|b l IH]; [reflexivity|]. cbn [map cells_bytes cbytes app]. rewrite IH. reflexivity. Qed.
Lemma cells_size_map_C1 : forall l : list byte, cells_size (map C1 l) = length l.
Proof. induction l as [|b l IH]; [reflexivity|]. cbn [map cells_size csize length]. rewrite IH. reflexivity. Qed.
Lemma u8arr_of_C1s : forall (m : mem) A l, rw_cells bsegs m A (map C1 l) -> u8arr bsegs m A l.
Proof.
  intros m A l H. split.
  - pose proof (rw_cells_bytes_at bsegs m A _ H) as B. rewrite cells_bytes_map_C1 in B. exact B.
  - eapply rw_cells_wr_at; [exact H|]. rewrite cells_size_map_C1. lia.
Qed.

Lemma ser_frame_raw_size : forall f SB DOC w x, cells_size (ser_frame_raw f SB DOC w x) = 312%nat.
Proof. intros. reflexivity. Qed.

Section Top.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Hypothesis SM3W : stack_malloc3w_contract RT.
Variable PMc : Model -> Prop.
Hypothesis GROW : grow_cpsA RT PMc.
Hypothesis PSTR : str_stmtA RT PMc.
Hypothesis PI64 : i64_stmtA RT PMc.
Hypothesis PU64 : u64_stmtA RT PMc.
Hypothesis PDBL : dbl_stmtA RT PMc.
Hypothesis PTRUE : true_stmtA RT PMc.
Hypothesis PFALSE : false_stmtA RT PMc.
Hypothesis PNULL : null_stmtA RT PMc.
Hypothesis PKEY : key_stmtA RT PMc.
Notation aevt := (aevt RT PMc).
Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

Lemma ser_exitA : forall (E : pjenvA) (D : nat) (I : serI) (K : config -> Prop),
  fdfs_only PMc -> mat_stable PMc -> pjenvA_ok E -> sctxA E D I ->
  (forall (Σ' : rts RT) (st' : sbA) (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem),
     frm0 fc' -> ART RT Σ' m' -> mem_inv bsegs m' -> stk bsegs m' (pa_lo E) (si_q I) ->
     SBINVA E m' st' -> DOCREPA E m' -> sb_accA st' (si_j I) (si_c' I) -> pa_live RT Σ' E st' ->
     rt_frames RT Σ' = si_fr I -> rt_sp0 RT Σ' = si_sp0 I -> si_R I + pj_psi (pa_len E) st' <= rt_credit RT Σ' ->
     rt_pres_fp (pa_L E) (si_fr I) (si_q I) [(pa_SB E, pa_SB E + 88)] (si_m0 I) m' ->
     aevt Σ' K (MS (mkR (si_ra I) (wz (si_q I)) (si_gp I) (wz TPV_A) t0' t1' t2' (si_s0 I) (si_s1 I) a0' a1' a2' a3' a4' a5' a6' a7'
                       (si_s2 I) (si_s3 I) (si_s4 I) (si_s5 I) (si_s6 I) (si_s7 I) (si_s8 I) (si_s9 I) (si_s10 I) (si_s11 I) t3' t4' t5' t6')
                  F' (ret_pc (si_ra I)) fc' None m' (seg_rom bsegs))) ->
  exit_KA RT PMc E I K.
Proof using AF RC.
  intros E D I K FDO MST OK CX KFIN. unfold exit_KA.
  intros isobj Σc st m F fc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 HSM FRM ACC CR.
  destruct st as [buf size cap hp kk]. cbn [sa_size] in ACC.
  ser_envA OK CX. unbox FSB; unbox FDOC; unbox SHSB; unbox SHDC; unbox SHf; unbox DD.
  pose proof (c_F4 E D I CX) as IN4. pose proof (c_R E D I CX) as R0. pose proof (c_b32 E D I CX) as B32. pose proof (c_sp0 E D I CX) as (W1 & W2).
  pose proof (c_fF E D I CX) as FF.
  pose proof (env_rangesA E OK) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & FS4 & B1 & B2 & D1 & D2 & FL & _ & _).
  pose proof (env_div8 E D I OK CX) as (ED & EF & _ & ESB & EFS & Efs & _).
  destruct HSM as [x0 HSM]. pose proof HSM as [HR HC]. pose proof HR as (ART0 & LV & FRS & SP & DR & SBSH & PU & PRES0).
  pose proof (SBINVA_of_SERMA RT E D I _ _ _ _ Σc _ m OK CX HSM) as INV0.
  ser_open HSM OK. unbox R3.

  pose proof (stk_of_rw_cells bsegs _ _ _ (rw_cells_of_u8arr bsegs _ _ _ SHF)) as SHS0. rewrite SHL in SHS0. cbn [cells_size csize Nat.add] in SHS0.
  pose proof (stk_merge bsegs _ _ _ _ SHS0 SHT ltac:(clear; lia)) as SHS. clear SHS0.
  replace (SHFA I + 64) with (si_f I / 8 + 2147450944) in SHS by (clear; lia).
  change (rw_cells bsegs m (si_b I) (ser_frameA E I (wkC E) (mkXJ xj0 xj8 xj16 xj24 xj80 xj208 xj216 xj288 xj296))) in FR.
  rewrite ser_frame_raw_eq in FR. cbn [si_f] in FR.
  assert (EU : bv_unsigned (wz (si_b I)) = si_b I) by (apply unsigned_lit; unfold si_b; clear - LQ DD QT LO; lia).

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (ser_epi1 (si_q I) (si_b I) (si_f I) (pa_SB E) (pa_DOC E)); [exact F0| clear - FLO LB; lia| clear - SFL LB; lia| exact Ef| exact SHf
                   | clear - BQ; lia| exact QT| exact FR| exact FH| exact SHS| exact MI]|].
  cbv beta. intros ms1 (m1 & -> & MU1 & WM1 & MI1 & FR1 & FH1 & SHS1). apply evt_done.
  assert (MU1' : munch (serWA E I (mkSbA buf size cap hp kk)) m m1).
  { eapply munch_weaken; [| exact MU1]. intros y Hy. unfold serWA in Hy. cbn [outside sa_buf sa_cap] in Hy |- *. clear - Hy. lia. }
  pose proof (ART_mu RT AF E D I Σc _ m m1 OK CX HR MU1' WM1) as ART1.

  eapply (aevt_setshadow RT RC PMc FDO MST Σc K 245 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 (SHFA I) 64 (pa_lo E));
    [cbn; repeat (first [left; reflexivity| right])| reflexivity| reflexivity| clear; lia| | apply (stk_wr_at m1 _ _ _ _ SHS1); clear; lia| exact ART1| exact MI1| |].
  { intros k Hk. exists (si_f I), 3%nat. split; [rewrite FRS; left; reflexivity|]. unfold shad, SHB. rewrite fs3. clear - Hk Ef. Z.div_mod_to_equations. lia. }
  { unfold call_ok. rewrite EU, SP. split; [| split; [exact W1| split; [clear - LB; unfold RT_STACK; lia| split; [clear - BQ QT; unfold USTACK_TOP; lia| clear - B32; Z.div_mod_to_equations; lia]]]].
    eapply stk_agree_nw; [exact ST|]. eapply agree_of_munch; [exact MU1|]. intros y Hy. cbn [outside] in Hy |- *. clear - Hy FLO LB SFL. lia. }
  intros v0 w0 w1 w2 e1 e2 e3 e4 e5 e6 e7 w3 w4 w5 w6 F2 m2 (ART2 & MI2 & WM2 & ST2) PR2 BY2. rewrite EU in ST2, PR2.
  rewrite (ret_pc_even 0xbaa48) by (clear; lia).

  destruct (af_frame_release RT AF Σc m2 (si_f I) 3%nat (si_fr I) ART2 FRS) as (Σ5 & fl & FLC & NAC & FL0 & FLW & FW & REL).
  rewrite fs3 in FW. replace (si_f I + 512 - 8) with (si_f I + 504) in FW by (clear; lia). rewrite SP in FLW.
  assert (AG2 : forall (P : Z -> Prop), (forall y, P y -> si_b I <= y < si_q I) -> agree_on P m1 m2).
  { intros P HP a Ha. pose proof (HP _ Ha) as H1. apply PR2; [left; clear - H1 QT; unfold USTACK_TOP; lia| clear - H1 SFL LB; lia]. }
  assert (FR2 : rw_cells bsegs m2 (si_b I) (ser_frame_raw (si_f I) (pa_SB E) (pa_DOC E) (wkC E) (mkXJ xj0 xj8 xj16 xj24 xj80 xj208 xj216 xj288 xj296)))
    by (eapply rw_cells_agree_nw; [exact FR1|]; apply AG2; intros y Hy; rewrite ser_frame_raw_size in Hy; unfold si_b in Hy |- *; clear - Hy DD; lia).
  assert (GAP2 : stk bsegs m2 (si_b I + 312) (si_q I - 104)).
  { eapply stk_agree_nw; [eapply stk_agree_nw; [exact GAP| eapply agree_of_munch; [exact MU1|]]| apply AG2]; intros y Hy; cbv beta in Hy.
    - cbn [outside]. unfold si_b in Hy. clear - Hy FLO LQ SFL DD. lia.
    - unfold si_b in Hy |- *. clear - Hy DD. lia. }
  assert (FS2 : rw_cells bsegs m2 (si_q I - 104) (ser_savedA I)).
  { eapply rw_cells_agree_nw; [eapply rw_cells_agree_nw; [exact FS| eapply agree_of_munch; [exact MU1|]]| apply AG2]; intros y Hy; rewrite ser_savedA_size in Hy.
    - cbn [outside]. clear - Hy FLO LQ SFL. lia.
    - unfold si_b. clear - Hy DD. lia. }
  unfold ser_savedA in FS2.

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (ser_epi2 (si_q I) (si_b I) (si_f I) fl (pa_lo E) _ w0 w1 w2 v0 e1 e2 e3 e4 e5 e6 e7 xs3 xs4 _ xs6 xs7 xs8 xs9 xs10 xs11 w3 w4 w5 w6 _
                             (si_ra I) (si_s0 I) (si_s1 I) (si_s2 I) (si_s3 I) (si_s4 I) (si_s5 I) (si_s6 I) (si_s7 I) (si_s8 I) (si_s9 I) (si_s10 I) (si_s11 I) _ F2 fc m2);
                   [exact F0| exact FLO| exact FL0| clear - FLW W1; lia| clear - LO; lia| clear - LB; lia| apply ser_frame_raw_size| clear - BQ; lia| exact QT
                   | unfold si_b; clear - DD; lia| exact ST2| exact FR2| exact GAP2| exact FS2| exact FW| exact FLC| exact MI2]|].
  cbv beta. intros ms3 (m3 & RS3 & FC3 & MU3 & WM3 & MI3 & ST3 & FLC3).
  destruct (REL m3 MU3 WM3 FLC3) as (ART3 & FRS3 & LV3 & SP3 & CR3 & AL3 & AM3).
  apply evt_done. apply (aevt_switch RT PMc Σc Σ5 K ms3 AL3 AM3).
  revert FC3. apply (ret_st_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 ms3 (fun ms => ms_fcsr ms = fc -> aevt Σ5 K ms) RS3).
  intros q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F5 fc5 FC5. change (fc5 = fc) in FC5. subst fc5.

  assert (NFL : forall a, aclient (rt_live RT Σc) (rt_frames RT Σc) (si_b I) a -> ~ (fl <= a < fl + 1)).
  { intros a Ha Hin. replace a with fl in Ha by (clear - Hin; lia).
    destruct Ha as [H|[H|[H|[H|H]]]]; [clear - H FLW W1 LB; lia| apply NAC..]; [right; left| right; right; left| right; right; right; left| right; right; right; right]; exact H. }
  assert (AGW : forall P : Z -> Prop,
    (forall y, P y -> aclient (rt_live RT Σc) (rt_frames RT Σc) (si_b I) y /\ outside (serWA E I (mkSbA buf size cap hp kk)) y) -> agree_on P m m3).
  { intros P HP a Ha. destruct (HP _ Ha) as [CA OW]. unfold serWA in OW. cbn [outside sa_buf sa_cap] in OW.
    rewrite (MU3 a), (PR2 a), (MU1 a); [reflexivity| | exact CA| |].
    - cbn [outside]. clear - OW. lia.
    - clear - OW. lia.
    - cbn [outside]. split; [exact (NFL _ CA)| exact Logic.I]. }
  pose proof (buf_factsA RT AF E D I Σc _ m (si_b I) OK CX HR) as (BLb & _ & _ & CLB & APB). cbn [sa_buf sa_cap] in BLb, CLB, APB.
  assert (AGS : agree_on (sbinv_rng E (mkSbA buf size cap hp kk)) m m3).
  { intros a Ha. unfold sbinv_rng in Ha. cbn [sa_buf sa_cap] in Ha.
    assert (CA : aclient (rt_live RT Σc) (rt_frames RT Σc) (si_b I) (bv_unsigned a)).
    { destruct Ha as [Ha|[Ha|Ha]].
      - right; right; right; left. exists (pa_F E), (pa_kF E). split; [rewrite FRS; right; exact IN4| clear - Ha B1 B2; lia].
      - right; right; right; right. exists (pa_F E), (pa_kF E). split; [rewrite FRS; right; exact IN4|]. unfold shad, SHB in Ha |- *. rewrite EFS. clear - Ha ESB EF Efs B1 B2. lia.
      - apply CLB. exact Ha. }
    assert (OW : ~ (si_f I <= bv_unsigned a < si_f I + 8) /\ ~ (SHFA I + 38 <= bv_unsigned a < SHFA I + 40) /\ ~ (SHFA I <= bv_unsigned a < SHFA I + 64)).
    { pose proof (c_f_shF E D I CX) as FSH2. destruct Ha as [Ha|[Ha|Ha]].
      - clear - Ha FF SHSB B1 B2. lia.
      - unfold shad, SHB in Ha. clear - Ha FF FSH2 EF Ef EFS Efs ESB B1 B2. lia.
      - destruct (APB _ Ha) as (A1 & A2 & _). clear - A1 A2. lia. }
    destruct OW as (O1 & O2 & O3).
    rewrite (MU3 a), (PR2 a), (MU1 a); [reflexivity| | exact CA| exact O3|].
    - cbn [outside]. clear - O1 O2. lia.
    - cbn [outside]. split; [exact (NFL _ CA)| exact Logic.I]. }
  apply (KFIN Σ5 (mkSbA buf size cap hp kk) q0 q1 q2 (wz fl) q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F5 fc m3 FRM ART3 MI3 ST3).
  - eapply SBINVA_agree; [exact INV0| exact AGS].
  - eapply DOCREPA_agree; [exact DR|]. apply AGW. intros y Hy. split; [| eapply docrep_outside; eassumption].
    unfold docrep_rng in Hy. pose proof (ok_tape E OK) as (_ & TN & _ & _ & INT). pose proof (ok_sbuf E OK) as (_ & SN & _ & _ & INS).
    destruct Hy as [Hy|[Hy|[Hy|Hy]]].
    + right; right; right; left. exists (pa_F E), (pa_kF E). split; [rewrite FRS; right; exact IN4| clear - Hy D1 D2; lia].
    + right; right; right; right. exists (pa_F E), (pa_kF E). split; [rewrite FRS; right; exact IN4|]. unfold shad, SHB in Hy |- *. rewrite EFS. clear - Hy ED EF Efs D1 D2. lia.
    + right; right; left. exists (pa_TAPE E), (pa_NT E). split; [rewrite LV; apply in_or_app; right; exact INT| clear - Hy TN; lia].
    + right; right; left. exists (pa_SBUF E), (pa_NS E). split; [rewrite LV; apply in_or_app; right; exact INS| clear - Hy SN; lia].
  - unfold sb_accA. cbn [sa_size]. exact ACC.
  - split; [rewrite LV3; exact LV|]. split; [rewrite FRS3; exact IN4| rewrite SP3, SP; exact W1].
  - exact FRS3.
  - rewrite SP3. exact SP.
  - rewrite CR3. unfold CREDA in CR. clear - CR. lia.
  - intros a Ha Ho. rewrite <- (PRES0 a Ha Ho). apply (AGW (fun y => y = bv_unsigned a)); [| reflexivity]. intros y ->. split.
    + eapply aclient_mono; [exact Ha| rewrite LV; intros e He; apply in_or_app; right; exact He| rewrite FRS; intros e He; right; exact He| unfold si_b; clear - DD; lia].
    + eapply serWA_below; eassumption.
  Unshelve. all: try exact (wz 0).
Qed.

Theorem ser_of_recA : forall D, rec_okA RT PMc D -> ser_cpsA RT PMc D.
Proof using AF RC SM3W GROW PSTR PI64 PU64 PDBL PTRUE PFALSE PNULL PKEY.
  intros D REC. unfold ser_cpsA.
  intros Σ K E st i j c c' q ra gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
         FDO MST OK PL INV DR HEL HI HJ HC HC' ACC ART0 MI0 ST0 LOQ QT Q16 FRM FR3 FRL LL CR HK.
  pose proof (ok_len E OK) as LEN. pose proof (ok_lo E OK) as LOW. pose proof (ok_wfS E OK) as WF. pose proof WF as (_ & SN & _).
  pose proof (ok_sb E OK) as (SB32 & B1 & B2). pose proof (ok_doc E OK) as (D8 & D1 & D2). pose proof (ok_frame E OK) as (F64' & FSEG & FL). pose proof (ok_apart E OK) as AP.
  pose proof (ok_tape E OK) as (_ & TN & _ & _ & INT). pose proof (ok_sbuf E OK) as (_ & SN' & _ & _ & INS).
  pose proof PL as (LVE & INF4 & SPLO).
  pose proof (elemS_lt _ _ _ _ _ _ _ _ _ HEL) as LT. pose proof (elemS_cur _ _ _ _ _ _ _ _ _ HEL) as (CUR & CUR2).
  pose proof (pj_psi_nonneg E m st OK INV) as PSI0.
  pose proof (af_client_consts RT AF Σ m ART0) as CC0. pose proof (af_sp0_win RT AF Σ m ART0) as SPW.
  pose proof (pa_n_32 E OK) as N32.
  unfold ser_needA, PJ_TC_STACK_A, RT_STACK in LOQ. unfold USTACK_TOP in QT.
  destruct (fs_size_64 (pa_kF E)) as (qF & EFS64 & QF1).

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (ser_pro1 q (pa_lo E) (pa_SB E) (pa_DOC E) i ra gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m ST0);
                   [clear - LOQ; lia| clear - LOW; lia| unfold USTACK_TOP; exact QT| exact Q16| exact CC0| exact MI0]|].
  cbv beta. intros ms1 (m1 & dd & a1' & a2' & DD & B32 & -> & MU1 & WM1 & MI1 & ST1 & FS1). apply evt_done.
  set (b := q - 416 - dd) in *.
  assert (LB : pa_lo E + 65696 <= b) by (unfold b; clear - LOQ DD; lia).
  assert (EU : bv_unsigned (wz b) = b) by (apply unsigned_lit; clear - LB LOW QT DD; unfold b; lia).

  assert (CSEP : forall sp a, aclient (rt_live RT Σ) (rt_frames RT Σ) sp a -> sp <= a \/ a < pa_lo E).
  { intros sp a Ha. destruct (aclient_split_c RT AF Σ m sp a ART0 Ha) as [H|H]; [left; exact H| right; clear - H SPLO; lia]. }
  assert (ART1 : ART RT Σ m1).
  { apply (art_client_write RT AF Σ m m1 (q - 416) ART0); [clear - SPLO LOQ; lia| | exact WM1].
    intros a Ha. apply MU1. cbn [outside]. split; [| exact Logic.I]. intros Hin. apply Ha. left. clear - Hin QT. unfold USTACK_TOP. lia. }
  assert (PRES1 : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) q (bv_unsigned a) -> m1 a = m a).
  { intros a Ha. apply MU1. cbn [outside]. split; [| exact Logic.I]. destruct (CSEP _ _ Ha); clear - H LOQ; lia. }
  destruct (stk_split bsegs m1 _ b _ ST1 ltac:(unfold b; clear - LOQ DD; lia)) as [ST1l ST1h].

  eapply (aevt_smalloc3w RT SM3W PMc FDO MST Σ K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 (pa_lo E));
    [reflexivity| clear - FR3; lia| clear - FRL; lia| clear - CR PSI0 LT; lia| exact ART1| exact MI1| | intros HN; exfalso; rewrite HN in INF4; exact INF4|].
  { unfold call_ok. rewrite EU. split; [exact ST1l|]. split; [exact SPLO|]. split; [clear - LB; unfold RT_STACK; lia|].
    split; [unfold b, USTACK_TOP; clear - QT DD; lia| clear - B32; unfold b; Z.div_mod_to_equations; lia]. }
  intros Σ1 f v0 v1 v2 e1 e2 e3 e4 e5 e6 e7 v3 v4 v5 v6 F1 m2 (ART2 & MI2 & WM2 & ST2) PRES2 WRF WRS FRS1 LV1 SP1 CR1 F0 F64 FTOP.
  rewrite EU in ST2, PRES2. rewrite (ret_pc_even 0xb7f28) by (clear; lia).
  change (fs_size 3 - 8) with 504 in WRF. change (fs_size 3 / 8) with 64 in WRS.

  assert (INf : In (f, 3%nat) (rt_frames RT Σ1)) by (rewrite FRS1; left; reflexivity).
  assert (INF1 : In (pa_F E, pa_kF E) (rt_frames RT Σ1)) by (rewrite FRS1; right; exact INF4).
  pose proof (af_frames_range RT AF Σ1 m2 f 3%nat ART2 INf) as (_ & FWIN & _ & F3CH). rewrite fs3, SP1 in FWIN. rewrite fs3 in F3CH.
  assert (FLO : f + 512 <= pa_lo E) by (clear - FWIN SPLO; lia).
  pose proof (af_frames_align RT AF Σ1 m2 f 3%nat ART2 INf) as [_ FSEGf].
  pose proof (af_fshadow_apart RT AF Σ1 m2 f 3%nat ART2 INf) as [F3SL F3SF]. rewrite fs3 in F3SL, F3SF.
  pose proof (af_fshadow_apart RT AF Σ1 m2 (pa_F E) (pa_kF E) ART2 INF1) as [F4SL F4SF].
  pose proof (af_frames_disj RT AF Σ1 m2 f 3%nat (pa_F E) (pa_kF E) [] (rt_frames RT Σ) ART2 FRS1 INF4) as FF. rewrite fs3 in FF.
  assert (Ef : 8 * (f / 8) = f) by (clear - F64; Z.div_mod_to_equations; lia).
  assert (EF : 8 * (pa_F E / 8) = pa_F E) by (clear - F64'; Z.div_mod_to_equations; lia).
  assert (E512 : (f + 512) / 8 = f / 8 + 64) by (clear - Ef; Z.div_mod_to_equations; lia).
  assert (EFS : (pa_F E + fs_size (pa_kF E)) / 8 = pa_F E / 8 + fs_size (pa_kF E) / 8) by (rewrite EFS64; clear - EF; Z.div_mod_to_equations; lia).
  assert (SFL : f / 8 + 2147450880 + 64 <= pa_lo E) by (clear - FLO LOW Ef; lia).

  assert (FRESH : forall sp a, pa_lo E <= sp -> aclient (rt_live RT Σ) (rt_frames RT Σ) sp a -> ~ (f <= a < f + 512) /\ ~ (f / 8 + 2147450880 <= a < f / 8 + 2147450880 + 64)).
  { intros sp a Hsp Ha. pose proof (newframe_apartI RT AF Σ Σ1 m2 f 3%nat sp a ART2 FRS1 ltac:(rewrite LV1; intros e He; exact He) SP1 ltac:(clear - Hsp SPLO; lia) Ha) as [N1 N2].
    rewrite fs3 in N1, N2. unfold shad, SHB in N2. rewrite E512 in N2. split; [exact N1| clear - N2; lia]. }

  destruct (wr_at_rw_CB m2 f 24 (wr_at_sub m2 f 504 f 24 WRF ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia)) as (jh & FH2). change (Z.to_nat 24) with 24%nat in FH2.
  pose proof (wr_at_stk m2 (f + 24) 280 (wr_at_sub m2 f 504 (f + 24) 280 WRF ltac:(lia) ltac:(lia) ltac:(lia))) as F3S2.
  replace (f + 24 + 280) with (f + 304) in F3S2 by lia.
  destruct (wr_at_rw_CB m2 (f + 304) 16 (wr_at_sub m2 f 504 (f + 304) 16 WRF ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia)) as (iso & IS2). change (Z.to_nat 16) with 16%nat in IS2.
  assert (ISL : length iso = 16%nat) by (destruct IS2 as [[WF' _] _]; cbn in WF'; clear - WF'; lia).
  apply u8arr_of_rw_cells in IS2.
  destruct (wr_at_rw_CB m2 (f / 8 + 2147450880) 64 WRS ltac:(lia)) as (sh & SHC2). change (Z.to_nat 64) with 64%nat in SHC2.

  assert (AG12 : forall (P : Z -> Prop), (forall y, P y -> b <= y < q) -> agree_on P m1 m2).
  { intros P HP a Ha. apply PRES2. left. pose proof (HP _ Ha). clear - H QT. unfold USTACK_TOP. lia. }
  assert (STb2 : stk bsegs m2 b (q - 104)) by (eapply stk_agree_nw; [exact ST1h|]; apply AG12; intros y Hy; clear - Hy; lia).
  assert (FS2 : rw_cells bsegs m2 (q - 104) (sa_savedA ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11))
    by (eapply rw_cells_agree_nw; [exact FS1|]; apply AG12; intros y Hy; unfold sa_savedA in Hy; cbn [cells_size csize Nat.add] in Hy; unfold b; clear - Hy DD; lia).
  assert (PRES2' : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) q (bv_unsigned a) -> m2 a = m a).
  { intros a Ha. rewrite <- (PRES1 a Ha). apply PRES2. eapply aclient_mono; [exact Ha| intros e He; exact He| intros e He; exact He| unfold b; clear - DD; lia]. }
  clear PRES1 PRES2 ST1 ST1l ST1h FS1 MU1 WM1 MI1 ART1 WRF WRS.

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (ser_pro2 q b f (pa_lo E) (pa_SB E) (pa_DOC E) i gp v0 v1 v2 e1 e2 e3 e4 e5 e6 e7 s2 s3 s4 s5 s7 s10 v3 v4 v5 v6 jh sh [] iso F1 fc m2 F0 FLO SFL Ef);
                   [| clear - LOW; lia| clear - LB; lia| unfold b; clear - DD; lia| unfold USTACK_TOP; exact QT| clear - FSEG B1; ul| clear - B2 FL; lia
                   | clear - FSEG D1; ul| clear - D2 FL; lia| exact D8| clear - HI LT HJ N32; lia| exact STb2| exact FH2| exact F3S2| exact IS2| exact ISL| exact SHC2| exact MI2]|].
  { destruct (F3SF f 3%nat INf) as [H|H]; unfold shad, SHB in H; rewrite ?fs3, ?E512 in H; [left| right]; clear - H; lia. }
  cbv beta. intros ms3 (m3 & x & w & ra' & t0' & t1' & t2' & a0' & a2'' & a3' & a4' & a5' & a6' & a7' & s3' & t3' & t4' & t5' & t6' & -> & MU3 & WM3 & MI3 & FRw & GAPw & FHw & F3Sw & ISw & (tsh & SHCw)).
  apply evt_done.

  set (I := mkSI q dd f j c' (rt_credit RT Σ - 2 * (j - i) - pj_psi (pa_len E) st) ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (rt_frames RT Σ) (rt_sp0 RT Σ) m).
  assert (CX : sctxA E D I).
  { subst I. split; cbn [si_q si_dd si_f si_j si_c' si_R si_fr si_sp0 si_b].
    - exact DD.
    - exact B32.
    - exact Q16.
    - unfold ser_needA, PJ_TC_STACK_A, RT_STACK. clear - LOQ. lia.
    - unfold USTACK_TOP. exact QT.
    - split; [exact SPLO| exact SPW].
    - split; [exact F0|]. split; [exact F64|]. split; [exact FSEGf| exact FLO].
    - clear - FF. lia.
    - pose proof (F3SF f 3%nat INf) as H. unfold shad, SHB in H. rewrite fs3, E512 in H. clear - H. lia.
    - pose proof (F3SF (pa_F E) (pa_kF E) INF1) as H. unfold shad, SHB in H. rewrite E512 in H. clear - H. lia.
    - pose proof (F4SF f 3%nat INf) as H. unfold shad, SHB in H. rewrite fs3 in H. clear - H. lia.
    - pose proof (F4SF (pa_F E) (pa_kF E) INF1) as H. unfold shad, SHB in H. clear - H. lia.
    - clear - HI LT HJ. lia.
    - clear - HC CUR CUR2 HC'. lia.
    - clear - CR PSI0. lia.
    - exact INF4.
    - exact FR3.
    - exact FRL.
    - exact LL. }

  assert (CL3 : forall y, (b <= y < b + 312) \/ (f <= y < f + 24) \/ (f + 304 <= y < f + 305) \/ (f / 8 + 2147450880 <= y < f / 8 + 2147450924) ->
                aclient (rt_live RT Σ1) (rt_frames RT Σ1) b y).
  { intros y [Hy|[Hy|[Hy|Hy]]].
    - left. clear - Hy QT LB DD. unfold b, USTACK_TOP in *. lia.
    - right; right; right; left. exists f, 3%nat. split; [exact INf| rewrite fs3; clear - Hy; lia].
    - right; right; right; left. exists f, 3%nat. split; [exact INf| rewrite fs3; clear - Hy; lia].
    - right; right; right; right. exists f, 3%nat. split; [exact INf| unfold shad, SHB; rewrite fs3, E512; clear - Hy; lia]. }
  assert (ART3 : ART RT Σ1 m3).
  { apply (art_client_write RT AF Σ1 m2 m3 b ART2); [rewrite SP1; clear - SPLO LB; lia| | exact WM3].
    intros a Ha. apply MU3. cbn [outside]. repeat split; try exact Logic.I; intros Hin; apply Ha; apply CL3; clear - Hin; lia. }

  assert (AG03 : forall (P : Z -> Prop), (forall y, P y -> aclient (rt_live RT Σ) (rt_frames RT Σ) q y) -> agree_on P m m3).
  { intros P HP a Ha. pose proof (HP _ Ha) as CA. rewrite <- (PRES2' a CA). apply MU3.
    destruct (FRESH q _ ltac:(clear - LOQ; lia) CA) as [N1 N2]. destruct (CSEP _ _ CA) as [H|H]; cbn [outside]; unfold b; clear - H N1 N2 LOQ DD; lia. }
  assert (INV3 : SBINVA E m3 st).
  { eapply SBINVA_agree; [exact INV|]. apply AG03. intros y Hy. unfold sbinv_rng in Hy. destruct Hy as [Hy|[Hy|Hy]].
    - right; right; right; left. exists (pa_F E), (pa_kF E). split; [exact INF4| clear - Hy B1 B2; lia].
    - right; right; right; right. exists (pa_F E), (pa_kF E). split; [exact INF4|]. unfold shad, SHB in Hy |- *. rewrite EFS.
      pose proof INV as (_ & _ & _ & _ & _ & _ & HB). clear - Hy EF EFS64 QF1 B1 B2 SB32. Z.div_mod_to_equations. lia.
    - pose proof INV as (_ & SZ & _ & _ & _ & _ & HB). destruct (sa_heap st) eqn:HP.
      + right; right; left. exists (sa_buf st), (sa_cap st). split; [rewrite LVE; unfold sbchunkA; rewrite HP; left; reflexivity| clear - Hy; lia].
      + destruct HB as (EB & EC & _). right; right; right; left. exists (pa_F E), (pa_kF E). split; [exact INF4| clear - Hy EB EC B1 B2; lia]. }
  assert (DR3 : DOCREPA E m3).
  { eapply DOCREPA_agree; [exact DR|]. apply AG03. intros y Hy. unfold docrep_rng in Hy. destruct Hy as [Hy|[Hy|[Hy|Hy]]].
    - right; right; right; left. exists (pa_F E), (pa_kF E). split; [exact INF4| clear - Hy D1 D2; lia].
    - right; right; right; right. exists (pa_F E), (pa_kF E). split; [exact INF4|]. unfold shad, SHB in Hy |- *. rewrite EFS.
      clear - Hy EF EFS64 QF1 D1 D2 D8. Z.div_mod_to_equations. lia.
    - right; right; left. exists (pa_TAPE E), (pa_NT E). split; [rewrite LVE; apply in_or_app; right; exact INT| clear - Hy TN; lia].
    - right; right; left. exists (pa_SBUF E), (pa_NS E). split; [rewrite LVE; apply in_or_app; right; exact INS| clear - Hy SN'; lia]. }
  pose proof INV3 as (SV3 & SZ3 & (bs3 & BUF3) & (ji3 & INL3) & SBSH3 & PK3 & PH3).
  apply rw_cells_app in SHCw. destruct SHCw as [SHF3 SHT3]. rewrite cells_size_map_C1, ser_shpatA_length in SHT3.
  apply u8arr_of_C1s in SHF3. pose proof (stk_of_rw_cells bsegs _ _ _ SHT3) as SHT3'. cbn [cells_size csize Nat.add] in SHT3'.
  assert (HSM : SERMA RT E I w x ser_shpatA (upd iso 0 (Z_to_bv 8 0)) Σ1 st m3).
  { unfold I. split.
    - unfold SREFA. cbn [si_f si_fr si_sp0 si_q si_m0]. split; [exact ART3|]. split; [rewrite LV1; exact LVE|]. split; [exact FRS1|]. split; [exact SP1|].
      split; [exact DR3|]. split; [exact SBSH3|]. split; [exact (conj PK3 PH3)|].
      intros a Ha Ho. apply (AG03 (fun y => aclient (pa_L E) (rt_frames RT Σ) q y)); [| exact Ha].
      intros y Hy. eapply aclient_mono; [exact Hy| rewrite LVE; intros e He; apply in_or_app; right; exact He| intros e He; exact He| clear; lia].
    - unfold SCURA, si_b. cbn [si_f si_fr si_sp0 si_q si_m0 si_dd]. fold b.
      split; [rewrite ser_frame_raw_eq; cbn [si_f]; exact FRw|]. split; [exact GAPw|].
      split. { unfold ser_savedA. cbn [si_ra si_s0 si_s1 si_s2 si_s3 si_s4 si_s5 si_s6 si_s7 si_s8 si_s9 si_s10 si_s11].
               eapply rw_cells_agree_nw; [exact FS2|]. eapply agree_of_munch; [exact MU3|]. intros y Hy. unfold sa_savedA in Hy. cbn [cells_size csize Nat.add] in Hy.
               cbn [outside]. unfold b. clear - Hy DD FLO SFL LOQ. repeat split; try exact Logic.I; lia. }
      split; [exists (wz 1102416563), (wz 0x22f0b), (wz 0xb7eb0); exact FHw|]. split; [exact F3Sw|].
      split; [exact ISw|]. split; [rewrite upd_length; exact ISL|]. split; [exact SHF3|]. split; [reflexivity|].
      split; [replace (f / 8 + 2147450880 + Z.of_nat 44 + Z.of_nat 20) with (f / 8 + 2147450880 + 64) in SHT3' by (clear; lia);
              replace (f / 8 + 2147450880 + Z.of_nat 44) with (f / 8 + 2147450880 + 44) in SHT3' by (clear; lia); exact SHT3'|].
      split; [exact SV3|]. split; [exact SZ3|].
      split. { pose proof (stk_of_rw_cells bsegs _ _ _ BUF3) as S. cbn [cells_size csize Nat.add] in S. rewrite Nat.add_0_r, Z2Nat.id in S by (clear - SZ3; lia). exact S. }
      split. { pose proof (stk_of_rw_cells bsegs _ _ _ INL3) as S. cbn [cells_size csize Nat.add] in S. exact S. }
      split; [exact MI3|].
      eapply stk_agree_nw; [exact ST2|]. eapply agree_of_munch; [exact MU3|]. intros y Hy. cbv beta in Hy. cbn [outside]. clear - Hy FLO SFL.
      repeat split; try exact Logic.I; lia. }

  assert (KX : exit_KA RT PMc E I K).
  { apply (ser_exitA E D I K FDO MST OK CX). unfold I. cbn [si_q si_j si_c' si_R si_fr si_sp0 si_m0 si_ra si_gp si_s0 si_s1 si_s2 si_s3 si_s4 si_s5 si_s6 si_s7 si_s8 si_s9 si_s10 si_s11].
    intros Σ' st' y0 y1 y2 z0 z1 z2 z3 z4 z5 z6 z7 y3 y4 y5 y6 F' fc' m' FRM' ART' MI' ST' INV' DR' ACC' PL' FRS' SP' CR' PRES'.
    apply (HK Σ' st' y0 y1 y2 z0 z1 z2 z3 z4 z5 z6 z7 y3 y4 y5 y6 F' fc' m' FRM' ART' MI' ST' INV' DR' ACC' PL' FRS' SP'); [clear - CR'; lia| exact PRES']. }
  pose proof (loop_closedA RT AF RC PMc FDO MST GROW PSTR PI64 PU64 PDBL PTRUE PFALSE PNULL PKEY E D I K OK CX KX REC (S (Z.to_nat (j - i)))) as HEAD.
  unfold head_stmtA in HEAD. unfold I in HEAD |- *.
  eapply aevt_eq; [| eapply (HEAD D [] i j c c' false (upd iso 0 (Z_to_bv 8 0)) Σ1 st m3 F1 fc w x)];
    [unfold si_b; cbn [si_q si_dd si_gp length Z.of_nat Z.b2z]; fold b; pj_st_eq| clear - LT; cbn [si_j]; lia| cbn [length]; clear; lia| cbn; clear; lia| | exact HEL| cbn [si_j si_c']; apply rest_nil| reflexivity
    | exact HI| exact HC| exact HSM| exact FRM| exact ACC| unfold CREDA; cbn [si_R si_j]; rewrite CR1; clear; lia].
  split; [apply nth_error_upd_same; rewrite ISL; clear; lia| intros jj k Hk; cbn in Hk; destruct jj; discriminate Hk].
Qed.

End Top.
