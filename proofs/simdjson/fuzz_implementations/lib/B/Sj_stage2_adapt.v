(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.P Require Import Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface D_kit Sj_akit Sj_acps Sj_hkit Sj_rtf Sj_num_iface Sj_num_akit Sj_num_amem
 I_lkit
  Sj_stage2_iface Sj_stage2_defs Sj_stage2_exitw Sj_stage2_exit Sj_stage2_pro Sj_stage2_entry Sj_stage2_objf Sj_stage2_hex4 Sj_stage2_main Sj_stage2_main2 Sj_stage2_world.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, SHB in *; lia.

Lemma cps_f_of_aevt : forall RT Σ PMc ms (Kp : config -> Prop),
  (frm0 (ms_fcsr ms) -> cps bsegs (ASTA RT Σ PMc (eq ms)) Kp) -> (forall c, Kp c -> cfrm0 c) -> cps_f (ASTA RT Σ PMc (eq ms)) Kp.
Proof.
  intros RT Σ PMc ms Kp H HF. unfold cps_f. intros T c [Hc Fc] Hk.
  assert (F0 : frm0 (ms_fcsr ms)).
  { destruct c as [ms0 mo]. destruct Hc as (_ & E & _). rewrite E. exact Fc. }
  apply (H F0 T c Hc). intros c' Hc'. apply Hk. split; [exact Hc'| exact (HF c' Hc')].
Qed.

Lemma pd7 : forall x1 x2 x3 x4 x5 x6 x7, pairwise_disj [x1; x2; x3; x4; x5; x6; x7] ->
  (ivl_disj x1 x2 /\ ivl_disj x1 x3 /\ ivl_disj x1 x4 /\ ivl_disj x1 x5 /\ ivl_disj x1 x6 /\ ivl_disj x1 x7) /\
  (ivl_disj x2 x3 /\ ivl_disj x2 x4 /\ ivl_disj x2 x5 /\ ivl_disj x2 x6 /\ ivl_disj x2 x7) /\
  (ivl_disj x3 x4 /\ ivl_disj x3 x5 /\ ivl_disj x3 x6 /\ ivl_disj x3 x7) /\
  (ivl_disj x4 x5 /\ ivl_disj x4 x6 /\ ivl_disj x4 x7) /\ (ivl_disj x5 x6 /\ ivl_disj x5 x7) /\ ivl_disj x6 x7.
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 H. cbn [pairwise_disj] in H.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  repeat match goal with H : Forall _ (_ :: _) |- _ => apply Forall_cons_iff in H; destruct H end.
  tauto.
Qed.

Lemma chunk_al : forall p n X size, p mod 8 = 0 -> X mod 8 = 0 -> size mod 8 = 0 -> X + size <= p + n -> X + size <= p + 8 * (n / 8).
Proof.
  intros p n X size P8 X8 S8 H.
  assert (M : (X + size - p) mod 8 = 0).
  { rewrite Zminus_mod, Zplus_mod, X8, S8, P8. reflexivity. }
  pose proof (Z.div_exact (X + size - p) 8 ltac:(lia)) as [_ EX]. specialize (EX M).
  pose proof (Z.div_le_mono (X + size - p) n 8 ltac:(lia) ltac:(lia)) as LE. lia.
Qed.
Lemma chunk_al4 : forall p n X w k, p mod 8 = 0 -> X mod 8 = 0 -> X + 4 * w <= p + n -> k + 1 <= w -> X + 4 * k <= p + 8 * (n / 8).
Proof.
  intros p n X w k P8 X8 H Hk.
  pose proof (chunk_al p n X (8 * ((4 * w) / 8)) P8 X8 ltac:(rewrite Z.mul_comm; apply Z.mod_mul; lia)) as C.
  pose proof (Z.div_mod (4 * w) 8 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (4 * w) 8 ltac:(lia)) as MB.
  specialize (C ltac:(lia)).
  assert (4 * k <= 8 * (4 * w / 8)); [| lia].
  assert (R : (4 * w) mod 8 = 0 \/ (4 * w) mod 8 = 4).
  { replace (4 * w) with (w * 4) by lia. change 8 with (2 * 4). rewrite Zmult_mod_distr_r.
    pose proof (Z.mod_pos_bound w 2 ltac:(lia)). assert (w mod 2 = 0 \/ w mod 2 = 1) as [->| ->] by lia; [left|right]; reflexivity. }
  lia.
Qed.
Lemma chunk_un : forall p n X size, X + size + 8 <= p + n -> X + size <= p + 8 * (n / 8).
Proof.
  intros p n X size H. pose proof (Z.div_mod n 8 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound n 8 ltac:(lia)) as MB. lia.
Qed.

Lemma wr_at_sub : forall (mx : mem) a n a' n', wr_at bsegs mx a n -> a <= a' -> a' + n' <= a + n -> 0 <= a' -> wr_at bsegs mx a' n'.
Proof.
  intros mx a n a' n' (A0 & A1 & H) H1 H2 H3. split; [exact H3|]. split; [lia|]. intros i Hi.
  replace (a' + i) with (a + (a' - a + i)) by lia. apply H. lia.
Qed.

Section Adapt.
  Variable RT : rt_sig.
  Hypothesis AF : art_facts RT.
  Hypothesis RTF : rt_contracts_f RT.
  Variable PMc : Model -> Prop.
  Hypothesis FDO : fdfs_only PMc.
  Hypothesis MST : mat_stable PMc.

  Lemma live_reg_rng : forall Σx (mx : mem) X size, ART RT Σx mx -> live_reg RT Σx X size ->
    exists p n, In (p, n) (rt_live RT Σx) /\ p mod 8 = 0 /\ p <= X /\ X + size <= p + n /\ 0 < p /\ p + n <= rt_sp0 RT Σx - STACK_WIN.
  Proof using AF.
    intros Σx mx X size HA (p & n & Hin & P8 & H1 & H2). exists p, n.
    pose proof (af_live_range RT AF Σx mx p n HA Hin) as (P0 & P1 & _). repeat (split; [assumption|]). assumption.
  Qed.

  Variable Σ : rts RT.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word.
  Variable m : mem.
  Variable lo : Z.
  Variables THIS DOC IDX BUF TAPE SBUF OC IA : Z.
  Variables bs idxs : list Z.
  Variable iws : list word.
  Variables tcap scap : Z.
  Variables vptr capv nxt dcap : word.
  Variables p12 p28 p50 : list byte.
  Hypothesis ETP : tp = Z_to_bv 64 0x6be3e8.
  Hypothesis HS1 : S1OUT bs idxs.
  Hypothesis HBOK : bytes_ok bs.
  Hypothesis HLEN : blen bs <= 1048512.
  Hypothesis HIWS : firstn (length idxs + 3) iws = map (Z_to_bv 64) (idxs ++ [blen bs; blen bs; 0]).
  Hypothesis HTC1 : blen bs + 3 <= tcap.
  Hypothesis HTC2 : tcap <= 2^40.
  Hypothesis HSC1 : 5 * blen bs + 5 <= 3 * scap.
  Hypothesis HSC2 : scap <= 2^40.
  Hypothesis HSC8 : scap mod 8 = 0.
  Hypothesis HIWL : blen bs + 4 <= Z.of_nat (length iws).
  Hypothesis HIWM : Z.of_nat (length iws) < 2^40.
  Hypothesis ART0 : ART RT Σ m.
  Hypothesis LOR : rt_sp0 RT Σ - STACK_WIN <= lo.
  Hypothesis ROOM : lo + S2A_STACK <= bv_unsigned sp.
  Hypothesis TOP : bv_unsigned sp + 16 <= USTACK_TOP.
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis FRL : (length (rt_frames RT Σ) + S2A_FRAMES <= FRAMES_MAX)%nat.
  Hypothesis CRD : S2A_COST (blen bs) <= rt_credit RT Σ.
  Hypothesis LVL : Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX.
  Hypothesis L_THIS : live_reg RT Σ THIS 96.
  Hypothesis L_IDX : live_reg RT Σ IDX (4 * Z.of_nat (length iws)).
  Hypothesis L_BUF : live_reg RT Σ BUF (blen bs + 64).
  Hypothesis L_TAPE : live_reg RT Σ TAPE (8 * tcap).
  Hypothesis L_SBUF : live_reg RT Σ SBUF scap.
  Hypothesis L_OC : live_reg RT Σ OC 8192.
  Hypothesis L_IA : live_reg RT Σ IA 1024.
  Hypothesis A_THIS : THIS mod 8 = 0.
  Hypothesis A_IDX : IDX mod 8 = 0.
  Hypothesis A_TAPE : TAPE mod 8 = 0.
  Hypothesis A_SBUF : SBUF mod 8 = 0.
  Hypothesis A_OC : OC mod 8 = 0.
  Hypothesis A_IA : IA mod 8 = 0.
  Hypothesis HPD : pairwise_disj [(THIS, 96); (IDX, 4 * Z.of_nat (length iws)); (BUF, blen bs + 64); (TAPE, 8 * tcap); (SBUF, scap); (OC, 8192); (IA, 1024)].
  Hypothesis FOBJ : fobj RT Σ m DOC 24.

  Variable Σ1 : rts RT.
  Variables f spa : Z.
  Variables ej0 ej256 : list byte.
  Variable m3 : mem.
  Hypothesis ART1 : ART RT Σ1 m3.
  Hypothesis FRS : rt_frames RT Σ1 = (f, 5%nat) :: rt_frames RT Σ.
  Hypothesis LVS : rt_live RT Σ1 = rt_live RT Σ.
  Hypothesis SP0S : rt_sp0 RT Σ1 = rt_sp0 RT Σ.
  Hypothesis CRS : rt_credit RT Σ1 = rt_credit RT Σ - 1.
  Hypothesis F64 : f mod 64 = 0.
  Hypothesis SPA1 : bv_unsigned sp - 432 <= spa <= bv_unsigned sp - 416.
  Hypothesis SPA32 : spa mod 32 = 0.

  Definition E0 : s2env :=
    mkS2Env ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo spa f THIS DOC IDX BUF TAPE SBUF OC IA bs idxs iws tcap scap
            vptr p12 nxt p28 capv p50 dcap ej0 ej256 m3 [] [].

  Lemma E0_ok : env_ok E0.
  Proof using All.
    pose proof (blen_nonneg bs) as BL0.
    destruct (live_reg_rng Σ m _ _ ART0 L_THIS) as (pT & nT & IT & _ & T1 & T2 & T3 & T4).
    destruct (live_reg_rng Σ m _ _ ART0 L_IDX) as (pI & nI & II & _ & I1 & I2 & I3 & I4).
    destruct (live_reg_rng Σ m _ _ ART0 L_BUF) as (pB & nB & IB & _ & B1 & B2 & B3 & B4).
    destruct (live_reg_rng Σ m _ _ ART0 L_TAPE) as (pP & nP & IP & _ & P1 & P2 & P3 & P4).
    destruct (live_reg_rng Σ m _ _ ART0 L_SBUF) as (pS & nS & IS & _ & S1 & S2 & S3 & S4).
    destruct (live_reg_rng Σ m _ _ ART0 L_OC) as (pO & nO & IO & _ & O1 & O2 & O3 & O4).
    destruct (live_reg_rng Σ m _ _ ART0 L_IA) as (pA & nA & IA' & _ & A1 & A2 & A3 & A4).
    destruct FOBJ as (D8 & _ & (fd & cd & IFD & FD1 & FD2) & _). change (8 * ((24 + 7) / 8)) with 24 in FD2.
    pose proof (af_frames_range RT AF Σ m fd cd ART0 IFD) as (FD0 & FDH & _ & FDL).
    assert (INF : In (f, 5%nat) (rt_frames RT Σ1)) by (rewrite FRS; left; reflexivity).
    pose proof (af_frames_range RT AF Σ1 m3 f 5%nat ART1 INF) as (FF0 & FFH & _ & FFL). rewrite SP0S in FFH. rewrite LVS in FFL.
    change (fs_size 5) with 2048 in *.
    pose proof (af_frames_disj RT AF Σ1 m3 f 5%nat fd cd [] (rt_frames RT Σ) ART1 FRS IFD) as FFD. change (fs_size 5) with 2048 in FFD.
    assert (FSD : 0 <= fs_size cd) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
    pose proof (af_sp0_win RT AF Σ m ART0) as SPW. unfold STACK_WIN, S2A_STACK, NUMA_STACK, RT_STACK, USTACK_TOP in *.
    destruct (pd7 _ _ _ _ _ _ _ HPD) as ((D12 & D13 & D14 & D15 & D16 & D17) & (D23 & D24 & D25 & D26 & D27) & (D34 & D35 & D36 & D37) & (D45 & D46 & D47) & (D56 & D57) & D67).
    unfold ivl_disj in *. cbn [fst snd] in *.
    pose proof (FDL _ _ IT) as X1. pose proof (FDL _ _ IP) as X2. pose proof (FDL _ _ IS) as X3. pose proof (FDL _ _ IO) as X4. pose proof (FDL _ _ IA') as X5.
    pose proof (FFL _ _ IT) as Y1. pose proof (FFL _ _ II) as Y2. pose proof (FFL _ _ IB) as Y3. pose proof (FFL _ _ IP) as Y4.
    pose proof (FFL _ _ IS) as Y5. pose proof (FFL _ _ IO) as Y6. pose proof (FFL _ _ IA') as Y7.
    clear FDL FFL HPD.

    assert (R_glo : 0x645000 <= lo) by (clear - SPW LOR; lia).
    assert (R_spa : lo <= spa /\ bv_unsigned sp - 432 <= spa /\ spa <= bv_unsigned sp - 416) by (clear - ROOM SPA1; lia).
    assert (R_top : bv_unsigned sp <= 2^47) by (clear - TOP; lia).
    assert (R_ff : 0 < f /\ f + 2048 <= lo) by (clear - FF0 FFH LOR; lia).
    assert (R_this : 0 < THIS /\ THIS + 96 <= lo) by (clear - T1 T2 T3 T4 LOR; lia).
    assert (R_doc : 0 < DOC /\ DOC + 24 <= lo) by (clear - FD0 FD1 FD2 FDH LOR; lia).
    assert (R_idx : 0 < IDX /\ IDX + 4 * Z.of_nat (length iws) <= lo) by (clear - I1 I2 I3 I4 LOR; lia).
    assert (R_buf : 0 < BUF /\ BUF + blen bs + 64 <= lo) by (clear - B1 B2 B3 B4 LOR; lia).
    assert (R_tape : 0 < TAPE /\ TAPE + 8 * tcap <= lo) by (clear - P1 P2 P3 P4 LOR; lia).
    assert (R_sbuf : 0 < SBUF /\ SBUF + scap <= lo) by (clear - S1 S2 S3 S4 LOR; lia).
    assert (R_oc : 0 < OC /\ OC + 8192 <= lo) by (clear - O1 O2 O3 O4 LOR; lia).
    assert (R_ia : 0 < IA /\ IA + 1024 <= lo) by (clear - A1 A2 A3 A4 LOR; lia).

    assert (E13 : THIS + 96 <= BUF \/ BUF + blen bs + 64 <= THIS) by (clear - D13; lia).
    assert (E24 : TAPE + 8 * tcap <= IDX \/ IDX + 4 * Z.of_nat (length iws) <= TAPE) by (clear - D24; lia).
    assert (E34 : TAPE + 8 * tcap <= BUF \/ BUF + blen bs + 64 <= TAPE) by (clear - D34; lia).
    assert (E25 : SBUF + scap <= IDX \/ IDX + 4 * Z.of_nat (length iws) <= SBUF) by (clear - D25; lia).
    assert (E35 : SBUF + scap <= BUF \/ BUF + blen bs + 64 <= SBUF) by (clear - D35; lia).
    assert (E26 : OC + 8192 <= IDX \/ IDX + 4 * Z.of_nat (length iws) <= OC) by (clear - D26; lia).
    assert (E36 : OC + 8192 <= BUF \/ BUF + blen bs + 64 <= OC) by (clear - D36; lia).
    assert (E27 : IA + 1024 <= IDX \/ IDX + 4 * Z.of_nat (length iws) <= IA) by (clear - D27; lia).
    assert (E37 : IA + 1024 <= BUF \/ BUF + blen bs + 64 <= IA) by (clear - D37; lia).
    assert (G1 : DOC + 24 <= THIS \/ THIS + 96 <= DOC) by (clear - X1 T1 T2 FD1 FD2 FSD; lia).
    assert (G2 : DOC + 24 <= TAPE \/ TAPE + 8 * tcap <= DOC) by (clear - X2 P1 P2 FD1 FD2 FSD; lia).
    assert (G3 : DOC + 24 <= SBUF \/ SBUF + scap <= DOC) by (clear - X3 S1 S2 FD1 FD2 FSD; lia).
    assert (G4 : DOC + 24 <= OC \/ OC + 8192 <= DOC) by (clear - X4 O1 O2 FD1 FD2 FSD; lia).
    assert (G5 : DOC + 24 <= IA \/ IA + 1024 <= DOC) by (clear - X5 A1 A2 FD1 FD2 FSD; lia).
    assert (H1 : f + 8 <= THIS \/ THIS + 96 <= f) by (clear - Y1 T1 T2; lia).
    assert (H2 : f + 8 <= DOC \/ DOC + 24 <= f) by (clear - FFD FD1 FD2 FSD; lia).
    assert (H3 : f + 8 <= IDX \/ IDX + 4 * Z.of_nat (length iws) <= f) by (clear - Y2 I1 I2; lia).
    assert (H4 : f + 8 <= BUF \/ BUF + blen bs + 64 <= f) by (clear - Y3 B1 B2; lia).
    assert (H5 : f + 8 <= TAPE \/ TAPE + 8 * tcap <= f) by (clear - Y4 P1 P2; lia).
    assert (H6 : f + 8 <= SBUF \/ SBUF + scap <= f) by (clear - Y5 S1 S2; lia).
    assert (H7 : f + 8 <= OC \/ OC + 8192 <= f) by (clear - Y6 O1 O2; lia).
    assert (H8 : f + 8 <= IA \/ IA + 1024 <= f) by (clear - Y7 A1 A2; lia).
    unfold E0. constructor; cbn [e_bs e_idxs e_iws e_tcap e_scap e_lo e_sp e_spa e_FF e_THIS e_DOC e_IDX e_BUF e_TAPE e_SBUF e_OC e_IA];
      unfold S2_LEN_MAX; first [assumption | split; assumption].
  Qed.

  Definition Kfin : config -> Prop :=
    fun c => exists (Σ' : rts RT),
       ASTA RT Σ' PMc (fun ms => exists m' (v nxt' : word),
           ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
         /\ bv_unsigned v < 64
         /\ s2a_okres TAPE SBUF tcap scap v m'
         /\ frm0 (ms_fcsr ms)
         /\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
         /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (s2a_X THIS TAPE SBUF OC IA tcap scap) m m'
         /\ rw_cells bsegs m' THIS (s2a_impl_cells vptr (Z.of_nat (length idxs)) IDX capv OC IA BUF (blen bs) nxt' (Z_to_bv 64 DOC) p12 p28 p50)) c
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_live RT Σ' = rt_live RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ - S2A_COST (blen bs) <= rt_credit RT Σ'.

  Notation WDt := (WD RT).
  Notation wE := (Sj_stage2_main.wE E0 WDt (@wm RT)).
  Notation wQ := (@wQ RT PMc Kfin).
  Definition good (w : WDt) (kk : Z) : Prop :=
    ART RT (snd w) (fst w) /\
    rt_frames RT (snd w) = (f, 5%nat) :: rt_frames RT Σ /\ rt_live RT (snd w) = rt_live RT Σ /\ rt_sp0 RT (snd w) = rt_sp0 RT Σ /\
    rt_credit RT Σ - 1 - NUMA_CREDIT * Z.min kk (blen bs + 2) - (if kk <=? 0 then 0 else mcost (blen bs + 64)) <= rt_credit RT (snd w) /\
    rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (s2a_X THIS TAPE SBUF OC IA tcap scap) m (fst w) /\
    fobj RT (snd w) (fst w) DOC 24.

  Lemma mcost_nonneg : forall n, 0 <= n -> 0 <= mcost n.
  Proof. intros n Hn. unfold mcost, DCOST. destruct (n <=? 64512); lia. Qed.

  Lemma good_mono : g_mono RT good.
  Proof using All.
    intros w kk kk' (G1 & G2 & G3 & G4 & G5 & G6 & G7) Hk. unfold good. repeat (split; [assumption|]). split; [|split; assumption].
    pose proof (mcost_nonneg (blen bs + 64) ltac:(pose proof (blen_nonneg bs); lia)) as MC. unfold NUMA_CREDIT in *.
    clear - G5 Hk MC. destruct (kk <=? 0) eqn:K1; destruct (kk' <=? 0) eqn:K2; lia.
  Qed.

  Lemma fp_ok_of_client : forall Σx lo' W, fp_client RT Σx lo' W -> fp_ok RT Σx lo' W.
  Proof.
    intros Σx lo' W H. unfold fp_client, fp_ok in *. rewrite Forall_forall in *. intros r Hr. specialize (H r Hr).
    destruct H as [H|[H|H]]; [left; exact H| right; left; exact H| right; right; left; exact H].
  Qed.
  Lemma good_fpc : forall w kk, good w kk -> fp_client RT (snd w) lo (s2_W E0).
  Proof using All.
    intros w kk (G1 & G2 & G3 & G4 & G5 & G6 & G7).
    destruct L_THIS as (pT & nT & IT & _ & T1 & T2). destruct L_TAPE as (pP & nP & IP & _ & P1 & P2). destruct L_SBUF as (pS & nS & IS & _ & S1 & S2).
    destruct L_OC as (pO & nO & IO & _ & O1 & O2). destruct L_IA as (pA & nA & IA' & _ & A1 & A2).
    unfold s2_W, E0. cbn [e_lo e_sp e_THIS e_TAPE e_tcap e_SBUF e_scap e_OC e_IA e_FF].
    repeat first [apply Forall_nil | apply Forall_cons]; cbn [fst snd].
    - left. clear - TOP. unfold USTACK_TOP in *. lia.
    - right; left. exists pT, nT. rewrite G3. split; [exact IT| clear - T1 T2; lia].
    - right; left. exists pP, nP. rewrite G3. split; [exact IP| clear - P1 P2; lia].
    - right; left. exists pS, nS. rewrite G3. split; [exact IS| clear - S1 S2; lia].
    - right; left. exists pO, nO. rewrite G3. split; [exact IO| clear - O1 O2; lia].
    - right; left. exists pA, nA. rewrite G3. split; [exact IA'| clear - A1 A2; lia].
    - right; right. exists f, 5%nat. rewrite G2. split; [left; reflexivity|]. change (fs_size 5) with 2048. clear. lia.
  Qed.
  Lemma good_fp : forall w kk, good w kk -> fp_ok RT (snd w) lo (s2_W E0).
  Proof using All. intros w kk HG. apply fp_ok_of_client. exact (good_fpc w kk HG). Qed.

  Lemma shz_in_chunk : forall Σx (mx : mem) X size, ART RT Σx mx ->
    (exists p n, In (p, n) (rt_live RT Σx) /\ p mod 8 = 0 /\ p <= X /\ X + size <= p + 8 * (n / 8)) -> shz mx X size.
  Proof using AF.
    intros Σx mx X size HA (p & n & Hin & P8 & H1 & H2). eapply shz_sub; [exact (shz_live RT AF Σx mx p n HA Hin P8)| exact H1| exact H2].
  Qed.

  Lemma shz_all_gen : forall Σx (mx : mem), ART RT Σx mx -> (forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σx)) -> fobj RT Σx mx DOC 24 ->
    shz_all E0 mx.
  Proof using All.
    intros Σx mx ART' HL FO. pose proof (blen_nonneg bs) as BL0.
    unfold shz_all. change (e_THIS E0) with THIS. change (e_DOC E0) with DOC. change (e_IDX E0) with IDX. change (e_BUF E0) with BUF.
    change (e_TAPE E0) with TAPE. change (e_SBUF E0) with SBUF. change (e_OC E0) with OC. change (e_IA E0) with IA.
    change (e_tcap E0) with tcap. change (e_scap E0) with scap. change (e_bs E0) with bs.
    assert (LIT : forall a n, In (a, n) ACC_LITS -> a mod 8 = 0 -> 0 <= a -> n mod 8 = 0 -> shz mx a n).
    { intros a n Hin A8 A0 N8. pose proof (shz_of_acc mx a n (acc_lit RT AF Σx mx a n ART' Hin) A8 A0) as S.
      replace (8 * (n / 8)) with n in S; [exact S|]. pose proof (Z.div_mod n 8 ltac:(lia)) as DM. clear - DM N8. lia. }
    split. { apply (shz_in_chunk Σx mx THIS 96 ART'). destruct L_THIS as (p & n & Hin & P8 & H1 & H2). exists p, n.
             split; [exact (HL _ Hin)|]. split; [exact P8|]. split; [exact H1|]. exact (chunk_al p n THIS 96 P8 A_THIS eq_refl H2). }
    split. { exact (fobj_shz RT AF Σx mx DOC 24 ART' FO). }
    split. { apply (shz_in_chunk Σx mx IDX _ ART'). destruct L_IDX as (p & n & Hin & P8 & H1 & H2). exists p, n.
             split; [exact (HL _ Hin)|]. split; [exact P8|]. split; [exact H1|].
             apply (chunk_al4 p n IDX (Z.of_nat (length iws)) (blen bs + 3) P8 A_IDX H2). clear - HIWL. lia. }
    split. { apply (shz_in_chunk Σx mx BUF _ ART'). destruct L_BUF as (p & n & Hin & P8 & H1 & H2). exists p, n.
             split; [exact (HL _ Hin)|]. split; [exact P8|]. split; [exact H1|]. apply chunk_un. clear - H2. lia. }
    split. { apply (shz_in_chunk Σx mx TAPE _ ART'). destruct L_TAPE as (p & n & Hin & P8 & H1 & H2). exists p, n.
             split; [exact (HL _ Hin)|]. split; [exact P8|]. split; [exact H1|].
             apply (chunk_al p n TAPE (8 * tcap) P8 A_TAPE); [rewrite Z.mul_comm; apply Z.mod_mul; lia| exact H2]. }
    split. { apply (shz_in_chunk Σx mx SBUF _ ART'). destruct L_SBUF as (p & n & Hin & P8 & H1 & H2). exists p, n.
             split; [exact (HL _ Hin)|]. split; [exact P8|]. split; [exact H1|]. exact (chunk_al p n SBUF scap P8 A_SBUF HSC8 H2). }
    split. { apply (shz_in_chunk Σx mx OC _ ART'). destruct L_OC as (p & n & Hin & P8 & H1 & H2). exists p, n.
             split; [exact (HL _ Hin)|]. split; [exact P8|]. split; [exact H1|]. exact (chunk_al p n OC 8192 P8 A_OC eq_refl H2). }
    split. { apply (shz_in_chunk Σx mx IA _ ART'). destruct L_IA as (p & n & Hin & P8 & H1 & H2). exists p, n.
             split; [exact (HL _ Hin)|]. split; [exact P8|]. split; [exact H1|]. exact (chunk_al p n IA 1024 P8 A_IA eq_refl H2). }
    unfold T_SOWN, T_DIG, T_P10, T_P5, T_ESC.
    split. { apply LIT; [unfold ACC_LITS; cbn [In]; tauto| reflexivity| lia| reflexivity]. }
    split. { apply LIT; [unfold ACC_LITS; cbn [In]; tauto| reflexivity| lia| reflexivity]. }
    split. { apply LIT; [unfold ACC_LITS; cbn [In]; tauto| reflexivity| lia| reflexivity]. }
    split. { apply LIT; [unfold ACC_LITS; cbn [In]; tauto| reflexivity| lia| reflexivity]. }
    apply LIT; [unfold ACC_LITS; cbn [In]; tauto| reflexivity| lia| reflexivity].
  Qed.

  Lemma good_shz : g_shz RT E0 good.
  Proof using All.
    intros w kk HG m' MU WM. pose proof (good_fp w kk HG) as FP. pose proof (good_fpc w kk HG) as FPC. destruct HG as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
    change (e_m0 (wE w)) with (fst w) in MU, WM. change (s2_W (wE w)) with (s2_W E0) in MU.
    assert (LOR' : rt_sp0 RT (snd w) - STACK_WIN <= lo) by (rewrite G4; exact LOR).
    pose proof (art_of_munch RT AF (snd w) (fst w) m' lo (s2_W E0) G1 LOR' FP MU WM) as ART'.
    change (shz_all (wE w) m') with (shz_all E0 m').
    apply (shz_all_gen (snd w) m' ART'); [intros e He; rewrite G3; exact He|].
    exact (fobj_munch RT AF (snd w) (fst w) m' lo (s2_W E0) DOC 24 G1 LOR' FPC MU G7).
  Qed.

  Lemma good_cc : forall w kk, good w kk -> a_cc (wE w).
  Proof using All.
    intros w kk HG m' MU WM. pose proof (good_fp w kk HG) as FP. destruct HG as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
    change (e_m0 (wE w)) with (fst w) in MU, WM. change (s2_W (wE w)) with (s2_W E0) in MU.
    assert (LOR' : rt_sp0 RT (snd w) - STACK_WIN <= lo) by (rewrite G4; exact LOR).
    pose proof (art_of_munch RT AF (snd w) (fst w) m' lo (s2_W E0) G1 LOR' FP MU WM) as ART'.
    destruct (af_client_consts RT AF (snd w) m' ART') as (C1 & C2 & _). exact (conj C1 C2).
  Qed.
  Lemma room16 : e_lo E0 + 16 <= e_spa E0.
  Proof using All. change (e_lo E0) with lo. change (e_spa E0) with spa. clear - ROOM SPA1. unfold S2A_STACK, NUMA_STACK, RT_STACK in ROOM. lia. Qed.

  Lemma caller_split : forall a, aclient (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) a ->
    (bv_unsigned sp <= a \/ a < lo) /\ ~ (f <= a < f + 2048).
  Proof using All.
    intros a Ha. split.
    - destruct (aclient_split_c RT AF Σ m _ a ART0 Ha) as [H|H]; [left; exact H| right; clear - H LOR; lia].
    - assert (SPL : rt_sp0 RT Σ - STACK_WIN <= bv_unsigned sp) by (clear - LOR ROOM; unfold S2A_STACK, NUMA_STACK, RT_STACK in ROOM; lia).
      exact (proj1 (newframe_apart RT AF Σ Σ1 m3 f 5%nat (bv_unsigned sp) a ART1 FRS LVS SP0S SPL Ha)).
  Qed.
  Lemma caller_client : forall w kk a usp, good w kk -> usp <= bv_unsigned sp ->
    aclient (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) a -> aclient (rt_live RT (snd w)) (rt_frames RT (snd w)) usp a.
  Proof using All.
    intros w kk a usp (G1 & G2 & G3 & G4 & G5 & G6 & G7) Hu Ha. rewrite G2, G3.
    eapply aclient_mono; [exact Ha| auto| intros e He; right; exact He| exact Hu].
  Qed.
  Lemma caller_outside : forall a, aclient (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) a ->
    outside (s2a_X THIS TAPE SBUF OC IA tcap scap) a -> outside (s2_W E0) a /\ outside (s2_X0 E0) a.
  Proof using All.
    intros a Ha HO. destruct (caller_split a Ha) as [S1 S2]. unfold s2a_X in HO. unfold s2_W, s2_X0, E0.
    cbn [outside e_lo e_sp e_THIS e_TAPE e_tcap e_SBUF e_scap e_OC e_IA e_FF] in *.
    destruct HO as (O1 & O2 & O3 & O4 & O5 & _).
    split; repeat (split; [first [assumption | clear - S1; lia | clear - S2; lia]|]); exact I.
  Qed.

  Lemma good_num : g_num RT E0 good.
  Proof using All.
    intros w kk HG Hk. pose proof HG as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
    change (e_n E0) with (n idxs) in Hk. pose proof (n_le_len _ _ HS1) as NL.
    pose proof (mcost_nonneg (blen bs + 64) ltac:(pose proof (blen_nonneg bs); lia)) as MC.
    constructor.
    - exact G1.
    - rewrite G2. cbn [length]. clear - FRL. unfold S2A_FRAMES in FRL. lia.
    - clear - G5 CRD Hk NL MC. unfold S2A_COST, NUMA_CREDIT in *. destruct (kk <=? 0); lia.
    - rewrite G4. exact LOR.
    - change (e_lo E0) with lo. change (e_spa E0) with spa. clear - ROOM SPA1. unfold S2A_STACK in ROOM. lia.
    - exact TOP.
    - exact ETP.
    - rewrite G3. destruct L_BUF as (p & n0 & Hin & P8 & H1 & H2). exists p, n0. repeat (split; [assumption|]). change (e_BUF E0) with BUF. change (e_bs E0) with bs. clear - H2. lia.
    - intros x Hx. unfold s2_region in Hx. rewrite G2, G3.
      change (e_spa E0) with spa in *. change (e_sp E0) with sp in Hx. change (e_THIS E0) with THIS in Hx. change (e_DOC E0) with DOC in Hx. change (e_IDX E0) with IDX in Hx.
      change (e_BUF E0) with BUF in Hx. change (e_TAPE E0) with TAPE in Hx. change (e_SBUF E0) with SBUF in Hx. change (e_OC E0) with OC in Hx. change (e_IA E0) with IA in Hx.
      change (e_FF E0) with f in Hx. change (e_iws E0) with iws in Hx. change (e_bs E0) with bs in Hx. change (e_tcap E0) with tcap in Hx. change (e_scap E0) with scap in Hx.
      destruct Hx as [Hx|[Hx|[Hx|[Hx|[Hx|[Hx|[Hx|[Hx|[Hx|Hx]]]]]]]]].
      + left. clear - Hx TOP. unfold USTACK_TOP in *. lia.
      + right; right; left. destruct L_THIS as (p & n0 & Hin & _ & H1 & H2). exists p, n0. split; [exact Hin| clear - Hx H1 H2; lia].
      + right; right; right; left. destruct FOBJ as (_ & _ & (fd & cd & IFD & FD1 & FD2) & _). change (8 * ((24 + 7) / 8)) with 24 in FD2.
        exists fd, cd. split; [right; exact IFD| clear - Hx FD1 FD2; lia].
      + right; right; left. destruct L_IDX as (p & n0 & Hin & _ & H1 & H2). exists p, n0. split; [exact Hin| clear - Hx H1 H2; lia].
      + right; right; left. destruct L_BUF as (p & n0 & Hin & _ & H1 & H2). exists p, n0. split; [exact Hin| clear - Hx H1 H2; lia].
      + right; right; left. destruct L_TAPE as (p & n0 & Hin & _ & H1 & H2). exists p, n0. split; [exact Hin| clear - Hx H1 H2; lia].
      + right; right; left. destruct L_SBUF as (p & n0 & Hin & _ & H1 & H2). exists p, n0. split; [exact Hin| clear - Hx H1 H2; lia].
      + right; right; left. destruct L_OC as (p & n0 & Hin & _ & H1 & H2). exists p, n0. split; [exact Hin| clear - Hx H1 H2; lia].
      + right; right; left. destruct L_IA as (p & n0 & Hin & _ & H1 & H2). exists p, n0. split; [exact Hin| clear - Hx H1 H2; lia].
      + right; right; right; left. exists f, 5%nat. split; [left; reflexivity|]. change (fs_size 5) with 2048. clear - Hx. lia.
    - rewrite G2. discriminate.
  Qed.

  Lemma doc_shadow : forall w kk x, good w kk -> shad DOC <= x < shad DOC + 3 ->
    (forall usp, aclient (rt_live RT (snd w)) (rt_frames RT (snd w)) usp x) /\ x < lo /\ outside (s2_X0 E0) x.
  Proof using All.
    intros w kk x HG Hx. pose proof HG as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
    destruct (fobj_shadow_range RT AF (snd w) (fst w) DOC 24 G1 G7) as (f' & c' & Hin & S1 & S2 & _). change ((24 + 7) / 8) with 3 in S2.
    pose proof (fframe_ranges RT AF (snd w) (fst w) f' c' G1 Hin) as (_ & _ & _ & _ & R5). rewrite G4 in R5.
    pose proof (af_fshadow_apart RT AF (snd w) (fst w) f' c' G1 Hin) as (AL & AFR). rewrite G3 in AL.
    split; [| split].
    - intros usp. right; right; right; right. exists f', c'. split; [exact Hin| clear - Hx S1 S2; lia].
    - clear - Hx S2 R5 LOR. lia.
    - destruct L_THIS as (pT & nT & IT & _ & T1 & T2). destruct L_TAPE as (pP & nP & IP & _ & P1 & P2). destruct L_SBUF as (pS & nS & IS & _ & Q1 & Q2).
      destruct L_OC as (pO & nO & IO & _ & O1 & O2). destruct L_IA as (pA & nA & IA' & _ & A1 & A2).
      pose proof (AL _ _ IT) as X1. pose proof (AL _ _ IP) as X2. pose proof (AL _ _ IS) as X3. pose proof (AL _ _ IO) as X4. pose proof (AL _ _ IA') as X5.
      pose proof (AFR f 5%nat ltac:(rewrite G2; left; reflexivity)) as X6. change (fs_size 5) with 2048 in X6.
      unfold s2_X0, E0. cbn [outside e_THIS e_TAPE e_tcap e_SBUF e_scap e_OC e_IA e_FF].
      split; [clear - Hx S1 S2 X1 T1 T2; lia|]. split; [clear - Hx S1 S2 X2 P1 P2; lia|]. split; [clear - Hx S1 S2 X3 Q1 Q2; lia|].
      split; [clear - Hx S1 S2 X4 O1 O2; lia|]. split; [clear - Hx S1 S2 X5 A1 A2; lia|]. split; [clear - Hx S1 S2 X6; lia| exact I].
  Qed.

  Lemma good_rootf : g_rootf RT E0 good.
  Proof using All.
    intros w HG. pose proof HG as (G1 & G2 & G3 & G4 & G5 & G6 & G7). constructor.
    - apply (good_num w 0 HG). change (e_n E0) with (n idxs). pose proof (n_pos _ _ HS1). lia.
    - rewrite G3. exact LVL.
    - change (e_bs E0) with bs. pose proof (blen_nonneg bs) as BL0. clear - G5 CRD BL0. unfold S2A_COST, NUMA_CREDIT in *. change (0 <=? 0) with true in G5. cbv iota in G5.
      pose proof (Z.le_min_l 0 (blen bs + 2)). lia.
    - intros Σ' m' ART' HL FRS' AG. apply (shz_all_gen Σ' m' ART'); [intros e He; apply HL; rewrite G3; exact He|].
      change (e_DOC E0) with DOC in AG. change (wm RT w) with (fst w) in AG.
      apply (fobj_agree RT AF (snd w) Σ' (fst w) m' DOC 24 G1 G7 FRS'). change ((24 + 7) / 8) with 3. exact AG.
    - intros x Hx. change (e_DOC E0) with DOC in Hx. change (e_lo E0) with lo. exact (doc_shadow w 0 x HG Hx).
  Qed.

  Lemma good_step : g_step RT E0 good.
  Proof using All.
    intros w w' kk HG Hk (m1 & MU & WM & ARTm1 & RA & PEX & EF & EL & ES & EC). pose proof HG as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
    change (e_n E0) with (n idxs) in Hk. pose proof (n_le_len _ _ HS1) as NL.
    change (s2_W (Sj_stage2_main.wE E0 WDt (@wm RT) w)) with (s2_W E0) in MU. change (wm RT w) with (fst w) in *. change (wm RT w') with (fst w') in *.
    change (e_spa E0) with spa in *. change (e_lo E0) with lo in *.
    pose proof (mcost_nonneg (blen bs + 64) ltac:(pose proof (blen_nonneg bs); lia)) as MC.
    assert (LOR' : rt_sp0 RT (snd w) - STACK_WIN <= lo) by (rewrite G4; exact LOR).
    unfold good. split; [exact (proj1 RA)|]. split; [rewrite EF; exact G2|]. split; [rewrite EL; exact G3|]. split; [rewrite ES; exact G4|].
    split. { clear - G5 EC Hk NL MC. unfold NUMA_CREDIT in *. destruct (kk <=? 0); destruct (kk + 1 <=? 0) eqn:K2; lia. }
    split.
    - intros a Ha HO. destruct (caller_outside _ Ha HO) as [OW _]. destruct (caller_split _ Ha) as [SPL _].
      rewrite (PEX a (caller_client w kk _ spa HG ltac:(clear - SPA1; lia) Ha) ltac:(clear - SPL SPA1 ROOM; unfold S2A_STACK, NUMA_STACK, RT_STACK in ROOM; lia)).
      rewrite (MU a OW). exact (G6 a Ha HO).
    - pose proof (fobj_munch RT AF (snd w) (fst w) m1 lo (s2_W E0) DOC 24 G1 LOR' (good_fpc w kk HG) MU G7) as FO1.
      apply (fobj_agree RT AF (snd w) (snd w') m1 (fst w') DOC 24 ARTm1 FO1 EF). change ((24 + 7) / 8) with 3.
      apply (agree_of_pres_ex _ _ _ _ _ _ _ _ PEX). intros x Hx. destruct (doc_shadow w kk x HG Hx) as (D1 & D2 & _).
      split; [exact (D1 spa)| clear - D2 ROOM SPA1; unfold S2A_STACK, NUMA_STACK, RT_STACK in ROOM; lia].
  Qed.

  Lemma good_root : g_root RT E0 good.
  Proof using All.
    intros w w' HG (ART' & PFP & EF & EL & ES & EC). pose proof HG as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
    change (wm RT w) with (fst w) in *. change (wm RT w') with (fst w') in *. change (e_sp E0) with sp in *. change (e_bs E0) with bs in *.
    pose proof (blen_nonneg bs) as BL0.
    unfold good. split; [exact ART'|]. split; [rewrite EF; exact G2|]. split; [rewrite EL; exact G3|]. split; [rewrite ES; exact G4|].
    split. { clear - G5 EC BL0. unfold NUMA_CREDIT in *. change (0 <=? 0) with true in G5. change (1 <=? 0) with false. cbv iota in *.
             pose proof (Z.le_min_l 0 (blen bs + 2)). rewrite (Z.min_l 1 (blen bs + 2)) by lia. lia. }
    split.
    - intros a Ha HO. destruct (caller_outside _ Ha HO) as [_ OX].
      rewrite (PFP a (caller_client w 0 _ _ HG (Z.le_refl _) Ha) OX). exact (G6 a Ha HO).
    - apply (fobj_agree RT AF (snd w) (snd w') (fst w) (fst w') DOC 24 G1 G7 EF). change ((24 + 7) / 8) with 3.
      apply (agree_of_pres_fp _ _ _ _ _ _ _ PFP). intros x Hx. destruct (doc_shadow w 0 x HG Hx) as (D1 & _ & D3).
      split; [exact (D1 _)| exact D3].
  Qed.

  Lemma good_kxw : forall w kk tws sbs, good w kk -> exit_kw (s2_ghost (wE w) tws sbs) (wQ w).
  Proof using All.
    intros w kk tws sbs HG. pose proof HG as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
    pose proof (env_at_ok E0 (fst w) E0_ok) as OKw. pose proof (env_ok_ghost _ tws sbs OKw) as OKg.
    unfold exit_kw. intros until m1. intros HE HMX.
    eapply evt_mono; [exact (s2_exitw (s2_ghost (wE w) tws sbs) OKg err x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x27 x28 x29 x30 x31 F fc m1 HE HMX)|].
    clear HMX HE. intros ms' (err' & y5 & y6 & y7 & y12 & y13 & y14 & y15 & y16 & y17 & y18 & y20 & y21 & y22 & y23 & y24 & y25 & y27 & y28 & y29 & y30 & y31 & F' & fc' & m' & -> & HE' & HMX').
    destruct HMX' as (FRM' & (jlo & jhi & FR') & SAV' & GAP' & FFW' & (nxt' & IMPL') & MI' & MU' & WM' & ST' & TIMG').
    destruct TIMG' as (TT1 & TT2 & TT3 & TT4 & _ & _ & TSB).
    unfold s2_errok in HE'.
    cbn [e_ra e_sp e_gp e_tp e_s0 e_s1 e_s2 e_s3 e_s4 e_s5 e_s6 e_s7 e_s8 e_s9 e_s10 e_s11 e_lo e_spa e_FF e_THIS e_DOC e_IDX e_BUF e_TAPE e_SBUF e_OC e_IA
         e_bs e_idxs e_iws e_tcap e_scap e_vptr e_p12 e_nxt0 e_p28 e_capv e_p50 e_dcap e_j0 e_j256 e_m0 e_tws e_sbs s2_ghost] in FR', SAV', GAP', FFW', IMPL', MU', WM', ST', TT1, TT2, TT3, TT4, HE' |- *.
    change (e_TAPE (wE w)) with TAPE in *. change (e_SBUF (wE w)) with SBUF in *. change (e_tcap (wE w)) with tcap in *. change (e_scap (wE w)) with scap in *.
    assert (HE64 : 0 <= err' < 64) by (clear - HE'; destruct HE' as [HF|[HZ _]]; lia).
    change (e_spa (wE w)) with spa in *. change (e_sp (wE w)) with sp in *. change (e_gp (wE w)) with gp. change (e_tp (wE w)) with tp.
    change (e_FF (wE w)) with f in *. change (e_lo (wE w)) with lo in *. change (e_THIS (wE w)) with THIS in *.
    change (e_m0 (wE w)) with (fst w) in *. change (s2_W (wE w)) with (s2_W E0) in MU'.
    assert (LOR' : rt_sp0 RT (snd w) - STACK_WIN <= lo) by (rewrite G4; exact LOR).
    pose proof (art_of_munch RT AF (snd w) (fst w) m' lo (s2_W E0) G1 LOR' (good_fp w kk HG) MU' WM') as ART'.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    assert (SPAR : 0 <= spa < 2^64) by (pose proof (stk_lo_nonneg _ _ _ _ ST'); clear - SPA1 SPR ROOM H; unfold S2A_STACK, NUMA_STACK, RT_STACK in ROOM; lia).
    unfold Sj_stage2_world.wQ.
    eapply (aevt_stack_free5 RT RTF PMc FDO MST (snd w) Kfin) with (f := f) (fr := rt_frames RT Σ) (lo := lo);
      [ reflexivity | exact ETP | exact G2 | exact ART' | exact MI'
      | unfold call_ok; rewrite (unsigned_lit spa SPAR); split; [exact ST'|]; split; [exact LOR'|];
        clear - ROOM SPA1 TOP SPA32; unfold S2A_STACK, NUMA_STACK, RT_STACK, USTACK_TOP in *; split; [lia|]; split; [lia|]; Z.div_mod_to_equations; lia
      | exact FRM' | ].
    intros Σ2 v t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F2 fc2 m2 FRM2 RA PR EF EL ES EC.
    rewrite (unsigned_lit spa SPAR) in RA, PR. destruct RA as (ART2 & MI2 & WM2 & ST2).

    assert (AG : agree_on (fun x => spa <= x < bv_unsigned sp) m' m2).
    { apply (agree_of_pres _ _ _ _ _ _ PR). intros x Hx. left. clear - Hx TOP. unfold USTACK_TOP in *. lia. }
    pose proof (rw_cells_merge bsegs m' spa [] [CB 264 jlo; C8 (Z_to_bv 64 f)] [C8 (Z_to_bv 64 err'); CB 32 jhi] FR') as FRm.
    cbn [app cells_size csize Nat.add] in FRm.
    eapply (rw_cells_agree bsegs m' m2) in FRm; [| eapply agree_sub; [exact AG| cbn [cells_size csize Nat.add]; intros x Hx; clear - Hx SPA1; lia] | exact WM2].
    eapply (rw_cells_agree bsegs m' m2) in SAV'; [| eapply agree_sub; [exact AG| unfold saved_cells; cbn [cells_size csize Nat.add]; intros x Hx; clear - Hx SPA1; lia] | exact WM2].
    eapply (stk_agree bsegs m' m2) in GAP'; [| eapply agree_sub; [exact AG| intros x Hx; cbv beta; clear - Hx SPA1; lia] | exact WM2].
    apply (aevt_evt RT AF PMc MST).
    rewrite (ret_pc_even 0xdbcb4) by (first [lia | reflexivity]).
    eapply evt_mono; [exact (s2_epi (wE w) OKw (Z_to_bv 64 err') _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F2 fc2 m2 _ _ FRm SAV' GAP' ST2)|].
    intros ms2 (q0 & q1 & q2 & q3 & q4 & q5 & q6 & q7 & q8 & q9 & q10 & q11 & q12 & q13 & -> & STF).
    change (e_lo (wE w)) with lo in STF. change (e_sp (wE w)) with sp in STF.
    apply (aevt_done RT PMc). intros c Hc. exists Σ2.
    split; [| split; [exact EF| split; [rewrite EL; exact G3| split; [rewrite ES; exact G4|]]]].
    - eapply AST_conseq; [exact Hc| | intros mo H; exact H]. intros ms <-.
      exists m2, (Z_to_bv 64 err'), nxt'.
      split. { unfold ret_st. do 16 eexists. reflexivity. }
      split. { rewrite unsigned_lit by (clear - HE64; lia). clear - HE64; lia. }
      split. {
               destruct HE' as [HF | [-> HOK]]; [left; rewrite unsigned_lit by (clear - HF; lia); exact HF | right].
               split; [reflexivity|]. exists tws, sbs.
               assert (AT : agree_on (fun x => TAPE <= x < TAPE + 8 * tcap \/ SBUF <= x < SBUF + scap) m' m2).
               { apply (agree_of_pres _ _ _ _ _ _ PR). intros x Hx. right; right; left. rewrite G3.
                 destruct Hx as [Hx|Hx]; [destruct L_TAPE as (p & n0 & Hin & _ & H1 & H2) | destruct L_SBUF as (p & n0 & Hin & _ & H1 & H2)]; exists p, n0; split; [exact Hin| clear - Hx H1 H2; lia | exact Hin | clear - Hx H1 H2; lia]. }
               pose proof (Zle_0_nat (length tws)) as LT0. pose proof (Zle_0_nat (length sbs)) as LS0.
               split. { unfold twords in TT1. apply (bytes_at_agree bsegs m' m2 _ _ TT1). eapply agree_sub; [exact AT|]. intros x Hx. cbv beta in Hx. rewrite u64s_length, length_map in Hx. left. clear - Hx TT3 LT0. lia. }
               split. { unfold zbytes in TT2. apply (bytes_at_agree bsegs m' m2 _ _ TT2). eapply agree_sub; [exact AT|]. intros x Hx. cbv beta in Hx. rewrite length_map in Hx. right. clear - Hx TT4 LS0. lia. }
               split; [exact HOK|]. split; [exact TSB|]. split; [exact TT3| exact TT4]. }
      split. { exact FRM2. }
      split. { split; [exact ART2|]. split; [exact MI2| exact STF]. }
      split.
      + intros a Ha HO. destruct (caller_outside _ Ha HO) as [OW _].
        rewrite (PR a). 2:{ rewrite G3. eapply aclient_mono; [exact Ha| auto| auto| clear - SPA1; lia]. }
        rewrite (MU' a OW). exact (G6 a Ha HO).
      + eapply (rw_cells_agree bsegs m' m2); [exact IMPL'| | exact WM2].
        apply (agree_of_pres _ _ _ _ _ _ PR). intros x Hx. unfold s2a_impl_cells in Hx. cbn [cells_size csize Nat.add] in Hx.
        right; right; left. destruct L_THIS as (p & n0 & Hin & _ & H1 & H2). exists p, n0. rewrite G3. split; [exact Hin| clear - Hx H1 H2; lia].
    - rewrite EC. pose proof (mcost_nonneg (blen bs + 64) ltac:(pose proof (blen_nonneg bs); lia)) as MC.
      clear - G5 MC. unfold S2A_COST, NUMA_CREDIT in *. pose proof (Z.le_min_r kk (blen bs + 2)). destruct (kk <=? 0); lia.
  Qed.

  Lemma good_kx : g_kx RT PMc E0 Kfin good.
  Proof using All. intros w kk tws sbs HG. apply exit_k_of_w. exact (good_kxw w kk tws sbs HG). Qed.

  Variable docv : word.
  Variables j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j160 j168 j176 j184 j192 j200 j208 j216 j224 j232 j240 j248 j256 j264 j272 j280 j288 j296 j304 : list byte.
  Hypothesis PRESALL : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (bv_unsigned a) -> m3 a = m a.
  Hypothesis WMALL : wmono bsegs m m3.
  Hypothesis MI3 : mem_inv bsegs m3.
  Hypothesis FR3 : rw_cells bsegs m3 spa [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; CB 8 j152; CB 8 j160; CB 8 j168; CB 8 j176; CB 8 j184; CB 8 j192; CB 8 j200; CB 8 j208; CB 8 j216; CB 8 j224; CB 8 j232; CB 8 j240; CB 8 j248; CB 8 j256; CB 8 j264; CB 8 j272; CB 8 j280; CB 8 j288; CB 8 j296; CB 8 j304].
  Hypothesis SAV3 : rw_cells bsegs m3 (bv_unsigned sp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Hypothesis GAP3 : stk bsegs m3 (spa + 312) (bv_unsigned sp + -104).
  Hypothesis FFW3 : wr_at bsegs m3 f 8.
  Hypothesis ST3 : stk bsegs m3 lo spa.
  Hypothesis IMPL0 : rw_cells bsegs m THIS (s2a_impl_cells vptr (Z.of_nat (length idxs)) IDX capv OC IA BUF (blen bs) nxt docv p12 p28 p50).
  Hypothesis DOCC0 : rw_cells bsegs m DOC [C8 (Z_to_bv 64 TAPE); C8 (Z_to_bv 64 SBUF); C8 dcap].
  Hypothesis IDXA0 : u32arr bsegs m IDX iws.
  Hypothesis BUF0 : bytes_at bsegs m BUF (Sj_stage1_kit.padded_bytes bs).
  Hypothesis OCA0 : exists ocs, u32arr bsegs m OC ocs /\ length ocs = 2048%nat.
  Hypothesis IAA0 : exists ias, u8arr bsegs m IA ias /\ length ias = 1024%nat.

  Lemma in_chunk_agree : forall X size, live_reg RT Σ X size -> agree_on (fun x => X <= x < X + size) m m3.
  Proof using All.
    intros X size (p & n0 & Hin & _ & H1 & H2) a Ha. apply PRESALL. right; right; left. exists p, n0. split; [exact Hin| clear - Ha H1 H2; lia].
  Qed.

  Lemma good0 : good (m3, Σ1) 0.
  Proof using All.
    unfold good. cbn [fst snd]. split; [exact ART1|]. split; [exact FRS|]. split; [exact LVS|]. split; [exact SP0S|].
    split. { rewrite CRS. pose proof (blen_nonneg bs) as BL0. clear - BL0. unfold NUMA_CREDIT. change (0 <=? 0) with true. cbv iota.
             rewrite (Z.min_l 0 (blen bs + 2)) by lia. lia. }
    split. { intros a Ha _. exact (PRESALL a Ha). }
    pose proof FOBJ as FO. destruct (fobj_shadow_range RT AF Σ m DOC 24 ART0 FO) as (f' & c' & Hin & S1 & S2 & _). change ((24 + 7) / 8) with 3 in S2.
    destruct FO as (D8 & N0 & (fd & cd & IFD & FD1 & FD2) & HB).
    split; [exact D8|]. split; [exact N0|]. split; [exists fd, cd; split; [rewrite FRS; right; exact IFD| split; assumption]|].
    apply (bytes_at_agree bsegs m m3 _ _ HB). intros a Ha. rewrite repeat_length in Ha. change (Z.of_nat (Z.to_nat ((24 + 7) / 8))) with 3 in Ha.
    apply PRESALL. right; right; right; right. exists f', c'. split; [exact Hin| clear - Ha S1 S2; lia].
  Qed.

  Lemma tapew3 : wr_at bsegs m3 TAPE (8 * tcap).
  Proof using All.
    destruct (live_reg_rng Σ m _ _ ART0 L_TAPE) as (pP & nP & IP & _ & P1 & P2 & P3 & P4).
    apply (wr_at_transport bsegs m m3 _ _ (wr_at_sub m pP nP TAPE (8 * tcap) (proj1 (af_acc_live RT AF Σ m pP nP ART0 IP)) P1 P2 ltac:(clear - P1 P3; lia)) WMALL).
  Qed.
  Lemma sbufw3 : wr_at bsegs m3 SBUF scap.
  Proof using All.
    destruct (live_reg_rng Σ m _ _ ART0 L_SBUF) as (pS & nS & IS & _ & Q1 & Q2 & Q3 & Q4).
    apply (wr_at_transport bsegs m m3 _ _ (wr_at_sub m pS nS SBUF scap (proj1 (af_acc_live RT AF Σ m pS nS ART0 IS)) Q1 Q2 ltac:(clear - Q1 Q3; lia)) WMALL).
  Qed.
  Lemma tape_img_init : exists h0, tape_img E0 [h0] [] m3.
  Proof using All.
    pose proof tapew3 as WT. pose proof sbufw3 as WS. pose proof (blen_nonneg bs) as BL0.
    pose proof (wr_at_stk m3 _ _ WT) as S1. pose proof (wr_at_stk m3 _ _ WS) as S2.
    destruct WT as (T0 & T1 & _). destruct WS as (U0 & U1 & _).
    destruct (stk_split bsegs m3 _ (TAPE + 8) _ S1 ltac:(clear - HTC1 BL0; lia)) as [S3 _].
    destruct (stk_bytes bsegs m3 _ _ S3 ltac:(lia)) as (bs8 & HL & HB).
    destruct (le8_surj bs8 ltac:(clear - HL; lia)) as (v & <-).
    exists (bv_unsigned v). unfold tape_img, twords, zbytes, E0. cbn [map u64s length Z.of_nat Pos.of_succ_nat e_TAPE e_SBUF e_tcap e_scap].
    rewrite Z_to_bv_bv_unsigned.
    split; [|split; [|split; [clear - HTC1 BL0; lia|split; [clear - HSC1 BL0; lia|split; [exact S1 | split; [exact S2 | constructor]]]]]].
    - apply bytes_at_app. split; [exact HB|]. rewrite length_le8. apply timg_bytes_at_nil. clear - T0 T1 HTC1 BL0. lia.
    - apply timg_bytes_at_nil. clear - U0 U1 HSC1 HSC2 BL0. lia.
  Qed.

  Lemma mem1_0 : forall fc, frm0 fc -> forall h0, tape_img E0 [h0] [] m3 -> MEM1 (s2_ghost E0 [h0] []) docv fc m3.
  Proof using All.
    intros fc FRM h0 TI. pose proof (blen_nonneg bs) as BL0.
    destruct OCA0 as (ocs & OCA & OCL). destruct IAA0 as (ias & IAA & IAL).
    destruct (live_reg_rng Σ m _ _ ART0 L_TAPE) as (pP & nP & IP & _ & P1 & P2 & P3 & P4).
    destruct (live_reg_rng Σ m _ _ ART0 L_SBUF) as (pS & nS & IS & _ & Q1 & Q2 & Q3 & Q4).
    unfold MEM1. cbn [e_ra e_sp e_gp e_tp e_s0 e_s1 e_s2 e_s3 e_s4 e_s5 e_s6 e_s7 e_s8 e_s9 e_s10 e_s11 e_lo e_spa e_FF e_THIS e_DOC e_IDX e_BUF e_TAPE e_SBUF e_OC e_IA
         e_bs e_idxs e_iws e_tcap e_scap e_vptr e_p12 e_nxt0 e_p28 e_capv e_p50 e_dcap e_j0 e_j256 e_m0 e_tws e_sbs s2_ghost impl_cells0 fr_cells0 doc_cells saved_cells s2_W].
    split; [exact FRM|].
    split. { exists j0, j8, j16, j24, j32, j40, j48, j56, j64, j72, j80, j88, j96, j104, j112, j120, j128, j136, j144, j152, j160, j168, j176, j184, j192, j200, j208, j216, j224, j232, j240, j248, j256, j264, j272, j280, j288, j296, j304. exact FR3. }
    split; [exact SAV3|]. split; [exact GAP3|]. split; [exact FFW3|].
    split. { apply (rw_cells_agree bsegs m m3 _ _ IMPL0); [| exact WMALL]. exact (in_chunk_agree THIS 96 L_THIS). }
    split. { apply (rw_cells_agree bsegs m m3 _ _ DOCC0); [| exact WMALL]. cbn [cells_size csize Nat.add]. intros a Ha. apply PRESALL.
             destruct FOBJ as (_ & _ & (fd & cd & IFD & FD1 & FD2) & _). change (8 * ((24 + 7) / 8)) with 24 in FD2.
             right; right; right; left. exists fd, cd. split; [exact IFD| clear - Ha FD1 FD2; lia]. }
    split. { apply (u32arr_agree m m3 _ _ IDXA0); [| exact WMALL]. exact (in_chunk_agree IDX _ L_IDX). }
    split. { change (Sj_stage2_defs.padded_bytes (e_bs E0)) with (Sj_stage1_kit.padded_bytes bs). apply (bytes_at_agree bsegs m m3 _ _ BUF0).
             rewrite Sj_stage1_kit.padded_bytes_length. pose proof (in_chunk_agree BUF _ L_BUF) as AG. unfold blen in AG.
             eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in *. clear - Hx. lia. }
    split. { apply (wr_at_transport bsegs m m3 _ _ (wr_at_sub m pP nP TAPE (8 * tcap) (proj1 (af_acc_live RT AF Σ m pP nP ART0 IP)) P1 P2 ltac:(clear - P1 P3; lia)) WMALL). }
    split. { apply (wr_at_transport bsegs m m3 _ _ (wr_at_sub m pS nS SBUF scap (proj1 (af_acc_live RT AF Σ m pS nS ART0 IS)) Q1 Q2 ltac:(clear - Q1 Q3; lia)) WMALL). }
    split. { exists ocs. split; [| exact OCL]. apply (u32arr_agree m m3 _ _ OCA); [| exact WMALL]. rewrite OCL. exact (in_chunk_agree OC 8192 L_OC). }
    split. { exists ias. split; [| exact IAL]. apply (u8arr_agree m m3 _ _ IAA); [| exact WMALL]. rewrite IAL. exact (in_chunk_agree IA 1024 L_IA). }
    split; [exact MI3|]. split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact ST3| exact TI].
  Qed.

  Hypothesis HNUMA : numa_stmt RT.
  Hypothesis HNUMO : numo_stmt RT.
  Hypothesis HROOT : rootnum_stmt RT.
  Hypothesis STR_KEYA : forall E Q s, env_ok E -> a_shz E -> Inv (e_bs E) (e_idxs E) ObjBegin s -> (depth s + 1 < MAXDEPTH)%Z ->
    e_tok E (k s) = c_quote -> Z.of_nat (length (e_tws E)) = W s -> Z.of_nat (length (e_sbs E)) = sb s ->
    (forall hv, exit_k (gapp E [hv; tword t_str (sb s)] []) Q) ->
    (forall d hv cb, string_ok (e_bs E) (e_idxs E) (k s) d -> Z.of_nat (length cb) = d ->
       keyend_k (gapp (gapp E [hv; tword t_str (sb s)] []) [] (srec d cb)) Q (k s) (depth s + 1) (W s + 2) (sb s) d ((false, W s) :: scopes s)) ->
    keya_k E Q s.
  Hypothesis STR_KEYB : forall E Q s0, env_ok E -> a_shz E -> Inv (e_bs E) (e_idxs E) ObjCont s0 ->
    e_tok E (k s0) = c_comma -> e_tok E (k s0 + 1) = c_quote -> Z.of_nat (length (e_tws E)) = W s0 -> Z.of_nat (length (e_sbs E)) = sb s0 ->
    exit_k (gapp E [tword t_str (sb s0)] []) Q ->
    (forall d cb, string_ok (e_bs E) (e_idxs E) (k s0 + 1) d -> Z.of_nat (length cb) = d ->
       keyend_k (gapp (gapp E [tword t_str (sb s0)] []) [] (srec d cb)) Q (k s0 + 1) (depth s0) (W s0 + 1) (sb s0) d (scopes s0)) ->
    keyb_k E Q (mkst (k s0 + 1) (depth s0) (W s0) (sb s0) (scopes s0)).
  Hypothesis STR_O : forall E Q s, env_ok E -> a_shz E ->
    (0 <= k s < e_n E)%Z -> (1 <= W s /\ W s + 1 <= e_tcap E)%Z -> (0 <= sb s /\ 3 * sb s <= 5 * e_off E (k s))%Z -> (0 <= depth s <= 1023)%Z ->
    e_tok E (k s) = c_quote -> Z.of_nat (length (e_tws E)) = W s -> Z.of_nat (length (e_sbs E)) = sb s ->
    exit_k (gapp E [tword t_str (sb s)] []) Q ->
    (forall d cb, string_ok (e_bs E) (e_idxs E) (k s) d -> Z.of_nat (length cb) = d ->
       objcont_k (gapp (gapp E [tword t_str (sb s)] []) [] (srec d cb)) Q (mkst (k s + 1) (depth s) (W s + 1) (sb s + d + 5) (scopes s))) ->
    objstr_k E Q s.
  Hypothesis STR_A : forall E Q s, env_ok E -> a_shz E -> Inv (e_bs E) (e_idxs E) ArrValue s ->
    e_tok E (k s) = c_quote -> Z.of_nat (length (e_tws E)) = W s -> Z.of_nat (length (e_sbs E)) = sb s ->
    exit_k (gapp E [tword t_str (sb s)] []) Q ->
    (forall d cb, string_ok (e_bs E) (e_idxs E) (k s) d -> Z.of_nat (length cb) = d ->
       arrcont_k (gapp (gapp E [tword t_str (sb s)] []) [] (srec d cb)) Q (mkst (k s + 1) (depth s) (W s + 1) (sb s + d + 5) (scopes s))) ->
    arrstr_k E Q s.

  Hypothesis STR_ROOT : forall E Q, env_ok E -> a_shz E -> a_cc E -> (e_lo E + 16 <= e_spa E)%Z -> e_tok E 0 = c_quote ->
    Z.of_nat (length (e_tws E)) = 1%Z -> Z.of_nat (length (e_sbs E)) = 0%Z ->
    exit_k (gapp E [tword t_str 0%Z] []) Q ->
    (forall d cb, string_ok (e_bs E) (e_idxs E) 0 d -> Z.of_nat (length cb) = d ->
       docend_k (gapp (gapp E [tword t_str 0%Z] []) [] (srec d cb)) Q (mkst 1 0 2 (0 + d + 5) [])) ->
    rootprim_k E Q 0xc75c8.

  Lemma walk_all : forall x1 x5 x6 x7 x11 x12 x13 x16 x17 x18 x22 x23 x25 x27 x28 x29 x30 x31 (F : bvmap 5 word) (fc : bv 32),
    frm0 fc ->
    evt bsegs (aevt RT PMc Σ1 Kfin)
      (MS (mkR x1 (Z_to_bv 64 spa) gp tp x5 x6 x7 sp (Z_to_bv 64 spa) (Z_to_bv 64 (Z.shiftr (THIS + 88) 3)) x11 x12 x13 (Z_to_bv 64 (THIS + 88)) (Z_to_bv 64 f)
               x16 x17 x18 (Z_to_bv 64 (Z.shiftr f 3 + 2147450880)) (Z_to_bv 64 2147450880) (Z_to_bv 64 DOC) x22 x23 (Z_to_bv 64 THIS) x25
               (Z_to_bv 64 f) x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0xc5778) fc None m3 (seg_rom bsegs)).
  Proof using All.
    intros x1 x5 x6 x7 x11 x12 x13 x16 x17 x18 x22 x23 x25 x27 x28 x29 x30 x31 F fc FRM. destruct tape_img_init as [h0 TI].
    exact (s2_main E0 E0_ok WDt (@wm RT) wQ good good_shz good_mono good_kxw good_cc room16
             (HNUMA PMc FDO MST E0 E0_ok Kfin good good_shz good_mono good_kx good_num good_step)
             (HNUMO PMc FDO MST E0 E0_ok Kfin good good_shz good_mono good_kx good_num good_step)
             (HROOT PMc FDO MST E0 E0_ok Kfin good good_shz good_mono good_kx good_num good_step good_rootf good_root)
             STR_KEYA STR_KEYB STR_O STR_A STR_ROOT
             (m3, Σ1) h0 docv x1 x5 x6 x7 x11 x12 x13 x16 x17 x18 x22 x23 x25 x27 x28 x29 x30 x31 F fc m3 good0 (mem1_0 fc FRM h0 TI)).
  Qed.
End Adapt.

Lemma l_this_range : forall RT, art_facts RT -> forall Σ (m : mem) THIS, ART RT Σ m -> live_reg RT Σ THIS 96 ->
  0 < THIS /\ THIS + 96 <= rt_sp0 RT Σ - STACK_WIN.
Proof.
  intros RT AF Σ m THIS HA (p & n & Hin & _ & H1 & H2). pose proof (af_live_range RT AF Σ m p n HA Hin) as (P0 & P1 & _). lia.
Qed.

Lemma split_312 : forall (mx : mem) A jf, rw_cells bsegs mx A [CB 312 jf] ->
  exists j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j160 j168 j176 j184 j192 j200 j208 j216 j224 j232 j240 j248 j256 j264 j272 j280 j288 j296 j304, rw_cells bsegs mx A [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; CB 8 j152; CB 8 j160; CB 8 j168; CB 8 j176; CB 8 j184; CB 8 j192; CB 8 j200; CB 8 j208; CB 8 j216; CB 8 j224; CB 8 j232; CB 8 j240; CB 8 j248; CB 8 j256; CB 8 j264; CB 8 j272; CB 8 j280; CB 8 j288; CB 8 j296; CB 8 j304].
Proof.
  intros mx A jf H.
  apply (rw_cells_split_CB bsegs mx _ [] 312 jf [] [8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8]%nat) in H; [|reflexivity].
  cbn [mk_CB_cells app] in H. do 39 eexists. exact H.
Qed.

Theorem stage2at_ok : forall RT, art_facts RT -> rt_contracts_f RT -> numa_stmt RT -> numo_stmt RT -> rootnum_stmt RT ->
  (forall E Q s, env_ok E -> a_shz E -> Inv (e_bs E) (e_idxs E) ObjBegin s -> (depth s + 1 < MAXDEPTH)%Z -> e_tok E (k s) = c_quote -> Z.of_nat (length (e_tws E)) = W s -> Z.of_nat (length (e_sbs E)) = sb s -> (forall hv, exit_k (gapp E [hv; tword t_str (sb s)] []) Q) -> (forall d hv cb, string_ok (e_bs E) (e_idxs E) (k s) d -> Z.of_nat (length cb) = d -> keyend_k (gapp (gapp E [hv; tword t_str (sb s)] []) [] (srec d cb)) Q (k s) (depth s + 1) (W s + 2) (sb s) d ((false, W s) :: scopes s)) -> keya_k E Q s) ->
  (forall E Q s0, env_ok E -> a_shz E -> Inv (e_bs E) (e_idxs E) ObjCont s0 -> e_tok E (k s0) = c_comma -> e_tok E (k s0 + 1) = c_quote -> Z.of_nat (length (e_tws E)) = W s0 -> Z.of_nat (length (e_sbs E)) = sb s0 -> exit_k (gapp E [tword t_str (sb s0)] []) Q -> (forall d cb, string_ok (e_bs E) (e_idxs E) (k s0 + 1) d -> Z.of_nat (length cb) = d -> keyend_k (gapp (gapp E [tword t_str (sb s0)] []) [] (srec d cb)) Q (k s0 + 1) (depth s0) (W s0 + 1) (sb s0) d (scopes s0)) -> keyb_k E Q (mkst (k s0 + 1) (depth s0) (W s0) (sb s0) (scopes s0))) ->
  (forall E Q s, env_ok E -> a_shz E -> (0 <= k s < e_n E)%Z -> (1 <= W s /\ W s + 1 <= e_tcap E)%Z -> (0 <= sb s /\ 3 * sb s <= 5 * e_off E (k s))%Z -> (0 <= depth s <= 1023)%Z -> e_tok E (k s) = c_quote -> Z.of_nat (length (e_tws E)) = W s -> Z.of_nat (length (e_sbs E)) = sb s -> exit_k (gapp E [tword t_str (sb s)] []) Q -> (forall d cb, string_ok (e_bs E) (e_idxs E) (k s) d -> Z.of_nat (length cb) = d -> objcont_k (gapp (gapp E [tword t_str (sb s)] []) [] (srec d cb)) Q (mkst (k s + 1) (depth s) (W s + 1) (sb s + d + 5) (scopes s))) -> objstr_k E Q s) ->
  (forall E Q s, env_ok E -> a_shz E -> Inv (e_bs E) (e_idxs E) ArrValue s -> e_tok E (k s) = c_quote -> Z.of_nat (length (e_tws E)) = W s -> Z.of_nat (length (e_sbs E)) = sb s -> exit_k (gapp E [tword t_str (sb s)] []) Q -> (forall d cb, string_ok (e_bs E) (e_idxs E) (k s) d -> Z.of_nat (length cb) = d -> arrcont_k (gapp (gapp E [tword t_str (sb s)] []) [] (srec d cb)) Q (mkst (k s + 1) (depth s) (W s + 1) (sb s + d + 5) (scopes s))) -> arrstr_k E Q s) ->
  (forall E Q, env_ok E -> a_shz E -> a_cc E -> (e_lo E + 16 <= e_spa E)%Z -> e_tok E 0 = c_quote -> Z.of_nat (length (e_tws E)) = 1%Z -> Z.of_nat (length (e_sbs E)) = 0%Z -> exit_k (gapp E [tword t_str 0%Z] []) Q -> (forall d cb, string_ok (e_bs E) (e_idxs E) 0 d -> Z.of_nat (length cb) = d -> docend_k (gapp (gapp E [tword t_str 0%Z] []) [] (srec d cb)) Q (mkst 1 0 2 (0 + d + 5) [])) -> rootprim_k E Q 0xc75c8) ->
  stage2at_cps RT.
Proof.
  intros RT AF RTF HNUMA HNUMO HROOT SKA SKB SO SA SR. unfold stage2at_cps.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo THIS DOC IDX BUF TAPE SBUF OC IA
         bs idxs iws tcap scap vptr capv nxt docv dcap p12 p28 p50
         FDO MST ETP FRM HS1 HBOK HLEN HIWS HTC1 HTC2 HSC1 HSC2 HSC8 HIWL HIWM ART0 MI0 ST0 LOR ROOM TOP SP16 FRL CRD LVL
         L_THIS L_IDX L_BUF L_TAPE L_SBUF L_OC L_IA A_THIS A_IDX A_TAPE A_SBUF A_OC A_IA HPD FOBJ IMPL0 DOCC0 IDXA0 BUF0 OCA0 IAA0.
  apply cps_f_of_aevt.
  2:{ intros c (Σ' & HA & _). apply (cfrm0_of_asta RT Σ' PMc _ c HA). intros ms (m' & v & nxt' & _ & _ & _ & F0 & _). exact F0. }
  intros _.
  pose proof (af_client_consts RT AF Σ m ART0) as (G1 & G2 & G3 & G4).
  pose proof (af_sp0_win RT AF Σ m ART0) as SPW.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (blen_nonneg bs) as BL0.
  assert (LO0 : 0 <= lo) by exact (stk_lo_nonneg _ _ _ _ ST0).
  refine (aevt_evt RT AF PMc MST Σ _ _ _).
  eapply evt_mono; [apply (s2_pro1 ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo THIS DOC ST0);
                     [clear - ROOM; unfold S2A_STACK, NUMA_STACK, RT_STACK in ROOM; lia | exact SP16 | clear - SPW LOR; unfold STACK_WIN in LOR; lia
                     | exact MI0 | exact G1 | exact G2 | exact G3 | exact G4] |].
  intros ms1 (spa & x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x18 & x19 & x22 & x23 & x25 & x26 & x27 & x28 & x29 & x30 & x31 & m1 & jf
              & -> & SPA1 & SPA32 & FR1 & SAV1 & GAP1 & ST1 & MU1 & WM1 & MI1).
  assert (SPAR : 0 <= spa < 2^64) by (clear - SPA1 SPR ROOM LO0; unfold S2A_STACK, NUMA_STACK, RT_STACK in ROOM; lia).
  assert (FP1 : fp_ok RT Σ lo [(lo, bv_unsigned sp)]).
  { constructor; [left; cbn [fst snd]; clear - TOP; unfold USTACK_TOP in *; lia| constructor]. }
  pose proof (art_of_munch RT AF Σ m m1 lo _ ART0 LOR FP1 MU1 WM1) as ARTm1.
  change (Z_to_bv 64 437104) with (Z_to_bv 64 (e_stack_malloc 5)).
  eapply (aevt_stack_malloc RT RTF PMc FDO MST Σ _ 5%nat) with (lo := lo);
    [ right; reflexivity | exact ETP | clear - FRL; unfold S2A_FRAMES, FRAMES_MAX in *; lia
    | clear - CRD BL0; unfold S2A_COST, NUMA_CREDIT, mcost, DCOST in CRD; destruct (blen bs + 64 <=? 64512); lia
    | exact ARTm1 | exact MI1
    | unfold call_ok; rewrite (unsigned_lit spa SPAR); split; [exact ST1|]; split; [exact LOR|];
      clear - ROOM SPA1 TOP SPA32; unfold S2A_STACK, NUMA_STACK, RT_STACK, USTACK_TOP in *; split; [lia|]; split; [lia|]; Z.div_mod_to_equations; lia
    | intros Efr0; exfalso; destruct FOBJ as (_ & _ & (fd0 & cd0 & IFD0 & _) & _); rewrite Efr0 in IFD0; exact IFD0
    | exact FRM | ].
  intros Σ1 f t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F2 fc2 m2 FRM2 RA PR W1 W2 EFR ELV ESP ECR F0 F64 FTOP.
  rewrite (unsigned_lit spa SPAR) in RA, PR. destruct RA as (ART2 & MI2 & WM2 & ST2).
  change (fs_size 5 - 8) with 2040 in W1. change (fs_size 5 / 8) with 256 in W2. change (fs_size 5) with 2048 in FTOP.
  assert (SHF : shad f = Z.shiftr f 3 + 2147450880) by (unfold shad, SHB; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  rewrite SHF in W2.
  assert (INF : In (f, 5%nat) (rt_frames RT Σ1)) by (rewrite EFR; left; reflexivity).
  pose proof (fframe_ranges RT AF Σ1 m2 f 5%nat ART2 INF) as (_ & FH & _ & _ & FSH). change (fs_size 5) with 2048 in FH, FSH. rewrite ESP in FH, FSH.
  assert (SHF2 : shad (f + 2048) = Z.shiftr f 3 + 2147450880 + 256).
  { unfold shad, SHB. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. replace (f + 2048) with (f + 256 * 8) by lia. rewrite Z.div_add by lia. lia. }
  rewrite SHF2 in FSH.
  pose proof (l_this_range RT AF Σ m THIS ART0 L_THIS) as TR.
  apply (aevt_evt RT AF PMc MST).
  rewrite (ret_pc_even 0xc546c) by (first [lia | reflexivity]).
  eapply evt_mono; [apply (s2_pro2 sp gp tp (Z_to_bv 64 0xc546c) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' x18 x19 x22 x23 x25 x26 x27 t3' t4' t5' t6' F2 fc2 m2 spa f THIS DOC);
                     [exact F0 | clear - FTOP; unfold USTACK_TOP in FTOP; lia | clear - TR LOR ROOM TOP; unfold STACK_WIN, USTACK_TOP, S2A_STACK, NUMA_STACK, RT_STACK in *; lia | exact W1 | exact W2 | exact MI2] |].
  intros ms3 (y1 & y5 & y6 & y7 & y11 & y12 & y13 & y16 & y17 & y18 & y22 & y23 & y25 & y27 & y28 & y29 & y30 & y31 & m3 & -> & MU3 & WM3 & MI3).

  assert (LOR1 : rt_sp0 RT Σ1 - STACK_WIN <= lo) by (rewrite ESP; exact LOR).
  assert (FP3 : fp_ok RT Σ1 lo [(f, f + 24); (Z.shiftr f 3 + 2147450880, Z.shiftr f 3 + 2147450880 + 164)]).
  { constructor; [right; right; left; exists f, 5%nat; split; [exact INF|]; cbn [fst snd]; change (fs_size 5) with 2048; clear; lia|].
    constructor; [right; right; right; exists f, 5%nat; split; [exact INF|]; cbn [fst snd]; change (fs_size 5) with 2048; rewrite SHF, SHF2; clear; lia| constructor]. }
  pose proof (art_of_munch RT AF Σ1 m2 m3 lo _ ART2 LOR1 FP3 MU3 WM3) as ART1.
  assert (SPL : rt_sp0 RT Σ - STACK_WIN <= bv_unsigned sp) by (clear - LOR ROOM; unfold S2A_STACK, NUMA_STACK, RT_STACK in ROOM; lia).
  assert (PRESALL : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (bv_unsigned a) -> m3 a = m a).
  { intros a Ha.
    destruct (newframe_apart RT AF Σ Σ1 m2 f 5%nat (bv_unsigned sp) _ ART2 EFR ELV ESP SPL Ha) as [N1 N2]. change (fs_size 5) with 2048 in N1, N2. rewrite SHF, SHF2 in N2.
    rewrite (MU3 a) by (cbn [outside]; clear - N1 N2; lia).
    rewrite (PR a) by (eapply aclient_mono; [exact Ha| auto| auto| clear - SPA1; lia]).
    apply MU1. cbn [outside]. destruct (aclient_split_c RT AF Σ m _ _ ART0 Ha) as [H|H]; [clear - H; lia| clear - H LOR; lia]. }
  assert (WMALL : wmono bsegs m m3) by exact (wmono_trans bsegs _ _ _ (wmono_trans bsegs _ _ _ WM1 WM2) WM3).
  assert (AGS : agree_on (fun x => spa <= x < bv_unsigned sp) m1 m3).
  { intros a Ha. rewrite (MU3 a) by (cbn [outside]; clear - Ha FH FSH LOR ROOM SPA1; unfold S2A_STACK, NUMA_STACK, RT_STACK in ROOM; lia).
    apply PR. left. clear - Ha TOP. unfold USTACK_TOP in *. lia. }
  assert (WM13 : wmono bsegs m1 m3) by exact (wmono_trans bsegs _ _ _ WM2 WM3).
  eapply (rw_cells_agree bsegs m1 m3) in FR1; [| eapply agree_sub; [exact AGS| cbn [cells_size csize Nat.add]; intros x Hx; clear - Hx SPA1; lia] | exact WM13].
  eapply (rw_cells_agree bsegs m1 m3) in SAV1; [| eapply agree_sub; [exact AGS| cbn [cells_size csize Nat.add]; intros x Hx; clear - Hx SPA1; lia] | exact WM13].
  eapply (stk_agree bsegs m1 m3) in GAP1; [| eapply agree_sub; [exact AGS| intros x Hx; cbv beta; clear - Hx SPA1; lia] | exact WM13].
  assert (ST3 : stk bsegs m3 lo spa).
  { apply (stk_transport_disjoint bsegs _ m2 m3 lo spa ST2 MU3 WM3). cbn [disjoint_from].
    clear - FH FSH LOR ROOM SPA1. unfold S2A_STACK, NUMA_STACK, RT_STACK in ROOM. lia. }
  assert (FFW3 : wr_at bsegs m3 f 8).
  { apply (wr_at_transport bsegs m2 m3 _ _ (wr_at_sub m2 f 2040 f 8 W1 ltac:(lia) ltac:(lia) ltac:(lia)) WM3). }
  destruct (split_312 m3 spa jf FR1) as (j0 & j8 & j16 & j24 & j32 & j40 & j48 & j56 & j64 & j72 & j80 & j88 & j96 & j104 & j112 & j120 & j128 & j136 & j144 & j152 & j160 & j168 & j176 & j184 & j192 & j200 & j208 & j216 & j224 & j232 & j240 & j248 & j256 & j264 & j272 & j280 & j288 & j296 & j304 & FR3).
  apply (aevt_evt RT AF PMc MST).
  exact (walk_all RT AF RTF PMc FDO MST Σ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo THIS DOC IDX BUF TAPE SBUF OC IA bs idxs iws tcap scap vptr capv nxt dcap p12 p28 p50 ETP HS1 HBOK HLEN HIWS HTC1 HTC2 HSC1 HSC2 HSC8 HIWL HIWM ART0 LOR ROOM TOP SP16 FRL CRD LVL L_THIS L_IDX L_BUF L_TAPE L_SBUF L_OC L_IA A_THIS A_IDX A_TAPE A_SBUF A_OC A_IA HPD FOBJ Σ1 f spa j0 j256 m3 ART1 EFR ELV ESP ECR F64 SPA1 SPA32 docv j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j160 j168 j176 j184 j192 j200 j208 j216 j224 j232 j240 j248 j256 j264 j272 j280 j288 j296 j304 PRESALL WMALL MI3 FR3 SAV1 GAP1 FFW3 ST3 IMPL0 DOCC0 IDXA0 BUF0 OCA0 IAA0 HNUMA HNUMO HROOT SKA SKB SO SA SR
           y1 y5 y6 y7 y11 y12 y13 y16 y17 y18 y22 y23 y25 y27 y28 y29 y30 y31 F2 fc2 FRM2).
Qed.

Theorem stage2a_ok : forall RT, art_facts RT -> rt_contracts_f RT -> numa_stmt RT -> numo_stmt RT -> rootnum_stmt RT ->
  (forall E Q s, env_ok E -> a_shz E -> Inv (e_bs E) (e_idxs E) ObjBegin s -> (depth s + 1 < MAXDEPTH)%Z -> e_tok E (k s) = c_quote -> Z.of_nat (length (e_tws E)) = W s -> Z.of_nat (length (e_sbs E)) = sb s -> (forall hv, exit_k (gapp E [hv; tword t_str (sb s)] []) Q) -> (forall d hv cb, string_ok (e_bs E) (e_idxs E) (k s) d -> Z.of_nat (length cb) = d -> keyend_k (gapp (gapp E [hv; tword t_str (sb s)] []) [] (srec d cb)) Q (k s) (depth s + 1) (W s + 2) (sb s) d ((false, W s) :: scopes s)) -> keya_k E Q s) ->
  (forall E Q s0, env_ok E -> a_shz E -> Inv (e_bs E) (e_idxs E) ObjCont s0 -> e_tok E (k s0) = c_comma -> e_tok E (k s0 + 1) = c_quote -> Z.of_nat (length (e_tws E)) = W s0 -> Z.of_nat (length (e_sbs E)) = sb s0 -> exit_k (gapp E [tword t_str (sb s0)] []) Q -> (forall d cb, string_ok (e_bs E) (e_idxs E) (k s0 + 1) d -> Z.of_nat (length cb) = d -> keyend_k (gapp (gapp E [tword t_str (sb s0)] []) [] (srec d cb)) Q (k s0 + 1) (depth s0) (W s0 + 1) (sb s0) d (scopes s0)) -> keyb_k E Q (mkst (k s0 + 1) (depth s0) (W s0) (sb s0) (scopes s0))) ->
  (forall E Q s, env_ok E -> a_shz E -> (0 <= k s < e_n E)%Z -> (1 <= W s /\ W s + 1 <= e_tcap E)%Z -> (0 <= sb s /\ 3 * sb s <= 5 * e_off E (k s))%Z -> (0 <= depth s <= 1023)%Z -> e_tok E (k s) = c_quote -> Z.of_nat (length (e_tws E)) = W s -> Z.of_nat (length (e_sbs E)) = sb s -> exit_k (gapp E [tword t_str (sb s)] []) Q -> (forall d cb, string_ok (e_bs E) (e_idxs E) (k s) d -> Z.of_nat (length cb) = d -> objcont_k (gapp (gapp E [tword t_str (sb s)] []) [] (srec d cb)) Q (mkst (k s + 1) (depth s) (W s + 1) (sb s + d + 5) (scopes s))) -> objstr_k E Q s) ->
  (forall E Q s, env_ok E -> a_shz E -> Inv (e_bs E) (e_idxs E) ArrValue s -> e_tok E (k s) = c_quote -> Z.of_nat (length (e_tws E)) = W s -> Z.of_nat (length (e_sbs E)) = sb s -> exit_k (gapp E [tword t_str (sb s)] []) Q -> (forall d cb, string_ok (e_bs E) (e_idxs E) (k s) d -> Z.of_nat (length cb) = d -> arrcont_k (gapp (gapp E [tword t_str (sb s)] []) [] (srec d cb)) Q (mkst (k s + 1) (depth s) (W s + 1) (sb s + d + 5) (scopes s))) -> arrstr_k E Q s) ->
  (forall E Q, env_ok E -> a_shz E -> a_cc E -> (e_lo E + 16 <= e_spa E)%Z -> e_tok E 0 = c_quote -> Z.of_nat (length (e_tws E)) = 1%Z -> Z.of_nat (length (e_sbs E)) = 0%Z -> exit_k (gapp E [tword t_str 0%Z] []) Q -> (forall d cb, string_ok (e_bs E) (e_idxs E) 0 d -> Z.of_nat (length cb) = d -> docend_k (gapp (gapp E [tword t_str 0%Z] []) [] (srec d cb)) Q (mkst 1 0 2 (0 + d + 5) [])) -> rootprim_k E Q 0xc75c8) ->
  stage2a_cps RT.
Proof. intros. apply stage2a_of_stage2at. apply stage2at_ok; assumption. Qed.
