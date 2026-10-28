(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF ITreeA StepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg AProto ABase ABytes AQConst AKitQ AMalloc_iface ADepot_iface ARep ARepQ ARepQP ARepQR ARepQD ALayout AHeapP ARepKit ARepFrame
     AKit AKit2 AModelFacts ASecFacts ASec ASecFrame AFreeModel AFreeModelR AFreeRep AFreeGeo AFreeRead F_afree_tail F_afree_icpt F_afree_arep F_afree_arepR
     AFreeStoreK AFreeStore AFreeStoreR AFrameD ASF_kit ASF_read ASF_fast ASF_store ASF_refill ASF_storeR F_afreeC_iface F_adorec AQrecP AFreeC_kit_iface
     ASF_C_iface ASF_storeC.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import LiaTier0U.
Local Ltac Stdlib.micromega.Lia.lia ::= lia_tier0u.
Local Ltac OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib.StoreFast.tlia ::= tlia_u.
Local Ltac OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib.StoreFast.lia3 ::= lia3_u.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6443008 * k <= a.
Proof. intros a n H G2. unfold iclr, AIMG_LO, AIMG_HI in H. destruct H as [? [?|?]]; [exists 0 | exists 1]; lia. Qed.
Local Lemma ablk_int {rc : runConstT} : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6443008 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
Local Ltac band_int H :=
  let k := fresh "k" H in let A := fresh "KA" H in let B := fresh "KB" H in let C := fresh "KC" H in let D := fresh "KD" H in
  let G1 := fresh "G" in let G2 := fresh "G" in
  lazymatch type of H with
  | sclr ?a ?n =>
      assert (G1 : 0 <= a) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia); assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (sclr_int a n H G1 G2) as (k & A & B & C); clear G1 G2
  | iclr ?a ?n =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (iclr_int a n H G2) as (k & A & B & C & D); clear G2
  | 4096 <= ?a /\ (?a + ?n <= _ \/ _ <= ?a) =>      (* [comment removed for export] *)
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (iclr_int a n H G2) as (k & A & B & C & D); clear G2
  | ablk ?lo ?hi => let E := fresh "KE" H in destruct (ablk_int lo hi H) as (k & A & B & E & C & D)
  end.

Section CANSEC1. Context {rc : runConstT}.
(* [comment removed for export] *)
Local Lemma aobj_int : forall a n, aobj a n -> 0x10000 <= n ->
  6443008 <= a /\ a + n <= ATOP /\ exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof.
  intros a n H Hn. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. destruct H as (H1 & H2 & H3 & H4 & H5).
  split; [lia|]. split; [lia|]. destruct H4; [exists 0 | exists 1]; lia.
Qed.
Local Lemma aobj4_int : forall a, aobj a 4096 ->
  4096 <= a /\ a + 4096 <= ATOP
  /\ (exists k, 0 <= k <= 1 /\ a + 4096 <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a)
  /\ (exists j, 0 <= j <= 1 /\ a + 4096 <= 65536 + j * 18446744073709551616 /\ 6443008 * j <= a).
Proof.
  intros a H. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. destruct H as (H1 & H2 & H3 & H4 & H5).
  split; [lia|]. split; [lia|]. split; [destruct H4; [exists 0 | exists 1]; lia | destruct H5 as [_ [H5|H5]]; [exists 0 | exists 1]; lia].
Qed.

(* [comment removed for export] *)
Lemma ek_pre_b_hi : forall ek RNG t nb lst n hm m, ek_pre ek RNG t nb lst n hm m -> 0x10007fff8000 <= ek_b ek lst.
Proof.
  intros ek RNG t nb lst n hm m EK.
  destruct ek as [nx bsz cnt hs cnt24' maxc' csz' stj' | full nx bsz cnt24 maxc csz stj idxw chunks spacebeg b hs0]; cbn [ek_pre ek_b] in *.
  - destruct EK as (NB1 & LB & CNT & BSZ & BSZN & NX & LA & LEN & LJ & L0 & L1 & DTL & DHL & CR' & STS' & RL). exact L0.
  - destruct EK as (FULL & SB & CR & CH & LCH & CNT & NTH & IXS & STS & HB & BJ & SBP & B0 & BL1 & DTB & DTL & DBL & DHB & DHL & RB). exact B0.
Qed.

Lemma qnumR_freeR : forall st ch,
  qnum st -> 0 <= chunk_size ch ->
  let st2 := st_enq st ch in
  qnumR (st_after st2)
  /\ a_qloc_bytes st2 = batches_bytes (a_qloc st2) /\ a_qglob_bytes st2 = a_qglob_bytes st /\ a_qglob st2 = a_qglob st
  /\ Forall (fun b => Q_BATCH_BYTES <= b_size b) (a_qloc st2 ++ a_qglob st2).
Proof.
  intros st ch (N1 & N2 & N3 & N4 & N5) NN st2.
  assert (S2 : a_qloc_bytes st2 = batches_bytes (a_qloc st2) /\ a_qglob_bytes st2 = a_qglob_bytes st /\ a_qglob st2 = a_qglob st
               /\ Forall (fun b => Q_BATCH_BYTES <= b_size b) (a_qloc st2 ++ a_qglob st2)).
  { subst st2. unfold st_enq. destruct (enq_app st ch) as [s|] eqn:E.
    - destruct (enq_app_Some st ch s E) as (l & bl & QL & NF & ->). cbn -[batches_bytes Z.add].
      cbn -[batches_bytes Z.add] in QL |- *. rewrite QL in N1, N3.
      rewrite batches_bytes_app, batches_bytes_cons, batches_bytes_nil in N1 |- *. cbn [b_size].
      split; [lia|]. split; [reflexivity|]. split; [reflexivity|].
      rewrite <- app_assoc in N3 |- *. apply Forall_app in N3. destruct N3 as [F1 F2]. inversion F2; subst.
      apply Forall_app. split; [exact F1|]. constructor; [cbn; lia| assumption].
    - pose proof (enq_new_core ch st) as (_ & G1 & G2 & _ & L1 & L2 & _). rewrite G1, G2, L1, L2. cbn -[batches_bytes Z.add].
      rewrite batches_bytes_app, batches_bytes_cons, batches_bytes_nil. cbn [b_size].
      split; [lia|]. split; [reflexivity|]. split; [reflexivity|].
      rewrite <- app_assoc. apply Forall_app in N3. destruct N3 as [F1 F2].
      apply Forall_app. split; [exact F1|]. constructor; [cbn; unfold Q_BATCH_BYTES; lia| exact F2]. }
  split; [| exact S2]. destruct S2 as (B1 & B2 & B3 & B4).
  unfold st_after, qnumR. destruct (Z.ltb_spec Q_CACHE (a_qloc_bytes st2)) as [LT|GE]; cbn -[batches_bytes Z.add].
  - rewrite B2, B3 in *. rewrite ?batches_bytes_app, ?batches_bytes_nil, ?app_nil_r, ?Z.add_0_r.
    split; [reflexivity|]. split; [lia|].
    apply Forall_app in B4. destruct B4 as [F1 F2]. apply Forall_app. split; [exact F2| exact F1].
  - rewrite B2, B3 in *. repeat split; try assumption.
Qed.

Section S.
Variable DI : ADepotIface.
Variable AFK : alayout -> list ablock -> amem -> Prop.
Hypothesis HL : ahole_laws (AHQ DI ASEC_of AFK).
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI
                                  /\ (snd iv <= 0xcc970 \/ 0xcca30 <= fst iv)
                                  /\ (snd iv <= 0xd0f00 \/ 0x151f30 <= fst iv)
                                  /\ (snd iv <= 0x15f788 \/ 0x15f78c <= fst iv)) CI.
Hypothesis CI_OK2 : Forall (fun iv => snd iv <= AINSTANCE \/ AINSTANCE + 728 <= fst iv) CI.

Theorem store_freeSRC : store_freeSRC_stmt DI AFK CI.
Proof.
  unfold store_freeSRC_stmt. intros L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st LB X Q cs mb ms n b1 ctx lo k24 stj chunks.
  cbv zeta. intros ALO ARNG AR BL HFK PCS RSCS NOTL NQM B1 B13 CTX EAF NK0 NB0 KK0 NIB0 JK0 FSH0 CIN0 POS0 REC1 REC2 EK DK CEIL LO TP ms' PM. unfold AFREE_STACK in LO.
  assert (NEWF : enq_is_app st = false ->
        nth_error (xc_cache (x_cls X K_BATCH_CLASS)) (Z.to_nat (c_count (get_cls st K_BATCH_CLASS) - 1)) = Some k24
     /\ busy_of X K_BATCH_CLASS k24 = None /\ 0 <= k24 < ndist st K_BATCH_CLASS
     /\ ~ In k24 (map qb_slot (q_loc Q ++ q_glob Q))
     /\ junk_at m (abatch_addr L k24) 8192 /\ fill_at m (shad (abatch_addr L k24)) (shlen 8192) 0xfa
     /\ a_cinit st = true /\ 0 < c_count (get_cls st K_BATCH_CLASS)) by (intros _; repeat (split; [assumption|]); exact POS0).
  clear NK0 NB0 KK0 NIB0 JK0 FSH0 CIN0 POS0.
  set (ch := CSec mb ms n) in *.
  set (st2 := st_enq st ch) in *.
  set (ek := ek_of L st X Q n k24 stj chunks) in *.
  set (g := g_of L st Q (ek_delta ek n)) in *.
  (* [comment removed for export] *)
  pose proof AR as AR0. destruct AR0 as (WF & RT & INST & THR & CLS & HQ & HS & HD & HRO & HRT2 & AVL & RT3).
  cbn [ah_quar ah_sec ah_depot AHSm] in HQ, HS, HD. rename HQ into AQ.
  destruct THR as (T0 & T40 & CACHES & CSTATS & STATS0 & UNW).
  pose proof HS as HS0. destruct HS0 as (WFS & ARR0 & SINST & PZ & SHZ).
  pose proof WFS as (_ & WP & WR & WL & WB & WF1 & WD).
  assert (INcs : In ch cs) by (eapply Permutation_in; [apply Permutation_sym; exact PCS| left; reflexivity]).
  pose proof (proj1 (Forall_forall _ _) WF1 ch INcs) as WFch.
  destruct (sec_wf1_facts' L mb ms n WFch) as (MAL & MLO & MCE & MSE & NB & RZ & MSB & MSAL & NMS & NS0 & SCL & NPR & N6).
  pose proof (ablk_lin _ _ MLO) as (ML1 & ML2 & ML3 & ML4). unfold AIMG_HI in ML1. pose proof (ablk_int _ _ MLO) as (kM & KAM & KBM & KEM & KCM & KDM).   (* [comment removed for export] *)
  pose proof SCL as (SC_t & SC_c & SC_r & SC_p & SC_n & SC_st & SC_f & SC_d).
  (* [comment removed for export] *)
  destruct ARR0 as (order & PO & U64 & JK & PER).
  assert (INo : In ch order) by (eapply Permutation_in; [apply Permutation_sym; exact PO| exact INcs]).
  destruct (In_nth_error _ _ INo) as [i NTH].
  assert (IL : (i < length order)%nat) by (apply (proj1 (nth_error_Some order i)); rewrite NTH; discriminate).
  assert (LENO : Z.of_nat (length order) = a_nsec st) by (rewrite (Permutation_length PO); exact WL).
  assert (WF1o : Forall (sec_wf1 L) order).
  { rewrite Forall_forall in WF1 |- *. intros c Hc. apply WF1. eapply Permutation_in; [exact PO| exact Hc]. }
  assert (WDo : sec_disjoint order) by (eapply sec_disjoint_perm; [apply Permutation_sym; exact PO| exact WD]).
  destruct (PER i _ NTH) as (lv0 & LV0 & CH).
  assert (Elv : lv0 = false) by (destruct lv0; [exfalso; apply NOTL; apply (proj1 LV0); reflexivity| reflexivity]). subst lv0.
  pose proof CH as CH0. unfold ch in CH0. cbn [asec_chunk] in CH0.
  destruct CH0 as (H1 & _ & _ & _ & _ & H6 & S1 & _ & S3). unfold SEC_UOFF in H6, S3.
  destruct (junk_split m _ 8 (ms - 6144 - 8) ltac:(replace (8 + (ms - 6144 - 8)) with (ms - 6144) by lia; exact H6) ltac:(lia) ltac:(lia)) as [_ UJ].
  rewrite (granules_rup n) in S3 by (clear -NB; lia).
  pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4).
  pose proof (alayout_ctx L ALO) as (CL1 & CL2 & CL3 & CL4 & CL5).
  pose proof (alayout_depot L ALO) as (DL1 & DL2 & DL3 & DL4 & DL5 & DL6 & DL7 & DL8 & DL9 & DL10).
  pose proof (alayout_stack L ALO) as (STK1 & STK2 & STK3).
  pose proof (alayout_space L ALO) as (SP1 & SP2 & SP3 & SP4).
  pose proof (ao_res L ALO) as RES. pose proof (ao_t L ALO) as OT. pose proof (ao_ctx L ALO) as OC. pose proof (ao_nodes L ALO) as ON. pose proof (ao_store L ALO) as OS.
  pose proof (aobj4_int _ OT) as (_ & _ & [kT TBND] & [jT TIMG]).   (* [comment removed for export] *)
  pose proof (aobj_int _ _ OC ltac:(clear; lia)) as (Ci & _ & [kC CBND]). pose proof (aobj_int _ _ ON ltac:(clear; lia)) as (Ni & _ & [kN NBND]).
  pose proof (aobj_int _ _ OS ltac:(clear; lia)) as (Si & _ & [kS SBND]). pose proof (ao_res_hi L ALO) as RHI.
  unfold aobj in RES, OT, OC, ON, OS. pose proof (ao_space L ALO) as RSP.
  pose proof (ad_t_res L ALO) as D_t_res. pose proof (ad_nodes_res L ALO) as D_n_res. pose proof (ad_store_res L ALO) as D_s_res.
  pose proof (ad_ctx_res L ALO) as D_c_res. pose proof (ad_ctx_nodes L ALO) as D_c_n. pose proof (ad_ctx_store L ALO) as D_c_s.
  unfold adisj in D_t_res, D_n_res, D_s_res, D_c_res, D_c_n, D_c_s.
  assert (D_c_t : al_ctx L + 65536 <= al_t L \/ al_t L + 4096 <= al_ctx L) by (pose proof (ad_t_ctx L ALO) as X1; unfold adisj in X1; clear -X1; lia).
  box DL7. box DL8. box DL9. box DL10. box D_t_res. box D_n_res. box D_s_res. box D_c_res. box D_c_n. box D_c_s. box D_c_t. box CL5.
  word_range sp SPR.
  set (UB := mb + 6144) in *.
  assert (EUB : UB = mb + 6144) by reflexivity.
  assert (EHM : mb + 6128 = UB - 16) by (subst UB; clear; lia).
  assert (UB16' : UB mod 8 = 0) by (subst UB; clear -MAL; Z.div_mod_to_equations; lia).
  assert (MAL8 : mb mod 8 = 0) by (clear -MAL; Z.div_mod_to_equations; lia).
  rewrite EHM in PM, EK, DK.
  replace (mb + 6144) with UB in UJ, S3 by reflexivity.
  pose proof (rup8_facts n ltac:(clear -NB; lia)) as (RUP & RUP8 & RUPS).
  assert (SHGEO : shad UB = shad mb + 768 /\ shlen (rup n 8) <= ms / 8 - 768 /\ 0 < shlen (rup n 8) /\ UB + rup n 8 <= mb + ms
                  /\ 2148256256 <= shad mb /\ shad mb + ms / 8 <= 17594332446720).   (* [comment removed for export] *)
  { subst UB. rewrite !shad_div, RUPS. unfold ASHOFF. pose proof (sec_facts n ltac:(clear -NB; lia) NPR) as (_ & _ & _ & RS1 & _ & NSE & _).
    unfold K_HIGH_MEM in *. pose proof atop_range as AR8. clear -MAL RUP RUP8 RS1 NSE NMS N6 NB ML1 ML3 MCE MSAL AR8. Z.div_mod_to_equations. lia. }
  destruct SHGEO as (SHE & SHL & SHP & UBS & SHLO & SHHI).
  (* [comment removed for export] *)
  pose proof AQ as AQ0. destruct AQ0 as ([QK MX] & [QC ABL] & [GCQ ABG] & (FL & IAS & IAM) & CP & NUM).
  pose proof NUM as NUM0. destruct NUM0 as (NB1 & NB2 & NF & NC & NM).
  pose proof CP as CP0. destruct CP0 as (LN1 & LN2 & _ & _ & ND2 & BSI & _).
  (* [comment removed for export] *)
  assert (CNT : enq_app st ch = None -> 0 < c_count (get_cls st K_BATCH_CLASS)) by (intros _; exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (NEWF EAF))))))))).
  assert (EAPP0 : enq_app st ch = None).
  { destruct (enq_app st ch) as [sx|] eqn:EAPP; [exfalso| reflexivity].
    assert (EA1 : enq_is_app st = true) by (apply (proj2 (enq_is_app_spec st ch)); eexists; exact EAPP). congruence. }
  assert (SB : a_qloc_bytes st2 = a_qloc_bytes st + ek_delta ek n /\ a_qglob_bytes st2 = a_qglob_bytes st /\ a_qglob st2 = a_qglob st).
  { subst st2 ek. unfold st_enq, ek_of. rewrite EAPP0, EAF. cbn [ek_delta]. pose proof (enq_new_core ch st) as (_ & G1' & G2' & _ & _ & L2' & _).
    rewrite G1', G2', L2'. unfold ch. cbn [chunk_size]. unfold Q_BATCH_BYTES. repeat split; try reflexivity. clear; lia. }
  destruct SB as (SB1 & SB2 & SB3).
  assert (ED0 : 0 <= ek_delta ek n /\ ek_delta ek n <= n + 8192) by (subst ek; unfold ek_of; destruct (enq_is_app st); cbn [ek_delta]; clear -NB; lia).
  assert (EBK : ek_b ek (qlast L (q_loc Q)) = qlast L (q_loc Q) \/ (enq_is_app st = false /\ ek_b ek (qlast L (q_loc Q)) = abatch_addr L k24)).
  { subst ek. unfold ek_of. destruct (enq_is_app st) eqn:EAx; cbn [ek_b]; [left; reflexivity| right; split; reflexivity]. }
  assert (EBB : ek_b ek (qlast L (q_loc Q)) = qlast L (q_loc Q)
      \/ exists kk, ek_b ek (qlast L (q_loc Q)) = abatch_addr L kk /\ 0 <= kk < ndist st K_BATCH_CLASS /\ ~ In kk (map qb_slot (q_loc Q ++ q_glob Q))).
  { destruct EBK as [E|[EAx E]]; [left; exact E| right; exists k24]. destruct (NEWF EAx) as (NK & NBk & KK & NIB & _). split; [exact E|]. split; [exact KK| exact NIB]. }
  assert (HMSEP : forall kk, 0 <= kk < ndist st K_BATCH_CLASS -> UB - 16 + 24 <= abatch_addr L kk \/ abatch_addr L kk + 8192 <= UB - 16).
  { intros kk KK. pose proof WF as WF0. destruct WF0 as (_ & _ & _ & _ & _ & PERC & _).
    destruct (PERC K_BATCH_CLASS (K24)) as (Q1 & Q2 & _).
    pose proof (slot_in_region L st K_BATCH_CLASS kk ltac:(rewrite size_of_class_24; lia) (proj1 Q1) KK) as (P5 & P4 & _).
    rewrite size_of_class_24 in P4. subst UB. unfold abatch_addr, aregion, K_REGION, K_FREEARR_OFF, K_BATCH_CLASS in *.
    clear -P5 P4 Q1 Q2 RSP SC_r MSB. lia. }
  assert (GL : g_lst g = qlast L (q_glob Q)) by reflexivity.
  assert (GLST : dk_glst g (qlast L (q_loc Q)) = (if Q_CACHE <? a_qloc_bytes st + ek_delta ek n then qlast L (q_glob Q) else qlast L (q_loc Q))) by reflexivity.
  assert (REC1' : Q_CACHE < a_qloc_bytes st + ek_delta ek n) by (rewrite <- SB1; exact REC1).
  set (lst := qlast L (q_loc Q)) in *. set (eb := ek_b ek lst) in *. set (gl := dk_glst g lst) in *. set (gq := shlen (rup n 8)) in *.
  (* [comment removed for export] *)
  assert (BGEO : forall q, In q (q_loc Q ++ q_glob Q) ->
      aregion L K_BATCH_CLASS <= abatch_addr L (qb_slot q) /\ abatch_addr L (qb_slot q) + 8192 <= aregion L K_BATCH_CLASS + c_allocated_user (get_cls st K_BATCH_CLASS)
      /\ al_res L + 4096 <= abatch_addr L (qb_slot q) /\ abatch_addr L (qb_slot q) + 8192 <= al_res L + 137439023104).
  { intros q Hq. pose proof (slot_geo L st X K_BATCH_CLASS (qb_slot q) ALO WF (K24) (bslot_range L st X Q WF CP q Hq)) as (_ & _ & _ & Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & _).
    rewrite size_of_class_24 in Q2, Q6. unfold abatch_addr. unfold K_SPACE_SIZE in Q6. change (2^37) with 137438953472 in Q6.
    generalize Q1 Q2 Q5 Q6 RSP; clear; intros. lia. }
  assert (A24 : c_allocated_user (get_cls st K_BATCH_CLASS) <= K_FREEARR_OFF).
  { destruct WF as (_ & _ & _ & _ & _ & PERC & _). destruct (PERC K_BATCH_CLASS (K24)) as (Q1 & Q2 & _). lia. }
  assert (LSTF : lst = 0 \/ ((exists q, In q (q_loc Q) /\ lst = abatch_addr L (qb_slot q))
                            /\ aregion L K_BATCH_CLASS <= lst /\ lst + 8192 <= aregion L K_BATCH_CLASS + c_allocated_user (get_cls st K_BATCH_CLASS)
                            /\ al_res L + 4096 <= lst /\ lst + 8192 <= al_res L + 137439023104)).
  { subst lst. destruct (qlast_cases L (q_loc Q)) as [E0|(q & Hq & Eq)]; [left; exact E0| right].
    assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; left; exact Hq).
    rewrite Eq. split; [exists q; split; [exact Hq| reflexivity]|]. exact (BGEO q INq). }
  assert (GDR : g_drain g = (Q_CACHE <? a_qloc_bytes st + ek_delta ek n)) by reflexivity.
  assert (GLF : (g_drain g = false /\ gl = lst)
             \/ (g_drain g = true /\ gl = qlast L (q_glob Q)
                 /\ (gl = 0 \/ ((exists q, In q (q_glob Q) /\ gl = abatch_addr L (qb_slot q))
                            /\ aregion L K_BATCH_CLASS <= gl /\ gl + 8192 <= aregion L K_BATCH_CLASS + c_allocated_user (get_cls st K_BATCH_CLASS)
                            /\ al_res L + 4096 <= gl /\ gl + 8192 <= al_res L + 137439023104)))).
  { subst gl. rewrite GLST, GDR. destruct (Q_CACHE <? a_qloc_bytes st + ek_delta ek n); [right| left; split; reflexivity].
    split; [reflexivity|]. split; [reflexivity|].
    destruct (qlast_cases L (q_glob Q)) as [E0|(q & Hq & Eq)]; [left; exact E0| right].
    assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; right; exact Hq).
    rewrite Eq. split; [exists q; split; [exact Hq| reflexivity]|]. exact (BGEO q INq). }
  assert (EBF : eb = 0 \/ (aregion L K_BATCH_CLASS <= eb /\ eb + 8192 <= aregion L K_BATCH_CLASS + c_allocated_user (get_cls st K_BATCH_CLASS)
                            /\ al_res L + 4096 <= eb /\ eb + 8192 <= al_res L + 137439023104)).
  { subst eb. destruct EBK as [E|[EAx E]].
    - rewrite E. destruct LSTF as [Z0|(_ & FF)]; [left; exact Z0| right; exact FF].
    - right. rewrite E. destruct (NEWF EAx) as (_ & _ & KK & _). pose proof (slot_geo L st X K_BATCH_CLASS k24 ALO WF (K24) KK) as (_ & _ & _ & Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & _).
      rewrite size_of_class_24 in Q2, Q6. unfold abatch_addr. unfold K_SPACE_SIZE in Q6. change (2^37) with 137438953472 in Q6.
      generalize Q1 Q2 Q5 Q6 RSP; clear; intros. lia. }
  (* [comment removed for export] *)
  unfold free_torec_post in PM. cbv zeta in PM.
  destruct PM as (id & t0' & t1' & t2' & xs0 & xs1 & xs2 & xs3 & xs4 & xs5 & xs6 & ps0 & ps1 & ps2 & ps3 & ps4 & ps5 & spv & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6'
                  & m' & sj' & csA & csT & junk2
                  & -> & MU & WM & MI' & ST' & IDR & FRP & FRA & SZA & FRT & SZT & FRS & HDR' & FC' & SH' & QC' & EKP & DKP & STATS' & LSJ' & UW' & FL' & IAS' & IAM' & DEP').
  fold lst in MU, QC', EKP, DKP, EBK. fold eb in MU, EBK. fold gl in MU. fold gq in MU, SH'.
  replace (UB - 16 + 16) with UB in MU, FC', SH' by (clear; lia).
  assert (ELST : lst = qlast L (q_loc Q)) by reflexivity. assert (EEB : eb = ek_b ek lst) by reflexivity.
  assert (EGL : gl = dk_glst g lst) by reflexivity. assert (EGQ : gq = shlen (rup n 8)) by reflexivity.
  clearbody lst eb gl gq.
  (* [comment removed for export] *)
  assert (EBNZ : 0x10007fff8000 <= eb) by (rewrite EEB; exact (ek_pre_b_hi _ _ _ _ _ _ _ _ EK)).   (* [comment removed for export] *)
  replace (eb + 8192) with (eb + qsz eb) in MU by (rewrite (qsz_pos eb) by (clear -EBNZ; lia); reflexivity).   (* [comment removed for export] *)
  assert (MUn : munch (WfS (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) m m').
  { eapply munch_weaken; [| exact MU]. solve_sub_fp sp. }
  clear MU.
  assert (KF : kfactsS (bv_unsigned sp) (al_t L) mb ms UB gq (al_nodes L) (al_store L) (al_res L) (al_ctx L) lo lst eb gl).
  { unfold kfactsS. unfold K_HIGH_MEM in *.
    assert (GQ1 : 1 <= gq) by (clear -SHP EGQ; lia).
    generalize CEIL LO OT OC ON OS RES RHI RSP MLO ML1 ML3 MCE EUB UBS NB RUP SC_t SC_r SC_n SC_st SHE SHL SHLO SHHI GQ1 EGQ LSTF EBF GLF EBNZ. clear. intros.
    rewrite ?EGQ in SHL. unfold iclr, AIMG_LO, AIMG_HI in *.   (* [comment removed for export] *)
    (destruct LSTF as [Z0|(_ & FF)]; [rewrite (qsz_eq0 lst Z0) | rewrite (qsz_pos lst) by (atop_facts; lia)]);
    (destruct EBF as [Z1|FF1]; [exfalso; atop_facts; lia|]); rewrite (qsz_pos eb) by (atop_facts; lia); destruct GLF as [[_ Z2]|(_ & _ & [Z2|(_ & FF2)])];
    repeat match goal with H : _ /\ _ |- _ => destruct H end; repeat split; first [assumption | lia]. }
  pose proof (KS_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Kimg.
  pose proof (KS_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Klow.
  pose proof (KS_hi _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Khi.
  pose proof (KS_shad _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Kshad.
  pose proof (KS_ctx _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF (unbxF D_c_t) (unbxF D_c_res) (unbxF D_c_n) (unbxF D_c_s) SC_c) as Kctx.
  pose proof (KS_t _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF (unbxF D_t_res) (unbxF DL7) (unbxF DL8)) as Kt.
  pose proof (KS_res _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF (unbxF D_t_res) (unbxF D_n_res) (unbxF D_s_res)) as Kres.
  pose proof (KS_obj _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Kobj.
  pose proof (KS_chunk _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Kchunk.
  (* [comment removed for export] *)
  assert (SC : same_core st (st_after st2) /\ a_cinit (st_after st2) = a_cinit st /\ a_live (st_after st2) = a_live st /\ a_next (st_after st2) = a_next st
               /\ a_space_beg (st_after st2) = a_space_beg st /\ a_ptr_array (st_after st2) = a_ptr_array st
               /\ (enq_is_app st = true -> a_cls (st_after st2) = a_cls st)
               /\ (enq_is_app st = false -> a_cls (st_after st2) = <[ K_BATCH_CLASS := cls_set_count (c_count (get_cls st K_BATCH_CLASS) - 1) (get_cls st K_BATCH_CLASS) ]> (a_cls st))).
  { pose proof (st_after_core st2) as [SC2 CL2'].
    assert (SC1 : same_core st st2 /\ (enq_is_app st = true -> a_cls st2 = a_cls st) /\ (enq_is_app st = false -> a_cls st2 = <[ K_BATCH_CLASS := cls_set_count (c_count (get_cls st K_BATCH_CLASS) - 1) (get_cls st K_BATCH_CLASS) ]> (a_cls st))).
    { subst st2. unfold st_enq. destruct (enq_app st ch) as [sx|] eqn:EAPP.
      - destruct (enq_app_Some st _ sx EAPP) as (l & bl & QL & NFz & ->). split; [repeat split; intros; reflexivity|].
        split; [intros _; reflexivity|]. intros EAx. exfalso.
        assert (EA1 : enq_is_app st = true) by (apply (proj2 (enq_is_app_spec st ch)); eexists; exact EAPP).
        congruence.
      - pose proof (enq_new_core ch st) as (C1 & _ & _ & _ & _ & _ & C7). split; [exact C1|].
        split; [| intros _; exact C7]. intros EAx. exfalso.
        assert (EA1 : enq_is_app st = true) by exact EAx. destruct (proj1 (enq_is_app_spec st ch) EA1) as [s Hs]. congruence. }
    destruct SC1 as (SC1 & CLa & CLb). pose proof (same_core_trans _ _ _ SC1 SC2) as SC3.
    pose proof SC3 as SC0. destruct SC0 as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & _).
    split; [exact SC3|]. split; [exact F3|]. split; [exact F1|]. split; [exact F2|]. split; [exact F4|]. split; [exact F5|].
    split; [intros EAx; rewrite CL2'; exact (CLa EAx)| intros EAx; rewrite CL2'; exact (CLb EAx)]. }
  destruct SC as (SC & ECIN & ELIVE & ENEXT & ESB & EPA & CLa & CLb).
  pose proof SC as SC0. destruct SC0 as (_ & _ & _ & _ & _ & ENRES & ENSEC & GCo & M24a & M24b & M24c & M24d).
  set (st' := st_after st2) in *.
  set (X' := xfreeS X (enq_is_app st) k24).
  assert (GC24 : get_cls st' K_BATCH_CLASS = (if enq_is_app st then get_cls st K_BATCH_CLASS else cls_set_count (c_count (get_cls st K_BATCH_CLASS) - 1) (get_cls st K_BATCH_CLASS))).
  { unfold get_cls at 1. destruct (enq_is_app st) eqn:EAx; [rewrite (CLa eq_refl); reflexivity| rewrite (CLb eq_refl), lookup_insert_eq; reflexivity]. }
  assert (GCo' : forall c', c' <> K_BATCH_CLASS -> get_cls st' c' = get_cls st c') by (intros c' NE; rewrite (GCo c' NE); reflexivity).
  assert (NDS : forall c', ndist st' c' = ndist st c').
  { intros c'. unfold ndist. destruct (Z.eq_dec c' K_BATCH_CLASS) as [->|NE]; [rewrite M24b; reflexivity| rewrite (GCo' c' NE); reflexivity]. }
  assert (MC' : forall c', max_count st' c' = max_count st c') by (intros c'; unfold max_count; rewrite ECIN; reflexivity).
  (* [comment removed for export] *)
  assert (WF' : awf L st' X').
  { subst X'. unfold xfreeS. destruct (enq_is_app st) eqn:EAx.
    - exfalso. clear -EAF EAx. congruence.
    - destruct (NEWF eq_refl) as (NK & NBk & KK & NIB & JKb & FSH & CIN & POS).
      apply (awf_xbatch L st X k24 (c_count (get_cls st K_BATCH_CLASS)) WF eq_refl POS NK).
      + exact ESB. + exact EPA. + exact ECIN. + exact ELIVE. + exact ENEXT.
      + intros c' NE. rewrite (GCo' c' NE). reflexivity.
      + rewrite GC24. reflexivity. }
  (* [comment removed for export] *)
  assert (RT' : arep_rt L m').
  { eapply arep_rt_frame; [exact MUn | exact WM | exact RT |]. unfold rt_hulls, ATP88, ATSD.
    repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia] |]). apply Forall_nil. }
  assert (INST' : ainstance L st' m').
  { eapply ainstance_frame; [exact MUn | exact WM | exact INST | exact ENRES | exact ENSEC | | |]; apply Kimg; clear; unfold AINSTANCE, AIMG_HI; lia. }
  assert (HRO' : arelro m') by (eapply arelro_frame; [exact MUn | exact HRO | apply Kimg; clear; unfold ARELRO_LO, ARELRO_HI, AIMG_HI; lia]).
  assert (HRT2' : arep_rt2 m') by (eapply arep_rt2_frame; [exact MUn | exact WM | exact HRT2 | | |]; apply Kimg; clear; unfold AIMG_HI; lia).
  assert (RT3' : arep_rt3 m') by (eapply arep_rt3_frame; [exact MUn | exact WM | exact RT3 |]; unfold rt3_hulls; repeat (apply Forall_cons; [cbn [fst snd]; apply Kimg; clear; unfold AIMG_HI; lia|]); apply Forall_nil).
  (* [comment removed for export] *)
  assert (THR' : athread L st' X' m').
  { unfold athread. split; [| split; [| split; [| split; [| split]]]].
    - eapply cells_frame; [exact T0 | exact MUn | exact WM |]. cbn [cells_size csize Nat.add]. apply Kt; clear; lia.
    - eapply cells_frame; [exact T40 | exact MUn | exact WM |]. cbn [cells_size csize Nat.add]. apply Kt; clear; lia.
    - intros c' Hc'. destruct (Z.eq_dec c' K_BATCH_CLASS) as [->|NE].
      + destruct (CACHES K_BATCH_CLASS Hc') as [tail (CR & CHc & LCH)]. unfold acache_cells. cbv zeta.
        rewrite GC24, MC', ECIN. subst X'. rewrite xfreeS_cache, Z.eqb_refl, andb_true_r.
        replace (acache_addr L K_BATCH_CLASS) with (al_t L + 2128) in CR, CHc |- * by (unfold acache_addr, K_BATCH_CLASS; clear; lia).
        subst ek. unfold ek_of in EKP. destruct (enq_is_app st) eqn:EAx; cbn [ek_post negb] in EKP |- *.
        * destruct EKP as (_ & _ & _ & CR' & _). exists tail. split; [exact CR'|]. split; [| exact LCH].
          eapply u32arr_frame; [exact CHc | exact MUn | exact WM |]. rewrite length_app, length_map. apply Kt; clear -LCH; lia.
        * destruct EKP as (CR' & _). destruct (NEWF eq_refl) as (NK & NBk & KK & NIB & JKb & FSH & CIN & POS).
          cbn [c_count cls_set_count]. exists (Z_to_bv 64 (acompact K_BATCH_CLASS k24) :: tail).
          pose proof (cache24_split L st X k24 (c_count (get_cls st K_BATCH_CLASS)) WF eq_refl POS NK) as [CACHE LRL].
          split; [exact CR'|]. split.
          -- eapply u32arr_frame; [| exact MUn | exact WM |].
             ++ rewrite CACHE, map_app in CHc. cbn [map] in CHc. rewrite <- app_assoc in CHc. cbn [app] in CHc. exact CHc.
             ++ rewrite length_app, length_map. cbn [length].
                replace (length (removelast (xc_cache (x_cls X K_BATCH_CLASS))) + Datatypes.S (length tail))%nat with 16%nat
                  by (rewrite CACHE, length_app in LCH; cbn [length] in LCH; clear -LCH; lia).
                apply Kt; clear; lia.
          -- cbn [length]. rewrite CACHE, length_app in LCH. cbn [length] in LCH. clear -LCH. lia.
      + eapply acache_cells_frame; [exact MUn | exact WM | exact (CACHES c' Hc') | rewrite (GCo' c' NE); reflexivity | exact ECIN | |].
        * subst X'. rewrite xfreeS_cache. destruct (Z.eqb_spec c' K_BATCH_CLASS) as [E|_]; [exfalso; exact (NE E)|]. rewrite andb_false_r. reflexivity.
        * unfold acache_addr. unfold K_NUM_CLASSES, K_BATCH_CLASS in *. apply Kt; clear -Hc' NE; lia.
    - apply (junk_merge m' (al_t L + 2768) 16 16); [| | clear; lia | clear; lia].
      + eapply junk_frame; [exact (proj1 (junk_split m (al_t L + 2768) 16 16 CSTATS ltac:(clear; lia) ltac:(clear; lia))) | exact MUn | exact WM | intros _; apply Kt; clear; lia].
      + apply (junk_merge m' (al_t L + 2768 + 16) 8 8); [| | clear; lia | clear; lia].
        * replace (al_t L + 2768 + 16) with (al_t L + 2784) by (clear; lia).
          assert (STJ' : exists w : word, rw_cells bsegs m' (al_t L + 2784) [C8 w]).
          { subst ek. unfold ek_of in EKP. destruct (enq_is_app st); cbn [ek_post] in EKP.
            - destruct EKP as (_ & _ & _ & _ & STS'). exists stj. exact STS'.
            - destruct EKP as (_ & STS' & _). exact STS'. }
          destruct STJ' as [w STS']. pose proof (junk_of_cells m' _ _ STS') as J. cbn in J. exact J.
        * replace (al_t L + 2768 + 16 + 8) with (al_t L + 2792) by (clear; lia).
          eapply junk_frame; [| exact MUn | exact WM | intros _; apply Kt; clear; lia].
          pose proof (junk_split m (al_t L + 2768) 16 16 CSTATS ltac:(clear; lia) ltac:(clear; lia)) as [_ CSb].
          pose proof (junk_split m (al_t L + 2768 + 16) 8 8 CSb ltac:(clear; lia) ltac:(clear; lia)) as [_ CSc].
          replace (al_t L + 2768 + 16 + 8) with (al_t L + 2792) in CSc by (clear; lia). exact CSc.
    - exists sj'. split; [exact STATS' | exact LSJ'].
    - exact UW'. }
  (* [comment removed for export] *)
  assert (BDIS : forall q1 q2, In q1 (q_loc Q ++ q_glob Q) -> In q2 (q_loc Q ++ q_glob Q) ->
      abatch_addr L (qb_slot q1) = abatch_addr L (qb_slot q2) \/ abatch_addr L (qb_slot q1) + 8192 <= abatch_addr L (qb_slot q2) \/ abatch_addr L (qb_slot q2) + 8192 <= abatch_addr L (qb_slot q1)).
  { intros q1 q2 Hq1 Hq2. destruct (Z.eq_dec (qb_slot q1) (qb_slot q2)) as [E|NE]; [left; rewrite E; reflexivity| right].
    pose proof (slots_disjoint L K_BATCH_CLASS (qb_slot q1) (qb_slot q2) ltac:(pose proof (bslot_range L st X Q WF CP q1 Hq1); lia)
                  ltac:(pose proof (bslot_range L st X Q WF CP q2 Hq2); lia) NE ltac:(rewrite size_of_class_24; lia)) as D.
    rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
  assert (KDIS : forall q, In q (q_loc Q ++ q_glob Q) -> enq_is_app st = false ->
      abatch_addr L k24 + 8192 <= abatch_addr L (qb_slot q) \/ abatch_addr L (qb_slot q) + 8192 <= abatch_addr L k24).
  { intros q Hq EAx. destruct (NEWF EAx) as (NK & NBk & KK & NIB & _).
    assert (NE : k24 <> qb_slot q) by (intros ->; apply NIB; apply in_map; exact Hq).
    pose proof (slots_disjoint L K_BATCH_CLASS k24 (qb_slot q) ltac:(lia) ltac:(pose proof (bslot_range L st X Q WF CP q Hq); lia) NE ltac:(rewrite size_of_class_24; lia)) as D.
    rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
  (* [comment removed for export] *)
  assert (RC : forall c1 c2, c1 < c2 -> aregion L c1 + K_REGION <= aregion L c2) by (intros; apply regions_sep; assumption).
  assert (CLS' : forall c'', 1 <= c'' < K_NUM_CLASSES ->
      aregion_cells L st' m' c'' /\ afreearray L st' X' m' c'' /\ aslots L st' X' m' c'' /\ aslot_shadow L st' X' m' c'').
  { intros c'' Hc''. destruct (CLS c'' Hc'') as (REG & FARR & SLOTS & SHADOW).
    pose proof WF as WF0. destruct WF0 as (_ & _ & SAL & _ & _ & PERC & _).
    destruct (PERC c'' Hc'') as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & QLENF & QLENC & QCNTB & QND & QRANGE).
    pose proof (size_of_class_facts c'' Hc'') as [QS QS16].
    pose proof (aregion_mod L c'' SAL) as RM''.
    assert (EC1 : c_num_freed (get_cls st' c'') = c_num_freed (get_cls st c'')) by (destruct (Z.eq_dec c'' K_BATCH_CLASS) as [->|NE]; [exact M24c| rewrite (GCo' c'' NE); reflexivity]).
    assert (EC2 : c_mapped_free_array (get_cls st' c'') = c_mapped_free_array (get_cls st c'')) by (destruct (Z.eq_dec c'' K_BATCH_CLASS) as [->|NE]; [exact M24d| rewrite (GCo' c'' NE); reflexivity]).
    assert (EC3 : c_allocated_user (get_cls st' c'') = c_allocated_user (get_cls st c'')) by (destruct (Z.eq_dec c'' K_BATCH_CLASS) as [->|NE]; [exact M24b| rewrite (GCo' c'' NE); reflexivity]).
    assert (EC4 : c_mapped_user (get_cls st' c'') = c_mapped_user (get_cls st c'')) by (destruct (Z.eq_dec c'' K_BATCH_CLASS) as [->|NE]; [exact M24a| rewrite (GCo' c'' NE); reflexivity]).
    unfold K_NUM_CLASSES in Hc''.
    assert (RI : al_res L <= aregion L c'' /\ aregion L c'' + K_REGION <= al_space_beg L + K_SPACE_SIZE
                 /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104 /\ al_res L + 4096 <= aregion L c'').
    { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc'' RSP. lia. }
    destruct RI as (RI1 & RI2 & RI3 & RI4).
    split; [| split; [| split]].
    - eapply aregion_cells_frame; [exact MUn | exact WM | exact REG | exact EC1 | exact EC2 | exact EC3 | exact EC4 |].
      unfold aregion_info, ARI_STRIDE, K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
      apply Kres; try (clear -Hc'' RSP; lia).
      + destruct LSTF as [Z0|(_ & F1 & F2 & F3 & F4)]; [rewrite Z0; right; clear -RSP RES RHI Hc''; lia| right].
        clear -F2 A24 Hc''. unfold aregion, K_REGION, K_BATCH_CLASS, K_FREEARR_OFF in *. change (2^32) with 4294967296 in *. lia.
      + destruct EBF as [Z0|(F1 & F2 & F3 & F4)]; [rewrite Z0; right; clear -RSP RES RHI Hc''; lia| right].
        clear -F2 A24 Hc''. unfold aregion, K_REGION, K_BATCH_CLASS, K_FREEARR_OFF in *. change (2^32) with 4294967296 in *. lia.
      + assert (GLR : gl = 0 \/ gl + 8192 <= aregion L K_BATCH_CLASS + c_allocated_user (get_cls st K_BATCH_CLASS)).
        { destruct GLF as [[_ ->]|(_ & _ & [Z0|(_ & F1 & F2 & _)])]; [| left; exact Z0| right; exact F2].
          destruct LSTF as [Z0|(_ & F1 & F2 & _)]; [left; exact Z0| right; exact F2]. }
        destruct GLR as [Z0|F2]; [rewrite Z0; right; clear -RSP RES RHI Hc''; lia| right].
        clear -F2 A24 Hc''. unfold aregion, K_REGION, K_BATCH_CLASS, K_FREEARR_OFF in *. change (2^32) with 4294967296 in *. lia.
    - eapply afreearray_frame; [exact MUn | exact WM | exact FARR | exact EC1 | exact EC2 | | exact QLENF | exact Q5 | | clear -Q6; lia |].
      + subst X'. apply xfreeS_free.
      + assert (FA1 : aregion L c'' + K_FREEARR_OFF <= afreearr L c'' /\ afreearr L c'' + c_mapped_free_array (get_cls st c'') <= aregion L c'' + K_REGION).
        { unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q6. lia. }
        destruct FA1 as [FA1 FA2].
        apply Kres; [clear -RI1 FA1; unfold K_FREEARR_OFF in *; lia | clear -RI2 RI3 FA2; lia | clear -Q5 Q6; lia | | |].
        * destruct LSTF as [Z0|(_ & F1 & F2 & _)]; [rewrite Z0; right; clear -RI4 FA1 RES RHI; unfold K_FREEARR_OFF in *; lia|].
          exact (farr_vs_user L c'' K_BATCH_CLASS _ _ lst 8192 F1 ltac:(clear -F2 A24; lia) FA1 FA2).
        * destruct EBF as [Z0|(F1 & F2 & _)]; [rewrite Z0; right; clear -RI4 FA1 RES RHI; unfold K_FREEARR_OFF in *; lia|].
          exact (farr_vs_user L c'' K_BATCH_CLASS _ _ eb 8192 F1 ltac:(clear -F2 A24; lia) FA1 FA2).
        * assert (GLR : gl = 0 \/ (aregion L K_BATCH_CLASS <= gl /\ gl + 8192 <= aregion L K_BATCH_CLASS + c_allocated_user (get_cls st K_BATCH_CLASS))).
          { destruct GLF as [[_ ->]|(_ & _ & [Z0|(_ & F1 & F2 & _)])]; [| left; exact Z0| right; split; [exact F1| exact F2]].
            destruct LSTF as [Z0|(_ & F1 & F2 & _)]; [left; exact Z0| right; split; [exact F1| exact F2]]. }
          destruct GLR as [Z0|[F1 F2]]; [rewrite Z0; right; clear -RI4 FA1 RES RHI; unfold K_FREEARR_OFF in *; lia|].
          pose proof (farr_vs_user L c'' K_BATCH_CLASS _ _ gl 8192 F1 ltac:(clear -F2 A24; lia) FA1 FA2) as D. clear -D. lia.
      + assert (FA1 : aregion L c'' + K_FREEARR_OFF <= afreearr L c'' /\ afreearr L c'' + c_mapped_free_array (get_cls st c'') <= aregion L c'' + K_REGION).
        { unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q6. lia. }
        destruct FA1 as [FA1 FA2].
        apply Kshad.
        * rewrite shad_div. unfold ASHOFF, AIMG_HI, K_FREEARR_OFF in *. clear -RI1 FA1 RES RHI. Z.div_mod_to_equations. lia.
        * rewrite shad_div, shlen_div. unfold ASHOFF, K_SPACE_SIZE in *. clear -RI2 RI3 FA2 RES RHI. Z.div_mod_to_equations. lia.
        * apply shlen_nonneg. clear -Q5 Q6. lia.
        * assert (AM : afreearr L c'' mod 8 = 0) by (unfold afreearr, K_FREEARR_OFF; clear -RM''; Z.div_mod_to_equations; lia).
          rewrite SHE. destruct SC_r as [D|D].
          -- right. pose proof (shad_sep _ _ _ D MAL8) as HH. rewrite shlen_div in HH.
             pose proof (shad_mono (al_res L) (afreearr L c'') ltac:(clear -RI1 FA1; unfold K_FREEARR_OFF in *; lia)) as MM. clear -HH MM SHL. lia.
          -- left. apply (Z.le_trans _ (shad mb)); [apply shad_sep; [clear -D RI2 RI3 FA2; lia| exact AM] | clear; lia].
    - (* [comment removed for export] *)
      eapply (aslots_update_gen L _ m m' MUn WM st st' X X' c''); [exact SLOTS | apply NDS | exact EC3 | exact EC4 | |].
      + intros k'' Hk''.
        pose proof (slot_geo L st X c'' k'' ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) Hk'') as (T16 & TM16 & TAL & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & _).
        assert (D2 : (enq_is_app st = false /\ c'' = K_BATCH_CLASS /\ k'' = k24) \/ (enq_is_app st = true \/ c'' <> K_BATCH_CLASS \/ k'' <> k24))
          by (destruct (enq_is_app st); clear; lia).
        destruct D2 as [(EAx & E24 & EK24)|NE2].
        * (* [comment removed for export] *)
          subst c'' k''. right.
          subst X'. rewrite (busy_of_xfreeS X (enq_is_app st) k24 K_BATCH_CLASS k24), EAx. cbn [negb andb]. rewrite !Z.eqb_refl. cbn [andb].
          unfold aslot_busy, bbatch. cbn [xb_st xb_class xb_slot]. unfold xb_alloc. cbn [xb_class xb_slot]. rewrite size_of_class_24.
          subst ek. unfold ek_of in EKP. rewrite EAx in EKP. cbn [ek_post] in EKP. destruct EKP as (_ & _ & BC & BA & [bsb BJ] & _).
          fold (abatch_addr L k24) in BC, BA, BJ |- *. change (aslot_addr L K_BATCH_CLASS k24) with (abatch_addr L k24).
          replace 8192 with (24 + (8 * Z.of_nat (length [Z_to_bv 64 (UB - 16)]) + (8192 - 24 - 8 * 1))) by (cbn; lia).
          apply junk_merge; [| | clear; lia| cbn; clear; lia].
          -- pose proof (junk_of_cells m' _ _ BC) as J. cbn in J. exact J.
          -- apply junk_merge; [apply junk_of_u64arr; exact BA | | cbn; clear; lia | clear; lia].
             cbn [length Z.of_nat Pos.of_succ_nat]. eexists. exact BJ.
        * assert (T1 : negb (enq_is_app st) && (K_BATCH_CLASS =? c'') && (k24 =? k'') = false).
          { destruct (enq_is_app st); cbn [negb andb]; [reflexivity|].
            destruct (Z.eqb_spec K_BATCH_CLASS c'') as [E|]; [| reflexivity]. destruct (Z.eqb_spec k24 k'') as [E'|]; [| reflexivity]. exfalso.
            destruct NE2 as [NE|[NE|NE]]; [discriminate| apply NE; symmetry; exact E| apply NE; symmetry; exact E']. }
          assert (BX : busy_of X' c'' k'' = busy_of X c'' k'').
          { subst X'. rewrite (busy_of_xfreeS X (enq_is_app st) k24 c'' k''), T1. reflexivity. }
          (* [comment removed for export] *)
          assert (BQ : forall q, In q (q_loc Q ++ q_glob Q) -> c'' = K_BATCH_CLASS -> aslot_addr L c'' k'' = abatch_addr L (qb_slot q) ->
              exists yq, busy_of X c'' k'' = Some yq /\ xb_st yq = BBatch /\ xb_class yq = K_BATCH_CLASS /\ xb_slot yq = k''
                         /\ junk_at m (abatch_addr L (qb_slot q)) 8192 /\ k'' = qb_slot q).
          { intros q Hq -> EQA. destruct (bslot_busy L st X Q CP q Hq) as (yq & Hyq & Syq & Cyq & Kyq).
            assert (EK' : k'' = qb_slot q) by (unfold abatch_addr, aslot_addr in EQA; rewrite size_of_class_24 in EQA; clear -EQA; lia). subst k''.
            exists yq. pose proof (busy_of_In_nodup L st X yq WF Hyq) as BY. rewrite Cyq, Kyq in BY.
            split; [exact BY|]. split; [exact Syq|]. split; [exact Cyq|]. split; [exact Kyq|]. split; [| reflexivity].
            destruct SLOTS as [SLK _]. specialize (SLK (qb_slot q) Hk''). rewrite BY in SLK. unfold aslot_busy in SLK. rewrite Syq in SLK.
            unfold xb_alloc in SLK. rewrite Cyq, Kyq, size_of_class_24 in SLK. exact SLK. }
          assert (D3 : (c'' = K_BATCH_CLASS /\ lst <> 0 /\ aslot_addr L c'' k'' = lst) \/ (c'' <> K_BATCH_CLASS \/ lst = 0 \/ aslot_addr L c'' k'' <> lst)) by (clear; lia).
          destruct D3 as [(E24 & LNZ & EL)|NE3].
          -- (* [comment removed for export] *)
             right. rewrite BX. destruct LSTF as [Z0|((q & Hq & Eq) & F1 & F2 & F3 & F4)]; [exfalso; exact (LNZ Z0)|].
             destruct (BQ q ltac:(apply in_or_app; left; exact Hq) E24 ltac:(rewrite EL; exact Eq)) as (yq & BY & Syq & Cyq & Kyq & JQ & EKQ).
             rewrite BY. unfold aslot_busy. rewrite Syq. unfold xb_alloc. rewrite Cyq, Kyq, size_of_class_24, <- E24, EL.
             assert (QNE : a_qloc st <> []) by (intros QL0; apply LNZ; rewrite ELST; replace (q_loc Q) with (@nil qbatchc) by (destruct (q_loc Q); [reflexivity| rewrite QL0 in LN1; cbn in LN1; discriminate]); reflexivity).
             subst ek. unfold ek_of in EKP, EK. destruct (enq_is_app st) eqn:EAx; cbn [ek_post ek_pre] in EKP, EK.
             ** destruct EKP as (LB' & LA' & [bs LJ'] & _). destruct EK as (_ & _ & CNT' & _ & _ & _ & _ & LEN & _).
                rewrite ELST in LB', LA', LJ' |- *.
                set (cnt := b_count (List.last (a_qloc st) dummy_batch)) in *.
                replace 8192 with (24 + (8 * Z.of_nat (length (map (Z_to_bv 64) (qhdrs L (b_chunks (List.last (a_qloc st) dummy_batch)) (qb_ks (List.last (q_loc Q) dummy_qb))) ++ [Z_to_bv 64 (UB - 16)])) + (8192 - 24 - 8 * (cnt + 1))))
                  by (rewrite length_app, LEN; cbn [length]; clear -CNT'; lia).
                apply junk_merge; [| | clear; lia| rewrite length_app, LEN; cbn [length]; clear -CNT'; lia].
                +++ pose proof (junk_of_cells m' _ _ LB') as J. cbn in J. exact J.
                +++ apply junk_merge; [apply junk_of_u64arr; exact LA' | | rewrite length_app, LEN; cbn [length]; clear -CNT'; lia | clear -CNT'; lia].
                    rewrite length_app, LEN. cbn [length]. replace (8 * Z.of_nat (Z.to_nat cnt + 1)) with (8 * (cnt + 1)) by (clear -CNT'; lia). eexists. exact LJ'.
             ** destruct (a_qloc st) as [|b0 bs0] eqn:QL0; [exfalso; exact (QNE eq_refl)|]. rewrite <- QL0 in *.
                destruct EKP as (_ & _ & _ & _ & _ & [LB' LA']). destruct EK as ((_ & _ & _ & _ & _ & _ & _ & LEN0 & _) & _).
                rewrite ELST in LB', LA' |- *.
                replace 8192 with (24 + 8 * Z.of_nat (length (map (Z_to_bv 64) (qhdrs L (b_chunks (List.last (a_qloc st) dummy_batch)) (qb_ks (List.last (q_loc Q) dummy_qb))))))
                  by (rewrite LEN0; clear; lia).
                apply junk_merge; [| apply junk_of_u64arr; exact LA' | clear; lia| rewrite LEN0; clear; lia].
                pose proof (junk_of_cells m' _ _ LB') as J. cbn in J. exact J.
          -- assert (D4 : (g_drain g = true /\ c'' = K_BATCH_CLASS /\ gl <> 0 /\ aslot_addr L c'' k'' = gl /\ gl <> lst)
                        \/ (g_drain g = false \/ c'' <> K_BATCH_CLASS \/ gl = 0 \/ aslot_addr L c'' k'' <> gl \/ gl = lst)) by (destruct (g_drain g); clear; lia).
             destruct D4 as [(GD & E24 & GNZ & EG & GNL)|NE4].
             ** (* [comment removed for export] *)
                right. rewrite BX. destruct GLF as [[GD' _]|(_ & GQL & [Z0|((q & Hq & Eq) & F1 & F2 & F3 & F4)])]; [congruence| exfalso; exact (GNZ Z0)|].
                destruct (BQ q ltac:(apply in_or_app; right; exact Hq) E24 ltac:(rewrite EG; exact Eq)) as (yq & BY & Syq & Cyq & Kyq & JQ & EKQ).
                rewrite BY. unfold aslot_busy. rewrite Syq. unfold xb_alloc. rewrite Cyq, Kyq, size_of_class_24, <- E24, EG.
                assert (GNE : a_qglob st <> []) by (intros QG0; destruct (q_glob Q) eqn:QQ0; [destruct Hq| rewrite QG0 in LN2; cbn in LN2; discriminate]).
                unfold dk_postC in DKP. destruct DKP as (_ & _ & GLN).
                assert (GF : g_full g = true) by (subst g; unfold g_of; cbn [g_full]; destruct (a_qglob st); [exfalso; exact (GNE eq_refl)| reflexivity]).
                rewrite GF, GL, <- GQL in GLN.
                replace 8192 with (8 + 8184) by (clear; lia). apply junk_merge; [| | clear; lia | clear; lia].
                +++ pose proof (junk_of_cells m' _ _ GLN) as J. cbn in J. exact J.
                +++ rewrite <- Eq in JQ. destruct (junk_split m gl 8 8184 JQ ltac:(clear; lia) ltac:(clear; lia)) as [_ J2].
                    eapply junk_frame; [exact J2 | exact MUn | exact WM |]. intros _.
                    assert (DL : lst = 0 \/ lst + 8192 <= gl \/ gl + 8192 <= lst).
                    { destruct LSTF as [Z0|((ql & Hql & Eql) & _)]; [left; exact Z0| right]. rewrite Eql, Eq.
                      destruct (BDIS ql q ltac:(apply in_or_app; left; exact Hql) ltac:(apply in_or_app; right; exact Hq)) as [E|E]; [| exact E].
                      exfalso. apply GNL. rewrite Eq, Eql. symmetry. exact E. }
                    assert (DE : eb = lst \/ eb + 8192 <= gl \/ gl + 8192 <= eb).
                    { destruct EBK as [E|[EAx E]]; [left; exact E| right]. rewrite E, Eq. exact (KDIS q ltac:(apply in_or_app; right; exact Hq) EAx). }
                    apply Kres; clear -F3 F4 RES RHI GNZ DL DE; lia.
             ** (* [comment removed for export] *)
                left. split; [exact BX|]. split.
                +++ assert (DQ : forall q, In q (q_loc Q ++ q_glob Q) -> (c'' <> K_BATCH_CLASS \/ aslot_addr L c'' k'' <> abatch_addr L (qb_slot q)) ->
                        aslot_addr L c'' k'' + size_of_class c'' <= abatch_addr L (qb_slot q) \/ abatch_addr L (qb_slot q) + 8192 <= aslot_addr L c'' k'').
                    { intros q Hq NE. pose proof (slots_sep_any L st X c'' k'' K_BATCH_CLASS (qb_slot q) ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) (K24) Hk''
                                    (bslot_range L st X Q WF CP q Hq) ltac:(destruct NE as [NE|NE]; [left; exact NE| destruct (Z.eq_dec c'' K_BATCH_CLASS) as [->|NC']; [right| left; exact NC']];
                                                                                 intros EKK; apply NE; rewrite EKK; reflexivity)) as D.
                      rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
                    assert (DW13 : lst = 0 \/ aslot_addr L c'' k'' + size_of_class c'' <= lst \/ lst + 8192 <= aslot_addr L c'' k'').
                    { destruct LSTF as [Z0|((ql & Hql & Eql) & _)]; [left; exact Z0| right]. rewrite Eql. apply DQ; [apply in_or_app; left; exact Hql|].
                      destruct NE3 as [NE|[Z0|NE]]; [left; exact NE| exfalso| right; rewrite <- Eql; exact NE].
                      rewrite Eql in Z0. destruct (BGEO ql ltac:(apply in_or_app; left; exact Hql)) as (_ & _ & B3 & _). clear -Z0 B3 RES RHI. lia. }
                    assert (DW14 : eb = lst \/ aslot_addr L c'' k'' + size_of_class c'' <= eb \/ eb + 8192 <= aslot_addr L c'' k'').
                    { destruct EBK as [E|[EAx E]]; [left; exact E| right]. rewrite E. destruct (NEWF EAx) as (_ & _ & KK & _).
                      pose proof (slots_sep_any L st X c'' k'' K_BATCH_CLASS k24 ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) (K24) Hk'' KK
                                    ltac:(destruct NE2 as [NE|[NE|NE]]; [rewrite EAx in NE; discriminate| left; exact NE| right; exact NE])) as D.
                      rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
                    assert (DW15 : gl = lst \/ gl = 0 \/ aslot_addr L c'' k'' + size_of_class c'' <= gl \/ gl + 8192 <= aslot_addr L c'' k'').
                    { destruct GLF as [[_ E]|(GD & GQL & [Z0|((q & Hq & Eq) & _)])]; [left; exact E| right; left; exact Z0| right; right].
                      rewrite Eq. apply DQ; [apply in_or_app; right; exact Hq|].
                      destruct NE4 as [NE|[NE|[NE|[NE|NE]]]]; [congruence| left; exact NE| | right; rewrite <- Eq; exact NE| ].
                      - exfalso. rewrite Eq in NE. destruct (BGEO q ltac:(apply in_or_app; right; exact Hq)) as (_ & _ & B3 & _). clear -NE B3 RES RHI. lia.
                      - rewrite NE in *. destruct NE3 as [NE'|[Z0|NE']]; [left; exact NE'| exfalso| right; rewrite <- Eq; exact NE'].
                        rewrite Eq in Z0. destruct (BGEO q ltac:(apply in_or_app; right; exact Hq)) as (_ & _ & B3 & _). clear -Z0 B3 RES RHI. lia. }
                    apply Kres; [clear -P5 RSP; lia | clear -P6 RSP; unfold K_SPACE_SIZE in *; lia | clear -T16; lia
                                | clear -DW13 P5 RSP RES RHI; lia | clear -DW14 DW13 P5 RSP RES RHI; lia | clear -DW15 DW13 P5 RSP RES RHI; lia].
                +++ intros b Hb. destruct (busy_of_Some_facts X c'' k'' b Hb) as (IB & CB' & KB'). split; [exact CB'|]. split; [exact KB'|]. exact (awf_fits L st X b WF IB).
      + intros POS''.
        set (AU := aregion L c'' + c_allocated_user (get_cls st c'')) in *.
        assert (U0 : aregion L c'' <= AU /\ AU + (c_mapped_user (get_cls st c'') - c_allocated_user (get_cls st c'')) <= aregion L c'' + K_FREEARR_OFF) by (subst AU; clear -Q1 Q2; lia).
        destruct U0 as [U0 U0'].
        assert (U2 : c'' = K_BATCH_CLASS -> aregion L K_BATCH_CLASS + c_allocated_user (get_cls st K_BATCH_CLASS) <= AU) by (intros E; subst AU; rewrite <- E; clear; lia).
        apply Kres; [clear -RI4 Q1 U0; lia | subst AU; clear -Q1 Q2 RI2 RI3; unfold K_FREEARR_OFF, K_REGION, K_SPACE_SIZE in *; lia | clear -POS''; lia | | |].
        * destruct LSTF as [Z0|(_ & F1 & F2 & _)]; [rewrite Z0; right; clear -RI4 RES RHI Q1 U0; lia|].
          exact (undist_vs_user L c'' K_BATCH_CLASS _ _ lst 8192 _ F1 F2 A24 U2 U0 U0').
        * destruct EBF as [Z0|(F1 & F2 & _)]; [rewrite Z0; right; clear -RI4 RES RHI Q1 U0; lia|].
          exact (undist_vs_user L c'' K_BATCH_CLASS _ _ eb 8192 _ F1 F2 A24 U2 U0 U0').
        * assert (GLR : gl = 0 \/ (aregion L K_BATCH_CLASS <= gl /\ gl + 8192 <= aregion L K_BATCH_CLASS + c_allocated_user (get_cls st K_BATCH_CLASS))).
          { destruct GLF as [[_ ->]|(_ & _ & [Z0|(_ & F1 & F2 & _)])]; [| left; exact Z0| right; split; [exact F1| exact F2]].
            destruct LSTF as [Z0|(_ & F1 & F2 & _)]; [left; exact Z0| right; split; [exact F1| exact F2]]. }
          destruct GLR as [Z0|[F1 F2]]; [rewrite Z0; right; clear -RI4 RES RHI Q1 U0; lia|].
          pose proof (undist_vs_user L c'' K_BATCH_CLASS _ _ gl 8192 _ F1 F2 A24 U2 U0 U0') as D. clear -D. lia.
    - (* [comment removed for export] *)
      eapply (aslot_shadow_update_gen L _ m m' MUn WM st st' X X' c''); [exact SHADOW | apply NDS | exact EC3 | exact EC4 | | | apply shlen_nonneg; clear -QS; lia].
      + intros k'' Hk''. left.
        pose proof (slot_geo L st X c'' k'' ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) Hk'') as (T16 & TM16 & TAL & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & _).
        split.
        -- subst X'. rewrite (busy_of_xfreeS X (enq_is_app st) k24 c'' k'').
           destruct (negb (enq_is_app st) && (K_BATCH_CLASS =? c'') && (k24 =? k'')) eqn:T1; [| reflexivity].
           destruct (enq_is_app st) eqn:EAx; [cbn in T1; discriminate|]. cbn [negb andb] in T1.
           destruct (Z.eqb_spec K_BATCH_CLASS c'') as [<-|]; [| discriminate]. destruct (Z.eqb_spec k24 k'') as [<-|]; [| discriminate].
           destruct (NEWF eq_refl) as (_ & NBk & _). rewrite NBk. rewrite size_of_class_24. rewrite slot_shadow_bbatch by (clear; change (shlen 8192) with 1024; lia).
           reflexivity.
        -- pose proof (slot_aligned L c'' k'' SAL ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia)) as AL''.
           apply Kshad.
           ++ rewrite shad_div. unfold ASHOFF, AIMG_HI. clear -P7 RES RHI. Z.div_mod_to_equations. lia.
           ++ rewrite shad_div, shlen_div. unfold ASHOFF in *. clear -P8 T16. Z.div_mod_to_equations. lia.
           ++ apply shlen_nonneg. clear -T16; lia.
           ++ rewrite SHE. destruct SC_r as [D|D].
              ** right. pose proof (shad_sep _ _ _ D MAL8) as HH. rewrite shlen_div in HH.
                 pose proof (shad_mono (al_res L) (aslot_addr L c'' k'') ltac:(clear -P5 RSP; lia)) as MM. clear -HH MM SHL. lia.
              ** left. apply (Z.le_trans _ (shad mb)); [apply shad_sep; [clear -D P6 RI3; unfold K_SPACE_SIZE in *; lia| clear -AL''; Z.div_mod_to_equations; lia] | clear; lia].
      + intros POS''.
        set (AU := aregion L c'' + c_allocated_user (get_cls st c'')) in *.
        assert (U0 : aregion L c'' <= AU /\ AU + (c_mapped_user (get_cls st c'') - c_allocated_user (get_cls st c'')) <= aregion L c'' + K_FREEARR_OFF) by (subst AU; clear -Q1 Q2; lia).
        destruct U0 as [U0 U0'].
        assert (AM : AU mod 8 = 0) by (subst AU; pose proof (mod16_of_class _ _ Q3 QS16 ltac:(clear -QS; lia)) as AM; clear -AM RM''; Z.div_mod_to_equations; lia).
        apply Kshad.
        * rewrite shad_div. unfold ASHOFF, AIMG_HI. clear -U0 RI4 RES RHI. Z.div_mod_to_equations. lia.
        * rewrite shad_div, shlen_div. unfold ASHOFF, K_FREEARR_OFF, K_REGION, K_SPACE_SIZE in *. clear -U0' RI2 RI3 RES RHI. Z.div_mod_to_equations. lia.
        * clear -POS''; lia.
        * rewrite SHE. destruct SC_r as [D|D].
          -- right. pose proof (shad_sep _ _ _ D MAL8) as HH. rewrite shlen_div in HH.
             pose proof (shad_mono (al_res L) AU ltac:(clear -U0 RI4; lia)) as MM. clear -HH MM SHL. lia.
          -- left. apply (Z.le_trans _ (shad mb)); [apply shad_sep; [clear -D U0' RI2 RI3; unfold K_FREEARR_OFF, K_REGION, K_SPACE_SIZE in *; lia| exact AM] | clear; lia].
  }
  (* [comment removed for export] *)
  assert (AVL' : forall c'', 1 <= c'' < K_NUM_CLASSES -> ashadow_avail L st' m' c'').
  { intros c'' Hc''. pose proof WF as WF0. destruct WF0 as (_ & _ & SAL & _ & _ & PERC & _).
    destruct (PERC c'' Hc'') as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & _). pose proof (aregion_mod L c'' SAL) as RM''.
    assert (EC2 : c_mapped_free_array (get_cls st' c'') = c_mapped_free_array (get_cls st c'')) by (destruct (Z.eq_dec c'' K_BATCH_CLASS) as [->|NE]; [exact M24d| rewrite (GCo' c'' NE); reflexivity]).
    assert (EC4 : c_mapped_user (get_cls st' c'') = c_mapped_user (get_cls st c'')) by (destruct (Z.eq_dec c'' K_BATCH_CLASS) as [->|NE]; [exact M24a| rewrite (GCo' c'' NE); reflexivity]).
    unfold K_NUM_CLASSES in Hc''.
    assert (RI : al_res L + 4096 <= aregion L c'' /\ aregion L c'' + K_REGION <= al_space_beg L + K_SPACE_SIZE /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
    { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc'' RSP. lia. }
    destruct RI as (RI1 & RI2 & RI3).
    eapply ashadow_avail_frame; [exact MUn | exact WM | exact (AVL c'' ltac:(unfold K_NUM_CLASSES; exact Hc'')) | exact EC4 | exact EC2 | |].
    - intros POS''. set (AU := aregion L c'' + c_mapped_user (get_cls st c'')) in *.
      assert (U0 : aregion L c'' <= AU /\ AU + (K_FREEARR_OFF - c_mapped_user (get_cls st c'')) <= aregion L c'' + K_FREEARR_OFF) by (subst AU; clear -Q1 Q2; lia).
      destruct U0 as [U0 U0'].
      assert (AM : AU mod 8 = 0) by (subst AU; generalize Q4 RM''; clear; unfold K_USER_MAP; intros; Z.div_mod_to_equations; lia).
      apply Kshad.
      + rewrite shad_div. unfold ASHOFF, AIMG_HI. clear -U0 RI1 RES RHI. Z.div_mod_to_equations. lia.
      + rewrite shad_div, shlen_div. unfold ASHOFF, K_FREEARR_OFF, K_REGION, K_SPACE_SIZE in *. clear -U0' RI2 RI3 RES RHI. Z.div_mod_to_equations. lia.
      + clear -POS''; lia.
      + rewrite SHE. destruct SC_r as [D|D].
        * right. pose proof (shad_sep _ _ _ D MAL8) as HH. rewrite shlen_div in HH.
          pose proof (shad_mono (al_res L) AU ltac:(clear -U0 RI1; lia)) as MM. clear -HH MM SHL. lia.
        * left. apply (Z.le_trans _ (shad mb)); [apply shad_sep; [clear -D U0' RI2 RI3; unfold K_FREEARR_OFF, K_REGION, K_SPACE_SIZE in *; lia| exact AM] | clear; lia].
    - intros POS''. set (AU := afreearr L c'' + c_mapped_free_array (get_cls st c'')) in *.
      assert (FA : aregion L c'' + K_FREEARR_OFF <= AU /\ AU + (K_FREEARR_MAX - c_mapped_free_array (get_cls st c'')) <= aregion L c'' + K_REGION).
      { subst AU. unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q5 Q6. lia. }
      destruct FA as [FA1 FA2].
      assert (AM : AU mod 8 = 0) by (subst AU; generalize Q7 RM''; clear; unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAP; intros; Z.div_mod_to_equations; lia).
      apply Kshad.
      + rewrite shad_div. unfold ASHOFF, AIMG_HI, K_FREEARR_OFF in *. clear -FA1 RI1 RES RHI. Z.div_mod_to_equations. lia.
      + rewrite shad_div, shlen_div. unfold ASHOFF, K_SPACE_SIZE in *. clear -FA2 RI2 RI3 RES RHI. Z.div_mod_to_equations. lia.
      + clear -POS''; lia.
      + rewrite SHE. destruct SC_r as [D|D].
        * right. pose proof (shad_sep _ _ _ D MAL8) as HH. rewrite shlen_div in HH.
          pose proof (shad_mono (al_res L) AU ltac:(clear -FA1 RI1; unfold K_FREEARR_OFF in *; lia)) as MM. clear -HH MM SHL. lia.
        * left. apply (Z.le_trans _ (shad mb)); [apply shad_sep; [clear -D FA2 RI2 RI3; unfold K_REGION, K_SPACE_SIZE in *; lia| exact AM] | clear; lia]. }
  (* [comment removed for export] *)
  assert (PD : Permutation (sec_chunks_of st') cs).
  { eapply Permutation_trans; [| apply Permutation_sym; exact PCS]. apply (sec_chunks_of_quar_sec st st' mb ms n ELIVE). exact (st_after_enq_qfilt_sec st ch eq_refl). }
  assert (NOTL' : ~ sec_live st' ch) by (unfold sec_live; rewrite ELIVE; exact NOTL).
  assert (LVE : forall j c, nth_error order j = Some c -> j <> i -> (sec_live st' c <-> sec_live st c)) by (intros; unfold sec_live; rewrite ELIVE; reflexivity).
  pose proof (ad_t_ptr L ALO) as D_t_p. pose proof (ad_ptr_res L ALO) as D_p_r. pose proof (ad_nodes_ptr L ALO) as D_n_p. pose proof (ad_store_ptr L ALO) as D_s_p.
  pose proof (ao_ptr L ALO) as OP. pose proof (aobj_int _ _ OP ltac:(clear; lia)) as (OPi & OPa & [kP OPs]). unfold adisj, aobj in D_t_p, D_p_r, D_n_p, D_s_p, OP.   (* [comment removed for export] *)
  assert (HS' : ASEC_of L st' X' m').
  { unfold ASEC_of, ASECc.
    pose proof HS as HS1. destruct HS1 as (_ & _ & _ & _ & SHZ0).
    split; [| split; [| split; [| split]]].
    - (* [comment removed for export] *) unfold asec_wf. rewrite EPA, WP, ENRES, ENSEC.
      split; [exact ALO|]. split; [reflexivity|]. split; [exact WR|]. split; [rewrite (Permutation_length PD); exact WL|]. split; [exact WB|].
      split; [rewrite Forall_forall in WF1 |- *; intros c Hc; apply WF1; eapply Permutation_in; [exact PD| exact Hc]|].
      eapply sec_disjoint_perm; [apply Permutation_sym; exact PD| exact WD].
    - (* [comment removed for export] *) exists order. rewrite ?ENRES, ?ENSEC.
      split; [eapply Permutation_trans; [exact PO| apply Permutation_sym; exact PD]|].
      unfold K_HIGH_MEM in *.
      split; [| split].
      + eapply u64arr_frame; [exact U64| exact MUn| exact WM|]. rewrite length_map, LENO.
        apply Kobj; [clear -OP OPi OPs WB WR LENO; lia| clear -OP OPi OPs WB WR; lia| clear -WB; lia| clear -D_t_p WB WR; lia| clear -D_p_r WB WR; lia| clear -D_n_p WB WR; lia| clear -D_s_p WB WR; lia| clear -SC_p WB WR; lia].
      + eapply junk_frame; [exact JK| exact MUn| exact WM|]. intros POS.
        apply Kobj; [clear -OP OPi OPs WB WR POS; lia| clear -OP OPi OPs WB WR; lia| clear -WB POS; lia| clear -D_t_p WB WR; lia| clear -D_p_r WB WR; lia| clear -D_n_p WB WR; lia| clear -D_s_p WB WR; lia| clear -SC_p WB WR; lia].
      + intros j c Hj. destruct (Nat.eq_dec j i) as [->|NEji].
        * (* [comment removed for export] *)
          rewrite NTH in Hj. injection Hj as <-. exists false. split; [split; [discriminate| intros Hl; exfalso; exact (NOTL' Hl)]|].
          unfold ch. cbn [asec_chunk]. pose proof CH as CH0. cbn [asec_chunk] in CH0.
          pose proof CH as CH1. unfold ch in CH1. cbn [asec_chunk] in CH1. destruct CH1 as (G1 & G2 & G3 & G4 & _). unfold SEC_UOFF in G1, G2, G3, G4 |- *. rewrite <- ?EUB in *.
          replace (UB - 16 + 16) with UB in FC' by (clear; lia).
          split; [eapply cells_frame; [exact G1| exact MUn| exact WM| cbn; apply Kchunk; clear -EUB MSB; lia]|].
          split; [eapply junk_frame; [exact G2| exact MUn| exact WM| intros _; apply Kchunk; clear -EUB MSB; lia]|].
          split; [eapply cells_frame; [exact G3| exact MUn| exact WM| cbn; apply Kchunk; clear -EUB MSB; lia]|].
          split; [eapply junk_frame; [exact G4| exact MUn| exact WM| intros _; apply Kchunk; clear -EUB MSB; lia]|].
          split; [exists b1, ctx; split; [exact HDR'| split; [exact B1| split; [exact B13| exact CTX]]]|].
          split. { replace (ms - 6144) with (8 + (ms - 6144 - 8)) by (clear; lia). apply junk_merge; [| | clear; lia| clear -NMS N6 NB; lia].
                   - pose proof (junk_of_cells m' _ _ FC') as J. cbn in J. exact J.
                   - eapply junk_frame; [| exact MUn| exact WM| intros POS; apply Kchunk; clear -EUB MSB POS; lia].
                     exact UJ. }
          split; [eapply fill_frame; [exact S1| exact MUn| exact WM| intros _; apply Kshad; clear -SHLO SHHI SHE MSB; unfold AIMG_HI; Z.div_mod_to_equations; lia]|].
          rewrite (granules_rup n) by (clear -NB; lia). rewrite <- EGQ. unfold sec_user_shadow.
          split; [rewrite (granules_rup n) by (clear -NB; lia); rewrite <- EGQ; exact SH'|].
          eapply fill_frame; [exact S3| exact MUn| exact WM| intros POS; apply Kshad; clear -SHLO SHHI SHE SHL SHP POS MSB; unfold AIMG_HI; Z.div_mod_to_equations; lia].
        * (* [comment removed for export] *)
          destruct (PER j c Hj) as (lvj & LVj & CHj). exists lvj. split; [rewrite (LVE j c Hj NEji); exact LVj|].
          assert (INj : In c order) by (eapply nth_error_In; exact Hj).
          pose proof (proj1 (Forall_forall _ _) WF1o c INj) as Wc. destruct c as [cc ck|mb' ms' n']; [destruct Wc|].
          destruct (sec_wf1_facts' L mb' ms' n' Wc) as (JAL & JLO & JCE & _ & _ & _ & JMSB & _ & _ & _ & (JC_t & _ & JC_r & _ & JC_n & JC_st & _) & _).
          assert (NEc : CSec mb' ms' n' <> ch).
          { intros E. apply NEji. destruct WDo as [ND _]. apply (proj1 (NoDup_nth_error order) ND j i); [apply (proj1 (nth_error_Some order j)); rewrite Hj; discriminate|]. rewrite Hj, NTH, E. reflexivity. }
          destruct WDo as [_ DJ].
          destruct (DJ _ _ INj INo NEc) as [Dc|Dc]; unfold ch in Dc; cbn [sec_mb sec_ms] in Dc.
          all: assert (JAL8 : mb' mod 8 = 0) by (clear -JAL; Z.div_mod_to_equations; lia).
          all: unfold K_HIGH_MEM in JLO, JCE.
          all: pose proof (ablk_lin _ _ JLO) as (JL1 & JL2 & JL3 & JL4); unfold AIMG_HI in JL1; pose proof (ablk_int _ _ JLO) as (kJ & KAJ & KBJ & KEJ & KCJ & KDJ).   (* [comment removed for export] *)
          all: eapply asec_chunk_frameD'; [exact MUn| exact Wc| | | | exists (Z.of_nat j); exact CHj].
          all: try (intros Ad kk Z1 Z2 Z3; apply Kobj; [clear -Z1 Z3 JLO JL1 KAJ KBJ KEJ KCJ KDJ; lia| clear -Z3 JCE; lia| clear -Z2; lia| clear -Z1 Z3 JC_t; lia| clear -Z1 Z3 JC_r; lia| clear -Z1 Z3 JC_n; lia| clear -Z1 Z3 JC_st; lia| clear -Z1 Z3 Dc; lia]).
          all: try (pose proof CHj as CH1; cbn [asec_chunk] in CH1; destruct CH1 as (Hh & _);
                    eapply cells_frame; [exact Hh| exact MUn| exact WM| cbn; apply Kobj; [clear -JLO JL1 JMSB KAJ KBJ KEJ KCJ KDJ; lia| clear -JCE JMSB; lia| clear; lia| clear -JC_t JMSB; lia| clear -JC_r JMSB; lia| clear -JC_n JMSB; lia| clear -JC_st JMSB; lia| clear -Dc JMSB; lia]]).
          -- intros Ad kk Z1 Z2 Z3. apply Kshad; [rewrite shad_div in Z1; unfold ASHOFF, AIMG_HI in *; clear -Z1 JLO JL1; Z.div_mod_to_equations; lia| rewrite shad_div in Z3; unfold ASHOFF in *; clear -Z3 JCE JAL8; Z.div_mod_to_equations; lia| clear -Z2; lia|].
             left. rewrite SHE. pose proof (shad_sep _ _ _ Dc JAL8) as HH. rewrite shlen_div in HH. clear -HH Z3. lia.
          -- intros Ad kk Z1 Z2 Z3. apply Kshad; [rewrite shad_div in Z1; unfold ASHOFF, AIMG_HI in *; clear -Z1 JLO JL1; Z.div_mod_to_equations; lia| rewrite shad_div in Z3; unfold ASHOFF in *; clear -Z3 JCE JAL8; Z.div_mod_to_equations; lia| clear -Z2; lia|].
             right. rewrite SHE. pose proof (shad_sep _ _ _ Dc MAL8) as HH. rewrite shlen_div in HH. clear -HH Z1 SHL. lia.
    - (* [comment removed for export] *) destruct SINST as (I1 & [srt I2] & I3 & I4 & I5 & I6). unfold asec_inst. unfold AINSTANCE in *.
      split; [eapply cells_frame; [exact I1| exact MUn| exact WM| cbn; apply Kimg; clear; unfold AIMG_HI; lia]|].
      split; [exists srt; eapply cells_frame; [exact I2| exact MUn| exact WM| cbn; apply Kimg; clear; unfold AIMG_HI; lia]|].
      split; [eapply junk_frame; [exact I3| exact MUn| exact WM| intros _; apply Kimg; clear; unfold AIMG_HI; lia]|].
      split; [eapply junk_frame; [exact I4| exact MUn| exact WM| intros _; apply Kimg; clear; unfold AIMG_HI; lia]|].
      split; [eapply cells_frame; [exact I5| exact MUn| exact WM| cbn; apply Kimg; clear; unfold AIMG_HI; lia]|].
      eapply junk_frame; [exact I6| exact MUn| exact WM| intros _; apply Kimg; clear; unfold AIMG_HI; lia].
    - (* [comment removed for export] *) unfold aprim0 in *. eapply azero_frame; [exact PZ| exact MUn| exact WM|]. intros POS.
      apply Kshad.
      + rewrite shad_div. unfold ASHOFF, AIMG_HI. clear -RSP RES RHI. Z.div_mod_to_equations. lia.
      + rewrite shad_div, shlen_div. unfold ASHOFF. clear -SP2. unfold K_REGION, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472 in *. change (2^32) with 4294967296 in *. Z.div_mod_to_equations. lia.
      + clear -POS; lia.
      + rewrite SHE. destruct SC_r as [D|D].
        * right. pose proof (shad_sep _ _ _ D MAL8) as HH. rewrite shlen_div in HH.
          pose proof (shad_mono (al_res L) (al_space_beg L) ltac:(clear -RSP; lia)) as MM. clear -HH MM SHL. lia.
        * left. apply (Z.le_trans _ (shad mb)); [apply shad_sep; [clear -D SP2 RSP; unfold K_REGION, K_SPACE_SIZE, K_SPACE_EXTRA in *; lia| clear -SP3; unfold K_ALIGN in SP3; Z.div_mod_to_equations; lia] | clear; lia].
    - (* [comment removed for export] *) intros x Hx HFh HC.
      assert (HC0 : Forall (fun c => ~ (sec_mb c <= x < sec_mb c + sec_ms c)) cs).
      { rewrite Forall_forall in HC |- *. intros c Hin. apply HC. eapply Permutation_in; [apply Permutation_sym; exact PD| exact Hin]. }
      pose proof INcs as INst.
      pose proof (proj1 (Forall_forall _ _) HC0 ch INst) as NX. unfold ch in NX. cbn [sec_mb sec_ms] in NX.
      unfold K_HIGH_MEM, AIMG_HI, KLS in Hx.   (* [comment removed for export] *)
      assert (SX : 0 <= shad x < 2^64) by (rewrite shad_div; unfold ASHOFF, K_HIGH_MEM in *; unfold AIMG_HI, KLS in Hx; clear -Hx; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
      rewrite <- (SHZ0 x ltac:(unfold K_HIGH_MEM; exact Hx) HFh HC0). apply MUn. rewrite wa_unsigned by exact SX.
      eapply (disjoint_outside _ (shad x) 1); [| clear; lia]. apply Kshad; [rewrite shad_div; unfold ASHOFF, AIMG_HI; clear -Hx; Z.div_mod_to_equations; lia| rewrite shad_div; unfold ASHOFF; pose proof atop_range as AR8; clear -Hx AR8; Z.div_mod_to_equations; lia| clear; lia|].
      rewrite SHE. destruct (Z_lt_le_dec x mb) as [LT|GE].
      + left. rewrite !shad_div. clear -LT MAL8. Z.div_mod_to_equations. lia.
      + right. rewrite !shad_div in *. clear -GE NX SHL MAL8 MSAL. Z.div_mod_to_equations. lia. }
  assert (BL' : ablocks L st' X' LB).
  { eapply ablocks_mono; [exact BL| intros y q Hy _; subst X'; apply In_xfreeS; exact Hy| intros q mb' ms' n' Hl; rewrite ELIVE; exact Hl]. }
  assert (FKD : forall cls FA sz, In (mkABlock (ABFake cls) FA sz) LB -> al_fake L <= FA /\ 0 <= sz /\ FA + sz <= al_fake L + 11571200)
    by (intros cls FA sz Hin; exact (proj1 (proj2 BL) cls FA sz Hin)).
  pose proof (ao_fake L ALO) as FKO. pose proof (aobj_int _ _ FKO ltac:(clear; lia)) as (FKi & FKa & [kF FBND]). unfold aobj in FKO.   (* [comment removed for export] *)
  pose proof (ad_t_fake L ALO) as D_t_f. pose proof (ad_fake_res L ALO) as D_f_res. pose proof (ad_nodes_fake L ALO) as D_n_f. pose proof (ad_store_fake L ALO) as D_s_f.
  unfold adisj in D_t_f, D_f_res, D_n_f, D_s_f. box D_t_f. box D_f_res. box D_n_f. box D_s_f.
  assert (SHB : 2148256256 <= shad UB /\ shad UB + gq <= 17594333495296) by (clear -SHLO SHHI SHE SHL; lia).   (* [comment removed for export] *)
  assert (HFK' : AFK L LB m').
  { eapply (hf_frame _ HL L LB m m'); [exact HFK | exact MUn | exact WM |].
    - pose proof (ao_dtls L ALO) as DTO. pose proof (aobj4_int _ DTO) as (_ & _ & [kD DBND] & [jD DIMG]). unfold aobj in DTO.   (* [comment removed for export] *)
      pose proof (ad_t_dtls L ALO) as D1. pose proof (ad_dtls_res L ALO) as D2. pose proof (ad_nodes_dtls L ALO) as D3. pose proof (ad_store_dtls L ALO) as D4.
      unfold adisj in D1, D2, D3, D4.
      unfold fake_untouched. unfold K_SPACE_SIZE, K_HIGH_MEM in *. change (2^37) with 137438953472 in *.
      assert (SHF : (shad (al_fake L) + shlen 11571200 <= shad UB \/ shad UB + gq <= shad (al_fake L))
                    /\ 2148256256 <= shad (al_fake L) /\ shad (al_fake L) + shlen 11571200 <= 17594333495296).   (* [comment removed for export] *)
      { split; [| rewrite shad_div, shlen_div; unfold ASHOFF; pose proof atop_range as AR8; clear -FKO FKi FBND AR8; Z.div_mod_to_equations; lia].
        rewrite SHE. destruct SC_f as [D|D].
        - right. pose proof (shad_sep _ _ _ D MAL8) as HH. rewrite shlen_div in HH. clear -HH SHL. lia.
        - left. apply (Z.le_trans _ (shad mb)); [apply shad_sep; [exact D| clear -FKO FKi FBND; Z.div_mod_to_equations; lia] | clear; lia]. }
      destruct SHF as (SHF1 & SHF2 & SHF3).
      pose proof D_t_f as DTF; unbox DTF. pose proof D_f_res as DFR; unbox DFR. pose proof D_n_f as DNF; unbox DNF. pose proof D_s_f as DSF; unbox DSF.
      assert (LSTR : (lst = 0 /\ qsz lst = 8) \/ (al_res L + 4096 <= lst /\ lst + 8192 <= al_res L + 137439023104 /\ qsz lst = 8192))   (* [comment removed for export] *)
        by (destruct LSTF as [Z0|(_ & _ & _ & F3 & F4)]; [left; split; [exact Z0| apply qsz_eq0; exact Z0]| right; split; [exact F3| split; [exact F4| apply qsz_pos; clear -F3 RES RHI; lia]]]).
      assert (EBR : al_res L + 4096 <= eb /\ eb + 8192 <= al_res L + 137439023104 /\ qsz eb = 8192) by (destruct EBF as [Z0|(_ & _ & F3 & F4)]; [exfalso; clear -Z0 EBNZ; lia| split; [assumption| split; [assumption| apply qsz_pos; clear -EBNZ; lia]]]).   (* [comment removed for export] *)
      assert (GLRR : gl = lst \/ gl = 0 \/ (al_res L + 4096 <= gl /\ gl + 8192 <= al_res L + 137439023104))
        by (destruct GLF as [[_ Z2]|(_ & _ & [Z2|(_ & _ & _ & H3 & H4)])]; [left; exact Z2| right; left; exact Z2| right; right; split; assumption]).
      do 16 (apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [lia|]); lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3; repeat (split; [lia|]); lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3; repeat (split; [lia|]); lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [lia|]); lia]
              | solve [clear -SC_f SC_d EUB UBS NB RUP MLO ML1 ML3 KAM KBM KEM KCM KDM MCE FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [lia|]); lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR; repeat (split; [lia|]); lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR; repeat (split; [lia|]); lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR; repeat (split; [lia|]); lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] |]).
      apply Forall_nil. }
  assert (QH : qhdr L ch 0 = UB - 16) by (unfold ch; cbn [qhdr]; unfold PG; rewrite RZ, EUB; clear; lia).
  (* [comment removed for export] *)
  assert (GNB : g_nb g = Z.of_nat (length (a_qglob st))) by reflexivity.
  assert (GFST : g_fst g = qfirst L (q_glob Q)) by reflexivity.
  assert (GQB : g_qb g = a_qglob_bytes st) by reflexivity.
  assert (GFU : g_full g = match a_qglob st with [] => false | _ :: _ => true end) by reflexivity.
  destruct DKP as (MX' & GC' & GLN).
  pose proof (qnumR_freeR st ch NUM ltac:(unfold ch; cbn [chunk_size]; clear -NB; lia)) as (NUM' & NB2a & NB2b & NB2c & NF2).
  fold st2 st' in NUM', NB2a, NB2b, NB2c, NF2.
  pose proof (st_after_q st2) as [DRN NDR]. fold st' in DRN, NDR.
  assert (QK' : aquar_consts m').
  { eapply cells_frame; [exact QK | exact MUn | exact WM |]. cbn [cells_size csize Nat.add]. apply Kimg; clear; unfold AQ_MAX, AIMG_HI; lia. }
  assert (IA' : aintal true m').
  { split; [exact FL'|]. split; [exact IAS'|]. intros _ j Hj. apply IAM'. revert Hj. clear. unfold AIA_MAP1_LEN. intros Hj. Z.div_mod_to_equations. lia. }
  (* [comment removed for export] *)
  assert (BLST : forall q, In q (q_loc Q ++ q_glob Q) -> abatch_addr L (qb_slot q) <> lst ->
      abatch_addr L (qb_slot q) + 8192 <= lst \/ lst + 8192 <= abatch_addr L (qb_slot q) \/ lst = 0).
  { intros q Hq NE. destruct LSTF as [Z0|((ql & Hql & Eql) & _)]; [right; right; exact Z0|].
    destruct (BDIS q ql Hq ltac:(apply in_or_app; left; exact Hql)) as [E|E]; [exfalso; apply NE; rewrite Eql; exact E| rewrite Eql].
    destruct E as [E|E]; [left; exact E| right; left; exact E]. }
  assert (BFR : forall q, In q (q_loc Q ++ q_glob Q) -> abatch_addr L (qb_slot q) <> lst -> abatch_addr L (qb_slot q) <> gl ->
      disjoint_from (WfS (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) (abatch_addr L (qb_slot q)) 8192).
  { intros q Hq NL NG. destruct (BGEO q Hq) as (_ & _ & F3 & F4). pose proof (BLST q Hq NL) as DL.
    assert (DE : eb = lst \/ abatch_addr L (qb_slot q) + 8192 <= eb \/ eb + 8192 <= abatch_addr L (qb_slot q)).
    { destruct EBK as [E|[EA E]]; [left; exact E| right]. rewrite E.
      destruct (KDIS q Hq EA) as [D|D]; [right; exact D| left; exact D]. }
    assert (DG : gl = lst \/ gl = 0 \/ abatch_addr L (qb_slot q) + 8192 <= gl \/ gl + 8192 <= abatch_addr L (qb_slot q)).
    { destruct GLF as [[_ E]|(_ & _ & [Z0|((qg & Hqg & Eqg) & _)])]; [left; exact E| right; left; exact Z0| right; right].
      destruct (BDIS q qg Hq ltac:(apply in_or_app; right; exact Hqg)) as [E|E]; [exfalso; apply NG; rewrite Eqg; exact E| rewrite Eqg; exact E]. }
    apply Kres; clear -F3 F4 RES RHI DL DE DG; lia. }
  assert (HQ' : exists Q', q_loc Q' = [] /\ q_ia Q' = true /\ q_pend Q' = q_pend Q
            /\ aqcache L m' (aq_tcache L) (a_qloc st') (q_loc Q') (a_qloc_bytes st')
            /\ aqcache L m' AQ_GCACHE (a_qglob st') (q_glob Q') (a_qglob_bytes st')
            /\ qcoupled L st' X' Q').
  { subst ek. unfold ek_of in EKP, EK, QC', GC', GLN, EEB, SB1, GDR, GL, GLST, REC1'.
    destruct (enq_is_app st) eqn:EA; cbn [ek_nb ek_fst ek_lst ek_delta ek_b ek_post ek_pre] in EKP, EK, QC', GC', GLN, EEB, SB1, GDR, GL, GLST, REC1'.
    - (* [comment removed for export] *)
      destruct EKP as (LB' & LA' & [bs LJ'] & _). destruct EK as (_ & _ & CNT' & _ & _ & _ & _ & LEN & _).
      (* [comment removed for export] *)
      pose proof EA as EA0. unfold enq_is_app in EA0. destruct (rev (a_qloc st)) as [|blr rl] eqn:RV; [discriminate|].
      assert (QL : a_qloc st = rev rl ++ [blr]) by (rewrite <- (rev_involutive (a_qloc st)), RV; reflexivity).
      destruct (Z.eqb_spec (b_count blr) Q_BATCH) as [|NFULL]; [discriminate|]. clear EA0.
      set (l := rev rl) in *. set (bl := blr) in *.
      assert (LQ : (0 < length (q_loc Q))%nat) by (rewrite LN1, QL, length_app; cbn; clear; lia).
      assert (QQ : q_loc Q = removelast (q_loc Q) ++ [List.last (q_loc Q) dummy_qb]) by (apply app_removelast_last; destruct (q_loc Q); [cbn in LQ; clear -LQ; lia| discriminate]).
      set (ql := removelast (q_loc Q)) in *. set (qz := List.last (q_loc Q) dummy_qb) in *.
      assert (LNl : length ql = length l) by (rewrite QQ, QL, !length_app in LN1; cbn in LN1; clear -LN1; lia).
      assert (LST : List.last (a_qloc st) dummy_batch = bl) by (rewrite QL; apply last_app1). rewrite LST in *.
      assert (QLST : lst = abatch_addr L (qb_slot qz)) by (rewrite ELST, QQ; apply qlast_app1).
      set (bl' := mkABatch (b_count bl + 1) (b_size bl + n) (ch :: b_chunks bl)) in *.
      set (qz' := mkQB (qb_slot qz) (0 :: qb_ks qz)) in *.
      assert (EAPP : enq_app st ch = Some (set_qloc (l ++ [bl']) (a_qloc_bytes st + n) st)).
      { unfold enq_app. rewrite RV. fold bl. replace (b_count bl =? Q_BATCH) with false by (symmetry; apply Z.eqb_neq; exact NFULL).
        subst bl'. reflexivity. }
      assert (Q2 : a_qloc st2 = l ++ [bl'] /\ a_qloc_bytes st2 = a_qloc_bytes st + n /\ a_qglob st2 = a_qglob st /\ a_qglob_bytes st2 = a_qglob_bytes st).
      { subst st2. unfold st_enq. rewrite EAPP. cbn. repeat split; reflexivity. }
      destruct Q2 as (QL2 & QB2 & QG2 & QGB2).
      (* [comment removed for export] *)
      unfold abatches in ABL, ABG. rewrite QL, QQ in ABL. apply abatches_to_app in ABL; [| exact LNl]. destruct ABL as [ABl ABz].
      cbn [abatches_to qaddrs map hd] in ABz. destruct ABz as [(Z1 & Z2 & Z3 & Z4 & Z5 & Z6) _].
      assert (ABl' : abatches_to L m' l ql (hd 0 (qaddrs L [qz']))).
      { cbn [qaddrs map hd qz' qb_slot]. cbn [qaddrs map hd] in ABl. eapply abatches_to_frame; [exact MUn | exact WM | exact ABl |].
        intros q Hq. assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; left; rewrite QQ; apply in_or_app; left; exact Hq).
        assert (NEq : abatch_addr L (qb_slot q) <> lst).
        { rewrite QLST. intros E. apply in_split in Hq. destruct Hq as (qs1 & qs2 & EQl).
          apply (bslots_nodup_split L st X Q CP qs1 q qs2 qz (q_glob Q)); [rewrite QQ, EQl; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; reflexivity|].
          pose proof (bslot_range L st X Q WF CP q INq). pose proof (bslot_range L st X Q WF CP qz ltac:(apply in_or_app; left; rewrite QQ; apply in_or_app; right; left; reflexivity)).
          unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia. }
        apply BFR; [exact INq | exact NEq |].
        destruct GLF as [[_ E]|(GD & GQL & [Z0|((qg & Hqg & Eqg) & _)])]; [rewrite E; exact NEq| rewrite Z0; destruct (BGEO q INq) as (_ & _ & F3 & _); clear -F3 RES RHI; lia|].
        rewrite Eqg. intros E. apply in_split in Hq. destruct Hq as (qs1 & qs2 & EQl). apply in_split in Hqg. destruct Hqg as (gs1 & gs2 & EQg).
        apply (bslots_nodup_split L st X Q CP qs1 q (qs2 ++ [qz] ++ gs1) qg gs2); [rewrite QQ, EQl, EQg; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; reflexivity|].
        pose proof (bslot_range L st X Q WF CP q INq). pose proof (bslot_range L st X Q WF CP qg ltac:(apply in_or_app; right; rewrite EQg; apply in_or_app; right; left; reflexivity)).
        unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia. }
      assert (ABz' : abatch_cells L m' bl' qz' 0).
      { unfold abatch_cells. cbv zeta. cbn [qb_slot qb_ks b_size b_count b_chunks bl' qz']. rewrite <- QLST. rewrite qhdrs_cons, map_app. cbn [map qhdr]. rewrite QH.
        split; [exact LB'|]. split; [exact LA'|]. split; [| split; [cbn [length]; rewrite Z4; clear; lia| split; [cbn [length]; rewrite Z5; reflexivity| unfold Q_BATCH in *; clear -CNT' Z6; lia]]].
        exists bs. unfold Q_BATCH_BYTES. exact LJ'. }
      assert (ABL' : abatches_to L m' (l ++ [bl']) (ql ++ [qz']) 0).
      { apply abatches_to_app; [exact LNl|]. split; [exact ABl'|]. cbn. split; [exact ABz'| exact I]. }
      assert (CP2 : qcoupled L st2 X' (mkQConc (ql ++ [qz']) (q_glob Q) true (q_pend Q))).
      { subst X'. unfold xfreeS. apply (qcoupled_app_sec L st X Q mb ms n CP st2 l bl ql qz true 0 QL QQ QL2 QG2). }
      subst qz'.
      destruct (Z.lt_ge_cases Q_CACHE (a_qloc_bytes st2)) as [DR|NDRN]; [| exfalso; clear -NDRN REC1; lia].
      + (* [comment removed for export] *)
        destruct (DRN DR) as (QL3 & QB3 & QG3 & QGB3).
        assert (GD : g_drain g = true) by (rewrite GDR; apply Z.ltb_lt; rewrite <- QB2; exact DR).
        exists (mkQConc [] (q_glob Q ++ (ql ++ [{| qb_slot := qb_slot qz; qb_ks := 0 :: qb_ks qz |}])) true (q_pend Q)). cbn [q_loc q_glob q_ia q_pend].
        split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
        rewrite QL3, QB3, QG3, QGB3, QL2, QG2, QB2, QGB2.
        split; [| split].
        * split; [cbn [length qfirst qlast qaddrs map hd last Z.of_nat]; exact QC'| exact I].
        * split.
          -- rewrite length_app, Nat2Z.inj_add, <- GNB. rewrite length_app. cbn [length].
             replace (Z.of_nat (length l + 1)) with (Z.of_nat (length (a_qloc st))) by (rewrite QL, length_app; cbn; reflexivity).
             rewrite qlast_app by (intros Enil; apply app_eq_nil in Enil; destruct Enil as [_ Enil]; discriminate). rewrite qlast_reslot, <- QQ, <- ELST.
             assert (FE : qfirst L (q_glob Q ++ ql ++ [{| qb_slot := qb_slot qz; qb_ks := 0 :: qb_ks qz |}]) = (if g_full g then g_fst g else qfirst L (q_loc Q))).
             { rewrite GFU, GFST. destruct (a_qglob st) eqn:QG0.
               - replace (q_glob Q) with (@nil qbatchc) by (destruct (q_glob Q); [reflexivity| cbn in LN2; discriminate]). cbn [app]. rewrite qfirst_reslot, <- QQ. reflexivity.
               - apply qfirst_app. destruct (q_glob Q); [cbn in LN2; discriminate| discriminate]. }
             rewrite FE, <- GQB. exact GC'.
          -- unfold abatches. apply abatches_to_app; [exact LN2|]. split.
             ++ (* [comment removed for export] *)
                rewrite hd_qaddrs by (intros Enil; apply app_eq_nil in Enil; destruct Enil as [_ Enil]; discriminate). rewrite qfirst_reslot, <- QQ.
                destruct (a_qglob st) as [|bg0 lg0] eqn:QG0.
                ** replace (q_glob Q) with (@nil qbatchc) by (destruct (q_glob Q); [reflexivity| cbn in LN2; discriminate]). exact I.
                ** rewrite <- QG0 in *.
                   assert (GNE : a_qglob st <> []) by (rewrite QG0; discriminate).
                   assert (QG : a_qglob st = removelast (a_qglob st) ++ [List.last (a_qglob st) dummy_batch]) by (apply app_removelast_last; exact GNE).
                   assert (LQg : (0 < length (q_glob Q))%nat) by (rewrite LN2, QG0; cbn; clear; lia).
                   assert (QQg : q_glob Q = removelast (q_glob Q) ++ [List.last (q_glob Q) dummy_qb]) by (apply app_removelast_last; destruct (q_glob Q); [cbn in LQg; clear -LQg; lia| discriminate]).
                   set (lg := removelast (a_qglob st)) in *. set (blg := List.last (a_qglob st) dummy_batch) in *.
                   set (qg := removelast (q_glob Q)) in *. set (qgz := List.last (q_glob Q) dummy_qb) in *.
                   assert (LNg : length qg = length lg) by (rewrite QQg, QG, !length_app in LN2; cbn in LN2; clear -LN2; lia).
                   rewrite QG, QQg in ABG. apply abatches_to_app in ABG; [| exact LNg]. destruct ABG as [ABg ABgz].
                   cbn [abatches_to qaddrs map hd] in ABgz. destruct ABgz as [(Y1 & Y2 & Y3 & Y4 & Y5 & Y6) _].
                   assert (QGLST : qlast L (q_glob Q) = abatch_addr L (qb_slot qgz)) by (rewrite QQg; apply qlast_app1).
                   rewrite GFU in GLN. rewrite ?QG0 in GLN. cbv iota beta in GLN. rewrite GL, QGLST in GLN.
                   rewrite QG, QQg. apply abatches_to_app; [exact LNg|]. split.
                   +++ cbn [qaddrs map hd]. eapply abatches_to_frame; [exact MUn | exact WM | exact ABg |].
                       intros q Hq. assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; right; rewrite QQg; apply in_or_app; left; exact Hq).
                       assert (NEg : abatch_addr L (qb_slot q) <> abatch_addr L (qb_slot qgz)).
                       { intros E. apply in_split in Hq. destruct Hq as (gs1 & gs2 & EQg).
                         apply (bslots_nodup_split L st X Q CP (q_loc Q ++ gs1) q gs2 qgz []); [rewrite QQg, EQg; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; reflexivity|].
                         pose proof (bslot_range L st X Q WF CP q INq). pose proof (bslot_range L st X Q WF CP qgz ltac:(apply in_or_app; right; rewrite QQg; apply in_or_app; right; left; reflexivity)).
                         unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia. }
                       apply BFR; [exact INq | | rewrite EGL; unfold dk_glst; rewrite GD, GL, QGLST; exact NEg].
                       rewrite QLST. intros E. apply in_split in Hq. destruct Hq as (gs1 & gs2 & EQg).
                       apply (bslots_nodup_split L st X Q CP ql qz gs1 q (gs2 ++ [qgz])); [rewrite QQ, QQg, EQg; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; reflexivity|].
                       pose proof (bslot_range L st X Q WF CP q INq). pose proof (bslot_range L st X Q WF CP qz ltac:(apply in_or_app; left; rewrite QQ; apply in_or_app; right; left; reflexivity)).
                       unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia.
                   +++ cbn [abatches_to]. split; [| exact I].
                       (* [comment removed for export] *)
                       unfold abatch_cells. cbv zeta. change (hd (qfirst L (q_loc Q)) (qaddrs L [])) with (qfirst L (q_loc Q)).
                       assert (GLS : gl = abatch_addr L (qb_slot qgz)) by (rewrite EGL; unfold dk_glst; rewrite GD, GL, QGLST; reflexivity).
                       assert (NGL : abatch_addr L (qb_slot qgz) <> lst).
                       { rewrite QLST. intros E. apply (bslots_nodup_split L st X Q CP ql qz qg qgz []); [rewrite QQ, QQg; rewrite <- ?app_assoc; cbn [app]; reflexivity|].
                         pose proof (bslot_range L st X Q WF CP qz ltac:(apply in_or_app; left; rewrite QQ; apply in_or_app; right; left; reflexivity)).
                         pose proof (bslot_range L st X Q WF CP qgz ltac:(apply in_or_app; right; rewrite QQg; apply in_or_app; right; left; reflexivity)).
                         unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia. }
                       assert (INgz : In qgz (q_loc Q ++ q_glob Q)) by (apply in_or_app; right; rewrite QQg; apply in_or_app; right; left; reflexivity).
                       destruct (BGEO qgz INgz) as (_ & _ & F3 & F4). pose proof (BLST qgz INgz NGL) as DL.
                       assert (DE : eb = lst \/ abatch_addr L (qb_slot qgz) + 8192 <= eb \/ eb + 8192 <= abatch_addr L (qb_slot qgz)).
                       { destruct EBK as [E|[EA' E]]; [left; exact E| discriminate]. }
                       assert (D8 : forall A8 kk, abatch_addr L (qb_slot qgz) + 8 <= A8 -> A8 + kk <= abatch_addr L (qb_slot qgz) + 8192 -> 0 <= kk ->
                                  disjoint_from (WfS (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) A8 kk).
                       { intros A8 kk HA HK KK0. apply Kres; clear -F3 F4 RES RHI DL DE GLS HA HK KK0; lia. }
                       pose proof Y1 as Y1'. rw_split Y1' 1%nat YN YR.
                       eapply cells_frame in YR; [| exact MUn | exact WM | cbn [cells_size csize Nat.add]; apply D8; clear; lia].
                       rw_join GLN YR YH.
                       split; [exact YH|]. split; [| split; [| split; [exact Y4| split; [exact Y5| exact Y6]]]].
                       --- eapply u64arr_frame; [exact Y2 | exact MUn | exact WM |]. rewrite length_map, qhdrs_length by exact Y5. rewrite <- Y4.
                           apply D8; unfold Q_BATCH in Y6; clear -Y6; lia.
                       --- eapply junk_frame; [exact Y3 | exact MUn | exact WM |]. intros Hp. apply D8; unfold Q_BATCH, Q_BATCH_BYTES in *; clear -Y6 Hp; lia.
             ++ exact ABL'.
        * exact (qcoupled_drain L st2 st' X' (mkQConc (ql ++ [{| qb_slot := qb_slot qz; qb_ks := 0 :: qb_ks qz |}]) (q_glob Q) true (q_pend Q)) true CP2 QL3 QG3).
    - (* [comment removed for export] *)
      destruct (NEWF eq_refl) as (NK24 & NB24 & KK24 & NIB & JK24 & FK & CIN & POS).
      destruct EKP as (C24' & [stj' SJ'] & NBc & NAc & [bs NJc] & OLDc).
      pose proof EAPP0 as EAPP.
      set (nbt := mkABatch 1 (n + 8192) [ch]) in *.
      set (qn := mkQB k24 [0]) in *.
      assert (Q2 : a_qloc st2 = a_qloc st ++ [nbt] /\ a_qloc_bytes st2 = a_qloc_bytes st + (n + 8192) /\ a_qglob st2 = a_qglob st /\ a_qglob_bytes st2 = a_qglob_bytes st).
      { subst st2. unfold st_enq. rewrite EAPP. pose proof (enq_new_core ch st) as (_ & E1 & E2 & _ & E3 & E4 & _).
        rewrite E1, E2, E3, E4. subst nbt. unfold ch. cbn [a_qloc a_qloc_bytes a_qglob a_qglob_bytes set_live chunk_size]. fold ch. unfold Q_BATCH_BYTES.
        split; [reflexivity|]. split; [clear; lia|]. split; reflexivity. }
      destruct Q2 as (QL2 & QB2 & QG2 & QGB2).
      assert (FSTE : (if match a_qloc st with [] => false | _ :: _ => true end then qfirst L (q_loc Q) else abatch_addr L k24) = qfirst L (q_loc Q ++ [qn])).
      { rewrite qfirst_app_r. subst qn; cbn [qb_slot]. generalize LN1. clear. generalize (a_qloc st) (q_loc Q).
        intros [|x1 r1] [|x2 r2] LL; cbn in LL; first [reflexivity | discriminate]. }
      first [rewrite FSTE in GC' | idtac]. first [rewrite FSTE in GLN | idtac].
      assert (QLST' : qlast L (q_loc Q ++ [qn]) = abatch_addr L k24) by (subst qn; apply qlast_app1).
      (* [comment removed for export] *)
      assert (GNL : forall q, In q (q_glob Q) -> abatch_addr L (qb_slot q) <> lst).
      { intros q Hq E. assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; right; exact Hq).
        destruct LSTF as [Z0|((q' & Hq' & Eq') & _)].
        - destruct (BGEO q INq) as (_ & _ & F3 & _). clear -F3 RES RHI E Z0. lia.
        - apply in_split in Hq. destruct Hq as (gs1 & gs2 & EQg). apply in_split in Hq'. destruct Hq' as (qs1 & qs2 & EQl).
          apply (bslots_nodup_split L st X Q CP qs1 q' (qs2 ++ gs1) q gs2); [rewrite EQl, EQg; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; reflexivity|].
          pose proof (bslot_range L st X Q WF CP q INq). pose proof (bslot_range L st X Q WF CP q' ltac:(apply in_or_app; left; rewrite EQl; apply in_or_app; right; left; reflexivity)).
          rewrite Eq' in E. unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia. }
      (* [comment removed for export] *)
      assert (ABO' : abatches_to L m' (a_qloc st) (q_loc Q) (abatch_addr L k24)).
      { destruct (a_qloc st) as [|b0 l0] eqn:QL0.
        - replace (q_loc Q) with (@nil qbatchc) by (destruct (q_loc Q); [reflexivity| cbn in LN1; discriminate]). exact I.
        - cbv iota beta in OLDc. destruct OLDc as [OLD1 OLD2]. rewrite <- QL0 in *.
          assert (LNE : a_qloc st <> []) by (rewrite QL0; discriminate).
          assert (QL : a_qloc st = removelast (a_qloc st) ++ [List.last (a_qloc st) dummy_batch]) by (apply app_removelast_last; exact LNE).
          assert (LQ : (0 < length (q_loc Q))%nat) by (rewrite LN1, QL0; cbn; clear; lia).
          assert (QQ : q_loc Q = removelast (q_loc Q) ++ [List.last (q_loc Q) dummy_qb]) by (apply app_removelast_last; destruct (q_loc Q); [cbn in LQ; clear -LQ; lia| discriminate]).
          set (l := removelast (a_qloc st)) in *. set (bl := List.last (a_qloc st) dummy_batch) in *.
          set (ql := removelast (q_loc Q)) in *. set (qz := List.last (q_loc Q) dummy_qb) in *.
          assert (LNl : length ql = length l) by (rewrite QQ, QL, !length_app in LN1; cbn in LN1; clear -LN1; lia).
          assert (QLST : lst = abatch_addr L (qb_slot qz)) by (rewrite ELST, QQ; apply qlast_app1).
          assert (FULL : b_count bl = Q_BATCH).
          { pose proof EA as EA0. unfold enq_is_app in EA0. rewrite QL, rev_unit in EA0. cbv iota beta in EA0.
            revert EA0. destruct (Z.eqb_spec (b_count bl) Q_BATCH) as [E|NE]; intros EA0; [exact E| discriminate]. }
          unfold abatches in ABL. rewrite QL, QQ in ABL. apply abatches_to_app in ABL; [| exact LNl]. destruct ABL as [ABl ABz].
          cbn [abatches_to qaddrs map hd] in ABz. destruct ABz as [(Z1 & Z2 & Z3 & Z4 & Z5 & Z6) _].
          rewrite QL, QQ. apply abatches_to_app; [exact LNl|]. split.
          + cbn [qaddrs map hd]. eapply abatches_to_frame; [exact MUn | exact WM | exact ABl |].
            intros q Hq. assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; left; rewrite QQ; apply in_or_app; left; exact Hq).
            assert (NEq : abatch_addr L (qb_slot q) <> lst).
            { rewrite QLST. intros E. apply in_split in Hq. destruct Hq as (qs1 & qs2 & EQl).
              apply (bslots_nodup_split L st X Q CP qs1 q qs2 qz (q_glob Q)); [rewrite QQ, EQl; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; reflexivity|].
              pose proof (bslot_range L st X Q WF CP q INq). pose proof (bslot_range L st X Q WF CP qz ltac:(apply in_or_app; left; rewrite QQ; apply in_or_app; right; left; reflexivity)).
              unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia. }
            apply BFR; [exact INq | exact NEq |].
            destruct GLF as [[_ E]|(GD & GQL & [Z0|((qg & Hqg & Eqg) & _)])]; [rewrite E; exact NEq| rewrite Z0; destruct (BGEO q INq) as (_ & _ & F3 & _); clear -F3 RES RHI; lia|].
            rewrite Eqg. intros E. apply in_split in Hq. destruct Hq as (qs1 & qs2 & EQl). apply in_split in Hqg. destruct Hqg as (gs1 & gs2 & EQg).
            apply (bslots_nodup_split L st X Q CP qs1 q (qs2 ++ [qz] ++ gs1) qg gs2); [rewrite QQ, EQl, EQg; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; reflexivity|].
            pose proof (bslot_range L st X Q WF CP q INq). pose proof (bslot_range L st X Q WF CP qg ltac:(apply in_or_app; right; rewrite EQg; apply in_or_app; right; left; reflexivity)).
            unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia.
          + cbn [abatches_to]. split; [| exact I].
            unfold abatch_cells. cbv zeta. change (hd (abatch_addr L k24) (qaddrs L [])) with (abatch_addr L k24). rewrite <- QLST.
            split; [rewrite FULL; exact OLD1|]. split; [exact OLD2|]. split; [| split; [exact Z4| split; [exact Z5| exact Z6]]].
            rewrite FULL. replace (Q_BATCH_BYTES - 24 - 8 * Q_BATCH) with 0 by reflexivity. unfold Q_BATCH. apply junk_nil; (destruct LSTF as [Z0|(_ & _ & _ & F3 & F4)]; [clear -Z0; lia | atop_facts; clear -F3 F4 RES RHI; lia]). }
      (* [comment removed for export] *)
      assert (ABN' : abatch_cells L m' nbt qn 0).
      { unfold abatch_cells. cbv zeta. subst nbt qn. cbn [qb_slot qb_ks b_size b_count b_chunks]. rewrite qhdrs_cons. cbn [qhdrs app map qhdr]. rewrite QH.
        split; [exact NBc|]. split; [exact NAc|]. split; [exists bs; unfold Q_BATCH_BYTES; exact NJc|]. split; [reflexivity|]. split; [reflexivity| unfold Q_BATCH; clear; lia]. }
      assert (ABL' : abatches_to L m' (a_qloc st ++ [nbt]) (q_loc Q ++ [qn]) 0).
      { apply abatches_to_app; [exact LN1|]. split; [cbn [qaddrs map hd]; subst qn; cbn [qb_slot]; exact ABO'|]. cbn [abatches_to]. split; [exact ABN'| exact I]. }
      assert (CP2 : qcoupled L st2 X' (mkQConc (q_loc Q ++ [qn]) (q_glob Q) true (q_pend Q))).
      { subst X' qn nbt. rewrite ?EA. unfold xfreeS. cbv iota beta.
        apply (qcoupled_new_sec L st X Q mb ms n WF CP st2 k24 (c_count (get_cls st K_BATCH_CLASS)) (n + 8192) true 0 eq_refl POS NK24 QL2 QG2). }
      destruct (Z.lt_ge_cases Q_CACHE (a_qloc_bytes st2)) as [DR|NDRN]; [| exfalso; clear -NDRN REC1; lia].
      + (* [comment removed for export] *)
        destruct (DRN DR) as (QL3 & QB3 & QG3 & QGB3).
        assert (GD : g_drain g = true) by (rewrite GDR; apply Z.ltb_lt; rewrite <- QB2; exact DR).
        exists (mkQConc [] (q_glob Q ++ (q_loc Q ++ [qn])) true (q_pend Q)). cbn [q_loc q_glob q_ia q_pend].
        split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
        rewrite QL3, QB3, QG3, QGB3, QL2, QG2, QB2, QGB2.
        split; [| split].
        * split; [cbn [length qfirst qlast qaddrs map hd last Z.of_nat]; exact QC'| exact I].
        * split.
          -- rewrite length_app, Nat2Z.inj_add, <- GNB. rewrite length_app. cbn [length]. rewrite Nat2Z.inj_add. change (Z.of_nat 1) with 1.
             rewrite qlast_app by (intros Enil; apply app_eq_nil in Enil; destruct Enil as [_ Enil]; discriminate). rewrite QLST'.
             assert (FE : qfirst L (q_glob Q ++ q_loc Q ++ [qn]) = (if g_full g then g_fst g else qfirst L (q_loc Q ++ [qn]))).
             { rewrite GFU, GFST. destruct (a_qglob st) eqn:QG0.
               - replace (q_glob Q) with (@nil qbatchc) by (destruct (q_glob Q); [reflexivity| cbn in LN2; discriminate]). reflexivity.
               - apply qfirst_app. destruct (q_glob Q); [cbn in LN2; discriminate| discriminate]. }
             rewrite FE, <- GQB. exact GC'.
          -- unfold abatches. apply abatches_to_app; [exact LN2|]. split.
             ++ (* [comment removed for export] *)
                rewrite hd_qaddrs by (intros Enil; apply app_eq_nil in Enil; destruct Enil as [_ Enil]; discriminate).
                destruct (a_qglob st) as [|bg0 lg0] eqn:QG0.
                ** replace (q_glob Q) with (@nil qbatchc) by (destruct (q_glob Q); [reflexivity| cbn in LN2; discriminate]). exact I.
                ** rewrite <- QG0 in *.
                   assert (GNE : a_qglob st <> []) by (rewrite QG0; discriminate).
                   assert (QG : a_qglob st = removelast (a_qglob st) ++ [List.last (a_qglob st) dummy_batch]) by (apply app_removelast_last; exact GNE).
                   assert (LQg : (0 < length (q_glob Q))%nat) by (rewrite LN2, QG0; cbn; clear; lia).
                   assert (QQg : q_glob Q = removelast (q_glob Q) ++ [List.last (q_glob Q) dummy_qb]) by (apply app_removelast_last; destruct (q_glob Q); [cbn in LQg; clear -LQg; lia| discriminate]).
                   set (lg := removelast (a_qglob st)) in *. set (blg := List.last (a_qglob st) dummy_batch) in *.
                   set (qg := removelast (q_glob Q)) in *. set (qgz := List.last (q_glob Q) dummy_qb) in *.
                   assert (LNg : length qg = length lg) by (rewrite QQg, QG, !length_app in LN2; cbn in LN2; clear -LN2; lia).
                   rewrite QG, QQg in ABG. apply abatches_to_app in ABG; [| exact LNg]. destruct ABG as [ABg ABgz].
                   cbn [abatches_to qaddrs map hd] in ABgz. destruct ABgz as [(Y1 & Y2 & Y3 & Y4 & Y5 & Y6) _].
                   assert (QGLST : qlast L (q_glob Q) = abatch_addr L (qb_slot qgz)) by (rewrite QQg; apply qlast_app1).
                   rewrite GFU in GLN. rewrite ?QG0 in GLN. cbv iota beta in GLN. rewrite GL, QGLST in GLN.
                   rewrite QG, QQg. apply abatches_to_app; [exact LNg|]. split.
                   +++ cbn [qaddrs map hd]. eapply abatches_to_frame; [exact MUn | exact WM | exact ABg |].
                       intros q Hq. assert (INg : In q (q_glob Q)) by (rewrite QQg; apply in_or_app; left; exact Hq).
                       assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; right; exact INg).
                       assert (NEg : abatch_addr L (qb_slot q) <> abatch_addr L (qb_slot qgz)).
                       { intros E. apply in_split in Hq. destruct Hq as (gs1 & gs2 & EQg).
                         apply (bslots_nodup_split L st X Q CP (q_loc Q ++ gs1) q gs2 qgz []); [rewrite QQg, EQg; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; reflexivity|].
                         pose proof (bslot_range L st X Q WF CP q INq). pose proof (bslot_range L st X Q WF CP qgz ltac:(apply in_or_app; right; rewrite QQg; apply in_or_app; right; left; reflexivity)).
                         unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia. }
                       apply BFR; [exact INq | exact (GNL q INg) | rewrite EGL; unfold dk_glst; rewrite GD, GL, QGLST; exact NEg].
                   +++ cbn [abatches_to]. split; [| exact I].
                       (* [comment removed for export] *)
                       unfold abatch_cells. cbv zeta. change (hd (qfirst L (q_loc Q ++ [qn])) (qaddrs L [])) with (qfirst L (q_loc Q ++ [qn])).
                       assert (GLS : gl = abatch_addr L (qb_slot qgz)) by (rewrite EGL; unfold dk_glst; rewrite GD, GL, QGLST; reflexivity).
                       assert (INgzg : In qgz (q_glob Q)) by (rewrite QQg; apply in_or_app; right; left; reflexivity).
                       assert (INgz : In qgz (q_loc Q ++ q_glob Q)) by (apply in_or_app; right; exact INgzg).
                       pose proof (GNL qgz INgzg) as NGL.
                       destruct (BGEO qgz INgz) as (_ & _ & F3 & F4). pose proof (BLST qgz INgz NGL) as DL.
                       pose proof (KDIS qgz INgz eq_refl) as DE.
                       assert (D8 : forall A8 kk, abatch_addr L (qb_slot qgz) + 8 <= A8 -> A8 + kk <= abatch_addr L (qb_slot qgz) + 8192 -> 0 <= kk ->
                                  disjoint_from (WfS (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) A8 kk).
                       { intros A8 kk HA HK KK0. apply Kres; clear -F3 F4 RES RHI DL DE EEB GLS HA HK KK0; lia. }
                       pose proof Y1 as Y1'. rw_split Y1' 1%nat YN YR.
                       eapply cells_frame in YR; [| exact MUn | exact WM | cbn [cells_size csize Nat.add]; apply D8; clear; lia].
                       rw_join GLN YR YH.
                       split; [exact YH|]. split; [| split; [| split; [exact Y4| split; [exact Y5| exact Y6]]]].
                       --- eapply u64arr_frame; [exact Y2 | exact MUn | exact WM |]. rewrite length_map, qhdrs_length by exact Y5. rewrite <- Y4.
                           apply D8; unfold Q_BATCH in Y6; clear -Y6; lia.
                       --- eapply junk_frame; [exact Y3 | exact MUn | exact WM |]. intros Hp. apply D8; unfold Q_BATCH, Q_BATCH_BYTES in *; clear -Y6 Hp; lia.
             ++ exact ABL'.
        * exact (qcoupled_drain L st2 st' X' (mkQConc (q_loc Q ++ [qn]) (q_glob Q) true (q_pend Q)) true CP2 QL3 QG3). }

  (* [comment removed for export] *)
  assert (HBK : forall blk, In blk LB -> disjoint_from (WfS (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) (ab_addr blk) (ab_size blk)).
  { intros [[q|cls] A' n'] Hin; cbn [ab_addr ab_size].
    - destruct (proj1 BL q A' n' Hin) as [(b & Hb & Sb & Ub & Nb)|(mb' & msz' & Lp & EUA & Gs)].
      + destruct (busy_slot_range L st X b WF Hb) as [HCb HKb].
        pose proof (awf_fits L st X b WF Hb) as FIT. unfold xb_fits in FIT. rewrite Sb in FIT.
        pose proof (busy_of_In_nodup L st X b WF Hb) as BOF.
        unfold xb_user, xb_alloc in Ub. subst A' n'.
        set (cb := xb_class b) in *. set (kb := xb_slot b) in *.
        pose proof (slot_geo L st X cb kb ALO WF HCb HKb) as (T16 & TM16 & TAL & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & _).
        assert (DQ : forall q', In q' (q_loc Q ++ q_glob Q) ->
            aslot_addr L cb kb + size_of_class cb <= abatch_addr L (qb_slot q') \/ abatch_addr L (qb_slot q') + 8192 <= aslot_addr L cb kb).
        { intros q' Hq'. destruct (bslot_busy L st X Q CP q' Hq') as (yq & Hyq & Syq & Cyq & Kyq).
          assert (NE : cb <> K_BATCH_CLASS \/ kb <> qb_slot q').
          { destruct (Z.eq_dec cb K_BATCH_CLASS) as [E1|NE0]; [| left; exact NE0]. right. intros E2.
            pose proof (busy_of_In_nodup L st X yq WF Hyq) as BY. rewrite Cyq, Kyq, <- E1, <- E2, BOF in BY. injection BY as EE. subst yq. rewrite Sb in Syq. discriminate. }
          pose proof (slots_sep_any L st X cb kb K_BATCH_CLASS (qb_slot q') ALO WF HCb (K24) HKb (bslot_range L st X Q WF CP q' Hq') NE) as D.
          rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
        assert (DK24 : enq_is_app st = false -> aslot_addr L cb kb + size_of_class cb <= abatch_addr L k24 \/ abatch_addr L k24 + 8192 <= aslot_addr L cb kb).
        { intros EAx. destruct (NEWF EAx) as (_ & NBk & KK & _).
          assert (NE : cb <> K_BATCH_CLASS \/ kb <> k24).
          { destruct (Z.eq_dec cb K_BATCH_CLASS) as [E1|NE0]; [| left; exact NE0]. right. intros E2. rewrite <- E1, <- E2, BOF in NBk. discriminate. }
          pose proof (slots_sep_any L st X cb kb K_BATCH_CLASS k24 ALO WF HCb (K24) HKb KK NE) as D.
          rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
        assert (DL : lst = 0 \/ aslot_addr L cb kb + size_of_class cb <= lst \/ lst + 8192 <= aslot_addr L cb kb).
        { destruct LSTF as [Z0|((q' & Hq' & Eq') & _)]; [left; exact Z0| right]. rewrite Eq'. apply DQ. apply in_or_app; left; exact Hq'. }
        assert (DE : eb = lst \/ aslot_addr L cb kb + size_of_class cb <= eb \/ eb + 8192 <= aslot_addr L cb kb).
        { destruct EBK as [E|[EAx E]]; [left; exact E| right]. rewrite E. exact (DK24 EAx). }
        assert (DG : gl = lst \/ gl = 0 \/ aslot_addr L cb kb + size_of_class cb <= gl \/ gl + 8192 <= aslot_addr L cb kb).
        { destruct GLF as [[_ E]|(_ & _ & [Z0|((q' & Hq' & Eq') & _)])]; [left; exact E| right; left; exact Z0| right; right].
          rewrite Eq'. apply DQ. apply in_or_app; right; exact Hq'. }
        apply Kres; [clear -P5 RSP FIT; lia | clear -P6 RSP FIT; unfold K_SPACE_SIZE in *; lia | clear -FIT; lia
                    | clear -DL FIT P5 RSP RES RHI; lia | clear -DE DL FIT P5 RSP RES RHI; lia | clear -DG DL FIT P5 RSP RES RHI; lia].
      + (* [comment removed for export] *)
        assert (NEc : CSec mb' msz' n' <> ch).
        { intros E. apply NOTL. exists q. rewrite <- E. exact Lp. }
        assert (INc : In (CSec mb' msz' n') cs) by (eapply Permutation_in; [apply Permutation_sym; exact PCS| right; eapply live_sec_in; exact Lp]).
        pose proof INcs as INs.
        destruct WD as [_ DJ]. destruct (DJ _ _ INc INs NEc) as [Dc|Dc]; unfold ch in Dc; cbn [sec_mb sec_ms] in Dc.
        all: cbn [sec_wf1] in Gs; destruct Gs as (Gs1 & Gs2 & Gs3 & Gs4 & Gs5 & Gs6 & (Ct & Cc & Cr & Cp & Cn & Cs & Cf & Cd)).
        all: pose proof (sec_facts n' ltac:(clear -Gs5; lia) Gs6) as SF; subst A'; unfold SEC_UOFF, K_HIGH_MEM in *.
        all: unfold ablk, KLS, AIMG_HI in Gs2.   (* [comment removed for export] *)
        all: apply Kobj; [clear -Gs2 Gs4 Gs5 SF; lia| clear -Gs3 Gs4 Gs5 SF; lia| clear -Gs5; lia| clear -Gs4 Gs5 SF Ct; lia| clear -Gs4 Gs5 SF Cr; lia| clear -Gs4 Gs5 SF Cn; lia| clear -Gs4 Gs5 SF Cs; lia| clear -Gs4 Gs5 SF Dc; lia].
    - destruct (FKD cls A' n' Hin) as (K1 & K2 & K3). unfold K_HIGH_MEM in *.
      pose proof D_t_f as DTF; unbox DTF. pose proof D_f_res as DFR; unbox DFR. pose proof D_n_f as DNF; unbox DNF. pose proof D_s_f as DSF; unbox DSF.
      apply Kobj; [clear -K1 K3 FKO FKi FBND; lia | clear -K3 FKO FKi FBND; lia | exact K2 | clear -K1 K3 DTF; lia
                  | clear -K1 K3 DFR; lia | clear -K1 K3 DNF; lia | clear -K1 K3 DSF; lia | clear -K1 K3 SC_f; lia]. }
  assert (HFS : forall cls FA sz, In (mkABlock (ABFake cls) FA sz) LB -> forall a', FA <= a' < FA + sz ->
      disjoint_from (WfS (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) (shad a') 1).
  { intros cls FA sz Hin a' Ha'.
    destruct (FKD cls FA sz Hin) as (K1 & K2 & K3). unfold K_HIGH_MEM in *.
    assert (FAL8 : al_fake L mod 8 = 0) by (destruct FKO as [F8 _]; clear -F8; Z.div_mod_to_equations; lia).
    apply Kshad; [rewrite shad_div; unfold ASHOFF, AIMG_HI; clear -K1 FKO FKi FBND Ha'; Z.div_mod_to_equations; lia
                 | rewrite shad_div; unfold ASHOFF; clear -K3 FKO FKi FBND Ha'; Z.div_mod_to_equations; lia | clear; lia |].
    rewrite SHE. destruct SC_f as [D|D].
    - right. pose proof (shad_sep _ _ _ D MAL8) as HH. rewrite shlen_div in HH.
      pose proof (shad_mono (al_fake L) a' ltac:(clear -K1 Ha'; lia)) as MM. clear -HH MM SHL. lia.
    - left. pose proof (shad_sep _ _ _ D FAL8) as HH. rewrite (shad_div a'), (shad_div (al_fake L)), shlen_div in *.
      clear -HH Ha' K3 FAL8. Z.div_mod_to_equations. lia. }
  (* [comment removed for export] *)
  destruct HQ' as (Q' & QL0 & QIA & QPD & TC' & GCc & CPL).
  destruct (DRN ltac:(first [exact REC1 | rewrite SB1; exact REC1' | (let H := fresh in pose proof REC1' as H; rewrite <- SB1 in H; exact H)])) as (QL3f & QB3f & QG3f & QGB3f).
  exists X', (qr_of_q Q'), m', id, t0', t1', t2', xs0, xs1, xs2, xs3, xs4, xs5, xs6, ps0, ps1, ps2, ps3, ps4, ps5, spv, a3', a4', a5', a6', a7', t3', t4', t5', t6', csA, csT, junk2.
  split; [rewrite TP; reflexivity|].
  split.
  { (* [comment removed for export] *)
    split; [exact WF'|]. split; [exact RT'|]. split; [exact INST'|]. split; [exact THR'|]. split; [exact CLS'|].
    split.
    { cbn [ah_quar AHc AHq]. unfold AQdr, qr_of_q. cbn [qr_loc qr_glob qr_ia qr_tmp qr_pendb qr_pend qr_qpend map fst snd].
      split; [exact QK'|]. split; [exact MX'|]. split; [exact TC'|]. split; [exact GCc|].
      split; [exact I|]. split; [rewrite QIA; exact IA'|]. split; [apply qcoupled_rec_of_q; exact CPL|].
      split; [exact NUM'| constructor]. }
    split.
    { cbn [ah_sec AHc AHq]. replace (csx st' (qr_of_q Q')) with (sec_chunks_of st') by (unfold csx, inflight, secsT, qr_of_q; cbn [qr_tmp qr_pend map fst snd qentries esecs flat_map app]; rewrite app_nil_r; reflexivity).
      exact HS'. }
    split; [exact DEP'|]. split; [exact HRO'|]. split; [exact HRT2'|]. split; [exact AVL'| exact RT3']. }
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split. { pose proof ARNG as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & RCl & RPA & RSC & RPSH).
           unfold arng. repeat (split; [assumption|]). split; [| split; [rewrite ENRES; exact RPA| split; [eapply RSEC_perm; [apply Permutation_sym; exact PD| exact RSCS]| exact RPSH]]].
           intros c' Hc'. cbv zeta. destruct (Z.eq_dec c' K_BATCH_CLASS) as [->|NE]; [rewrite M24a, M24d; exact (RCl K_BATCH_CLASS Hc')| rewrite (GCo' c' NE); exact (RCl c' Hc')]. }
  split; [exact BL'|]. split; [exact HFK'|].
  split; [rewrite QGB3f;   (* [comment removed for export] *)
           apply (Z.le_lt_trans _ (a_qglob_bytes st + (a_qloc_bytes st + ek_delta ek n))); [apply Z.eq_le_incl; unfold st2, st1; f_equal; [exact SB2| exact SB1]|];
           clear -NC NM ED0 NQM NB; unfold Q_MAX, Q_CACHE in *; lia|].
  split; [exact QL3f|]. split; [exact QB3f|].
  split; [exact MI'|]. split; [exact ST'|].
  split. { eapply (aheap_pres_freeS CI); [exact KF | exact CI_OK | exact MUn | exact WM | exact HBK | exact HFS]. }
  split; [exact IDR|].
  split; [exact FRP|]. split; [exact FRA|]. split; [exact SZA|]. split; [exact FRT|]. split; [exact SZT|]. exact FRS.
Qed.
End S.
End CANSEC1.
