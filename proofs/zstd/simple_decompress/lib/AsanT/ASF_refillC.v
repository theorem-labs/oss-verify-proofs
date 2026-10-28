(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF ITreeA StepF SysStepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import ASecFacts ASec ASecFrame BImg AProto ABase ABytes AQConst AKitQ AMalloc_iface ADepot_iface ARep ARepQ ARepQP ALayout AHeapP ARepKit ARepFrame
     AKit AKit2 AModelFacts AFreeModel AFreeModelR AFreeRep AFreeGeo AFreeRead ARefill_iface
     F_apoison F_aalloc_s F_aalloc1 F_afree_tail F_afree_icpt F_aenqueueR F_afree_tailR F_afree_icptR F_afree_arep F_afree_arepR
     ASF_kit ASF_read ASF_fast ASF_refill ASecRecycle_iface ASecRecycle ARecyc1P ARecGeo F_adorec F_aqrec_iface F_aqrec AQrecP
     F_afreeC_iface F_afree_icptC F_afree_icptRC AFreeC_kit_iface AFreeModelC ASF_C_iface ARepQR ARepQD ASecStore.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import LiaTier0U.
Local Ltac Stdlib.micromega.Lia.lia ::= lia_tier0u.
Local Ltac OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib.StoreFast.tlia ::= tlia_u.
Local Ltac OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib.StoreFast.lia3 ::= lia3_u.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.

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

Lemma sec_same0_of : forall st st', sec_same st st' -> sec_same0 st st'.
Proof.
  intros st st' (EN & ER & EP & EL & _). split; [exact EN|]. split; [exact ER|]. split; [exact EP|].
  intros [c n0|mb ms n0] Hs; [discriminate|]. unfold sec_live. split; intros [q Hq]; exists q; [apply (proj1 (EL q mb ms n0)); exact Hq| apply (proj2 (EL q mb ms n0)); exact Hq].
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
Hypothesis DEPD : depot_frameD_law (ADEPOT DI).
Hypothesis AFKD : fake_frameD_law AFK.
Hypothesis MID : mid_stmtS DI AFK CI.
Hypothesis STORE_RC : store_freeSRC_stmt DI AFK CI.
Hypothesis REFILL : forall cs Q1, refill_stmt (AHSm DI AFK cs Q1).
Hypothesis BACK : afree_back_stmt DI AFK CI.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma AHr_laws : forall R cs, ahole_laws (ARecyc1P.AHr ASECc (ADEPOT DI) AFK R cs).
Proof.
  intros R cs. destruct HL as [HQF HSF HDF HFF HFB].
  constructor; cbn [ah_quar ah_sec ah_depot ah_fake ARecyc1P.AHr AHQ] in *; try assumption.
  - intros L st st' X X' m m' W AQ MU WM UT QS. eapply AQdr_frame; eassumption.
  - intros L st st' X X' m m' W AS MU WM SU SS. eapply asecc_frame; [exact AS| exact MU| exact WM| exact SU| apply sec_same0_of; exact SS].
Qed.

Lemma ASECc_wf1' : forall cs L st X m, ASECc cs L st X m -> Forall (sec_wf1 L) cs.
Proof. intros cs L st X m ((_ & _ & _ & _ & _ & WF1 & _) & _). exact WF1. Qed.
Lemma ASECc_disj' : forall cs L st X m, ASECc cs L st X m -> sec_disjoint cs.
Proof. intros cs L st X m ((_ & _ & _ & _ & _ & _ & WD) & _). exact WD. Qed.
Lemma ASECc_nres' : forall cs L st X m, ASECc cs L st X m -> 0 <= a_nres st /\ 8 * a_nres st <= 8388608.
Proof. intros cs L st X m ((_ & _ & (_ & NR) & _) & _). lia. Qed.
Lemma ASECc_qglob' : forall cs L st X X' m g gb, ASECc cs L st X m -> ASECc cs L (set_qglob g gb st) X' m.
Proof. intros cs L st X X' m g gb HS. exact HS. Qed.
Lemma RSEC_app' : forall a b RNG, RSEC (a ++ b) RNG <-> RSEC a RNG /\ RSEC b RNG.
Proof. intros. unfold RSEC. apply Forall_app. Qed.
Lemma RSEC_arng' : forall L RNG st, arng L RNG st -> RSEC (sec_chunks_of st) RNG.
Proof. intros L RNG st (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RS & _). exact RS. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem afree_sec_recrefill : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (p : aptr) (A n lo : Z) (tr : list Z) (mb ms : Z),
  (* [comment removed for export] *)
  (a_live st) !! p = Some (CSec mb ms n) -> n <= Q_MAX ->
  enq_is_app st = false -> c_count (get_cls st K_BATCH_CLASS) = 0 ->
  Q_CACHE < a_qloc_bytes st + (n + 8192) -> Q_MAX < a_qglob_bytes st + (a_qloc_bytes st + (n + 8192)) ->
  (* [comment removed for export] *)
  AHEAP_P (AHQ DI ASEC_of AFK) L RNG st LB m -> In (HB p A n) LB ->
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 A ->
  aunw m L RNG lo AFREE_PC sp s0 ra tr ->
  bv_unsigned s0 <> bv_unsigned sp + 8 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AFREE_PC ->
  bv_unsigned sp mod 16 = 0 ->
  rng RNG lo (bv_unsigned sp - lo) ->
  implS bsegs RNG (aembed ATOP (afree st (Some p)))
        (epostF (afree_post CI (AHEAP_P (AHQ DI ASEC_of AFK)) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB p lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AFREE_SYM) fc None m (seg_rom bsegs)).
Proof.
  intros until ms. intros LIVE NQM EA CNT0 QC1 REC AH HIN MI ST BOT LO TP Ha0 AUNW S0NE RA4 RANE SP16 RSTK.
  assert (UNWX : exists trt, afree_unw RNG lo m (al_top L) sp s0 ra trt /\ In (AFREE_PC :: trt) (al_U L)).
  { destruct AUNW as [(BT & UC & LTR & TRU & RTOP)|(TOPLE & SPLT & TRU)]; [exists (bv_unsigned ra :: tr); split; [left; exists tr; split; [reflexivity|]; split; [exact UC|]; split; [exact LTR|]; split; [exact BT| exact RTOP]| exact TRU] | exists (@nil Z); split; [right; auto| exact TRU]]. }
  destruct UNWX as (trt & FUNW & TRU).
  set (st1 := set_live (delete p (a_live st)) st).
  destruct AH as (ALO & ARNG & [X [AR BL]] & HFK).
  pose proof AR as AR0. destruct AR0 as (WF & RT & INST & THR & CLS & HQ & HS & HD & HRO & HRT2 & AVL & RT3).
  cbn [ah_quar ah_sec ah_depot F_afree_arep.AHQ] in HQ, HS, HD. destruct HQ as [Q AQ].
  pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVEB & FRESH & UNIQ).
  (* [comment removed for export] *)
  destruct (freed_block_sec L st X LB p mb ms n A n WF BL HIN LIVE) as (EAu & _ & WFch).
  destruct (sec_wf1_facts' L mb ms n WFch) as (MAL & MLO & MCE & MSE & NB & RZ & MSB & MSAL & NMS & NS0 & SCL & NPR & N6).
  pose proof (ablk_lin _ _ MLO) as (ML1 & ML2 & ML3 & ML4). unfold AIMG_HI in ML1. pose proof (ablk_int _ _ MLO) as (kM & KAM & KBM & KEM & KCM & KDM).   (* [comment removed for export] *)
  pose proof SCL as (SC_t & SC_c & SC_r & SC_p & SC_n & SC_st & SC_f & SC_d).
  destruct (read_chunk_sec _ L st X m p mb ms n HS (Permutation_refl _) LIVE)
    as (order & i & b1 & cx & uw & PO & NTH & IL & LENO & WF1o & WDo & U64 & JK & PER & CH & H1 & H5 & B1 & B3 & CX & HUW & UJ & S1 & S2 & S3).
  cbv zeta in H5, HUW, UJ, S2, S3.
  set (hm := mb + 6128) in *.
  (* [comment removed for export] *)
  pose proof ARNG as ARNG0. destruct ARNG0 as (RIMG & RT4 & RCTX & RNO & RSTO & RRI & RFK & RSFK & RDT & RCLS & RPA & RSECS & RPSH).
  pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4).
  pose proof TL1 as TL1u. pose proof TL4 as TL4u. unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in TL1u, TL4u.   (* [comment removed for export] *)
  pose proof (alayout_ctx L ALO) as (CL1 & CL2 & CL3 & CL4 & CL5).
  pose proof (alayout_depot L ALO) as (DL1 & DL2 & DL3 & DL4 & DL5 & DL6 & DL7 & DL8 & DL9 & DL10).
  pose proof (alayout_stack L ALO) as (STK1 & STK2 & STK3).
  pose proof (alayout_space L ALO) as (SP1 & SP2 & SP3 & SP4).
  pose proof (ao_space L ALO) as RSP. pose proof (ao_res L ALO) as RES. unfold aobj in RES. pose proof (ao_res_hi L ALO) as RHI. unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in RES.   (* [comment removed for export] *)
  assert (SP47 : bv_unsigned sp < 2^47) by (eapply afree_unw_sp47; [exact FUNW| exact STK2]).
  pose proof (rup8_facts n ltac:(clear -NB; lia)) as (RUP & RUP8 & RUPS).
  assert (SHGEO : shad (hm + 16) = shad mb + 768 /\ shlen (rup n 8) <= ms / 8 - 768 /\ 0 < shlen (rup n 8) /\ hm + 16 + rup n 8 <= mb + ms
                  /\ 2148256256 <= shad mb /\ shad mb + ms / 8 <= 17594332446720).   (* [comment removed for export] *)
  { subst hm. rewrite !shad_div, RUPS. unfold ASHOFF. pose proof (sec_facts n ltac:(clear -NB; lia) NPR) as (_ & _ & _ & RS1 & _ & NSE & _).
    unfold K_HIGH_MEM in *. pose proof atop_range as AR8. clear -MAL RUP RUP8 RS1 NSE NMS N6 NB ML1 ML3 MCE MSAL AR8. Z.div_mod_to_equations. lia. }
  destruct SHGEO as (SHE & SHL & SHP & UBS & SHLO & SHHI).
  assert (MAL8 : mb mod 8 = 0) by (clear -MAL; Z.div_mod_to_equations; lia).
  assert (HM0' : ablk hm (hm + 24)) by (subst hm; eapply ablk_sub; [exact MLO| clear; lia| clear -NMS MSB; lia]).   (* [comment removed for export] *)
  (* [comment removed for export] *)
  assert (HMSEPg : forall s Xs, awf L s Xs -> forall kk, 0 <= kk < ndist s K_BATCH_CLASS -> hm + 24 <= abatch_addr L kk \/ abatch_addr L kk + 8192 <= hm).
  { intros s Xs WFs kk KK. destruct WFs as (_ & _ & _ & _ & _ & PERCs & _).
    destruct (PERCs K_BATCH_CLASS (K24)) as (Q1' & Q2' & _).
    pose proof (slot_in_region L s K_BATCH_CLASS kk ltac:(rewrite size_of_class_24; lia) (proj1 Q1') KK) as (P5 & P4 & _).
    rewrite size_of_class_24 in P4. subst hm. unfold abatch_addr, aregion, K_REGION, K_FREEARR_OFF, K_BATCH_CLASS in *.
    clear -P5 P4 Q1' Q2' RSP SC_r MSB. lia. }
  pose proof (HMSEPg st X WF) as HMSEP.
  (* [comment removed for export] *)
  assert (IN : In (CSec mb ms n) (sec_chunks_of st)) by (eapply Permutation_in; [exact PO| eapply nth_error_In; exact NTH]).
  pose proof (proj1 (Forall_forall _ _) RSECS _ IN) as [RMB RSH]. cbn [sec_mb sec_ms] in RMB, RSH.
  (* [comment removed for export] *)
  pose proof RT as RT0.
  destruct RT0 as (GPG & GOT & GOT80 & RIC & LS1 & REAL & IMAX4 & FLG5 & FLG & HPP & SHB & CANP & TI & TK & INI2 & LAY & MCS & OOM3
                    & PGC & HK2 & CF8 & CF34 & CSMT & T88 & TSD & LS2 & CT8 & CT).
  pose proof INI2 as INI. rw_split INI 1%nat INI1 INIx. clear INIx.
  pose proof OOM3 as OOM. rw_split OOM 2%nat OOMx RSS0. clear OOMx.
  pose proof IMAX4 as IMAX. rw_split IMAX 3%nat IMAX3 IMAXx. clear IMAXx.
  pose proof HK2 as HK. rw_split HK 1%nat HK1 HKF.
  pose proof GOT as GOT6. rw_split GOT 1%nat GOTa GOTr. rw_split GOTr 1%nat GF GOTx. clear GOTa GOTx.
  destruct THR as (T0 & T40 & CACHES & CSTATS & [sj [STATS LSJ]] & UNW).
  destruct (CACHES K_BATCH_CLASS (K24)) as [tail (CR & CHc & LCH)].
  replace (acache_addr L K_BATCH_CLASS) with (al_t L + 2128) in CR by (unfold acache_addr, K_BATCH_CLASS; lia).
  rewrite CNT0 in CR.
  (* [comment removed for export] *)
  pose proof AQ as AQ0. destruct AQ0 as ([QK MX] & [QC ABL] & [GCQ ABG] & (FL & IAS & IAM) & CP & NUM).
  destruct NUM as (NB1 & NB2 & NF & NC & NM).
  pose proof (batches_bytes_lb (a_qloc st) ltac:(apply Forall_app in NF; exact (proj1 NF))) as LLB. rewrite <- NB1 in LLB.
  (* [comment removed for export] *)
  pose proof (read_lastS (AHQ DI ASEC_of AFK) L st X Q m RNG hm ALO ARNG AR AQ HM0' HMSEP EA) as (FULL & DTL & DHL & DNL & DSL & LST64).
  cbv zeta in FULL.
  set (full := match a_qloc st with [] => false | _ :: _ => true end) in *.
  set (lst := qlast L (q_loc Q)) in *.
  set (bsz := b_size (List.last (a_qloc st) dummy_batch)) in *.
  set (hs := map (Z_to_bv 64) (qhdrs L (b_chunks (List.last (a_qloc st) dummy_batch)) (qb_ks (List.last (q_loc Q) dummy_qb)))) in *.
  assert (FULL' : if full then 0 < Z.of_nat (length (a_qloc st)) /\ rw_cells bsegs m lst [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 1021)]
             /\ 0x10007fff8000 <= lst /\ lst + 8192 <= ATOP /\ u64arr bsegs m (lst + 24) hs /\ length hs = 1021%nat /\ rng RNG lst 8192
           else Z.of_nat (length (a_qloc st)) = 0 /\ lst = 0).
  { destruct full; [| exact FULL]. destruct FULL as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & _). repeat (split; [assumption|]). exact F7. }
  (* [comment removed for export] *)
  rewrite (afree_refill_eq st p (CSec mb ms n) LIVE ltac:(cbn [chunk_size]; exact NQM) EA CNT0). fold st1.
  (* [comment removed for export] *)
  assert (AB64 : forall q, In q (q_loc Q ++ q_glob Q) -> 0 <= abatch_addr L (qb_slot q) < 2^64).
  { intros q Hq. pose proof (bslot_geo L st X ALO WF (qb_slot q) (bslot_range L st X Q WF CP q Hq)) as (B0 & B1' & _). atop_facts. lia. }
  assert (LF64 : 0 <= qfirst L (q_loc Q) < 2^64).
  { destruct (qfirst_cases L (q_loc Q)) as [-> |(q & Hq & ->)]; [lia| apply AB64; apply in_or_app; left; exact Hq]. }
  assert (CEIL : ATOP <= lo) by (generalize BOT STK3; clear; intros; lia).
  (* [comment removed for export] *)
  unfold AIMG_HI, AFREE_STACK, UDEPTH, Q_MAX, Q_CACHE, K_HIGH_MEM, AREQMAX in *.
  (* [comment removed for export] *)
  box SC_t. box SC_c. box SC_r. box SC_p. box SC_n. box SC_st. box SC_f. box SC_d. box CL5. box DL7. box DL8. box DL9. box DL10. box DTL. box DHL. box DNL. box DSL.
  eapply implF_evtF.
  { eapply (free_to_refill_spec DI L (q_ia Q) full RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m
              (al_t L) (al_ctx L) hm n b1 cx lo (al_top L) (al_bot L)
              (Z.of_nat (length (a_qloc st))) (qfirst L (q_loc Q)) lst (a_qloc_bytes st) 0 bsz uw _ _ sj hs (block_shadow_bytes n) trt).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => first [exact ST | exact IAS]
         | |- ablk _ (_ + 16 + rup _ 8) => first [assumption | exact HM0' | (try subst hm; eapply ablk_sub; [exact MLO| clear; lia| clear -NMS MSB MSAL N6 NB; unfold rup; Z.div_mod_to_equations; lia])]   (* [comment removed for export] *)
         | |- mem_inv _ _ => exact MI
         | |- allocA_cells _ _ _ => unfold allocA_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
         | |- poison_cells _ => unfold poison_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
         | |- ADEPOT _ _ _ => exact HD
         | |- afree_unw _ _ _ _ _ _ _ _ => exact FUNW
         | |- In _ _ => exact TRU
         | |- u64arr _ _ _ _ => exact STATS
         | |- if _ then _ else _ => exact FULL'
         | |- _ = true -> _ => exact IAM
         | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact H5
         | |- rw_cells _ _ (shad _) _ => exact S2
         | |- rw_cells _ _ (_ + 80) _ => exact QC
         | |- rw_cells _ _ (_ + 2128) _ => exact CR
         | |- rw_cells _ _ (_ + 16) [C8 _] => exact HUW
         end.
    all: try lazymatch goal with
         | |- rw_cells _ _ _ [C8 _; C8 _; C8 _] => first [exact T0 | exact QK]
         | |- rw_cells _ _ _ _ => assumption
         | |- @eq word _ _ => first [exact TP | rewrite Ha0, EAu; subst hm; unfold SEC_UOFF; f_equal; clear; lia | reflexivity]
         | |- _ \/ _ => first [unboxed CL5 | unboxed DL7 | unboxed DL8 | unboxed DL9 | unboxed DL10 | unboxed DTL | unboxed DHL | unboxed DNL | unboxed DSL
                             | ub SC_t; clear -Y MSB; subst hm; lia | ub SC_c; clear -Y MSB; subst hm; lia | ub SC_n; clear -Y MSB; subst hm; lia | ub SC_st; clear -Y MSB; subst hm; lia]
         | |- rng _ (shad _) _ => rewrite SHE; eapply rng_sub; [exact RSH| clear; lia| clear -SHL; lia]
         | |- rng _ _ 24 => subst hm; eapply rng_sub; [exact RMB| clear; lia| clear -MSB; lia]
         | |- rng _ (al_ctx _) _ => eapply rng_sub; [exact RCTX| clear; lia| clear; lia]
         | |- rng _ _ _ => assumption
         | |- rng_aimg _ => exact RIMG
         end.
    all: try assumption.
    all: subst hm; unfold AIMG_HI, Q_MAX, Q_CACHE, Q_BATCH_BYTES, UDEPTH in *.
    all: try (generalize NB N6 NMS NQM MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MAL MSAL RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6
                         B1 CX LLB NC NM LF64 LST64 RA4 RUP; clear; intros; Z.div_mod_to_equations; lia).
    all: match goal with |- ?G => idtac "REMF" G end. }
  cbv beta. intros ms1 PTR.
  pose proof (MID L RNG full ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st LB X Q p mb ms n b1 cx A lo lst 0 bsz hs trt
              ALO ARNG AR AQ BL HFK LIVE HIN NQM H5 B1 B3 CX CEIL LO ms1 PTR) as (ARm & BLm & FKm & HPm).
  unfold free_to_refill_post in PTR.
  destruct PTR as (id & t0a & t1a & t2a & a4a & a5a & a6a & a7a & t3a & t4a & t5a & t6a & m1 & sj1 & tb1 & junk2 & j0
                   & -> & MUf & WMf & MIf & STf & IDR & HD1 & FC1 & SH1 & STATS1 & LSJ1 & UW1 & FL1 & IAS1 & IAM1 & SS1 & TB1 & LTB1 & FRS1 & FRP1 & FRE1 & LBS1 & DEP1).
  cbn [ms_mem MS] in ARm, FKm, HPm.
  (* [comment removed for export] *)
  set (Q1 := mkQConc (q_loc Q) (q_glob Q) true (q_pend Q)) in *.
  assert (PD1 : Permutation (CSec mb ms n :: sec_chunks_of st1) (sec_chunks_of st)).
  { apply (sec_chunks_of_delete_sec st st1 p mb ms n LIVE); [reflexivity| apply Permutation_refl]. }
  eapply (REFILL (sec_chunks_of st) Q1 _ (KB (CSec mb ms n)) _ L RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 st1 X K_BATCH_CLASS lo).
  all: try lazymatch goal with
       | |- alayout_ok _ => exact ALO
       | |- arng _ _ _ => apply (arng_sub L RNG st st1); [intros; reflexivity| reflexivity| intros cc Hcc; eapply Permutation_in; [exact PD1| right; exact Hcc]| exact ARNG]
       | |- AREP _ _ _ _ _ => exact ARm
       | |- mem_inv _ _ => exact MIf
       | |- stk _ _ _ _ => rewrite unsigned_lit by lia; exact STf
       | |- @eq word _ _ => first [exact TP | reflexivity | unfold acache_addr, K_BATCH_CLASS; f_equal; clear; lia | unfold AINSTANCE; reflexivity]
       | |- _ <= K_BATCH_CLASS < _ => exact (K24)
       | |- c_count _ = 0 => exact CNT0
       | |- _ <= _ => first [exact CEIL | rewrite ?unsigned_lit by lia; lia]
       | |- rng _ _ _ => rewrite unsigned_lit by lia; eapply rng_sub; [exact RSTK| lia| lia]
       end.
  all: match goal with |- forall _ _ _ _, refill_ret _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ -> _ => idtac | |- ?G => idtac "REMR" G end.
  intros st_r X' RNG' ms' RR. unfold refill_ret in RR.
  destruct RR as (FPLE & t0c & t1c & t2c & a1c & a2c & a3c & a4c & a5c & a6c & a7c & t3c & t4c & t5c & t6c & m' & -> & MUr & WMr & MIr & STr & ARr & ARNGr
                  & CINr & CNTr & MAXr & XBr & XCr & LIVEr & NEXTr & QLr & QBr & QGr & QGBr & NSECr & NRESr & GCr).
  rewrite ?unsigned_lit in MUr by lia. rewrite ?unsigned_lit in STr by lia.
  (* [comment removed for export] *)
  assert (EAr : enq_is_app st_r = false) by (unfold enq_is_app; rewrite QLr; exact EA).
  pose proof (enq_new_core (CSec mb ms n) st_r) as (_ & NG1 & NG2 & _ & NL1 & NL2 & _). cbn [chunk_size] in NL1, NL2.
  assert (ENr : st_enq st_r (CSec mb ms n) = enq_new st_r (CSec mb ms n)).
  { unfold st_enq. destruct (enq_app st_r (CSec mb ms n)) as [s'|] eqn:E; [| reflexivity]. exfalso.
    assert (EA1 : enq_is_app st_r = true) by (apply (proj2 (enq_is_app_spec st_r (CSec mb ms n))); eexists; exact E). congruence. }
  assert (QCr1 : Q_CACHE < a_qloc_bytes (st_enq st_r (CSec mb ms n))).
  { rewrite ENr, NL2, QBr. change (a_qloc_bytes st1) with (a_qloc_bytes st). unfold Q_CACHE, Q_BATCH_BYTES. generalize QC1; clear; intros; lia. }
  assert (RECr : Q_MAX < a_qglob_bytes (st_enq st_r (CSec mb ms n)) + a_qloc_bytes (st_enq st_r (CSec mb ms n))).
  { rewrite ENr, NG2, NL2, QBr, QGBr. change (a_qloc_bytes st1) with (a_qloc_bytes st). change (a_qglob_bytes st1) with (a_qglob_bytes st).
    unfold Q_CACHE, Q_MAX, Q_BATCH_BYTES. generalize REC; clear; intros; lia. }
  rewrite (KB_apop_rec_eq st_r (CSec mb ms n) EAr QCr1 RECr).
  replace (ret_pc (Z_to_bv 64 0x37f0c)) with (Z_to_bv 64 0x37f0c) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  (* [comment removed for export] *)
  pose proof (ad_t_res L ALO) as D_t_res. unfold adisj in D_t_res.
  destruct (PERC K_BATCH_CLASS (K24)) as (A24a & A24b & _).
  assert (ERI : aregion_info L K_BATCH_CLASS = al_space_beg L + 137438953472 + 3072) by (unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE, K_BATCH_CLASS; lia).
  assert (ER24 : aregion L K_BATCH_CLASS = al_space_beg L + 24 * 4294967296) by (unfold aregion, K_REGION, K_BATCH_CLASS; lia).
  assert (W6B : 2199023255552 <= shad (aregion L K_BATCH_CLASS + c_mapped_user (get_cls st K_BATCH_CLASS))
             /\ shad (aregion L K_BATCH_CLASS) + shlen K_REGION <= 17594333495296).
  { rewrite !shad_div, shlen_div. unfold ASHOFF, K_REGION. rewrite ER24. generalize SP1 SP2 A24a A24b. clear. unfold K_SPACE_SIZE, K_SPACE_EXTRA, K_FREEARR_OFF. change (2^37) with 137438953472. change (2^32) with 4294967296. change (2^41) with 2199023255552. intros. Z.div_mod_to_equations. lia. }
  destruct W6B as [W6LO W6HI].
  (* [comment removed for export] *)
  assert (SLW5 : mb + ms <= aregion L K_BATCH_CLASS + c_mapped_user (get_cls st K_BATCH_CLASS) \/ aregion L K_BATCH_CLASS + K_REGION <= mb).
  { rewrite ER24. unfold K_REGION. ub SC_r. destruct Y as [D|D]; [left| right]; generalize D RSP RES RHI A24a A24b; clear; unfold K_FREEARR_OFF; intros; lia. }
  assert (SLW6 : shad (hm + 16) + shlen (rup n 8) <= shad (aregion L K_BATCH_CLASS + c_mapped_user (get_cls st K_BATCH_CLASS))
              \/ shad (aregion L K_BATCH_CLASS) + shlen K_REGION <= shad (hm + 16)).
  { pose proof (aregion_mod L K_BATCH_CLASS SAL) as RM. destruct SLW5 as [D|D].
    - left. rewrite SHE. pose proof (shad_sep _ _ _ D MAL8) as HH. rewrite shlen_div in HH. generalize HH SHL; clear; intros; lia.
    - right. apply (Z.le_trans _ (shad mb)); [apply shad_sep; [exact D| generalize RM; clear; intros; Z.div_mod_to_equations; lia]| rewrite SHE; clear; lia]. }
  word_range sp SPR.
  change (get_cls st1 K_BATCH_CLASS) with (get_cls st K_BATCH_CLASS) in MUr.
  (* [comment removed for export] *)
  lazymatch type of MUr with munch ?W _ _ =>
    assert (KHI : forall Ad sz, bv_unsigned sp + -2272 <= Ad -> 0 <= sz -> disjoint_from W Ad sz);
    [ intros Ad sz Y1 Y2; cbn [disjoint_from fst snd]; unfold AINSTANCE, K_REGION;
      generalize Y1 Y2 LO CEIL TL1 TL2 TL1u TL4u SP1 SP2 ERI ER24 A24a A24b W6LO W6HI; clear; unfold K_SPACE_SIZE, K_SPACE_EXTRA, K_FREEARR_OFF, K_REGION; change (2^37) with 137438953472; change (2^32) with 4294967296; intros; repeat split; lia |];
    assert (KIM : forall Ad sz, 0xd0f00 <= Ad -> Ad + sz <= 0x15f790 -> 0 <= sz -> disjoint_from W Ad sz);
    [ intros Ad sz Y1 Y2 Y3; cbn [disjoint_from fst snd]; unfold AINSTANCE, K_REGION;
      generalize Y1 Y2 Y3 LO CEIL TL1 TL2 TL1u TL4u SP1 SP2 ERI ER24 A24a A24b W6LO W6HI SPR; clear; unfold K_SPACE_SIZE, K_SPACE_EXTRA, K_FREEARR_OFF, K_REGION; change (2^37) with 137438953472; change (2^32) with 4294967296; intros; repeat split; lia |];
    assert (KCH : forall Ad sz, mb <= Ad -> Ad + sz <= mb + ms -> 0 <= sz -> disjoint_from W Ad sz);
    [ intros Ad sz Y1 Y2 Y3; cbn [disjoint_from fst snd]; unfold AINSTANCE, K_REGION; pose proof SLW5 as SL5; pose proof SC_t as SCT; unbox SCT; pose proof SC_r as SCR; unbox SCR;
      generalize Y1 Y2 Y3 LO CEIL TL1 TL2 TL1u TL4u SP1 SP2 ERI ER24 A24a A24b W6LO W6HI SPR SCT SCR RSP RES RHI SL5 MLO ML1 ML3 KAM KBM KEM KCM KDM MCE; clear; unfold K_SPACE_SIZE, K_SPACE_EXTRA, K_FREEARR_OFF, K_REGION; change (2^37) with 137438953472; change (2^32) with 4294967296; intros; repeat split; lia |];
    assert (KSH : disjoint_from W (shad (hm + 16)) (shlen (rup n 8)));
    [ cbn [disjoint_from fst snd]; unfold AINSTANCE, K_REGION; pose proof SLW6 as SL6;
      generalize LO CEIL TL1 TL2 TL1u TL4u SP1 SP2 ERI ER24 A24a A24b W6LO W6HI SPR SL6 SHLO SHHI SHE SHL SHP; clear; unfold K_SPACE_SIZE, K_SPACE_EXTRA, K_FREEARR_OFF, K_REGION; change (2^37) with 137438953472; change (2^32) with 4294967296; intros; repeat split; lia |]
  end.
  (* [comment removed for export] *)
  eapply (cells_frame _ m1 m') in HD1; [| exact MUr | exact WMr | apply KCH; cbn [cells_size csize Nat.add]; subst hm; generalize NMS N6 NB; clear; intros; lia].
  eapply (cells_frame _ m1 m') in FC1; [| exact MUr | exact WMr | apply KCH; cbn [cells_size csize Nat.add]; subst hm; generalize NMS N6 NB; clear; intros; lia].
  eapply (cells_frame _ m1 m') in SH1; [| exact MUr | exact WMr | match goal with |- disjoint_from _ _ ?z => replace z with (shlen (rup n 8)) by (cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id; [reflexivity| generalize SHP; clear; intros; lia]) end; exact KSH].
  clear STATS1 LSJ1 UW1.
  eapply (cells_frame _ m1 m') in FL1; [| exact MUr | exact WMr | apply KIM; cbn [cells_size csize Nat.add]; clear; lia].
  eapply (stk_transport_disjoint _ _ m1 m') in IAS1; [| exact MUr | exact WMr | apply KIM; clear; lia].
  eapply (cells_frame _ m1 m') in SS1; [| exact MUr | exact WMr | apply KHI; cbn [cells_size csize Nat.add]; clear; lia].
  eapply (u64arr_frame _ m1 m') in TB1; [| exact MUr | exact WMr | apply KHI; rewrite ?LTB1; clear; cbn; lia].
  eapply (cells_frame _ m1 m') in FRS1; [| exact MUr | exact WMr | apply KHI; cbn [cells_size csize Nat.add]; clear; lia].
  eapply (cells_frame _ m1 m') in FRP1; [| exact MUr | exact WMr | apply KHI; cbn [cells_size csize Nat.add]; clear; lia].
  eapply (cells_frame _ m1 m') in FRE1; [| exact MUr | exact WMr | apply KHI; cbn [cells_size csize Nat.add]; clear; lia].
  assert (IAM2 : forall j, 0 <= j < 32768 -> bytes_at bsegs m' (0xd0f08 + 8 * j) (le8 (Z_to_bv 64 0))).
  { intros j Hj. eapply bytes_at_agree; [exact (IAM1 j Hj)|].
    intros ii Hi. apply MUr. rewrite length_le8 in Hi. rewrite wa_unsigned by lia.
    eapply disjoint_outside; [apply (KIM (0xd0f08 + 8 * j) 8); generalize Hj; clear; intros; lia| generalize Hi; clear; intros; lia]. }
  clear IAM1.
  (* [comment removed for export] *)
  pose proof ARr as AR0. destruct AR0 as (WFr & RTr & INSTr & THRr & CLSr & HQr & HSr & HDr & HROr & HRT2r & AVLr).
  cbn [ah_quar ah_sec ah_depot AHSm] in HQr, HSr, HDr.
  destruct THRr as (T0r & T40r & CACHESr & CSTATSr & [sjr [STATSr LSJr]] & UNWr).
  destruct (junk_split m' (al_t L + 2768) 16 16 CSTATSr ltac:(lia) ltac:(lia)) as [CSa CSb].
  destruct (junk_split m' (al_t L + 2768 + 16) 8 8 CSb ltac:(lia) ltac:(lia)) as [CS8 CSc].
  replace (al_t L + 2768 + 16) with (al_t L + 2784) in CS8 by lia.
  destruct (c8_of_junk m' _ CS8) as [stj' STSr].
  assert (POSr : 0 < c_count (get_cls st_r K_BATCH_CLASS)) by (rewrite CNTr; exact MAXr).
  pose proof (HMSEPg st_r X' WFr) as HMSEPr.
  destruct (read_ek_newS (AHSm DI AFK (sec_chunks_of st) Q1) L st_r X' Q1 m' RNG' hm n ALO ARNGr ARr HQr HM0' HMSEPr stj' EAr POSr STSr)
    as (k24 & chunks & EK & ES & ED & EB & NK & NBk & KK & NIB & JKb & FSH & CIN & _ & EKE).
  pose proof HQr as AQr. destruct AQr as ([QKr MXr] & [QCr ABLr] & [GCQr ABGr] & (FLr & IASr & IAMr) & CPr & NUMr).
  destruct (read_dkSC (AHSm DI AFK (sec_chunks_of st) Q1) L st_r X' Q1 m' RNG' hm ALO ARNGr ARr HQr HMSEPr
              (abatch_addr L k24) (n + 8192) (ek_of L st_r X' Q1 n k24 stj' chunks) ltac:(lia) ltac:(generalize NQM; clear; unfold Q_MAX; intros; lia)
              ltac:(right; exists k24; split; [reflexivity|]; split; [exact KK| exact NIB])
              ltac:(rewrite ENr, NL2 in QCr1; generalize QCr1; clear; unfold Q_CACHE, Q_BATCH_BYTES; intros; lia)
              ltac:(rewrite ENr, NG2, NL2 in RECr; generalize RECr; clear; unfold Q_CACHE, Q_MAX, Q_BATCH_BYTES; intros; lia) EB) as (DK & DS & GL & GLST & GDR).
  set (ek := ek_of L st_r X' Q1 n k24 stj' chunks) in *.
  set (g := g_of L st_r Q1 (n + 8192)) in *.
  (* [comment removed for export] *)
  pose proof ARNGr as AG0. destruct AG0 as (RIMGr & RT4r & RCTXr & RNOr & RSTOr & _ & _ & _ & _ & _ & _ & RSECSr & _).
  pose proof (rng_fp_le _ _ _ _ FPLE RSTK) as RSTKr. pose proof (rng_fp_le _ _ _ _ FPLE RMB) as RMBr. pose proof (rng_fp_le _ _ _ _ FPLE RSH) as RSHr.
  assert (BLr : ablocks L st_r X' (lb_remove p LB)) by (apply (ablocks_xbusy L st1 st_r X); [exact XBr | exact LIVEr | exact BLm]).
  pose proof (ao_fake L ALO) as FKO. pose proof (aobj_int _ _ FKO ltac:(clear; lia)) as (FKi & FKa & [kF FBND]). unfold aobj in FKO.   (* [comment removed for export] *) pose proof (ao_dtls L ALO) as DTO. pose proof (aobj4_int _ DTO) as (_ & _ & [kD DBND] & [jD DIMG]). unfold aobj in DTO.   (* [comment removed for export] *)
  pose proof (ad_fake_res L ALO) as D_f_res. pose proof (ad_t_fake L ALO) as D_t_f. pose proof (ad_dtls_res L ALO) as D_d_res. pose proof (ad_t_dtls L ALO) as D_t_d.
  unfold adisj in D_f_res, D_t_f, D_d_res, D_t_d.
  assert (FKr : AFK L (lb_remove p LB) m').
  { eapply (hf_frame _ HL L (lb_remove p LB) m1 m'); [exact FKm | exact MUr | exact WMr |].
    unfold fake_untouched. unfold AINSTANCE, K_REGION.
    assert (SHF : (shad (al_fake L) + shlen 11571200 <= shad (aregion L K_BATCH_CLASS + c_mapped_user (get_cls st K_BATCH_CLASS))
                   \/ shad (aregion L K_BATCH_CLASS) + shlen K_REGION <= shad (al_fake L))).
    { destruct D_f_res as [D|D].
      - left. apply shad_sep; [| generalize FKO FKi FBND; clear; intros; Z.div_mod_to_equations; lia]. rewrite ER24. generalize D RSP A24a; clear; intros; lia.
      - right. apply shad_sep; [| pose proof (aregion_mod L K_BATCH_CLASS SAL) as RM; generalize RM; clear; intros; Z.div_mod_to_equations; lia].
        rewrite ER24. unfold K_REGION. generalize D RSP RES RHI; clear; atop_facts; intros; lia. }
    unfold K_REGION in SHF.
    repeat (apply Forall_cons; [cbn [fst snd];
      generalize LO CEIL TL1 TL2 TL1u TL4u SP1 SP2 ERI ER24 A24a A24b W6LO W6HI SPR FKO FKi FBND DTO DBND DIMG D_f_res D_t_f D_d_res D_t_d RES RHI RSP SHF; clear;
      unfold K_SPACE_SIZE, K_SPACE_EXTRA, K_FREEARR_OFF, K_REGION; change (2^37) with 137438953472; change (2^32) with 4294967296;
      rewrite ?shad_div, ?shlen_div; unfold ASHOFF; intros; Z.div_mod_to_equations; repeat split; lia |]).
    apply Forall_nil. }
  clear D_f_res D_t_f D_d_res D_t_d D_t_res.
  pose proof EK as EK0. pose proof ES as ES0. pose proof DK as DK0.
  rewrite EKE in EK, ES, DK. cbn [ek_pre] in EK.
  destruct EK as (FULLr & SBr & CRr & CHr & LCHr & CNTr' & NTHr & IXSr & STSr' & HBr & BJr & SBPr & B0r & BL1r & DTBr & DTLr & DBLr & DHBr & DHLr & RBr).
  box DTBr. box DTLr. box DBLr. box DHBr. box DHLr.
  pose proof ES as ES1. cbn [ek_seps] in ES1. destruct ES1 as (SB1r & SB2r & SB3r & SLr).
  assert (DHL24 : hm + 24 <= qlast L (q_loc Q1) \/ qlast L (q_loc Q1) + 8192 <= hm).
  { destruct (a_qloc st_r); [destruct FULLr as [_ E0]; rewrite E0; right; generalize HM0'; clear; intros HB; pose proof (ablk_lin _ _ HB) as (HB1 & HB2 & HB3 & HB4); unfold AIMG_HI in HB1; lia | exact (proj1 (SLr eq_refl))]. }   (* [comment removed for export] *)
  box SB1r. box DHL24.
  assert (NBr : 0 <= Z.of_nat (length (a_qloc st_r)) < 2^62) by (rewrite QLr; change (a_qloc st1) with (a_qloc st); generalize LLB NC; clear; unfold Q_BATCH_BYTES; intros; lia).
  assert (QB0r : 0 <= a_qloc_bytes st_r) by (rewrite QBr; change (a_qloc_bytes st1) with (a_qloc_bytes st); generalize LLB; clear; unfold Q_BATCH_BYTES; intros; lia).
  (* [comment removed for export] *)
  iprefix. eapply evtF_cut.
  { lazymatch type of EKE with _ = EkNew ?fu ?nx ?bs ?cn ?mx ?cz ?sj0 ?ix ?chs ?sb ?bb ?hs0 =>
      eapply (free_from_refill_torec DI L fu g RNG' ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m'
                (al_t L) hm n b1 cx lo (Z.of_nat (length (a_qloc st_r))) (qfirst L (q_loc Q1)) (qlast L (q_loc Q1)) (a_qloc_bytes st_r)
                nx bs cn sb id bb mx cz sj0 ix sjr tb1 chs hs0 junk2 j0 trt)
    end.
    all: try lazymatch goal with
         | |- stk _ _ _ _ => first [exact STr | exact IAS1]
         | |- ablk _ (_ + 16 + rup _ 8) => first [assumption | exact HM0x | (try subst hm; eapply ablk_sub; [exact MLO| clear; lia| clear -NMS MSB MSAL N6 NB; unfold rup; Z.div_mod_to_equations; lia])]   (* [comment removed for export] *)
         | |- mem_inv _ _ => exact MIr
         | |- ADEPOT _ _ _ => exact HDr
         | |- u64arr _ _ (_ + 2800) _ => exact STATSr
         | |- u64arr _ _ _ _ => first [exact TB1 | exact CHr]
         | |- if _ then _ else _ => exact FULLr
         | |- forall j, _ -> bytes_at _ _ _ _ => exact IAM2
         | |- ek_seps _ _ _ _ => exact ES
         | |- dk_preC _ _ _ _ _ _ _ _ => exact DK
         | |- dk_seps _ _ _ => exact DS
         | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact HD1
         | |- rw_cells _ _ (shad _) _ => exact SH1
         | |- rw_cells _ _ (aq_tcache _) _ => exact QCr
         | |- rw_cells _ _ (_ + 80) _ => exact QCr
         | |- rw_cells _ _ (_ + 2128) _ => exact CRr
         | |- rw_cells _ _ (_ + 2784) _ => exact STSr'
         | |- rw_cells _ _ (_ + 3168) _ => exact UNWr
         | |- rw_cells _ _ (_ + -72) _ => exact FRS1
         | |- rw_cells _ _ (_ + -2128) _ => exact SS1
         | |- rw_cells _ _ (_ + -2208) _ => exact FRP1
         | |- rw_cells _ _ (_ + -2272) _ => exact FRE1
         | |- rw_cells _ _ (_ + 16) [C8 _] => exact FC1
         | |- rw_cells _ _ _ [C8 _; C8 _; C8 _] => exact QKr
         | |- nth_error _ _ = _ => exact NTHr
         | |- @eq Z _ _ => exact HBr
         | |- ex _ => exact BJr
         | |- _ + 24 <= al_t _ \/ _ => ub SC_t; clear -Y MSB; subst hm; lia
         | |- _ \/ _ => first [unboxed DTBr | unboxed DTLr | unboxed DBLr | unboxed SB1r | unboxed DHL24 | unboxed DL7 | unboxed DL8]
         | |- rng _ (shad _) _ => rewrite SHE; eapply rng_sub; [exact RSHr| clear; lia| clear -SHL; lia]
         | |- rng _ _ 24 => subst hm; eapply rng_sub; [exact RMBr| clear; lia| clear -MSB; lia]
         | |- rng _ _ _ => first [assumption | eapply rng_sub; [exact RSTKr| clear; lia| clear -LO; lia]]
         | |- rng_aimg _ => exact RIMGr
         end.
    all: try assumption.
    all: try (subst hm; unfold Q_MAX, Q_BATCH_BYTES; rewrite ?QLr, ?QBr; change (a_qloc st1) with (a_qloc st); change (a_qloc_bytes st1) with (a_qloc_bytes st);
              generalize NB N6 NMS NQM MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MAL MSAL RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 DL1 DL2 DL3 DL4 DL5 DL6
                         B1 CX LLB NC NM LF64 LST64 RA4 IDR RUP; clear; intros; Z.div_mod_to_equations; lia).
    all: match goal with |- ?G => idtac "REMT" G end. }
  cbv beta. intros msf PF.
  rewrite <- EKE in PF.
  pose proof ARm as ARm0. destruct ARm0 as [WFm _].
  assert (DK1 : dk_preC ek (g_of L st_r Q1 (ek_delta ek n)) RNG' (al_t L) (qlast L (q_loc Q1)) hm (a_qloc_bytes st_r + ek_delta ek n) m') by (rewrite ED; exact DK0).
  assert (PF1 : free_torec_post DI L ek (g_of L st_r Q1 (ek_delta ek n)) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (al_t L) hm n
                  (Z.of_nat (length (a_qloc st_r))) (qfirst L (q_loc Q1)) (qlast L (q_loc Q1)) (a_qloc_bytes st_r) b1 cx lo m' msf) by (rewrite ED; exact PF).
  (* [comment removed for export] *)
  assert (PDr : Permutation (sec_chunks_of st) (CSec mb ms n :: sec_chunks_of st_r)).
  { rewrite (sec_chunks_of_eq st1 st_r LIVEr QLr QGr). apply Permutation_sym. exact PD1. }
  assert (NOTLr : ~ sec_live st_r (CSec mb ms n)).
  { intros [q Hq]. destruct HS as (WFS & _). apply (sec_not_live_after L st _ p mb ms n st1 WFS (Permutation_refl _) LIVE eq_refl). exists q. rewrite <- LIVEr. exact Hq. }
  assert (RSCSr : RSEC (sec_chunks_of st) RNG') by (eapply RSEC_mono; [exact FPLE| exact RSECS]).
  assert (QCr2 : Q_CACHE < a_qloc_bytes (st_enq st_r (CSec mb ms n))) by exact QCr1.
  pose proof (STORE_RC L RNG' ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m' st_r (lb_remove p LB) X' Q1 (sec_chunks_of st) mb ms n b1 cx lo k24 stj' chunks
                ALO ARNGr ARr BLr FKr PDr RSCSr NOTLr NQM B1 B3 CX EAr NK NBk KK NIB JKb FSH CIN POSr QCr2 RECr EK0 DK1 CEIL LO TP msf PF1) as SP.
  unfold storeC_post in SP.
  destruct SP as (X2 & R & mR & id2 & t0' & t1' & t2' & xs0 & xs1 & xs2 & xs3 & xs4 & xs5 & xs6 & ps0 & ps1 & ps2 & ps3 & ps4 & ps5 & spv & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6'
                  & csA & csT & junk2' & -> & AR1 & RT1 & RB1 & RE1 & ARNG1 & BL1 & HFK1 & GB56 & QL1' & QLB1' & MI1 & ST1 & HP1 & ID1 & PF1' & FA1 & SZA & FT1 & SZT & FS1).
  apply evtF_done.
  (* [comment removed for export] *)
  assert (HPall : aheap_pres CI (lb_remove p LB) (bv_unsigned sp) m mR).
  { eapply aheap_pres_trans; [exact HPm|]. eapply aheap_pres_trans; [| exact HP1].
    eapply (aheap_pres_refill CI CI_OK CI_OK2 L st1 X (lb_remove p LB) sp (bv_unsigned sp + -2272) lo m1 m');
      [exact ALO | exact WFm | exact BLm | exact MUr | exact WMr | exact CEIL | generalize LO; clear; intros; lia | clear; lia]. }
  (* [comment removed for export] *)
  subst tp.
  eapply (AQrecP.aqrec ASECc (ADEPOT DI) AFK RSEC AHr_laws ASecRecycle.srec F_aqrec.qrec_front DEPD AFKD
            ASECc_perm ASECc_wf1' ASECc_disj' ASECc_nres' ASECc_qglob' RSEC_app' RSEC_perm RSEC_mono RSEC_arng'
            (fun st3 => aret st3) _ L RNG' (lb_remove p LB) R X2 (st_after (st_enq st_r (CSec mb ms n))) mR lo Q_MIN);
    try lazymatch goal with
    | |- alayout_ok _ => exact ALO
    | |- arng _ _ _ => exact ARNG1
    | |- AREP _ _ _ _ _ => exact AR1
    | |- qr_tmp _ = _ => exact RT1
    | |- qr_pendb _ = _ => exact RB1
    | |- qr_pend _ = _ => exact RE1
    | |- ablocks _ _ _ _ => exact BL1
    | |- mem_inv _ _ => exact MI1
    | |- stk _ _ _ _ => rewrite unsigned_lit by (clear -SP47 LO BOT STK3; atop_facts; lia); exact ST1
    | |- ATOP <= _ => atop_facts; clear -LO BOT STK3; lia
    | |- _ <= bv_unsigned _ - _ => rewrite unsigned_lit by (clear -SP47 LO BOT STK3; lia); clear -LO BOT STK3; lia
    | |- bv_unsigned _ <= 2 ^ 47 => rewrite unsigned_lit by (clear -SP47 LO BOT STK3; lia); clear -SP47 LO BOT STK3; lia
    | |- _ < 2 ^ 56 => exact GB56
    | |- 0 <= Q_MIN < _ => unfold Q_MIN; clear; lia
    | |- rng _ lo _ => rewrite unsigned_lit by (clear -SP47 LO BOT STK3; lia); eapply rng_sub; [exact RSTKr| clear; lia| clear -LO BOT STK3; lia]
    | |- AFK _ _ _ => exact HFK1
    end.
  (* [comment removed for export] *)
  intros st3 X3 RNG3 ms3 RET3.
  eapply (BACK L RNG RNG' RNG3 ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xs0 xs1 xs2 xs3 xs4 xs5 xs6 ps0 ps1 ps2 ps3 ps4 ps5 spv a3' F fc
            m mR st (st_after (st_enq st_r (CSec mb ms n))) X2 R LB p (al_t L) lo csA csT junk2' st3 X3 ms3);
    try lazymatch goal with
    | |- alayout_ok _ => exact ALO
    | |- ATOP <= _ => atop_facts; clear -LO BOT STK3; lia
    | |- _ <= bv_unsigned _ - AFREE_STACK => unfold AFREE_STACK; clear -LO; lia
    | |- Forall _ CI => first [exact CI_OK| exact CI_OK2]
    | |- fp_le _ _ => exact FPLE
    | |- awf _ _ _ => exact (proj1 AR1)
    | |- ablocks _ _ _ _ => exact BL1
    | |- aheap_pres _ _ _ _ _ => exact HPall
    | |- cells_size _ = _ => first [exact SZA| exact SZT]
    | |- rng _ lo _ => exact RSTKr
    | |- rng _ _ _ => exact RIMGr
    | |- aqrec_ret _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => exact RET3
    | |- a_qloc _ = _ => exact QL1'
    | |- a_qloc_bytes _ = _ => exact QLB1'
    | |- rw_cells _ _ _ _ => first [exact PF1'| exact FA1| exact FT1| exact FS1]
    end.
  all: match goal with |- ?G => idtac "REMB" G end.
Qed.
End S.
End CANSEC1.
