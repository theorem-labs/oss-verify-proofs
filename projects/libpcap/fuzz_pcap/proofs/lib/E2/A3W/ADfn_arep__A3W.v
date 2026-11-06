(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require ExecF ITreeA StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AQConst.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitR__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeRep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeRead.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apoison__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARealloc_iface__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecSlog__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_tail.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_front__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_arep__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require NDestr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecFacts.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aunwind.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_adrain__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc3g0__A3W.
From Stdlib Require Sorting.Permutation.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepStore__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_tailR__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_tabscan__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASF_fast__A3W.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module ADfn_arep.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AQConst. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AMalloc_iface. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitR__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeRead. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apoison__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARealloc_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecSlog__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_tail. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_front__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_arep__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AFreeModel OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.AFreeGeo OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRead OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_aalloc_s OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.F_aalloc1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tail OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_afree_icpt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.F_afree_arep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_adeallocfn_front OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_adeallocfn_icpt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.AFn_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ADeallocFn_kit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.ATlsKit.   (* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.

Section S.
(* [comment removed for export] *)
Variable DI : ADepotIface.
Variables (ASEC : alayout -> astate -> aconc -> amem -> Prop) (AFK : alayout -> list ablock -> amem -> Prop).
Notation AHQ := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.F_afree_arep.AHQ DI ASEC AFK).
Hypothesis HL : ahole_laws AHQ.
(* [comment removed for export] *)
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI
                                  /\ (snd iv <= 0xab270 \/ 0xab330 <= fst iv)
                                  /\ (snd iv <= 0xaf800 \/ 0x130830 <= fst iv)
                                  /\ (snd iv <= 0x13e088 \/ 0x13e08c <= fst iv)) CI.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Hypothesis STORE : store_free_stmt DI ASEC AFK CI.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="STORE"] Theorem dfn_fast : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (p : aptr) (A n lo SO pc : Z) (trt : list Z) (tb : list word) (c : Z),
  (* [comment removed for export] *)
  (a_live st) !! p = Some (CPrim c n) -> 1 <= n ->
  let st1 := set_live (delete p (a_live st)) st in
  let st2 := st_enq st1 (CPrim c n) in
  (enq_app st1 (CPrim c n) = None -> 0 < c_count (get_cls st K_BATCH_CLASS)) ->
  (Q_CACHE < a_qloc_bytes st2 -> a_qglob_bytes st2 + a_qloc_bytes st2 <= Q_MAX) ->
  (* [comment removed for export] *)
  AHEAP_P AHQ L RNG st LB m -> In (HB p A n) LB ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 0 -> a3 = Z_to_bv 64 0 -> a4 = Z_to_bv 64 SO -> a5 = Z_to_bv 64 1 ->
  rw_cells asegs m 0x13e088 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  bv_unsigned sp <= SO -> SO + 2056 <= 2^47 ->
  rw_cells asegs m SO [C8 (Z_to_bv 64 (SO + 16)); C4 (Z_to_bv 64 (1 + Z.of_nat (length trt))); C4 (Z_to_bv 64 0)] ->
  u64arr asegs m (SO + 16) tb -> length tb = 255%nat ->
  map bv_unsigned (firstn (Datatypes.S (length trt)) tb) = pc :: trt ->
  In (pc :: trt) (al_U L) -> (length trt <= 29)%nat ->
  rng RNG lo (bv_unsigned sp - lo) -> rng RNG SO 2056 ->
  implS asegs RNG (aembed ATOP (afree st (Some p)))
        (epostF (afree_post CI (AHEAP_P AHQ) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB p lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 DEALLOCATE_ENTRY) fc None m (seg_rom asegs)).
Proof.
  intros until c. intros LIVE N1 st1 st2 CNT NOREC AH HIN MI ST BOT LO TP Ha0 Ha1 Ha2 Ha3 Ha4 Ha5 FLAG1 SGE S47 SS TB LTB TRF TRU LTRT RSTK RS.
  assert (RA4 : True) by exact I.
  (nd_pre AH 4%nat; intros ALO ARNG [X [AR BL]] HFK; nd_post).
  pose proof AR as AR0. (nd_pre AR0 12%nat; intros WF RT INST THR CLS HQ HS HD HRO HRT2 AVL RT3; nd_post).
  cbn [ah_quar ah_sec ah_depot AHQ] in HQ, HS, HD. destruct HQ as [Q AQ].
  (* [comment removed for export] *)
  pose proof BL as BL0. destruct BL0 as (BH & _).
  pose proof WF as WF0. (nd_pre WF0 11%nat; intros SBE PAE SAL SLO SHI PERC OUTC BUSY LIVEB FRESH UNIQ; nd_post).
  destruct (BH p A n HIN) as [(y & Hy & Sy & Uy & Ny)|(mb & msz & Lp & _)]; [| exfalso; rewrite LIVE in Lp; discriminate].
  destruct (BUSY y Hy) as [CLy My]. rewrite Sy in My. (nd_pre My 6%nat; intros _ _ _ _ _ M5; nd_post). rewrite LIVE in M5.
  injection M5 as Cy Ny'. clear Ny'.
  (nd_pre (in_split _ _ Hy) 3%nat; intros l1 l2 XB; nd_post).
  destruct y as [yc yk yn yst yb1 yctx]. cbn in Sy, Uy, Ny, Cy, CLy. subst yst yn yc.
  rename yk into k. rename yb1 into b1. rename yctx into ctx.
  change ({| xb_class := c; xb_slot := k; xb_n := n; xb_st := BLive p; xb_b1 := b1; xb_ctx := ctx |}) with (bfreed p c k n b1 ctx) in XB.
  unfold xb_user, xb_alloc in Uy. cbn [xb_class xb_slot xb_n] in Uy.
  (* [comment removed for export] *)
  destruct (freed_range L st X p c k n b1 ctx l1 l2 WF XB) as [HC KR].
  (pose proof (freed_live L st X p c k n b1 ctx l1 l2 XB WF) as ndP__; nd_pre ndP__ 6%nat; intros _ N0 FIT0 B10 AT0 CTX0; nd_post).
  (pose proof (chunk_geo L st X c k n ALO WF HC KR (proj1 N0) FIT0) as ndP__; nd_pre ndP__ 14%nat; intros HM16 UB16 ABUB ABHM HLO UBS ABCE HHI N65 NQM ABLO RUP RUP8 S8; nd_post).
  (pose proof (slot_sep_objects L st X c k ALO WF HC KR) as ndP__; nd_pre ndP__ 5%nat; intros DT DC DN DSO DF; nd_post).
  destruct (slot_rng L st X c k ALO WF HC KR RNG ARNG) as [RSL RSS].
  pose proof ARNG as ARNG0. (nd_pre ARNG0 14%nat; intros RIMG RT4 RCTX RNO RSTO RRI RFK RSFK RDT RCLS RPA RSECS RPSH RTLS; nd_post).
  (pose proof (chunk_shadow_geo L st X c k n ALO WF HC KR (proj1 N0) FIT0) as ndP__; nd_pre ndP__ 8%nat; intros SE G2 GE G0 GFS SHLO SHHI _; nd_post).
  (pose proof (alayout_t L ALO) as ndP__; nd_pre ndP__ 4%nat; intros TL1 TL2 TL3 TL4; nd_post).
  (pose proof (alayout_ctx L ALO) as ndP__; nd_pre ndP__ 5%nat; intros CL1 CL2 CL3 CL4 CL5; nd_post).
  (pose proof (alayout_depot L ALO) as ndP__; nd_pre ndP__ 10%nat; intros DL1 DL2 DL3 DL4 DL5 DL6 DL7 DL8 DL9 DL10; nd_post).
  (pose proof (alayout_stack L ALO) as ndP__; nd_pre ndP__ 3%nat; intros STK1 STK2 STK3; nd_post).
  assert (SP47 : bv_unsigned sp < 2^47) by (clear -SGE S47; lia).
  set (AB := aslot_addr L c k) in *. set (UB := AB + rz_size n) in *.
  assert (EHM : fhm L c k n = UB - 16) by (unfold fhm; subst AB UB; lia).
  (* [comment removed for export] *)
  pose proof RT as RT0.
  (nd_pre RT0 28%nat; intros GPG GOT GOT80 RIC LS1 REAL IMAX4 FLG5 FLG HPP SHB CANP TI TK INI2 LAY MCS OOM3 PGC HK2 CF8 CF34 CSMT T88 TSD LS2 CT8 CT; nd_post).
  pose proof INI2 as INI. rw_split INI 1%nat INI1 INIx. clear INIx.
  pose proof OOM3 as OOM. rw_split OOM 2%nat OOMx RSS0. clear OOMx.
  pose proof IMAX4 as IMAX. rw_split IMAX 3%nat IMAX3 IMAXx. clear IMAXx.
  pose proof HK2 as HK. rw_split HK 1%nat HK1 HKF.
  pose proof GOT as GOT6. rw_split GOT 1%nat GOTa GOTr. rw_split GOTr 1%nat GF GOTx. clear GOTa GOTx.
  (nd_pre THR 6%nat; intros T0 T40 CACHES CSTATS [sj [STATS LSJ]] UNW; nd_post).
  destruct (CACHES K_BATCH_CLASS (K24)) as [tail (CR & CH & LCH)].
  replace (acache_addr L K_BATCH_CLASS) with (al_t L + 2128) in CR by (unfold acache_addr, K_BATCH_CLASS; lia).
  destruct (junk_split m (al_t L + 2768) 16 16 CSTATS ltac:(lia) ltac:(lia)) as [CSa CSb].
  destruct (junk_split m (al_t L + 2768 + 16) 8 8 CSb ltac:(lia) ltac:(lia)) as [CS8 CSc].
  replace (al_t L + 2768 + 16) with (al_t L + 2784) in CS8 by lia.
  destruct (c8_of_junk m _ CS8) as [stj STS].
  (* [comment removed for export] *)
  (nd_pre (read_chunk L st X m p c k n b1 ctx l1 l2 ALO WF XB (conj (proj1 (proj2 (proj2 (CLS c HC)))) (proj2 (proj2 (proj2 (CLS c HC)))))) 7%nat; intros HDR [uw HUW] UJR LH SHA SHU SHR; nd_post).
  fold AB in HDR, HUW, UJR, LH, SHA, SHU, SHR. fold UB in HDR, HUW, UJR, LH, SHU, SHR.
  (* [comment removed for export] *)
  pose proof AQ as AQ0. (nd_pre AQ0 6%nat; intros [QK MX] [QC ABL] [GCQ ABG] (FL & IAS & IAM) CP NUM; nd_post).
  pose proof (aintal_flag_true _ _ FL FLAG1) as EIA. rewrite EIA in FL, IAM. specialize (IAM eq_refl).
  unfold AIA_FLAG, AIA_BASE, AIA_SIZE, AIA_MAP1, AIA_MAP1_LEN in FL, IAS, IAM. change (262144 / 8) with 32768 in IAM.
  (nd_pre NUM 5%nat; intros NB1 NB2 NF NC NM; nd_post).
  pose proof (batches_bytes_lb (a_qloc st) ltac:(apply Forall_app in NF; exact (proj1 NF))) as LLB. rewrite <- NB1 in LLB.
  (* [comment removed for export] *)
  assert (EKX : exists k24 chunks, let ek := ek_of L st X Q n k24 stj chunks in
       ek_pre ek RNG (al_t L) (Z.of_nat (length (a_qloc st))) (qlast L (q_loc Q)) n (fhm L c k n) m
    /\ ek_seps ek L (fhm L c k n) (qlast L (q_loc Q))
    /\ 0 <= ek_delta ek n /\ a_qloc_bytes st2 = a_qloc_bytes st + ek_delta ek n /\ a_qglob_bytes st2 = a_qglob_bytes st
    /\ (ek_b ek (qlast L (q_loc Q)) = qlast L (q_loc Q)
        \/ exists kk, ek_b ek (qlast L (q_loc Q)) = abatch_addr L kk /\ 0 <= kk < ndist st K_BATCH_CLASS /\ ~ In kk (map qb_slot (q_loc Q ++ q_glob Q)))
    /\ (enq_is_app st = false ->
          nth_error (xc_cache (x_cls X K_BATCH_CLASS)) (Z.to_nat (c_count (get_cls st K_BATCH_CLASS) - 1)) = Some k24
       /\ busy_of X K_BATCH_CLASS k24 = None /\ 0 <= k24 < ndist st K_BATCH_CLASS
       /\ ~ In k24 (map qb_slot (q_loc Q ++ q_glob Q))
       /\ junk_at m (abatch_addr L k24) 8192 /\ fill_at m (shad (abatch_addr L k24)) (shlen 8192) 0xfa
       /\ a_cinit st = true /\ 0 < c_count (get_cls st K_BATCH_CLASS))).
  { pose proof (st_enq_bytes st p (CPrim c n) L X Q) as SB.
    destruct (enq_is_app st) eqn:EA.
    - (nd_pre (read_ek_app AHQ L st X Q m RNG (BLive p) c k n b1 ctx l1 l2 ALO ARNG AR AQ XB ltac:(discriminate) stj [] 0 EA
                (Z_to_bv 64 0) (Z_to_bv 64 0) 0 CR STS) 5%nat; intros EK ES ED EB _; nd_post).
      specialize (SB 0 stj [] ltac:(intros E; exfalso; change (enq_app st1 (CPrim c n) = None) in E; assert (EA1 : enq_is_app st1 = true) by exact EA;
                    destruct (proj1 (enq_is_app_spec st1 (CPrim c n)) EA1) as [s Hs]; congruence)).
      cbn [chunk_size] in SB. (nd_pre SB 3%nat; intros SB1 SB2 _; nd_post).
      exists 0, []. cbv zeta. split; [exact EK|]. split; [exact ES|]. split; [rewrite ED; lia|]. split; [exact SB1|]. split; [exact SB2|].
      split; [left; exact EB|]. intros; discriminate.
    - assert (POS : 0 < c_count (get_cls st K_BATCH_CLASS)).
      { apply CNT. destruct (enq_app st1 (CPrim c n)) eqn:E; [| reflexivity]. exfalso.
        assert (EA1 : enq_is_app st1 = true) by (apply (proj2 (enq_is_app_spec st1 (CPrim c n))); eexists; exact E).
        change (enq_is_app st1) with (enq_is_app st) in EA1. congruence. }
      (nd_pre (read_ek_new AHQ L st X Q m RNG (BLive p) c k n b1 ctx l1 l2 ALO ARNG AR AQ XB ltac:(discriminate) stj EA POS STS) 14%nat; intros k24 chunks EK ES ED EB NK NB KK NIB JK FSH CIN _; nd_post).
      specialize (SB k24 stj chunks ltac:(intros _; exact POS)). cbn [chunk_size] in SB. (nd_pre SB 3%nat; intros SB1 SB2 _; nd_post).
      exists k24, chunks. cbv zeta. split; [exact EK|]. split; [exact ES|]. split; [rewrite ED; lia|]. split; [exact SB1|]. split; [exact SB2|].
      split; [right; exists k24; split; [exact EB|]; split; [exact KK| exact NIB]|].
      intros _. repeat (split; [assumption|]). exact POS. }
  (nd_pre EKX 3%nat; intros k24 chunks EKX; nd_post). cbv zeta in EKX. (nd_pre EKX 7%nat; intros EK ES ED0 SB1 SB2 EBB NEWF; nd_post).
  set (ek := ek_of L st X Q n k24 stj chunks) in *.
  (* [comment removed for export] *)
  (nd_pre (read_dk AHQ L st X Q m RNG (BLive p) c k n b1 ctx l1 l2 ALO ARNG AR AQ XB ltac:(discriminate) (ek_b ek (qlast L (q_loc Q))) (ek_delta ek n) ek ED0 EBB
              ltac:(rewrite <- SB1, <- SB2; exact NOREC) eq_refl) 4%nat; intros DK DS GL GLST; nd_post).
  set (g := g_of L st Q (ek_delta ek n)) in *.
  (* [comment removed for export] *)
  rewrite (afree_fast_eq st p (CPrim c n) LIVE ltac:(cbn [chunk_size]; exact NQM) CNT NOREC).
  apply implS_ret.
  (* [comment removed for export] *)
  assert (AB64 : forall q, In q (q_loc Q ++ q_glob Q) -> 0 <= abatch_addr L (qb_slot q) < 2^64).
  { intros q Hq. (pose proof (bslot_geo L st X ALO WF (qb_slot q) (bslot_range L st X Q WF CP q Hq)) as ndP__; nd_pre ndP__ 3%nat; intros B0 B1 _; nd_post). atop_facts. lia. }
  assert (LF64 : 0 <= qfirst L (q_loc Q) < 2^64).
  { destruct (qfirst_cases L (q_loc Q)) as [-> |(q & Hq & ->)]; [lia| apply AB64; apply in_or_app; left; exact Hq]. }
  assert (LL64 : 0 <= qlast L (q_loc Q) < 2^64).
  { destruct (qlast_cases L (q_loc Q)) as [-> |(q & Hq & ->)]; [lia| apply AB64; apply in_or_app; left; exact Hq]. }
  assert (DELTA : ek_delta ek n <= n + 8192) by (subst ek; unfold ek_of; destruct (enq_is_app st); cbn [ek_delta]; lia).
  (* [comment removed for export] *)
  unfold AIMG_HI, AFREE_STACK, UDEPTH, Q_MAX, Q_CACHE in *.
  box DT. box DC. box DN. box DSO. box DF. box CL5. box DL7. box DL8. box DL9. box DL10.
  eapply evtF_mono.
  { eapply (dfn_fast_spec DI L ek g RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m
              (al_t L) (al_ctx L) (fhm L c k n) n b1 ctx lo
              (Z.of_nat (length (a_qloc st))) (qfirst L (q_loc Q)) (qlast L (q_loc Q)) (a_qloc_bytes st) SO (1 + Z.of_nat (length trt)) pc
              uw _ _ sj tb (block_shadow_bytes n) trt).
    all: rewrite ?EHM.
    all: try lazymatch goal with
         | |- stk _ _ _ _ => first [exact ST | exact IAS]
         | |- ablk _ (_ + 16 + rup _ 8) => first [assumption | unfold ablk; right; generalize HLO HHI; try generalize EHM; clear; unfold fhm; intros; lia]   (* [comment removed for export] *)
         | |- mem_inv _ _ => exact MI
         | |- allocA_cells _ _ _ => unfold allocA_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
         | |- poison_cells _ => unfold poison_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
         | |- ADEPOT _ _ _ => exact HD
         | |- In _ _ => exact TRU
         | |- u64arr _ _ (_ + 2800) _ => exact STATS
         | |- u64arr _ _ _ _ => exact TB
         | |- map _ _ = _ => exact TRF
         | |- forall j, _ => exact IAM
         | |- rw_cells _ _ _ [C8 _; C4 _; C4 _] => exact SS
         | |- ek_pre _ _ _ _ _ _ _ _ => exact EK
         | |- ek_seps _ _ _ _ => exact ES
         | |- dk_pre _ _ _ _ _ _ _ _ => exact DK
         | |- dk_seps _ _ _ => exact DS
         | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact HDR
         | |- rw_cells _ _ (shad _) _ => eapply rw_cells_addr_eq; [exact SHU| f_equal; lia]
         | |- rw_cells _ _ (_ + 80) _ => exact QC
         | |- rw_cells _ _ (_ - 16 + 16) [C8 _] => eapply rw_cells_addr_eq; [exact HUW| lia]
         end.
    all: try lazymatch goal with
         | |- rw_cells _ _ _ [C8 _; C8 _; C8 _] => first [exact T0 | exact QK]
         | |- rw_cells _ _ _ _ => assumption
         | |- @eq word _ _ => first [exact TP | exact Ha0 | exact Ha2 | exact Ha3 | exact Ha4 | exact Ha5 | rewrite Ha1, <- Uy; subst AB UB; apply Z_to_bv_eqm; first [(generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LL64 ED0 DELTA RA4; clear; intros; lia) | lia] | reflexivity]   (* [comment removed for export] *)
         | |- _ \/ _ => first [unboxed DT | unboxed DC | unboxed DN | unboxed DSO | unboxed CL5 | unboxed DL7 | unboxed DL8 | unboxed DL9 | unboxed DL10
                             | ub DT; (generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LL64 ED0 DELTA RA4; clear -Y; intros; lia) | ub DC; (generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LL64 ED0 DELTA RA4; clear -Y; intros; lia) | ub DN; (generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LL64 ED0 DELTA RA4; clear -Y; intros; lia) | ub DSO; (generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LL64 ED0 DELTA RA4; clear -Y; intros; lia)
                             | ub DT; lia | ub DC; lia | ub DN; lia | ub DSO; lia]
         | |- rng _ (shad _) _ => replace (UB - 16 + 16) with UB by (clear; lia); eapply rng_sub; [exact RSS| rewrite SE; first [(generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LL64 ED0 DELTA RA4; clear; intros; lia) | lia]| rewrite SE, GE; first [(generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LL64 ED0 DELTA RA4; clear; intros; lia) | lia]]
         | |- rng _ _ _ => first [assumption | eapply rng_sub; [exact RSL| (generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LL64 ED0 DELTA RA4; clear; intros; lia)| (generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LL64 ED0 DELTA RA4; clear; intros; lia)] | eapply rng_sub; [exact RCTX| (generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LL64 ED0 DELTA RA4; clear; intros; lia)| (generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LL64 ED0 DELTA RA4; clear; intros; lia)] | eapply rng_sub; [exact RSL| lia| lia] | eapply rng_sub; [exact RCTX| lia| lia] | solve_rng]
         end.
    all: try assumption.
    all: unfold AIMG_HI, Q_MAX, Q_CACHE, Q_BATCH_BYTES, UDEPTH in *.
    all: try (generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6
                         B10 LLB NC NM LF64 LL64 ED0 DELTA RA4; clear; intros; lia).
    all: try (tclr_solve ALO ltac:((pose proof (slot_geo L st X c k ALO WF HC KR) as ndP__; nd_pre ndP__ 10%nat; intros _ _ _ _ _ _ _ SG5 SG6 _; nd_post);
                                    unfold K_SPACE_SIZE in SG6; change (2^37) with 137438953472 in SG6;
                                    generalize SG5 SG6 ABHM UBS RUP N0 N1; subst UB AB; clear; intros; lia)).      (* [comment removed for export] *)
    all: try (clear -LTRT; lia).
    all: match goal with |- ?G => idtac "REMF" G end. }
  cbv beta. intros ms' PM. rewrite EHM in PM.
  (* [comment removed for export] *)
  eapply (STORE L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st LB X Q p c k n b1 ctx A lo k24 l1 l2 stj chunks).
  all: try lazymatch goal with
       | |- free_fast_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => exact PM
       | |- alayout_ok _ => exact ALO
       | |- arng _ _ _ => exact ARNG
       | |- AREP _ _ _ _ _ => exact AR
       | |- AQUAR_at _ _ _ _ _ => exact AQ
       | |- ablocks _ _ _ _ => exact BL
       | |- In _ _ => exact HIN
       | |- _ = _ => exact XB
       | |- _ = false -> _ => exact NEWF
       | |- ek_pre _ _ _ _ _ _ _ _ => exact EK
       | |- dk_pre _ _ _ _ _ _ _ _ => exact DK
       end.
  all: try assumption.
  all: try (generalize N1 LO BOT STK3; clear; intros; unfold AFREE_STACK in *; lia).
  all: match goal with |- ?G => idtac "REMS" G end.
Qed.
End S.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Exec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AFreeModel.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.AFreeGeo.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRead.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_aalloc_s.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.F_aalloc1.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tail.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_afree_icpt.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.F_afree_arep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_adeallocfn_front.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_adeallocfn_icpt.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.AFn_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ADeallocFn_kit.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.ATlsKit.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.

Section S.
(* [comment removed for export] *)
Variable DI : ADepotIface.
Variables (ASEC : alayout -> astate -> aconc -> amem -> Prop) (AFK : alayout -> list ablock -> amem -> Prop).
Notation AHQ := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.F_afree_arep.TwB.AHQ DI ASEC AFK).
Hypothesis HL : ahole_laws AHQ.
(* [comment removed for export] *)
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI
                                  /\ (snd iv <= 0xab670 \/ 0xab730 <= fst iv)
                                  /\ (snd iv <= 0xafc00 \/ 0x130c30 <= fst iv)
                                  /\ (snd iv <= 0x13e488 \/ 0x13e48c <= fst iv)) CI.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Hypothesis STORE : store_free_stmt DI ASEC AFK CI.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="STORE"] Theorem dfn_fast : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (p : aptr) (A n lo SO pc : Z) (trt : list Z) (tb : list word) (c : Z),
  (* [comment removed for export] *)
  (a_live st) !! p = Some (CPrim c n) -> 1 <= n ->
  let st1 := set_live (delete p (a_live st)) st in
  let st2 := st_enq st1 (CPrim c n) in
  (enq_app st1 (CPrim c n) = None -> 0 < c_count (get_cls st K_BATCH_CLASS)) ->
  (Q_CACHE < a_qloc_bytes st2 -> a_qglob_bytes st2 + a_qloc_bytes st2 <= Q_MAX) ->
  (* [comment removed for export] *)
  AHEAP_P AHQ L RNG st LB m -> In (HB p A n) LB ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 0 -> a3 = Z_to_bv 64 0 -> a4 = Z_to_bv 64 SO -> a5 = Z_to_bv 64 1 ->
  rw_cells asegs m 0x13e488 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  bv_unsigned sp <= SO -> SO + 2056 <= 2^47 ->
  rw_cells asegs m SO [C8 (Z_to_bv 64 (SO + 16)); C4 (Z_to_bv 64 (1 + Z.of_nat (length trt))); C4 (Z_to_bv 64 0)] ->
  u64arr asegs m (SO + 16) tb -> length tb = 255%nat ->
  map bv_unsigned (firstn (Datatypes.S (length trt)) tb) = pc :: trt ->
  In (pc :: trt) (al_U L) -> (length trt <= 29)%nat ->
  rng RNG lo (bv_unsigned sp - lo) -> rng RNG SO 2056 ->
  implS asegs RNG (aembed ATOP (afree st (Some p)))
        (epostF (afree_post CI (AHEAP_P AHQ) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB p lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 DEALLOCATE_ENTRY) fc None m (seg_rom asegs)).
Proof.
  intros until c. intros LIVE N1 st1 st2 CNT NOREC AH HIN MI ST BOT LO TP Ha0 Ha1 Ha2 Ha3 Ha4 Ha5 FLAG1 SGE S47 SS TB LTB TRF TRU LTRT RSTK RS.
  assert (RA4 : True) by exact I.
  (nd_pre AH 4%nat; intros ALO ARNG [X [AR BL]] HFK; nd_post).
  pose proof AR as AR0. (nd_pre AR0 12%nat; intros WF RT INST THR CLS HQ HS HD HRO HRT2 AVL RT3; nd_post).
  cbn [ah_quar ah_sec ah_depot AHQ] in HQ, HS, HD. destruct HQ as [Q AQ].
  (* [comment removed for export] *)
  pose proof BL as BL0. destruct BL0 as (BH & _).
  pose proof WF as WF0. (nd_pre WF0 11%nat; intros SBE PAE SAL SLO SHI PERC OUTC BUSY LIVEB FRESH UNIQ; nd_post).
  destruct (BH p A n HIN) as [(y & Hy & Sy & Uy & Ny)|(mb & msz & Lp & _)]; [| exfalso; rewrite LIVE in Lp; discriminate].
  destruct (BUSY y Hy) as [CLy My]. rewrite Sy in My. (nd_pre My 6%nat; intros _ _ _ _ _ M5; nd_post). rewrite LIVE in M5.
  injection M5 as Cy Ny'. clear Ny'.
  (nd_pre (in_split _ _ Hy) 3%nat; intros l1 l2 XB; nd_post).
  destruct y as [yc yk yn yst yb1 yctx]. cbn in Sy, Uy, Ny, Cy, CLy. subst yst yn yc.
  rename yk into k. rename yb1 into b1. rename yctx into ctx.
  change ({| xb_class := c; xb_slot := k; xb_n := n; xb_st := BLive p; xb_b1 := b1; xb_ctx := ctx |}) with (bfreed p c k n b1 ctx) in XB.
  unfold xb_user, xb_alloc in Uy. cbn [xb_class xb_slot xb_n] in Uy.
  (* [comment removed for export] *)
  destruct (freed_range L st X p c k n b1 ctx l1 l2 WF XB) as [HC KR].
  (pose proof (freed_live L st X p c k n b1 ctx l1 l2 XB WF) as ndP__; nd_pre ndP__ 6%nat; intros _ N0 FIT0 B10 AT0 CTX0; nd_post).
  (pose proof (chunk_geo L st X c k n ALO WF HC KR (proj1 N0) FIT0) as ndP__; nd_pre ndP__ 14%nat; intros HM16 UB16 ABUB ABHM HLO UBS ABCE HHI N65 NQM ABLO RUP RUP8 S8; nd_post).
  (pose proof (slot_sep_objects L st X c k ALO WF HC KR) as ndP__; nd_pre ndP__ 5%nat; intros DT DC DN DSO DF; nd_post).
  destruct (slot_rng L st X c k ALO WF HC KR RNG ARNG) as [RSL RSS].
  pose proof ARNG as ARNG0. (nd_pre ARNG0 14%nat; intros RIMG RT4 RCTX RNO RSTO RRI RFK RSFK RDT RCLS RPA RSECS RPSH RTLS; nd_post).
  (pose proof (chunk_shadow_geo L st X c k n ALO WF HC KR (proj1 N0) FIT0) as ndP__; nd_pre ndP__ 8%nat; intros SE G2 GE G0 GFS SHLO SHHI _; nd_post).
  (pose proof (alayout_t L ALO) as ndP__; nd_pre ndP__ 4%nat; intros TL1 TL2 TL3 TL4; nd_post).
  (pose proof (alayout_ctx L ALO) as ndP__; nd_pre ndP__ 5%nat; intros CL1 CL2 CL3 CL4 CL5; nd_post).
  (pose proof (alayout_depot L ALO) as ndP__; nd_pre ndP__ 10%nat; intros DL1 DL2 DL3 DL4 DL5 DL6 DL7 DL8 DL9 DL10; nd_post).
  (pose proof (alayout_stack L ALO) as ndP__; nd_pre ndP__ 3%nat; intros STK1 STK2 STK3; nd_post).
  assert (SP47 : bv_unsigned sp < 2^47) by (clear -SGE S47; lia).
  set (AB := aslot_addr L c k) in *. set (UB := AB + rz_size n) in *.
  assert (EHM : fhm L c k n = UB - 16) by (unfold fhm; subst AB UB; lia).
  (* [comment removed for export] *)
  pose proof RT as RT0.
  (nd_pre RT0 28%nat; intros GPG GOT GOT80 RIC LS1 REAL IMAX4 FLG5 FLG HPP SHB CANP TI TK INI2 LAY MCS OOM3 PGC HK2 CF8 CF34 CSMT T88 TSD LS2 CT8 CT; nd_post).
  pose proof INI2 as INI. rw_split INI 1%nat INI1 INIx. clear INIx.
  pose proof OOM3 as OOM. rw_split OOM 2%nat OOMx RSS0. clear OOMx.
  pose proof IMAX4 as IMAX. rw_split IMAX 3%nat IMAX3 IMAXx. clear IMAXx.
  pose proof HK2 as HK. rw_split HK 1%nat HK1 HKF.
  pose proof GOT as GOT6. rw_split GOT 1%nat GOTa GOTr. rw_split GOTr 1%nat GF GOTx. clear GOTa GOTx.
  (nd_pre THR 6%nat; intros T0 T40 CACHES CSTATS [sj [STATS LSJ]] UNW; nd_post).
  destruct (CACHES K_BATCH_CLASS (K24)) as [tail (CR & CH & LCH)].
  replace (acache_addr L K_BATCH_CLASS) with (al_t L + 2128) in CR by (unfold acache_addr, K_BATCH_CLASS; lia).
  destruct (junk_split m (al_t L + 2768) 16 16 CSTATS ltac:(lia) ltac:(lia)) as [CSa CSb].
  destruct (junk_split m (al_t L + 2768 + 16) 8 8 CSb ltac:(lia) ltac:(lia)) as [CS8 CSc].
  replace (al_t L + 2768 + 16) with (al_t L + 2784) in CS8 by lia.
  destruct (c8_of_junk m _ CS8) as [stj STS].
  (* [comment removed for export] *)
  (nd_pre (read_chunk L st X m p c k n b1 ctx l1 l2 ALO WF XB (conj (proj1 (proj2 (proj2 (CLS c HC)))) (proj2 (proj2 (proj2 (CLS c HC)))))) 7%nat; intros HDR [uw HUW] UJR LH SHA SHU SHR; nd_post).
  fold AB in HDR, HUW, UJR, LH, SHA, SHU, SHR. fold UB in HDR, HUW, UJR, LH, SHU, SHR.
  (* [comment removed for export] *)
  pose proof AQ as AQ0. (nd_pre AQ0 6%nat; intros [QK MX] [QC ABL] [GCQ ABG] (FL & IAS & IAM) CP NUM; nd_post).
  pose proof (aintal_flag_true _ _ FL FLAG1) as EIA. rewrite EIA in FL, IAM. specialize (IAM eq_refl).
  unfold AIA_FLAG, AIA_BASE, AIA_SIZE, AIA_MAP1, AIA_MAP1_LEN in FL, IAS, IAM. change (262144 / 8) with 32768 in IAM.
  (nd_pre NUM 5%nat; intros NB1 NB2 NF NC NM; nd_post).
  pose proof (batches_bytes_lb (a_qloc st) ltac:(apply Forall_app in NF; exact (proj1 NF))) as LLB. rewrite <- NB1 in LLB.
  (* [comment removed for export] *)
  assert (EKX : exists k24 chunks, let ek := ek_of L st X Q n k24 stj chunks in
       ek_pre ek RNG (al_t L) (Z.of_nat (length (a_qloc st))) (qlast L (q_loc Q)) n (fhm L c k n) m
    /\ ek_seps ek L (fhm L c k n) (qlast L (q_loc Q))
    /\ 0 <= ek_delta ek n /\ a_qloc_bytes st2 = a_qloc_bytes st + ek_delta ek n /\ a_qglob_bytes st2 = a_qglob_bytes st
    /\ (ek_b ek (qlast L (q_loc Q)) = qlast L (q_loc Q)
        \/ exists kk, ek_b ek (qlast L (q_loc Q)) = abatch_addr L kk /\ 0 <= kk < ndist st K_BATCH_CLASS /\ ~ In kk (map qb_slot (q_loc Q ++ q_glob Q)))
    /\ (enq_is_app st = false ->
          nth_error (xc_cache (x_cls X K_BATCH_CLASS)) (Z.to_nat (c_count (get_cls st K_BATCH_CLASS) - 1)) = Some k24
       /\ busy_of X K_BATCH_CLASS k24 = None /\ 0 <= k24 < ndist st K_BATCH_CLASS
       /\ ~ In k24 (map qb_slot (q_loc Q ++ q_glob Q))
       /\ junk_at m (abatch_addr L k24) 8192 /\ fill_at m (shad (abatch_addr L k24)) (shlen 8192) 0xfa
       /\ a_cinit st = true /\ 0 < c_count (get_cls st K_BATCH_CLASS))).
  { pose proof (st_enq_bytes st p (CPrim c n) L X Q) as SB.
    destruct (enq_is_app st) eqn:EA.
    - (nd_pre (read_ek_app AHQ L st X Q m RNG (BLive p) c k n b1 ctx l1 l2 ALO ARNG AR AQ XB ltac:(discriminate) stj [] 0 EA
                (Z_to_bv 64 0) (Z_to_bv 64 0) 0 CR STS) 5%nat; intros EK ES ED EB _; nd_post).
      specialize (SB 0 stj [] ltac:(intros E; exfalso; change (enq_app st1 (CPrim c n) = None) in E; assert (EA1 : enq_is_app st1 = true) by exact EA;
                    destruct (proj1 (enq_is_app_spec st1 (CPrim c n)) EA1) as [s Hs]; congruence)).
      cbn [chunk_size] in SB. (nd_pre SB 3%nat; intros SB1 SB2 _; nd_post).
      exists 0, []. cbv zeta. split; [exact EK|]. split; [exact ES|]. split; [rewrite ED; lia|]. split; [exact SB1|]. split; [exact SB2|].
      split; [left; exact EB|]. intros; discriminate.
    - assert (POS : 0 < c_count (get_cls st K_BATCH_CLASS)).
      { apply CNT. destruct (enq_app st1 (CPrim c n)) eqn:E; [| reflexivity]. exfalso.
        assert (EA1 : enq_is_app st1 = true) by (apply (proj2 (enq_is_app_spec st1 (CPrim c n))); eexists; exact E).
        change (enq_is_app st1) with (enq_is_app st) in EA1. congruence. }
      (nd_pre (read_ek_new AHQ L st X Q m RNG (BLive p) c k n b1 ctx l1 l2 ALO ARNG AR AQ XB ltac:(discriminate) stj EA POS STS) 14%nat; intros k24 chunks EK ES ED EB NK NB KK NIB JK FSH CIN _; nd_post).
      specialize (SB k24 stj chunks ltac:(intros _; exact POS)). cbn [chunk_size] in SB. (nd_pre SB 3%nat; intros SB1 SB2 _; nd_post).
      exists k24, chunks. cbv zeta. split; [exact EK|]. split; [exact ES|]. split; [rewrite ED; lia|]. split; [exact SB1|]. split; [exact SB2|].
      split; [right; exists k24; split; [exact EB|]; split; [exact KK| exact NIB]|].
      intros _. repeat (split; [assumption|]). exact POS. }
  (nd_pre EKX 3%nat; intros k24 chunks EKX; nd_post). cbv zeta in EKX. (nd_pre EKX 7%nat; intros EK ES ED0 SB1 SB2 EBB NEWF; nd_post).
  set (ek := ek_of L st X Q n k24 stj chunks) in *.
  (* [comment removed for export] *)
  (nd_pre (read_dk AHQ L st X Q m RNG (BLive p) c k n b1 ctx l1 l2 ALO ARNG AR AQ XB ltac:(discriminate) (ek_b ek (qlast L (q_loc Q))) (ek_delta ek n) ek ED0 EBB
              ltac:(rewrite <- SB1, <- SB2; exact NOREC) eq_refl) 4%nat; intros DK DS GL GLST; nd_post).
  set (g := g_of L st Q (ek_delta ek n)) in *.
  (* [comment removed for export] *)
  rewrite (afree_fast_eq st p (CPrim c n) LIVE ltac:(cbn [chunk_size]; exact NQM) CNT NOREC).
  apply implS_ret.
  (* [comment removed for export] *)
  assert (AB64 : forall q, In q (q_loc Q ++ q_glob Q) -> 0 <= abatch_addr L (qb_slot q) < 2^64).
  { intros q Hq. (pose proof (bslot_geo L st X ALO WF (qb_slot q) (bslot_range L st X Q WF CP q Hq)) as ndP__; nd_pre ndP__ 3%nat; intros B0 B1 _; nd_post). atop_facts. lia. }
  assert (LF64 : 0 <= qfirst L (q_loc Q) < 2^64).
  { destruct (qfirst_cases L (q_loc Q)) as [-> |(q & Hq & ->)]; [lia| apply AB64; apply in_or_app; left; exact Hq]. }
  assert (LL64 : 0 <= qlast L (q_loc Q) < 2^64).
  { destruct (qlast_cases L (q_loc Q)) as [-> |(q & Hq & ->)]; [lia| apply AB64; apply in_or_app; left; exact Hq]. }
  assert (DELTA : ek_delta ek n <= n + 8192) by (subst ek; unfold ek_of; destruct (enq_is_app st); cbn [ek_delta]; lia).
  (* [comment removed for export] *)
  unfold AIMG_HI, AFREE_STACK, UDEPTH, Q_MAX, Q_CACHE in *.
  box DT. box DC. box DN. box DSO. box DF. box CL5. box DL7. box DL8. box DL9. box DL10.
  eapply evtF_mono.
  { eapply (dfn_fast_spec DI L ek g RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m
              (al_t L) (al_ctx L) (fhm L c k n) n b1 ctx lo
              (Z.of_nat (length (a_qloc st))) (qfirst L (q_loc Q)) (qlast L (q_loc Q)) (a_qloc_bytes st) SO (1 + Z.of_nat (length trt)) pc
              uw _ _ sj tb (block_shadow_bytes n) trt).
    all: rewrite ?EHM.
    all: try lazymatch goal with
         | |- stk _ _ _ _ => first [exact ST | exact IAS]
         | |- ablk _ (_ + 16 + rup _ 8) => first [assumption | unfold ablk; right; generalize HLO HHI; try generalize EHM; clear; unfold fhm; intros; lia]   (* [comment removed for export] *)
         | |- mem_inv _ _ => exact MI
         | |- allocA_cells _ _ _ => unfold allocA_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
         | |- poison_cells _ => unfold poison_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
         | |- ADEPOT _ _ _ => exact HD
         | |- In _ _ => exact TRU
         | |- u64arr _ _ (_ + 2800) _ => exact STATS
         | |- u64arr _ _ _ _ => exact TB
         | |- map _ _ = _ => exact TRF
         | |- forall j, _ => exact IAM
         | |- rw_cells _ _ _ [C8 _; C4 _; C4 _] => exact SS
         | |- ek_pre _ _ _ _ _ _ _ _ => exact EK
         | |- ek_seps _ _ _ _ => exact ES
         | |- dk_pre _ _ _ _ _ _ _ _ => exact DK
         | |- dk_seps _ _ _ => exact DS
         | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact HDR
         | |- rw_cells _ _ (shad _) _ => eapply rw_cells_addr_eq; [exact SHU| f_equal; lia]
         | |- rw_cells _ _ (_ + 80) _ => exact QC
         | |- rw_cells _ _ (_ - 16 + 16) [C8 _] => eapply rw_cells_addr_eq; [exact HUW| lia]
         end.
    all: try lazymatch goal with
         | |- rw_cells _ _ _ [C8 _; C8 _; C8 _] => first [exact T0 | exact QK]
         | |- rw_cells _ _ _ _ => assumption
         | |- @eq word _ _ => first [exact TP | exact Ha0 | exact Ha2 | exact Ha3 | exact Ha4 | exact Ha5 | rewrite Ha1, <- Uy; subst AB UB; apply Z_to_bv_eqm; first [(generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LL64 ED0 DELTA RA4; clear; intros; lia) | lia] | reflexivity]   (* [comment removed for export] *)
         | |- _ \/ _ => first [unboxed DT | unboxed DC | unboxed DN | unboxed DSO | unboxed CL5 | unboxed DL7 | unboxed DL8 | unboxed DL9 | unboxed DL10
                             | ub DT; (generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LL64 ED0 DELTA RA4; clear -Y; intros; lia) | ub DC; (generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LL64 ED0 DELTA RA4; clear -Y; intros; lia) | ub DN; (generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LL64 ED0 DELTA RA4; clear -Y; intros; lia) | ub DSO; (generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LL64 ED0 DELTA RA4; clear -Y; intros; lia)
                             | ub DT; lia | ub DC; lia | ub DN; lia | ub DSO; lia]
         | |- rng _ (shad _) _ => replace (UB - 16 + 16) with UB by (clear; lia); eapply rng_sub; [exact RSS| rewrite SE; first [(generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LL64 ED0 DELTA RA4; clear; intros; lia) | lia]| rewrite SE, GE; first [(generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LL64 ED0 DELTA RA4; clear; intros; lia) | lia]]
         | |- rng _ _ _ => first [assumption | eapply rng_sub; [exact RSL| (generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LL64 ED0 DELTA RA4; clear; intros; lia)| (generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LL64 ED0 DELTA RA4; clear; intros; lia)] | eapply rng_sub; [exact RCTX| (generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LL64 ED0 DELTA RA4; clear; intros; lia)| (generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LL64 ED0 DELTA RA4; clear; intros; lia)] | eapply rng_sub; [exact RSL| lia| lia] | eapply rng_sub; [exact RCTX| lia| lia] | solve_rng]
         end.
    all: try assumption.
    all: unfold AIMG_HI, Q_MAX, Q_CACHE, Q_BATCH_BYTES, UDEPTH in *.
    all: try (generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6
                         B10 LLB NC NM LF64 LL64 ED0 DELTA RA4; clear; intros; lia).
    all: try (tclr_solve ALO ltac:((pose proof (slot_geo L st X c k ALO WF HC KR) as ndP__; nd_pre ndP__ 10%nat; intros _ _ _ _ _ _ _ SG5 SG6 _; nd_post);
                                    unfold K_SPACE_SIZE in SG6; change (2^37) with 137438953472 in SG6;
                                    generalize SG5 SG6 ABHM UBS RUP N0 N1; subst UB AB; clear; intros; lia)).      (* [comment removed for export] *)
    all: try (clear -LTRT; lia).
    all: match goal with |- ?G => idtac "REMF" G end. }
  cbv beta. intros ms' PM. rewrite EHM in PM.
  (* [comment removed for export] *)
  eapply (STORE L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st LB X Q p c k n b1 ctx A lo k24 l1 l2 stj chunks).
  all: try lazymatch goal with
       | |- free_fast_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => exact PM
       | |- alayout_ok _ => exact ALO
       | |- arng _ _ _ => exact ARNG
       | |- AREP _ _ _ _ _ => exact AR
       | |- AQUAR_at _ _ _ _ _ => exact AQ
       | |- ablocks _ _ _ _ => exact BL
       | |- In _ _ => exact HIN
       | |- _ = _ => exact XB
       | |- _ = false -> _ => exact NEWF
       | |- ek_pre _ _ _ _ _ _ _ _ => exact EK
       | |- dk_pre _ _ _ _ _ _ _ _ => exact DK
       end.
  all: try assumption.
  all: try (generalize N1 LO BOT STK3; clear; intros; unfold AFREE_STACK in *; lia).
  all: match goal with |- ?G => idtac "REMS" G end.
Qed.
End S.
End CANSEC1.
End TwB.
End ADfn_arep.

(* [comment removed for export] *)
Module AFreeNull.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecFacts AImg AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AQConst. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AMalloc_iface. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitR__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARealloc_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecSlog__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aunwind. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_adrain__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_front__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_arep__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_aalloc_s OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.F_aalloc1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aunwind OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_adrain__A3W.F_afree_iseg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_afree_null OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.F_afree_arep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac hide_disj_all := repeat match goal with H : (_ \/ _) |- _ => change (?P) with (sf_hide P) in H end.
Local Ltac hide_disj_but X :=
  repeat match goal with H : (_ \/ _) |- _ => tryif constr_eq H X then fail else change (?P) with (sf_hide P) in H end.
Local Ltac lia_rel := first [ solve [ hide_disj_all; lia ] | match goal with X : (_ \/ _) |- _ => solve [ hide_disj_but X; lia ] end ].
Local Ltac lia_relc := repeat split; first [ lia_rel | lia ].
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition q_set_ia (Q : qconc) : qconc := mkQConc (q_loc Q) (q_glob Q) true (q_pend Q).

(* [comment removed for export] *)
#[using="Type"] Lemma AQUAR_null : forall L st X Q m m' W,
  AQUAR_at L st X Q m -> munch W m m' -> wmono asegs m m' ->
  Forall (fun iv => (snd iv <= al_t L + 80 \/ al_t L + 208 <= fst iv)
                 /\ (snd iv <= AINSTANCE + 728 \/ AINSTANCE + 984 <= fst iv)
                 /\ (forall b, In b (x_busy X) -> match xb_st b with BLive _ => True | _ =>
                       snd iv <= xb_alloc L b \/ xb_alloc L b + size_of_class (xb_class b) <= fst iv end)) W ->
  aintal true m' ->
  AQUAR_at L st X (q_set_ia Q) m'.
Proof.
  intros L st X Q m m' W (GC & TC & GL & IA & CP & NUM) MU WM UT IA'.
  unfold AQUAR_at. cbn [q_loc q_glob q_ia q_pend q_set_ia].
  assert (DT : disjoint_from W (aq_tcache L) 32).
  { apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP.disjoint_from_Forall. eapply Forall_impl; [| exact UT]. intros iv (A & _). unfold aq_tcache. cbn in A |- *. lia. }
  assert (DG : disjoint_from W AQ_MAX 24 /\ disjoint_from W AQ_MUTEX 4 /\ disjoint_from W AQ_GCACHE 32).
  { unfold AQ_MAX, AQ_MUTEX, AQ_GCACHE, AINSTANCE in *.
    repeat split; apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP.disjoint_from_Forall; eapply Forall_impl; try exact UT; intros iv (_ & A & _); unfold AINSTANCE in A; cbn in A |- *; lia. }
  (nd_pre DG 3%nat; intros DG1 DG2 DG3; nd_post).
  assert (DQ : forall q, In q (q_loc Q ++ q_glob Q) -> disjoint_from W (abatch_addr L (qb_slot q)) Q_BATCH_BYTES).
  { intros q Hq. (nd_pre (qcoupled_bslot_busy L st X Q q CP Hq) 5%nat; intros b Hb Sb Cb Kb; nd_post).
    apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP.disjoint_from_Forall. eapply Forall_impl; [| exact UT]. intros iv (_ & _ & A).
    specialize (A b Hb). rewrite Sb in A. unfold xb_alloc in A. rewrite Cb, Kb, size_of_class_24 in A.
    unfold abatch_addr, Q_BATCH_BYTES. cbn. exact A. }
  split; [| split; [| split; [| split; [exact IA'| split; [| exact NUM]]]]].
  - eapply aquar_glob_const_frame; eassumption.
  - eapply aqcache_frame; [exact MU | exact WM | exact TC | exact DT |]. intros q Hq. apply DQ. apply in_app_iff. left. exact Hq.
  - eapply aqcache_frame; [exact MU | exact WM | exact GL | exact DG3 |]. intros q Hq. apply DQ. apply in_app_iff. right. exact Hq.
  - (* [comment removed for export] *)
    (nd_pre CP 8%nat; intros LN1 LN2 OK ND1 ND2 BS PS NN; nd_post).
    unfold qcoupled. cbn [q_loc q_glob q_pend]. cbv zeta.
    split; [exact LN1|]. split; [exact LN2|]. split; [exact OK|]. split; [exact ND1|]. split; [exact ND2|].
    split; [exact BS|]. split; [exact PS| exact NN].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition Wnull (SP t : Z) : list (Z * Z) :=
  [(SP - 4096, SP); (0xaf800, 0xaf800 + 0x81030); (0x13e088, 0x13e088 + 4); (t + 3168, t + 3169)]%Z.

Section S.
Variable DI : ADepotIface.
Variables (ASEC : alayout -> astate -> aconc -> amem -> Prop) (AFK : alayout -> list ablock -> amem -> Prop).
Hypothesis HL : ahole_laws (AHQ DI ASEC AFK).
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI
                                  /\ (snd iv <= 0xab270 \/ 0xab330 <= fst iv)
                                  /\ (snd iv <= 0xaf800 \/ 0x130830 <= fst iv)
                                  /\ (snd iv <= 0x13e088 \/ 0x13e08c <= fst iv)) CI.

Definition AREP_null__stmt : Prop := forall L st X Q m m' SP,
  alayout_ok L -> AREP (AHQ DI ASEC AFK) L st X m -> AQUAR_at L st X Q m ->
  munch (Wnull SP (al_t L)) m m' -> wmono asegs m m' -> ATOP + 4096 <= SP ->
  rw_cells asegs m' (al_t L + 3168) [C1 (Z_to_bv 8 0)] -> aintal true m' ->
  AREP (AHQ DI ASEC AFK) L st X m' /\ AQUAR_at L st X (q_set_ia Q) m'.
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'AREP_null__stmt 0).
Variable st : ltac2:(SecDietF.SzSecF.ty 'AREP_null__stmt 1).
Variable X : ltac2:(SecDietF.SzSecF.ty 'AREP_null__stmt 2).
Variable Q : ltac2:(SecDietF.SzSecF.ty 'AREP_null__stmt 3).
Variable m : ltac2:(SecDietF.SzSecF.ty 'AREP_null__stmt 4).
Variable m' : ltac2:(SecDietF.SzSecF.ty 'AREP_null__stmt 5).
Variable SP : ltac2:(SecDietF.SzSecF.ty 'AREP_null__stmt 6).
Let W := Wnull SP (al_t L).
#[using="HL W"] Lemma AREP_null__body : ltac:(let T := type of (fun (h : AREP_null__stmt) => h L st X Q m m' SP) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (st, (X, (Q, (m, (m', SP))))))) as _.
  intros ALO AR AQ MU WM HSP UNW' IA'.
  chg (Wnull SP (al_t L)) W.
  (* [comment removed for export] *)
  (pose proof (alayout_space L ALO) as ndP__; nd_pre ndP__ 4%nat; intros SP1 SP2 SP3 SP4; nd_post).
  pose proof (ao_t L ALO) as OT. pose proof (ao_ctx L ALO) as OC. pose proof (ao_res L ALO) as ORS. pose proof (ao_nodes L ALO) as ON.
  pose proof (ao_store L ALO) as OS. pose proof (ao_fake L ALO) as OFK. pose proof (ao_dtls L ALO) as ODT.
  unfold aobj in OT, OC, ORS, ON, OS, OFK, ODT. pose proof (ao_space L ALO) as RSP.
  pose proof (ao_res_hi L ALO) as RHI. unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in OT, OC, ORS, ON, OS, OFK, ODT.   (* [comment removed for export] *)
  pose proof (ad_t_res L ALO) as D_t_res. pose proof (ad_t_ctx L ALO) as D_t_c. pose proof (ad_t_nodes L ALO) as D_t_n.
  pose proof (ad_t_store L ALO) as D_t_s. pose proof (ad_t_fake L ALO) as D_t_f. pose proof (ad_t_dtls L ALO) as D_t_d.
  unfold adisj in D_t_res, D_t_c, D_t_n, D_t_s, D_t_f, D_t_d.
  assert (SHRES : 2201439137792 <= shad (al_res L) /\ shad (al_res L) + shlen 137439023104 = shad (al_res L + 137439023104)
                  /\ shad (al_res L + 137439023104) <= 17594332446720).   (* [comment removed for export] *)
  { rewrite !shad_div, shlen_div. unfold ASHOFF in *. clear -ORS RHI. Z.div_mod_to_equations. lia. }
  (nd_pre SHRES 3%nat; intros SR1 SR2 SR3; nd_post).
  (* [comment removed for export] *)
  assert (Kimg : forall A k, 0x10000 <= A -> 0 <= k -> A + k <= AIMG_HI ->      (* [comment removed for export] *)
            (A + k <= 0xaf800 \/ 0x130830 <= A) -> (A + k <= 0x13e088 \/ 0x13e08c <= A) -> disjoint_from W A k).
  { intros A k H1 H2 H3 H4 H5. unfold W, Wnull. cbn. unfold AIMG_HI in *. clear -H1 H2 H3 H4 H5 HSP OT. lia. }
  assert (Kobj : forall A k, AIMG_HI <= A -> 0 <= k -> A + k <= ATOP -> (A + k <= al_t L + 3168 \/ al_t L + 3169 <= A) -> disjoint_from W A k).
  { intros A k H1 H2 H3 H4. unfold W, Wnull. cbn. unfold AIMG_HI in *. clear -H1 H2 H3 H4 HSP. lia. }
  assert (Kres : forall A k, al_res L <= A -> 0 <= k -> A + k <= al_res L + 137439023104 -> disjoint_from W A k).
  { intros A k H1 H2 H3. apply Kobj; unfold AIMG_HI in *; [clear -H1 ORS; lia | exact H2 | clear -H3 ORS; lia | clear -H1 H3 D_t_res; lia]. }
  assert (Kres_sh : forall A k, shad (al_res L) <= A -> 0 <= k -> A + k <= shad (al_res L + 137439023104) -> disjoint_from W A k).
  { intros A k H1 H2 H3. apply Kobj; unfold AIMG_HI in *; [clear -H1 SR1; lia | exact H2 | clear -H3 SR3; lia | clear -H1 H3 SR1 SR3 OT; lia]. }
  assert (Kt : forall A k, al_t L <= A -> 0 <= k -> A + k <= al_t L + 3168 -> disjoint_from W A k).
  { intros A k H1 H2 H3. unfold W, Wnull. cbn. unfold AIMG_HI in *. clear -H1 H2 H3 HSP OT. lia. }   (* [comment removed for export] *)
  assert (Kctx : forall A k, al_ctx L <= A -> 0 <= k -> A + k <= al_ctx L + 65536 -> disjoint_from W A k).
  { intros A k H1 H2 H3. apply Kobj; unfold AIMG_HI in *; [clear -H1 OC; lia | exact H2 | clear -H3 OC; lia | clear -H1 H3 D_t_c; lia]. }
  assert (Ktls : forall A k, ATPv + -200 <= A -> 0 <= k -> A + k <= ATPv + 312 -> disjoint_from W A k).      (* [comment removed for export] *)
  { pose proof (ad_tls_t L ALO) as D_tls_t. unfold adisj in D_tls_t. pose proof atp_lin as TLN. pose proof atop_range as ATR0.
    intros A k H1 H2 H3. unfold W, Wnull. cbn. unfold AIMG_HI in *. clear -H1 H2 H3 HSP OT D_tls_t TLN ATR0. lia. }
  (* [comment removed for export] *)
  pose proof AR as AR0. (nd_pre AR0 12%nat; intros WF RT INST THR CLS HQ HS HD HRO RT2 AVL RT3; nd_post).
  pose proof WF as WF0. (nd_pre WF0 11%nat; intros SBE PAE SAL SLO SHI PERC OUTC BUSY LIVE FRESH UNIQ; nd_post).
  (* [comment removed for export] *)
  assert (BB : forall b, In b (x_busy X) -> al_res L <= xb_alloc L b /\ xb_alloc L b + size_of_class (xb_class b) <= al_res L + 137439023104).
  { intros b Hb. destruct (BUSY b Hb) as [CLB _].
    (nd_pre (PERC (xb_class b) CLB) 12%nat; intros Q1 Q2 _ _ _ _ _ _ _ _ _ QR; nd_post).
    pose proof (size_of_class_facts (xb_class b) CLB) as [QS _].
    assert (KB : 0 <= xb_slot b < ndist st (xb_class b)).
    { apply QR. apply in_app_iff. right. apply in_app_iff. right. unfold busy_slots. apply in_map_iff. exists b. split; [reflexivity|].
      apply filter_In. split; [exact Hb| apply Z.eqb_refl]. }
    (pose proof (slot_in_region L st (xb_class b) (xb_slot b) ltac:(clear -QS; lia) (proj1 Q1) KB) as ndP__; nd_pre ndP__ 3%nat; intros P5 P4 P0; nd_post).
    unfold xb_alloc, aregion, K_REGION, K_FREEARR_OFF, K_NUM_CLASSES in *. clear -P5 P4 Q1 Q2 CLB RSP. lia. }
  assert (AQ' : AQUAR_at L st X (q_set_ia Q) m').
  { eapply AQUAR_null; [exact AQ | exact MU | exact WM | | exact IA'].
    unfold W, Wnull. unfold AINSTANCE, AIMG_HI in *.
    repeat (apply Forall_cons; [cbn [fst snd]; split; [clear -OT HSP; lia|]; split; [clear -OT HSP; lia|];
                                intros b Hb; destruct (BB b Hb) as [B1 B2]; destruct (xb_st b); [exact I| |]; clear -B1 B2 ORS OT HSP D_t_res; lia |]).
    apply Forall_nil. }
  split; [| exact AQ'].
  split; [exact WF|].
  split. { eapply arep_rt_frame; [exact MU | exact WM | exact RT |]. unfold rt_hulls, ATP88, ATSD.
           repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply Ktls; clear; lia] |]). apply Forall_nil. }
  split. { eapply ainstance_frame; [exact MU | exact WM | exact INST | reflexivity | reflexivity | | |]; apply Kimg; clear; unfold AINSTANCE, AIMG_HI; lia. }
  split.
  { (nd_pre THR 6%nat; intros T0 T40 CACHES CSTATS [sj [STATS LSJ]] UNW; nd_post). unfold athread.
    split; [eapply cells_frame; [exact T0 | exact MU | exact WM | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; apply Kt; clear; lia]|].
    split; [eapply cells_frame; [exact T40 | exact MU | exact WM | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; apply Kt; clear; lia]|].
    split. { intros c Hc. eapply acache_cells_frame; [exact MU | exact WM | exact (CACHES c Hc) | reflexivity | reflexivity | reflexivity |].
             unfold acache_addr. unfold K_NUM_CLASSES in Hc. apply Kt; clear -Hc; lia. }
    split; [eapply junk_frame; [exact CSTATS | exact MU | exact WM | intros _; apply Kt; clear; lia]|].
    split; [exists sj; split; [eapply u64arr_frame; [exact STATS | exact MU | exact WM | replace (8 * Z.of_nat (length sj)) with 368 by (rewrite LSJ; reflexivity); apply Kt; clear; lia] | exact LSJ]|].
    exact UNW'. }
  split.
  { intros c Hc. (nd_pre (CLS c Hc) 4%nat; intros REG FARR SLOTS SHADOW; nd_post).
    (nd_pre (PERC c Hc) 12%nat; intros Q1 Q2 Q3 Q4 Q5 Q6 Q7 QLENF QLENC QCNTB QND QRANGE; nd_post).
    pose proof (size_of_class_facts c Hc) as [QS QS16]. pose proof (aregion_mod L c SAL) as RM. unfold K_NUM_CLASSES in Hc.
    assert (RI : al_res L <= aregion L c /\ aregion L c + K_REGION <= al_space_beg L + K_SPACE_SIZE
                 /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
    { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc RSP. lia. }
    (nd_pre RI 3%nat; intros RI1 RI2 RI3; nd_post). unfold K_REGION, K_SPACE_SIZE in RI2, RI3. change (2^37) with 137438953472 in RI2, RI3.
    split; [| split; [| split]].
    - eapply aregion_cells_frame; [exact MU | exact WM | exact REG | reflexivity | reflexivity | reflexivity | reflexivity |].
      apply Kres; unfold aregion_info, ARI_STRIDE, K_SPACE_SIZE; change (2^37) with 137438953472; clear -Hc RSP; lia.
    - eapply afreearray_frame; [exact MU | exact WM | exact FARR | reflexivity | reflexivity | reflexivity | exact QLENF | exact Q5 | | clear -Q6; lia |].
      + apply Kres; unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX in *; [clear -RI1; lia | clear -Q5 Q6; lia | clear -RI2 RI3 Q6; lia].
      + apply Kres_sh; [apply shad_mono; unfold afreearr, K_FREEARR_OFF; clear -RI1; lia | apply shlen_nonneg; clear -Q5 Q6; lia |].
        rewrite <- shad_add_shlen by (unfold afreearr, K_FREEARR_OFF; clear -RM; Z.div_mod_to_equations; lia). apply shad_mono.
        unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX in *. clear -RI2 RI3 Q6. lia.
    - eapply (aslots_update L W m m' MU WM st st X X c (-1)); [exact SLOTS | reflexivity | reflexivity | reflexivity | | | intros Hk; exfalso; clear -Hk; lia].
      + intros k Hk _. (pose proof (slot_in_region L st c k ltac:(clear -QS; lia) (proj1 Q1) Hk) as ndP__; nd_pre ndP__ 3%nat; intros P5 P4 P0; nd_post).
        split; [reflexivity|]. split.
        * apply Kres; [clear -P5 RI1; lia | clear -QS; lia | clear -P4 Q1 Q2 RI2 RI3; unfold K_FREEARR_OFF in *; lia].
        * intros b Hb. pose proof Hb as Hb'. unfold busy_of in Hb'. apply find_some in Hb'. destruct Hb' as [HIn HP].
          apply andb_true_iff in HP. destruct HP as [HP1 HP2]. apply Z.eqb_eq in HP1. apply Z.eqb_eq in HP2.
          split; [exact HP1|]. split; [exact HP2|]. exact (awf_fits L st X b WF HIn).
      + intros POS. apply Kres; [clear -Q1 RI1; lia | clear -POS; lia | clear -Q1 Q2 RI2 RI3; unfold K_FREEARR_OFF in *; lia].
    - eapply (aslot_shadow_update L W m m' MU WM st st X X c (-1)); [exact SHADOW | reflexivity | reflexivity | reflexivity | | | intros Hk; exfalso; clear -Hk; lia | apply shlen_nonneg; clear -QS; lia].
      + intros k Hk _. (pose proof (slot_in_region L st c k ltac:(clear -QS; lia) (proj1 Q1) Hk) as ndP__; nd_pre ndP__ 3%nat; intros P5 P4 P0; nd_post).
        pose proof (slot_aligned L c k SAL ltac:(unfold K_NUM_CLASSES; clear -Hc; lia)) as AL.
        split; [reflexivity|]. apply Kres_sh; [apply shad_mono; clear -P5 RI1; lia | apply shlen_nonneg; clear -QS; lia |].
        rewrite <- shad_add_shlen by (clear -AL; Z.div_mod_to_equations; lia). apply shad_mono. clear -P4 Q1 Q2 RI2 RI3. unfold K_FREEARR_OFF in *. lia.
      + intros POS. apply Kres_sh; [apply shad_mono; clear -Q1 RI1; lia | clear -POS; lia |].
        rewrite <- shad_add_shlen by (pose proof (mod16_of_class _ _ Q3 QS16 ltac:(clear -QS; lia)) as AM; clear -AM RM; Z.div_mod_to_equations; lia).
        apply shad_mono. clear -Q1 Q2 RI2 RI3. unfold K_FREEARR_OFF in *. lia. }
  split; [exists (q_set_ia Q); exact AQ'|].
  split.
  { cbn [ah_sec AHQ]. cbn [ah_sec AHQ] in HS.
    eapply (hs_frame _ HL L st st X X m m' W); [exact HS | exact MU | exact WM | |].
    - unfold sec_untouched, aknown, W, Wnull. unfold AINSTANCE, AIMG_HI in *.
      (* [comment removed for export] *)
      apply Forall_cons; [cbn [fst snd]; intros a Ha; do 4 right; left; clear -Ha HSP; lia|].
      do 2 (apply Forall_cons; [cbn [fst snd]; intros a Ha; left; clear -Ha; lia|]).
      apply Forall_cons; [cbn [fst snd]; intros a Ha; do 5 right; left; clear -Ha OT; lia|].
      apply Forall_nil.
    - apply sec_same_refl. }
  split.
  { cbn [ah_depot AHQ]. cbn [ah_depot AHQ] in HD.
    eapply (hd_frame _ HL L m m' W); [exact HD | exact MU | exact WM |].
    unfold W, Wnull. unfold AIMG_HI in *.
    repeat (apply Forall_cons; [cbn [fst snd]; intros a Ha; clear -Ha OT ON OS HSP D_t_n D_t_s; lia|]). apply Forall_nil. }
  split; [eapply arelro_frame; [exact MU | exact HRO | apply Kimg; clear; unfold ARELRO_LO, ARELRO_HI, AIMG_HI; lia]|].
  split; [eapply arep_rt2_frame; [exact MU | exact WM | exact RT2 | | |]; apply Kimg; clear; unfold AIMG_HI; lia|].
  split; [| eapply arep_rt3_frame; [exact MU | exact WM | exact RT3 |]; unfold rt3_hulls; repeat (apply Forall_cons; [cbn [fst snd]; apply Kimg; clear; unfold AIMG_HI; lia|]); apply Forall_nil].
  intros c Hc. (nd_pre (PERC c Hc) 8%nat; intros Q1 Q2 Q3 Q4 Q5 Q6 Q7 _; nd_post). unfold K_NUM_CLASSES in Hc.
  assert (RI : al_res L <= aregion L c /\ aregion L c + K_REGION <= al_space_beg L + K_SPACE_SIZE
               /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
  { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc RSP. lia. }
  (nd_pre RI 3%nat; intros RI1 RI2 RI3; nd_post). unfold K_REGION, K_SPACE_SIZE in RI2, RI3. change (2^37) with 137438953472 in RI2, RI3.
  eapply (ashadow_avail_frame L W m m' MU WM st); [exact (AVL c ltac:(unfold K_NUM_CLASSES; clear -Hc; lia)) | reflexivity | reflexivity | |].
  - intros POS. apply Kres_sh; [apply shad_mono; unfold aregion in *; clear -Q1 RI1; lia | clear -POS; lia |].
    rewrite <- shad_add_shlen by (pose proof (aregion_mod L c SAL) as RM; clear -RM Q4; unfold K_USER_MAP in *; Z.div_mod_to_equations; lia).
    apply shad_mono. unfold K_FREEARR_OFF, K_REGION in *. clear -Q1 Q2 RI2 RI3. lia.
  - intros POS. apply Kres_sh; [apply shad_mono; unfold afreearr, K_FREEARR_OFF, aregion in *; clear -Q5 Q6 RI1; lia | clear -POS; lia |].
    rewrite <- shad_add_shlen by (pose proof (aregion_mod L c SAL) as RM; unfold afreearr, K_FREEARR_OFF; clear -RM Q7; unfold K_FREEARR_MAP in *; Z.div_mod_to_equations; lia).
    apply shad_mono. unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q5 Q6 RI2 RI3. lia.
Qed.
End Zd1.
#[using="HL"] Lemma AREP_null : ltac:(let t := eval cbv delta [AREP_null__stmt] in AREP_null__stmt in exact t).
Proof. exact AREP_null__body. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition afree_nullP__stmt : Prop := afree_null_stmt CI (AHEAP_P (AHQ DI ASEC AFK)).
Section Zd2.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'afree_nullP__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'afree_nullP__stmt 1).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'afree_nullP__stmt 2).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'afree_nullP__stmt 3).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'afree_nullP__stmt 4).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'afree_nullP__stmt 5).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'afree_nullP__stmt 6).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'afree_nullP__stmt 7).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'afree_nullP__stmt 8).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'afree_nullP__stmt 9).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'afree_nullP__stmt 10).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'afree_nullP__stmt 11).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'afree_nullP__stmt 12).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'afree_nullP__stmt 13).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'afree_nullP__stmt 14).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'afree_nullP__stmt 15).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'afree_nullP__stmt 16).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'afree_nullP__stmt 17).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'afree_nullP__stmt 18).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'afree_nullP__stmt 19).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'afree_nullP__stmt 20).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'afree_nullP__stmt 21).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'afree_nullP__stmt 22).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'afree_nullP__stmt 23).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'afree_nullP__stmt 24).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'afree_nullP__stmt 25).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'afree_nullP__stmt 26).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'afree_nullP__stmt 27).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'afree_nullP__stmt 28).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'afree_nullP__stmt 29).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'afree_nullP__stmt 30).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'afree_nullP__stmt 31).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'afree_nullP__stmt 32).
Variable F : ltac2:(SecDietF.SzSecF.ty 'afree_nullP__stmt 33).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'afree_nullP__stmt 34).
Variable m : ltac2:(SecDietF.SzSecF.ty 'afree_nullP__stmt 35).
Variable st : ltac2:(SecDietF.SzSecF.ty 'afree_nullP__stmt 36).
Variable LB : ltac2:(SecDietF.SzSecF.ty 'afree_nullP__stmt 37).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'afree_nullP__stmt 38).
Variable tr : ltac2:(SecDietF.SzSecF.ty 'afree_nullP__stmt 39).
#[using="HL CI_OK"] Lemma afree_nullP__body : ltac:(let T := type of (fun (h : afree_nullP__stmt) => h L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st LB lo tr) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (st, (LB, (lo, tr)))))))))))))))))))))))))))))))))))))))) as _.
  unfold afree_null_stmt.  intros AH MI ST BOT LO TP Ha0 AUNW S0NE RA4 RANE SP16 RSTK.
  assert (UNWX : exists trt, afree_unw RNG lo m (al_top L) sp s0 ra trt /\ In (AFREE_PC :: trt) (al_U L)).
  { destruct AUNW as [(BT & UC & LTR & TRU & RTOP)|(TOPLE & SPLT & TRU)]; [exists (bv_unsigned ra :: tr); split; [left; exists tr; split; [reflexivity|]; split; [exact UC|]; split; [exact LTR|]; split; [exact BT| exact RTOP]| exact TRU] | exists (@nil Z); split; [right; auto| exact TRU]]. }
  (nd_pre UNWX 3%nat; intros trt FUNW TRU; nd_post).
  (nd_pre AH 4%nat; intros ALO ARNG [X [AR BL]] HFK; nd_post).
  pose proof AR as AR0. (nd_pre AR0 12%nat; intros WF RT INST THR CLS HQ HS HD HRO HRT2 AVL RT3; nd_post).
  cbn [ah_quar ah_sec ah_depot ah_fake AHQ] in HQ, HS, HD, HFK. destruct HQ as [Q AQ].
  pose proof WF as WF0. (nd_pre WF0 11%nat; intros SBE PAE SAL SLO SHI PERC OUTC BUSY LIVEB FRESH UNIQ; nd_post).
  (* [comment removed for export] *)
  pose proof ARNG as ARNG0. (nd_pre ARNG0 14%nat; intros RIMG RT4 RCTX RNO RSTO RRI RFK RSFK RDT RCLS RPA RSECS RPSH RTLS; nd_post).
  (pose proof (alayout_t L ALO) as ndP__; nd_pre ndP__ 4%nat; intros TL1 TL2 TL3 TL4; nd_post). pose proof TL1 as TL1u. pose proof TL4 as TL4u. unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in TL1u, TL4u.   (* [comment removed for export] *)
  (pose proof (alayout_ctx L ALO) as ndP__; nd_pre ndP__ 5%nat; intros CL1 CL2 CL3 CL4 CL5; nd_post).
  (pose proof (alayout_stack L ALO) as ndP__; nd_pre ndP__ 3%nat; intros STK1 STK2 STK3; nd_post).
  assert (SP47 : bv_unsigned sp < 2^47) by (eapply afree_unw_sp47; [exact FUNW| exact STK2]).
  pose proof (ao_t L ALO) as OT. pose proof (ao_res L ALO) as ORS. pose proof (ao_fake L ALO) as OFK. pose proof (ao_dtls L ALO) as ODT.
  unfold aobj in OT, ORS, OFK, ODT. pose proof (ao_space L ALO) as RSP. pose proof (ao_res_hi L ALO) as RHI. unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in OT, ORS, OFK, ODT.   (* [comment removed for export] *)
  pose proof (ad_t_res L ALO) as D_t_res. pose proof (ad_t_fake L ALO) as D_t_f. pose proof (ad_t_dtls L ALO) as D_t_d.
  unfold adisj in D_t_res, D_t_f, D_t_d.
  (* [comment removed for export] *)
  pose proof RT as RT0.
  (nd_pre RT0 28%nat; intros GPG GOT GOT80 RIC LS1 REAL IMAX4 FLG5 FLG HPP SHB CANP TI TK INI2 LAY MCS OOM3 PGC HK2 CF8 CF34 CSMT T88 TSD LS2 CT8 CT; nd_post).
  pose proof INI2 as INI. rw_split INI 1%nat INI1 INIx. clear INIx.
  pose proof OOM3 as OOM. rw_split OOM 2%nat OOMx RSS0. clear OOMx.
  pose proof IMAX4 as IMAX. rw_split IMAX 3%nat IMAX3 IMAXx. clear IMAXx.
  (nd_pre THR 6%nat; intros T0 T40 CACHES CSTATS [sj [STATS LSJ]] UNW; nd_post).
  pose proof AQ as AQ0. (nd_pre AQ0 6%nat; intros _ _ _ (FL & IAS & IAM) CP _; nd_post).
  unfold AIA_FLAG, AIA_BASE, AIA_SIZE, AIA_MAP1, AIA_MAP1_LEN in FL, IAS, IAM.
  (* [comment removed for export] *)
  unfold AIMG_HI, AFREE_STACK, UDEPTH in *.
  box CL5.
  eapply evtF_mono.
  { eapply (free_null_spec (q_ia Q) RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m
              (al_t L) (al_ctx L) lo (al_top L) (al_bot L) trt).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => first [exact ST | exact IAS]
         | |- mem_inv _ _ => exact MI
         | |- allocA_cells _ _ _ => unfold allocA_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
         | |- afree_unw _ _ _ _ _ _ => exact FUNW
         | |- _ = true -> _ => exact IAM
         end.
    all: try lazymatch goal with
         | |- rw_cells _ _ _ [C8 _; C8 _; C8 _] => exact T0
         | |- rw_cells _ _ _ _ => assumption
         | |- @eq word _ _ => first [exact TP | exact Ha0 | reflexivity]
         | |- _ \/ _ => first [unboxed CL5 | pose proof CL5 as Y; unbox Y; lia]
         | |- rng _ _ _ => first [assumption | eapply rng_sub; [exact RCTX| lia| lia] | solve_rng]
         end.
    all: try assumption.
    all: unfold AIMG_HI, UDEPTH in *.
    all: try (generalize LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 RA4; clear; intros; lia).
    all: match goal with |- ?G => idtac "REMF" G end. }
  cbv beta. intros ms' PM.
  (nd_pre PM 17%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 8%nat; intros MU WM MI' ST' UNW' FL' IAS' IAM'; nd_post).
  change (munch (Wnull (bv_unsigned sp) (al_t L)) m m') in MU.
  assert (IA' : aintal true m').
  { unfold aintal, AIA_FLAG, AIA_BASE, AIA_SIZE, AIA_MAP1, AIA_MAP1_LEN. split; [exact FL'|]. split; [exact IAS'|]. intros _. exact IAM'. }
  destruct (AREP_null L st X Q m m' (bv_unsigned sp) ALO AR AQ MU WM ltac:(atop_facts; clear -LO BOT STK3; lia) UNW' IA') as [AR' AQ'].
  (* [comment removed for export] *)
  exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
  split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split.
  { (* [comment removed for export] *)
    intros a Ha CLA. split; [| intros Hw; apply WM; exact Hw]. apply MU. rewrite wa_unsigned by exact Ha.
    word_range sp SPR.
    unfold Wnull. cbn [outside].
    destruct CLA as [CLA|TL].
    2:{ (* [comment removed for export] *)
        pose proof (ad_tls_t L ALO) as DLT. unfold adisj in DLT. pose proof atp_lin as TLN. pose proof atop_range as ATR0. pose proof atp_below_atop as TBA.
        destruct TL as [[T|(ta & Hta & ->)]|[IM|IM]].
        4:{ pose proof (ao_ahm L ALO) as OAH. pose proof (aobj_img _ _ OAH ltac:(clear; lia)) as OAHI. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OAH, OAHI.
          rewrite <- (ao_ahm_eq L ALO) in IM. unfold AAHM_SZ in IM. pose proof (ad_ahm_t L ALO) as DA1. unfold adisj in DA1.
            clear -IM OAH OAHI DA1 Ha LO BOT STK3 ATR0. lia. }
        - clear -T Ha DLT TLN ATR0 TBA LO BOT STK3. lia.
        - pose proof (tls_shadow_band ta Hta) as (TS1 & TS2).
          assert (SA : shad ATOP <= 17594332446720) by (rewrite shad_div; unfold ASHOFF; clear -ATR0; Z.div_mod_to_equations; lia).
          clear -TS1 TS2 SA Ha TL1u LO BOT STK3 ATR0. lia.
        - unfold AIMSH_LO, AIMSH_LEN in IM. clear -IM Ha TL1u LO BOT STK3 ATR0. lia. }
    destruct CLA as [SK | [CIa | [BLK | SH]]].
    - clear -SK Ha LO BOT STK3 TL2. lia.
    - (nd_pre CIa 3%nat; intros iv Hiv R; nd_post). (pose proof (proj1 (Forall_forall _ _) CI_OK iv Hiv) as ndP__; nd_pre ndP__ 6%nat; intros Q1 Q2 Q3 Q4 Q5 Q6; nd_post). cbn [fst snd] in *.
      unfold AIMG_HI in *. clear -R Q1 Q3 Q5 Q6 LO BOT STK3 TL4u. lia.
    - (nd_pre BLK 3%nat; intros [[q|cls] A' n'] Hin R; nd_post); cbn [ab_addr ab_size] in R.
      + destruct (proj1 BL q A' n' Hin) as [(b & Hb & Sb & Ub & Nb)|(mb & msz & Lp & EUA & Gs)].
        * destruct (BUSY b Hb) as [CLB _].
          (nd_pre (PERC (xb_class b) CLB) 12%nat; intros P1 P2 _ _ _ _ _ _ _ _ _ PR; nd_post).
          pose proof (size_of_class_facts (xb_class b) CLB) as [QS _].
          assert (KB : 0 <= xb_slot b < ndist st (xb_class b)).
          { apply PR. apply in_app_iff. right. apply in_app_iff. right. unfold busy_slots. apply in_map_iff. exists b. split; [reflexivity|].
            apply filter_In. split; [exact Hb| apply Z.eqb_refl]. }
          (pose proof (slot_in_region L st (xb_class b) (xb_slot b) ltac:(clear -QS; lia) (proj1 P1) KB) as ndP__; nd_pre ndP__ 3%nat; intros P5 P4 P0; nd_post).
          pose proof (awf_fits L st X b WF Hb) as FIT. unfold xb_fits in FIT. rewrite Sb in FIT.
          subst A' n'. unfold xb_user, xb_alloc, aregion, K_REGION, K_FREEARR_OFF, K_NUM_CLASSES in *.
          clear -R P5 P4 P1 P2 CLB RSP FIT ORS D_t_res LO BOT STK3. lia.
        * (* [comment removed for export] *)
          cbn [sec_wf1] in Gs. (nd_pre Gs 7%nat; intros Gs1 Gs2 Gs3 Gs4 Gs5 Gs6 (Ct & Cc & Cr & Cp & Cn & Cs & Cf & Cd); nd_post).
          pose proof (sec_facts n' ltac:(clear -Gs5; lia) Gs6) as SF. subst A'. unfold SEC_UOFF, K_HIGH_MEM in *.
          unfold ablk, KLS, AIMG_HI in Gs2.   (* [comment removed for export] *)
          clear -R Gs2 Gs3 Gs4 Gs5 SF Ct LO BOT STK3. lia.
      + (nd_pre (proj1 (proj2 BL) cls A' n' Hin) 3%nat; intros K1 K2 K3; nd_post).
        clear -R K1 K2 K3 OFK D_t_f LO BOT STK3. lia.
    - (nd_pre SH 3%nat; intros a' Ha' ndR1__; nd_post; revert ndR1__; intros ->). rewrite shad_div in Ha |- *. unfold ASHOFF in *.
      assert (A47 : 0 <= a' < 2^47).
      { destruct Ha' as [SK | [CIa | FK]].
        - atop_facts. clear -SK SPR. lia.
        - (nd_pre CIa 3%nat; intros iv Hiv R; nd_post). (pose proof (proj1 (Forall_forall _ _) CI_OK iv Hiv) as ndP__; nd_pre ndP__ 4%nat; intros Q1 Q2 Q3 _; nd_post). cbn [fst snd] in *.
          unfold AIMG_HI in *. clear -R Q1 Q3. lia.
        - (nd_pre FK 5%nat; intros cls FA sz Hin R; nd_post). (nd_pre (proj1 (proj2 BL) cls FA sz Hin) 3%nat; intros K1 K2 K3; nd_post). clear -R K1 K3 OFK. lia. }
      clear -A47 LO BOT STK3 TL1u. Z.div_mod_to_equations. lia. }
  split; [exact ALO|]. split; [exact ARNG|]. split; [exists X; split; [exact AR'| exact BL]|].
  (* [comment removed for export] *)
  cbn [ah_fake AHQ].
  assert (SF : 2148238848 <= shad (al_fake L) /\ shad (al_fake L) + shlen 11571200 <= 17594332446720).   (* [comment removed for export] *)
  { rewrite shad_div, shlen_div. unfold ASHOFF in *. pose proof atop_range as AR8. clear -OFK AR8. Z.div_mod_to_equations. lia. }
  eapply (hf_frame _ HL L LB m m'); [exact HFK | exact MU | exact WM |].
  unfold fake_untouched, Wnull.
  pose proof (ad_tls_t L ALO) as D_l_t. unfold adisj in D_l_t. pose proof atp_lin as TLN. pose proof atop_range as ATR0.      (* [comment removed for export] *)
  repeat (apply Forall_cons; [cbn [fst snd]; clear -OFK ODT OT SF D_t_f D_t_d LO BOT STK3 D_l_t TLN ATR0; lia_relc|]). apply Forall_nil.
Qed.
End Zd2.
#[using="HL CI_OK"] Theorem afree_nullP : ltac:(let t := eval cbv delta [afree_nullP__stmt] in afree_nullP__stmt in exact t).
Proof. exact afree_nullP__body. Qed.
End S.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Exec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_aalloc_s.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.F_aalloc1.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aunwind.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_adrain__A3W.F_afree_iseg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_afree_null.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.F_afree_arep.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac hide_disj_all := repeat match goal with H : (_ \/ _) |- _ => change (?P) with (sf_hide P) in H end.
Local Ltac hide_disj_but X :=
  repeat match goal with H : (_ \/ _) |- _ => tryif constr_eq H X then fail else change (?P) with (sf_hide P) in H end.
Local Ltac lia_rel := first [ solve [ hide_disj_all; lia ] | match goal with X : (_ \/ _) |- _ => solve [ hide_disj_but X; lia ] end ].
Local Ltac lia_relc := repeat split; first [ lia_rel | lia ].
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition q_set_ia (Q : qconc) : qconc := mkQConc (q_loc Q) (q_glob Q) true (q_pend Q).

(* [comment removed for export] *)
#[using="Type"] Lemma AQUAR_null : forall L st X Q m m' W,
  AQUAR_at L st X Q m -> munch W m m' -> wmono asegs m m' ->
  Forall (fun iv => (snd iv <= al_t L + 80 \/ al_t L + 208 <= fst iv)
                 /\ (snd iv <= AINSTANCE + 728 \/ AINSTANCE + 984 <= fst iv)
                 /\ (forall b, In b (x_busy X) -> match xb_st b with BLive _ => True | _ =>
                       snd iv <= xb_alloc L b \/ xb_alloc L b + size_of_class (xb_class b) <= fst iv end)) W ->
  aintal true m' ->
  AQUAR_at L st X (q_set_ia Q) m'.
Proof.
  intros L st X Q m m' W (GC & TC & GL & IA & CP & NUM) MU WM UT IA'.
  unfold AQUAR_at. cbn [q_loc q_glob q_ia q_pend q_set_ia].
  assert (DT : disjoint_from W (aq_tcache L) 32).
  { apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP.TwB.disjoint_from_Forall. eapply Forall_impl; [| exact UT]. intros iv (A & _). unfold aq_tcache. cbn in A |- *. lia. }
  assert (DG : disjoint_from W AQ_MAX 24 /\ disjoint_from W AQ_MUTEX 4 /\ disjoint_from W AQ_GCACHE 32).
  { unfold AQ_MAX, AQ_MUTEX, AQ_GCACHE, AINSTANCE in *.
    repeat split; apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP.TwB.disjoint_from_Forall; eapply Forall_impl; try exact UT; intros iv (_ & A & _); unfold AINSTANCE in A; cbn in A |- *; lia. }
  (nd_pre DG 3%nat; intros DG1 DG2 DG3; nd_post).
  assert (DQ : forall q, In q (q_loc Q ++ q_glob Q) -> disjoint_from W (abatch_addr L (qb_slot q)) Q_BATCH_BYTES).
  { intros q Hq. (nd_pre (qcoupled_bslot_busy L st X Q q CP Hq) 5%nat; intros b Hb Sb Cb Kb; nd_post).
    apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP.TwB.disjoint_from_Forall. eapply Forall_impl; [| exact UT]. intros iv (_ & _ & A).
    specialize (A b Hb). rewrite Sb in A. unfold xb_alloc in A. rewrite Cb, Kb, size_of_class_24 in A.
    unfold abatch_addr, Q_BATCH_BYTES. cbn. exact A. }
  split; [| split; [| split; [| split; [exact IA'| split; [| exact NUM]]]]].
  - eapply aquar_glob_const_frame; eassumption.
  - eapply aqcache_frame; [exact MU | exact WM | exact TC | exact DT |]. intros q Hq. apply DQ. apply in_app_iff. left. exact Hq.
  - eapply aqcache_frame; [exact MU | exact WM | exact GL | exact DG3 |]. intros q Hq. apply DQ. apply in_app_iff. right. exact Hq.
  - (* [comment removed for export] *)
    (nd_pre CP 8%nat; intros LN1 LN2 OK ND1 ND2 BS PS NN; nd_post).
    unfold qcoupled. cbn [q_loc q_glob q_pend]. cbv zeta.
    split; [exact LN1|]. split; [exact LN2|]. split; [exact OK|]. split; [exact ND1|]. split; [exact ND2|].
    split; [exact BS|]. split; [exact PS| exact NN].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition Wnull (SP t : Z) : list (Z * Z) :=
  [(SP - 4096, SP); (0xafc00, 0xafc00 + 0x81030); (0x13e488, 0x13e488 + 4); (t + 3168, t + 3169)]%Z.

Section S.
Variable DI : ADepotIface.
Variables (ASEC : alayout -> astate -> aconc -> amem -> Prop) (AFK : alayout -> list ablock -> amem -> Prop).
Hypothesis HL : ahole_laws (AHQ DI ASEC AFK).
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI
                                  /\ (snd iv <= 0xab670 \/ 0xab730 <= fst iv)
                                  /\ (snd iv <= 0xafc00 \/ 0x130c30 <= fst iv)
                                  /\ (snd iv <= 0x13e488 \/ 0x13e48c <= fst iv)) CI.

Definition AREP_null__stmt : Prop := forall L st X Q m m' SP,
  alayout_ok L -> AREP (AHQ DI ASEC AFK) L st X m -> AQUAR_at L st X Q m ->
  munch (Wnull SP (al_t L)) m m' -> wmono asegs m m' -> ATOP + 4096 <= SP ->
  rw_cells asegs m' (al_t L + 3168) [C1 (Z_to_bv 8 0)] -> aintal true m' ->
  AREP (AHQ DI ASEC AFK) L st X m' /\ AQUAR_at L st X (q_set_ia Q) m'.
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'AREP_null__stmt 0).
Variable st : ltac2:(SecDietF.SzSecF.ty 'AREP_null__stmt 1).
Variable X : ltac2:(SecDietF.SzSecF.ty 'AREP_null__stmt 2).
Variable Q : ltac2:(SecDietF.SzSecF.ty 'AREP_null__stmt 3).
Variable m : ltac2:(SecDietF.SzSecF.ty 'AREP_null__stmt 4).
Variable m' : ltac2:(SecDietF.SzSecF.ty 'AREP_null__stmt 5).
Variable SP : ltac2:(SecDietF.SzSecF.ty 'AREP_null__stmt 6).
Let W := Wnull SP (al_t L).
#[using="HL W"] Lemma AREP_null__body : ltac:(let T := type of (fun (h : AREP_null__stmt) => h L st X Q m m' SP) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (st, (X, (Q, (m, (m', SP))))))) as _.
  intros ALO AR AQ MU WM HSP UNW' IA'.
  chg (Wnull SP (al_t L)) W.
  (* [comment removed for export] *)
  (pose proof (alayout_space L ALO) as ndP__; nd_pre ndP__ 4%nat; intros SP1 SP2 SP3 SP4; nd_post).
  pose proof (ao_t L ALO) as OT. pose proof (ao_ctx L ALO) as OC. pose proof (ao_res L ALO) as ORS. pose proof (ao_nodes L ALO) as ON.
  pose proof (ao_store L ALO) as OS. pose proof (ao_fake L ALO) as OFK. pose proof (ao_dtls L ALO) as ODT.
  unfold aobj in OT, OC, ORS, ON, OS, OFK, ODT. pose proof (ao_space L ALO) as RSP.
  pose proof (ao_res_hi L ALO) as RHI. unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in OT, OC, ORS, ON, OS, OFK, ODT.   (* [comment removed for export] *)
  pose proof (ad_t_res L ALO) as D_t_res. pose proof (ad_t_ctx L ALO) as D_t_c. pose proof (ad_t_nodes L ALO) as D_t_n.
  pose proof (ad_t_store L ALO) as D_t_s. pose proof (ad_t_fake L ALO) as D_t_f. pose proof (ad_t_dtls L ALO) as D_t_d.
  unfold adisj in D_t_res, D_t_c, D_t_n, D_t_s, D_t_f, D_t_d.
  assert (SHRES : 2201439137792 <= shad (al_res L) /\ shad (al_res L) + shlen 137439023104 = shad (al_res L + 137439023104)
                  /\ shad (al_res L + 137439023104) <= 17594332446720).   (* [comment removed for export] *)
  { rewrite !shad_div, shlen_div. unfold ASHOFF in *. clear -ORS RHI. Z.div_mod_to_equations. lia. }
  (nd_pre SHRES 3%nat; intros SR1 SR2 SR3; nd_post).
  (* [comment removed for export] *)
  assert (Kimg : forall A k, 0x10000 <= A -> 0 <= k -> A + k <= AIMG_HI ->      (* [comment removed for export] *)
            (A + k <= 0xafc00 \/ 0x130c30 <= A) -> (A + k <= 0x13e488 \/ 0x13e48c <= A) -> disjoint_from W A k).
  { intros A k H1 H2 H3 H4 H5. unfold W, Wnull. cbn. unfold AIMG_HI in *. clear -H1 H2 H3 H4 H5 HSP OT. lia. }
  assert (Kobj : forall A k, AIMG_HI <= A -> 0 <= k -> A + k <= ATOP -> (A + k <= al_t L + 3168 \/ al_t L + 3169 <= A) -> disjoint_from W A k).
  { intros A k H1 H2 H3 H4. unfold W, Wnull. cbn. unfold AIMG_HI in *. clear -H1 H2 H3 H4 HSP. lia. }
  assert (Kres : forall A k, al_res L <= A -> 0 <= k -> A + k <= al_res L + 137439023104 -> disjoint_from W A k).
  { intros A k H1 H2 H3. apply Kobj; unfold AIMG_HI in *; [clear -H1 ORS; lia | exact H2 | clear -H3 ORS; lia | clear -H1 H3 D_t_res; lia]. }
  assert (Kres_sh : forall A k, shad (al_res L) <= A -> 0 <= k -> A + k <= shad (al_res L + 137439023104) -> disjoint_from W A k).
  { intros A k H1 H2 H3. apply Kobj; unfold AIMG_HI in *; [clear -H1 SR1; lia | exact H2 | clear -H3 SR3; lia | clear -H1 H3 SR1 SR3 OT; lia]. }
  assert (Kt : forall A k, al_t L <= A -> 0 <= k -> A + k <= al_t L + 3168 -> disjoint_from W A k).
  { intros A k H1 H2 H3. unfold W, Wnull. cbn. unfold AIMG_HI in *. clear -H1 H2 H3 HSP OT. lia. }   (* [comment removed for export] *)
  assert (Kctx : forall A k, al_ctx L <= A -> 0 <= k -> A + k <= al_ctx L + 65536 -> disjoint_from W A k).
  { intros A k H1 H2 H3. apply Kobj; unfold AIMG_HI in *; [clear -H1 OC; lia | exact H2 | clear -H3 OC; lia | clear -H1 H3 D_t_c; lia]. }
  assert (Ktls : forall A k, ATPv + -200 <= A -> 0 <= k -> A + k <= ATPv + 312 -> disjoint_from W A k).      (* [comment removed for export] *)
  { pose proof (ad_tls_t L ALO) as D_tls_t. unfold adisj in D_tls_t. pose proof atp_lin as TLN. pose proof atop_range as ATR0.
    intros A k H1 H2 H3. unfold W, Wnull. cbn. unfold AIMG_HI in *. clear -H1 H2 H3 HSP OT D_tls_t TLN ATR0. lia. }
  (* [comment removed for export] *)
  pose proof AR as AR0. (nd_pre AR0 12%nat; intros WF RT INST THR CLS HQ HS HD HRO RT2 AVL RT3; nd_post).
  pose proof WF as WF0. (nd_pre WF0 11%nat; intros SBE PAE SAL SLO SHI PERC OUTC BUSY LIVE FRESH UNIQ; nd_post).
  (* [comment removed for export] *)
  assert (BB : forall b, In b (x_busy X) -> al_res L <= xb_alloc L b /\ xb_alloc L b + size_of_class (xb_class b) <= al_res L + 137439023104).
  { intros b Hb. destruct (BUSY b Hb) as [CLB _].
    (nd_pre (PERC (xb_class b) CLB) 12%nat; intros Q1 Q2 _ _ _ _ _ _ _ _ _ QR; nd_post).
    pose proof (size_of_class_facts (xb_class b) CLB) as [QS _].
    assert (KB : 0 <= xb_slot b < ndist st (xb_class b)).
    { apply QR. apply in_app_iff. right. apply in_app_iff. right. unfold busy_slots. apply in_map_iff. exists b. split; [reflexivity|].
      apply filter_In. split; [exact Hb| apply Z.eqb_refl]. }
    (pose proof (slot_in_region L st (xb_class b) (xb_slot b) ltac:(clear -QS; lia) (proj1 Q1) KB) as ndP__; nd_pre ndP__ 3%nat; intros P5 P4 P0; nd_post).
    unfold xb_alloc, aregion, K_REGION, K_FREEARR_OFF, K_NUM_CLASSES in *. clear -P5 P4 Q1 Q2 CLB RSP. lia. }
  assert (AQ' : AQUAR_at L st X (q_set_ia Q) m').
  { eapply AQUAR_null; [exact AQ | exact MU | exact WM | | exact IA'].
    unfold W, Wnull. unfold AINSTANCE, AIMG_HI in *.
    repeat (apply Forall_cons; [cbn [fst snd]; split; [clear -OT HSP; lia|]; split; [clear -OT HSP; lia|];
                                intros b Hb; destruct (BB b Hb) as [B1 B2]; destruct (xb_st b); [exact I| |]; clear -B1 B2 ORS OT HSP D_t_res; lia |]).
    apply Forall_nil. }
  split; [| exact AQ'].
  split; [exact WF|].
  split. { eapply arep_rt_frame; [exact MU | exact WM | exact RT |]. unfold rt_hulls, ATP88, ATSD.
           repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply Ktls; clear; lia] |]). apply Forall_nil. }
  split. { eapply ainstance_frame; [exact MU | exact WM | exact INST | reflexivity | reflexivity | | |]; apply Kimg; clear; unfold AINSTANCE, AIMG_HI; lia. }
  split.
  { (nd_pre THR 6%nat; intros T0 T40 CACHES CSTATS [sj [STATS LSJ]] UNW; nd_post). unfold athread.
    split; [eapply cells_frame; [exact T0 | exact MU | exact WM | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; apply Kt; clear; lia]|].
    split; [eapply cells_frame; [exact T40 | exact MU | exact WM | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; apply Kt; clear; lia]|].
    split. { intros c Hc. eapply acache_cells_frame; [exact MU | exact WM | exact (CACHES c Hc) | reflexivity | reflexivity | reflexivity |].
             unfold acache_addr. unfold K_NUM_CLASSES in Hc. apply Kt; clear -Hc; lia. }
    split; [eapply junk_frame; [exact CSTATS | exact MU | exact WM | intros _; apply Kt; clear; lia]|].
    split; [exists sj; split; [eapply u64arr_frame; [exact STATS | exact MU | exact WM | replace (8 * Z.of_nat (length sj)) with 368 by (rewrite LSJ; reflexivity); apply Kt; clear; lia] | exact LSJ]|].
    exact UNW'. }
  split.
  { intros c Hc. (nd_pre (CLS c Hc) 4%nat; intros REG FARR SLOTS SHADOW; nd_post).
    (nd_pre (PERC c Hc) 12%nat; intros Q1 Q2 Q3 Q4 Q5 Q6 Q7 QLENF QLENC QCNTB QND QRANGE; nd_post).
    pose proof (size_of_class_facts c Hc) as [QS QS16]. pose proof (aregion_mod L c SAL) as RM. unfold K_NUM_CLASSES in Hc.
    assert (RI : al_res L <= aregion L c /\ aregion L c + K_REGION <= al_space_beg L + K_SPACE_SIZE
                 /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
    { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc RSP. lia. }
    (nd_pre RI 3%nat; intros RI1 RI2 RI3; nd_post). unfold K_REGION, K_SPACE_SIZE in RI2, RI3. change (2^37) with 137438953472 in RI2, RI3.
    split; [| split; [| split]].
    - eapply aregion_cells_frame; [exact MU | exact WM | exact REG | reflexivity | reflexivity | reflexivity | reflexivity |].
      apply Kres; unfold aregion_info, ARI_STRIDE, K_SPACE_SIZE; change (2^37) with 137438953472; clear -Hc RSP; lia.
    - eapply afreearray_frame; [exact MU | exact WM | exact FARR | reflexivity | reflexivity | reflexivity | exact QLENF | exact Q5 | | clear -Q6; lia |].
      + apply Kres; unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX in *; [clear -RI1; lia | clear -Q5 Q6; lia | clear -RI2 RI3 Q6; lia].
      + apply Kres_sh; [apply shad_mono; unfold afreearr, K_FREEARR_OFF; clear -RI1; lia | apply shlen_nonneg; clear -Q5 Q6; lia |].
        rewrite <- shad_add_shlen by (unfold afreearr, K_FREEARR_OFF; clear -RM; Z.div_mod_to_equations; lia). apply shad_mono.
        unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX in *. clear -RI2 RI3 Q6. lia.
    - eapply (aslots_update L W m m' MU WM st st X X c (-1)); [exact SLOTS | reflexivity | reflexivity | reflexivity | | | intros Hk; exfalso; clear -Hk; lia].
      + intros k Hk _. (pose proof (slot_in_region L st c k ltac:(clear -QS; lia) (proj1 Q1) Hk) as ndP__; nd_pre ndP__ 3%nat; intros P5 P4 P0; nd_post).
        split; [reflexivity|]. split.
        * apply Kres; [clear -P5 RI1; lia | clear -QS; lia | clear -P4 Q1 Q2 RI2 RI3; unfold K_FREEARR_OFF in *; lia].
        * intros b Hb. pose proof Hb as Hb'. unfold busy_of in Hb'. apply find_some in Hb'. destruct Hb' as [HIn HP].
          apply andb_true_iff in HP. destruct HP as [HP1 HP2]. apply Z.eqb_eq in HP1. apply Z.eqb_eq in HP2.
          split; [exact HP1|]. split; [exact HP2|]. exact (awf_fits L st X b WF HIn).
      + intros POS. apply Kres; [clear -Q1 RI1; lia | clear -POS; lia | clear -Q1 Q2 RI2 RI3; unfold K_FREEARR_OFF in *; lia].
    - eapply (aslot_shadow_update L W m m' MU WM st st X X c (-1)); [exact SHADOW | reflexivity | reflexivity | reflexivity | | | intros Hk; exfalso; clear -Hk; lia | apply shlen_nonneg; clear -QS; lia].
      + intros k Hk _. (pose proof (slot_in_region L st c k ltac:(clear -QS; lia) (proj1 Q1) Hk) as ndP__; nd_pre ndP__ 3%nat; intros P5 P4 P0; nd_post).
        pose proof (slot_aligned L c k SAL ltac:(unfold K_NUM_CLASSES; clear -Hc; lia)) as AL.
        split; [reflexivity|]. apply Kres_sh; [apply shad_mono; clear -P5 RI1; lia | apply shlen_nonneg; clear -QS; lia |].
        rewrite <- shad_add_shlen by (clear -AL; Z.div_mod_to_equations; lia). apply shad_mono. clear -P4 Q1 Q2 RI2 RI3. unfold K_FREEARR_OFF in *. lia.
      + intros POS. apply Kres_sh; [apply shad_mono; clear -Q1 RI1; lia | clear -POS; lia |].
        rewrite <- shad_add_shlen by (pose proof (mod16_of_class _ _ Q3 QS16 ltac:(clear -QS; lia)) as AM; clear -AM RM; Z.div_mod_to_equations; lia).
        apply shad_mono. clear -Q1 Q2 RI2 RI3. unfold K_FREEARR_OFF in *. lia. }
  split; [exists (q_set_ia Q); exact AQ'|].
  split.
  { cbn [ah_sec AHQ]. cbn [ah_sec AHQ] in HS.
    eapply (hs_frame _ HL L st st X X m m' W); [exact HS | exact MU | exact WM | |].
    - unfold sec_untouched, aknown, W, Wnull. unfold AINSTANCE, AIMG_HI in *.
      (* [comment removed for export] *)
      apply Forall_cons; [cbn [fst snd]; intros a Ha; do 4 right; left; clear -Ha HSP; lia|].
      do 2 (apply Forall_cons; [cbn [fst snd]; intros a Ha; left; clear -Ha; lia|]).
      apply Forall_cons; [cbn [fst snd]; intros a Ha; do 5 right; left; clear -Ha OT; lia|].
      apply Forall_nil.
    - apply sec_same_refl. }
  split.
  { cbn [ah_depot AHQ]. cbn [ah_depot AHQ] in HD.
    eapply (hd_frame _ HL L m m' W); [exact HD | exact MU | exact WM |].
    unfold W, Wnull. unfold AIMG_HI in *.
    repeat (apply Forall_cons; [cbn [fst snd]; intros a Ha; clear -Ha OT ON OS HSP D_t_n D_t_s; lia|]). apply Forall_nil. }
  split; [eapply arelro_frame; [exact MU | exact HRO | apply Kimg; clear; unfold ARELRO_LO, ARELRO_HI, AIMG_HI; lia]|].
  split; [eapply arep_rt2_frame; [exact MU | exact WM | exact RT2 | | |]; apply Kimg; clear; unfold AIMG_HI; lia|].
  split; [| eapply arep_rt3_frame; [exact MU | exact WM | exact RT3 |]; unfold rt3_hulls; repeat (apply Forall_cons; [cbn [fst snd]; apply Kimg; clear; unfold AIMG_HI; lia|]); apply Forall_nil].
  intros c Hc. (nd_pre (PERC c Hc) 8%nat; intros Q1 Q2 Q3 Q4 Q5 Q6 Q7 _; nd_post). unfold K_NUM_CLASSES in Hc.
  assert (RI : al_res L <= aregion L c /\ aregion L c + K_REGION <= al_space_beg L + K_SPACE_SIZE
               /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
  { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc RSP. lia. }
  (nd_pre RI 3%nat; intros RI1 RI2 RI3; nd_post). unfold K_REGION, K_SPACE_SIZE in RI2, RI3. change (2^37) with 137438953472 in RI2, RI3.
  eapply (ashadow_avail_frame L W m m' MU WM st); [exact (AVL c ltac:(unfold K_NUM_CLASSES; clear -Hc; lia)) | reflexivity | reflexivity | |].
  - intros POS. apply Kres_sh; [apply shad_mono; unfold aregion in *; clear -Q1 RI1; lia | clear -POS; lia |].
    rewrite <- shad_add_shlen by (pose proof (aregion_mod L c SAL) as RM; clear -RM Q4; unfold K_USER_MAP in *; Z.div_mod_to_equations; lia).
    apply shad_mono. unfold K_FREEARR_OFF, K_REGION in *. clear -Q1 Q2 RI2 RI3. lia.
  - intros POS. apply Kres_sh; [apply shad_mono; unfold afreearr, K_FREEARR_OFF, aregion in *; clear -Q5 Q6 RI1; lia | clear -POS; lia |].
    rewrite <- shad_add_shlen by (pose proof (aregion_mod L c SAL) as RM; unfold afreearr, K_FREEARR_OFF; clear -RM Q7; unfold K_FREEARR_MAP in *; Z.div_mod_to_equations; lia).
    apply shad_mono. unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q5 Q6 RI2 RI3. lia.
Qed.
End Zd1.
#[using="HL"] Lemma AREP_null : ltac:(let t := eval cbv delta [AREP_null__stmt] in AREP_null__stmt in exact t).
Proof. exact AREP_null__body. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition afree_nullP__stmt : Prop := afree_null_stmt CI (AHEAP_P (AHQ DI ASEC AFK)).
Section Zd2.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'afree_nullP__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'afree_nullP__stmt 1).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'afree_nullP__stmt 2).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'afree_nullP__stmt 3).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'afree_nullP__stmt 4).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'afree_nullP__stmt 5).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'afree_nullP__stmt 6).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'afree_nullP__stmt 7).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'afree_nullP__stmt 8).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'afree_nullP__stmt 9).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'afree_nullP__stmt 10).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'afree_nullP__stmt 11).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'afree_nullP__stmt 12).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'afree_nullP__stmt 13).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'afree_nullP__stmt 14).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'afree_nullP__stmt 15).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'afree_nullP__stmt 16).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'afree_nullP__stmt 17).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'afree_nullP__stmt 18).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'afree_nullP__stmt 19).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'afree_nullP__stmt 20).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'afree_nullP__stmt 21).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'afree_nullP__stmt 22).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'afree_nullP__stmt 23).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'afree_nullP__stmt 24).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'afree_nullP__stmt 25).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'afree_nullP__stmt 26).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'afree_nullP__stmt 27).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'afree_nullP__stmt 28).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'afree_nullP__stmt 29).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'afree_nullP__stmt 30).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'afree_nullP__stmt 31).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'afree_nullP__stmt 32).
Variable F : ltac2:(SecDietF.SzSecF.ty 'afree_nullP__stmt 33).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'afree_nullP__stmt 34).
Variable m : ltac2:(SecDietF.SzSecF.ty 'afree_nullP__stmt 35).
Variable st : ltac2:(SecDietF.SzSecF.ty 'afree_nullP__stmt 36).
Variable LB : ltac2:(SecDietF.SzSecF.ty 'afree_nullP__stmt 37).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'afree_nullP__stmt 38).
Variable tr : ltac2:(SecDietF.SzSecF.ty 'afree_nullP__stmt 39).
#[using="HL CI_OK"] Lemma afree_nullP__body : ltac:(let T := type of (fun (h : afree_nullP__stmt) => h L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st LB lo tr) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (st, (LB, (lo, tr)))))))))))))))))))))))))))))))))))))))) as _.
  unfold afree_null_stmt.  intros AH MI ST BOT LO TP Ha0 AUNW S0NE RA4 RANE SP16 RSTK.
  assert (UNWX : exists trt, afree_unw RNG lo m (al_top L) sp s0 ra trt /\ In (AFREE_PC :: trt) (al_U L)).
  { destruct AUNW as [(BT & UC & LTR & TRU & RTOP)|(TOPLE & SPLT & TRU)]; [exists (bv_unsigned ra :: tr); split; [left; exists tr; split; [reflexivity|]; split; [exact UC|]; split; [exact LTR|]; split; [exact BT| exact RTOP]| exact TRU] | exists (@nil Z); split; [right; auto| exact TRU]]. }
  (nd_pre UNWX 3%nat; intros trt FUNW TRU; nd_post).
  (nd_pre AH 4%nat; intros ALO ARNG [X [AR BL]] HFK; nd_post).
  pose proof AR as AR0. (nd_pre AR0 12%nat; intros WF RT INST THR CLS HQ HS HD HRO HRT2 AVL RT3; nd_post).
  cbn [ah_quar ah_sec ah_depot ah_fake AHQ] in HQ, HS, HD, HFK. destruct HQ as [Q AQ].
  pose proof WF as WF0. (nd_pre WF0 11%nat; intros SBE PAE SAL SLO SHI PERC OUTC BUSY LIVEB FRESH UNIQ; nd_post).
  (* [comment removed for export] *)
  pose proof ARNG as ARNG0. (nd_pre ARNG0 14%nat; intros RIMG RT4 RCTX RNO RSTO RRI RFK RSFK RDT RCLS RPA RSECS RPSH RTLS; nd_post).
  (pose proof (alayout_t L ALO) as ndP__; nd_pre ndP__ 4%nat; intros TL1 TL2 TL3 TL4; nd_post). pose proof TL1 as TL1u. pose proof TL4 as TL4u. unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in TL1u, TL4u.   (* [comment removed for export] *)
  (pose proof (alayout_ctx L ALO) as ndP__; nd_pre ndP__ 5%nat; intros CL1 CL2 CL3 CL4 CL5; nd_post).
  (pose proof (alayout_stack L ALO) as ndP__; nd_pre ndP__ 3%nat; intros STK1 STK2 STK3; nd_post).
  assert (SP47 : bv_unsigned sp < 2^47) by (eapply afree_unw_sp47; [exact FUNW| exact STK2]).
  pose proof (ao_t L ALO) as OT. pose proof (ao_res L ALO) as ORS. pose proof (ao_fake L ALO) as OFK. pose proof (ao_dtls L ALO) as ODT.
  unfold aobj in OT, ORS, OFK, ODT. pose proof (ao_space L ALO) as RSP. pose proof (ao_res_hi L ALO) as RHI. unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in OT, ORS, OFK, ODT.   (* [comment removed for export] *)
  pose proof (ad_t_res L ALO) as D_t_res. pose proof (ad_t_fake L ALO) as D_t_f. pose proof (ad_t_dtls L ALO) as D_t_d.
  unfold adisj in D_t_res, D_t_f, D_t_d.
  (* [comment removed for export] *)
  pose proof RT as RT0.
  (nd_pre RT0 28%nat; intros GPG GOT GOT80 RIC LS1 REAL IMAX4 FLG5 FLG HPP SHB CANP TI TK INI2 LAY MCS OOM3 PGC HK2 CF8 CF34 CSMT T88 TSD LS2 CT8 CT; nd_post).
  pose proof INI2 as INI. rw_split INI 1%nat INI1 INIx. clear INIx.
  pose proof OOM3 as OOM. rw_split OOM 2%nat OOMx RSS0. clear OOMx.
  pose proof IMAX4 as IMAX. rw_split IMAX 3%nat IMAX3 IMAXx. clear IMAXx.
  (nd_pre THR 6%nat; intros T0 T40 CACHES CSTATS [sj [STATS LSJ]] UNW; nd_post).
  pose proof AQ as AQ0. (nd_pre AQ0 6%nat; intros _ _ _ (FL & IAS & IAM) CP _; nd_post).
  unfold AIA_FLAG, AIA_BASE, AIA_SIZE, AIA_MAP1, AIA_MAP1_LEN in FL, IAS, IAM.
  (* [comment removed for export] *)
  unfold AIMG_HI, AFREE_STACK, UDEPTH in *.
  box CL5.
  eapply evtF_mono.
  { eapply (free_null_spec (q_ia Q) RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m
              (al_t L) (al_ctx L) lo (al_top L) (al_bot L) trt).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => first [exact ST | exact IAS]
         | |- mem_inv _ _ => exact MI
         | |- allocA_cells _ _ _ => unfold allocA_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
         | |- afree_unw _ _ _ _ _ _ => exact FUNW
         | |- _ = true -> _ => exact IAM
         end.
    all: try lazymatch goal with
         | |- rw_cells _ _ _ [C8 _; C8 _; C8 _] => exact T0
         | |- rw_cells _ _ _ _ => assumption
         | |- @eq word _ _ => first [exact TP | exact Ha0 | reflexivity]
         | |- _ \/ _ => first [unboxed CL5 | pose proof CL5 as Y; unbox Y; lia]
         | |- rng _ _ _ => first [assumption | eapply rng_sub; [exact RCTX| lia| lia] | solve_rng]
         end.
    all: try assumption.
    all: unfold AIMG_HI, UDEPTH in *.
    all: try (generalize LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 RA4; clear; intros; lia).
    all: match goal with |- ?G => idtac "REMF" G end. }
  cbv beta. intros ms' PM.
  (nd_pre PM 17%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 8%nat; intros MU WM MI' ST' UNW' FL' IAS' IAM'; nd_post).
  change (munch (Wnull (bv_unsigned sp) (al_t L)) m m') in MU.
  assert (IA' : aintal true m').
  { unfold aintal, AIA_FLAG, AIA_BASE, AIA_SIZE, AIA_MAP1, AIA_MAP1_LEN. split; [exact FL'|]. split; [exact IAS'|]. intros _. exact IAM'. }
  destruct (AREP_null L st X Q m m' (bv_unsigned sp) ALO AR AQ MU WM ltac:(atop_facts; clear -LO BOT STK3; lia) UNW' IA') as [AR' AQ'].
  (* [comment removed for export] *)
  exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
  split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split.
  { (* [comment removed for export] *)
    intros a Ha CLA. split; [| intros Hw; apply WM; exact Hw]. apply MU. rewrite wa_unsigned by exact Ha.
    word_range sp SPR.
    unfold Wnull. cbn [outside].
    destruct CLA as [CLA|TL].
    2:{ (* [comment removed for export] *)
        pose proof (ad_tls_t L ALO) as DLT. unfold adisj in DLT. pose proof atp_lin as TLN. pose proof atop_range as ATR0. pose proof atp_below_atop as TBA.
        destruct TL as [[T|(ta & Hta & ->)]|[IM|IM]].
        4:{ pose proof (ao_ahm L ALO) as OAH. pose proof (aobj_img _ _ OAH ltac:(clear; lia)) as OAHI. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OAH, OAHI.
          rewrite <- (ao_ahm_eq L ALO) in IM. unfold AAHM_SZ in IM. pose proof (ad_ahm_t L ALO) as DA1. unfold adisj in DA1.
            clear -IM OAH OAHI DA1 Ha LO BOT STK3 ATR0. lia. }
        - clear -T Ha DLT TLN ATR0 TBA LO BOT STK3. lia.
        - pose proof (tls_shadow_band ta Hta) as (TS1 & TS2).
          assert (SA : shad ATOP <= 17594332446720) by (rewrite shad_div; unfold ASHOFF; clear -ATR0; Z.div_mod_to_equations; lia).
          clear -TS1 TS2 SA Ha TL1u LO BOT STK3 ATR0. lia.
        - unfold AIMSH_LO, AIMSH_LEN in IM. clear -IM Ha TL1u LO BOT STK3 ATR0. lia. }
    destruct CLA as [SK | [CIa | [BLK | SH]]].
    - clear -SK Ha LO BOT STK3 TL2. lia.
    - (nd_pre CIa 3%nat; intros iv Hiv R; nd_post). (pose proof (proj1 (Forall_forall _ _) CI_OK iv Hiv) as ndP__; nd_pre ndP__ 6%nat; intros Q1 Q2 Q3 Q4 Q5 Q6; nd_post). cbn [fst snd] in *.
      unfold AIMG_HI in *. clear -R Q1 Q3 Q5 Q6 LO BOT STK3 TL4u. lia.
    - (nd_pre BLK 3%nat; intros [[q|cls] A' n'] Hin R; nd_post); cbn [ab_addr ab_size] in R.
      + destruct (proj1 BL q A' n' Hin) as [(b & Hb & Sb & Ub & Nb)|(mb & msz & Lp & EUA & Gs)].
        * destruct (BUSY b Hb) as [CLB _].
          (nd_pre (PERC (xb_class b) CLB) 12%nat; intros P1 P2 _ _ _ _ _ _ _ _ _ PR; nd_post).
          pose proof (size_of_class_facts (xb_class b) CLB) as [QS _].
          assert (KB : 0 <= xb_slot b < ndist st (xb_class b)).
          { apply PR. apply in_app_iff. right. apply in_app_iff. right. unfold busy_slots. apply in_map_iff. exists b. split; [reflexivity|].
            apply filter_In. split; [exact Hb| apply Z.eqb_refl]. }
          (pose proof (slot_in_region L st (xb_class b) (xb_slot b) ltac:(clear -QS; lia) (proj1 P1) KB) as ndP__; nd_pre ndP__ 3%nat; intros P5 P4 P0; nd_post).
          pose proof (awf_fits L st X b WF Hb) as FIT. unfold xb_fits in FIT. rewrite Sb in FIT.
          subst A' n'. unfold xb_user, xb_alloc, aregion, K_REGION, K_FREEARR_OFF, K_NUM_CLASSES in *.
          clear -R P5 P4 P1 P2 CLB RSP FIT ORS D_t_res LO BOT STK3. lia.
        * (* [comment removed for export] *)
          cbn [sec_wf1] in Gs. (nd_pre Gs 7%nat; intros Gs1 Gs2 Gs3 Gs4 Gs5 Gs6 (Ct & Cc & Cr & Cp & Cn & Cs & Cf & Cd); nd_post).
          pose proof (sec_facts n' ltac:(clear -Gs5; lia) Gs6) as SF. subst A'. unfold SEC_UOFF, K_HIGH_MEM in *.
          unfold ablk, KLS, AIMG_HI in Gs2.   (* [comment removed for export] *)
          clear -R Gs2 Gs3 Gs4 Gs5 SF Ct LO BOT STK3. lia.
      + (nd_pre (proj1 (proj2 BL) cls A' n' Hin) 3%nat; intros K1 K2 K3; nd_post).
        clear -R K1 K2 K3 OFK D_t_f LO BOT STK3. lia.
    - (nd_pre SH 3%nat; intros a' Ha' ndR1__; nd_post; revert ndR1__; intros ->). rewrite shad_div in Ha |- *. unfold ASHOFF in *.
      assert (A47 : 0 <= a' < 2^47).
      { destruct Ha' as [SK | [CIa | FK]].
        - atop_facts. clear -SK SPR. lia.
        - (nd_pre CIa 3%nat; intros iv Hiv R; nd_post). (pose proof (proj1 (Forall_forall _ _) CI_OK iv Hiv) as ndP__; nd_pre ndP__ 4%nat; intros Q1 Q2 Q3 _; nd_post). cbn [fst snd] in *.
          unfold AIMG_HI in *. clear -R Q1 Q3. lia.
        - (nd_pre FK 5%nat; intros cls FA sz Hin R; nd_post). (nd_pre (proj1 (proj2 BL) cls FA sz Hin) 3%nat; intros K1 K2 K3; nd_post). clear -R K1 K3 OFK. lia. }
      clear -A47 LO BOT STK3 TL1u. Z.div_mod_to_equations. lia. }
  split; [exact ALO|]. split; [exact ARNG|]. split; [exists X; split; [exact AR'| exact BL]|].
  (* [comment removed for export] *)
  cbn [ah_fake AHQ].
  assert (SF : 2148239360 <= shad (al_fake L) /\ shad (al_fake L) + shlen 11571200 <= 17594332446720).   (* [comment removed for export] *)
  { rewrite shad_div, shlen_div. unfold ASHOFF in *. pose proof atop_range as AR8. clear -OFK AR8. Z.div_mod_to_equations. lia. }
  eapply (hf_frame _ HL L LB m m'); [exact HFK | exact MU | exact WM |].
  unfold fake_untouched, Wnull.
  pose proof (ad_tls_t L ALO) as D_l_t. unfold adisj in D_l_t. pose proof atp_lin as TLN. pose proof atop_range as ATR0.      (* [comment removed for export] *)
  repeat (apply Forall_cons; [cbn [fst snd]; clear -OFK ODT OT SF D_t_f D_t_d LO BOT STK3 D_l_t TLN ATR0; lia_relc|]). apply Forall_nil.
Qed.
End Zd2.
#[using="HL CI_OK"] Theorem afree_nullP : ltac:(let t := eval cbv delta [afree_nullP__stmt] in afree_nullP__stmt in exact t).
Proof. exact afree_nullP__body. Qed.
End S.
End CANSEC1.
End TwB.
End AFreeNull.

(* [comment removed for export] *)
Module ARealloc_preP.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecFacts AImg AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AQConst. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AMalloc_iface. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitR__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARealloc_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecSlog__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aunwind. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_adrain__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_front__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_arep__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc3g0__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_aalloc_s OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.F_aalloc1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aunwind OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_adrain__A3W.F_afree_iseg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_afree_null OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.F_afree_arep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfn_arep__A3W.AFreeNull OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepExt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3g0__A3W.F_arealloc_iseg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3g0__A3W.F_arealloc_pre.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac hide_disj_all := repeat match goal with H : (_ \/ _) |- _ => change (?P) with (sf_hide P) in H end.
Local Ltac hide_disj_but X :=
  repeat match goal with H : (_ \/ _) |- _ => tryif constr_eq H X then fail else change (?P) with (sf_hide P) in H end.
Local Ltac lia_rel := first [ solve [ hide_disj_all; lia ] | match goal with X : (_ \/ _) |- _ => solve [ hide_disj_but X; lia ] end ].
Local Ltac lia_relc := repeat split; first [ lia_rel | lia ].
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition Wrpre (SP t : Z) : list (Z * Z) :=
  [(SP - 4096, SP); (0xaf800, 0xaf800 + 0x81030); (0x13e088, 0x13e088 + 4); (t + 3168, t + 3169); (t + 2800, t + 2800 + 368)]%Z.

Section S.
Variable DI : ADepotIface.
Variables (ASEC : alayout -> astate -> aconc -> amem -> Prop) (AFK : alayout -> list ablock -> amem -> Prop).
Hypothesis HL : ahole_laws (AHQ DI ASEC AFK).
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI
                                  /\ (snd iv <= 0xab270 \/ 0xab330 <= fst iv)
                                  /\ (snd iv <= 0xaf800 \/ 0x130830 <= fst iv)
                                  /\ (snd iv <= 0x13e088 \/ 0x13e08c <= fst iv)) CI.

Definition AREP_rpre__stmt : Prop := forall L st X Q m m' SP,
  alayout_ok L -> AREP (AHQ DI ASEC AFK) L st X m -> AQUAR_at L st X Q m ->
  munch (Wrpre SP (al_t L)) m m' -> wmono asegs m m' -> ATOP + 4096 <= SP ->
  rw_cells asegs m' (al_t L + 3168) [C1 (Z_to_bv 8 0)] -> aintal true m' ->
  (exists sj', u64arr asegs m' (al_t L + 2800) sj' /\ length sj' = 46%nat) ->
  AREP (AHQ DI ASEC AFK) L st X m' /\ AQUAR_at L st X (q_set_ia Q) m'.
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'AREP_rpre__stmt 0).
Variable st : ltac2:(SecDietF.SzSecF.ty 'AREP_rpre__stmt 1).
Variable X : ltac2:(SecDietF.SzSecF.ty 'AREP_rpre__stmt 2).
Variable Q : ltac2:(SecDietF.SzSecF.ty 'AREP_rpre__stmt 3).
Variable m : ltac2:(SecDietF.SzSecF.ty 'AREP_rpre__stmt 4).
Variable m' : ltac2:(SecDietF.SzSecF.ty 'AREP_rpre__stmt 5).
Variable SP : ltac2:(SecDietF.SzSecF.ty 'AREP_rpre__stmt 6).
Let W := Wrpre SP (al_t L).
#[using="HL W"] Lemma AREP_rpre__body : ltac:(let T := type of (fun (h : AREP_rpre__stmt) => h L st X Q m m' SP) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (st, (X, (Q, (m, (m', SP))))))) as _.
  intros ALO AR AQ MU WM HSP UNW' IA' STATS'.
  chg (Wrpre SP (al_t L)) W.
  (* [comment removed for export] *)
  (pose proof (alayout_space L ALO) as ndP__; nd_pre ndP__ 4%nat; intros SP1 SP2 SP3 SP4; nd_post).
  pose proof (ao_t L ALO) as OT. pose proof (ao_ctx L ALO) as OC. pose proof (ao_res L ALO) as ORS. pose proof (ao_nodes L ALO) as ON.
  pose proof (ao_store L ALO) as OS. pose proof (ao_fake L ALO) as OFK. pose proof (ao_dtls L ALO) as ODT.
  unfold aobj in OT, OC, ORS, ON, OS, OFK, ODT. pose proof (ao_space L ALO) as RSP.
  pose proof (ao_res_hi L ALO) as RHI. unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in OT, OC, ORS, ON, OS, OFK, ODT.   (* [comment removed for export] *)
  pose proof (ad_t_res L ALO) as D_t_res. pose proof (ad_t_ctx L ALO) as D_t_c. pose proof (ad_t_nodes L ALO) as D_t_n.
  pose proof (ad_t_store L ALO) as D_t_s. pose proof (ad_t_fake L ALO) as D_t_f. pose proof (ad_t_dtls L ALO) as D_t_d.
  unfold adisj in D_t_res, D_t_c, D_t_n, D_t_s, D_t_f, D_t_d.
  assert (SHRES : 2201439137792 <= shad (al_res L) /\ shad (al_res L) + shlen 137439023104 = shad (al_res L + 137439023104)
                  /\ shad (al_res L + 137439023104) <= 17594332446720).   (* [comment removed for export] *)
  { rewrite !shad_div, shlen_div. unfold ASHOFF in *. clear -ORS RHI. Z.div_mod_to_equations. lia. }
  (nd_pre SHRES 3%nat; intros SR1 SR2 SR3; nd_post).
  (* [comment removed for export] *)
  assert (Kimg : forall A k, 0x10000 <= A -> 0 <= k -> A + k <= AIMG_HI ->      (* [comment removed for export] *)
            (A + k <= 0xaf800 \/ 0x130830 <= A) -> (A + k <= 0x13e088 \/ 0x13e08c <= A) -> disjoint_from W A k).
  { intros A k H1 H2 H3 H4 H5. unfold W, Wrpre. cbn. unfold AIMG_HI in *. clear -H1 H2 H3 H4 H5 HSP OT. lia. }
  assert (Kobj : forall A k, AIMG_HI <= A -> 0 <= k -> A + k <= ATOP -> (A + k <= al_t L + 2800 \/ al_t L + 3169 <= A) -> disjoint_from W A k).
  { intros A k H1 H2 H3 H4. unfold W, Wrpre. cbn. unfold AIMG_HI in *. clear -H1 H2 H3 H4 HSP. lia. }
  assert (Kres : forall A k, al_res L <= A -> 0 <= k -> A + k <= al_res L + 137439023104 -> disjoint_from W A k).
  { intros A k H1 H2 H3. apply Kobj; unfold AIMG_HI in *; [clear -H1 ORS; lia | exact H2 | clear -H3 ORS; lia | clear -H1 H3 D_t_res; lia]. }
  assert (Kres_sh : forall A k, shad (al_res L) <= A -> 0 <= k -> A + k <= shad (al_res L + 137439023104) -> disjoint_from W A k).
  { intros A k H1 H2 H3. apply Kobj; unfold AIMG_HI in *; [clear -H1 SR1; lia | exact H2 | clear -H3 SR3; lia | clear -H1 H3 SR1 SR3 OT; lia]. }
  assert (Kt : forall A k, al_t L <= A -> 0 <= k -> A + k <= al_t L + 2800 -> disjoint_from W A k).
  { intros A k H1 H2 H3. unfold W, Wrpre. cbn. unfold AIMG_HI in *. clear -H1 H2 H3 HSP OT. lia. }   (* [comment removed for export] *)
  assert (Kctx : forall A k, al_ctx L <= A -> 0 <= k -> A + k <= al_ctx L + 65536 -> disjoint_from W A k).
  { intros A k H1 H2 H3. apply Kobj; unfold AIMG_HI in *; [clear -H1 OC; lia | exact H2 | clear -H3 OC; lia | clear -H1 H3 D_t_c; lia]. }
  assert (Ktls : forall A k, ATPv + -200 <= A -> 0 <= k -> A + k <= ATPv + 312 -> disjoint_from W A k).      (* [comment removed for export] *)
  { pose proof (ad_tls_t L ALO) as D_tls_t. unfold adisj in D_tls_t. pose proof atp_lin as TLN. pose proof atop_range as ATR0.
    intros A k H1 H2 H3. unfold W, Wrpre. cbn. unfold AIMG_HI in *. clear -H1 H2 H3 HSP OT D_tls_t TLN ATR0. lia. }
  (* [comment removed for export] *)
  pose proof AR as AR0. (nd_pre AR0 12%nat; intros WF RT INST THR CLS HQ HS HD HRO RT2 AVL RT3; nd_post).
  pose proof WF as WF0. (nd_pre WF0 11%nat; intros SBE PAE SAL SLO SHI PERC OUTC BUSY LIVE FRESH UNIQ; nd_post).
  (* [comment removed for export] *)
  assert (BB : forall b, In b (x_busy X) -> al_res L <= xb_alloc L b /\ xb_alloc L b + size_of_class (xb_class b) <= al_res L + 137439023104).
  { intros b Hb. destruct (BUSY b Hb) as [CLB _].
    (nd_pre (PERC (xb_class b) CLB) 12%nat; intros Q1 Q2 _ _ _ _ _ _ _ _ _ QR; nd_post).
    pose proof (size_of_class_facts (xb_class b) CLB) as [QS _].
    assert (KB : 0 <= xb_slot b < ndist st (xb_class b)).
    { apply QR. apply in_app_iff. right. apply in_app_iff. right. unfold busy_slots. apply in_map_iff. exists b. split; [reflexivity|].
      apply filter_In. split; [exact Hb| apply Z.eqb_refl]. }
    (pose proof (slot_in_region L st (xb_class b) (xb_slot b) ltac:(clear -QS; lia) (proj1 Q1) KB) as ndP__; nd_pre ndP__ 3%nat; intros P5 P4 P0; nd_post).
    unfold xb_alloc, aregion, K_REGION, K_FREEARR_OFF, K_NUM_CLASSES in *. clear -P5 P4 Q1 Q2 CLB RSP. lia. }
  assert (AQ' : AQUAR_at L st X (q_set_ia Q) m').
  { eapply AQUAR_null; [exact AQ | exact MU | exact WM | | exact IA'].
    unfold W, Wrpre. unfold AINSTANCE, AIMG_HI in *.
    repeat (apply Forall_cons; [cbn [fst snd]; split; [clear -OT HSP; lia|]; split; [clear -OT HSP; lia|];
                                intros b Hb; destruct (BB b Hb) as [B1 B2]; destruct (xb_st b); [exact I| |]; clear -B1 B2 ORS OT HSP D_t_res; lia |]).
    apply Forall_nil. }
  split; [| exact AQ'].
  split; [exact WF|].
  split. { eapply arep_rt_frame; [exact MU | exact WM | exact RT |]. unfold rt_hulls, ATP88, ATSD.
           repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply Ktls; clear; lia] |]). apply Forall_nil. }
  split. { eapply ainstance_frame; [exact MU | exact WM | exact INST | reflexivity | reflexivity | | |]; apply Kimg; clear; unfold AINSTANCE, AIMG_HI; lia. }
  split.
  { (nd_pre THR 6%nat; intros T0 T40 CACHES CSTATS [sj [STATS LSJ]] UNW; nd_post). unfold athread.
    split; [eapply cells_frame; [exact T0 | exact MU | exact WM | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; apply Kt; clear; lia]|].
    split; [eapply cells_frame; [exact T40 | exact MU | exact WM | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; apply Kt; clear; lia]|].
    split. { intros c Hc. eapply acache_cells_frame; [exact MU | exact WM | exact (CACHES c Hc) | reflexivity | reflexivity | reflexivity |].
             unfold acache_addr. unfold K_NUM_CLASSES in Hc. apply Kt; clear -Hc; lia. }
    split; [eapply junk_frame; [exact CSTATS | exact MU | exact WM | intros _; apply Kt; clear; lia]|].
    split; [exact STATS'|].
    exact UNW'. }
  split.
  { intros c Hc. (nd_pre (CLS c Hc) 4%nat; intros REG FARR SLOTS SHADOW; nd_post).
    (nd_pre (PERC c Hc) 12%nat; intros Q1 Q2 Q3 Q4 Q5 Q6 Q7 QLENF QLENC QCNTB QND QRANGE; nd_post).
    pose proof (size_of_class_facts c Hc) as [QS QS16]. pose proof (aregion_mod L c SAL) as RM. unfold K_NUM_CLASSES in Hc.
    assert (RI : al_res L <= aregion L c /\ aregion L c + K_REGION <= al_space_beg L + K_SPACE_SIZE
                 /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
    { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc RSP. lia. }
    (nd_pre RI 3%nat; intros RI1 RI2 RI3; nd_post). unfold K_REGION, K_SPACE_SIZE in RI2, RI3. change (2^37) with 137438953472 in RI2, RI3.
    split; [| split; [| split]].
    - eapply aregion_cells_frame; [exact MU | exact WM | exact REG | reflexivity | reflexivity | reflexivity | reflexivity |].
      apply Kres; unfold aregion_info, ARI_STRIDE, K_SPACE_SIZE; change (2^37) with 137438953472; clear -Hc RSP; lia.
    - eapply afreearray_frame; [exact MU | exact WM | exact FARR | reflexivity | reflexivity | reflexivity | exact QLENF | exact Q5 | | clear -Q6; lia |].
      + apply Kres; unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX in *; [clear -RI1; lia | clear -Q5 Q6; lia | clear -RI2 RI3 Q6; lia].
      + apply Kres_sh; [apply shad_mono; unfold afreearr, K_FREEARR_OFF; clear -RI1; lia | apply shlen_nonneg; clear -Q5 Q6; lia |].
        rewrite <- shad_add_shlen by (unfold afreearr, K_FREEARR_OFF; clear -RM; Z.div_mod_to_equations; lia). apply shad_mono.
        unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX in *. clear -RI2 RI3 Q6. lia.
    - eapply (aslots_update L W m m' MU WM st st X X c (-1)); [exact SLOTS | reflexivity | reflexivity | reflexivity | | | intros Hk; exfalso; clear -Hk; lia].
      + intros k Hk _. (pose proof (slot_in_region L st c k ltac:(clear -QS; lia) (proj1 Q1) Hk) as ndP__; nd_pre ndP__ 3%nat; intros P5 P4 P0; nd_post).
        split; [reflexivity|]. split.
        * apply Kres; [clear -P5 RI1; lia | clear -QS; lia | clear -P4 Q1 Q2 RI2 RI3; unfold K_FREEARR_OFF in *; lia].
        * intros b Hb. pose proof Hb as Hb'. unfold busy_of in Hb'. apply find_some in Hb'. destruct Hb' as [HIn HP].
          apply andb_true_iff in HP. destruct HP as [HP1 HP2]. apply Z.eqb_eq in HP1. apply Z.eqb_eq in HP2.
          split; [exact HP1|]. split; [exact HP2|]. exact (awf_fits L st X b WF HIn).
      + intros POS. apply Kres; [clear -Q1 RI1; lia | clear -POS; lia | clear -Q1 Q2 RI2 RI3; unfold K_FREEARR_OFF in *; lia].
    - eapply (aslot_shadow_update L W m m' MU WM st st X X c (-1)); [exact SHADOW | reflexivity | reflexivity | reflexivity | | | intros Hk; exfalso; clear -Hk; lia | apply shlen_nonneg; clear -QS; lia].
      + intros k Hk _. (pose proof (slot_in_region L st c k ltac:(clear -QS; lia) (proj1 Q1) Hk) as ndP__; nd_pre ndP__ 3%nat; intros P5 P4 P0; nd_post).
        pose proof (slot_aligned L c k SAL ltac:(unfold K_NUM_CLASSES; clear -Hc; lia)) as AL.
        split; [reflexivity|]. apply Kres_sh; [apply shad_mono; clear -P5 RI1; lia | apply shlen_nonneg; clear -QS; lia |].
        rewrite <- shad_add_shlen by (clear -AL; Z.div_mod_to_equations; lia). apply shad_mono. clear -P4 Q1 Q2 RI2 RI3. unfold K_FREEARR_OFF in *. lia.
      + intros POS. apply Kres_sh; [apply shad_mono; clear -Q1 RI1; lia | clear -POS; lia |].
        rewrite <- shad_add_shlen by (pose proof (mod16_of_class _ _ Q3 QS16 ltac:(clear -QS; lia)) as AM; clear -AM RM; Z.div_mod_to_equations; lia).
        apply shad_mono. clear -Q1 Q2 RI2 RI3. unfold K_FREEARR_OFF in *. lia. }
  split; [exists (q_set_ia Q); exact AQ'|].
  split.
  { cbn [ah_sec AHQ]. cbn [ah_sec AHQ] in HS.
    eapply (hs_frame _ HL L st st X X m m' W); [exact HS | exact MU | exact WM | |].
    - unfold sec_untouched, aknown, W, Wrpre. unfold AINSTANCE, AIMG_HI in *.
      (* [comment removed for export] *)
      apply Forall_cons; [cbn [fst snd]; intros a Ha; do 4 right; left; clear -Ha HSP; lia|].
      do 2 (apply Forall_cons; [cbn [fst snd]; intros a Ha; left; clear -Ha; lia|]).
      do 2 (apply Forall_cons; [cbn [fst snd]; intros a Ha; do 5 right; left; clear -Ha OT; lia|]).
      apply Forall_nil.
    - apply sec_same_refl. }
  split.
  { cbn [ah_depot AHQ]. cbn [ah_depot AHQ] in HD.
    eapply (hd_frame _ HL L m m' W); [exact HD | exact MU | exact WM |].
    unfold W, Wrpre. unfold AIMG_HI in *.
    repeat (apply Forall_cons; [cbn [fst snd]; intros a Ha; clear -Ha OT ON OS HSP D_t_n D_t_s; lia|]). apply Forall_nil. }
  split; [eapply arelro_frame; [exact MU | exact HRO | apply Kimg; clear; unfold ARELRO_LO, ARELRO_HI, AIMG_HI; lia]|].
  split; [eapply arep_rt2_frame; [exact MU | exact WM | exact RT2 | | |]; apply Kimg; clear; unfold AIMG_HI; lia|].
  split; [| eapply arep_rt3_frame; [exact MU | exact WM | exact RT3 |]; unfold rt3_hulls; repeat (apply Forall_cons; [cbn [fst snd]; apply Kimg; clear; unfold AIMG_HI; lia|]); apply Forall_nil].
  intros c Hc. (nd_pre (PERC c Hc) 8%nat; intros Q1 Q2 Q3 Q4 Q5 Q6 Q7 _; nd_post). unfold K_NUM_CLASSES in Hc.
  assert (RI : al_res L <= aregion L c /\ aregion L c + K_REGION <= al_space_beg L + K_SPACE_SIZE
               /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
  { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc RSP. lia. }
  (nd_pre RI 3%nat; intros RI1 RI2 RI3; nd_post). unfold K_REGION, K_SPACE_SIZE in RI2, RI3. change (2^37) with 137438953472 in RI2, RI3.
  eapply (ashadow_avail_frame L W m m' MU WM st); [exact (AVL c ltac:(unfold K_NUM_CLASSES; clear -Hc; lia)) | reflexivity | reflexivity | |].
  - intros POS. apply Kres_sh; [apply shad_mono; unfold aregion in *; clear -Q1 RI1; lia | clear -POS; lia |].
    rewrite <- shad_add_shlen by (pose proof (aregion_mod L c SAL) as RM; clear -RM Q4; unfold K_USER_MAP in *; Z.div_mod_to_equations; lia).
    apply shad_mono. unfold K_FREEARR_OFF, K_REGION in *. clear -Q1 Q2 RI2 RI3. lia.
  - intros POS. apply Kres_sh; [apply shad_mono; unfold afreearr, K_FREEARR_OFF, aregion in *; clear -Q5 Q6 RI1; lia | clear -POS; lia |].
    rewrite <- shad_add_shlen by (pose proof (aregion_mod L c SAL) as RM; unfold afreearr, K_FREEARR_OFF; clear -RM Q7; unfold K_FREEARR_MAP in *; Z.div_mod_to_equations; lia).
    apply shad_mono. unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q5 Q6 RI2 RI3. lia.
Qed.
End Zd1.
#[using="HL"] Lemma AREP_rpre : ltac:(let t := eval cbv delta [AREP_rpre__stmt] in AREP_rpre__stmt in exact t).
Proof. exact AREP_rpre__body. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition arealloc_preP__stmt : Prop := forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (p : aptr) (A nold n lo : Z) (tr : list Z),
  AHEAP_P (AHQ DI ASEC AFK) L RNG st LB m -> In (HB p A nold) LB ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - 8192 ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 n -> 1 <= n < 2^64 ->
  aunw m L RNG lo AREALLOC_PC' sp s0 ra tr ->
  bv_unsigned s0 <> bv_unsigned sp + 8 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AREALLOC_PC' ->
  bv_unsigned sp mod 16 = 0 ->
  rng RNG lo (bv_unsigned sp - lo) ->
  exists trc, In (AREALLOC_PC' :: trc) (al_U L) /\ (length trc <= 29)%nat /\ bv_unsigned sp < 2^47 /\
  evtF asegs RNG (fun ms' => realloc_pre_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A n (al_t L) lo trc m ms'
                             /\ AHEAP_P (AHQ DI ASEC AFK) L RNG st LB (ms_mem ms')
                             /\ aheap_pres CI LB (bv_unsigned sp) m (ms_mem ms'))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AREALLOC_SYM') fc None m (seg_rom asegs)).
Section Zd2.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'arealloc_preP__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'arealloc_preP__stmt 1).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'arealloc_preP__stmt 2).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'arealloc_preP__stmt 3).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'arealloc_preP__stmt 4).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'arealloc_preP__stmt 5).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'arealloc_preP__stmt 6).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'arealloc_preP__stmt 7).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'arealloc_preP__stmt 8).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'arealloc_preP__stmt 9).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'arealloc_preP__stmt 10).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'arealloc_preP__stmt 11).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'arealloc_preP__stmt 12).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'arealloc_preP__stmt 13).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'arealloc_preP__stmt 14).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'arealloc_preP__stmt 15).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'arealloc_preP__stmt 16).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'arealloc_preP__stmt 17).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'arealloc_preP__stmt 18).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'arealloc_preP__stmt 19).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'arealloc_preP__stmt 20).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'arealloc_preP__stmt 21).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'arealloc_preP__stmt 22).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'arealloc_preP__stmt 23).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'arealloc_preP__stmt 24).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'arealloc_preP__stmt 25).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'arealloc_preP__stmt 26).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'arealloc_preP__stmt 27).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'arealloc_preP__stmt 28).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'arealloc_preP__stmt 29).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'arealloc_preP__stmt 30).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'arealloc_preP__stmt 31).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'arealloc_preP__stmt 32).
Variable F : ltac2:(SecDietF.SzSecF.ty 'arealloc_preP__stmt 33).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'arealloc_preP__stmt 34).
Variable m : ltac2:(SecDietF.SzSecF.ty 'arealloc_preP__stmt 35).
Variable st : ltac2:(SecDietF.SzSecF.ty 'arealloc_preP__stmt 36).
Variable LB : ltac2:(SecDietF.SzSecF.ty 'arealloc_preP__stmt 37).
Variable p : ltac2:(SecDietF.SzSecF.ty 'arealloc_preP__stmt 38).
Variable A : ltac2:(SecDietF.SzSecF.ty 'arealloc_preP__stmt 39).
Variable nold : ltac2:(SecDietF.SzSecF.ty 'arealloc_preP__stmt 40).
Variable n : ltac2:(SecDietF.SzSecF.ty 'arealloc_preP__stmt 41).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'arealloc_preP__stmt 42).
Variable tr : ltac2:(SecDietF.SzSecF.ty 'arealloc_preP__stmt 43).
#[using="HL CI_OK"] Lemma arealloc_preP__body : ltac:(let T := type of (fun (h : arealloc_preP__stmt) => h L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st LB p A nold n lo tr) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (st, (LB, (p, (A, (nold, (n, (lo, tr)))))))))))))))))))))))))))))))))))))))))))) as _.
 intros AH HIN MI ST BOT LO8 TP Ha0 Ha1 NR AUNW S0NE RA4 RANE SP16 RSTK.
  assert (LO : lo <= bv_unsigned sp - AFREE_STACK) by (unfold AFREE_STACK; clear -LO8; lia).
  (pose proof (AHEAP_P_hb_range _ L RNG st LB m p A nold AH HIN) as ndP__; nd_pre ndP__ 4%nat; intros ABLK NOLD0 AHI0 A16; nd_post).
  assert (APOS : 1 <= A < 2^47) by (unfold ablk, KLS, AIMG_HI in ABLK; atop_facts; clear -ABLK AHI0 NOLD0; lia).
  assert (EXARM : exists trc,
      ((bv_unsigned sp + 16 < al_top L /\ uchain m (al_top L) AREALLOC_PC' (bv_unsigned sp) (bv_unsigned s0) 28%nat tr /\ (length tr <= 28)%nat /\ trc = bv_unsigned ra :: tr
        /\ rng RNG lo (al_top L - lo))
       \/ (al_top L <= bv_unsigned sp + 16 /\ bv_unsigned sp < 2^47 /\ trc = []))
      /\ In (AREALLOC_PC' :: trc) (al_U L) /\ (length trc <= 29)%nat /\ bv_unsigned sp < 2^47).
  { (pose proof (alayout_stack L (proj1 AH)) as ndP__; nd_pre ndP__ 3%nat; intros K1 K2 K3; nd_post).
    destruct AUNW as [(T1 & U1 & L1 & I1 & R1)|(T1 & T2 & I1)].
    - exists (bv_unsigned ra :: tr). split; [left; split; [exact T1|]; split; [exact U1|]; split; [exact L1|]; split; [reflexivity| exact R1]|].
      split; [exact I1|]. split; [cbn [length]; clear -L1; lia | clear -T1 K2; lia].
    - exists (@nil Z). split; [right; split; [exact T1|]; split; [exact T2| reflexivity]|]. split; [exact I1|]. split; [cbn [length]; clear; lia | exact T2]. }
  (nd_pre EXARM 5%nat; intros trc ARM TRU LTRC SP47; nd_post).
  exists trc. split; [exact TRU|]. split; [exact LTRC|]. split; [exact SP47|].
  (nd_pre AH 4%nat; intros ALO ARNG [X [AR BL]] HFK; nd_post).
  pose proof AR as AR0. (nd_pre AR0 12%nat; intros WF RT INST THR CLS HQ HS HD HRO HRT2 AVL RT3; nd_post).
  cbn [ah_quar ah_sec ah_depot ah_fake AHQ] in HQ, HS, HD, HFK. destruct HQ as [Q AQ].
  pose proof WF as WF0. (nd_pre WF0 11%nat; intros SBE PAE SAL SLO SHI PERC OUTC BUSY LIVEB FRESH UNIQ; nd_post).
  (* [comment removed for export] *)
  pose proof ARNG as ARNG0. (nd_pre ARNG0 14%nat; intros RIMG RT4 RCTX RNO RSTO RRI RFK RSFK RDT RCLS RPA RSECS RPSH RTLS; nd_post).
  (pose proof (alayout_t L ALO) as ndP__; nd_pre ndP__ 4%nat; intros TL1 TL2 TL3 TL4; nd_post). pose proof TL1 as TL1u. pose proof TL4 as TL4u. unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in TL1u, TL4u.   (* [comment removed for export] *)
  (pose proof (alayout_ctx L ALO) as ndP__; nd_pre ndP__ 5%nat; intros CL1 CL2 CL3 CL4 CL5; nd_post).
  (pose proof (alayout_stack L ALO) as ndP__; nd_pre ndP__ 3%nat; intros STK1 STK2 STK3; nd_post).
  pose proof (ao_t L ALO) as OT. pose proof (ao_res L ALO) as ORS. pose proof (ao_fake L ALO) as OFK. pose proof (ao_dtls L ALO) as ODT.
  unfold aobj in OT, ORS, OFK, ODT. pose proof (ao_space L ALO) as RSP. pose proof (ao_res_hi L ALO) as RHI. unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in OT, ORS, OFK, ODT.   (* [comment removed for export] *)
  pose proof (ad_t_res L ALO) as D_t_res. pose proof (ad_t_fake L ALO) as D_t_f. pose proof (ad_t_dtls L ALO) as D_t_d.
  unfold adisj in D_t_res, D_t_f, D_t_d.
  (* [comment removed for export] *)
  pose proof RT as RT0.
  (nd_pre RT0 28%nat; intros GPG GOT GOT80 RIC LS1 REAL IMAX4 FLG5 FLG HPP SHB CANP TI TK INI2 LAY MCS OOM3 PGC HK2 CF8 CF34 CSMT T88 TSD LS2 CT8 CT; nd_post).
  pose proof INI2 as INI. rw_split INI 1%nat INI1 INIx. clear INIx.
  pose proof OOM3 as OOM. rw_split OOM 2%nat OOMx RSS0. clear OOMx.
  pose proof IMAX4 as IMAX. rw_split IMAX 3%nat IMAX3 IMAXx. clear IMAXx.
  (nd_pre THR 6%nat; intros T0 T40 CACHES CSTATS [sj [STATS LSJ]] UNW; nd_post).
  pose proof AQ as AQ0. (nd_pre AQ0 6%nat; intros _ _ _ (FL & IAS & IAM) CP _; nd_post).
  unfold AIA_FLAG, AIA_BASE, AIA_SIZE, AIA_MAP1, AIA_MAP1_LEN in FL, IAS, IAM.
  (* [comment removed for export] *)
  unfold AIMG_HI, AFREE_STACK, UDEPTH in *.
  box CL5.
  pose proof T0 as TT0. rw_split TT0 1%nat TTctx TT.
  eapply evtF_mono.
  { eapply (realloc_pre_spec L (q_ia Q) RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m
              A n (al_t L) lo (al_top L) (al_bot L) tr trc sj).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => first [exact ST | exact IAS]
         | |- mem_inv _ _ => exact MI
         | |- allocA_cells _ _ _ => unfold allocA_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
         | |- (_ /\ _) \/ (_ /\ _) => exact ARM
         | |- u64arr _ _ _ _ => exact STATS
         | |- _ = true -> _ => exact IAM
         end.
    all: try lazymatch goal with
         | |- rw_cells _ _ (al_t _) [C8 _] => exact TTctx
         | |- rw_cells _ _ (al_t _ + 8) _ => exact TT
         | |- rw_cells _ _ _ _ => assumption
         | |- @eq word _ _ => first [exact TP | exact Ha0 | exact Ha1 | reflexivity]
         | |- _ \/ _ => first [unboxed CL5 | pose proof CL5 as Y; unbox Y; lia]
         | |- rng _ _ _ => first [assumption | eapply rng_sub; [exact RCTX| lia| lia] | solve_rng]
         end.
    all: try assumption.
    all: unfold AIMG_HI, UDEPTH in *.
    all: try (generalize LO LO8 BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 RA4 APOS NR LSJ LTRC; clear; intros; unfold AFREE_STACK in *; lia).
    all: match goal with |- ?G => idtac "REMF" G end. }
  cbv beta. intros ms' PM. pose proof PM as PM0. unfold realloc_pre_post in PM.
  (nd_pre PM 15%nat; intros t0' t1' t2' a7' t3' t4' t5' t6' fr0 junk0 junk2 tb sj' m' ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 18%nat; intros MU0 WM MI' ST' FR48 FR16 FRP SS TB LTB TRF FRS UNW' STATS' LSJ' FL' IAS' IAM'; nd_post).
  assert (MU : munch (Wrpre (bv_unsigned sp) (al_t L)) m m').
  { eapply munch_weaken; [| exact MU0]. unfold Wrpre, sub_fp. cbn [outside]. intros q Hq. clear -Hq. lia. }
  assert (IA' : aintal true m').
  { unfold aintal, AIA_FLAG, AIA_BASE, AIA_SIZE, AIA_MAP1, AIA_MAP1_LEN. split; [exact FL'|]. split; [exact IAS'|]. intros _. exact IAM'. }
  destruct (AREP_rpre L st X Q m m' (bv_unsigned sp) ALO AR AQ MU WM ltac:(atop_facts; clear -LO BOT STK3; unfold AFREE_STACK in *; lia) UNW' IA'
              ltac:(exists sj'; split; [exact STATS'| exact LSJ'])) as [AR' AQ'].
  split; [exact PM0|]. cbn [ms_mem].
  apply and_comm. split.
  (* [comment removed for export] *)
  { (* [comment removed for export] *)
    intros a Ha CLA. split; [| intros Hw; apply WM; exact Hw]. apply MU. rewrite wa_unsigned by exact Ha.
    word_range sp SPR.
    unfold Wrpre. cbn [outside].
    destruct CLA as [CLA|TL].
    2:{ (* [comment removed for export] *)
        pose proof (ad_tls_t L ALO) as DLT. unfold adisj in DLT. pose proof atp_lin as TLN. pose proof atop_range as ATR0. pose proof atp_below_atop as TBA.
        destruct TL as [[T|(ta & Hta & ->)]|[IM|IM]].
        4:{ pose proof (ao_ahm L ALO) as OAH. pose proof (aobj_img _ _ OAH ltac:(clear; lia)) as OAHI. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OAH, OAHI.
          rewrite <- (ao_ahm_eq L ALO) in IM. unfold AAHM_SZ in IM. pose proof (ad_ahm_t L ALO) as DA1. unfold adisj in DA1.
            clear -IM OAH OAHI DA1 Ha LO BOT STK3 ATR0. lia. }
        - clear -T Ha DLT TLN ATR0 TBA LO BOT STK3. lia.
        - pose proof (tls_shadow_band ta Hta) as (TS1 & TS2).
          assert (SA : shad ATOP <= 17594332446720) by (rewrite shad_div; unfold ASHOFF; clear -ATR0; Z.div_mod_to_equations; lia).
          clear -TS1 TS2 SA Ha TL1u LO BOT STK3 ATR0. lia.
        - unfold AIMSH_LO, AIMSH_LEN in IM. clear -IM Ha TL1u LO BOT STK3 ATR0. lia. }
    destruct CLA as [SK | [CIa | [BLK | SH]]].
    - clear -SK Ha LO BOT STK3 TL2. lia.
    - (nd_pre CIa 3%nat; intros iv Hiv R; nd_post). (pose proof (proj1 (Forall_forall _ _) CI_OK iv Hiv) as ndP__; nd_pre ndP__ 6%nat; intros Q1 Q2 Q3 Q4 Q5 Q6; nd_post). cbn [fst snd] in *.
      unfold AIMG_HI in *. clear -R Q1 Q3 Q5 Q6 LO BOT STK3 TL4u. lia.
    - (nd_pre BLK 3%nat; intros [[q|cls] A' n'] Hin R; nd_post); cbn [ab_addr ab_size] in R.
      + destruct (proj1 BL q A' n' Hin) as [(b & Hb & Sb & Ub & Nb)|(mb & msz & Lp & EUA & Gs)].
        * destruct (BUSY b Hb) as [CLB _].
          (nd_pre (PERC (xb_class b) CLB) 12%nat; intros P1 P2 _ _ _ _ _ _ _ _ _ PR; nd_post).
          pose proof (size_of_class_facts (xb_class b) CLB) as [QS _].
          assert (KB : 0 <= xb_slot b < ndist st (xb_class b)).
          { apply PR. apply in_app_iff. right. apply in_app_iff. right. unfold busy_slots. apply in_map_iff. exists b. split; [reflexivity|].
            apply filter_In. split; [exact Hb| apply Z.eqb_refl]. }
          (pose proof (slot_in_region L st (xb_class b) (xb_slot b) ltac:(clear -QS; lia) (proj1 P1) KB) as ndP__; nd_pre ndP__ 3%nat; intros P5 P4 P0; nd_post).
          pose proof (awf_fits L st X b WF Hb) as FIT. unfold xb_fits in FIT. rewrite Sb in FIT.
          subst A' n'. unfold xb_user, xb_alloc, aregion, K_REGION, K_FREEARR_OFF, K_NUM_CLASSES in *.
          clear -R P5 P4 P1 P2 CLB RSP FIT ORS D_t_res LO BOT STK3. lia.
        * (* [comment removed for export] *)
          cbn [sec_wf1] in Gs. (nd_pre Gs 7%nat; intros Gs1 Gs2 Gs3 Gs4 Gs5 Gs6 (Ct & Cc & Cr & Cp & Cn & Cs & Cf & Cd); nd_post).
          pose proof (sec_facts n' ltac:(clear -Gs5; lia) Gs6) as SF. subst A'. unfold SEC_UOFF, K_HIGH_MEM in *.
          unfold ablk, KLS, AIMG_HI in Gs2.   (* [comment removed for export] *)
          clear -R Gs2 Gs3 Gs4 Gs5 SF Ct LO BOT STK3. lia.
      + (nd_pre (proj1 (proj2 BL) cls A' n' Hin) 3%nat; intros K1 K2 K3; nd_post).
        clear -R K1 K2 K3 OFK D_t_f LO BOT STK3. lia.
    - (nd_pre SH 3%nat; intros a' Ha' ndR1__; nd_post; revert ndR1__; intros ->). rewrite shad_div in Ha |- *. unfold ASHOFF in *.
      assert (A47 : 0 <= a' < 2^47).
      { destruct Ha' as [SK | [CIa | FK]].
        - atop_facts. clear -SK SPR. lia.
        - (nd_pre CIa 3%nat; intros iv Hiv R; nd_post). (pose proof (proj1 (Forall_forall _ _) CI_OK iv Hiv) as ndP__; nd_pre ndP__ 4%nat; intros Q1 Q2 Q3 _; nd_post). cbn [fst snd] in *.
          unfold AIMG_HI in *. clear -R Q1 Q3. lia.
        - (nd_pre FK 5%nat; intros cls FA sz Hin R; nd_post). (nd_pre (proj1 (proj2 BL) cls FA sz Hin) 3%nat; intros K1 K2 K3; nd_post). clear -R K1 K3 OFK. lia. }
      clear -A47 LO BOT STK3 TL1u. Z.div_mod_to_equations. lia. }
  split; [exact ALO|]. split; [exact ARNG|]. split; [exists X; split; [exact AR'| exact BL]|].
  (* [comment removed for export] *)
  cbn [ah_fake AHQ].
  assert (SF : 2148238848 <= shad (al_fake L) /\ shad (al_fake L) + shlen 11571200 <= 17594332446720).   (* [comment removed for export] *)
  { rewrite shad_div, shlen_div. unfold ASHOFF in *. pose proof atop_range as AR8. clear -OFK AR8. Z.div_mod_to_equations. lia. }
  eapply (hf_frame _ HL L LB m m'); [exact HFK | exact MU | exact WM |].
  unfold fake_untouched, Wrpre.
  pose proof (ad_tls_t L ALO) as D_l_t. unfold adisj in D_l_t. pose proof atp_lin as TLN. pose proof atop_range as ATR0.      (* [comment removed for export] *)
  repeat (apply Forall_cons; [cbn [fst snd]; clear -OFK ODT OT SF D_t_f D_t_d LO BOT STK3 D_l_t TLN ATR0; lia_relc|]). apply Forall_nil.
Qed.
End Zd2.
#[using="HL CI_OK"] Theorem arealloc_preP : ltac:(let t := eval cbv delta [arealloc_preP__stmt] in arealloc_preP__stmt in exact t).
Proof. exact arealloc_preP__body. Qed.
End S.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Exec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_aalloc_s.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.F_aalloc1.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aunwind.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_adrain__A3W.F_afree_iseg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_afree_null.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.F_afree_arep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfn_arep__A3W.AFreeNull.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepExt.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3g0__A3W.F_arealloc_iseg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3g0__A3W.F_arealloc_pre.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac hide_disj_all := repeat match goal with H : (_ \/ _) |- _ => change (?P) with (sf_hide P) in H end.
Local Ltac hide_disj_but X :=
  repeat match goal with H : (_ \/ _) |- _ => tryif constr_eq H X then fail else change (?P) with (sf_hide P) in H end.
Local Ltac lia_rel := first [ solve [ hide_disj_all; lia ] | match goal with X : (_ \/ _) |- _ => solve [ hide_disj_but X; lia ] end ].
Local Ltac lia_relc := repeat split; first [ lia_rel | lia ].
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition Wrpre (SP t : Z) : list (Z * Z) :=
  [(SP - 4096, SP); (0xafc00, 0xafc00 + 0x81030); (0x13e488, 0x13e488 + 4); (t + 3168, t + 3169); (t + 2800, t + 2800 + 368)]%Z.

Section S.
Variable DI : ADepotIface.
Variables (ASEC : alayout -> astate -> aconc -> amem -> Prop) (AFK : alayout -> list ablock -> amem -> Prop).
Hypothesis HL : ahole_laws (AHQ DI ASEC AFK).
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI
                                  /\ (snd iv <= 0xab670 \/ 0xab730 <= fst iv)
                                  /\ (snd iv <= 0xafc00 \/ 0x130c30 <= fst iv)
                                  /\ (snd iv <= 0x13e488 \/ 0x13e48c <= fst iv)) CI.

Definition AREP_rpre__stmt : Prop := forall L st X Q m m' SP,
  alayout_ok L -> AREP (AHQ DI ASEC AFK) L st X m -> AQUAR_at L st X Q m ->
  munch (Wrpre SP (al_t L)) m m' -> wmono asegs m m' -> ATOP + 4096 <= SP ->
  rw_cells asegs m' (al_t L + 3168) [C1 (Z_to_bv 8 0)] -> aintal true m' ->
  (exists sj', u64arr asegs m' (al_t L + 2800) sj' /\ length sj' = 46%nat) ->
  AREP (AHQ DI ASEC AFK) L st X m' /\ AQUAR_at L st X (q_set_ia Q) m'.
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'AREP_rpre__stmt 0).
Variable st : ltac2:(SecDietF.SzSecF.ty 'AREP_rpre__stmt 1).
Variable X : ltac2:(SecDietF.SzSecF.ty 'AREP_rpre__stmt 2).
Variable Q : ltac2:(SecDietF.SzSecF.ty 'AREP_rpre__stmt 3).
Variable m : ltac2:(SecDietF.SzSecF.ty 'AREP_rpre__stmt 4).
Variable m' : ltac2:(SecDietF.SzSecF.ty 'AREP_rpre__stmt 5).
Variable SP : ltac2:(SecDietF.SzSecF.ty 'AREP_rpre__stmt 6).
Let W := Wrpre SP (al_t L).
#[using="HL W"] Lemma AREP_rpre__body : ltac:(let T := type of (fun (h : AREP_rpre__stmt) => h L st X Q m m' SP) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (st, (X, (Q, (m, (m', SP))))))) as _.
  intros ALO AR AQ MU WM HSP UNW' IA' STATS'.
  chg (Wrpre SP (al_t L)) W.
  (* [comment removed for export] *)
  (pose proof (alayout_space L ALO) as ndP__; nd_pre ndP__ 4%nat; intros SP1 SP2 SP3 SP4; nd_post).
  pose proof (ao_t L ALO) as OT. pose proof (ao_ctx L ALO) as OC. pose proof (ao_res L ALO) as ORS. pose proof (ao_nodes L ALO) as ON.
  pose proof (ao_store L ALO) as OS. pose proof (ao_fake L ALO) as OFK. pose proof (ao_dtls L ALO) as ODT.
  unfold aobj in OT, OC, ORS, ON, OS, OFK, ODT. pose proof (ao_space L ALO) as RSP.
  pose proof (ao_res_hi L ALO) as RHI. unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in OT, OC, ORS, ON, OS, OFK, ODT.   (* [comment removed for export] *)
  pose proof (ad_t_res L ALO) as D_t_res. pose proof (ad_t_ctx L ALO) as D_t_c. pose proof (ad_t_nodes L ALO) as D_t_n.
  pose proof (ad_t_store L ALO) as D_t_s. pose proof (ad_t_fake L ALO) as D_t_f. pose proof (ad_t_dtls L ALO) as D_t_d.
  unfold adisj in D_t_res, D_t_c, D_t_n, D_t_s, D_t_f, D_t_d.
  assert (SHRES : 2201439137792 <= shad (al_res L) /\ shad (al_res L) + shlen 137439023104 = shad (al_res L + 137439023104)
                  /\ shad (al_res L + 137439023104) <= 17594332446720).   (* [comment removed for export] *)
  { rewrite !shad_div, shlen_div. unfold ASHOFF in *. clear -ORS RHI. Z.div_mod_to_equations. lia. }
  (nd_pre SHRES 3%nat; intros SR1 SR2 SR3; nd_post).
  (* [comment removed for export] *)
  assert (Kimg : forall A k, 0x10000 <= A -> 0 <= k -> A + k <= AIMG_HI ->      (* [comment removed for export] *)
            (A + k <= 0xafc00 \/ 0x130c30 <= A) -> (A + k <= 0x13e488 \/ 0x13e48c <= A) -> disjoint_from W A k).
  { intros A k H1 H2 H3 H4 H5. unfold W, Wrpre. cbn. unfold AIMG_HI in *. clear -H1 H2 H3 H4 H5 HSP OT. lia. }
  assert (Kobj : forall A k, AIMG_HI <= A -> 0 <= k -> A + k <= ATOP -> (A + k <= al_t L + 2800 \/ al_t L + 3169 <= A) -> disjoint_from W A k).
  { intros A k H1 H2 H3 H4. unfold W, Wrpre. cbn. unfold AIMG_HI in *. clear -H1 H2 H3 H4 HSP. lia. }
  assert (Kres : forall A k, al_res L <= A -> 0 <= k -> A + k <= al_res L + 137439023104 -> disjoint_from W A k).
  { intros A k H1 H2 H3. apply Kobj; unfold AIMG_HI in *; [clear -H1 ORS; lia | exact H2 | clear -H3 ORS; lia | clear -H1 H3 D_t_res; lia]. }
  assert (Kres_sh : forall A k, shad (al_res L) <= A -> 0 <= k -> A + k <= shad (al_res L + 137439023104) -> disjoint_from W A k).
  { intros A k H1 H2 H3. apply Kobj; unfold AIMG_HI in *; [clear -H1 SR1; lia | exact H2 | clear -H3 SR3; lia | clear -H1 H3 SR1 SR3 OT; lia]. }
  assert (Kt : forall A k, al_t L <= A -> 0 <= k -> A + k <= al_t L + 2800 -> disjoint_from W A k).
  { intros A k H1 H2 H3. unfold W, Wrpre. cbn. unfold AIMG_HI in *. clear -H1 H2 H3 HSP OT. lia. }   (* [comment removed for export] *)
  assert (Kctx : forall A k, al_ctx L <= A -> 0 <= k -> A + k <= al_ctx L + 65536 -> disjoint_from W A k).
  { intros A k H1 H2 H3. apply Kobj; unfold AIMG_HI in *; [clear -H1 OC; lia | exact H2 | clear -H3 OC; lia | clear -H1 H3 D_t_c; lia]. }
  assert (Ktls : forall A k, ATPv + -200 <= A -> 0 <= k -> A + k <= ATPv + 312 -> disjoint_from W A k).      (* [comment removed for export] *)
  { pose proof (ad_tls_t L ALO) as D_tls_t. unfold adisj in D_tls_t. pose proof atp_lin as TLN. pose proof atop_range as ATR0.
    intros A k H1 H2 H3. unfold W, Wrpre. cbn. unfold AIMG_HI in *. clear -H1 H2 H3 HSP OT D_tls_t TLN ATR0. lia. }
  (* [comment removed for export] *)
  pose proof AR as AR0. (nd_pre AR0 12%nat; intros WF RT INST THR CLS HQ HS HD HRO RT2 AVL RT3; nd_post).
  pose proof WF as WF0. (nd_pre WF0 11%nat; intros SBE PAE SAL SLO SHI PERC OUTC BUSY LIVE FRESH UNIQ; nd_post).
  (* [comment removed for export] *)
  assert (BB : forall b, In b (x_busy X) -> al_res L <= xb_alloc L b /\ xb_alloc L b + size_of_class (xb_class b) <= al_res L + 137439023104).
  { intros b Hb. destruct (BUSY b Hb) as [CLB _].
    (nd_pre (PERC (xb_class b) CLB) 12%nat; intros Q1 Q2 _ _ _ _ _ _ _ _ _ QR; nd_post).
    pose proof (size_of_class_facts (xb_class b) CLB) as [QS _].
    assert (KB : 0 <= xb_slot b < ndist st (xb_class b)).
    { apply QR. apply in_app_iff. right. apply in_app_iff. right. unfold busy_slots. apply in_map_iff. exists b. split; [reflexivity|].
      apply filter_In. split; [exact Hb| apply Z.eqb_refl]. }
    (pose proof (slot_in_region L st (xb_class b) (xb_slot b) ltac:(clear -QS; lia) (proj1 Q1) KB) as ndP__; nd_pre ndP__ 3%nat; intros P5 P4 P0; nd_post).
    unfold xb_alloc, aregion, K_REGION, K_FREEARR_OFF, K_NUM_CLASSES in *. clear -P5 P4 Q1 Q2 CLB RSP. lia. }
  assert (AQ' : AQUAR_at L st X (q_set_ia Q) m').
  { eapply AQUAR_null; [exact AQ | exact MU | exact WM | | exact IA'].
    unfold W, Wrpre. unfold AINSTANCE, AIMG_HI in *.
    repeat (apply Forall_cons; [cbn [fst snd]; split; [clear -OT HSP; lia|]; split; [clear -OT HSP; lia|];
                                intros b Hb; destruct (BB b Hb) as [B1 B2]; destruct (xb_st b); [exact I| |]; clear -B1 B2 ORS OT HSP D_t_res; lia |]).
    apply Forall_nil. }
  split; [| exact AQ'].
  split; [exact WF|].
  split. { eapply arep_rt_frame; [exact MU | exact WM | exact RT |]. unfold rt_hulls, ATP88, ATSD.
           repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply Ktls; clear; lia] |]). apply Forall_nil. }
  split. { eapply ainstance_frame; [exact MU | exact WM | exact INST | reflexivity | reflexivity | | |]; apply Kimg; clear; unfold AINSTANCE, AIMG_HI; lia. }
  split.
  { (nd_pre THR 6%nat; intros T0 T40 CACHES CSTATS [sj [STATS LSJ]] UNW; nd_post). unfold athread.
    split; [eapply cells_frame; [exact T0 | exact MU | exact WM | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; apply Kt; clear; lia]|].
    split; [eapply cells_frame; [exact T40 | exact MU | exact WM | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; apply Kt; clear; lia]|].
    split. { intros c Hc. eapply acache_cells_frame; [exact MU | exact WM | exact (CACHES c Hc) | reflexivity | reflexivity | reflexivity |].
             unfold acache_addr. unfold K_NUM_CLASSES in Hc. apply Kt; clear -Hc; lia. }
    split; [eapply junk_frame; [exact CSTATS | exact MU | exact WM | intros _; apply Kt; clear; lia]|].
    split; [exact STATS'|].
    exact UNW'. }
  split.
  { intros c Hc. (nd_pre (CLS c Hc) 4%nat; intros REG FARR SLOTS SHADOW; nd_post).
    (nd_pre (PERC c Hc) 12%nat; intros Q1 Q2 Q3 Q4 Q5 Q6 Q7 QLENF QLENC QCNTB QND QRANGE; nd_post).
    pose proof (size_of_class_facts c Hc) as [QS QS16]. pose proof (aregion_mod L c SAL) as RM. unfold K_NUM_CLASSES in Hc.
    assert (RI : al_res L <= aregion L c /\ aregion L c + K_REGION <= al_space_beg L + K_SPACE_SIZE
                 /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
    { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc RSP. lia. }
    (nd_pre RI 3%nat; intros RI1 RI2 RI3; nd_post). unfold K_REGION, K_SPACE_SIZE in RI2, RI3. change (2^37) with 137438953472 in RI2, RI3.
    split; [| split; [| split]].
    - eapply aregion_cells_frame; [exact MU | exact WM | exact REG | reflexivity | reflexivity | reflexivity | reflexivity |].
      apply Kres; unfold aregion_info, ARI_STRIDE, K_SPACE_SIZE; change (2^37) with 137438953472; clear -Hc RSP; lia.
    - eapply afreearray_frame; [exact MU | exact WM | exact FARR | reflexivity | reflexivity | reflexivity | exact QLENF | exact Q5 | | clear -Q6; lia |].
      + apply Kres; unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX in *; [clear -RI1; lia | clear -Q5 Q6; lia | clear -RI2 RI3 Q6; lia].
      + apply Kres_sh; [apply shad_mono; unfold afreearr, K_FREEARR_OFF; clear -RI1; lia | apply shlen_nonneg; clear -Q5 Q6; lia |].
        rewrite <- shad_add_shlen by (unfold afreearr, K_FREEARR_OFF; clear -RM; Z.div_mod_to_equations; lia). apply shad_mono.
        unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX in *. clear -RI2 RI3 Q6. lia.
    - eapply (aslots_update L W m m' MU WM st st X X c (-1)); [exact SLOTS | reflexivity | reflexivity | reflexivity | | | intros Hk; exfalso; clear -Hk; lia].
      + intros k Hk _. (pose proof (slot_in_region L st c k ltac:(clear -QS; lia) (proj1 Q1) Hk) as ndP__; nd_pre ndP__ 3%nat; intros P5 P4 P0; nd_post).
        split; [reflexivity|]. split.
        * apply Kres; [clear -P5 RI1; lia | clear -QS; lia | clear -P4 Q1 Q2 RI2 RI3; unfold K_FREEARR_OFF in *; lia].
        * intros b Hb. pose proof Hb as Hb'. unfold busy_of in Hb'. apply find_some in Hb'. destruct Hb' as [HIn HP].
          apply andb_true_iff in HP. destruct HP as [HP1 HP2]. apply Z.eqb_eq in HP1. apply Z.eqb_eq in HP2.
          split; [exact HP1|]. split; [exact HP2|]. exact (awf_fits L st X b WF HIn).
      + intros POS. apply Kres; [clear -Q1 RI1; lia | clear -POS; lia | clear -Q1 Q2 RI2 RI3; unfold K_FREEARR_OFF in *; lia].
    - eapply (aslot_shadow_update L W m m' MU WM st st X X c (-1)); [exact SHADOW | reflexivity | reflexivity | reflexivity | | | intros Hk; exfalso; clear -Hk; lia | apply shlen_nonneg; clear -QS; lia].
      + intros k Hk _. (pose proof (slot_in_region L st c k ltac:(clear -QS; lia) (proj1 Q1) Hk) as ndP__; nd_pre ndP__ 3%nat; intros P5 P4 P0; nd_post).
        pose proof (slot_aligned L c k SAL ltac:(unfold K_NUM_CLASSES; clear -Hc; lia)) as AL.
        split; [reflexivity|]. apply Kres_sh; [apply shad_mono; clear -P5 RI1; lia | apply shlen_nonneg; clear -QS; lia |].
        rewrite <- shad_add_shlen by (clear -AL; Z.div_mod_to_equations; lia). apply shad_mono. clear -P4 Q1 Q2 RI2 RI3. unfold K_FREEARR_OFF in *. lia.
      + intros POS. apply Kres_sh; [apply shad_mono; clear -Q1 RI1; lia | clear -POS; lia |].
        rewrite <- shad_add_shlen by (pose proof (mod16_of_class _ _ Q3 QS16 ltac:(clear -QS; lia)) as AM; clear -AM RM; Z.div_mod_to_equations; lia).
        apply shad_mono. clear -Q1 Q2 RI2 RI3. unfold K_FREEARR_OFF in *. lia. }
  split; [exists (q_set_ia Q); exact AQ'|].
  split.
  { cbn [ah_sec AHQ]. cbn [ah_sec AHQ] in HS.
    eapply (hs_frame _ HL L st st X X m m' W); [exact HS | exact MU | exact WM | |].
    - unfold sec_untouched, aknown, W, Wrpre. unfold AINSTANCE, AIMG_HI in *.
      (* [comment removed for export] *)
      apply Forall_cons; [cbn [fst snd]; intros a Ha; do 4 right; left; clear -Ha HSP; lia|].
      do 2 (apply Forall_cons; [cbn [fst snd]; intros a Ha; left; clear -Ha; lia|]).
      do 2 (apply Forall_cons; [cbn [fst snd]; intros a Ha; do 5 right; left; clear -Ha OT; lia|]).
      apply Forall_nil.
    - apply sec_same_refl. }
  split.
  { cbn [ah_depot AHQ]. cbn [ah_depot AHQ] in HD.
    eapply (hd_frame _ HL L m m' W); [exact HD | exact MU | exact WM |].
    unfold W, Wrpre. unfold AIMG_HI in *.
    repeat (apply Forall_cons; [cbn [fst snd]; intros a Ha; clear -Ha OT ON OS HSP D_t_n D_t_s; lia|]). apply Forall_nil. }
  split; [eapply arelro_frame; [exact MU | exact HRO | apply Kimg; clear; unfold ARELRO_LO, ARELRO_HI, AIMG_HI; lia]|].
  split; [eapply arep_rt2_frame; [exact MU | exact WM | exact RT2 | | |]; apply Kimg; clear; unfold AIMG_HI; lia|].
  split; [| eapply arep_rt3_frame; [exact MU | exact WM | exact RT3 |]; unfold rt3_hulls; repeat (apply Forall_cons; [cbn [fst snd]; apply Kimg; clear; unfold AIMG_HI; lia|]); apply Forall_nil].
  intros c Hc. (nd_pre (PERC c Hc) 8%nat; intros Q1 Q2 Q3 Q4 Q5 Q6 Q7 _; nd_post). unfold K_NUM_CLASSES in Hc.
  assert (RI : al_res L <= aregion L c /\ aregion L c + K_REGION <= al_space_beg L + K_SPACE_SIZE
               /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
  { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc RSP. lia. }
  (nd_pre RI 3%nat; intros RI1 RI2 RI3; nd_post). unfold K_REGION, K_SPACE_SIZE in RI2, RI3. change (2^37) with 137438953472 in RI2, RI3.
  eapply (ashadow_avail_frame L W m m' MU WM st); [exact (AVL c ltac:(unfold K_NUM_CLASSES; clear -Hc; lia)) | reflexivity | reflexivity | |].
  - intros POS. apply Kres_sh; [apply shad_mono; unfold aregion in *; clear -Q1 RI1; lia | clear -POS; lia |].
    rewrite <- shad_add_shlen by (pose proof (aregion_mod L c SAL) as RM; clear -RM Q4; unfold K_USER_MAP in *; Z.div_mod_to_equations; lia).
    apply shad_mono. unfold K_FREEARR_OFF, K_REGION in *. clear -Q1 Q2 RI2 RI3. lia.
  - intros POS. apply Kres_sh; [apply shad_mono; unfold afreearr, K_FREEARR_OFF, aregion in *; clear -Q5 Q6 RI1; lia | clear -POS; lia |].
    rewrite <- shad_add_shlen by (pose proof (aregion_mod L c SAL) as RM; unfold afreearr, K_FREEARR_OFF; clear -RM Q7; unfold K_FREEARR_MAP in *; Z.div_mod_to_equations; lia).
    apply shad_mono. unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q5 Q6 RI2 RI3. lia.
Qed.
End Zd1.
#[using="HL"] Lemma AREP_rpre : ltac:(let t := eval cbv delta [AREP_rpre__stmt] in AREP_rpre__stmt in exact t).
Proof. exact AREP_rpre__body. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition arealloc_preP__stmt : Prop := forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (p : aptr) (A nold n lo : Z) (tr : list Z),
  AHEAP_P (AHQ DI ASEC AFK) L RNG st LB m -> In (HB p A nold) LB ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - 8192 ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 n -> 1 <= n < 2^64 ->
  aunw m L RNG lo AREALLOC_PC' sp s0 ra tr ->
  bv_unsigned s0 <> bv_unsigned sp + 8 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AREALLOC_PC' ->
  bv_unsigned sp mod 16 = 0 ->
  rng RNG lo (bv_unsigned sp - lo) ->
  exists trc, In (AREALLOC_PC' :: trc) (al_U L) /\ (length trc <= 29)%nat /\ bv_unsigned sp < 2^47 /\
  evtF asegs RNG (fun ms' => realloc_pre_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A n (al_t L) lo trc m ms'
                             /\ AHEAP_P (AHQ DI ASEC AFK) L RNG st LB (ms_mem ms')
                             /\ aheap_pres CI LB (bv_unsigned sp) m (ms_mem ms'))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AREALLOC_SYM') fc None m (seg_rom asegs)).
Section Zd2.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'arealloc_preP__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'arealloc_preP__stmt 1).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'arealloc_preP__stmt 2).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'arealloc_preP__stmt 3).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'arealloc_preP__stmt 4).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'arealloc_preP__stmt 5).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'arealloc_preP__stmt 6).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'arealloc_preP__stmt 7).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'arealloc_preP__stmt 8).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'arealloc_preP__stmt 9).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'arealloc_preP__stmt 10).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'arealloc_preP__stmt 11).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'arealloc_preP__stmt 12).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'arealloc_preP__stmt 13).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'arealloc_preP__stmt 14).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'arealloc_preP__stmt 15).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'arealloc_preP__stmt 16).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'arealloc_preP__stmt 17).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'arealloc_preP__stmt 18).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'arealloc_preP__stmt 19).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'arealloc_preP__stmt 20).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'arealloc_preP__stmt 21).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'arealloc_preP__stmt 22).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'arealloc_preP__stmt 23).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'arealloc_preP__stmt 24).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'arealloc_preP__stmt 25).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'arealloc_preP__stmt 26).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'arealloc_preP__stmt 27).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'arealloc_preP__stmt 28).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'arealloc_preP__stmt 29).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'arealloc_preP__stmt 30).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'arealloc_preP__stmt 31).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'arealloc_preP__stmt 32).
Variable F : ltac2:(SecDietF.SzSecF.ty 'arealloc_preP__stmt 33).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'arealloc_preP__stmt 34).
Variable m : ltac2:(SecDietF.SzSecF.ty 'arealloc_preP__stmt 35).
Variable st : ltac2:(SecDietF.SzSecF.ty 'arealloc_preP__stmt 36).
Variable LB : ltac2:(SecDietF.SzSecF.ty 'arealloc_preP__stmt 37).
Variable p : ltac2:(SecDietF.SzSecF.ty 'arealloc_preP__stmt 38).
Variable A : ltac2:(SecDietF.SzSecF.ty 'arealloc_preP__stmt 39).
Variable nold : ltac2:(SecDietF.SzSecF.ty 'arealloc_preP__stmt 40).
Variable n : ltac2:(SecDietF.SzSecF.ty 'arealloc_preP__stmt 41).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'arealloc_preP__stmt 42).
Variable tr : ltac2:(SecDietF.SzSecF.ty 'arealloc_preP__stmt 43).
#[using="HL CI_OK"] Lemma arealloc_preP__body : ltac:(let T := type of (fun (h : arealloc_preP__stmt) => h L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st LB p A nold n lo tr) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (st, (LB, (p, (A, (nold, (n, (lo, tr)))))))))))))))))))))))))))))))))))))))))))) as _.
 intros AH HIN MI ST BOT LO8 TP Ha0 Ha1 NR AUNW S0NE RA4 RANE SP16 RSTK.
  assert (LO : lo <= bv_unsigned sp - AFREE_STACK) by (unfold AFREE_STACK; clear -LO8; lia).
  (pose proof (AHEAP_P_hb_range _ L RNG st LB m p A nold AH HIN) as ndP__; nd_pre ndP__ 4%nat; intros ABLK NOLD0 AHI0 A16; nd_post).
  assert (APOS : 1 <= A < 2^47) by (unfold ablk, KLS, AIMG_HI in ABLK; atop_facts; clear -ABLK AHI0 NOLD0; lia).
  assert (EXARM : exists trc,
      ((bv_unsigned sp + 16 < al_top L /\ uchain m (al_top L) AREALLOC_PC' (bv_unsigned sp) (bv_unsigned s0) 28%nat tr /\ (length tr <= 28)%nat /\ trc = bv_unsigned ra :: tr
        /\ rng RNG lo (al_top L - lo))
       \/ (al_top L <= bv_unsigned sp + 16 /\ bv_unsigned sp < 2^47 /\ trc = []))
      /\ In (AREALLOC_PC' :: trc) (al_U L) /\ (length trc <= 29)%nat /\ bv_unsigned sp < 2^47).
  { (pose proof (alayout_stack L (proj1 AH)) as ndP__; nd_pre ndP__ 3%nat; intros K1 K2 K3; nd_post).
    destruct AUNW as [(T1 & U1 & L1 & I1 & R1)|(T1 & T2 & I1)].
    - exists (bv_unsigned ra :: tr). split; [left; split; [exact T1|]; split; [exact U1|]; split; [exact L1|]; split; [reflexivity| exact R1]|].
      split; [exact I1|]. split; [cbn [length]; clear -L1; lia | clear -T1 K2; lia].
    - exists (@nil Z). split; [right; split; [exact T1|]; split; [exact T2| reflexivity]|]. split; [exact I1|]. split; [cbn [length]; clear; lia | exact T2]. }
  (nd_pre EXARM 5%nat; intros trc ARM TRU LTRC SP47; nd_post).
  exists trc. split; [exact TRU|]. split; [exact LTRC|]. split; [exact SP47|].
  (nd_pre AH 4%nat; intros ALO ARNG [X [AR BL]] HFK; nd_post).
  pose proof AR as AR0. (nd_pre AR0 12%nat; intros WF RT INST THR CLS HQ HS HD HRO HRT2 AVL RT3; nd_post).
  cbn [ah_quar ah_sec ah_depot ah_fake AHQ] in HQ, HS, HD, HFK. destruct HQ as [Q AQ].
  pose proof WF as WF0. (nd_pre WF0 11%nat; intros SBE PAE SAL SLO SHI PERC OUTC BUSY LIVEB FRESH UNIQ; nd_post).
  (* [comment removed for export] *)
  pose proof ARNG as ARNG0. (nd_pre ARNG0 14%nat; intros RIMG RT4 RCTX RNO RSTO RRI RFK RSFK RDT RCLS RPA RSECS RPSH RTLS; nd_post).
  (pose proof (alayout_t L ALO) as ndP__; nd_pre ndP__ 4%nat; intros TL1 TL2 TL3 TL4; nd_post). pose proof TL1 as TL1u. pose proof TL4 as TL4u. unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in TL1u, TL4u.   (* [comment removed for export] *)
  (pose proof (alayout_ctx L ALO) as ndP__; nd_pre ndP__ 5%nat; intros CL1 CL2 CL3 CL4 CL5; nd_post).
  (pose proof (alayout_stack L ALO) as ndP__; nd_pre ndP__ 3%nat; intros STK1 STK2 STK3; nd_post).
  pose proof (ao_t L ALO) as OT. pose proof (ao_res L ALO) as ORS. pose proof (ao_fake L ALO) as OFK. pose proof (ao_dtls L ALO) as ODT.
  unfold aobj in OT, ORS, OFK, ODT. pose proof (ao_space L ALO) as RSP. pose proof (ao_res_hi L ALO) as RHI. unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in OT, ORS, OFK, ODT.   (* [comment removed for export] *)
  pose proof (ad_t_res L ALO) as D_t_res. pose proof (ad_t_fake L ALO) as D_t_f. pose proof (ad_t_dtls L ALO) as D_t_d.
  unfold adisj in D_t_res, D_t_f, D_t_d.
  (* [comment removed for export] *)
  pose proof RT as RT0.
  (nd_pre RT0 28%nat; intros GPG GOT GOT80 RIC LS1 REAL IMAX4 FLG5 FLG HPP SHB CANP TI TK INI2 LAY MCS OOM3 PGC HK2 CF8 CF34 CSMT T88 TSD LS2 CT8 CT; nd_post).
  pose proof INI2 as INI. rw_split INI 1%nat INI1 INIx. clear INIx.
  pose proof OOM3 as OOM. rw_split OOM 2%nat OOMx RSS0. clear OOMx.
  pose proof IMAX4 as IMAX. rw_split IMAX 3%nat IMAX3 IMAXx. clear IMAXx.
  (nd_pre THR 6%nat; intros T0 T40 CACHES CSTATS [sj [STATS LSJ]] UNW; nd_post).
  pose proof AQ as AQ0. (nd_pre AQ0 6%nat; intros _ _ _ (FL & IAS & IAM) CP _; nd_post).
  unfold AIA_FLAG, AIA_BASE, AIA_SIZE, AIA_MAP1, AIA_MAP1_LEN in FL, IAS, IAM.
  (* [comment removed for export] *)
  unfold AIMG_HI, AFREE_STACK, UDEPTH in *.
  box CL5.
  pose proof T0 as TT0. rw_split TT0 1%nat TTctx TT.
  eapply evtF_mono.
  { eapply (realloc_pre_spec L (q_ia Q) RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m
              A n (al_t L) lo (al_top L) (al_bot L) tr trc sj).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => first [exact ST | exact IAS]
         | |- mem_inv _ _ => exact MI
         | |- allocA_cells _ _ _ => unfold allocA_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
         | |- (_ /\ _) \/ (_ /\ _) => exact ARM
         | |- u64arr _ _ _ _ => exact STATS
         | |- _ = true -> _ => exact IAM
         end.
    all: try lazymatch goal with
         | |- rw_cells _ _ (al_t _) [C8 _] => exact TTctx
         | |- rw_cells _ _ (al_t _ + 8) _ => exact TT
         | |- rw_cells _ _ _ _ => assumption
         | |- @eq word _ _ => first [exact TP | exact Ha0 | exact Ha1 | reflexivity]
         | |- _ \/ _ => first [unboxed CL5 | pose proof CL5 as Y; unbox Y; lia]
         | |- rng _ _ _ => first [assumption | eapply rng_sub; [exact RCTX| lia| lia] | solve_rng]
         end.
    all: try assumption.
    all: unfold AIMG_HI, UDEPTH in *.
    all: try (generalize LO LO8 BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 RA4 APOS NR LSJ LTRC; clear; intros; unfold AFREE_STACK in *; lia).
    all: match goal with |- ?G => idtac "REMF" G end. }
  cbv beta. intros ms' PM. pose proof PM as PM0. unfold realloc_pre_post in PM.
  (nd_pre PM 15%nat; intros t0' t1' t2' a7' t3' t4' t5' t6' fr0 junk0 junk2 tb sj' m' ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 18%nat; intros MU0 WM MI' ST' FR48 FR16 FRP SS TB LTB TRF FRS UNW' STATS' LSJ' FL' IAS' IAM'; nd_post).
  assert (MU : munch (Wrpre (bv_unsigned sp) (al_t L)) m m').
  { eapply munch_weaken; [| exact MU0]. unfold Wrpre, sub_fp. cbn [outside]. intros q Hq. clear -Hq. lia. }
  assert (IA' : aintal true m').
  { unfold aintal, AIA_FLAG, AIA_BASE, AIA_SIZE, AIA_MAP1, AIA_MAP1_LEN. split; [exact FL'|]. split; [exact IAS'|]. intros _. exact IAM'. }
  destruct (AREP_rpre L st X Q m m' (bv_unsigned sp) ALO AR AQ MU WM ltac:(atop_facts; clear -LO BOT STK3; unfold AFREE_STACK in *; lia) UNW' IA'
              ltac:(exists sj'; split; [exact STATS'| exact LSJ'])) as [AR' AQ'].
  split; [exact PM0|]. cbn [ms_mem].
  apply and_comm. split.
  (* [comment removed for export] *)
  { (* [comment removed for export] *)
    intros a Ha CLA. split; [| intros Hw; apply WM; exact Hw]. apply MU. rewrite wa_unsigned by exact Ha.
    word_range sp SPR.
    unfold Wrpre. cbn [outside].
    destruct CLA as [CLA|TL].
    2:{ (* [comment removed for export] *)
        pose proof (ad_tls_t L ALO) as DLT. unfold adisj in DLT. pose proof atp_lin as TLN. pose proof atop_range as ATR0. pose proof atp_below_atop as TBA.
        destruct TL as [[T|(ta & Hta & ->)]|[IM|IM]].
        4:{ pose proof (ao_ahm L ALO) as OAH. pose proof (aobj_img _ _ OAH ltac:(clear; lia)) as OAHI. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OAH, OAHI.
          rewrite <- (ao_ahm_eq L ALO) in IM. unfold AAHM_SZ in IM. pose proof (ad_ahm_t L ALO) as DA1. unfold adisj in DA1.
            clear -IM OAH OAHI DA1 Ha LO BOT STK3 ATR0. lia. }
        - clear -T Ha DLT TLN ATR0 TBA LO BOT STK3. lia.
        - pose proof (tls_shadow_band ta Hta) as (TS1 & TS2).
          assert (SA : shad ATOP <= 17594332446720) by (rewrite shad_div; unfold ASHOFF; clear -ATR0; Z.div_mod_to_equations; lia).
          clear -TS1 TS2 SA Ha TL1u LO BOT STK3 ATR0. lia.
        - unfold AIMSH_LO, AIMSH_LEN in IM. clear -IM Ha TL1u LO BOT STK3 ATR0. lia. }
    destruct CLA as [SK | [CIa | [BLK | SH]]].
    - clear -SK Ha LO BOT STK3 TL2. lia.
    - (nd_pre CIa 3%nat; intros iv Hiv R; nd_post). (pose proof (proj1 (Forall_forall _ _) CI_OK iv Hiv) as ndP__; nd_pre ndP__ 6%nat; intros Q1 Q2 Q3 Q4 Q5 Q6; nd_post). cbn [fst snd] in *.
      unfold AIMG_HI in *. clear -R Q1 Q3 Q5 Q6 LO BOT STK3 TL4u. lia.
    - (nd_pre BLK 3%nat; intros [[q|cls] A' n'] Hin R; nd_post); cbn [ab_addr ab_size] in R.
      + destruct (proj1 BL q A' n' Hin) as [(b & Hb & Sb & Ub & Nb)|(mb & msz & Lp & EUA & Gs)].
        * destruct (BUSY b Hb) as [CLB _].
          (nd_pre (PERC (xb_class b) CLB) 12%nat; intros P1 P2 _ _ _ _ _ _ _ _ _ PR; nd_post).
          pose proof (size_of_class_facts (xb_class b) CLB) as [QS _].
          assert (KB : 0 <= xb_slot b < ndist st (xb_class b)).
          { apply PR. apply in_app_iff. right. apply in_app_iff. right. unfold busy_slots. apply in_map_iff. exists b. split; [reflexivity|].
            apply filter_In. split; [exact Hb| apply Z.eqb_refl]. }
          (pose proof (slot_in_region L st (xb_class b) (xb_slot b) ltac:(clear -QS; lia) (proj1 P1) KB) as ndP__; nd_pre ndP__ 3%nat; intros P5 P4 P0; nd_post).
          pose proof (awf_fits L st X b WF Hb) as FIT. unfold xb_fits in FIT. rewrite Sb in FIT.
          subst A' n'. unfold xb_user, xb_alloc, aregion, K_REGION, K_FREEARR_OFF, K_NUM_CLASSES in *.
          clear -R P5 P4 P1 P2 CLB RSP FIT ORS D_t_res LO BOT STK3. lia.
        * (* [comment removed for export] *)
          cbn [sec_wf1] in Gs. (nd_pre Gs 7%nat; intros Gs1 Gs2 Gs3 Gs4 Gs5 Gs6 (Ct & Cc & Cr & Cp & Cn & Cs & Cf & Cd); nd_post).
          pose proof (sec_facts n' ltac:(clear -Gs5; lia) Gs6) as SF. subst A'. unfold SEC_UOFF, K_HIGH_MEM in *.
          unfold ablk, KLS, AIMG_HI in Gs2.   (* [comment removed for export] *)
          clear -R Gs2 Gs3 Gs4 Gs5 SF Ct LO BOT STK3. lia.
      + (nd_pre (proj1 (proj2 BL) cls A' n' Hin) 3%nat; intros K1 K2 K3; nd_post).
        clear -R K1 K2 K3 OFK D_t_f LO BOT STK3. lia.
    - (nd_pre SH 3%nat; intros a' Ha' ndR1__; nd_post; revert ndR1__; intros ->). rewrite shad_div in Ha |- *. unfold ASHOFF in *.
      assert (A47 : 0 <= a' < 2^47).
      { destruct Ha' as [SK | [CIa | FK]].
        - atop_facts. clear -SK SPR. lia.
        - (nd_pre CIa 3%nat; intros iv Hiv R; nd_post). (pose proof (proj1 (Forall_forall _ _) CI_OK iv Hiv) as ndP__; nd_pre ndP__ 4%nat; intros Q1 Q2 Q3 _; nd_post). cbn [fst snd] in *.
          unfold AIMG_HI in *. clear -R Q1 Q3. lia.
        - (nd_pre FK 5%nat; intros cls FA sz Hin R; nd_post). (nd_pre (proj1 (proj2 BL) cls FA sz Hin) 3%nat; intros K1 K2 K3; nd_post). clear -R K1 K3 OFK. lia. }
      clear -A47 LO BOT STK3 TL1u. Z.div_mod_to_equations. lia. }
  split; [exact ALO|]. split; [exact ARNG|]. split; [exists X; split; [exact AR'| exact BL]|].
  (* [comment removed for export] *)
  cbn [ah_fake AHQ].
  assert (SF : 2148239360 <= shad (al_fake L) /\ shad (al_fake L) + shlen 11571200 <= 17594332446720).   (* [comment removed for export] *)
  { rewrite shad_div, shlen_div. unfold ASHOFF in *. pose proof atop_range as AR8. clear -OFK AR8. Z.div_mod_to_equations. lia. }
  eapply (hf_frame _ HL L LB m m'); [exact HFK | exact MU | exact WM |].
  unfold fake_untouched, Wrpre.
  pose proof (ad_tls_t L ALO) as D_l_t. unfold adisj in D_l_t. pose proof atp_lin as TLN. pose proof atop_range as ATR0.      (* [comment removed for export] *)
  repeat (apply Forall_cons; [cbn [fst snd]; clear -OFK ODT OT SF D_t_f D_t_d LO BOT STK3 D_l_t TLN ATR0; lia_relc|]). apply Forall_nil.
Qed.
End Zd2.
#[using="HL CI_OK"] Theorem arealloc_preP : ltac:(let t := eval cbv delta [arealloc_preP__stmt] in arealloc_preP__stmt in exact t).
Proof. exact arealloc_preP__body. Qed.
End S.
End CANSEC1.
End TwB.
End ARealloc_preP.

(* [comment removed for export] *)
Module AFreeMid.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Import InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecFacts AImg AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AQConst AMalloc_iface. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitR__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepStore__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeRead F_afree_tail. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_front__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_tailR__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_arep__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_tabscan__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASF_fast__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepStore__A3W.ARepStore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AFreeModel OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.AFreeGeo OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRead OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tail OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_afree_icpt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tailR__A3W.F_afree_icptR OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.F_afree_arep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_tabscan__A3W.AFreeStoreK OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.AFreeStore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_fast__A3W.F_afree_arepR.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac sg_set := let GG := fresh "GG" in (match goal with |- ?G => set (GG := G) end).
Local Ltac sg_unset := match goal with |- ?G => is_var G; subst G end.
Local Ltac sg_destr := sg_set; repeat match goal with H : _ /\ _ |- _ => destruct H end; sg_unset.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Notation WfM sp t UB gq nodes store :=
  ([(sp - 4096, sp); (0xaf800, 0x130830); (0x13e088, 0x13e08c); (ADEPOT_LO, ADEPOT_HI);
    (t + 2800, t + 3169); (UB - 16, UB + 8); (shad UB, shad UB + gq);
    (nodes, nodes + 1048576); (store, store + 8388608)]%Z) (only parsing).

(* [comment removed for export] *)
Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6303744 * k <= a.
Proof. intros a n H G2. unfold iclr, AIMG_LO, AIMG_HI in H. destruct H as [? [?|?]]; [exists 0 | exists 1]; lia. Qed.
Local Lemma ablk_int {rc : runConstT} {tlsI : ABase.atlsT} : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6303744 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
Local Ltac band_int H :=
  let k := fresh "k" H in let A := fresh "KA" H in let B := fresh "KB" H in let C := fresh "KC" H in let D := fresh "KD" H in
  let G1 := fresh "G" in let G2 := fresh "G" in
  lazymatch type of H with
  | sclr ?a ?n =>
      assert (G1 : 0 <= a) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia); assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      (nd_pre (sclr_int a n H G1 G2) 4%nat; intros k A B C; nd_post); clear G1 G2
  | iclr ?a ?n =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      (nd_pre (iclr_int a n H G2) 5%nat; intros k A B C D; nd_post); clear G2
  | 4096 <= ?a /\ (?a + ?n <= _ \/ _ <= ?a) =>      (* [comment removed for export] *)
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      (nd_pre (iclr_int a n H G2) 5%nat; intros k A B C D; nd_post); clear G2
  | ablk ?lo ?hi => let E := fresh "KE" H in destruct (ablk_int lo hi H) as (k & A & B & E & C & D)
  end.

(* [comment removed for export] *)
Ltac fu_drop_fake := repeat match goal with H : context [al_fake _] |- _ => clear H end.
Ltac fu_drop_dtls := repeat match goal with H : context [al_dtls _] |- _ => clear H end.
Ltac fu_drop_tls := repeat match goal with H : context [ATPv] |- _ => clear H | H : context [kt_img] |- _ => clear H end.
Ltac fu_focus :=
  lazymatch goal with
  | |- context [al_fake _] => fu_drop_dtls; fu_drop_tls
  | |- context [al_dtls _] => fu_drop_fake; fu_drop_tls
  | |- context [ATPv] => fu_drop_fake; fu_drop_dtls
  | |- _ => fu_drop_fake; fu_drop_dtls; fu_drop_tls
  end.
Ltac fu_lia := first [solve [fu_focus; lia] | lia].
(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
(* [comment removed for export] *)
#[using="Type"] Local Lemma aobj_int : forall a n, aobj a n -> 0x10000 <= n ->
  6303744 <= a /\ a + n <= ATOP /\ exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof.
  intros a n H Hn. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. (nd_pre H 5%nat; intros H1 H2 H3 H4 H5; nd_post).
  split; [lia|]. split; [lia|]. destruct H4; [exists 0 | exists 1]; lia.
Qed.
#[using="Type"] Local Lemma aobj4_int : forall a, aobj a 4096 ->
  4096 <= a /\ a + 4096 <= ATOP
  /\ (exists k, 0 <= k <= 1 /\ a + 4096 <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a)
  /\ (exists j, 0 <= j <= 1 /\ a + 4096 <= 65536 + j * 18446744073709551616 /\ 6303744 * j <= a).
Proof.
  intros a H. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. (nd_pre H 5%nat; intros H1 H2 H3 H4 H5; nd_post).
  split; [lia|]. split; [lia|]. split; [destruct H4; [exists 0 | exists 1]; lia | destruct H5 as [_ [H5|H5]]; [exists 0 | exists 1]; lia].
Qed.

Section KindsM.
Variables (sp t AB S UB gq nodes store res ctx lo grz ssz : Z).
Definition kfactsM : Prop :=
     (ATOP <= lo /\ lo <= sp - 4096)
  /\ (sclr t 4096 /\ iclr t 4096 /\ 4096 <= t /\ t + 4096 <= ATOP)      (* [comment removed for export] *)
  /\ (17594333495296 <= res /\ res + 137439023104 <= ATOP)      (* [comment removed for export] *)
  /\ (res + 4096 <= AB /\ AB + S <= res + 137439023104 /\ AB + 16 <= UB /\ UB + 8 <= AB + S)
  /\ (2201439137792 <= shad AB /\ shad UB = shad AB + grz /\ 2 <= grz /\ 1 <= gq /\ shad UB + gq <= shad AB + ssz
      /\ shad AB + ssz <= 17594333495296)
  /\ (sclr nodes 1048576 /\ 6303744 <= nodes /\ nodes + 1048576 <= ATOP /\ sclr store 8388608 /\ 6303744 <= store /\ store + 8388608 <= ATOP)   (* [comment removed for export] *)
  /\ (sclr ctx 65536 /\ 6303744 <= ctx /\ ctx + 65536 <= ATOP).   (* [comment removed for export] *)
Hypothesis KF : kfactsM.

(* [comment removed for export] *)
Ltac kbase L := lazymatch L with Z.add ?X _ => kbase X | Z.sub ?X _ => kbase X | Z.mul _ ?X => kbase X | _ => L end.
Ltac kalias X := lazymatch X with UB => constr:(res) | AB => constr:(res) | _ => X end.
Ltac kkeep2 X Y := repeat match goal with H : _ \/ _ |- _ => lazymatch type of H with context [X] => fail | context [Y] => fail | _ => clear H end end.
Ltac klia := Zify.zify; xlia zchecker.
Ltac kind1 := lazymatch goal with
  | |- (_ <= ?L \/ _)%Z => let X := kbase L in let Y := kalias X in first [ solve [ kkeep2 X Y; klia ] | lia ]
  | |- _ => lia end.
Ltac kind := pose proof KF as KF'; unfold kfactsM, AIMG_HI in *;
  sg_set; (nd_pre KF' 7%nat; intros F_lo sgk1 F_res F_slot F_sh sgk2 sgk3; nd_post); (nd_pre sgk1 4%nat; intros Ft1 Ft2 Ft3 Ft4; nd_post); (nd_pre sgk2 6%nat; intros Fn1 Fn2 Fn3 Fs1 Fs2 Fs3; nd_post); (nd_pre sgk3 3%nat; intros Fc1 Fc2 Fc3; nd_post);
  band_int Ft1; band_int Ft2; band_int Fn1; band_int Fs1; band_int Fc1; clear Ft1 Ft2 Fn1 Fs1 Fc1;   (* [comment removed for export] *)
  sg_unset; cbn [disjoint_from]; repeat (split; [kind1|]); first [kind1 | exact I].

#[using="rc AB S res ctx lo grz ssz KF"] Lemma KM_img : forall A k, 0x10000 <= A -> 0 <= k ->
  (A + k <= ADEPOT_LO /\ (A + k <= 0xaf800 \/ 0x130830 <= A) /\ (A + k <= 0x13e088 \/ 0x13e08c <= A))
  \/ (ADEPOT_HI <= A /\ A + k <= AIMG_HI) ->
  disjoint_from (WfM sp t UB gq nodes store) A k.
Proof. intros. kind. Qed.
#[using="rc AB S res ctx lo grz ssz KF"] Lemma KM_low : forall A k, 2147450880 <= A -> A + k <= 2148238848 -> 0 <= k ->      (* [comment removed for export] *)
  disjoint_from (WfM sp t UB gq nodes store) A k.
Proof. intros. kind. Qed.
#[using="rc AB S res ctx lo grz ssz KF"] Lemma KM_hi : forall A k, sp <= A -> 0 <= k -> disjoint_from (WfM sp t UB gq nodes store) A k.
Proof. intros. kind. Qed.
#[using="rc AB S res ctx lo grz ssz KF"] Lemma KM_shad : forall A k, 2147446784 <= A -> A + k <= 17594333495296 -> 0 <= k ->      (* [comment removed for export] *)
  (A + k <= shad UB \/ shad UB + gq <= A) -> disjoint_from (WfM sp t UB gq nodes store) A k.
Proof. intros. kind. Qed.
#[using="rc AB S lo grz ssz KF"] Lemma KM_ctx :
  (ctx + 65536 <= t \/ t + 4096 <= ctx) -> (ctx + 65536 <= res \/ res + 137439023104 <= ctx) ->
  (ctx + 65536 <= nodes \/ nodes + 1048576 <= ctx) -> (ctx + 65536 <= store \/ store + 8388608 <= ctx) ->
  forall A k, ctx <= A -> A + k <= ctx + 65536 -> 0 <= k -> disjoint_from (WfM sp t UB gq nodes store) A k.
Proof. intros. kind. Qed.
#[using="rc AB S ctx lo grz ssz KF"] Lemma KM_t :
  (t + 4096 <= res \/ res + 137439023104 <= t) -> (t + 4096 <= nodes \/ nodes + 1048576 <= t) -> (t + 4096 <= store \/ store + 8388608 <= t) ->
  forall A k, t <= A -> A + k <= t + 4096 -> 0 <= k -> (A + k <= t + 2800 \/ t + 3169 <= A) ->
  disjoint_from (WfM sp t UB gq nodes store) A k.
Proof. intros. kind. Qed.
#[using="rc AB S ctx lo grz ssz KF"] Lemma KM_res :
  (t + 4096 <= res \/ res + 137439023104 <= t) -> (nodes + 1048576 <= res \/ res + 137439023104 <= nodes) ->
  (store + 8388608 <= res \/ res + 137439023104 <= store) ->
  forall A k, res <= A -> A + k <= res + 137439023104 -> 0 <= k -> (A + k <= UB - 16 \/ UB + 8 <= A) ->
  disjoint_from (WfM sp t UB gq nodes store) A k.
Proof. intros. kind. Qed.
#[using="AB S ctx lo grz ssz KF"] Lemma KM_obj : forall A k, ((6303744 <= A /\ A + k <= 2147446784) \/ 17594333495296 <= A) -> A + k <= ATOP -> 0 <= k ->      (* [comment removed for export] *)
  (A + k <= t \/ t + 4096 <= A) -> (A + k <= res \/ res + 137439023104 <= A) ->
  (A + k <= nodes \/ nodes + 1048576 <= A) -> (A + k <= store \/ store + 8388608 <= A) ->
  disjoint_from (WfM sp t UB gq nodes store) A k.
Proof. intros. kind. Qed.
(* [comment removed for export] *)
#[using="AB S ctx lo grz ssz KF"] Lemma KM_objL : forall A k, ((A + k <= 65536 \/ 6303744 <= A) /\ (A + k <= 2147446784 \/ 17594333495296 <= A)) -> A + k <= ATOP -> 0 <= k ->      
  (A + k <= t \/ t + 4096 <= A) -> (A + k <= res \/ res + 137439023104 <= A) ->
  (A + k <= nodes \/ nodes + 1048576 <= A) -> (A + k <= store \/ store + 8388608 <= A) ->
  disjoint_from (WfM sp t UB gq nodes store) A k.
Proof. intros. kind. Qed.
End KindsM.

(* [comment removed for export] *)
#[using="Type"] Lemma aheap_pres_mid : forall (CI : list (Z * Z)) sp t AB S UB gq nodes store res ctx lo grz ssz (LB : list ablock) m m',
  kfactsM sp t AB S UB gq nodes store res ctx lo grz ssz ->
  Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI
                 /\ (snd iv <= 0xab270 \/ 0xab330 <= fst iv)
                 /\ (snd iv <= 0xaf800 \/ 0x130830 <= fst iv)
                 /\ (snd iv <= 0x13e088 \/ 0x13e08c <= fst iv)) CI ->
  munch (WfM sp t UB gq nodes store) m m' -> wmono asegs m m' ->
  (forall b, In b LB -> disjoint_from (WfM sp t UB gq nodes store) (ab_addr b) (ab_size b)) ->
  (forall cls FA sz, In (mkABlock (ABFake cls) FA sz) LB -> forall a', FA <= a' < FA + sz ->
       disjoint_from (WfM sp t UB gq nodes store) (shad a') 1) ->
  shad UB + gq <= shad ATOP ->
  (forall A k, ATPv + -200 <= A -> A + k <= ATPv + 312 -> 0 <= k -> disjoint_from (WfM sp t UB gq nodes store) A k) ->      (* [comment removed for export] *)
  (forall a', ATPv + -200 <= a' < ATPv + 312 -> disjoint_from (WfM sp t UB gq nodes store) (shad a') 1) ->                  (* [comment removed for export] *)
  disjoint_from (WfM sp t UB gq nodes store) AIMSH_LO AIMSH_LEN ->                                                          (* [comment removed for export] *)
  disjoint_from (WfM sp t UB gq nodes store) AAHMv AAHM_SZ ->                                                          (* [comment removed for export] *)
  aheap_pres CI LB sp m m'.
Proof.
  intros CI sp t AB S UB gq nodes store res ctx lo grz ssz LB m m' KF CIOK MU WM HBK HFK PSP TLSK TLSS IMSH AHMK a Ha CL.
  split; [| intros Hw; apply WM; exact Hw].
  apply MU. rewrite wa_unsigned by exact Ha.
  destruct CL as [CL|TL]; [| exact (aextra_outside _ a TLSK TLSS IMSH AHMK TL)].
  pose proof KF as KF'. (nd_pre KF' 7%nat; intros F_lo F_t F_res F_slot F_sh F_ns F_ctx; nd_post).
  destruct CL as [ST | [CIa | [BLK | SH]]].
  - eapply disjoint_outside; [eapply (KM_hi _ _ _ _ _ _ _ _ _ _ _ _ _ KF a 1); lia | lia].
  - (nd_pre CIa 3%nat; intros iv Hiv R; nd_post). (pose proof (proj1 (Forall_forall _ _) CIOK iv Hiv) as ndP__; nd_pre ndP__ 6%nat; intros Q1 Q2 Q3 Q4 Q5 Q6; nd_post). cbn [fst snd] in *.
    eapply disjoint_outside; [eapply (KM_img _ _ _ _ _ _ _ _ _ _ _ _ _ KF a 1); unfold AIMG_HI in *; lia | lia].
  - (nd_pre BLK 3%nat; intros b Hb R; nd_post). eapply disjoint_outside; [exact (HBK b Hb) | lia].
  - (nd_pre SH 3%nat; intros a' Ha' ndR1__; nd_post; revert ndR1__; intros ->).
    pose proof (shad_div a') as SD. pose proof (shad_div ATOP) as SDs. unfold ASHOFF in *.
    destruct Ha' as [ST | [CIa | FK]].
    + eapply disjoint_outside; [eapply (KM_shad _ _ _ _ _ _ _ _ _ _ _ _ _ KF (shad a') 1) | lia].
      all: atop_facts; clear -ST SD SDs F_sh F_lo PSP; Z.div_mod_to_equations; lia.
    + (nd_pre CIa 3%nat; intros iv Hiv R; nd_post). (pose proof (proj1 (Forall_forall _ _) CIOK iv Hiv) as ndP__; nd_pre ndP__ 4%nat; intros Q1 Q2 Q3 _; nd_post). cbn [fst snd] in *.
      eapply disjoint_outside; [eapply (KM_low _ _ _ _ _ _ _ _ _ _ _ _ _ KF (shad a') 1) | lia].
      all: unfold AIMG_HI in *; clear -R SD Q1 Q3; Z.div_mod_to_equations; lia.
    + (nd_pre FK 5%nat; intros cls FA sz Hin R; nd_post). eapply disjoint_outside; [exact (HFK cls FA sz Hin a' R) | lia].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma qcoupled_pend : forall L s s' X X' Q c k n b1 ctx,
  qcoupled L s X Q -> a_qloc s' = a_qloc s -> a_qglob s' = a_qglob s ->
  (forall y, In y (x_busy X') /\ xb_st y = BQuar <-> (In y (x_busy X) /\ xb_st y = BQuar) \/ y = mkXBusy c k n BQuar b1 ctx) ->
  (forall y, In y (x_busy X') /\ xb_st y = BBatch <-> (In y (x_busy X) /\ xb_st y = BBatch) \/ In y []) ->
  (forall y, In y (x_busy X) -> xb_st y = BQuar -> xb_class y = c -> xb_slot y = k -> False) ->
  qcoupled L s' X' (mkQConc (q_loc Q) (q_glob Q) true ((c, k) :: q_pend Q)).
Proof.
  intros L s s' X X' Q c k n b1 ctx (LN1 & LN2 & OK & ND1 & ND2 & BS & PS & NN) QL QG HQ HB FQ.
  unfold qcoupled. cbn [q_loc q_glob q_pend]. rewrite QL, QG.
  set (es := qentries (a_qloc s) (q_loc Q) ++ qentries (a_qglob s) (q_glob Q)) in *.
  assert (PM : Permutation (qprim_ids es ++ (c, k) :: q_pend Q) ((c, k) :: (qprim_ids es ++ q_pend Q))) by (apply Permutation_sym; apply Permutation_middle).
  split; [exact LN1|]. split; [exact LN2|]. split.
  { eapply Forall_impl; [| exact OK]. intros [ch k'] HOK. unfold qentry_ok in *. cbn [fst snd] in *.
    destruct ch as [c' n'| mb ms n']; [| exact I]. (nd_pre HOK 3%nat; intros b1' ctx' Hin; nd_post). exists b1', ctx'.
    apply (proj1 (proj2 (HQ _) (or_introl (conj Hin eq_refl)))). }
  split.
  { eapply Permutation_NoDup'; [apply Permutation_sym; exact PM|]. constructor; [| exact ND1].
    intros Hin. apply (PS c k) in Hin. (nd_pre Hin 5%nat; intros y Hy Sy Cy Ky; nd_post). exact (FQ y Hy Sy Cy Ky). }
  split; [exact ND2|]. split.
  { intros k0. rewrite (BS k0). split; intros (y & Hy & Sy & Cy & Ky); exists y; (split; [| split; [exact Sy| split; [exact Cy| exact Ky]]]).
    - apply (proj1 (proj2 (HB y) (or_introl (conj Hy Sy)))).
    - destruct (proj1 (HB y) (conj Hy Sy)) as [[Hy0 _]|[]]. exact Hy0. }
  split; [| exact NN].
  intros c0 k0. split.
  - intros H. apply (Permutation_in _ PM) in H. destruct H as [E|H].
    + injection E as <- <-. exists (mkXBusy c k n BQuar b1 ctx). split; [apply (proj1 (proj2 (HQ _) (or_intror eq_refl)))|]. cbn. auto.
    + apply (PS c0 k0) in H. (nd_pre H 5%nat; intros y Hy Sy Cy Ky; nd_post). exists y. split; [apply (proj1 (proj2 (HQ y) (or_introl (conj Hy Sy))))|]. auto.
  - intros (y & Hy & Sy & Cy & Ky). eapply Permutation_in; [apply Permutation_sym; exact PM|].
    destruct (proj1 (HQ y) (conj Hy Sy)) as [[Hy0 _]| ->].
    + right. apply (PS c0 k0). exists y. auto.
    + left. cbn in Cy, Ky. subst. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section S.
Variable DI : ADepotIface.
Variables (ASEC : alayout -> astate -> aconc -> amem -> Prop) (AFK : alayout -> list ablock -> amem -> Prop).
Hypothesis HL : ahole_laws (AHQ DI ASEC AFK).
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI
                                  /\ (snd iv <= 0xab270 \/ 0xab330 <= fst iv)
                                  /\ (snd iv <= 0xaf800 \/ 0x130830 <= fst iv)
                                  /\ (snd iv <= 0x13e088 \/ 0x13e08c <= fst iv)) CI.

Definition mid_kit__stmt : Prop := mid_stmt DI ASEC AFK CI.
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'mid_kit__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'mid_kit__stmt 1).
Variable full : ltac2:(SecDietF.SzSecF.ty 'mid_kit__stmt 2).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'mid_kit__stmt 3).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'mid_kit__stmt 4).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'mid_kit__stmt 5).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'mid_kit__stmt 6).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'mid_kit__stmt 7).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'mid_kit__stmt 8).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'mid_kit__stmt 9).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'mid_kit__stmt 10).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'mid_kit__stmt 11).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'mid_kit__stmt 12).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'mid_kit__stmt 13).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'mid_kit__stmt 14).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'mid_kit__stmt 15).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'mid_kit__stmt 16).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'mid_kit__stmt 17).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'mid_kit__stmt 18).
Variable F : ltac2:(SecDietF.SzSecF.ty 'mid_kit__stmt 19).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'mid_kit__stmt 20).
Variable m : ltac2:(SecDietF.SzSecF.ty 'mid_kit__stmt 21).
Variable st : ltac2:(SecDietF.SzSecF.ty 'mid_kit__stmt 22).
Variable LB : ltac2:(SecDietF.SzSecF.ty 'mid_kit__stmt 23).
Variable X : ltac2:(SecDietF.SzSecF.ty 'mid_kit__stmt 24).
Variable Q : ltac2:(SecDietF.SzSecF.ty 'mid_kit__stmt 25).
Variable p : ltac2:(SecDietF.SzSecF.ty 'mid_kit__stmt 26).
Variable c : ltac2:(SecDietF.SzSecF.ty 'mid_kit__stmt 27).
Variable k : ltac2:(SecDietF.SzSecF.ty 'mid_kit__stmt 28).
Variable n : ltac2:(SecDietF.SzSecF.ty 'mid_kit__stmt 29).
Variable b1 : ltac2:(SecDietF.SzSecF.ty 'mid_kit__stmt 30).
Variable ctx : ltac2:(SecDietF.SzSecF.ty 'mid_kit__stmt 31).
Variable A : ltac2:(SecDietF.SzSecF.ty 'mid_kit__stmt 32).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'mid_kit__stmt 33).
Variable lst : ltac2:(SecDietF.SzSecF.ty 'mid_kit__stmt 34).
Variable nx : ltac2:(SecDietF.SzSecF.ty 'mid_kit__stmt 35).
Variable bsz : ltac2:(SecDietF.SzSecF.ty 'mid_kit__stmt 36).
Variable hs : ltac2:(SecDietF.SzSecF.ty 'mid_kit__stmt 37).
Variable tr : ltac2:(SecDietF.SzSecF.ty 'mid_kit__stmt 38).
Variable l1 : ltac2:(SecDietF.SzSecF.ty 'mid_kit__stmt 39).
Variable l2 : ltac2:(SecDietF.SzSecF.ty 'mid_kit__stmt 40).
Let st1 := set_live (delete p (a_live st)) st.
Let X1 := xquar X c k n b1 ctx l1 l2.
Let QM := mkQConc (q_loc Q) (q_glob Q) true ((c, k) :: q_pend Q).
Let S := size_of_class c.
Let AB := aslot_addr L c k.
Let UB := AB + rz_size n.
Let gq := shlen (rup n 8).
#[using="HL CI_OK st1 X1 QM S AB UB gq"] Lemma mid_kit__body : ltac:(let T := type of (fun (h : mid_kit__stmt) => h L RNG full ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st LB X Q p c k n b1 ctx A lo lst nx bsz hs tr l1 l2) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (full, (ra, (sp, (gp, (tp, (s0, (s1, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (F, (fc, (m, (st, (LB, (X, (Q, (p, (c, (k, (n, (b1, (ctx, (A, (lo, (lst, (nx, (bsz, (hs, (tr, (l1, l2))))))))))))))))))))))))))))))))))))))))) as _.
  unfold mid_stmt. 
  cbv zeta. intros ALO ARNG AR AQ BL HFK XB HIN N1 CEIL LO ms1 PM. unfold AFREE_STACK in LO.
  chg (set_live (delete p (a_live st)) st) st1.
  chg (xquar X c k n b1 ctx l1 l2) X1.
  chg (mkQConc (q_loc Q) (q_glob Q) true ((c, k) :: q_pend Q)) QM.
  (* [comment removed for export] *)
  pose proof AR as AR0. (nd_pre AR0 12%nat; intros WF RT INST THR CLS HQ HS HD HRO HRT2 AVL RT3; nd_post).
  cbn [ah_quar ah_sec ah_depot AHQ] in HQ, HS, HD.
  (nd_pre THR 6%nat; intros T0 T40 CACHES CSTATS STATS0 UNW; nd_post).
  destruct (freed_range L st X p c k n b1 ctx l1 l2 WF XB) as [HC KR].
  (pose proof (freed_live L st X p c k n b1 ctx l1 l2 XB WF) as ndP__; nd_pre ndP__ 6%nat; intros LIVE N0 FIT0 B10 AT0 CTX0; nd_post).
  (pose proof (chunk_geo L st X c k n ALO WF HC KR (proj1 N0) FIT0) as ndP__; nd_pre ndP__ 14%nat; intros HM16 UB16 ABUB ABHM HLO UBS ABCE HHI N65 NQM ABLO RUP RUP8 S8; nd_post).
  (pose proof (slot_geo L st X c k ALO WF HC KR) as ndP__; nd_pre ndP__ 13%nat; intros S16 SM16 AL16 G1 G2 G3 G4 G5 G6 G7 G8 R8 M8; nd_post).
  (pose proof (slot_sep_objects L st X c k ALO WF HC KR) as ndP__; nd_pre ndP__ 5%nat; intros DT DC DN DSO DF; nd_post).
  (pose proof (chunk_shadow_geo L st X c k n ALO WF HC KR (proj1 N0) FIT0) as ndP__; nd_pre ndP__ 9%nat; intros SE GR3 GE G0 GFS SHLO SHHI SHM1 SHM2; nd_post).
  pose proof (rz_size_facts n (proj1 N0)) as [RZ1 RZ2].
  (pose proof (alayout_t L ALO) as ndP__; nd_pre ndP__ 4%nat; intros TL1 TL2 TL3 TL4; nd_post).
  (pose proof (alayout_ctx L ALO) as ndP__; nd_pre ndP__ 5%nat; intros CL1 CL2 CL3 CL4 CL5; nd_post).
  (pose proof (alayout_depot L ALO) as ndP__; nd_pre ndP__ 10%nat; intros DL1 DL2 DL3 DL4 DL5 DL6 DL7 DL8 DL9 DL10; nd_post).
  (pose proof (alayout_stack L ALO) as ndP__; nd_pre ndP__ 3%nat; intros STK1 STK2 STK3; nd_post).
  (pose proof (alayout_space L ALO) as ndP__; nd_pre ndP__ 4%nat; intros SP1 SP2 SP3 SP4; nd_post).
  pose proof (ao_res L ALO) as RES. pose proof (ao_t L ALO) as OT. pose proof (ao_ctx L ALO) as OC. pose proof (ao_nodes L ALO) as ON. pose proof (ao_store L ALO) as OS.
  (pose proof (aobj4_int _ OT) as ndP__; nd_pre ndP__ 4%nat; intros _ _ [kT TBND] [jT TIMG]; nd_post).   (* [comment removed for export] *)
  (pose proof (aobj_int _ _ OC ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros Ci _ [kC CBND]; nd_post). (pose proof (aobj_int _ _ ON ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros Ni _ [kN NBND]; nd_post).
  (pose proof (aobj_int _ _ OS ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros Si _ [kS SBND]; nd_post). pose proof (ao_res_hi L ALO) as RHI.
  unfold aobj in RES, OT, OC, ON, OS. pose proof (ao_space L ALO) as RSP.
  pose proof (ad_t_res L ALO) as D_t_res. pose proof (ad_nodes_res L ALO) as D_n_res. pose proof (ad_store_res L ALO) as D_s_res.
  pose proof (ad_ctx_res L ALO) as D_c_res. pose proof (ad_ctx_nodes L ALO) as D_c_n. pose proof (ad_ctx_store L ALO) as D_c_s.
  unfold adisj in D_t_res, D_n_res, D_s_res, D_c_res, D_c_n, D_c_s.
  assert (D_c_t : al_ctx L + 65536 <= al_t L \/ al_t L + 4096 <= al_ctx L) by (pose proof (ad_t_ctx L ALO) as X0; unfold adisj in X0; clear -X0; lia).
  box DL7. box DL8. box DL9. box DL10. box D_t_res. box D_n_res. box D_s_res. box D_c_res. box D_c_n. box D_c_s. box D_c_t. box CL5.
  box DT. box DC. box DN. box DSO. box DF.
  word_range sp SPR.
  chg (size_of_class c) S. chg (aslot_addr L c k) AB. chg (AB + rz_size n) UB.
  assert (EAB : AB = aslot_addr L c k) by reflexivity. assert (EUB : UB = AB + rz_size n) by reflexivity. assert (ES : S = size_of_class c) by reflexivity.
  assert (EHM : fhm L c k n = UB - 16) by (unfold fhm; subst AB UB; clear; lia).
  assert (UB16' : UB mod 8 = 0) by (clear -UB16; Z.div_mod_to_equations; lia).
  (* [comment removed for export] *)
  (nd_pre (read_chunk L st X m p c k n b1 ctx l1 l2 ALO WF XB (conj (proj1 (proj2 (proj2 (CLS c HC)))) (proj2 (proj2 (proj2 (CLS c HC)))))) 7%nat; intros _ _ UJR LH SHA _ SHR; nd_post).
  fold AB in UJR, LH, SHA, SHR. fold UB in UJR, LH, SHR. fold S in UJR, SHR.
  (* [comment removed for export] *)
  pose proof AQ as AQ0. (nd_pre AQ0 6%nat; intros [QK MX] [QC ABL] [GCQ ABG] (FL & IAS & IAM) CP NUM; nd_post).
  pose proof CP as CP0. (nd_pre CP0 7%nat; intros LN1 LN2 _ _ ND2 BSI _; nd_post).
  (* [comment removed for export] *)
  unfold free_to_refill_post in PM. rewrite EHM in PM.
  (nd_pre PM 18%nat; intros id t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' m' sj' tb' junk2 j0 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 22%nat; intros MU WM MI' ST' IDR HDR' FC' SH' STATS' LSJ' UW' FL' IAS' IAM' SS' TB' LTB' FRS' FRP' FRE' LBS' DEP'; nd_post).
  cbn [ms_mem MS].
  replace (UB - 16 + 16) with UB in MU, FC', SH' by (clear; lia).
  chg (shlen (rup n 8)) gq. assert (EGQ : gq = shlen (rup n 8)) by reflexivity. clearbody gq.
  (* [comment removed for export] *)
  assert (MUn : munch (WfM (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L)) m m').
  { eapply munch_weaken; [| exact MU]. solve_sub_fp sp. }
  clear MU.
  assert (KF : kfactsM (bv_unsigned sp) (al_t L) AB S UB gq (al_nodes L) (al_store L) (al_res L) (al_ctx L) lo (shlen (rz_size n)) (shlen S)).
  { unfold kfactsM. unfold K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
    assert (GQ1 : 1 <= gq) by (rewrite EGQ, shlen_div; generalize RUP RUP8 N1; clear; intros; Z.div_mod_to_equations; lia).
    generalize CEIL LO OT OC ON OS RES RHI RSP G5 G6 ABUB UBS S8 RUP EUB SHLO SE GR3 GQ1 GFS GE SHHI. clear. intros.
    unfold iclr, AIMG_LO, AIMG_HI in *; sg_destr; repeat split; first [assumption | lia].   (* [comment removed for export] *) }
  pose proof (KM_img _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Kimg.
  pose proof (KM_low _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Klow.
  pose proof (KM_hi _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Khi.
  pose proof (KM_shad _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Kshad.
  pose proof (KM_ctx _ _ _ _ _ _ _ _ _ _ _ _ _ KF (unbxF D_c_t) (unbxF D_c_res) (unbxF D_c_n) (unbxF D_c_s)) as Kctx.
  pose proof (KM_t _ _ _ _ _ _ _ _ _ _ _ _ _ KF (unbxF D_t_res) (unbxF DL7) (unbxF DL8)) as Kt.
  pose proof (KM_res _ _ _ _ _ _ _ _ _ _ _ _ _ KF (unbxF D_t_res) (unbxF D_n_res) (unbxF D_s_res)) as Kres.
  pose proof (KM_obj _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Kobj.
  pose proof (KM_objL _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as KobjL.      (* [comment removed for export] *)
  pose proof (ad_tls_t L ALO) as D_l_t. pose proof (ad_tls_res L ALO) as D_l_r. pose proof (ad_tls_nodes L ALO) as D_l_n. pose proof (ad_tls_store L ALO) as D_l_s.
  unfold adisj in D_l_t, D_l_r, D_l_n, D_l_s. pose proof atp_lin as TLN. pose proof atop_range as ATR0.
  (* [comment removed for export] *)
  assert (NDS : forall c', ndist st1 c' = ndist st c') by (intros c'; reflexivity).
  assert (WF' : awf L st1 X1) by (apply (awf_xquar L st X p c k n b1 ctx l1 l2 XB WF); reflexivity).
  (* [comment removed for export] *)
  assert (RT' : arep_rt L m').
  { eapply arep_rt_frame; [exact MUn | exact WM | exact RT |]. unfold rt_hulls, ATP88, ATSD.
    (first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kctx; clear; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kctx; clear; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |])] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]). apply Forall_nil. }
  assert (INST' : ainstance L st1 m').
  { eapply ainstance_frame; [exact MUn | exact WM | exact INST | reflexivity | reflexivity | | |]; apply Kimg; clear; unfold AINSTANCE, AIMG_HI; lia. }
  assert (HRO' : arelro m') by (eapply arelro_frame; [exact MUn | exact HRO | apply Kimg; clear; unfold ARELRO_LO, ARELRO_HI, AIMG_HI; lia]).
  assert (HRT2' : arep_rt2 m') by (eapply arep_rt2_frame; [exact MUn | exact WM | exact HRT2 | | |]; apply Kimg; clear; unfold AIMG_HI; lia).
  assert (RT3' : arep_rt3 m') by (eapply arep_rt3_frame; [exact MUn | exact WM | exact RT3 |]; unfold rt3_hulls; repeat (apply Forall_cons; [cbn [fst snd]; apply Kimg; clear; unfold AIMG_HI; lia|]); apply Forall_nil).
  (* [comment removed for export] *)
  assert (THR' : athread L st1 X1 m').
  { unfold athread. split; [| split; [| split; [| split; [| split]]]].
    - eapply cells_frame; [exact T0 | exact MUn | exact WM |]. cbn [cells_size csize Nat.add]. apply Kt; clear; lia.
    - eapply cells_frame; [exact T40 | exact MUn | exact WM |]. cbn [cells_size csize Nat.add]. apply Kt; clear; lia.
    - intros c' Hc'. eapply acache_cells_frame; [exact MUn | exact WM | exact (CACHES c' Hc') | reflexivity | reflexivity | reflexivity |].
      unfold acache_addr. unfold K_NUM_CLASSES, K_BATCH_CLASS in *. apply Kt; clear -Hc'; lia.
    - eapply junk_frame; [exact CSTATS | exact MUn | exact WM | intros _; apply Kt; clear; lia].
    - exists sj'. split; [exact STATS' | exact LSJ'].
    - exact UW'. }
  idtac "CHECKPOINT-M1".
  (* [comment removed for export] *)
  assert (RC : forall c1 c2, c1 < c2 -> aregion L c1 + K_REGION <= aregion L c2) by (intros; apply regions_sep; assumption).
  assert (CLS' : forall c'', 1 <= c'' < K_NUM_CLASSES ->
      aregion_cells L st1 m' c'' /\ afreearray L st1 X1 m' c'' /\ aslots L st1 X1 m' c'' /\ aslot_shadow L st1 X1 m' c'').
  { intros c'' Hc''. (nd_pre (CLS c'' Hc'') 4%nat; intros REG FARR SLOTS SHADOW; nd_post).
    pose proof WF as WF0. (nd_pre WF0 7%nat; intros _ _ SAL _ _ PERC _; nd_post).
    (nd_pre (PERC c'' Hc'') 12%nat; intros Q1 Q2 Q3 Q4 Q5 Q6 Q7 QLENF QLENC QCNTB QND QRANGE; nd_post).
    pose proof (size_of_class_facts c'' Hc'') as [QS QS16].
    pose proof (aregion_mod L c'' SAL) as RM''.
    unfold K_NUM_CLASSES in Hc''.
    assert (RI : al_res L <= aregion L c'' /\ aregion L c'' + K_REGION <= al_space_beg L + K_SPACE_SIZE
                 /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104 /\ al_res L + 4096 <= aregion L c'').
    { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc'' RSP. lia. }
    (nd_pre RI 4%nat; intros RI1 RI2 RI3 RI4; nd_post).
    assert (PC0 : aregion L c <= AB /\ AB + S <= aregion L c + K_FREEARR_OFF /\ AB + S <= aregion L c + c_allocated_user (get_cls st c)) by (clear -G1 G2 G3 G4; lia).
    split; [| split; [| split]].
    - eapply aregion_cells_frame; [exact MUn | exact WM | exact REG | reflexivity | reflexivity | reflexivity | reflexivity |].
      unfold aregion_info, ARI_STRIDE, K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
      apply Kres; clear -Hc'' RSP G6 S8 EUB RES RHI; lia.
    - eapply afreearray_frame; [exact MUn | exact WM | exact FARR | reflexivity | reflexivity | reflexivity | exact QLENF | exact Q5 | | clear -Q6; lia |].
      + assert (FA1 : aregion L c'' + K_FREEARR_OFF <= afreearr L c'' /\ afreearr L c'' + c_mapped_free_array (get_cls st c'') <= aregion L c'' + K_REGION).
        { unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q6. lia. }
        destruct FA1 as [FA1 FA2].
        apply Kres; [clear -RI1 FA1; unfold K_FREEARR_OFF in *; lia | clear -RI2 RI3 FA2; lia | clear -Q5 Q6; lia |].
        pose proof (farr_vs_user L c'' c _ _ AB S (proj1 PC0) (proj1 (proj2 PC0)) FA1 FA2) as D. clear -D ABUB S8 EUB. lia.
      + assert (FA1 : aregion L c'' + K_FREEARR_OFF <= afreearr L c'' /\ afreearr L c'' + c_mapped_free_array (get_cls st c'') <= aregion L c'' + K_REGION).
        { unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q6. lia. }
        destruct FA1 as [FA1 FA2].
        apply Kshad.
        * rewrite shad_div. unfold ASHOFF, K_FREEARR_OFF in *. clear -RI1 FA1 RES RHI. Z.div_mod_to_equations. lia.
        * rewrite shad_div, shlen_div. unfold ASHOFF, K_SPACE_SIZE in *. clear -RI2 RI3 FA2 RES RHI. Z.div_mod_to_equations. lia.
        * apply shlen_nonneg. clear -Q5 Q6. lia.
        * pose proof (farr_vs_user L c'' c _ _ UB (rup n 8) ltac:(clear -PC0 ABUB; lia) ltac:(clear -PC0 UBS; lia) FA1 FA2) as D.
          assert (AM : afreearr L c'' mod 8 = 0) by (unfold afreearr, K_FREEARR_OFF; clear -RM''; Z.div_mod_to_equations; lia).
          rewrite EGQ. destruct D as [D|D]; [left; apply shad_sep; [exact D| exact AM] | right; apply shad_sep; [exact D| clear -UB16; Z.div_mod_to_equations; lia]].
    - (* [comment removed for export] *)
      eapply (aslots_update_gen L _ m m' MUn WM st st1 X X1 c''); [exact SLOTS | apply NDS | reflexivity | reflexivity | |].
      + intros k'' Hk''.
        (pose proof (slot_geo L st X c'' k'' ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) Hk'') as ndP__; nd_pre ndP__ 12%nat; intros T16 TM16 TAL P1 P2 P3 P4 P5 P6 P7 P8 _; nd_post).
        assert (D1 : (c'' = c /\ k'' = k) \/ (c'' <> c \/ k'' <> k)) by (clear; lia). destruct D1 as [[Ec Ek]|NE1].
        * (* [comment removed for export] *)
          subst c'' k''. right.
          subst X1. rewrite (busy_of_xquar L st X p c k n b1 ctx l1 l2 XB WF). rewrite !Z.eqb_refl. cbn [andb].
          unfold aslot_busy, bquar. cbn [xb_st xb_class xb_n xb_b1 xb_ctx xb_slot bstate_byte]. unfold xb_user, xb_hdr, xb_alloc. cbn [xb_class xb_slot xb_n].
          rewrite <- EAB. fold S. rewrite <- EUB.
          split; [| split].
          -- intros R16. pose proof (rz_gt16 n (proj1 N0) R16) as R32. destruct (LH R16) as [LC LJ]. split.
             ++ eapply cells_frame; [exact LC | exact MUn | exact WM |]. cbn [cells_size csize Nat.add].
                apply Kres; clear -G5 G6 RSP RES RHI S16 EUB R32 S8; unfold K_SPACE_SIZE in *; lia.
             ++ eapply junk_frame; [exact LJ | exact MUn | exact WM |]. intros Hp.
                apply Kres; clear -G5 G6 RSP RES RHI S16 EUB R32 S8 Hp; unfold K_SPACE_SIZE in *; lia.
          -- exists 3. split; [reflexivity|]. exact HDR'.
          -- replace (S - rz_size n) with (8 + (S - rz_size n - 8)) by (clear; lia).
             apply (junk_merge m' UB 8 (S - rz_size n - 8)); [| | clear; lia | clear -S8; lia].
             ++ pose proof (junk_of_cells m' _ _ FC') as J. cbn in J. exact J.
             ++ eapply junk_frame; [exact UJR | exact MUn | exact WM |]. intros Hp.
                apply Kres; clear -G5 G6 RSP RES RHI S16 EUB ABUB S8 Hp; unfold K_SPACE_SIZE in *; lia.
        * (* [comment removed for export] *)
          left.
          assert (T2 : (c =? c'') && (k =? k'') = false).
          { destruct (Z.eqb_spec c c'') as [E|]; [| reflexivity]. destruct (Z.eqb_spec k k'') as [E'|]; [| reflexivity]. exfalso. clear -NE1 E E'. lia. }
          split; [subst X1; rewrite (busy_of_xquar L st X p c k n b1 ctx l1 l2 XB WF), T2; reflexivity|]. split.
          -- assert (DW9 : aslot_addr L c'' k'' + size_of_class c'' <= AB \/ AB + S <= aslot_addr L c'' k'').
             { pose proof (slots_sep_any L st X c'' k'' c k ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) HC Hk'' KR NE1) as D.
               rewrite <- EAB, <- ES in D. exact D. }
             apply Kres; [clear -P5 RSP; lia | clear -P6 RSP; unfold K_SPACE_SIZE in *; lia | clear -T16; lia | clear -DW9 ABUB S8 EUB; lia].
          -- intros b Hb. (nd_pre (busy_of_Some_facts X c'' k'' b Hb) 3%nat; intros IB CB' KB'; nd_post). split; [exact CB'|]. split; [exact KB'|]. exact (awf_fits L st X b WF IB).
      + intros POS''.
        set (AU := aregion L c'' + c_allocated_user (get_cls st c'')) in *.
        assert (U0 : aregion L c'' <= AU /\ AU + (c_mapped_user (get_cls st c'') - c_allocated_user (get_cls st c'')) <= aregion L c'' + K_FREEARR_OFF) by (subst AU; clear -Q1 Q2; lia).
        destruct U0 as [U0 U0'].
        assert (U1 : c'' = c -> aregion L c + c_allocated_user (get_cls st c) <= AU) by (intros E; subst AU; rewrite <- E; clear; lia).
        apply Kres; [clear -RI4 Q1 U0; lia | subst AU; clear -Q1 Q2 RI2 RI3; unfold K_FREEARR_OFF, K_REGION, K_SPACE_SIZE in *; lia | clear -POS''; lia |].
        pose proof (undist_vs_user L c'' c _ _ AB S (c_allocated_user (get_cls st c)) (proj1 PC0) (proj2 (proj2 PC0)) ltac:(clear -G3 G4; lia) U1 U0 U0') as D.
        clear -D ABUB S8 EUB. lia.
    - (* [comment removed for export] *)
      eapply (aslot_shadow_update_gen L _ m m' MUn WM st st1 X X1 c''); [exact SHADOW | apply NDS | reflexivity | reflexivity | | | apply shlen_nonneg; clear -QS; lia].
      + intros k'' Hk''.
        (pose proof (slot_geo L st X c'' k'' ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) Hk'') as ndP__; nd_pre ndP__ 12%nat; intros T16 TM16 TAL P1 P2 P3 P4 P5 P6 P7 P8 _; nd_post).
        assert (D1 : (c'' = c /\ k'' = k) \/ (c'' <> c \/ k'' <> k)) by (clear; lia). destruct D1 as [[Ec Ek]|NE1].
        * (* [comment removed for export] *)
          subst c'' k''. right.
          subst X1. rewrite (busy_of_xquar L st X p c k n b1 ctx l1 l2 XB WF). rewrite !Z.eqb_refl. cbn [andb].
          unfold slot_shadow_bytes, bquar. cbn [xb_n xb_st]. rewrite <- EAB. fold S.
          eapply cells_frame in SHA; [| exact MUn | exact WM | cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by (clear -GR3; lia);
                                       apply Kshad; [clear -SHLO; lia| clear -SHHI GR3 GFS SE G0 GE; lia| clear -GR3; lia| left; clear -SE; lia]].
          eapply cells_frame in SHR; [| exact MUn | exact WM | cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by (clear -GFS GE GR3; unfold granules in *; lia);
                                       apply Kshad; [clear -SHLO SE GR3 G0 EGQ; lia| clear -SHHI GR3 GFS SE G0 GE EGQ; lia| clear -GFS GE GR3; unfold granules in *; lia| right; clear -EGQ; lia]].
          rewrite EGQ in SH'.
          replace (shad UB) with (shad AB + Z.of_nat (Z.to_nat (shlen (rz_size n)))) in SH' by (clear -SE GR3; lia).
          rewrite EGQ in SHR, G0.
          replace (shad UB + shlen (rup n 8)) with (shad AB + Z.of_nat (Z.to_nat (shlen (rz_size n))) + Z.of_nat (Z.to_nat (shlen (rup n 8)))) in SHR by (clear -SE GR3 G0; lia).
          pose proof (cb_app m' _ _ _ _ _ SHA (cb_app m' _ _ _ _ _ SH' SHR)) as FIN.
          assert (GE' : shlen (rup n 8) = granules n) by (rewrite <- EGQ; exact GE). rewrite <- GE'.
          replace (Z.to_nat (shlen (rz_size n)) + (Z.to_nat (shlen (rup n 8)) + Z.to_nat (shlen S - shlen (rz_size n) - shlen (rup n 8))))%nat with (Z.to_nat (shlen S)) in FIN
            by (clear -GR3 G0 GE' GFS; unfold granules in *; lia).
          rewrite <- ?app_assoc in FIN. rewrite <- ?app_assoc. exact FIN.
        * left. assert (T2 : (c =? c'') && (k =? k'') = false).
          { destruct (Z.eqb_spec c c'') as [E|]; [| reflexivity]. destruct (Z.eqb_spec k k'') as [E'|]; [| reflexivity]. exfalso. clear -NE1 E E'. lia. }
          split; [subst X1; rewrite (busy_of_xquar L st X p c k n b1 ctx l1 l2 XB WF), T2; reflexivity|].
          assert (DW : aslot_addr L c'' k'' + size_of_class c'' <= AB \/ AB + S <= aslot_addr L c'' k'').
          { pose proof (slots_sep_any L st X c'' k'' c k ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) HC Hk'' KR NE1) as D.
            rewrite <- EAB, <- ES in D. exact D. }
          pose proof (slot_aligned L c'' k'' SAL ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia)) as AL''.
          apply Kshad.
          -- rewrite shad_div. unfold ASHOFF. clear -P7 RES RHI. Z.div_mod_to_equations. lia.
          -- rewrite shad_div, shlen_div. unfold ASHOFF in *. clear -P8 T16. Z.div_mod_to_equations. lia.
          -- apply shlen_nonneg. clear -T16; lia.
          -- rewrite EGQ. destruct DW as [D|D].
             ++ left. eapply Z.le_trans; [apply shad_sep; [exact D| clear -AL''; Z.div_mod_to_equations; lia]|]. clear -SE GR3; lia.
             ++ right. apply shad_sep; [clear -D UBS; lia| exact UB16'].
      + intros POS''.
        set (AU := aregion L c'' + c_allocated_user (get_cls st c'')) in *.
        assert (U0 : aregion L c'' <= AU /\ AU + (c_mapped_user (get_cls st c'') - c_allocated_user (get_cls st c'')) <= aregion L c'' + K_FREEARR_OFF) by (subst AU; clear -Q1 Q2; lia).
        destruct U0 as [U0 U0'].
        assert (U1 : c'' = c -> aregion L c + c_allocated_user (get_cls st c) <= AU) by (intros E; subst AU; rewrite <- E; clear; lia).
        pose proof (undist_vs_user L c'' c _ _ UB (rup n 8) (c_allocated_user (get_cls st c)) ltac:(clear -PC0 ABUB; lia) ltac:(clear -PC0 UBS; lia) ltac:(clear -G3 G4; lia) U1 U0 U0') as D.
        assert (AM : AU mod 8 = 0) by (subst AU; pose proof (mod16_of_class _ _ Q3 QS16 ltac:(clear -QS; lia)) as AM; clear -AM RM''; Z.div_mod_to_equations; lia).
        apply Kshad.
        * rewrite shad_div. unfold ASHOFF. clear -U0 RI4 RES RHI. Z.div_mod_to_equations. lia.
        * rewrite shad_div, shlen_div. unfold ASHOFF, K_FREEARR_OFF, K_REGION, K_SPACE_SIZE in *. clear -U0' RI2 RI3 RES RHI. Z.div_mod_to_equations. lia.
        * clear -POS''; lia.
        * rewrite EGQ. destruct D as [D|D]; [left; apply shad_sep; [exact D| exact AM] | right; apply shad_sep; [exact D| exact UB16']].
  }
  idtac "CHECKPOINT-M2".
  (* [comment removed for export] *)
  assert (AVL' : forall c'', 1 <= c'' < K_NUM_CLASSES -> ashadow_avail L st1 m' c'').
  { intros c'' Hc''. pose proof WF as WF0. (nd_pre WF0 7%nat; intros _ _ SAL _ _ PERC _; nd_post).
    (nd_pre (PERC c'' Hc'') 8%nat; intros Q1 Q2 Q3 Q4 Q5 Q6 Q7 _; nd_post).
    pose proof (size_of_class_facts c'' Hc'') as [QS QS16]. pose proof (aregion_mod L c'' SAL) as RM''.
    unfold K_NUM_CLASSES in Hc''.
    assert (RI : al_res L + 4096 <= aregion L c'' /\ aregion L c'' + K_REGION <= al_space_beg L + K_SPACE_SIZE /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
    { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc'' RSP. lia. }
    (nd_pre RI 3%nat; intros RI1 RI2 RI3; nd_post).
    assert (PC0 : aregion L c <= AB /\ AB + S <= aregion L c + K_FREEARR_OFF /\ AB + S <= aregion L c + c_allocated_user (get_cls st c)) by (clear -G1 G2 G3 G4; lia).
    eapply ashadow_avail_frame; [exact MUn | exact WM | exact (AVL c'' ltac:(unfold K_NUM_CLASSES; exact Hc'')) | reflexivity | reflexivity | |].
    - intros POS''. set (AU := aregion L c'' + c_mapped_user (get_cls st c'')) in *.
      assert (U0 : aregion L c'' <= AU /\ AU + (K_FREEARR_OFF - c_mapped_user (get_cls st c'')) <= aregion L c'' + K_FREEARR_OFF) by (subst AU; clear -Q1 Q2; lia).
      destruct U0 as [U0 U0'].
      assert (U1 : c'' = c -> aregion L c + c_mapped_user (get_cls st c) <= AU) by (intros E; subst AU; rewrite <- E; clear; lia).
      pose proof (undist_vs_user L c'' c _ _ UB (rup n 8) (c_mapped_user (get_cls st c)) ltac:(clear -PC0 ABUB; lia) ltac:(clear -PC0 UBS G3; lia) G4 U1 U0 U0') as D.
      assert (AM : AU mod 8 = 0) by (subst AU; generalize Q4 RM''; clear; unfold K_USER_MAP; intros; Z.div_mod_to_equations; lia).
      apply Kshad.
      + rewrite shad_div. unfold ASHOFF. clear -U0 RI1 RES RHI. Z.div_mod_to_equations. lia.
      + rewrite shad_div, shlen_div. unfold ASHOFF, K_FREEARR_OFF, K_REGION, K_SPACE_SIZE in *. clear -U0' RI2 RI3 RES RHI. Z.div_mod_to_equations. lia.
      + clear -POS''; lia.
      + rewrite EGQ. destruct D as [D|D]; [left; apply shad_sep; [exact D| exact AM] | right; apply shad_sep; [exact D| exact UB16']].
    - intros POS''. set (AU := afreearr L c'' + c_mapped_free_array (get_cls st c'')) in *.
      assert (FA : aregion L c'' + K_FREEARR_OFF <= AU /\ AU + (K_FREEARR_MAX - c_mapped_free_array (get_cls st c'')) <= aregion L c'' + K_REGION).
      { subst AU. unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q5 Q6. lia. }
      destruct FA as [FA1 FA2].
      pose proof (farr_vs_user L c'' c _ _ UB (rup n 8) ltac:(clear -PC0 ABUB; lia) ltac:(clear -PC0 UBS; lia) FA1 FA2) as D.
      assert (AM : AU mod 8 = 0) by (subst AU; generalize Q7 RM''; clear; unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAP; intros; Z.div_mod_to_equations; lia).
      apply Kshad.
      + rewrite shad_div. unfold ASHOFF, K_FREEARR_OFF in *. clear -FA1 RI1 RES RHI. Z.div_mod_to_equations. lia.
      + rewrite shad_div, shlen_div. unfold ASHOFF, K_SPACE_SIZE in *. clear -FA2 RI2 RI3 RES RHI. Z.div_mod_to_equations. lia.
      + clear -POS''; lia.
      + rewrite EGQ. destruct D as [D|D]; [left; apply shad_sep; [exact D| exact AM] | right; apply shad_sep; [exact D| exact UB16']]. }
  idtac "CHECKPOINT-M3".
  (* [comment removed for export] *)
  assert (HS' : ASEC L st1 X1 m').
  { eapply (hs_frame _ HL L st st1 X X1 m m'); [exact HS | exact MUn | exact WM | |].
    - unfold sec_untouched, aknown. unfold AINSTANCE, K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
      assert (SHB : 2201439137792 <= shad UB /\ shad UB + gq <= 17594333495296) by (clear -SHLO SHHI SE GR3 GFS GE EGQ G0; lia).
      (* [comment removed for export] *)
      assert (SHB1 : shad (al_space_beg L) + 536870912 <= shad (aregion L c)).
      { rewrite !shad_div. unfold aregion, K_REGION, K_NUM_CLASSES in *. change (2^32) with 4294967296 in *. clear -HC. Z.div_mod_to_equations. lia. }
      assert (SHB2 : shad (aregion L c) + shlen (c_mapped_user (get_cls st c)) <= shad (al_space_beg L) + 17179869184).
      { (pose proof (alayout_space L ALO) as ndP__; nd_pre ndP__ 4%nat; intros _ _ SPal _; nd_post). rewrite !shad_div, shlen_div. unfold aregion, K_REGION, K_ALIGN, K_FREEARR_OFF, K_NUM_CLASSES in *. change (2^32) with 4294967296 in *.
        clear -HC G4 SPal. Z.div_mod_to_equations. lia. }
      (* [comment removed for export] *)
      apply Forall_cons; [cbn [fst snd]; intros a Ha; do 4 right; left; clear -Ha CEIL LO; lia |].
      do 3 (apply Forall_cons; [cbn [fst snd]; intros a Ha; left; left; clear -Ha; unfold AIMG_HI, AINSTANCE; lia |]).   (* [comment removed for export] *)
      apply Forall_cons; [cbn [fst snd]; intros a Ha; do 5 right; left; clear -Ha OT TBND TIMG; lia |].
      apply Forall_cons; [cbn [fst snd]; intros a Ha; do 7 right; left; clear -Ha G5 G6 ABUB S8 EUB RSP; lia |].
      apply Forall_cons; [cbn [fst snd]; intros a Ha; right; left; clear -Ha SE GR3 GFS GE EGQ G0 SHM1 SHM2 SHB1 SHB2; lia |].
      apply Forall_cons; [cbn [fst snd]; intros a Ha; do 8 right; left; clear -Ha; lia |].
      apply Forall_cons; [cbn [fst snd]; intros a Ha; do 9 right; left; clear -Ha; lia |].
      apply Forall_nil.
    - eapply (sec_same_free st p c n); [exact LIVE| apply same_core_refl| apply Permutation_refl]. }
  assert (BL' : ablocks L st1 X1 (lb_remove p LB)) by (exact (ablocks_xquar L st X p c k n b1 ctx l1 l2 XB LB st1 eq_refl BL)).
  assert (FKD : forall cls FA sz, In (mkABlock (ABFake cls) FA sz) LB -> al_fake L <= FA /\ 0 <= sz /\ FA + sz <= al_fake L + 11571200)
    by (intros cls FA sz Hin; exact (proj1 (proj2 BL) cls FA sz Hin)).
  pose proof (ao_fake L ALO) as FKO. (pose proof (aobj_int _ _ FKO ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros FKi FKa [kF FBND]; nd_post). unfold aobj in FKO.   (* [comment removed for export] *)
  pose proof (ad_t_fake L ALO) as D_t_f. pose proof (ad_fake_res L ALO) as D_f_res. pose proof (ad_nodes_fake L ALO) as D_n_f. pose proof (ad_store_fake L ALO) as D_s_f.
  unfold adisj in D_t_f, D_f_res, D_n_f, D_s_f. box D_t_f. box D_f_res. box D_n_f. box D_s_f.
  assert (HFK' : AFK L (lb_remove p LB) m').
  { eapply (hf_blocks _ HL L LB); [eapply (hf_frame _ HL L LB m m'); [exact HFK | exact MUn | exact WM |] |].
    - pose proof (ao_dtls L ALO) as DTO. (pose proof (aobj4_int _ DTO) as ndP__; nd_pre ndP__ 4%nat; intros _ _ [kD DBND] [jD DIMG]; nd_post). unfold aobj in DTO.   (* [comment removed for export] *)
      pose proof (ad_t_dtls L ALO) as D1. pose proof (ad_dtls_res L ALO) as D2. pose proof (ad_nodes_dtls L ALO) as D3. pose proof (ad_store_dtls L ALO) as D4.
      unfold adisj in D1, D2, D3, D4.
      unfold fake_untouched. unfold K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
      assert (SHF : (shad (al_fake L) + shlen 11571200 <= shad UB \/ shad UB + gq <= shad (al_fake L))
                    /\ 2148238848 <= shad (al_fake L) /\ shad (al_fake L) + shlen 11571200 <= 17594333495296).   (* [comment removed for export] *)
      { split; [| rewrite shad_div, shlen_div; unfold ASHOFF; pose proof atop_range as AR8; clear -FKO FKi FBND AR8; Z.div_mod_to_equations; lia].
        pose proof D_f_res as DFR. unbox DFR. rewrite EGQ. destruct DFR as [D|D].
        - left. apply shad_sep; [| clear -FKO FKi FBND; Z.div_mod_to_equations; lia]. clear -D RSP G5 ABUB. lia.
        - right. apply shad_sep; [| exact UB16']. clear -D RSP G6 UBS. lia. }
      (nd_pre SHF 3%nat; intros SHF1 SHF2 SHF3; nd_post).
      assert (SHB : 2201439137792 <= shad UB /\ shad UB + gq <= 17594333495296) by (clear -SHLO SHHI SE GR3 GFS GE EGQ G0; lia).
      pose proof D_t_f as DTF; unbox DTF. pose proof D_f_res as DFR; unbox DFR. pose proof D_n_f as DNF; unbox DNF. pose proof D_s_f as DSF; unbox DSF.
      (apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | idtac]]]]]]]]]).
      apply Forall_nil.
    - intros cls FA sz. rewrite (In_lb_remove p LB). cbn. split; [intros [Hin _]; exact Hin| intros Hin; split; [exact Hin| discriminate]]. }
  idtac "CHECKPOINT-M4".
  (* [comment removed for export] *)
  assert (SEPQ : forall q, In q (q_loc Q ++ q_glob Q) -> AB + S <= abatch_addr L (qb_slot q) \/ abatch_addr L (qb_slot q) + 8192 <= AB).
  { intros q Hq. (nd_pre (bslot_busy L st X Q CP q Hq) 5%nat; intros yq Hyq Syq Cyq Kyq; nd_post).
    pose proof (slots_sep_any L st X c k K_BATCH_CLASS (qb_slot q) ALO WF HC (K24) KR (bslot_range L st X Q WF CP q Hq)
                  ltac:(rewrite <- Cyq, <- Kyq; apply (other_key (AHQ DI ASEC AFK) L st X m (BLive p) c k n b1 ctx l1 l2 AR XB); [exact Hyq| rewrite Syq; discriminate])) as D.
    rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
  assert (BGEO : forall q, In q (q_loc Q ++ q_glob Q) ->
      al_res L + 4096 <= abatch_addr L (qb_slot q) /\ abatch_addr L (qb_slot q) + 8192 <= al_res L + 137439023104).
  { intros q Hq. (pose proof (slot_geo L st X K_BATCH_CLASS (qb_slot q) ALO WF (K24) (bslot_range L st X Q WF CP q Hq)) as ndP__; nd_pre ndP__ 10%nat; intros _ _ _ P1 P2 P3 P4 P5 P6 _; nd_post).
    rewrite size_of_class_24 in P2, P6. unfold abatch_addr. unfold K_SPACE_SIZE in P6. change (2^37) with 137438953472 in P6.
    generalize P1 P2 P5 P6 RSP; clear; intros. lia. }
  assert (BFR : forall q, In q (q_loc Q ++ q_glob Q) -> disjoint_from (WfM (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L)) (abatch_addr L (qb_slot q)) 8192).
  { intros q Hq. destruct (BGEO q Hq) as [F3 F4]. pose proof (SEPQ q Hq) as SQ. apply Kres; clear -F3 F4 RES RHI SQ ABUB S8 EUB; lia. }
  assert (HQ' : AQUAR_at L st1 X1 QM m').
  { subst QM. unfold AQUAR_at. cbn [q_loc q_glob q_ia q_pend].
    change (a_qloc st1) with (a_qloc st). change (a_qglob st1) with (a_qglob st). change (a_qloc_bytes st1) with (a_qloc_bytes st). change (a_qglob_bytes st1) with (a_qglob_bytes st).
    split; [| split; [| split; [| split; [| split]]]].
    - eapply (aquar_glob_const_frame _ m m' MUn WM); [exact (conj QK MX) | apply Kimg; clear; unfold AQ_MAX, AIMG_HI; lia | apply Kimg; clear; unfold AQ_MUTEX, AIMG_HI; lia].
    - eapply (aqcache_frame L _ m m' MUn WM); [exact (conj QC ABL) | unfold aq_tcache; apply Kt; clear; lia |].
      intros q Hq. unfold Q_BATCH_BYTES. apply BFR. apply in_or_app. left. exact Hq.
    - eapply (aqcache_frame L _ m m' MUn WM); [exact (conj GCQ ABG) | apply Kimg; clear; unfold AQ_GCACHE, AINSTANCE, AIMG_HI; lia |].
      intros q Hq. unfold Q_BATCH_BYTES. apply BFR. apply in_or_app. right. exact Hq.
    - split; [exact FL'|]. split; [exact IAS'|]. intros _ j Hj. apply IAM'. revert Hj. clear. unfold AIA_MAP1_LEN. cbn. lia.
    - subst X1. eapply (qcoupled_pend L st st1 X); [exact CP | reflexivity | reflexivity | | |].
      + exact (HQ_xquar X p c k n b1 ctx l1 l2 XB).
      + exact (HB_xquar X p c k n b1 ctx l1 l2 XB).
      + exact (FQ_X L st X p c k n b1 ctx l1 l2 XB WF).
    - exact NUM. }
  idtac "CHECKPOINT-M5".
  (* [comment removed for export] *)
  assert (HBK : forall blk, In blk (lb_remove p LB) -> disjoint_from (WfM (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L)) (ab_addr blk) (ab_size blk)).
  { intros [[q|cls] A' n'] Hin; cbn [ab_addr ab_size]; apply (proj1 (In_lb_remove p LB _)) in Hin; destruct Hin as [Hin NEp]; cbn [ab_kind] in NEp.
    - destruct (proj1 BL q A' n' Hin) as [(b & Hb & Sb & Ub & Nb)|(mb & msz & Lp & EUA & Gs)].
      + assert (NEq : xb_st b <> BLive p) by (rewrite Sb; intros E; apply NEp; congruence).
        pose proof (other_key (AHQ DI ASEC AFK) L st X m (BLive p) c k n b1 ctx l1 l2 AR XB b Hb NEq) as NE1.
        destruct (busy_slot_range L st X b WF Hb) as [HCb HKb].
        pose proof (awf_fits L st X b WF Hb) as FIT. unfold xb_fits in FIT. rewrite Sb in FIT.
        unfold xb_user, xb_alloc in Ub. subst A' n'.
        set (cb := xb_class b) in *. set (kb := xb_slot b) in *.
        (pose proof (slot_geo L st X cb kb ALO WF HCb HKb) as ndP__; nd_pre ndP__ 12%nat; intros T16 TM16 TAL P1 P2 P3 P4 P5 P6 P7 P8 _; nd_post).
        pose proof (slots_sep_any L st X cb kb c k ALO WF HCb HC HKb KR ltac:(clear -NE1; lia)) as D9. rewrite <- EAB, <- ES in D9.
        apply Kres; [clear -P5 RSP FIT; lia | clear -P6 RSP FIT; unfold K_SPACE_SIZE in *; lia | clear -FIT; lia | clear -D9 FIT ABUB S8 EUB; lia].
      + (* [comment removed for export] *)
        cbn [sec_wf1] in Gs. (nd_pre Gs 7%nat; intros Gs1 Gs2 Gs3 Gs4 Gs5 Gs6 (Ct & Cc & Cr & Cp & Cn & Cs & Cf & Cd); nd_post).
        pose proof (sec_facts n' ltac:(clear -Gs5; lia) Gs6) as SF. subst A'. unfold SEC_UOFF, K_HIGH_MEM in *.
        unfold ablk, KLS, AIMG_HI in Gs2.   (* [comment removed for export] *)
        apply Kobj; clear -Gs2 Gs3 Gs4 Gs5 SF Ct Cr Cn Cs; lia.
    - (nd_pre (FKD cls A' n' Hin) 3%nat; intros K1 K2 K3; nd_post). atop_facts.
      pose proof D_t_f as DTF; unbox DTF. pose proof D_f_res as DFR; unbox DFR. pose proof D_n_f as DNF; unbox DNF. pose proof D_s_f as DSF; unbox DSF.
      apply Kobj; [clear -K1 K3 FKO FKi FBND; lia | clear -K3 FKO FKi FBND; lia | exact K2 | clear -K1 K3 DTF; lia
                  | clear -K1 K3 DFR; lia | clear -K1 K3 DNF; lia | clear -K1 K3 DSF; lia]. }
  assert (HFS : forall cls FA sz, In (mkABlock (ABFake cls) FA sz) (lb_remove p LB) -> forall a', FA <= a' < FA + sz ->
      disjoint_from (WfM (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L)) (shad a') 1).
  { intros cls FA sz Hin a' Ha'. apply (proj1 (In_lb_remove p LB _)) in Hin. destruct Hin as [Hin _].
    (nd_pre (FKD cls FA sz Hin) 3%nat; intros K1 K2 K3; nd_post). atop_facts.
    apply Kshad; [rewrite shad_div; unfold ASHOFF; clear -K1 FKO FKi FBND Ha'; Z.div_mod_to_equations; lia
                 | rewrite shad_div; unfold ASHOFF; clear -K3 FKO FKi FBND Ha'; Z.div_mod_to_equations; lia | clear; lia |].
    pose proof D_f_res as DFR; unbox DFR. destruct DFR as [D|D].
    - left. rewrite (shad_div a'), (shad_div UB). clear -D Ha' K3 RSP G5 ABUB UB16'. Z.div_mod_to_equations. lia.
    - right. rewrite EGQ, shlen_div, (shad_div a'), (shad_div UB). unfold K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
      clear -D Ha' K1 RSP G6 UBS RUP8 UB16'. Z.div_mod_to_equations. lia. }
  (* [comment removed for export] *)
  assert (TLSK : forall TA tk, ATPv + -200 <= TA -> TA + tk <= ATPv + 312 -> 0 <= tk ->
      disjoint_from (WfM (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L)) TA tk).
  { intros TA tk TH1 TH2 TH3. pose proof ATPv_img as TI. apply Kimg; clear -TH1 TH2 TH3 TI; unfold AIMG_HI; lia. }
  assert (TLSS : forall a', ATPv + -200 <= a' < ATPv + 312 ->
      disjoint_from (WfM (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L)) (shad a') 1).
  { intros a' Ha'. pose proof ATPv_img as TI. apply Klow; clear -Ha' TI; try (rewrite shad_div; unfold ASHOFF); try Z.div_mod_to_equations; lia. }
  assert (PSP : shad UB + gq <= shad ATOP).
  { rewrite EGQ, shlen_div, (shad_div UB), (shad_div ATOP). atop_facts. clear -UBS G8 ABCE CEIL LO RUP8 UB16'. Z.div_mod_to_equations. lia. }
  (* [comment removed for export] *)
  split; [| split; [exact BL'| split; [exact HFK'|]]].
  - split; [exact WF'|]. split; [exact RT'|]. split; [exact INST'|]. split; [exact THR'|]. split; [exact CLS'|].
    split; [exact HQ'|]. split; [exact HS'|]. split; [exact DEP'|]. split; [exact HRO'|]. split; [exact HRT2'|]. split; [exact AVL'| exact RT3'].
  - eapply (aheap_pres_mid CI); [exact KF | exact CI_OK | exact MUn | exact WM | exact HBK | exact HFS | exact PSP | exact TLSK | exact TLSS | apply Klow; unfold AIMSH_LO, AIMSH_LEN; clear; lia
      | rewrite <- (ao_ahm_eq L ALO); unfold AAHM_SZ; pose proof (ao_ahm L ALO) as OAH; pose proof (aobj_img _ _ OAH ltac:(clear; lia)) as OAHI;
      pose proof (ad_ahm_t L ALO) as DA1; pose proof (ad_ahm_res L ALO) as DA2; pose proof (ad_ahm_nodes L ALO) as DA3; pose proof (ad_ahm_store L ALO) as DA4;
      unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI, adisj in OAH, OAHI, DA1, DA2, DA3, DA4; apply Kobj; clear -OAH OAHI DA1 DA2 DA3 DA4; lia].
Qed.
End Zd1.
#[using="HL CI_OK"] Theorem mid_kit : ltac:(let t := eval cbv delta [mid_kit__stmt] in mid_kit__stmt in exact t).
Proof. exact mid_kit__body. Qed.
End S.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Exec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepStore__A3W.ARepStore.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AFreeModel.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.AFreeGeo.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRead.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tail.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_afree_icpt.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tailR__A3W.F_afree_icptR.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.F_afree_arep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_tabscan__A3W.AFreeStoreK.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.AFreeStore.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_fast__A3W.F_afree_arepR.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac sg_set := let GG := fresh "GG" in (match goal with |- ?G => set (GG := G) end).
Local Ltac sg_unset := match goal with |- ?G => is_var G; subst G end.
Local Ltac sg_destr := sg_set; repeat match goal with H : _ /\ _ |- _ => destruct H end; sg_unset.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Notation WfM sp t UB gq nodes store :=
  ([(sp - 4096, sp); (0xafc00, 0x130c30); (0x13e488, 0x13e48c); (ADEPOT_LO, ADEPOT_HI);
    (t + 2800, t + 3169); (UB - 16, UB + 8); (shad UB, shad UB + gq);
    (nodes, nodes + 1048576); (store, store + 8388608)]%Z) (only parsing).

(* [comment removed for export] *)
Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6307840 * k <= a.
Proof. intros a n H G2. unfold iclr, AIMG_LO, AIMG_HI in H. destruct H as [? [?|?]]; [exists 0 | exists 1]; lia. Qed.
Local Lemma ablk_int {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT} : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6307840 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
Local Ltac band_int H :=
  let k := fresh "k" H in let A := fresh "KA" H in let B := fresh "KB" H in let C := fresh "KC" H in let D := fresh "KD" H in
  let G1 := fresh "G" in let G2 := fresh "G" in
  lazymatch type of H with
  | sclr ?a ?n =>
      assert (G1 : 0 <= a) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia); assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      (nd_pre (sclr_int a n H G1 G2) 4%nat; intros k A B C; nd_post); clear G1 G2
  | iclr ?a ?n =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      (nd_pre (iclr_int a n H G2) 5%nat; intros k A B C D; nd_post); clear G2
  | 4096 <= ?a /\ (?a + ?n <= _ \/ _ <= ?a) =>      (* [comment removed for export] *)
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      (nd_pre (iclr_int a n H G2) 5%nat; intros k A B C D; nd_post); clear G2
  | ablk ?lo ?hi => let E := fresh "KE" H in destruct (ablk_int lo hi H) as (k & A & B & E & C & D)
  end.

(* [comment removed for export] *)
Ltac fu_drop_fake := repeat match goal with H : context [al_fake _] |- _ => clear H end.
Ltac fu_drop_dtls := repeat match goal with H : context [al_dtls _] |- _ => clear H end.
Ltac fu_drop_tls := repeat match goal with H : context [ATPv] |- _ => clear H | H : context [kt_img] |- _ => clear H end.
Ltac fu_focus :=
  lazymatch goal with
  | |- context [al_fake _] => fu_drop_dtls; fu_drop_tls
  | |- context [al_dtls _] => fu_drop_fake; fu_drop_tls
  | |- context [ATPv] => fu_drop_fake; fu_drop_dtls
  | |- _ => fu_drop_fake; fu_drop_dtls; fu_drop_tls
  end.
Ltac fu_lia := first [solve [fu_focus; lia] | lia].
(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
(* [comment removed for export] *)
#[using="Type"] Local Lemma aobj_int : forall a n, aobj a n -> 0x10000 <= n ->
  6307840 <= a /\ a + n <= ATOP /\ exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof.
  intros a n H Hn. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. (nd_pre H 5%nat; intros H1 H2 H3 H4 H5; nd_post).
  split; [lia|]. split; [lia|]. destruct H4; [exists 0 | exists 1]; lia.
Qed.
#[using="Type"] Local Lemma aobj4_int : forall a, aobj a 4096 ->
  4096 <= a /\ a + 4096 <= ATOP
  /\ (exists k, 0 <= k <= 1 /\ a + 4096 <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a)
  /\ (exists j, 0 <= j <= 1 /\ a + 4096 <= 65536 + j * 18446744073709551616 /\ 6307840 * j <= a).
Proof.
  intros a H. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. (nd_pre H 5%nat; intros H1 H2 H3 H4 H5; nd_post).
  split; [lia|]. split; [lia|]. split; [destruct H4; [exists 0 | exists 1]; lia | destruct H5 as [_ [H5|H5]]; [exists 0 | exists 1]; lia].
Qed.

Section KindsM.
Variables (sp t AB S UB gq nodes store res ctx lo grz ssz : Z).
Definition kfactsM : Prop :=
     (ATOP <= lo /\ lo <= sp - 4096)
  /\ (sclr t 4096 /\ iclr t 4096 /\ 4096 <= t /\ t + 4096 <= ATOP)      (* [comment removed for export] *)
  /\ (17594333495296 <= res /\ res + 137439023104 <= ATOP)      (* [comment removed for export] *)
  /\ (res + 4096 <= AB /\ AB + S <= res + 137439023104 /\ AB + 16 <= UB /\ UB + 8 <= AB + S)
  /\ (2201439137792 <= shad AB /\ shad UB = shad AB + grz /\ 2 <= grz /\ 1 <= gq /\ shad UB + gq <= shad AB + ssz
      /\ shad AB + ssz <= 17594333495296)
  /\ (sclr nodes 1048576 /\ 6307840 <= nodes /\ nodes + 1048576 <= ATOP /\ sclr store 8388608 /\ 6307840 <= store /\ store + 8388608 <= ATOP)   (* [comment removed for export] *)
  /\ (sclr ctx 65536 /\ 6307840 <= ctx /\ ctx + 65536 <= ATOP).   (* [comment removed for export] *)
Hypothesis KF : kfactsM.

(* [comment removed for export] *)
Ltac kbase L := lazymatch L with Z.add ?X _ => kbase X | Z.sub ?X _ => kbase X | Z.mul _ ?X => kbase X | _ => L end.
Ltac kalias X := lazymatch X with UB => constr:(res) | AB => constr:(res) | _ => X end.
Ltac kkeep2 X Y := repeat match goal with H : _ \/ _ |- _ => lazymatch type of H with context [X] => fail | context [Y] => fail | _ => clear H end end.
Ltac klia := Zify.zify; xlia zchecker.
Ltac kind1 := lazymatch goal with
  | |- (_ <= ?L \/ _)%Z => let X := kbase L in let Y := kalias X in first [ solve [ kkeep2 X Y; klia ] | lia ]
  | |- _ => lia end.
Ltac kind := pose proof KF as KF'; unfold kfactsM, AIMG_HI in *;
  sg_set; (nd_pre KF' 7%nat; intros F_lo sgk1 F_res F_slot F_sh sgk2 sgk3; nd_post); (nd_pre sgk1 4%nat; intros Ft1 Ft2 Ft3 Ft4; nd_post); (nd_pre sgk2 6%nat; intros Fn1 Fn2 Fn3 Fs1 Fs2 Fs3; nd_post); (nd_pre sgk3 3%nat; intros Fc1 Fc2 Fc3; nd_post);
  band_int Ft1; band_int Ft2; band_int Fn1; band_int Fs1; band_int Fc1; clear Ft1 Ft2 Fn1 Fs1 Fc1;   (* [comment removed for export] *)
  sg_unset; cbn [disjoint_from]; repeat (split; [kind1|]); first [kind1 | exact I].

#[using="rc AB S res ctx lo grz ssz KF"] Lemma KM_img : forall A k, 0x10000 <= A -> 0 <= k ->
  (A + k <= ADEPOT_LO /\ (A + k <= 0xafc00 \/ 0x130c30 <= A) /\ (A + k <= 0x13e488 \/ 0x13e48c <= A))
  \/ (ADEPOT_HI <= A /\ A + k <= AIMG_HI) ->
  disjoint_from (WfM sp t UB gq nodes store) A k.
Proof. intros. kind. Qed.
#[using="rc AB S res ctx lo grz ssz KF"] Lemma KM_low : forall A k, 2147450880 <= A -> A + k <= 2148239360 -> 0 <= k ->      (* [comment removed for export] *)
  disjoint_from (WfM sp t UB gq nodes store) A k.
Proof. intros. kind. Qed.
#[using="rc AB S res ctx lo grz ssz KF"] Lemma KM_hi : forall A k, sp <= A -> 0 <= k -> disjoint_from (WfM sp t UB gq nodes store) A k.
Proof. intros. kind. Qed.
#[using="rc AB S res ctx lo grz ssz KF"] Lemma KM_shad : forall A k, 2147446784 <= A -> A + k <= 17594333495296 -> 0 <= k ->      (* [comment removed for export] *)
  (A + k <= shad UB \/ shad UB + gq <= A) -> disjoint_from (WfM sp t UB gq nodes store) A k.
Proof. intros. kind. Qed.
#[using="rc AB S lo grz ssz KF"] Lemma KM_ctx :
  (ctx + 65536 <= t \/ t + 4096 <= ctx) -> (ctx + 65536 <= res \/ res + 137439023104 <= ctx) ->
  (ctx + 65536 <= nodes \/ nodes + 1048576 <= ctx) -> (ctx + 65536 <= store \/ store + 8388608 <= ctx) ->
  forall A k, ctx <= A -> A + k <= ctx + 65536 -> 0 <= k -> disjoint_from (WfM sp t UB gq nodes store) A k.
Proof. intros. kind. Qed.
#[using="rc AB S ctx lo grz ssz KF"] Lemma KM_t :
  (t + 4096 <= res \/ res + 137439023104 <= t) -> (t + 4096 <= nodes \/ nodes + 1048576 <= t) -> (t + 4096 <= store \/ store + 8388608 <= t) ->
  forall A k, t <= A -> A + k <= t + 4096 -> 0 <= k -> (A + k <= t + 2800 \/ t + 3169 <= A) ->
  disjoint_from (WfM sp t UB gq nodes store) A k.
Proof. intros. kind. Qed.
#[using="rc AB S ctx lo grz ssz KF"] Lemma KM_res :
  (t + 4096 <= res \/ res + 137439023104 <= t) -> (nodes + 1048576 <= res \/ res + 137439023104 <= nodes) ->
  (store + 8388608 <= res \/ res + 137439023104 <= store) ->
  forall A k, res <= A -> A + k <= res + 137439023104 -> 0 <= k -> (A + k <= UB - 16 \/ UB + 8 <= A) ->
  disjoint_from (WfM sp t UB gq nodes store) A k.
Proof. intros. kind. Qed.
#[using="AB S ctx lo grz ssz KF"] Lemma KM_obj : forall A k, ((6307840 <= A /\ A + k <= 2147446784) \/ 17594333495296 <= A) -> A + k <= ATOP -> 0 <= k ->      (* [comment removed for export] *)
  (A + k <= t \/ t + 4096 <= A) -> (A + k <= res \/ res + 137439023104 <= A) ->
  (A + k <= nodes \/ nodes + 1048576 <= A) -> (A + k <= store \/ store + 8388608 <= A) ->
  disjoint_from (WfM sp t UB gq nodes store) A k.
Proof. intros. kind. Qed.
(* [comment removed for export] *)
#[using="AB S ctx lo grz ssz KF"] Lemma KM_objL : forall A k, ((A + k <= 65536 \/ 6307840 <= A) /\ (A + k <= 2147446784 \/ 17594333495296 <= A)) -> A + k <= ATOP -> 0 <= k ->      
  (A + k <= t \/ t + 4096 <= A) -> (A + k <= res \/ res + 137439023104 <= A) ->
  (A + k <= nodes \/ nodes + 1048576 <= A) -> (A + k <= store \/ store + 8388608 <= A) ->
  disjoint_from (WfM sp t UB gq nodes store) A k.
Proof. intros. kind. Qed.
End KindsM.

(* [comment removed for export] *)
#[using="Type"] Lemma aheap_pres_mid : forall (CI : list (Z * Z)) sp t AB S UB gq nodes store res ctx lo grz ssz (LB : list ablock) m m',
  kfactsM sp t AB S UB gq nodes store res ctx lo grz ssz ->
  Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI
                 /\ (snd iv <= 0xab670 \/ 0xab730 <= fst iv)
                 /\ (snd iv <= 0xafc00 \/ 0x130c30 <= fst iv)
                 /\ (snd iv <= 0x13e488 \/ 0x13e48c <= fst iv)) CI ->
  munch (WfM sp t UB gq nodes store) m m' -> wmono asegs m m' ->
  (forall b, In b LB -> disjoint_from (WfM sp t UB gq nodes store) (ab_addr b) (ab_size b)) ->
  (forall cls FA sz, In (mkABlock (ABFake cls) FA sz) LB -> forall a', FA <= a' < FA + sz ->
       disjoint_from (WfM sp t UB gq nodes store) (shad a') 1) ->
  shad UB + gq <= shad ATOP ->
  (forall A k, ATPv + -200 <= A -> A + k <= ATPv + 312 -> 0 <= k -> disjoint_from (WfM sp t UB gq nodes store) A k) ->      (* [comment removed for export] *)
  (forall a', ATPv + -200 <= a' < ATPv + 312 -> disjoint_from (WfM sp t UB gq nodes store) (shad a') 1) ->                  (* [comment removed for export] *)
  disjoint_from (WfM sp t UB gq nodes store) AIMSH_LO AIMSH_LEN ->                                                          (* [comment removed for export] *)
  disjoint_from (WfM sp t UB gq nodes store) AAHMv AAHM_SZ ->                                                          (* [comment removed for export] *)
  aheap_pres CI LB sp m m'.
Proof.
  intros CI sp t AB S UB gq nodes store res ctx lo grz ssz LB m m' KF CIOK MU WM HBK HFK PSP TLSK TLSS IMSH AHMK a Ha CL.
  split; [| intros Hw; apply WM; exact Hw].
  apply MU. rewrite wa_unsigned by exact Ha.
  destruct CL as [CL|TL]; [| exact (aextra_outside _ a TLSK TLSS IMSH AHMK TL)].
  pose proof KF as KF'. (nd_pre KF' 7%nat; intros F_lo F_t F_res F_slot F_sh F_ns F_ctx; nd_post).
  destruct CL as [ST | [CIa | [BLK | SH]]].
  - eapply disjoint_outside; [eapply (KM_hi _ _ _ _ _ _ _ _ _ _ _ _ _ KF a 1); lia | lia].
  - (nd_pre CIa 3%nat; intros iv Hiv R; nd_post). (pose proof (proj1 (Forall_forall _ _) CIOK iv Hiv) as ndP__; nd_pre ndP__ 6%nat; intros Q1 Q2 Q3 Q4 Q5 Q6; nd_post). cbn [fst snd] in *.
    eapply disjoint_outside; [eapply (KM_img _ _ _ _ _ _ _ _ _ _ _ _ _ KF a 1); unfold AIMG_HI in *; lia | lia].
  - (nd_pre BLK 3%nat; intros b Hb R; nd_post). eapply disjoint_outside; [exact (HBK b Hb) | lia].
  - (nd_pre SH 3%nat; intros a' Ha' ndR1__; nd_post; revert ndR1__; intros ->).
    pose proof (shad_div a') as SD. pose proof (shad_div ATOP) as SDs. unfold ASHOFF in *.
    destruct Ha' as [ST | [CIa | FK]].
    + eapply disjoint_outside; [eapply (KM_shad _ _ _ _ _ _ _ _ _ _ _ _ _ KF (shad a') 1) | lia].
      all: atop_facts; clear -ST SD SDs F_sh F_lo PSP; Z.div_mod_to_equations; lia.
    + (nd_pre CIa 3%nat; intros iv Hiv R; nd_post). (pose proof (proj1 (Forall_forall _ _) CIOK iv Hiv) as ndP__; nd_pre ndP__ 4%nat; intros Q1 Q2 Q3 _; nd_post). cbn [fst snd] in *.
      eapply disjoint_outside; [eapply (KM_low _ _ _ _ _ _ _ _ _ _ _ _ _ KF (shad a') 1) | lia].
      all: unfold AIMG_HI in *; clear -R SD Q1 Q3; Z.div_mod_to_equations; lia.
    + (nd_pre FK 5%nat; intros cls FA sz Hin R; nd_post). eapply disjoint_outside; [exact (HFK cls FA sz Hin a' R) | lia].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma qcoupled_pend : forall L s s' X X' Q c k n b1 ctx,
  qcoupled L s X Q -> a_qloc s' = a_qloc s -> a_qglob s' = a_qglob s ->
  (forall y, In y (x_busy X') /\ xb_st y = BQuar <-> (In y (x_busy X) /\ xb_st y = BQuar) \/ y = mkXBusy c k n BQuar b1 ctx) ->
  (forall y, In y (x_busy X') /\ xb_st y = BBatch <-> (In y (x_busy X) /\ xb_st y = BBatch) \/ In y []) ->
  (forall y, In y (x_busy X) -> xb_st y = BQuar -> xb_class y = c -> xb_slot y = k -> False) ->
  qcoupled L s' X' (mkQConc (q_loc Q) (q_glob Q) true ((c, k) :: q_pend Q)).
Proof.
  intros L s s' X X' Q c k n b1 ctx (LN1 & LN2 & OK & ND1 & ND2 & BS & PS & NN) QL QG HQ HB FQ.
  unfold qcoupled. cbn [q_loc q_glob q_pend]. rewrite QL, QG.
  set (es := qentries (a_qloc s) (q_loc Q) ++ qentries (a_qglob s) (q_glob Q)) in *.
  assert (PM : Permutation (qprim_ids es ++ (c, k) :: q_pend Q) ((c, k) :: (qprim_ids es ++ q_pend Q))) by (apply Permutation_sym; apply Permutation_middle).
  split; [exact LN1|]. split; [exact LN2|]. split.
  { eapply Forall_impl; [| exact OK]. intros [ch k'] HOK. unfold qentry_ok in *. cbn [fst snd] in *.
    destruct ch as [c' n'| mb ms n']; [| exact I]. (nd_pre HOK 3%nat; intros b1' ctx' Hin; nd_post). exists b1', ctx'.
    apply (proj1 (proj2 (HQ _) (or_introl (conj Hin eq_refl)))). }
  split.
  { eapply Permutation_NoDup'; [apply Permutation_sym; exact PM|]. constructor; [| exact ND1].
    intros Hin. apply (PS c k) in Hin. (nd_pre Hin 5%nat; intros y Hy Sy Cy Ky; nd_post). exact (FQ y Hy Sy Cy Ky). }
  split; [exact ND2|]. split.
  { intros k0. rewrite (BS k0). split; intros (y & Hy & Sy & Cy & Ky); exists y; (split; [| split; [exact Sy| split; [exact Cy| exact Ky]]]).
    - apply (proj1 (proj2 (HB y) (or_introl (conj Hy Sy)))).
    - destruct (proj1 (HB y) (conj Hy Sy)) as [[Hy0 _]|[]]. exact Hy0. }
  split; [| exact NN].
  intros c0 k0. split.
  - intros H. apply (Permutation_in _ PM) in H. destruct H as [E|H].
    + injection E as <- <-. exists (mkXBusy c k n BQuar b1 ctx). split; [apply (proj1 (proj2 (HQ _) (or_intror eq_refl)))|]. cbn. auto.
    + apply (PS c0 k0) in H. (nd_pre H 5%nat; intros y Hy Sy Cy Ky; nd_post). exists y. split; [apply (proj1 (proj2 (HQ y) (or_introl (conj Hy Sy))))|]. auto.
  - intros (y & Hy & Sy & Cy & Ky). eapply Permutation_in; [apply Permutation_sym; exact PM|].
    destruct (proj1 (HQ y) (conj Hy Sy)) as [[Hy0 _]| ->].
    + right. apply (PS c0 k0). exists y. auto.
    + left. cbn in Cy, Ky. subst. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section S.
Variable DI : ADepotIface.
Variables (ASEC : alayout -> astate -> aconc -> amem -> Prop) (AFK : alayout -> list ablock -> amem -> Prop).
Hypothesis HL : ahole_laws (AHQ DI ASEC AFK).
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI
                                  /\ (snd iv <= 0xab670 \/ 0xab730 <= fst iv)
                                  /\ (snd iv <= 0xafc00 \/ 0x130c30 <= fst iv)
                                  /\ (snd iv <= 0x13e488 \/ 0x13e48c <= fst iv)) CI.

Definition mid_kit__stmt : Prop := mid_stmt DI ASEC AFK CI.
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'mid_kit__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'mid_kit__stmt 1).
Variable full : ltac2:(SecDietF.SzSecF.ty 'mid_kit__stmt 2).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'mid_kit__stmt 3).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'mid_kit__stmt 4).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'mid_kit__stmt 5).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'mid_kit__stmt 6).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'mid_kit__stmt 7).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'mid_kit__stmt 8).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'mid_kit__stmt 9).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'mid_kit__stmt 10).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'mid_kit__stmt 11).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'mid_kit__stmt 12).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'mid_kit__stmt 13).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'mid_kit__stmt 14).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'mid_kit__stmt 15).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'mid_kit__stmt 16).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'mid_kit__stmt 17).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'mid_kit__stmt 18).
Variable F : ltac2:(SecDietF.SzSecF.ty 'mid_kit__stmt 19).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'mid_kit__stmt 20).
Variable m : ltac2:(SecDietF.SzSecF.ty 'mid_kit__stmt 21).
Variable st : ltac2:(SecDietF.SzSecF.ty 'mid_kit__stmt 22).
Variable LB : ltac2:(SecDietF.SzSecF.ty 'mid_kit__stmt 23).
Variable X : ltac2:(SecDietF.SzSecF.ty 'mid_kit__stmt 24).
Variable Q : ltac2:(SecDietF.SzSecF.ty 'mid_kit__stmt 25).
Variable p : ltac2:(SecDietF.SzSecF.ty 'mid_kit__stmt 26).
Variable c : ltac2:(SecDietF.SzSecF.ty 'mid_kit__stmt 27).
Variable k : ltac2:(SecDietF.SzSecF.ty 'mid_kit__stmt 28).
Variable n : ltac2:(SecDietF.SzSecF.ty 'mid_kit__stmt 29).
Variable b1 : ltac2:(SecDietF.SzSecF.ty 'mid_kit__stmt 30).
Variable ctx : ltac2:(SecDietF.SzSecF.ty 'mid_kit__stmt 31).
Variable A : ltac2:(SecDietF.SzSecF.ty 'mid_kit__stmt 32).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'mid_kit__stmt 33).
Variable lst : ltac2:(SecDietF.SzSecF.ty 'mid_kit__stmt 34).
Variable nx : ltac2:(SecDietF.SzSecF.ty 'mid_kit__stmt 35).
Variable bsz : ltac2:(SecDietF.SzSecF.ty 'mid_kit__stmt 36).
Variable hs : ltac2:(SecDietF.SzSecF.ty 'mid_kit__stmt 37).
Variable tr : ltac2:(SecDietF.SzSecF.ty 'mid_kit__stmt 38).
Variable l1 : ltac2:(SecDietF.SzSecF.ty 'mid_kit__stmt 39).
Variable l2 : ltac2:(SecDietF.SzSecF.ty 'mid_kit__stmt 40).
Let st1 := set_live (delete p (a_live st)) st.
Let X1 := xquar X c k n b1 ctx l1 l2.
Let QM := mkQConc (q_loc Q) (q_glob Q) true ((c, k) :: q_pend Q).
Let S := size_of_class c.
Let AB := aslot_addr L c k.
Let UB := AB + rz_size n.
Let gq := shlen (rup n 8).
#[using="HL CI_OK st1 X1 QM S AB UB gq"] Lemma mid_kit__body : ltac:(let T := type of (fun (h : mid_kit__stmt) => h L RNG full ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st LB X Q p c k n b1 ctx A lo lst nx bsz hs tr l1 l2) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (full, (ra, (sp, (gp, (tp, (s0, (s1, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (F, (fc, (m, (st, (LB, (X, (Q, (p, (c, (k, (n, (b1, (ctx, (A, (lo, (lst, (nx, (bsz, (hs, (tr, (l1, l2))))))))))))))))))))))))))))))))))))))))) as _.
  unfold mid_stmt. 
  cbv zeta. intros ALO ARNG AR AQ BL HFK XB HIN N1 CEIL LO ms1 PM. unfold AFREE_STACK in LO.
  chg (set_live (delete p (a_live st)) st) st1.
  chg (xquar X c k n b1 ctx l1 l2) X1.
  chg (mkQConc (q_loc Q) (q_glob Q) true ((c, k) :: q_pend Q)) QM.
  (* [comment removed for export] *)
  pose proof AR as AR0. (nd_pre AR0 12%nat; intros WF RT INST THR CLS HQ HS HD HRO HRT2 AVL RT3; nd_post).
  cbn [ah_quar ah_sec ah_depot AHQ] in HQ, HS, HD.
  (nd_pre THR 6%nat; intros T0 T40 CACHES CSTATS STATS0 UNW; nd_post).
  destruct (freed_range L st X p c k n b1 ctx l1 l2 WF XB) as [HC KR].
  (pose proof (freed_live L st X p c k n b1 ctx l1 l2 XB WF) as ndP__; nd_pre ndP__ 6%nat; intros LIVE N0 FIT0 B10 AT0 CTX0; nd_post).
  (pose proof (chunk_geo L st X c k n ALO WF HC KR (proj1 N0) FIT0) as ndP__; nd_pre ndP__ 14%nat; intros HM16 UB16 ABUB ABHM HLO UBS ABCE HHI N65 NQM ABLO RUP RUP8 S8; nd_post).
  (pose proof (slot_geo L st X c k ALO WF HC KR) as ndP__; nd_pre ndP__ 13%nat; intros S16 SM16 AL16 G1 G2 G3 G4 G5 G6 G7 G8 R8 M8; nd_post).
  (pose proof (slot_sep_objects L st X c k ALO WF HC KR) as ndP__; nd_pre ndP__ 5%nat; intros DT DC DN DSO DF; nd_post).
  (pose proof (chunk_shadow_geo L st X c k n ALO WF HC KR (proj1 N0) FIT0) as ndP__; nd_pre ndP__ 9%nat; intros SE GR3 GE G0 GFS SHLO SHHI SHM1 SHM2; nd_post).
  pose proof (rz_size_facts n (proj1 N0)) as [RZ1 RZ2].
  (pose proof (alayout_t L ALO) as ndP__; nd_pre ndP__ 4%nat; intros TL1 TL2 TL3 TL4; nd_post).
  (pose proof (alayout_ctx L ALO) as ndP__; nd_pre ndP__ 5%nat; intros CL1 CL2 CL3 CL4 CL5; nd_post).
  (pose proof (alayout_depot L ALO) as ndP__; nd_pre ndP__ 10%nat; intros DL1 DL2 DL3 DL4 DL5 DL6 DL7 DL8 DL9 DL10; nd_post).
  (pose proof (alayout_stack L ALO) as ndP__; nd_pre ndP__ 3%nat; intros STK1 STK2 STK3; nd_post).
  (pose proof (alayout_space L ALO) as ndP__; nd_pre ndP__ 4%nat; intros SP1 SP2 SP3 SP4; nd_post).
  pose proof (ao_res L ALO) as RES. pose proof (ao_t L ALO) as OT. pose proof (ao_ctx L ALO) as OC. pose proof (ao_nodes L ALO) as ON. pose proof (ao_store L ALO) as OS.
  (pose proof (aobj4_int _ OT) as ndP__; nd_pre ndP__ 4%nat; intros _ _ [kT TBND] [jT TIMG]; nd_post).   (* [comment removed for export] *)
  (pose proof (aobj_int _ _ OC ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros Ci _ [kC CBND]; nd_post). (pose proof (aobj_int _ _ ON ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros Ni _ [kN NBND]; nd_post).
  (pose proof (aobj_int _ _ OS ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros Si _ [kS SBND]; nd_post). pose proof (ao_res_hi L ALO) as RHI.
  unfold aobj in RES, OT, OC, ON, OS. pose proof (ao_space L ALO) as RSP.
  pose proof (ad_t_res L ALO) as D_t_res. pose proof (ad_nodes_res L ALO) as D_n_res. pose proof (ad_store_res L ALO) as D_s_res.
  pose proof (ad_ctx_res L ALO) as D_c_res. pose proof (ad_ctx_nodes L ALO) as D_c_n. pose proof (ad_ctx_store L ALO) as D_c_s.
  unfold adisj in D_t_res, D_n_res, D_s_res, D_c_res, D_c_n, D_c_s.
  assert (D_c_t : al_ctx L + 65536 <= al_t L \/ al_t L + 4096 <= al_ctx L) by (pose proof (ad_t_ctx L ALO) as X0; unfold adisj in X0; clear -X0; lia).
  box DL7. box DL8. box DL9. box DL10. box D_t_res. box D_n_res. box D_s_res. box D_c_res. box D_c_n. box D_c_s. box D_c_t. box CL5.
  box DT. box DC. box DN. box DSO. box DF.
  word_range sp SPR.
  chg (size_of_class c) S. chg (aslot_addr L c k) AB. chg (AB + rz_size n) UB.
  assert (EAB : AB = aslot_addr L c k) by reflexivity. assert (EUB : UB = AB + rz_size n) by reflexivity. assert (ES : S = size_of_class c) by reflexivity.
  assert (EHM : fhm L c k n = UB - 16) by (unfold fhm; subst AB UB; clear; lia).
  assert (UB16' : UB mod 8 = 0) by (clear -UB16; Z.div_mod_to_equations; lia).
  (* [comment removed for export] *)
  (nd_pre (read_chunk L st X m p c k n b1 ctx l1 l2 ALO WF XB (conj (proj1 (proj2 (proj2 (CLS c HC)))) (proj2 (proj2 (proj2 (CLS c HC)))))) 7%nat; intros _ _ UJR LH SHA _ SHR; nd_post).
  fold AB in UJR, LH, SHA, SHR. fold UB in UJR, LH, SHR. fold S in UJR, SHR.
  (* [comment removed for export] *)
  pose proof AQ as AQ0. (nd_pre AQ0 6%nat; intros [QK MX] [QC ABL] [GCQ ABG] (FL & IAS & IAM) CP NUM; nd_post).
  pose proof CP as CP0. (nd_pre CP0 7%nat; intros LN1 LN2 _ _ ND2 BSI _; nd_post).
  (* [comment removed for export] *)
  unfold free_to_refill_post in PM. rewrite EHM in PM.
  (nd_pre PM 18%nat; intros id t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' m' sj' tb' junk2 j0 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 22%nat; intros MU WM MI' ST' IDR HDR' FC' SH' STATS' LSJ' UW' FL' IAS' IAM' SS' TB' LTB' FRS' FRP' FRE' LBS' DEP'; nd_post).
  cbn [ms_mem MS].
  replace (UB - 16 + 16) with UB in MU, FC', SH' by (clear; lia).
  chg (shlen (rup n 8)) gq. assert (EGQ : gq = shlen (rup n 8)) by reflexivity. clearbody gq.
  (* [comment removed for export] *)
  assert (MUn : munch (WfM (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L)) m m').
  { eapply munch_weaken; [| exact MU]. solve_sub_fp sp. }
  clear MU.
  assert (KF : kfactsM (bv_unsigned sp) (al_t L) AB S UB gq (al_nodes L) (al_store L) (al_res L) (al_ctx L) lo (shlen (rz_size n)) (shlen S)).
  { unfold kfactsM. unfold K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
    assert (GQ1 : 1 <= gq) by (rewrite EGQ, shlen_div; generalize RUP RUP8 N1; clear; intros; Z.div_mod_to_equations; lia).
    generalize CEIL LO OT OC ON OS RES RHI RSP G5 G6 ABUB UBS S8 RUP EUB SHLO SE GR3 GQ1 GFS GE SHHI. clear. intros.
    unfold iclr, AIMG_LO, AIMG_HI in *; sg_destr; repeat split; first [assumption | lia].   (* [comment removed for export] *) }
  pose proof (KM_img _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Kimg.
  pose proof (KM_low _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Klow.
  pose proof (KM_hi _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Khi.
  pose proof (KM_shad _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Kshad.
  pose proof (KM_ctx _ _ _ _ _ _ _ _ _ _ _ _ _ KF (unbxF D_c_t) (unbxF D_c_res) (unbxF D_c_n) (unbxF D_c_s)) as Kctx.
  pose proof (KM_t _ _ _ _ _ _ _ _ _ _ _ _ _ KF (unbxF D_t_res) (unbxF DL7) (unbxF DL8)) as Kt.
  pose proof (KM_res _ _ _ _ _ _ _ _ _ _ _ _ _ KF (unbxF D_t_res) (unbxF D_n_res) (unbxF D_s_res)) as Kres.
  pose proof (KM_obj _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Kobj.
  pose proof (KM_objL _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as KobjL.      (* [comment removed for export] *)
  pose proof (ad_tls_t L ALO) as D_l_t. pose proof (ad_tls_res L ALO) as D_l_r. pose proof (ad_tls_nodes L ALO) as D_l_n. pose proof (ad_tls_store L ALO) as D_l_s.
  unfold adisj in D_l_t, D_l_r, D_l_n, D_l_s. pose proof atp_lin as TLN. pose proof atop_range as ATR0.
  (* [comment removed for export] *)
  assert (NDS : forall c', ndist st1 c' = ndist st c') by (intros c'; reflexivity).
  assert (WF' : awf L st1 X1) by (apply (awf_xquar L st X p c k n b1 ctx l1 l2 XB WF); reflexivity).
  (* [comment removed for export] *)
  assert (RT' : arep_rt L m').
  { eapply arep_rt_frame; [exact MUn | exact WM | exact RT |]. unfold rt_hulls, ATP88, ATSD.
    (first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kctx; clear; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kctx; clear; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |])] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]). apply Forall_nil. }
  assert (INST' : ainstance L st1 m').
  { eapply ainstance_frame; [exact MUn | exact WM | exact INST | reflexivity | reflexivity | | |]; apply Kimg; clear; unfold AINSTANCE, AIMG_HI; lia. }
  assert (HRO' : arelro m') by (eapply arelro_frame; [exact MUn | exact HRO | apply Kimg; clear; unfold ARELRO_LO, ARELRO_HI, AIMG_HI; lia]).
  assert (HRT2' : arep_rt2 m') by (eapply arep_rt2_frame; [exact MUn | exact WM | exact HRT2 | | |]; apply Kimg; clear; unfold AIMG_HI; lia).
  assert (RT3' : arep_rt3 m') by (eapply arep_rt3_frame; [exact MUn | exact WM | exact RT3 |]; unfold rt3_hulls; repeat (apply Forall_cons; [cbn [fst snd]; apply Kimg; clear; unfold AIMG_HI; lia|]); apply Forall_nil).
  (* [comment removed for export] *)
  assert (THR' : athread L st1 X1 m').
  { unfold athread. split; [| split; [| split; [| split; [| split]]]].
    - eapply cells_frame; [exact T0 | exact MUn | exact WM |]. cbn [cells_size csize Nat.add]. apply Kt; clear; lia.
    - eapply cells_frame; [exact T40 | exact MUn | exact WM |]. cbn [cells_size csize Nat.add]. apply Kt; clear; lia.
    - intros c' Hc'. eapply acache_cells_frame; [exact MUn | exact WM | exact (CACHES c' Hc') | reflexivity | reflexivity | reflexivity |].
      unfold acache_addr. unfold K_NUM_CLASSES, K_BATCH_CLASS in *. apply Kt; clear -Hc'; lia.
    - eapply junk_frame; [exact CSTATS | exact MUn | exact WM | intros _; apply Kt; clear; lia].
    - exists sj'. split; [exact STATS' | exact LSJ'].
    - exact UW'. }
  idtac "CHECKPOINT-M1".
  (* [comment removed for export] *)
  assert (RC : forall c1 c2, c1 < c2 -> aregion L c1 + K_REGION <= aregion L c2) by (intros; apply regions_sep; assumption).
  assert (CLS' : forall c'', 1 <= c'' < K_NUM_CLASSES ->
      aregion_cells L st1 m' c'' /\ afreearray L st1 X1 m' c'' /\ aslots L st1 X1 m' c'' /\ aslot_shadow L st1 X1 m' c'').
  { intros c'' Hc''. (nd_pre (CLS c'' Hc'') 4%nat; intros REG FARR SLOTS SHADOW; nd_post).
    pose proof WF as WF0. (nd_pre WF0 7%nat; intros _ _ SAL _ _ PERC _; nd_post).
    (nd_pre (PERC c'' Hc'') 12%nat; intros Q1 Q2 Q3 Q4 Q5 Q6 Q7 QLENF QLENC QCNTB QND QRANGE; nd_post).
    pose proof (size_of_class_facts c'' Hc'') as [QS QS16].
    pose proof (aregion_mod L c'' SAL) as RM''.
    unfold K_NUM_CLASSES in Hc''.
    assert (RI : al_res L <= aregion L c'' /\ aregion L c'' + K_REGION <= al_space_beg L + K_SPACE_SIZE
                 /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104 /\ al_res L + 4096 <= aregion L c'').
    { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc'' RSP. lia. }
    (nd_pre RI 4%nat; intros RI1 RI2 RI3 RI4; nd_post).
    assert (PC0 : aregion L c <= AB /\ AB + S <= aregion L c + K_FREEARR_OFF /\ AB + S <= aregion L c + c_allocated_user (get_cls st c)) by (clear -G1 G2 G3 G4; lia).
    split; [| split; [| split]].
    - eapply aregion_cells_frame; [exact MUn | exact WM | exact REG | reflexivity | reflexivity | reflexivity | reflexivity |].
      unfold aregion_info, ARI_STRIDE, K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
      apply Kres; clear -Hc'' RSP G6 S8 EUB RES RHI; lia.
    - eapply afreearray_frame; [exact MUn | exact WM | exact FARR | reflexivity | reflexivity | reflexivity | exact QLENF | exact Q5 | | clear -Q6; lia |].
      + assert (FA1 : aregion L c'' + K_FREEARR_OFF <= afreearr L c'' /\ afreearr L c'' + c_mapped_free_array (get_cls st c'') <= aregion L c'' + K_REGION).
        { unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q6. lia. }
        destruct FA1 as [FA1 FA2].
        apply Kres; [clear -RI1 FA1; unfold K_FREEARR_OFF in *; lia | clear -RI2 RI3 FA2; lia | clear -Q5 Q6; lia |].
        pose proof (farr_vs_user L c'' c _ _ AB S (proj1 PC0) (proj1 (proj2 PC0)) FA1 FA2) as D. clear -D ABUB S8 EUB. lia.
      + assert (FA1 : aregion L c'' + K_FREEARR_OFF <= afreearr L c'' /\ afreearr L c'' + c_mapped_free_array (get_cls st c'') <= aregion L c'' + K_REGION).
        { unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q6. lia. }
        destruct FA1 as [FA1 FA2].
        apply Kshad.
        * rewrite shad_div. unfold ASHOFF, K_FREEARR_OFF in *. clear -RI1 FA1 RES RHI. Z.div_mod_to_equations. lia.
        * rewrite shad_div, shlen_div. unfold ASHOFF, K_SPACE_SIZE in *. clear -RI2 RI3 FA2 RES RHI. Z.div_mod_to_equations. lia.
        * apply shlen_nonneg. clear -Q5 Q6. lia.
        * pose proof (farr_vs_user L c'' c _ _ UB (rup n 8) ltac:(clear -PC0 ABUB; lia) ltac:(clear -PC0 UBS; lia) FA1 FA2) as D.
          assert (AM : afreearr L c'' mod 8 = 0) by (unfold afreearr, K_FREEARR_OFF; clear -RM''; Z.div_mod_to_equations; lia).
          rewrite EGQ. destruct D as [D|D]; [left; apply shad_sep; [exact D| exact AM] | right; apply shad_sep; [exact D| clear -UB16; Z.div_mod_to_equations; lia]].
    - (* [comment removed for export] *)
      eapply (aslots_update_gen L _ m m' MUn WM st st1 X X1 c''); [exact SLOTS | apply NDS | reflexivity | reflexivity | |].
      + intros k'' Hk''.
        (pose proof (slot_geo L st X c'' k'' ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) Hk'') as ndP__; nd_pre ndP__ 12%nat; intros T16 TM16 TAL P1 P2 P3 P4 P5 P6 P7 P8 _; nd_post).
        assert (D1 : (c'' = c /\ k'' = k) \/ (c'' <> c \/ k'' <> k)) by (clear; lia). destruct D1 as [[Ec Ek]|NE1].
        * (* [comment removed for export] *)
          subst c'' k''. right.
          subst X1. rewrite (busy_of_xquar L st X p c k n b1 ctx l1 l2 XB WF). rewrite !Z.eqb_refl. cbn [andb].
          unfold aslot_busy, bquar. cbn [xb_st xb_class xb_n xb_b1 xb_ctx xb_slot bstate_byte]. unfold xb_user, xb_hdr, xb_alloc. cbn [xb_class xb_slot xb_n].
          rewrite <- EAB. fold S. rewrite <- EUB.
          split; [| split].
          -- intros R16. pose proof (rz_gt16 n (proj1 N0) R16) as R32. destruct (LH R16) as [LC LJ]. split.
             ++ eapply cells_frame; [exact LC | exact MUn | exact WM |]. cbn [cells_size csize Nat.add].
                apply Kres; clear -G5 G6 RSP RES RHI S16 EUB R32 S8; unfold K_SPACE_SIZE in *; lia.
             ++ eapply junk_frame; [exact LJ | exact MUn | exact WM |]. intros Hp.
                apply Kres; clear -G5 G6 RSP RES RHI S16 EUB R32 S8 Hp; unfold K_SPACE_SIZE in *; lia.
          -- exists 3. split; [reflexivity|]. exact HDR'.
          -- replace (S - rz_size n) with (8 + (S - rz_size n - 8)) by (clear; lia).
             apply (junk_merge m' UB 8 (S - rz_size n - 8)); [| | clear; lia | clear -S8; lia].
             ++ pose proof (junk_of_cells m' _ _ FC') as J. cbn in J. exact J.
             ++ eapply junk_frame; [exact UJR | exact MUn | exact WM |]. intros Hp.
                apply Kres; clear -G5 G6 RSP RES RHI S16 EUB ABUB S8 Hp; unfold K_SPACE_SIZE in *; lia.
        * (* [comment removed for export] *)
          left.
          assert (T2 : (c =? c'') && (k =? k'') = false).
          { destruct (Z.eqb_spec c c'') as [E|]; [| reflexivity]. destruct (Z.eqb_spec k k'') as [E'|]; [| reflexivity]. exfalso. clear -NE1 E E'. lia. }
          split; [subst X1; rewrite (busy_of_xquar L st X p c k n b1 ctx l1 l2 XB WF), T2; reflexivity|]. split.
          -- assert (DW9 : aslot_addr L c'' k'' + size_of_class c'' <= AB \/ AB + S <= aslot_addr L c'' k'').
             { pose proof (slots_sep_any L st X c'' k'' c k ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) HC Hk'' KR NE1) as D.
               rewrite <- EAB, <- ES in D. exact D. }
             apply Kres; [clear -P5 RSP; lia | clear -P6 RSP; unfold K_SPACE_SIZE in *; lia | clear -T16; lia | clear -DW9 ABUB S8 EUB; lia].
          -- intros b Hb. (nd_pre (busy_of_Some_facts X c'' k'' b Hb) 3%nat; intros IB CB' KB'; nd_post). split; [exact CB'|]. split; [exact KB'|]. exact (awf_fits L st X b WF IB).
      + intros POS''.
        set (AU := aregion L c'' + c_allocated_user (get_cls st c'')) in *.
        assert (U0 : aregion L c'' <= AU /\ AU + (c_mapped_user (get_cls st c'') - c_allocated_user (get_cls st c'')) <= aregion L c'' + K_FREEARR_OFF) by (subst AU; clear -Q1 Q2; lia).
        destruct U0 as [U0 U0'].
        assert (U1 : c'' = c -> aregion L c + c_allocated_user (get_cls st c) <= AU) by (intros E; subst AU; rewrite <- E; clear; lia).
        apply Kres; [clear -RI4 Q1 U0; lia | subst AU; clear -Q1 Q2 RI2 RI3; unfold K_FREEARR_OFF, K_REGION, K_SPACE_SIZE in *; lia | clear -POS''; lia |].
        pose proof (undist_vs_user L c'' c _ _ AB S (c_allocated_user (get_cls st c)) (proj1 PC0) (proj2 (proj2 PC0)) ltac:(clear -G3 G4; lia) U1 U0 U0') as D.
        clear -D ABUB S8 EUB. lia.
    - (* [comment removed for export] *)
      eapply (aslot_shadow_update_gen L _ m m' MUn WM st st1 X X1 c''); [exact SHADOW | apply NDS | reflexivity | reflexivity | | | apply shlen_nonneg; clear -QS; lia].
      + intros k'' Hk''.
        (pose proof (slot_geo L st X c'' k'' ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) Hk'') as ndP__; nd_pre ndP__ 12%nat; intros T16 TM16 TAL P1 P2 P3 P4 P5 P6 P7 P8 _; nd_post).
        assert (D1 : (c'' = c /\ k'' = k) \/ (c'' <> c \/ k'' <> k)) by (clear; lia). destruct D1 as [[Ec Ek]|NE1].
        * (* [comment removed for export] *)
          subst c'' k''. right.
          subst X1. rewrite (busy_of_xquar L st X p c k n b1 ctx l1 l2 XB WF). rewrite !Z.eqb_refl. cbn [andb].
          unfold slot_shadow_bytes, bquar. cbn [xb_n xb_st]. rewrite <- EAB. fold S.
          eapply cells_frame in SHA; [| exact MUn | exact WM | cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by (clear -GR3; lia);
                                       apply Kshad; [clear -SHLO; lia| clear -SHHI GR3 GFS SE G0 GE; lia| clear -GR3; lia| left; clear -SE; lia]].
          eapply cells_frame in SHR; [| exact MUn | exact WM | cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by (clear -GFS GE GR3; unfold granules in *; lia);
                                       apply Kshad; [clear -SHLO SE GR3 G0 EGQ; lia| clear -SHHI GR3 GFS SE G0 GE EGQ; lia| clear -GFS GE GR3; unfold granules in *; lia| right; clear -EGQ; lia]].
          rewrite EGQ in SH'.
          replace (shad UB) with (shad AB + Z.of_nat (Z.to_nat (shlen (rz_size n)))) in SH' by (clear -SE GR3; lia).
          rewrite EGQ in SHR, G0.
          replace (shad UB + shlen (rup n 8)) with (shad AB + Z.of_nat (Z.to_nat (shlen (rz_size n))) + Z.of_nat (Z.to_nat (shlen (rup n 8)))) in SHR by (clear -SE GR3 G0; lia).
          pose proof (cb_app m' _ _ _ _ _ SHA (cb_app m' _ _ _ _ _ SH' SHR)) as FIN.
          assert (GE' : shlen (rup n 8) = granules n) by (rewrite <- EGQ; exact GE). rewrite <- GE'.
          replace (Z.to_nat (shlen (rz_size n)) + (Z.to_nat (shlen (rup n 8)) + Z.to_nat (shlen S - shlen (rz_size n) - shlen (rup n 8))))%nat with (Z.to_nat (shlen S)) in FIN
            by (clear -GR3 G0 GE' GFS; unfold granules in *; lia).
          rewrite <- ?app_assoc in FIN. rewrite <- ?app_assoc. exact FIN.
        * left. assert (T2 : (c =? c'') && (k =? k'') = false).
          { destruct (Z.eqb_spec c c'') as [E|]; [| reflexivity]. destruct (Z.eqb_spec k k'') as [E'|]; [| reflexivity]. exfalso. clear -NE1 E E'. lia. }
          split; [subst X1; rewrite (busy_of_xquar L st X p c k n b1 ctx l1 l2 XB WF), T2; reflexivity|].
          assert (DW : aslot_addr L c'' k'' + size_of_class c'' <= AB \/ AB + S <= aslot_addr L c'' k'').
          { pose proof (slots_sep_any L st X c'' k'' c k ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) HC Hk'' KR NE1) as D.
            rewrite <- EAB, <- ES in D. exact D. }
          pose proof (slot_aligned L c'' k'' SAL ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia)) as AL''.
          apply Kshad.
          -- rewrite shad_div. unfold ASHOFF. clear -P7 RES RHI. Z.div_mod_to_equations. lia.
          -- rewrite shad_div, shlen_div. unfold ASHOFF in *. clear -P8 T16. Z.div_mod_to_equations. lia.
          -- apply shlen_nonneg. clear -T16; lia.
          -- rewrite EGQ. destruct DW as [D|D].
             ++ left. eapply Z.le_trans; [apply shad_sep; [exact D| clear -AL''; Z.div_mod_to_equations; lia]|]. clear -SE GR3; lia.
             ++ right. apply shad_sep; [clear -D UBS; lia| exact UB16'].
      + intros POS''.
        set (AU := aregion L c'' + c_allocated_user (get_cls st c'')) in *.
        assert (U0 : aregion L c'' <= AU /\ AU + (c_mapped_user (get_cls st c'') - c_allocated_user (get_cls st c'')) <= aregion L c'' + K_FREEARR_OFF) by (subst AU; clear -Q1 Q2; lia).
        destruct U0 as [U0 U0'].
        assert (U1 : c'' = c -> aregion L c + c_allocated_user (get_cls st c) <= AU) by (intros E; subst AU; rewrite <- E; clear; lia).
        pose proof (undist_vs_user L c'' c _ _ UB (rup n 8) (c_allocated_user (get_cls st c)) ltac:(clear -PC0 ABUB; lia) ltac:(clear -PC0 UBS; lia) ltac:(clear -G3 G4; lia) U1 U0 U0') as D.
        assert (AM : AU mod 8 = 0) by (subst AU; pose proof (mod16_of_class _ _ Q3 QS16 ltac:(clear -QS; lia)) as AM; clear -AM RM''; Z.div_mod_to_equations; lia).
        apply Kshad.
        * rewrite shad_div. unfold ASHOFF. clear -U0 RI4 RES RHI. Z.div_mod_to_equations. lia.
        * rewrite shad_div, shlen_div. unfold ASHOFF, K_FREEARR_OFF, K_REGION, K_SPACE_SIZE in *. clear -U0' RI2 RI3 RES RHI. Z.div_mod_to_equations. lia.
        * clear -POS''; lia.
        * rewrite EGQ. destruct D as [D|D]; [left; apply shad_sep; [exact D| exact AM] | right; apply shad_sep; [exact D| exact UB16']].
  }
  idtac "CHECKPOINT-M2".
  (* [comment removed for export] *)
  assert (AVL' : forall c'', 1 <= c'' < K_NUM_CLASSES -> ashadow_avail L st1 m' c'').
  { intros c'' Hc''. pose proof WF as WF0. (nd_pre WF0 7%nat; intros _ _ SAL _ _ PERC _; nd_post).
    (nd_pre (PERC c'' Hc'') 8%nat; intros Q1 Q2 Q3 Q4 Q5 Q6 Q7 _; nd_post).
    pose proof (size_of_class_facts c'' Hc'') as [QS QS16]. pose proof (aregion_mod L c'' SAL) as RM''.
    unfold K_NUM_CLASSES in Hc''.
    assert (RI : al_res L + 4096 <= aregion L c'' /\ aregion L c'' + K_REGION <= al_space_beg L + K_SPACE_SIZE /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
    { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc'' RSP. lia. }
    (nd_pre RI 3%nat; intros RI1 RI2 RI3; nd_post).
    assert (PC0 : aregion L c <= AB /\ AB + S <= aregion L c + K_FREEARR_OFF /\ AB + S <= aregion L c + c_allocated_user (get_cls st c)) by (clear -G1 G2 G3 G4; lia).
    eapply ashadow_avail_frame; [exact MUn | exact WM | exact (AVL c'' ltac:(unfold K_NUM_CLASSES; exact Hc'')) | reflexivity | reflexivity | |].
    - intros POS''. set (AU := aregion L c'' + c_mapped_user (get_cls st c'')) in *.
      assert (U0 : aregion L c'' <= AU /\ AU + (K_FREEARR_OFF - c_mapped_user (get_cls st c'')) <= aregion L c'' + K_FREEARR_OFF) by (subst AU; clear -Q1 Q2; lia).
      destruct U0 as [U0 U0'].
      assert (U1 : c'' = c -> aregion L c + c_mapped_user (get_cls st c) <= AU) by (intros E; subst AU; rewrite <- E; clear; lia).
      pose proof (undist_vs_user L c'' c _ _ UB (rup n 8) (c_mapped_user (get_cls st c)) ltac:(clear -PC0 ABUB; lia) ltac:(clear -PC0 UBS G3; lia) G4 U1 U0 U0') as D.
      assert (AM : AU mod 8 = 0) by (subst AU; generalize Q4 RM''; clear; unfold K_USER_MAP; intros; Z.div_mod_to_equations; lia).
      apply Kshad.
      + rewrite shad_div. unfold ASHOFF. clear -U0 RI1 RES RHI. Z.div_mod_to_equations. lia.
      + rewrite shad_div, shlen_div. unfold ASHOFF, K_FREEARR_OFF, K_REGION, K_SPACE_SIZE in *. clear -U0' RI2 RI3 RES RHI. Z.div_mod_to_equations. lia.
      + clear -POS''; lia.
      + rewrite EGQ. destruct D as [D|D]; [left; apply shad_sep; [exact D| exact AM] | right; apply shad_sep; [exact D| exact UB16']].
    - intros POS''. set (AU := afreearr L c'' + c_mapped_free_array (get_cls st c'')) in *.
      assert (FA : aregion L c'' + K_FREEARR_OFF <= AU /\ AU + (K_FREEARR_MAX - c_mapped_free_array (get_cls st c'')) <= aregion L c'' + K_REGION).
      { subst AU. unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q5 Q6. lia. }
      destruct FA as [FA1 FA2].
      pose proof (farr_vs_user L c'' c _ _ UB (rup n 8) ltac:(clear -PC0 ABUB; lia) ltac:(clear -PC0 UBS; lia) FA1 FA2) as D.
      assert (AM : AU mod 8 = 0) by (subst AU; generalize Q7 RM''; clear; unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAP; intros; Z.div_mod_to_equations; lia).
      apply Kshad.
      + rewrite shad_div. unfold ASHOFF, K_FREEARR_OFF in *. clear -FA1 RI1 RES RHI. Z.div_mod_to_equations. lia.
      + rewrite shad_div, shlen_div. unfold ASHOFF, K_SPACE_SIZE in *. clear -FA2 RI2 RI3 RES RHI. Z.div_mod_to_equations. lia.
      + clear -POS''; lia.
      + rewrite EGQ. destruct D as [D|D]; [left; apply shad_sep; [exact D| exact AM] | right; apply shad_sep; [exact D| exact UB16']]. }
  idtac "CHECKPOINT-M3".
  (* [comment removed for export] *)
  assert (HS' : ASEC L st1 X1 m').
  { eapply (hs_frame _ HL L st st1 X X1 m m'); [exact HS | exact MUn | exact WM | |].
    - unfold sec_untouched, aknown. unfold AINSTANCE, K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
      assert (SHB : 2201439137792 <= shad UB /\ shad UB + gq <= 17594333495296) by (clear -SHLO SHHI SE GR3 GFS GE EGQ G0; lia).
      (* [comment removed for export] *)
      assert (SHB1 : shad (al_space_beg L) + 536870912 <= shad (aregion L c)).
      { rewrite !shad_div. unfold aregion, K_REGION, K_NUM_CLASSES in *. change (2^32) with 4294967296 in *. clear -HC. Z.div_mod_to_equations. lia. }
      assert (SHB2 : shad (aregion L c) + shlen (c_mapped_user (get_cls st c)) <= shad (al_space_beg L) + 17179869184).
      { (pose proof (alayout_space L ALO) as ndP__; nd_pre ndP__ 4%nat; intros _ _ SPal _; nd_post). rewrite !shad_div, shlen_div. unfold aregion, K_REGION, K_ALIGN, K_FREEARR_OFF, K_NUM_CLASSES in *. change (2^32) with 4294967296 in *.
        clear -HC G4 SPal. Z.div_mod_to_equations. lia. }
      (* [comment removed for export] *)
      apply Forall_cons; [cbn [fst snd]; intros a Ha; do 4 right; left; clear -Ha CEIL LO; lia |].
      do 3 (apply Forall_cons; [cbn [fst snd]; intros a Ha; left; left; clear -Ha; unfold AIMG_HI, AINSTANCE; lia |]).   (* [comment removed for export] *)
      apply Forall_cons; [cbn [fst snd]; intros a Ha; do 5 right; left; clear -Ha OT TBND TIMG; lia |].
      apply Forall_cons; [cbn [fst snd]; intros a Ha; do 7 right; left; clear -Ha G5 G6 ABUB S8 EUB RSP; lia |].
      apply Forall_cons; [cbn [fst snd]; intros a Ha; right; left; clear -Ha SE GR3 GFS GE EGQ G0 SHM1 SHM2 SHB1 SHB2; lia |].
      apply Forall_cons; [cbn [fst snd]; intros a Ha; do 8 right; left; clear -Ha; lia |].
      apply Forall_cons; [cbn [fst snd]; intros a Ha; do 9 right; left; clear -Ha; lia |].
      apply Forall_nil.
    - eapply (sec_same_free st p c n); [exact LIVE| apply same_core_refl| apply Permutation_refl]. }
  assert (BL' : ablocks L st1 X1 (lb_remove p LB)) by (exact (ablocks_xquar L st X p c k n b1 ctx l1 l2 XB LB st1 eq_refl BL)).
  assert (FKD : forall cls FA sz, In (mkABlock (ABFake cls) FA sz) LB -> al_fake L <= FA /\ 0 <= sz /\ FA + sz <= al_fake L + 11571200)
    by (intros cls FA sz Hin; exact (proj1 (proj2 BL) cls FA sz Hin)).
  pose proof (ao_fake L ALO) as FKO. (pose proof (aobj_int _ _ FKO ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros FKi FKa [kF FBND]; nd_post). unfold aobj in FKO.   (* [comment removed for export] *)
  pose proof (ad_t_fake L ALO) as D_t_f. pose proof (ad_fake_res L ALO) as D_f_res. pose proof (ad_nodes_fake L ALO) as D_n_f. pose proof (ad_store_fake L ALO) as D_s_f.
  unfold adisj in D_t_f, D_f_res, D_n_f, D_s_f. box D_t_f. box D_f_res. box D_n_f. box D_s_f.
  assert (HFK' : AFK L (lb_remove p LB) m').
  { eapply (hf_blocks _ HL L LB); [eapply (hf_frame _ HL L LB m m'); [exact HFK | exact MUn | exact WM |] |].
    - pose proof (ao_dtls L ALO) as DTO. (pose proof (aobj4_int _ DTO) as ndP__; nd_pre ndP__ 4%nat; intros _ _ [kD DBND] [jD DIMG]; nd_post). unfold aobj in DTO.   (* [comment removed for export] *)
      pose proof (ad_t_dtls L ALO) as D1. pose proof (ad_dtls_res L ALO) as D2. pose proof (ad_nodes_dtls L ALO) as D3. pose proof (ad_store_dtls L ALO) as D4.
      unfold adisj in D1, D2, D3, D4.
      unfold fake_untouched. unfold K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
      assert (SHF : (shad (al_fake L) + shlen 11571200 <= shad UB \/ shad UB + gq <= shad (al_fake L))
                    /\ 2148239360 <= shad (al_fake L) /\ shad (al_fake L) + shlen 11571200 <= 17594333495296).   (* [comment removed for export] *)
      { split; [| rewrite shad_div, shlen_div; unfold ASHOFF; pose proof atop_range as AR8; clear -FKO FKi FBND AR8; Z.div_mod_to_equations; lia].
        pose proof D_f_res as DFR. unbox DFR. rewrite EGQ. destruct DFR as [D|D].
        - left. apply shad_sep; [| clear -FKO FKi FBND; Z.div_mod_to_equations; lia]. clear -D RSP G5 ABUB. lia.
        - right. apply shad_sep; [| exact UB16']. clear -D RSP G6 UBS. lia. }
      (nd_pre SHF 3%nat; intros SHF1 SHF2 SHF3; nd_post).
      assert (SHB : 2201439137792 <= shad UB /\ shad UB + gq <= 17594333495296) by (clear -SHLO SHHI SE GR3 GFS GE EGQ G0; lia).
      pose proof D_t_f as DTF; unbox DTF. pose proof D_f_res as DFR; unbox DFR. pose proof D_n_f as DNF; unbox DNF. pose proof D_s_f as DSF; unbox DSF.
      (apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | idtac]]]]]]]]]).
      apply Forall_nil.
    - intros cls FA sz. rewrite (In_lb_remove p LB). cbn. split; [intros [Hin _]; exact Hin| intros Hin; split; [exact Hin| discriminate]]. }
  idtac "CHECKPOINT-M4".
  (* [comment removed for export] *)
  assert (SEPQ : forall q, In q (q_loc Q ++ q_glob Q) -> AB + S <= abatch_addr L (qb_slot q) \/ abatch_addr L (qb_slot q) + 8192 <= AB).
  { intros q Hq. (nd_pre (bslot_busy L st X Q CP q Hq) 5%nat; intros yq Hyq Syq Cyq Kyq; nd_post).
    pose proof (slots_sep_any L st X c k K_BATCH_CLASS (qb_slot q) ALO WF HC (K24) KR (bslot_range L st X Q WF CP q Hq)
                  ltac:(rewrite <- Cyq, <- Kyq; apply (other_key (AHQ DI ASEC AFK) L st X m (BLive p) c k n b1 ctx l1 l2 AR XB); [exact Hyq| rewrite Syq; discriminate])) as D.
    rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
  assert (BGEO : forall q, In q (q_loc Q ++ q_glob Q) ->
      al_res L + 4096 <= abatch_addr L (qb_slot q) /\ abatch_addr L (qb_slot q) + 8192 <= al_res L + 137439023104).
  { intros q Hq. (pose proof (slot_geo L st X K_BATCH_CLASS (qb_slot q) ALO WF (K24) (bslot_range L st X Q WF CP q Hq)) as ndP__; nd_pre ndP__ 10%nat; intros _ _ _ P1 P2 P3 P4 P5 P6 _; nd_post).
    rewrite size_of_class_24 in P2, P6. unfold abatch_addr. unfold K_SPACE_SIZE in P6. change (2^37) with 137438953472 in P6.
    generalize P1 P2 P5 P6 RSP; clear; intros. lia. }
  assert (BFR : forall q, In q (q_loc Q ++ q_glob Q) -> disjoint_from (WfM (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L)) (abatch_addr L (qb_slot q)) 8192).
  { intros q Hq. destruct (BGEO q Hq) as [F3 F4]. pose proof (SEPQ q Hq) as SQ. apply Kres; clear -F3 F4 RES RHI SQ ABUB S8 EUB; lia. }
  assert (HQ' : AQUAR_at L st1 X1 QM m').
  { subst QM. unfold AQUAR_at. cbn [q_loc q_glob q_ia q_pend].
    change (a_qloc st1) with (a_qloc st). change (a_qglob st1) with (a_qglob st). change (a_qloc_bytes st1) with (a_qloc_bytes st). change (a_qglob_bytes st1) with (a_qglob_bytes st).
    split; [| split; [| split; [| split; [| split]]]].
    - eapply (aquar_glob_const_frame _ m m' MUn WM); [exact (conj QK MX) | apply Kimg; clear; unfold AQ_MAX, AIMG_HI; lia | apply Kimg; clear; unfold AQ_MUTEX, AIMG_HI; lia].
    - eapply (aqcache_frame L _ m m' MUn WM); [exact (conj QC ABL) | unfold aq_tcache; apply Kt; clear; lia |].
      intros q Hq. unfold Q_BATCH_BYTES. apply BFR. apply in_or_app. left. exact Hq.
    - eapply (aqcache_frame L _ m m' MUn WM); [exact (conj GCQ ABG) | apply Kimg; clear; unfold AQ_GCACHE, AINSTANCE, AIMG_HI; lia |].
      intros q Hq. unfold Q_BATCH_BYTES. apply BFR. apply in_or_app. right. exact Hq.
    - split; [exact FL'|]. split; [exact IAS'|]. intros _ j Hj. apply IAM'. revert Hj. clear. unfold AIA_MAP1_LEN. cbn. lia.
    - subst X1. eapply (qcoupled_pend L st st1 X); [exact CP | reflexivity | reflexivity | | |].
      + exact (HQ_xquar X p c k n b1 ctx l1 l2 XB).
      + exact (HB_xquar X p c k n b1 ctx l1 l2 XB).
      + exact (FQ_X L st X p c k n b1 ctx l1 l2 XB WF).
    - exact NUM. }
  idtac "CHECKPOINT-M5".
  (* [comment removed for export] *)
  assert (HBK : forall blk, In blk (lb_remove p LB) -> disjoint_from (WfM (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L)) (ab_addr blk) (ab_size blk)).
  { intros [[q|cls] A' n'] Hin; cbn [ab_addr ab_size]; apply (proj1 (In_lb_remove p LB _)) in Hin; destruct Hin as [Hin NEp]; cbn [ab_kind] in NEp.
    - destruct (proj1 BL q A' n' Hin) as [(b & Hb & Sb & Ub & Nb)|(mb & msz & Lp & EUA & Gs)].
      + assert (NEq : xb_st b <> BLive p) by (rewrite Sb; intros E; apply NEp; congruence).
        pose proof (other_key (AHQ DI ASEC AFK) L st X m (BLive p) c k n b1 ctx l1 l2 AR XB b Hb NEq) as NE1.
        destruct (busy_slot_range L st X b WF Hb) as [HCb HKb].
        pose proof (awf_fits L st X b WF Hb) as FIT. unfold xb_fits in FIT. rewrite Sb in FIT.
        unfold xb_user, xb_alloc in Ub. subst A' n'.
        set (cb := xb_class b) in *. set (kb := xb_slot b) in *.
        (pose proof (slot_geo L st X cb kb ALO WF HCb HKb) as ndP__; nd_pre ndP__ 12%nat; intros T16 TM16 TAL P1 P2 P3 P4 P5 P6 P7 P8 _; nd_post).
        pose proof (slots_sep_any L st X cb kb c k ALO WF HCb HC HKb KR ltac:(clear -NE1; lia)) as D9. rewrite <- EAB, <- ES in D9.
        apply Kres; [clear -P5 RSP FIT; lia | clear -P6 RSP FIT; unfold K_SPACE_SIZE in *; lia | clear -FIT; lia | clear -D9 FIT ABUB S8 EUB; lia].
      + (* [comment removed for export] *)
        cbn [sec_wf1] in Gs. (nd_pre Gs 7%nat; intros Gs1 Gs2 Gs3 Gs4 Gs5 Gs6 (Ct & Cc & Cr & Cp & Cn & Cs & Cf & Cd); nd_post).
        pose proof (sec_facts n' ltac:(clear -Gs5; lia) Gs6) as SF. subst A'. unfold SEC_UOFF, K_HIGH_MEM in *.
        unfold ablk, KLS, AIMG_HI in Gs2.   (* [comment removed for export] *)
        apply Kobj; clear -Gs2 Gs3 Gs4 Gs5 SF Ct Cr Cn Cs; lia.
    - (nd_pre (FKD cls A' n' Hin) 3%nat; intros K1 K2 K3; nd_post). atop_facts.
      pose proof D_t_f as DTF; unbox DTF. pose proof D_f_res as DFR; unbox DFR. pose proof D_n_f as DNF; unbox DNF. pose proof D_s_f as DSF; unbox DSF.
      apply Kobj; [clear -K1 K3 FKO FKi FBND; lia | clear -K3 FKO FKi FBND; lia | exact K2 | clear -K1 K3 DTF; lia
                  | clear -K1 K3 DFR; lia | clear -K1 K3 DNF; lia | clear -K1 K3 DSF; lia]. }
  assert (HFS : forall cls FA sz, In (mkABlock (ABFake cls) FA sz) (lb_remove p LB) -> forall a', FA <= a' < FA + sz ->
      disjoint_from (WfM (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L)) (shad a') 1).
  { intros cls FA sz Hin a' Ha'. apply (proj1 (In_lb_remove p LB _)) in Hin. destruct Hin as [Hin _].
    (nd_pre (FKD cls FA sz Hin) 3%nat; intros K1 K2 K3; nd_post). atop_facts.
    apply Kshad; [rewrite shad_div; unfold ASHOFF; clear -K1 FKO FKi FBND Ha'; Z.div_mod_to_equations; lia
                 | rewrite shad_div; unfold ASHOFF; clear -K3 FKO FKi FBND Ha'; Z.div_mod_to_equations; lia | clear; lia |].
    pose proof D_f_res as DFR; unbox DFR. destruct DFR as [D|D].
    - left. rewrite (shad_div a'), (shad_div UB). clear -D Ha' K3 RSP G5 ABUB UB16'. Z.div_mod_to_equations. lia.
    - right. rewrite EGQ, shlen_div, (shad_div a'), (shad_div UB). unfold K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
      clear -D Ha' K1 RSP G6 UBS RUP8 UB16'. Z.div_mod_to_equations. lia. }
  (* [comment removed for export] *)
  assert (TLSK : forall TA tk, ATPv + -200 <= TA -> TA + tk <= ATPv + 312 -> 0 <= tk ->
      disjoint_from (WfM (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L)) TA tk).
  { intros TA tk TH1 TH2 TH3. pose proof ATPv_img as TI. apply Kimg; clear -TH1 TH2 TH3 TI; unfold AIMG_HI; lia. }
  assert (TLSS : forall a', ATPv + -200 <= a' < ATPv + 312 ->
      disjoint_from (WfM (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L)) (shad a') 1).
  { intros a' Ha'. pose proof ATPv_img as TI. apply Klow; clear -Ha' TI; try (rewrite shad_div; unfold ASHOFF); try Z.div_mod_to_equations; lia. }
  assert (PSP : shad UB + gq <= shad ATOP).
  { rewrite EGQ, shlen_div, (shad_div UB), (shad_div ATOP). atop_facts. clear -UBS G8 ABCE CEIL LO RUP8 UB16'. Z.div_mod_to_equations. lia. }
  (* [comment removed for export] *)
  split; [| split; [exact BL'| split; [exact HFK'|]]].
  - split; [exact WF'|]. split; [exact RT'|]. split; [exact INST'|]. split; [exact THR'|]. split; [exact CLS'|].
    split; [exact HQ'|]. split; [exact HS'|]. split; [exact DEP'|]. split; [exact HRO'|]. split; [exact HRT2'|]. split; [exact AVL'| exact RT3'].
  - eapply (aheap_pres_mid CI); [exact KF | exact CI_OK | exact MUn | exact WM | exact HBK | exact HFS | exact PSP | exact TLSK | exact TLSS | apply Klow; unfold AIMSH_LO, AIMSH_LEN; clear; lia
      | rewrite <- (ao_ahm_eq L ALO); unfold AAHM_SZ; pose proof (ao_ahm L ALO) as OAH; pose proof (aobj_img _ _ OAH ltac:(clear; lia)) as OAHI;
      pose proof (ad_ahm_t L ALO) as DA1; pose proof (ad_ahm_res L ALO) as DA2; pose proof (ad_ahm_nodes L ALO) as DA3; pose proof (ad_ahm_store L ALO) as DA4;
      unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI, adisj in OAH, OAHI, DA1, DA2, DA3, DA4; apply Kobj; clear -OAH OAHI DA1 DA2 DA3 DA4; lia].
Qed.
End Zd1.
#[using="HL CI_OK"] Theorem mid_kit : ltac:(let t := eval cbv delta [mid_kit__stmt] in mid_kit__stmt in exact t).
Proof. exact mid_kit__body. Qed.
End S.
End CANSEC1.
End TwB.
End AFreeMid.

(* [comment removed for export] *)
Module AFreeStoreR.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Import InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecFacts AImg AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AQConst AMalloc_iface. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitR__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepStore__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeRead F_afree_tail. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_front__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_arep__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_tabscan__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASF_fast__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepStore__A3W.ARepStore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AFreeModel OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.AFreeGeo OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRead OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tail OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_afree_icpt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.F_afree_arep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_tabscan__A3W.AFreeStoreK OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.AFreeStore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_fast__A3W.F_afree_arepR.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac sg_set := let GG := fresh "GG" in (match goal with |- ?G => set (GG := G) end).
Local Ltac sg_unset := match goal with |- ?G => is_var G; subst G end.
Local Ltac sg_destr := sg_set; repeat match goal with H : _ /\ _ |- _ => destruct H end; sg_unset.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation Wf sp t UB gq nodes store lst eb gl :=
  ([(sp - 4096, sp); (0xab308, 0xab330); (0xaf800, 0x130830); (0x13e088, 0x13e08c); (ADEPOT_LO, ADEPOT_HI);
    (t + 80, t + 112); (t + 2128, t + 2132); (t + 2784, t + 2792); (t + 2800, t + 3169);
    (UB - 16, UB + 8); (shad UB, shad UB + gq);
    (nodes, nodes + 1048576); (store, store + 8388608);
    (lst, lst + qsz lst); (eb, eb + 8192); (gl, gl + 8)]%Z) (only parsing).      (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac fu_drop_fake := repeat match goal with H : context [al_fake _] |- _ => clear H end.
Ltac fu_drop_dtls := repeat match goal with H : context [al_dtls _] |- _ => clear H end.
Ltac fu_drop_tls := repeat match goal with H : context [ATPv] |- _ => clear H | H : context [kt_img] |- _ => clear H end.
Ltac fu_focus :=
  lazymatch goal with
  | |- context [al_fake _] => fu_drop_dtls; fu_drop_tls
  | |- context [al_dtls _] => fu_drop_fake; fu_drop_tls
  | |- context [ATPv] => fu_drop_fake; fu_drop_dtls
  | |- _ => fu_drop_fake; fu_drop_dtls; fu_drop_tls
  end.
Ltac fu_lia := first [solve [fu_focus; lia] | lia].
(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
(* [comment removed for export] *)
#[using="Type"] Local Lemma aobj_int : forall a n, aobj a n -> 0x10000 <= n ->
  6303744 <= a /\ a + n <= ATOP /\ exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof.
  intros a n H Hn. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. (nd_pre H 5%nat; intros H1 H2 H3 H4 H5; nd_post).
  split; [lia|]. split; [lia|]. destruct H4; [exists 0 | exists 1]; lia.
Qed.
#[using="Type"] Local Lemma aobj4_int : forall a, aobj a 4096 ->
  4096 <= a /\ a + 4096 <= ATOP
  /\ (exists k, 0 <= k <= 1 /\ a + 4096 <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a)
  /\ (exists j, 0 <= j <= 1 /\ a + 4096 <= 65536 + j * 18446744073709551616 /\ 6303744 * j <= a).
Proof.
  intros a H. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. (nd_pre H 5%nat; intros H1 H2 H3 H4 H5; nd_post).
  split; [lia|]. split; [lia|]. split; [destruct H4; [exists 0 | exists 1]; lia | destruct H5 as [_ [H5|H5]]; [exists 0 | exists 1]; lia].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma ek_pre_b_hi : forall ek RNG t nb lst n hm m, ek_pre ek RNG t nb lst n hm m -> 0x10007fff8000 <= ek_b ek lst.
Proof.
  intros ek RNG t nb lst n hm m EK.
  destruct ek as [nx bsz cnt hs cnt24' maxc' csz' stj' | full nx bsz cnt24 maxc csz stj idxw chunks spacebeg b hs0]; cbn [ek_pre ek_b] in *.
  - (nd_pre EK 16%nat; intros NB1 LB CNT BSZ BSZN NX LA LEN LJ L0 L1 DTL DHL CR' STS' RL; nd_post). exact L0.
  - (nd_pre EK 20%nat; intros FULL SB CR CH LCH CNT NTH IXS STS HB BJ SBP B0 BL1 DTB DTL DBL DHB DHL RB; nd_post). exact B0.
Qed.

#[using="Type"] Lemma xbatch_free : forall X k24 c', xc_free (x_cls (xbatch X k24) c') = xc_free (x_cls X c').
Proof. intros. unfold xbatch. cbn. destruct (Z.eqb_spec c' K_BATCH_CLASS) as [->|]; reflexivity. Qed.
#[using="Type"] Lemma xbatch_cache : forall X k24 c',
  xc_cache (x_cls (xbatch X k24) c') = if c' =? K_BATCH_CLASS then removelast (xc_cache (x_cls X K_BATCH_CLASS)) else xc_cache (x_cls X c').
Proof. intros. unfold xbatch. cbn. destruct (Z.eqb_spec c' K_BATCH_CLASS) as [->|]; reflexivity. Qed.

#[using="Type"] Lemma ablocks_xbatchR : forall L st st' X LB k24, a_live st' = a_live st -> ablocks L st X LB -> ablocks L st' (xbatch X k24) LB.
Proof.
  intros L st st' X LB k24 EL B. eapply ablocks_mono; [exact B| | intros; rewrite EL; assumption].
  intros b p Hb _. unfold xbatch. cbn. right. exact Hb.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma sec_same_core : forall st s, same_core st s -> Permutation (sec_chunks_of s) (sec_chunks_of st) -> sec_same st s.
Proof.
  intros st s (E1 & E2 & E3 & E4 & E5 & E6 & E7 & _) P. unfold sec_same. rewrite E7, E6, E5, E1.
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [intros; tauto| exact P].
Qed.

#[using="Type"] Lemma qnum_freeR : forall st ch,
  qnum st -> 0 <= chunk_size ch ->
  let st2 := st_enq st ch in
  (Q_CACHE < a_qloc_bytes st2 -> a_qglob_bytes st2 + a_qloc_bytes st2 <= Q_MAX) ->
  qnum (st_after st2)
  /\ a_qloc_bytes st2 = batches_bytes (a_qloc st2) /\ a_qglob_bytes st2 = a_qglob_bytes st /\ a_qglob st2 = a_qglob st
  /\ Forall (fun b => Q_BATCH_BYTES <= b_size b) (a_qloc st2 ++ a_qglob st2).
Proof.
  intros st ch (N1 & N2 & N3 & N4 & N5) NN st2 NOREC.
  assert (S2 : a_qloc_bytes st2 = batches_bytes (a_qloc st2) /\ a_qglob_bytes st2 = a_qglob_bytes st /\ a_qglob st2 = a_qglob st
               /\ Forall (fun b => Q_BATCH_BYTES <= b_size b) (a_qloc st2 ++ a_qglob st2)).
  { subst st2. unfold st_enq. destruct (enq_app st ch) as [s|] eqn:E.
    - (nd_pre (enq_app_Some st ch s E) 5%nat; intros l bl QL NF ndR1__; nd_post; revert ndR1__; intros ->). cbn -[batches_bytes Z.add].
      cbn -[batches_bytes Z.add] in QL |- *. rewrite QL in N1, N3.
      rewrite batches_bytes_app, batches_bytes_cons, batches_bytes_nil in N1 |- *. cbn [b_size].
      split; [lia|]. split; [reflexivity|]. split; [reflexivity|].
      rewrite <- app_assoc in N3 |- *. apply Forall_app in N3. destruct N3 as [F1 F2]. inversion F2; subst.
      apply Forall_app. split; [exact F1|]. constructor; [cbn; lia| assumption].
    - (pose proof (enq_new_core ch st) as ndP__; nd_pre ndP__ 7%nat; intros _ G1 G2 _ L1 L2 _; nd_post). rewrite G1, G2, L1, L2. cbn -[batches_bytes Z.add].
      rewrite batches_bytes_app, batches_bytes_cons, batches_bytes_nil. cbn [b_size].
      split; [lia|]. split; [reflexivity|]. split; [reflexivity|].
      rewrite <- app_assoc. apply Forall_app in N3. destruct N3 as [F1 F2].
      apply Forall_app. split; [exact F1|]. constructor; [cbn; unfold Q_BATCH_BYTES; lia| exact F2]. }
  split; [| exact S2]. (nd_pre S2 4%nat; intros B1 B2 B3 B4; nd_post).
  unfold st_after, qnum. destruct (Z.ltb_spec Q_CACHE (a_qloc_bytes st2)) as [LT|GE]; cbn -[batches_bytes Z.add].
  - specialize (NOREC LT). rewrite B2, B3 in *. rewrite ?batches_bytes_app, ?batches_bytes_nil, ?app_nil_r, ?Z.add_0_r.
    split; [reflexivity|]. split; [lia|]. split; [| unfold Q_CACHE; lia].
    apply Forall_app in B4. destruct B4 as [F1 F2]. apply Forall_app. split; [exact F2| exact F1].
  - rewrite B2, B3 in *. repeat split; try assumption; lia.
Qed.

(* [comment removed for export] *)
Section ChunkQ.
Variables (L : alayout) (st : astate) (X : aconc) (m : amem) (c k n b1 ctx : Z) (l1 l2 : list xbusy).
Hypothesis ALO : alayout_ok L.
Hypothesis WF : awf L st X.
Hypothesis XB : x_busy X = l1 ++ bany BQuar c k n b1 ctx :: l2.
Hypothesis CLS : aslots L st X m c /\ aslot_shadow L st X m c.
Let S := size_of_class c.
Let AB := aslot_addr L c k.
Let UB := AB + rz_size n.

#[using="rc tlsI st X b1 ctx l1 l2 ALO WF XB CLS"] Lemma read_chunk_q :
     junk_at m (UB + 8) (S - rz_size n - 8)
  /\ (16 < rz_size n -> rw_cells asegs m AB [C8 (Z_to_bv 64 AMAGIC); C8 (Z_to_bv 64 (UB - 16))] /\ junk_at m (AB + 16) (rz_size n - 32))
  /\ rw_cells asegs m (shad AB) [CB (Z.to_nat (shlen (rz_size n))) (repeat (Z_to_bv 8 0xfa) (Z.to_nat (shlen (rz_size n))))]
  /\ rw_cells asegs m (shad UB + shlen (rup n 8)) [CB (Z.to_nat (shlen S - shlen (rz_size n) - shlen (rup n 8)))
                                                      (repeat (Z_to_bv 8 0xfa) (Z.to_nat (shlen S - shlen (rz_size n) - shlen (rup n 8))))].
Proof.
  destruct (any_range L st X BQuar c k n b1 ctx l1 l2 XB WF) as [HC KR]. destruct CLS as [[SL _] [SH _]].
  (pose proof (any_facts L st X BQuar c k n b1 ctx l1 l2 XB WF ltac:(discriminate)) as ndP__; nd_pre ndP__ 5%nat; intros N0 FIT0 B10 AT0 CTX0; nd_post).
  specialize (SL k KR). specialize (SH k KR). rewrite (busy_of_X_self_g L st X BQuar c k n b1 ctx l1 l2 XB WF) in SL, SH.
  unfold aslot_busy in SL. cbn [xb_st xb_class xb_n xb_b1 xb_ctx bany bstate_byte xb_alloc xb_slot] in SL.
  (nd_pre SL 3%nat; intros LH [stb [E HDR]] UJ; nd_post). injection E as <-.
  (pose proof (chunk_geo L st X c k n ALO WF HC KR (proj1 N0) FIT0) as ndP__; nd_pre ndP__ 14%nat; intros _ _ _ _ _ _ _ _ _ _ _ _ _ S8; nd_post).
  destruct (junk_split m _ 8 (S - rz_size n - 8) ltac:(replace (8 + (S - rz_size n - 8)) with (S - rz_size n) by lia; exact UJ) ltac:(lia) ltac:(subst S; lia)) as [U8 UR].
  subst S AB UB. replace (aslot_addr L c k + rz_size n - 16) with (aslot_addr L c k + rz_size n + -16) by lia.
  split; [exact UR|]. split; [exact LH|].
  (pose proof (chunk_shadow_geo L st X c k n ALO WF HC KR (proj1 N0) FIT0) as ndP__; nd_pre ndP__ 6%nat; intros SE G2 GE G0 GF _; nd_post).
  cbn [slot_shadow_bytes xb_n xb_st bany] in SH.
  pose proof (rz_size_facts n (proj1 N0)) as [RZ1 _].
  pose proof (shlen_nonneg (rz_size n) ltac:(lia)) as SRZ. pose proof (shlen_nonneg (n + 7) ltac:(lia)) as SG7.
  assert (LB : length (repeat (Z_to_bv 8 253) (Z.to_nat (granules n))) = Z.to_nat (granules n)) by (apply repeat_length).
  replace (Z.to_nat (shlen (size_of_class c))) with
    (Z.to_nat (shlen (rz_size n)) + Z.to_nat (granules n) + Z.to_nat (shlen (size_of_class c) - shlen (rz_size n) - granules n))%nat in SH
    by (generalize SRZ SG7 GF; clear; unfold granules; intros; lia).
  (nd_pre (cb_split3_gen m _ _ _ _ _ _ _ ltac:(apply repeat_length) LB ltac:(apply repeat_length) SH) 3%nat; intros SHA SHU SHR; nd_post).
  rewrite Z2Nat.id in SHU by lia. rewrite Z2Nat.id in SHR by lia. rewrite Z2Nat.id in SHR by (generalize SG7; clear; unfold granules; intros; lia).
  rewrite <- SE in SHU, SHR. rewrite <- GE in SHU, SHR.
  split; [exact SHA| exact SHR].
Qed.
End ChunkQ.

(* [comment removed for export] *)
#[using="Type"] Lemma qcoupled_new_pend : forall L st X Q c k n b1 ctx l1 l2 s' k24 cnt sz ia pend,
  x_busy X = l1 ++ bany BQuar c k n b1 ctx :: l2 -> awf L st X -> qcoupled L st X Q ->
  q_pend Q = (c, k) :: pend ->
  c_count (get_cls st K_BATCH_CLASS) = cnt -> 0 < cnt ->
  nth_error (xc_cache (x_cls X K_BATCH_CLASS)) (Z.to_nat (cnt - 1)) = Some k24 ->
  0 <= k24 < ndist st K_BATCH_CLASS -> ~ In k24 (map qb_slot (q_loc Q ++ q_glob Q)) ->
  a_qloc s' = a_qloc st ++ [mkABatch 1 sz [CPrim c n]] -> a_qglob s' = a_qglob st ->
  qcoupled L s' (xbatch X k24) (mkQConc (q_loc Q ++ [mkQB k24 [k]]) (q_glob Q) ia pend).
Proof.
  intros L st X Q c k n b1 ctx l1 l2 s' k24 cnt sz ia pend XB WF CP PEND CNT POS NK KK NIB QL' QG'.
  pose proof CP as CP0. (nd_pre CP0 8%nat; intros LN1 LN2 OK ND1 ND2 BS PS NN; nd_post).
  unfold qcoupled. cbn [q_loc q_glob q_pend]. rewrite QL', QG'.
  rewrite PEND in ND1, PS.
  set (es := qentries (a_qloc st) (q_loc Q) ++ qentries (a_qglob st) (q_glob Q)) in *.
  assert (ESE : qentries (a_qloc st ++ [mkABatch 1 sz [CPrim c n]]) (q_loc Q ++ [mkQB k24 [k]]) ++ qentries (a_qglob st) (q_glob Q)
                = (qentries (a_qloc st) (q_loc Q) ++ [(CPrim c n, k)]) ++ qentries (a_qglob st) (q_glob Q)).
  { rewrite qentries_app by exact LN1. cbn [qentries combine b_chunks qb_ks app]. rewrite ?app_nil_r. reflexivity. }
  rewrite ESE.
  assert (PE : Permutation ((qentries (a_qloc st) (q_loc Q) ++ [(CPrim c n, k)]) ++ qentries (a_qglob st) (q_glob Q)) ((CPrim c n, k) :: es)).
  { subst es. rewrite <- app_assoc. cbn [app]. apply Permutation_sym. apply Permutation_middle. }
  assert (PI : Permutation (qprim_ids ((qentries (a_qloc st) (q_loc Q) ++ [(CPrim c n, k)]) ++ qentries (a_qglob st) (q_glob Q)) ++ pend)
                           (qprim_ids es ++ (c, k) :: pend)).
  { eapply Permutation_trans; [apply Permutation_app_tail; apply qprim_ids_perm; exact PE|]. cbn [qprim_ids flat_map fst snd app]. apply Permutation_middle. }
  assert (PB : Permutation (map qb_slot ((q_loc Q ++ [mkQB k24 [k]]) ++ q_glob Q)) (k24 :: map qb_slot (q_loc Q ++ q_glob Q))).
  { rewrite !map_app. cbn [map qb_slot]. rewrite <- app_assoc. cbn [app]. apply Permutation_sym. apply Permutation_middle. }
  split; [rewrite !length_app; cbn; lia|]. split; [exact LN2|]. split.
  { eapply Permutation_Forall; [apply Permutation_sym; exact PE|]. constructor.
    - unfold qentry_ok. cbn [fst snd]. exists b1, ctx. unfold xbatch. cbn [x_busy]. right. rewrite XB. apply in_or_app. right. left. reflexivity.
    - eapply Forall_impl; [| exact OK]. intros [ch k'] HOK. unfold qentry_ok in *. cbn [fst snd] in *.
      destruct ch as [c' n'| mb ms n']; [| exact I]. (nd_pre HOK 3%nat; intros b1' ctx' Hin; nd_post). exists b1', ctx'. unfold xbatch. cbn [x_busy]. right. exact Hin. }
  split; [eapply Permutation_NoDup'; [apply Permutation_sym; exact PI| exact ND1]|].
  split.
  { eapply Permutation_NoDup'; [apply Permutation_sym; exact PB|]. constructor; [exact NIB| exact ND2]. }
  split.
  { intros k0. split.
    - intros H. apply (Permutation_in _ PB) in H. destruct H as [<-|H].
      + exists (bbatch k24). unfold xbatch, bbatch. cbn. split; [left; reflexivity|]. auto.
      + apply (BS k0) in H. (nd_pre H 5%nat; intros y Hy Sy Cy Ky; nd_post). exists y. unfold xbatch. cbn [x_busy In]. split; [right; exact Hy|]. auto.
    - intros (y & Hy & Sy & Cy & Ky). eapply Permutation_in; [apply Permutation_sym; exact PB|].
      unfold xbatch in Hy. cbn [x_busy In] in Hy. destruct Hy as [<-|Hy].
      + left. cbn in Ky. exact Ky.
      + right. apply (BS k0). exists y. auto. }
  split.
  { intros c0 k0. rewrite (Permutation_in' eq_refl PI). rewrite (PS c0 k0). unfold xbatch. cbn [x_busy In].
    split; intros (y & Hy & Sy & Cy & Ky); exists y.
    - split; [right; exact Hy|]. auto.
    - destruct Hy as [<-|Hy]; [cbn in Sy; discriminate|]. auto. }
  eapply Permutation_Forall; [apply Permutation_sym; exact PB|]. constructor; [lia| exact NN].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section S.
Variable DI : ADepotIface.
Variables (ASEC : alayout -> astate -> aconc -> amem -> Prop) (AFK : alayout -> list ablock -> amem -> Prop).
Hypothesis HL : ahole_laws (AHQ DI ASEC AFK).
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI
                                  /\ (snd iv <= 0xab270 \/ 0xab330 <= fst iv)
                                  /\ (snd iv <= 0xaf800 \/ 0x130830 <= fst iv)
                                  /\ (snd iv <= 0x13e088 \/ 0x13e08c <= fst iv)) CI.

Definition store_freeR__stmt : Prop := store_freeR_stmt DI ASEC AFK CI.
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'store_freeR__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'store_freeR__stmt 1).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'store_freeR__stmt 2).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'store_freeR__stmt 3).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'store_freeR__stmt 4).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'store_freeR__stmt 5).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'store_freeR__stmt 6).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'store_freeR__stmt 7).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'store_freeR__stmt 8).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'store_freeR__stmt 9).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'store_freeR__stmt 10).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'store_freeR__stmt 11).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'store_freeR__stmt 12).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'store_freeR__stmt 13).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'store_freeR__stmt 14).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'store_freeR__stmt 15).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'store_freeR__stmt 16).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'store_freeR__stmt 17).
Variable F : ltac2:(SecDietF.SzSecF.ty 'store_freeR__stmt 18).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'store_freeR__stmt 19).
Variable m : ltac2:(SecDietF.SzSecF.ty 'store_freeR__stmt 20).
Variable st : ltac2:(SecDietF.SzSecF.ty 'store_freeR__stmt 21).
Variable LB : ltac2:(SecDietF.SzSecF.ty 'store_freeR__stmt 22).
Variable X : ltac2:(SecDietF.SzSecF.ty 'store_freeR__stmt 23).
Variable Q : ltac2:(SecDietF.SzSecF.ty 'store_freeR__stmt 24).
Variable c : ltac2:(SecDietF.SzSecF.ty 'store_freeR__stmt 25).
Variable k : ltac2:(SecDietF.SzSecF.ty 'store_freeR__stmt 26).
Variable n : ltac2:(SecDietF.SzSecF.ty 'store_freeR__stmt 27).
Variable b1 : ltac2:(SecDietF.SzSecF.ty 'store_freeR__stmt 28).
Variable ctx : ltac2:(SecDietF.SzSecF.ty 'store_freeR__stmt 29).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'store_freeR__stmt 30).
Variable k24 : ltac2:(SecDietF.SzSecF.ty 'store_freeR__stmt 31).
Variable l1 : ltac2:(SecDietF.SzSecF.ty 'store_freeR__stmt 32).
Variable l2 : ltac2:(SecDietF.SzSecF.ty 'store_freeR__stmt 33).
Variable stj : ltac2:(SecDietF.SzSecF.ty 'store_freeR__stmt 34).
Variable chunks : ltac2:(SecDietF.SzSecF.ty 'store_freeR__stmt 35).
Let st2 := st_enq st (CPrim c n).
Let ek := ek_of L st X Q n k24 stj chunks.
Let g := g_of L st Q (ek_delta ek n).
Let S := size_of_class c.
Let AB := aslot_addr L c k.
Let UB := AB + rz_size n.
Let lst := qlast L (q_loc Q).
Let eb := ek_b ek lst.
Let gl := dk_glst g lst.
Let gq := shlen (rup n 8).
Let st' := st_after st2.
#[using="HL CI_OK st2 ek g S AB UB lst eb gl gq st'"] Lemma store_freeR__body : ltac:(let T := type of (fun (h : store_freeR__stmt) => h L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st LB X Q c k n b1 ctx lo k24 l1 l2 stj chunks) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (ra, (sp, (gp, (tp, (s0, (s1, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (F, (fc, (m, (st, (LB, (X, (Q, (c, (k, (n, (b1, (ctx, (lo, (k24, (l1, (l2, (stj, chunks)))))))))))))))))))))))))))))))))))) as _.
  unfold store_freeR_stmt. 
  cbv zeta. intros ALO ARNG AR BL HFK XB N1 [pend PEND] EA NK0 NB0 KK0 NIB0 JK0 FSH0 CIN0 POS0 NOREC EK DK CEIL LO ms' PM. unfold AFREE_STACK in LO.
  assert (NEWF : enq_is_app st = false ->
        nth_error (xc_cache (x_cls X K_BATCH_CLASS)) (Z.to_nat (c_count (get_cls st K_BATCH_CLASS) - 1)) = Some k24
     /\ busy_of X K_BATCH_CLASS k24 = None /\ 0 <= k24 < ndist st K_BATCH_CLASS
     /\ ~ In k24 (map qb_slot (q_loc Q ++ q_glob Q))
     /\ junk_at m (abatch_addr L k24) 8192 /\ fill_at m (shad (abatch_addr L k24)) (shlen 8192) 0xfa
     /\ a_cinit st = true /\ 0 < c_count (get_cls st K_BATCH_CLASS)) by (intros _; repeat (split; [assumption|]); exact POS0).
  clear NK0 NB0 KK0 NIB0 JK0 FSH0 CIN0 POS0.
  chg (st_enq st (CPrim c n)) st2.
  chg (ek_of L st X Q n k24 stj chunks) ek.
  chg (g_of L st Q (ek_delta ek n)) g.
  (* [comment removed for export] *)
  pose proof AR as AR0. (nd_pre AR0 12%nat; intros WF RT INST THR CLS HQ HS HD HRO HRT2 AVL RT3; nd_post).
  cbn [ah_quar ah_sec ah_depot AHQm] in HQ, HS, HD. rename HQ into AQ.
  (nd_pre THR 6%nat; intros T0 T40 CACHES CSTATS STATS0 UNW; nd_post).
  destruct (any_range L st X BQuar c k n b1 ctx l1 l2 XB WF) as [HC KR].
  (pose proof (any_facts L st X BQuar c k n b1 ctx l1 l2 XB WF ltac:(discriminate)) as ndP__; nd_pre ndP__ 5%nat; intros N0 FIT0 B10 AT0 CTX0; nd_post).
  (pose proof (chunk_geo L st X c k n ALO WF HC KR (proj1 N0) FIT0) as ndP__; nd_pre ndP__ 14%nat; intros HM16 UB16 ABUB ABHM HLO UBS ABCE HHI N65 NQM ABLO RUP RUP8 S8; nd_post).
  (pose proof (slot_geo L st X c k ALO WF HC KR) as ndP__; nd_pre ndP__ 13%nat; intros S16 SM16 AL16 G1 G2 G3 G4 G5 G6 G7 G8 R8 M8; nd_post).
  (pose proof (slot_sep_objects L st X c k ALO WF HC KR) as ndP__; nd_pre ndP__ 5%nat; intros DT DC DN DSO DF; nd_post).
  (pose proof (chunk_shadow_geo L st X c k n ALO WF HC KR (proj1 N0) FIT0) as ndP__; nd_pre ndP__ 9%nat; intros SE GR3 GE G0 GFS SHLO SHHI SHM1 SHM2; nd_post).
  pose proof (rz_size_facts n (proj1 N0)) as [RZ1 RZ2].
  (pose proof (alayout_t L ALO) as ndP__; nd_pre ndP__ 4%nat; intros TL1 TL2 TL3 TL4; nd_post).
  (pose proof (alayout_ctx L ALO) as ndP__; nd_pre ndP__ 5%nat; intros CL1 CL2 CL3 CL4 CL5; nd_post).
  (pose proof (alayout_depot L ALO) as ndP__; nd_pre ndP__ 10%nat; intros DL1 DL2 DL3 DL4 DL5 DL6 DL7 DL8 DL9 DL10; nd_post).
  (pose proof (alayout_stack L ALO) as ndP__; nd_pre ndP__ 3%nat; intros STK1 STK2 STK3; nd_post).
  (pose proof (alayout_space L ALO) as ndP__; nd_pre ndP__ 4%nat; intros SP1 SP2 SP3 SP4; nd_post).
  pose proof (ao_res L ALO) as RES. pose proof (ao_t L ALO) as OT. pose proof (ao_ctx L ALO) as OC. pose proof (ao_nodes L ALO) as ON. pose proof (ao_store L ALO) as OS.
  (pose proof (aobj4_int _ OT) as ndP__; nd_pre ndP__ 4%nat; intros _ _ [kT TBND] [jT TIMG]; nd_post).   (* [comment removed for export] *)
  (pose proof (aobj_int _ _ OC ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros Ci _ [kC CBND]; nd_post). (pose proof (aobj_int _ _ ON ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros Ni _ [kN NBND]; nd_post).
  (pose proof (aobj_int _ _ OS ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros Si _ [kS SBND]; nd_post). pose proof (ao_res_hi L ALO) as RHI.
  unfold aobj in RES, OT, OC, ON, OS. pose proof (ao_space L ALO) as RSP.
  pose proof (ad_t_res L ALO) as D_t_res. pose proof (ad_nodes_res L ALO) as D_n_res. pose proof (ad_store_res L ALO) as D_s_res.
  pose proof (ad_ctx_res L ALO) as D_c_res. pose proof (ad_ctx_nodes L ALO) as D_c_n. pose proof (ad_ctx_store L ALO) as D_c_s.
  unfold adisj in D_t_res, D_n_res, D_s_res, D_c_res, D_c_n, D_c_s.
  assert (D_c_t : al_ctx L + 65536 <= al_t L \/ al_t L + 4096 <= al_ctx L) by (pose proof (ad_t_ctx L ALO) as X1; unfold adisj in X1; clear -X1; lia).
  box DL7. box DL8. box DL9. box DL10. box D_t_res. box D_n_res. box D_s_res. box D_c_res. box D_c_n. box D_c_s. box D_c_t. box CL5.
  box DT. box DC. box DN. box DSO. box DF.
  word_range sp SPR.
  chg (size_of_class c) S. chg (aslot_addr L c k) AB. chg (AB + rz_size n) UB.
  assert (EAB : AB = aslot_addr L c k) by reflexivity. assert (EUB : UB = AB + rz_size n) by reflexivity. assert (ES : S = size_of_class c) by reflexivity.
  assert (EHM : fhm L c k n = UB - 16) by (unfold fhm; subst AB UB; clear; lia).
  assert (UB16' : UB mod 8 = 0) by (clear -UB16; Z.div_mod_to_equations; lia).
  rewrite EHM in PM.
  (* [comment removed for export] *)
  (nd_pre (read_chunk_q L st X m c k n b1 ctx l1 l2 ALO WF XB (conj (proj1 (proj2 (proj2 (CLS c HC)))) (proj2 (proj2 (proj2 (CLS c HC)))))) 4%nat; intros UJR LH SHA SHR; nd_post).
  fold AB in UJR, LH, SHA, SHR. fold UB in UJR, LH, SHR. fold S in UJR, SHR.
  (* [comment removed for export] *)
  pose proof AQ as AQ0. (nd_pre AQ0 6%nat; intros [QK MX] [QC ABL] [GCQ ABG] (FL & IAS & IAM) CP NUM; nd_post).
  pose proof NUM as NUM0. (nd_pre NUM0 5%nat; intros NB1 NB2 NF NC NM; nd_post).
  pose proof CP as CP0. (nd_pre CP0 7%nat; intros LN1 LN2 _ _ ND2 BSI _; nd_post).
  (* [comment removed for export] *)
  assert (CNT : enq_app st (CPrim c n) = None -> 0 < c_count (get_cls st K_BATCH_CLASS)) by (intros _; exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (NEWF EA))))))))).
  assert (EAPP0 : enq_app st (CPrim c n) = None).
  { destruct (enq_app st (CPrim c n)) as [sx|] eqn:EAPP; [exfalso| reflexivity].
    assert (EA1 : enq_is_app st = true) by (apply (proj2 (enq_is_app_spec st (CPrim c n))); eexists; exact EAPP). congruence. }
  assert (SB : a_qloc_bytes st2 = a_qloc_bytes st + ek_delta ek n /\ a_qglob_bytes st2 = a_qglob_bytes st /\ a_qglob st2 = a_qglob st).
  { subst st2 ek. unfold st_enq, ek_of. rewrite EAPP0, EA. cbn [ek_delta]. (pose proof (enq_new_core (CPrim c n) st) as ndP__; nd_pre ndP__ 7%nat; intros _ G1' G2' _ _ L2' _; nd_post).
    rewrite G1', G2', L2'. cbn [chunk_size]. unfold Q_BATCH_BYTES. repeat split; try reflexivity. clear; lia. }
  (nd_pre SB 3%nat; intros SB1 SB2 SB3; nd_post).
  assert (ED0 : 0 <= ek_delta ek n /\ ek_delta ek n <= n + 8192) by (subst ek; unfold ek_of; rewrite EA; cbn [ek_delta]; lia).
  assert (EBK : ek_b ek (qlast L (q_loc Q)) = qlast L (q_loc Q) \/ (enq_is_app st = false /\ ek_b ek (qlast L (q_loc Q)) = abatch_addr L k24)).
  { subst ek. unfold ek_of. rewrite EA; cbn [ek_b]. right; split; reflexivity. }
  assert (EBB : ek_b ek (qlast L (q_loc Q)) = qlast L (q_loc Q)
      \/ exists kk, ek_b ek (qlast L (q_loc Q)) = abatch_addr L kk /\ 0 <= kk < ndist st K_BATCH_CLASS /\ ~ In kk (map qb_slot (q_loc Q ++ q_glob Q))).
  { destruct EBK as [E|[EA2 E]]; [left; exact E| right; exists k24]. (nd_pre (NEWF EA2) 5%nat; intros NK NB KK NIB _; nd_post). split; [exact E|]. split; [exact KK| exact NIB]. }
  (nd_pre (read_dk (AHQm DI ASEC AFK Q) L st X Q m RNG BQuar c k n b1 ctx l1 l2 ALO ARNG AR AQ XB ltac:(discriminate) (ek_b ek (qlast L (q_loc Q))) (ek_delta ek n) ek
              (proj1 ED0) EBB ltac:(rewrite <- SB1, <- SB2; exact NOREC) eq_refl) 4%nat; intros _ _ GL GLST; nd_post).
  fold g in GL, GLST.
  chg (qlast L (q_loc Q)) lst. chg (ek_b ek lst) eb. chg (dk_glst g lst) gl. chg (shlen (rup n 8)) gq.
  (* [comment removed for export] *)
  assert (BGEO : forall q, In q (q_loc Q ++ q_glob Q) ->
      aregion L K_BATCH_CLASS <= abatch_addr L (qb_slot q) /\ abatch_addr L (qb_slot q) + 8192 <= aregion L K_BATCH_CLASS + c_allocated_user (get_cls st K_BATCH_CLASS)
      /\ al_res L + 4096 <= abatch_addr L (qb_slot q) /\ abatch_addr L (qb_slot q) + 8192 <= al_res L + 137439023104).
  { intros q Hq. (pose proof (slot_geo L st X K_BATCH_CLASS (qb_slot q) ALO WF (K24) (bslot_range L st X Q WF CP q Hq)) as ndP__; nd_pre ndP__ 10%nat; intros _ _ _ Q1 Q2 Q3 Q4 Q5 Q6 _; nd_post).
    rewrite size_of_class_24 in Q2, Q6. unfold abatch_addr. unfold K_SPACE_SIZE in Q6. change (2^37) with 137438953472 in Q6.
    generalize Q1 Q2 Q5 Q6 RSP; clear; intros. lia. }
  assert (A24 : c_allocated_user (get_cls st K_BATCH_CLASS) <= K_FREEARR_OFF).
  { destruct WF as (_ & _ & _ & _ & _ & PERC & _). (nd_pre (PERC K_BATCH_CLASS (K24)) 3%nat; intros Q1 Q2 _; nd_post). lia. }
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
  { subst eb. destruct EBK as [E|[EA2 E]].
    - rewrite E. destruct LSTF as [Z0|(_ & FF)]; [left; exact Z0| right; exact FF].
    - right. rewrite E. (nd_pre (NEWF EA2) 4%nat; intros _ _ KK _; nd_post). (pose proof (slot_geo L st X K_BATCH_CLASS k24 ALO WF (K24) KK) as ndP__; nd_pre ndP__ 10%nat; intros _ _ _ Q1 Q2 Q3 Q4 Q5 Q6 _; nd_post).
      rewrite size_of_class_24 in Q2, Q6. unfold abatch_addr. unfold K_SPACE_SIZE in Q6. change (2^37) with 137438953472 in Q6.
      generalize Q1 Q2 Q5 Q6 RSP; clear; intros. lia. }
  (* [comment removed for export] *)
  (nd_pre PM 19%nat; intros id t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' sj' ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 18%nat; intros MU WM MI' ST' IDR HDR' FC' SH' QC' EKP DKP STATS' LSJ' UW' FL' IAS' IAM' DEP'; nd_post).
  fold lst in MU, QC', EKP, DKP, EBK. fold eb in MU, EBK. fold gl in MU. fold gq in MU, SH'.
  replace (UB - 16 + 16) with UB in MU, FC', SH' by (clear; lia).
  assert (ELST : lst = qlast L (q_loc Q)) by reflexivity. assert (EEB : eb = ek_b ek lst) by reflexivity.
  assert (EGL : gl = dk_glst g lst) by reflexivity. assert (EGQ : gq = shlen (rup n 8)) by reflexivity.
  clearbody lst eb gl gq.
  (* [comment removed for export] *)
  assert (MUn : munch (Wf (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) m m').
  { eapply munch_weaken; [| exact MU]. solve_sub_fp sp. }
  clear MU.
  assert (EBNZ : 0x10007fff8000 <= eb) by (rewrite EEB; exact (ek_pre_b_hi _ _ _ _ _ _ _ _ EK)).   (* [comment removed for export] *)
  assert (KF : kfactsF (bv_unsigned sp) (al_t L) AB S UB gq (al_nodes L) (al_store L) (al_res L) (al_ctx L) lo (shlen (rz_size n)) (shlen S) lst eb gl).
  { unfold kfactsF. unfold K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
    assert (GQ1 : 1 <= gq) by (rewrite EGQ, shlen_div; generalize RUP RUP8 N1; clear; intros; Z.div_mod_to_equations; lia).
    generalize CEIL LO OT OC ON OS RES RHI RSP G5 G6 ABUB UBS S8 RUP EUB SHLO SE GR3 GQ1 GFS GE SHHI LSTF EBF GLF EBNZ. clear. intros.
    unfold iclr, AIMG_LO, AIMG_HI in *.   (* [comment removed for export] *)
    (destruct LSTF as [Z0|(_ & FF)]; [rewrite (qsz_eq0 lst Z0) | rewrite (qsz_pos lst) by (atop_facts; lia)]);
    (destruct EBF as [Z1|FF1]; [exfalso; atop_facts; lia|]); destruct GLF as [[_ Z2]|(_ & _ & [Z2|(_ & FF2)])];
    sg_destr; repeat split; first [assumption | lia]. }
  pose proof (KF_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Kimg.
  pose proof (KF_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Klow.
  pose proof (KF_hi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Khi.
  pose proof (KF_shad _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Kshad.
  pose proof (KF_ctx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF (unbxF D_c_t) (unbxF D_c_res) (unbxF D_c_n) (unbxF D_c_s)) as Kctx.
  pose proof (KF_t _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF (unbxF D_t_res) (unbxF DL7) (unbxF DL8)) as Kt.
  pose proof (KF_res _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF (unbxF D_t_res) (unbxF D_n_res) (unbxF D_s_res)) as Kres.
  pose proof (KF_obj _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Kobj.
  pose proof (KF_objL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as KobjL.      (* [comment removed for export] *)
  pose proof (ad_tls_t L ALO) as D_l_t. pose proof (ad_tls_res L ALO) as D_l_r. pose proof (ad_tls_nodes L ALO) as D_l_n. pose proof (ad_tls_store L ALO) as D_l_s.
  unfold adisj in D_l_t, D_l_r, D_l_n, D_l_s. pose proof atp_lin as TLN. pose proof atop_range as ATR0.
  (* [comment removed for export] *)
  assert (SC : same_core st (st_after st2) /\ a_cinit (st_after st2) = a_cinit st /\ a_live (st_after st2) = a_live st /\ a_next (st_after st2) = a_next st
               /\ a_space_beg (st_after st2) = a_space_beg st /\ a_ptr_array (st_after st2) = a_ptr_array st
               /\ (enq_is_app st = true -> a_cls (st_after st2) = a_cls st)
               /\ (enq_is_app st = false -> a_cls (st_after st2) = <[ K_BATCH_CLASS := cls_set_count (c_count (get_cls st K_BATCH_CLASS) - 1) (get_cls st K_BATCH_CLASS) ]> (a_cls st))).
  { pose proof (st_after_core st2) as [SC2 CL2'].
    assert (SC1 : same_core st st2 /\ (enq_is_app st = true -> a_cls st2 = a_cls st) /\ (enq_is_app st = false -> a_cls st2 = <[ K_BATCH_CLASS := cls_set_count (c_count (get_cls st K_BATCH_CLASS) - 1) (get_cls st K_BATCH_CLASS) ]> (a_cls st))).
    { subst st2. unfold st_enq. rewrite EAPP0.
      (pose proof (enq_new_core (CPrim c n) st) as ndP__; nd_pre ndP__ 7%nat; intros C1 _ _ _ _ _ C7; nd_post). split; [exact C1|].
      split; [| intros _; exact C7]. intros EA'. exfalso. congruence. }
    (nd_pre SC1 3%nat; intros SC1 CLa CLb; nd_post). pose proof (same_core_trans _ _ _ SC1 SC2) as SC3.
    pose proof SC3 as SC0. (nd_pre SC0 8%nat; intros F1 F2 F3 F4 F5 F6 F7 _; nd_post).
    split; [exact SC3|]. split; [exact F3|]. split; [exact F1|]. split; [exact F2|]. split; [exact F4|]. split; [exact F5|].
    split; [intros EA2; rewrite CL2'; exact (CLa EA2)| intros EA2; rewrite CL2'; exact (CLb EA2)]. }
  (nd_pre SC 8%nat; intros SC ECIN ELIVE ENEXT ESB EPA CLa CLb; nd_post).
  pose proof SC as SC0. (nd_pre SC0 12%nat; intros _ _ _ _ _ ENRES ENSEC GCo M24a M24b M24c M24d; nd_post).
  chg (st_after st2) st'.
  set (X' := xbatch X k24).
  assert (GC24 : get_cls st' K_BATCH_CLASS = (if enq_is_app st then get_cls st K_BATCH_CLASS else cls_set_count (c_count (get_cls st K_BATCH_CLASS) - 1) (get_cls st K_BATCH_CLASS))).
  { unfold get_cls at 1. rewrite EA. rewrite (CLb EA), lookup_insert_eq; reflexivity. }
  assert (GCo' : forall c', c' <> K_BATCH_CLASS -> get_cls st' c' = get_cls st c') by (intros c' NE; rewrite (GCo c' NE); reflexivity).
  assert (NDS : forall c', ndist st' c' = ndist st c').
  { intros c'. unfold ndist. destruct (Z.eq_dec c' K_BATCH_CLASS) as [->|NE]; [rewrite M24b; reflexivity| rewrite (GCo' c' NE); reflexivity]. }
  assert (MC' : forall c', max_count st' c' = max_count st c') by (intros c'; unfold max_count; rewrite ECIN; reflexivity).
  (* [comment removed for export] *)
  assert (WF' : awf L st' X').
  { subst X'. (nd_pre (NEWF EA) 8%nat; intros NK NB KK NIB JK FSH CIN POS; nd_post).
    apply (awf_xbatch L st X k24 (c_count (get_cls st K_BATCH_CLASS)) WF eq_refl POS NK).
    + exact ESB. + exact EPA. + exact ECIN. + exact ELIVE. + exact ENEXT.
    + intros c' NE. rewrite (GCo' c' NE). reflexivity.
    + rewrite GC24, EA. reflexivity. }
  (* [comment removed for export] *)
  assert (RT' : arep_rt L m').
  { eapply arep_rt_frame; [exact MUn | exact WM | exact RT |]. unfold rt_hulls, ATP88, ATSD.
    (first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kctx; clear; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kctx; clear; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |])] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]). apply Forall_nil. }
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
      + destruct (CACHES K_BATCH_CLASS Hc') as [tail (CR & CH & LCH)]. unfold acache_cells. cbv zeta.
        rewrite GC24, MC', ECIN, EA. subst X'. rewrite xbatch_cache, Z.eqb_refl.
        replace (acache_addr L K_BATCH_CLASS) with (al_t L + 2128) in CR, CH |- * by (unfold acache_addr, K_BATCH_CLASS; clear; lia).
        subst ek. unfold ek_of in EKP. rewrite EA in EKP; cbn [ek_post negb] in EKP |- *.
        * destruct EKP as (CR' & _). (nd_pre (NEWF EA) 8%nat; intros NK NB KK NIB JK FSH CIN POS; nd_post).
          cbn [c_count cls_set_count]. exists (Z_to_bv 64 (acompact K_BATCH_CLASS k24) :: tail).
          pose proof (cache24_split L st X k24 (c_count (get_cls st K_BATCH_CLASS)) WF eq_refl POS NK) as [CACHE LRL].
          split; [exact CR'|]. split.
          -- eapply u32arr_frame; [| exact MUn | exact WM |].
             ++ rewrite CACHE, map_app in CH. cbn [map] in CH. rewrite <- app_assoc in CH. cbn [app] in CH. exact CH.
             ++ rewrite length_app, length_map. cbn [length].
                replace (length (removelast (xc_cache (x_cls X K_BATCH_CLASS))) + Datatypes.S (length tail))%nat with 16%nat
                  by (rewrite CACHE, length_app in LCH; cbn [length] in LCH; clear -LCH; lia).
                apply Kt; clear; lia.
          -- cbn [length]. rewrite CACHE, length_app in LCH. cbn [length] in LCH. clear -LCH. lia.
      + eapply acache_cells_frame; [exact MUn | exact WM | exact (CACHES c' Hc') | rewrite (GCo' c' NE); reflexivity | exact ECIN | |].
        * subst X'. rewrite xbatch_cache. destruct (Z.eqb_spec c' K_BATCH_CLASS) as [E|_]; [exfalso; exact (NE E)|]. reflexivity.
        * unfold acache_addr. unfold K_NUM_CLASSES, K_BATCH_CLASS in *. apply Kt; clear -Hc' NE; lia.
    - apply (junk_merge m' (al_t L + 2768) 16 16); [| | clear; lia | clear; lia].
      + eapply junk_frame; [exact (proj1 (junk_split m (al_t L + 2768) 16 16 CSTATS ltac:(clear; lia) ltac:(clear; lia))) | exact MUn | exact WM | intros _; apply Kt; clear; lia].
      + apply (junk_merge m' (al_t L + 2768 + 16) 8 8); [| | clear; lia | clear; lia].
        * replace (al_t L + 2768 + 16) with (al_t L + 2784) by (clear; lia).
          assert (STJ' : exists w : word, rw_cells asegs m' (al_t L + 2784) [C8 w]).
          { subst ek. unfold ek_of in EKP. rewrite EA in EKP; cbn [ek_post] in EKP. (nd_pre EKP 3%nat; intros _ STS' _; nd_post). exact STS'. }
          destruct STJ' as [w STS']. pose proof (junk_of_cells m' _ _ STS') as J. cbn in J. exact J.
        * replace (al_t L + 2768 + 16 + 8) with (al_t L + 2792) by (clear; lia).
          eapply junk_frame; [| exact MUn | exact WM | intros _; apply Kt; clear; lia].
          pose proof (junk_split m (al_t L + 2768) 16 16 CSTATS ltac:(clear; lia) ltac:(clear; lia)) as [_ CSb].
          pose proof (junk_split m (al_t L + 2768 + 16) 8 8 CSb ltac:(clear; lia) ltac:(clear; lia)) as [_ CSc].
          replace (al_t L + 2768 + 16 + 8) with (al_t L + 2792) in CSc by (clear; lia). exact CSc.
    - exists sj'. split; [exact STATS' | exact LSJ'].
    - exact UW'. }
  (* [comment removed for export] *)
  assert (SEPQ : forall q, In q (q_loc Q ++ q_glob Q) -> AB + S <= abatch_addr L (qb_slot q) \/ abatch_addr L (qb_slot q) + 8192 <= AB).
  { intros q Hq. (nd_pre (bslot_busy L st X Q CP q Hq) 5%nat; intros yq Hyq Syq Cyq Kyq; nd_post).
    pose proof (slots_sep_any L st X c k K_BATCH_CLASS (qb_slot q) ALO WF HC (K24) KR (bslot_range L st X Q WF CP q Hq)
                  ltac:(rewrite <- Cyq, <- Kyq; apply (other_key (AHQm DI ASEC AFK Q) L st X m BQuar c k n b1 ctx l1 l2 AR XB); [exact Hyq| rewrite Syq; discriminate])) as D.
    rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
  assert (SEPK : enq_is_app st = false -> AB + S <= abatch_addr L k24 \/ abatch_addr L k24 + 8192 <= AB).
  { intros EA2. (nd_pre (NEWF EA2) 4%nat; intros NK NB KK _; nd_post).
    pose proof (slots_sep_any L st X c k K_BATCH_CLASS k24 ALO WF HC (K24) KR KK
                  ltac:(destruct (Z.eq_dec c K_BATCH_CLASS) as [->|NE]; [right| left; exact NE]; intros ->;
                        pose proof (busy_of_X_self_g L st X BQuar K_BATCH_CLASS k24 n b1 ctx l1 l2 XB WF) as E'; rewrite NB in E'; discriminate)) as D.
    rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
  assert (SEPL : lst = 0 \/ (AB + S <= lst \/ lst + 8192 <= AB)).
  { destruct LSTF as [Z0|((q & Hq & Eq) & _)]; [left; exact Z0| right; rewrite Eq; apply SEPQ; apply in_or_app; left; exact Hq]. }
  assert (SEPE : eb = 0 \/ (AB + S <= eb \/ eb + 8192 <= AB)).
  { subst eb. destruct EBK as [E|[EA2 E]]; rewrite E; [exact SEPL| right; exact (SEPK EA2)]. }
  assert (SEPG : gl = 0 \/ (AB + S <= gl \/ gl + 8192 <= AB)).
  { destruct GLF as [[_ ->]|(_ & _ & [Z0|((q & Hq & Eq) & _)])]; [exact SEPL| left; exact Z0| right; rewrite Eq; apply SEPQ; apply in_or_app; right; exact Hq]. }
  (* [comment removed for export] *)
  assert (BDIS : forall q1 q2, In q1 (q_loc Q ++ q_glob Q) -> In q2 (q_loc Q ++ q_glob Q) ->
      abatch_addr L (qb_slot q1) = abatch_addr L (qb_slot q2) \/ abatch_addr L (qb_slot q1) + 8192 <= abatch_addr L (qb_slot q2) \/ abatch_addr L (qb_slot q2) + 8192 <= abatch_addr L (qb_slot q1)).
  { intros q1 q2 H1 H2. destruct (Z.eq_dec (qb_slot q1) (qb_slot q2)) as [E|NE]; [left; rewrite E; reflexivity| right].
    pose proof (slots_disjoint L K_BATCH_CLASS (qb_slot q1) (qb_slot q2) ltac:(pose proof (bslot_range L st X Q WF CP q1 H1); lia)
                  ltac:(pose proof (bslot_range L st X Q WF CP q2 H2); lia) NE ltac:(rewrite size_of_class_24; lia)) as D.
    rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
  assert (KDIS : forall q, In q (q_loc Q ++ q_glob Q) -> enq_is_app st = false ->
      abatch_addr L k24 + 8192 <= abatch_addr L (qb_slot q) \/ abatch_addr L (qb_slot q) + 8192 <= abatch_addr L k24).
  { intros q Hq EA2. (nd_pre (NEWF EA2) 5%nat; intros NK NB KK NIB _; nd_post).
    assert (NE : k24 <> qb_slot q) by (intros ->; apply NIB; apply in_map; exact Hq).
    pose proof (slots_disjoint L K_BATCH_CLASS k24 (qb_slot q) ltac:(lia) ltac:(pose proof (bslot_range L st X Q WF CP q Hq); lia) NE ltac:(rewrite size_of_class_24; lia)) as D.
    rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
  (* [comment removed for export] *)
  assert (RC : forall c1 c2, c1 < c2 -> aregion L c1 + K_REGION <= aregion L c2) by (intros; apply regions_sep; assumption).
  assert (CLS' : forall c'', 1 <= c'' < K_NUM_CLASSES ->
      aregion_cells L st' m' c'' /\ afreearray L st' X' m' c'' /\ aslots L st' X' m' c'' /\ aslot_shadow L st' X' m' c'').
  { intros c'' Hc''. (nd_pre (CLS c'' Hc'') 4%nat; intros REG FARR SLOTS SHADOW; nd_post).
    pose proof WF as WF0. (nd_pre WF0 7%nat; intros _ _ SAL _ _ PERC _; nd_post).
    (nd_pre (PERC c'' Hc'') 12%nat; intros Q1 Q2 Q3 Q4 Q5 Q6 Q7 QLENF QLENC QCNTB QND QRANGE; nd_post).
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
    (nd_pre RI 4%nat; intros RI1 RI2 RI3 RI4; nd_post).
    (* [comment removed for export] *)
    assert (PC0 : aregion L c <= AB /\ AB + S <= aregion L c + K_FREEARR_OFF /\ AB + S <= aregion L c + c_allocated_user (get_cls st c)) by (clear -G1 G2 G3 G4; lia).
    split; [| split; [| split]].
    - eapply aregion_cells_frame; [exact MUn | exact WM | exact REG | exact EC1 | exact EC2 | exact EC3 | exact EC4 |].
      unfold aregion_info, ARI_STRIDE, K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
      apply Kres; try (clear -Hc'' RSP G6 S8 EUB; lia).
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
      + subst X'. apply xbatch_free.
      + assert (FA1 : aregion L c'' + K_FREEARR_OFF <= afreearr L c'' /\ afreearr L c'' + c_mapped_free_array (get_cls st c'') <= aregion L c'' + K_REGION).
        { unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q6. lia. }
        destruct FA1 as [FA1 FA2].
        apply Kres; [clear -RI1 FA1; unfold K_FREEARR_OFF in *; lia | clear -RI2 RI3 FA2; lia | clear -Q5 Q6; lia | | | |].
        * pose proof (farr_vs_user L c'' c _ _ AB S (proj1 PC0) (proj1 (proj2 PC0)) FA1 FA2) as D. clear -D ABUB S8 EUB. lia.
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
        * rewrite shad_div. unfold ASHOFF, K_FREEARR_OFF in *. clear -RI1 FA1 RES RHI. Z.div_mod_to_equations. lia.
        * rewrite shad_div, shlen_div. unfold ASHOFF, K_SPACE_SIZE in *. clear -RI2 RI3 FA2 RES RHI. Z.div_mod_to_equations. lia.
        * apply shlen_nonneg. clear -Q5 Q6. lia.
        * pose proof (farr_vs_user L c'' c _ _ UB (rup n 8) ltac:(clear -PC0 ABUB; lia) ltac:(clear -PC0 UBS; lia) FA1 FA2) as D.
          assert (AM : afreearr L c'' mod 8 = 0) by (unfold afreearr, K_FREEARR_OFF; clear -RM''; Z.div_mod_to_equations; lia).
          rewrite EGQ. destruct D as [D|D]; [left; apply shad_sep; [exact D| exact AM] | right; apply shad_sep; [exact D| clear -UB16; Z.div_mod_to_equations; lia]].
    - (* [comment removed for export] *)
      eapply (aslots_update_gen L _ m m' MUn WM st st' X X' c''); [exact SLOTS | apply NDS | exact EC3 | exact EC4 | |].
      + intros k'' Hk''.
        (pose proof (slot_geo L st X c'' k'' ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) Hk'') as ndP__; nd_pre ndP__ 12%nat; intros T16 TM16 TAL P1 P2 P3 P4 P5 P6 P7 P8 _; nd_post).
        assert (D1 : (c'' = c /\ k'' = k) \/ (c'' <> c \/ k'' <> k)) by (clear; lia). destruct D1 as [[Ec Ek]|NE1].
        * (* [comment removed for export] *)
          subst c'' k''. right.
          subst X'. rewrite (busy_of_xbatch' X k24 c k).
          assert (NOK : ((K_BATCH_CLASS =? c) && (k24 =? k)) = false).
          { destruct (Z.eqb_spec K_BATCH_CLASS c) as [E1'|]; [| reflexivity]. destruct (Z.eqb_spec k24 k) as [E2'|]; [| reflexivity]. exfalso.
            (nd_pre (NEWF EA) 3%nat; intros _ NB _; nd_post). pose proof (busy_of_X_self_g L st X BQuar c k n b1 ctx l1 l2 XB WF) as E'. rewrite <- E1', <- E2', NB in E'. discriminate. }
          rewrite NOK, (busy_of_X_self_g L st X BQuar c k n b1 ctx l1 l2 XB WF).
          unfold aslot_busy, bany. cbn [xb_st xb_class xb_n xb_b1 xb_ctx xb_slot bstate_byte]. unfold xb_user, xb_hdr, xb_alloc. cbn [xb_class xb_slot xb_n].
          rewrite <- EAB. fold S. rewrite <- EUB.
          split; [| split].
          -- intros R16. pose proof (rz_gt16 n (proj1 N0) R16) as R32. destruct (LH R16) as [LC LJ]. split.
             ++ eapply cells_frame; [exact LC | exact MUn | exact WM |]. cbn [cells_size csize Nat.add].
                apply Kres; clear -G5 G6 RSP RES RHI S16 EUB R32 S8 SEPL SEPE SEPG; unfold K_SPACE_SIZE in *; lia.
             ++ eapply junk_frame; [exact LJ | exact MUn | exact WM |]. intros Hp.
                apply Kres; clear -G5 G6 RSP RES RHI S16 EUB R32 S8 SEPL SEPE SEPG Hp; unfold K_SPACE_SIZE in *; lia.
          -- exists 3. split; [reflexivity|]. exact HDR'.
          -- replace (S - rz_size n) with (8 + (S - rz_size n - 8)) by (clear; lia).
             apply (junk_merge m' UB 8 (S - rz_size n - 8)); [| | clear; lia | clear -S8; lia].
             ++ pose proof (junk_of_cells m' _ _ FC') as J. cbn in J. exact J.
             ++ eapply junk_frame; [exact UJR | exact MUn | exact WM |]. intros Hp.
                apply Kres; clear -G5 G6 RSP RES RHI S16 EUB ABUB S8 SEPL SEPE SEPG Hp; unfold K_SPACE_SIZE in *; lia.
        * (* [comment removed for export] *)
          assert (T2 : (c =? c'') && (k =? k'') = false).
          { destruct (Z.eqb_spec c c'') as [E|]; [| reflexivity]. destruct (Z.eqb_spec k k'') as [E'|]; [| reflexivity]. exfalso. clear -NE1 E E'. lia. }
          assert (D2 : (enq_is_app st = false /\ c'' = K_BATCH_CLASS /\ k'' = k24) \/ (enq_is_app st = true \/ c'' <> K_BATCH_CLASS \/ k'' <> k24))
            by (rewrite EA; clear; lia).
          destruct D2 as [(EA2 & E24 & EK24)|NE2].
          -- (* [comment removed for export] *)
             subst c'' k''. right.
             subst X'. rewrite (busy_of_xbatch' X k24 K_BATCH_CLASS k24). rewrite !Z.eqb_refl. cbn [andb].
             unfold aslot_busy, bbatch. cbn [xb_st xb_class xb_slot]. unfold xb_alloc. cbn [xb_class xb_slot]. rewrite size_of_class_24.
             subst ek. unfold ek_of in EKP. rewrite EA in EKP. cbn [ek_post] in EKP. (nd_pre EKP 6%nat; intros _ _ BC BA [bsb BJ] _; nd_post).
             fold (abatch_addr L k24) in BC, BA, BJ |- *. change (aslot_addr L K_BATCH_CLASS k24) with (abatch_addr L k24).
             replace 8192 with (24 + (8 * Z.of_nat (length [Z_to_bv 64 (UB - 16)]) + (8192 - 24 - 8 * 1))) by (cbn; lia).
             apply junk_merge; [| | clear; lia| cbn; clear; lia].
             ++ pose proof (junk_of_cells m' _ _ BC) as J. cbn in J. exact J.
             ++ apply junk_merge; [apply junk_of_u64arr; exact BA | | cbn; clear; lia | clear; lia].
                cbn [length Z.of_nat Pos.of_succ_nat]. eexists. exact BJ.
          -- assert (T1 : (K_BATCH_CLASS =? c'') && (k24 =? k'') = false).
             { destruct (Z.eqb_spec K_BATCH_CLASS c'') as [E|]; [| reflexivity]. destruct (Z.eqb_spec k24 k'') as [E'|]; [| reflexivity]. exfalso.
               destruct NE2 as [NE|[NE|NE]]; [congruence| apply NE; symmetry; exact E| apply NE; symmetry; exact E']. }
             assert (BX : busy_of X' c'' k'' = busy_of X c'' k'').
             { subst X'. rewrite (busy_of_xbatch' X k24 c'' k''), T1. reflexivity. }
             (* [comment removed for export] *)
             assert (BQ : forall q, In q (q_loc Q ++ q_glob Q) -> c'' = K_BATCH_CLASS -> aslot_addr L c'' k'' = abatch_addr L (qb_slot q) ->
                 exists yq, busy_of X c'' k'' = Some yq /\ xb_st yq = BBatch /\ xb_class yq = K_BATCH_CLASS /\ xb_slot yq = k''
                            /\ junk_at m (abatch_addr L (qb_slot q)) 8192 /\ k'' = qb_slot q).
             { intros q Hq -> EQA. (nd_pre (bslot_busy L st X Q CP q Hq) 5%nat; intros yq Hyq Syq Cyq Kyq; nd_post).
               assert (EK' : k'' = qb_slot q) by (unfold abatch_addr, aslot_addr in EQA; rewrite size_of_class_24 in EQA; clear -EQA; lia). subst k''.
               exists yq. pose proof (busy_of_In_nodup L st X yq WF Hyq) as BY. rewrite Cyq, Kyq in BY.
               split; [exact BY|]. split; [exact Syq|]. split; [exact Cyq|]. split; [exact Kyq|]. split; [| reflexivity].
               destruct SLOTS as [SLK _]. specialize (SLK (qb_slot q) Hk''). rewrite BY in SLK. unfold aslot_busy in SLK. rewrite Syq in SLK.
               unfold xb_alloc in SLK. rewrite Cyq, Kyq, size_of_class_24 in SLK. exact SLK. }
             assert (D3 : (c'' = K_BATCH_CLASS /\ lst <> 0 /\ aslot_addr L c'' k'' = lst) \/ (c'' <> K_BATCH_CLASS \/ lst = 0 \/ aslot_addr L c'' k'' <> lst)) by (clear; lia).
             destruct D3 as [(E24 & LNZ & EL)|NE3].
             ++ (* [comment removed for export] *)
                right. rewrite BX. destruct LSTF as [Z0|((q & Hq & Eq) & F1 & F2 & F3 & F4)]; [exfalso; exact (LNZ Z0)|].
                (nd_pre (BQ q ltac:(apply in_or_app; left; exact Hq) E24 ltac:(rewrite EL; exact Eq)) 7%nat; intros yq BY Syq Cyq Kyq JQ EKQ; nd_post).
                rewrite BY. unfold aslot_busy. rewrite Syq. unfold xb_alloc. rewrite Cyq, Kyq, size_of_class_24, <- E24, EL.
                assert (QNE : a_qloc st <> []) by (intros QL0; apply LNZ; rewrite ELST; replace (q_loc Q) with (@nil qbatchc) by (clear -QL0 LN1; destruct (q_loc Q); [reflexivity| rewrite QL0 in LN1; cbn in LN1; discriminate]); reflexivity).
                subst ek. unfold ek_of in EKP, EK. rewrite EA in EKP, EK; cbn [ek_post ek_pre] in EKP, EK.
                ** destruct (a_qloc st) as [|b0 bs0] eqn:QL0; [exfalso; exact (QNE eq_refl)|]. rewrite <- QL0 in *.
                   (nd_pre EKP 6%nat; intros _ _ _ _ _ [LB' LA']; nd_post). destruct EK as ((_ & _ & _ & _ & _ & _ & _ & LEN0 & _) & _).
                   rewrite ELST in LB', LA' |- *.
                   replace 8192 with (24 + 8 * Z.of_nat (length (map (Z_to_bv 64) (qhdrs L (b_chunks (List.last (a_qloc st) dummy_batch)) (qb_ks (List.last (q_loc Q) dummy_qb))))))
                     by (rewrite LEN0; clear; lia).
                   apply junk_merge; [| apply junk_of_u64arr; exact LA' | clear; lia| rewrite LEN0; clear; lia].
                   pose proof (junk_of_cells m' _ _ LB') as J. cbn in J. exact J.
             ++ assert (D4 : (g_drain g = true /\ c'' = K_BATCH_CLASS /\ gl <> 0 /\ aslot_addr L c'' k'' = gl /\ gl <> lst)
                           \/ (g_drain g = false \/ c'' <> K_BATCH_CLASS \/ gl = 0 \/ aslot_addr L c'' k'' <> gl \/ gl = lst)) by (destruct (g_drain g); clear; lia).
                destruct D4 as [(GD & E24 & GNZ & EG & GNL)|NE4].
                ** (* [comment removed for export] *)
                   right. rewrite BX. destruct GLF as [[GD' _]|(_ & GQL & [Z0|((q & Hq & Eq) & F1 & F2 & F3 & F4)])]; [congruence| exfalso; exact (GNZ Z0)|].
                   (nd_pre (BQ q ltac:(apply in_or_app; right; exact Hq) E24 ltac:(rewrite EG; exact Eq)) 7%nat; intros yq BY Syq Cyq Kyq JQ EKQ; nd_post).
                   rewrite BY. unfold aslot_busy. rewrite Syq. unfold xb_alloc. rewrite Cyq, Kyq, size_of_class_24, <- E24, EG.
                   (* [comment removed for export] *)
                   assert (GNE : a_qglob st <> []) by (intros QG0; clear -QG0 Hq LN2; destruct (q_glob Q) eqn:QQ0; [destruct Hq| rewrite QG0 in LN2; cbn in LN2; discriminate]).
                   unfold dk_post in DKP. rewrite GD in DKP. (nd_pre DKP 3%nat; intros _ _ GLN; nd_post).
                   assert (GF : g_full g = true) by (subst g; unfold g_of; cbn [g_full]; clear -GNE; destruct (a_qglob st); [exfalso; exact (GNE eq_refl)| reflexivity]).
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
                       { destruct EBK as [E|[EA2 E]]; [left; exact E| right]. rewrite E, Eq. exact (KDIS q ltac:(apply in_or_app; right; exact Hq) EA2). }
                       apply Kres; clear -F3 F4 RES RHI SEPG GNZ DL DE ABUB S8 EUB; lia.
                ** (* [comment removed for export] *)
                   left. split; [exact BX|]. split.
                   +++ assert (DW9 : aslot_addr L c'' k'' + size_of_class c'' <= AB \/ AB + S <= aslot_addr L c'' k'').
                       { pose proof (slots_sep_any L st X c'' k'' c k ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) HC Hk'' KR NE1) as D.
                         rewrite <- EAB, <- ES in D. exact D. }
                       assert (DQ : forall q, In q (q_loc Q ++ q_glob Q) -> (c'' <> K_BATCH_CLASS \/ aslot_addr L c'' k'' <> abatch_addr L (qb_slot q)) ->
                           aslot_addr L c'' k'' + size_of_class c'' <= abatch_addr L (qb_slot q) \/ abatch_addr L (qb_slot q) + 8192 <= aslot_addr L c'' k'').
                       { intros q Hq NE. pose proof (slots_sep_any L st X c'' k'' K_BATCH_CLASS (qb_slot q) ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) (K24) Hk''
                                       (bslot_range L st X Q WF CP q Hq) ltac:(destruct NE as [NE|NE]; [left; exact NE| destruct (Z.eq_dec c'' K_BATCH_CLASS) as [->|NC']; [right| left; exact NC']];
                                                                                    intros EKK; apply NE; rewrite EKK; reflexivity)) as D.
                         rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
                       assert (DW13 : lst = 0 \/ aslot_addr L c'' k'' + size_of_class c'' <= lst \/ lst + 8192 <= aslot_addr L c'' k'').
                       { destruct LSTF as [Z0|((ql & Hql & Eql) & _)]; [left; exact Z0| right]. rewrite Eql. apply DQ; [apply in_or_app; left; exact Hql|].
                         destruct NE3 as [NE|[Z0|NE]]; [left; exact NE| exfalso| right; rewrite <- Eql; exact NE].
                         rewrite Eql in Z0. (nd_pre (BGEO ql ltac:(apply in_or_app; left; exact Hql)) 4%nat; intros _ _ B3 _; nd_post). clear -Z0 B3 RES RHI. lia. }
                       assert (DW14 : eb = lst \/ aslot_addr L c'' k'' + size_of_class c'' <= eb \/ eb + 8192 <= aslot_addr L c'' k'').
                       { destruct EBK as [E|[EA2 E]]; [left; exact E| right]. rewrite E. (nd_pre (NEWF EA2) 4%nat; intros _ _ KK _; nd_post).
                         pose proof (slots_sep_any L st X c'' k'' K_BATCH_CLASS k24 ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) (K24) Hk'' KK
                                       ltac:(destruct NE2 as [NE|[NE|NE]]; [rewrite EA in NE; discriminate| left; exact NE| right; exact NE])) as D.
                         rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
                       assert (DW15 : gl = lst \/ gl = 0 \/ aslot_addr L c'' k'' + size_of_class c'' <= gl \/ gl + 8192 <= aslot_addr L c'' k'').
                       { destruct GLF as [[_ E]|(GD & GQL & [Z0|((q & Hq & Eq) & _)])]; [left; exact E| right; left; exact Z0| right; right].
                         rewrite Eq. apply DQ; [apply in_or_app; right; exact Hq|].
                         destruct NE4 as [NE|[NE|[NE|[NE|NE]]]]; [congruence| left; exact NE| | right; rewrite <- Eq; exact NE| ].
                         - exfalso. rewrite Eq in NE. (nd_pre (BGEO q ltac:(apply in_or_app; right; exact Hq)) 4%nat; intros _ _ B3 _; nd_post). clear -NE B3 RES RHI. lia.
                         - rewrite NE in *. destruct NE3 as [NE'|[Z0|NE']]; [left; exact NE'| exfalso| right; rewrite <- Eq; exact NE'].
                           rewrite Eq in Z0. (nd_pre (BGEO q ltac:(apply in_or_app; right; exact Hq)) 4%nat; intros _ _ B3 _; nd_post). clear -Z0 B3 RES RHI. lia. }
                       apply Kres; [clear -P5 RSP; lia | clear -P6 RSP; unfold K_SPACE_SIZE in *; lia | clear -T16; lia | clear -DW9 ABUB S8 EUB; lia
                                   | clear -DW13 P5 RSP RES RHI; lia | clear -DW14 DW13 P5 RSP RES RHI; lia | clear -DW15 DW13 P5 RSP RES RHI; lia].
                   +++ intros b Hb. (nd_pre (busy_of_Some_facts X c'' k'' b Hb) 3%nat; intros IB CB' KB'; nd_post). split; [exact CB'|]. split; [exact KB'|]. exact (awf_fits L st X b WF IB).
      + intros POS''.
        set (AU := aregion L c'' + c_allocated_user (get_cls st c'')) in *.
        assert (U0 : aregion L c'' <= AU /\ AU + (c_mapped_user (get_cls st c'') - c_allocated_user (get_cls st c'')) <= aregion L c'' + K_FREEARR_OFF) by (subst AU; clear -Q1 Q2; lia).
        destruct U0 as [U0 U0'].
        assert (U1 : c'' = c -> aregion L c + c_allocated_user (get_cls st c) <= AU) by (intros E; subst AU; rewrite <- E; clear; lia).
        assert (U2 : c'' = K_BATCH_CLASS -> aregion L K_BATCH_CLASS + c_allocated_user (get_cls st K_BATCH_CLASS) <= AU) by (intros E; subst AU; rewrite <- E; clear; lia).
        idtac "UND1".
        apply Kres; [clear -RI4 Q1 U0; lia | subst AU; clear -Q1 Q2 RI2 RI3; unfold K_FREEARR_OFF, K_REGION, K_SPACE_SIZE in *; lia | clear -POS''; lia | | | |].
        * pose proof (undist_vs_user L c'' c _ _ AB S (c_allocated_user (get_cls st c)) (proj1 PC0) (proj2 (proj2 PC0)) ltac:(clear -G3 G4; lia) U1 U0 U0') as D.
          clear -D ABUB S8 EUB. lia.
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
      + intros k'' Hk''.
        (pose proof (slot_geo L st X c'' k'' ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) Hk'') as ndP__; nd_pre ndP__ 12%nat; intros T16 TM16 TAL P1 P2 P3 P4 P5 P6 P7 P8 _; nd_post).
        assert (D1 : (c'' = c /\ k'' = k) \/ (c'' <> c \/ k'' <> k)) by (clear; lia). destruct D1 as [[Ec Ek]|NE1].
        * (* [comment removed for export] *)
          subst c'' k''. right.
          subst X'. rewrite (busy_of_xbatch' X k24 c k).
          assert (NOK : ((K_BATCH_CLASS =? c) && (k24 =? k)) = false).
          { destruct (Z.eqb_spec K_BATCH_CLASS c) as [E1'|]; [| reflexivity]. destruct (Z.eqb_spec k24 k) as [E2'|]; [| reflexivity]. exfalso.
            (nd_pre (NEWF EA) 3%nat; intros _ NB _; nd_post). pose proof (busy_of_X_self_g L st X BQuar c k n b1 ctx l1 l2 XB WF) as E'. rewrite <- E1', <- E2', NB in E'. discriminate. }
          rewrite NOK, (busy_of_X_self_g L st X BQuar c k n b1 ctx l1 l2 XB WF).
          unfold slot_shadow_bytes, bany. cbn [xb_n xb_st]. rewrite <- EAB. fold S.
          (* [comment removed for export] *)
          eapply cells_frame in SHA; [| exact MUn | exact WM | cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by (clear -GR3; lia);
                                       apply Kshad; [clear -SHLO; lia| clear -SHHI GR3 GFS SE G0 GE; lia| clear -GR3; lia| left; clear -SE; lia]].
          eapply cells_frame in SHR; [| exact MUn | exact WM | cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by (clear -GFS GE GR3; unfold granules in *; lia);
                                       apply Kshad; [clear -SHLO SE GR3 G0 EGQ; lia| clear -SHHI GR3 GFS SE G0 GE EGQ; lia| clear -GFS GE GR3; unfold granules in *; lia| right; clear -EGQ; lia]].
          rewrite EGQ in SH'.
          replace (shad UB) with (shad AB + Z.of_nat (Z.to_nat (shlen (rz_size n)))) in SH' by (clear -SE GR3; lia).
          rewrite EGQ in SHR, G0.
          replace (shad UB + shlen (rup n 8)) with (shad AB + Z.of_nat (Z.to_nat (shlen (rz_size n))) + Z.of_nat (Z.to_nat (shlen (rup n 8)))) in SHR by (clear -SE GR3 G0; lia).
          pose proof (cb_app m' _ _ _ _ _ SHA (cb_app m' _ _ _ _ _ SH' SHR)) as FIN.
          assert (GE' : shlen (rup n 8) = granules n) by (rewrite <- EGQ; exact GE). rewrite <- GE'.
          replace (Z.to_nat (shlen (rz_size n)) + (Z.to_nat (shlen (rup n 8)) + Z.to_nat (shlen S - shlen (rz_size n) - shlen (rup n 8))))%nat with (Z.to_nat (shlen S)) in FIN
            by (clear -GR3 G0 GE' GFS; unfold granules in *; lia).
          rewrite <- ?app_assoc in FIN. rewrite <- ?app_assoc. exact FIN.
        * left.
          assert (T2 : (c =? c'') && (k =? k'') = false).
          { destruct (Z.eqb_spec c c'') as [E|]; [| reflexivity]. destruct (Z.eqb_spec k k'') as [E'|]; [| reflexivity]. exfalso. clear -NE1 E E'. lia. }
          split.
          -- subst X'. rewrite (busy_of_xbatch' X k24 c'' k'').
             destruct ((K_BATCH_CLASS =? c'') && (k24 =? k'')) eqn:T1; [| reflexivity].
             destruct (Z.eqb_spec K_BATCH_CLASS c'') as [<-|]; [| discriminate]. destruct (Z.eqb_spec k24 k'') as [<-|]; [| discriminate].
             (nd_pre (NEWF EA) 3%nat; intros _ NB _; nd_post). rewrite NB. rewrite size_of_class_24. rewrite slot_shadow_bbatch by (clear; change (shlen 8192) with 1024; lia).
             reflexivity.
          -- assert (DW : aslot_addr L c'' k'' + size_of_class c'' <= AB \/ AB + S <= aslot_addr L c'' k'').
             { pose proof (slots_sep_any L st X c'' k'' c k ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) HC Hk'' KR NE1) as D.
               rewrite <- EAB, <- ES in D. exact D. }
             pose proof (slot_aligned L c'' k'' SAL ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia)) as AL''.
             apply Kshad.
             ++ rewrite shad_div. unfold ASHOFF. clear -P7 RES RHI. Z.div_mod_to_equations. lia.
             ++ rewrite shad_div, shlen_div. unfold ASHOFF in *. clear -P8 T16. Z.div_mod_to_equations. lia.
             ++ apply shlen_nonneg. clear -T16; lia.
             ++ rewrite EGQ. destruct DW as [D|D].
                ** left. eapply Z.le_trans; [apply shad_sep; [exact D| clear -AL''; Z.div_mod_to_equations; lia]|]. clear -SE GR3; lia.
                ** right. apply shad_sep; [clear -D UBS; lia| exact UB16'].
      + intros POS''.
        set (AU := aregion L c'' + c_allocated_user (get_cls st c'')) in *.
        assert (U0 : aregion L c'' <= AU /\ AU + (c_mapped_user (get_cls st c'') - c_allocated_user (get_cls st c'')) <= aregion L c'' + K_FREEARR_OFF) by (subst AU; clear -Q1 Q2; lia).
        destruct U0 as [U0 U0'].
        assert (U1 : c'' = c -> aregion L c + c_allocated_user (get_cls st c) <= AU) by (intros E; subst AU; rewrite <- E; clear; lia).
        pose proof (undist_vs_user L c'' c _ _ UB (rup n 8) (c_allocated_user (get_cls st c)) ltac:(clear -PC0 ABUB; lia) ltac:(clear -PC0 UBS; lia) ltac:(clear -G3 G4; lia) U1 U0 U0') as D.
        assert (AM : AU mod 8 = 0) by (subst AU; pose proof (mod16_of_class _ _ Q3 QS16 ltac:(clear -QS; lia)) as AM; clear -AM RM''; Z.div_mod_to_equations; lia).
        apply Kshad.
        * rewrite shad_div. unfold ASHOFF. clear -U0 RI4 RES RHI. Z.div_mod_to_equations. lia.
        * rewrite shad_div, shlen_div. unfold ASHOFF, K_FREEARR_OFF, K_REGION, K_SPACE_SIZE in *. clear -U0' RI2 RI3 RES RHI. Z.div_mod_to_equations. lia.
        * clear -POS''; lia.
        * rewrite EGQ. destruct D as [D|D]; [left; apply shad_sep; [exact D| exact AM] | right; apply shad_sep; [exact D| exact UB16']].
  }
  (* [comment removed for export] *)
  assert (AVL' : forall c'', 1 <= c'' < K_NUM_CLASSES -> ashadow_avail L st' m' c'').
  { intros c'' Hc''. pose proof WF as WF0. (nd_pre WF0 7%nat; intros _ _ SAL _ _ PERC _; nd_post).
    (nd_pre (PERC c'' Hc'') 8%nat; intros Q1 Q2 Q3 Q4 Q5 Q6 Q7 _; nd_post).
    pose proof (size_of_class_facts c'' Hc'') as [QS QS16]. pose proof (aregion_mod L c'' SAL) as RM''.
    assert (EC2 : c_mapped_free_array (get_cls st' c'') = c_mapped_free_array (get_cls st c'')) by (destruct (Z.eq_dec c'' K_BATCH_CLASS) as [->|NE]; [exact M24d| rewrite (GCo' c'' NE); reflexivity]).
    assert (EC4 : c_mapped_user (get_cls st' c'') = c_mapped_user (get_cls st c'')) by (destruct (Z.eq_dec c'' K_BATCH_CLASS) as [->|NE]; [exact M24a| rewrite (GCo' c'' NE); reflexivity]).
    unfold K_NUM_CLASSES in Hc''.
    assert (RI : al_res L + 4096 <= aregion L c'' /\ aregion L c'' + K_REGION <= al_space_beg L + K_SPACE_SIZE /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
    { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc'' RSP. lia. }
    (nd_pre RI 3%nat; intros RI1 RI2 RI3; nd_post).
    assert (PC0 : aregion L c <= AB /\ AB + S <= aregion L c + K_FREEARR_OFF /\ AB + S <= aregion L c + c_allocated_user (get_cls st c)) by (clear -G1 G2 G3 G4; lia).
    eapply ashadow_avail_frame; [exact MUn | exact WM | exact (AVL c'' ltac:(unfold K_NUM_CLASSES; exact Hc'')) | exact EC4 | exact EC2 | |].
    - intros POS''. set (AU := aregion L c'' + c_mapped_user (get_cls st c'')) in *.
      assert (U0 : aregion L c'' <= AU /\ AU + (K_FREEARR_OFF - c_mapped_user (get_cls st c'')) <= aregion L c'' + K_FREEARR_OFF) by (subst AU; clear -Q1 Q2; lia).
      destruct U0 as [U0 U0'].
      assert (U1 : c'' = c -> aregion L c + c_mapped_user (get_cls st c) <= AU) by (intros E; subst AU; rewrite <- E; clear; lia).
      pose proof (undist_vs_user L c'' c _ _ UB (rup n 8) (c_mapped_user (get_cls st c)) ltac:(clear -PC0 ABUB; lia) ltac:(clear -PC0 UBS G3; lia) G4 U1 U0 U0') as D.
      assert (AM : AU mod 8 = 0) by (subst AU; generalize Q4 RM''; clear; unfold K_USER_MAP; intros; Z.div_mod_to_equations; lia).
      apply Kshad.
      + rewrite shad_div. unfold ASHOFF. clear -U0 RI1 RES RHI. Z.div_mod_to_equations. lia.
      + rewrite shad_div, shlen_div. unfold ASHOFF, K_FREEARR_OFF, K_REGION, K_SPACE_SIZE in *. clear -U0' RI2 RI3 RES RHI. Z.div_mod_to_equations. lia.
      + clear -POS''; lia.
      + rewrite EGQ. destruct D as [D|D]; [left; apply shad_sep; [exact D| exact AM] | right; apply shad_sep; [exact D| exact UB16']].
    - intros POS''. set (AU := afreearr L c'' + c_mapped_free_array (get_cls st c'')) in *.
      assert (FA : aregion L c'' + K_FREEARR_OFF <= AU /\ AU + (K_FREEARR_MAX - c_mapped_free_array (get_cls st c'')) <= aregion L c'' + K_REGION).
      { subst AU. unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q5 Q6. lia. }
      destruct FA as [FA1 FA2].
      pose proof (farr_vs_user L c'' c _ _ UB (rup n 8) ltac:(clear -PC0 ABUB; lia) ltac:(clear -PC0 UBS; lia) FA1 FA2) as D.
      assert (AM : AU mod 8 = 0) by (subst AU; generalize Q7 RM''; clear; unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAP; intros; Z.div_mod_to_equations; lia).
      apply Kshad.
      + rewrite shad_div. unfold ASHOFF, K_FREEARR_OFF in *. clear -FA1 RI1 RES RHI. Z.div_mod_to_equations. lia.
      + rewrite shad_div, shlen_div. unfold ASHOFF, K_SPACE_SIZE in *. clear -FA2 RI2 RI3 RES RHI. Z.div_mod_to_equations. lia.
      + clear -POS''; lia.
      + rewrite EGQ. destruct D as [D|D]; [left; apply shad_sep; [exact D| exact AM] | right; apply shad_sep; [exact D| exact UB16']]. }
  (* [comment removed for export] *)
  assert (HS' : ASEC L st' X' m').
  { eapply (hs_frame _ HL L st st' X X' m m'); [exact HS | exact MUn | exact WM | |].
    - unfold sec_untouched, aknown. unfold AINSTANCE, K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
      assert (SHB : 2201439137792 <= shad UB /\ shad UB + gq <= 17594333495296) by (clear -SHLO SHHI SE GR3 GFS GE EGQ G0; lia).
      (* [comment removed for export] *)
      assert (SHB1 : shad (al_space_beg L) + 536870912 <= shad (aregion L c)).
      { rewrite !shad_div. unfold aregion, K_REGION, K_NUM_CLASSES in *. change (2^32) with 4294967296 in *. clear -HC. Z.div_mod_to_equations. lia. }
      assert (SHB2 : shad (aregion L c) + shlen (c_mapped_user (get_cls st c)) <= shad (al_space_beg L) + 17179869184).
      { (pose proof (alayout_space L ALO) as ndP__; nd_pre ndP__ 4%nat; intros _ _ SPal _; nd_post). rewrite !shad_div, shlen_div. unfold aregion, K_REGION, K_ALIGN, K_FREEARR_OFF, K_NUM_CLASSES in *. change (2^32) with 4294967296 in *.
        clear -HC G4 SPal. Z.div_mod_to_equations. lia. }
      (* [comment removed for export] *)
      apply Forall_cons; [cbn [fst snd]; intros a Ha; do 4 right; left; clear -Ha CEIL LO; lia |].
      do 4 (apply Forall_cons; [cbn [fst snd]; intros a Ha; left; left; clear -Ha; unfold AIMG_HI, AINSTANCE; lia |]).   (* [comment removed for export] *)
      do 4 (apply Forall_cons; [cbn [fst snd]; intros a Ha; do 5 right; left; clear -Ha OT TBND TIMG; lia |]).
      apply Forall_cons; [cbn [fst snd]; intros a Ha; do 7 right; left; clear -Ha G5 G6 ABUB S8 EUB RSP; lia |].
      apply Forall_cons; [cbn [fst snd]; intros a Ha; right; left; clear -Ha SE GR3 GFS GE EGQ G0 SHM1 SHM2 SHB1 SHB2; lia |].
      apply Forall_cons; [cbn [fst snd]; intros a Ha; do 8 right; left; clear -Ha; lia |].
      apply Forall_cons; [cbn [fst snd]; intros a Ha; do 9 right; left; clear -Ha; lia |].
      apply Forall_cons; [cbn [fst snd]; intros a Ha; clear -Ha RES RHI RSP LSTF; destruct LSTF as [Z0|(_ & _ & _ & F3 & F4)]; [rewrite Z0, qsz_0 in Ha; left; left; unfold AIMG_HI, AINSTANCE; lia| pose proof (qsz_bound lst); do 7 right; left; lia] |].   (* [comment removed for export] *)
      apply Forall_cons; [cbn [fst snd]; intros a Ha; clear -Ha RES RHI RSP EBF EBNZ; destruct EBF as [Z1|(_ & _ & E3 & E4)]; [exfalso; lia| do 7 right; left; lia] |].
      apply Forall_cons; [cbn [fst snd]; intros a Ha; clear -Ha RES RHI RSP LSTF GLF; destruct GLF as [[_ Z2]|(_ & _ & [Z2|(_ & _ & _ & H3 & H4)])];
        [ subst gl; destruct LSTF as [Z0|(_ & _ & _ & F3 & F4)]; [left; left; unfold AIMG_HI, AINSTANCE; lia| do 7 right; left; lia] | left; left; unfold AIMG_HI, AINSTANCE; lia | do 7 right; left; lia] |].
      apply Forall_nil.
    - exact (sec_same_core st st' SC (sec_chunks_qperm st st' ELIVE (st_after_enq_qfilt is_sec st (CPrim c n) eq_refl))). }
  assert (BL' : ablocks L st' X' LB) by (subst X'; exact (ablocks_xbatchR L st st' X LB k24 ELIVE BL)).
  assert (FKD : forall cls FA sz, In (mkABlock (ABFake cls) FA sz) LB -> al_fake L <= FA /\ 0 <= sz /\ FA + sz <= al_fake L + 11571200)
    by (intros cls FA sz Hin; exact (proj1 (proj2 BL) cls FA sz Hin)).
  pose proof (ao_fake L ALO) as FKO. (pose proof (aobj_int _ _ FKO ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros FKi FKa [kF FBND]; nd_post). unfold aobj in FKO.   (* [comment removed for export] *)
  pose proof (ad_t_fake L ALO) as D_t_f. pose proof (ad_fake_res L ALO) as D_f_res. pose proof (ad_nodes_fake L ALO) as D_n_f. pose proof (ad_store_fake L ALO) as D_s_f.
  unfold adisj in D_t_f, D_f_res, D_n_f, D_s_f. box D_t_f. box D_f_res. box D_n_f. box D_s_f.
  assert (HFK' : AFK L LB m').
  { eapply (hf_frame _ HL L LB m m'); [exact HFK | exact MUn | exact WM |].
    - pose proof (ao_dtls L ALO) as DTO. (pose proof (aobj4_int _ DTO) as ndP__; nd_pre ndP__ 4%nat; intros _ _ [kD DBND] [jD DIMG]; nd_post). unfold aobj in DTO.   (* [comment removed for export] *)
      pose proof (ad_t_dtls L ALO) as D1. pose proof (ad_dtls_res L ALO) as D2. pose proof (ad_nodes_dtls L ALO) as D3. pose proof (ad_store_dtls L ALO) as D4.
      unfold adisj in D1, D2, D3, D4.
      unfold fake_untouched. unfold K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
      assert (SHF : (shad (al_fake L) + shlen 11571200 <= shad UB \/ shad UB + gq <= shad (al_fake L))
                    /\ 2148238848 <= shad (al_fake L) /\ shad (al_fake L) + shlen 11571200 <= 17594333495296).   (* [comment removed for export] *)
      { split; [| rewrite shad_div, shlen_div; unfold ASHOFF; pose proof atop_range as AR8; clear -FKO FKi FBND AR8; Z.div_mod_to_equations; lia].
        pose proof D_f_res as DFR. unbox DFR. rewrite EGQ. destruct DFR as [D|D].
        - left. apply shad_sep; [| clear -FKO FKi FBND; Z.div_mod_to_equations; lia]. clear -D RSP G5 ABUB. lia.
        - right. apply shad_sep; [| exact UB16']. clear -D RSP G6 UBS. lia. }
      (nd_pre SHF 3%nat; intros SHF1 SHF2 SHF3; nd_post).
      assert (SHB : 2201439137792 <= shad UB /\ shad UB + gq <= 17594333495296) by (clear -SHLO SHHI SE GR3 GFS GE EGQ G0; lia).
      pose proof D_t_f as DTF; unbox DTF. pose proof D_f_res as DFR; unbox DFR. pose proof D_n_f as DNF; unbox DNF. pose proof D_s_f as DSF; unbox DSF.
      assert (LSTR : (lst = 0 /\ qsz lst = 8) \/ (al_res L + 4096 <= lst /\ lst + 8192 <= al_res L + 137439023104 /\ qsz lst = 8192))   (* [comment removed for export] *)
        by (destruct LSTF as [Z0|(_ & _ & _ & F3 & F4)]; [left; split; [exact Z0| apply qsz_eq0; exact Z0]| right; split; [exact F3| split; [exact F4| apply qsz_pos; clear -F3 RES RHI; lia]]]).
      assert (EBR : al_res L + 4096 <= eb /\ eb + 8192 <= al_res L + 137439023104) by (destruct EBF as [Z0|(_ & _ & F3 & F4)]; [exfalso; clear -Z0 EBNZ; lia| split; assumption]).   (* [comment removed for export] *)
      assert (GLRR : gl = lst \/ gl = 0 \/ (al_res L + 4096 <= gl /\ gl + 8192 <= al_res L + 137439023104))
        by (destruct GLF as [[_ Z2]|(_ & _ & [Z2|(_ & _ & _ & H3 & H4)])]; [left; exact Z2| right; left; exact Z2| right; right; split; assumption]).
      (apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | idtac]]]]]]]]]]]]]]]]).
      apply Forall_nil. }
  (* [comment removed for export] *)
  assert (GNB : g_nb g = Z.of_nat (length (a_qglob st))) by reflexivity.
  assert (GFST : g_fst g = qfirst L (q_glob Q)) by reflexivity.
  assert (GQB : g_qb g = a_qglob_bytes st) by reflexivity.
  assert (GFU : g_full g = match a_qglob st with [] => false | _ :: _ => true end) by reflexivity.
  destruct DKP as [MX' DKP'].
  (pose proof (qnum_freeR st (CPrim c n) NUM ltac:(cbn [chunk_size]; clear -N1; lia) NOREC) as ndP__; nd_pre ndP__ 5%nat; intros NUM' NB2a NB2b NB2c NF2; nd_post).
  fold st2 st' in NUM', NB2a, NB2b, NB2c, NF2.
  pose proof (st_after_q st2) as [DRN NDR]. fold st' in DRN, NDR.
  assert (QK' : aquar_glob_const m').
  { split; [| exact MX']. eapply cells_frame; [exact QK | exact MUn | exact WM |]. cbn [cells_size csize Nat.add]. apply Kimg; clear; unfold AQ_MAX, AIMG_HI; lia. }
  assert (IA' : aintal true m').
  { split; [exact FL'|]. split; [exact IAS'|]. intros _ j Hj. apply IAM'. revert Hj. clear. unfold AIA_MAP1_LEN. cbn. lia. }
  (* [comment removed for export] *)
  assert (BLST : forall q, In q (q_loc Q ++ q_glob Q) -> abatch_addr L (qb_slot q) <> lst ->
      abatch_addr L (qb_slot q) + 8192 <= lst \/ lst + 8192 <= abatch_addr L (qb_slot q) \/ lst = 0).
  { intros q Hq NE. destruct LSTF as [Z0|((ql & Hql & Eql) & _)]; [right; right; exact Z0|].
    destruct (BDIS q ql Hq ltac:(apply in_or_app; left; exact Hql)) as [E|E]; [exfalso; apply NE; rewrite Eql; exact E| rewrite Eql].
    destruct E as [E|E]; [left; exact E| right; left; exact E]. }
  assert (BFR : forall q, In q (q_loc Q ++ q_glob Q) -> abatch_addr L (qb_slot q) <> lst -> abatch_addr L (qb_slot q) <> gl ->
      disjoint_from (Wf (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) (abatch_addr L (qb_slot q)) 8192).
  { intros q Hq NL NG. (nd_pre (BGEO q Hq) 4%nat; intros _ _ F3 F4; nd_post). pose proof (SEPQ q Hq) as SQ. pose proof (BLST q Hq NL) as DL.
    assert (DE : eb = lst \/ abatch_addr L (qb_slot q) + 8192 <= eb \/ eb + 8192 <= abatch_addr L (qb_slot q)).
    { destruct EBK as [E|[EA2 E]]; [left; exact E| right]. rewrite E.
      destruct (KDIS q Hq EA2) as [D|D]; [right; exact D| left; exact D]. }
    assert (DG : gl = lst \/ gl = 0 \/ abatch_addr L (qb_slot q) + 8192 <= gl \/ gl + 8192 <= abatch_addr L (qb_slot q)).
    { destruct GLF as [[_ E]|(_ & _ & [Z0|((qg & Hqg & Eqg) & _)])]; [left; exact E| right; left; exact Z0| right; right].
      destruct (BDIS q qg Hq ltac:(apply in_or_app; right; exact Hqg)) as [E|E]; [exfalso; apply NG; rewrite Eqg; exact E| rewrite Eqg; exact E]. }
    apply Kres; clear -F3 F4 RES RHI SQ DL DE DG ABUB S8 EUB; lia. }
  assert (HQ' : AQUAR L st' X' m').
  { subst ek. unfold ek_of in EKP, EK, QC', DKP', EEB, SB1, GDR, GL, GLST.
    rewrite EA in EKP, EK, QC', DKP', EEB, SB1, GDR, GLST; cbn [ek_nb ek_fst ek_lst ek_delta ek_b ek_post ek_pre] in EKP, EK, QC', DKP', EEB, SB1, GDR, GL, GLST.
    - (* [comment removed for export] *)
      (nd_pre (NEWF EA) 8%nat; intros NK24 NB24 KK24 NIB JK FK CIN POS; nd_post).
      (nd_pre EKP 6%nat; intros C24' [stj' SJ'] NBc NAc [bs NJc] OLDc; nd_post).
      pose proof EAPP0 as EAPP.
      set (nbt := mkABatch 1 (n + 8192) [CPrim c n]) in *.
      set (qn := mkQB k24 [k]) in *.
      assert (Q2 : a_qloc st2 = a_qloc st ++ [nbt] /\ a_qloc_bytes st2 = a_qloc_bytes st + (n + 8192) /\ a_qglob st2 = a_qglob st /\ a_qglob_bytes st2 = a_qglob_bytes st).
      { subst st2. unfold st_enq. rewrite EAPP. (pose proof (enq_new_core (CPrim c n) st) as ndP__; nd_pre ndP__ 7%nat; intros _ E1 E2 _ E3 E4 _; nd_post).
        rewrite E1, E2, E3, E4. subst nbt. cbn [chunk_size]. unfold Q_BATCH_BYTES.
        split; [reflexivity|]. split; [clear; lia|]. split; reflexivity. }
      (nd_pre Q2 4%nat; intros QL2 QB2 QG2 QGB2; nd_post).
      assert (FSTE : (if match a_qloc st with [] => false | _ :: _ => true end then qfirst L (q_loc Q) else abatch_addr L k24) = qfirst L (q_loc Q ++ [qn])).
      { rewrite qfirst_app_r. subst qn; cbn [qb_slot]. generalize LN1. clear. generalize (a_qloc st) (q_loc Q).
        intros [|x1 r1] [|x2 r2] LL; cbn in LL; first [reflexivity | discriminate]. }
      rewrite FSTE in QC'. rewrite FSTE in DKP'.
      assert (QLST' : qlast L (q_loc Q ++ [qn]) = abatch_addr L k24) by (subst qn; apply qlast_app1).
      (* [comment removed for export] *)
      assert (GNL : forall q, In q (q_glob Q) -> abatch_addr L (qb_slot q) <> lst).
      { intros q Hq E. assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; right; exact Hq).
        destruct LSTF as [Z0|((q' & Hq' & Eq') & _)].
        - (nd_pre (BGEO q INq) 4%nat; intros _ _ F3 _; nd_post). clear -F3 RES RHI E Z0. lia.
        - apply in_split in Hq. (nd_pre Hq 3%nat; intros gs1 gs2 EQg; nd_post). apply in_split in Hq'. (nd_pre Hq' 3%nat; intros qs1 qs2 EQl; nd_post).
          apply (bslots_nodup_split L st X Q CP qs1 q' (qs2 ++ gs1) q gs2); [rewrite EQl, EQg; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; reflexivity|].
          pose proof (bslot_range L st X Q WF CP q INq). pose proof (bslot_range L st X Q WF CP q' ltac:(apply in_or_app; left; rewrite EQl; apply in_or_app; right; left; reflexivity)).
          rewrite Eq' in E. unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia. }
      (* [comment removed for export] *)
      assert (ABO' : abatches_to L m' (a_qloc st) (q_loc Q) (abatch_addr L k24)).
      { destruct (a_qloc st) as [|b0 l0] eqn:QL0.
        - replace (q_loc Q) with (@nil qbatchc) by (clear -LN1; destruct (q_loc Q); [reflexivity| cbn in LN1; discriminate]). exact I.
        - cbv iota beta in OLDc. destruct OLDc as [OLD1 OLD2]. rewrite <- QL0 in *.
          assert (LNE : a_qloc st <> []) by (rewrite QL0; discriminate).
          assert (QL : a_qloc st = removelast (a_qloc st) ++ [List.last (a_qloc st) dummy_batch]) by (apply app_removelast_last; exact LNE).
          assert (LQ : (0 < length (q_loc Q))%nat) by (rewrite LN1, QL0; cbn; clear; lia).
          assert (QQ : q_loc Q = removelast (q_loc Q) ++ [List.last (q_loc Q) dummy_qb]) by (apply app_removelast_last; clear -LQ; destruct (q_loc Q); [cbn in LQ; clear -LQ; lia| discriminate]).
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
            { rewrite QLST. intros E. apply in_split in Hq. (nd_pre Hq 3%nat; intros qs1 qs2 EQl; nd_post).
              apply (bslots_nodup_split L st X Q CP qs1 q qs2 qz (q_glob Q)); [rewrite QQ, EQl; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; reflexivity|].
              pose proof (bslot_range L st X Q WF CP q INq). pose proof (bslot_range L st X Q WF CP qz ltac:(apply in_or_app; left; rewrite QQ; apply in_or_app; right; left; reflexivity)).
              unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia. }
            apply BFR; [exact INq | exact NEq |].
            destruct GLF as [[_ E]|(GD & GQL & [Z0|((qg & Hqg & Eqg) & _)])]; [rewrite E; exact NEq| rewrite Z0; (nd_pre (BGEO q INq) 4%nat; intros _ _ F3 _; nd_post); clear -F3 RES RHI; lia|].
            rewrite Eqg. intros E. apply in_split in Hq. (nd_pre Hq 3%nat; intros qs1 qs2 EQl; nd_post). apply in_split in Hqg. (nd_pre Hqg 3%nat; intros gs1 gs2 EQg; nd_post).
            apply (bslots_nodup_split L st X Q CP qs1 q (qs2 ++ [qz] ++ gs1) qg gs2); [rewrite QQ, EQl, EQg; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; reflexivity|].
            pose proof (bslot_range L st X Q WF CP q INq). pose proof (bslot_range L st X Q WF CP qg ltac:(apply in_or_app; right; rewrite EQg; apply in_or_app; right; left; reflexivity)).
            unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia.
          + cbn [abatches_to]. split; [| exact I].
            unfold abatch_cells. cbv zeta. change (hd (abatch_addr L k24) (qaddrs L [])) with (abatch_addr L k24). rewrite <- QLST.
            split; [rewrite FULL; exact OLD1|]. split; [exact OLD2|]. split; [| split; [exact Z4| split; [exact Z5| exact Z6]]].
            rewrite FULL. replace (Q_BATCH_BYTES - 24 - 8 * Q_BATCH) with 0 by reflexivity. unfold Q_BATCH. apply junk_nil; (destruct LSTF as [Z0|(_ & _ & _ & F3 & F4)]; [clear -Z0; lia | atop_facts; clear -F3 F4 RES RHI; lia]). }
      (* [comment removed for export] *)
      assert (ABN' : abatch_cells L m' nbt qn 0).
      { unfold abatch_cells. cbv zeta. subst nbt qn. cbn [qb_slot qb_ks b_size b_count b_chunks]. rewrite qhdrs_cons. cbn [qhdrs app map qhdr]. rewrite <- EAB, <- EUB.
        split; [exact NBc|]. split; [exact NAc|]. split; [exists bs; unfold Q_BATCH_BYTES; exact NJc|]. split; [reflexivity|]. split; [reflexivity| unfold Q_BATCH; clear; lia]. }
      assert (ABL' : abatches_to L m' (a_qloc st ++ [nbt]) (q_loc Q ++ [qn]) 0).
      { apply abatches_to_app; [exact LN1|]. split; [cbn [qaddrs map hd]; subst qn; cbn [qb_slot]; exact ABO'|]. cbn [abatches_to]. split; [exact ABN'| exact I]. }
      assert (CP2 : qcoupled L st2 X' (mkQConc (q_loc Q ++ [qn]) (q_glob Q) true pend)).
      { subst X' qn nbt.
        apply (qcoupled_new_pend L st X Q c k n b1 ctx l1 l2 st2 k24 (c_count (get_cls st K_BATCH_CLASS)) (n + 8192) true pend XB WF CP PEND eq_refl POS NK24 KK24 NIB QL2 QG2). }
      destruct (Z.lt_ge_cases Q_CACHE (a_qloc_bytes st2)) as [DR|NDRN].
      + (* [comment removed for export] *)
        (nd_pre (DRN DR) 4%nat; intros QL3 QB3 QG3 QGB3; nd_post).
        assert (GD : g_drain g = true) by (rewrite GDR; apply Z.ltb_lt; rewrite <- QB2; exact DR).
        unfold tcache_post in QC'. rewrite GD in DKP', QC'.
        destruct DKP' as [GC' GLN].
        exists (mkQConc [] (q_glob Q ++ (q_loc Q ++ [qn])) true pend). unfold AQUAR_at. cbn [q_loc q_glob q_ia].
        rewrite QL3, QB3, QG3, QGB3, QL2, QG2, QB2, QGB2.
        split; [exact QK'|]. split; [| split; [| split; [exact IA'| split]]].
        * split; [cbn [length qfirst qlast qaddrs map hd last Z.of_nat]; exact QC'| exact I].
        * split.
          -- rewrite length_app, Nat2Z.inj_add, <- GNB. rewrite length_app. cbn [length]. rewrite Nat2Z.inj_add. change (Z.of_nat 1) with 1.
             rewrite qlast_app by (intros Enil; apply app_eq_nil in Enil; destruct Enil as [_ Enil]; discriminate). rewrite QLST'.
             assert (FE : qfirst L (q_glob Q ++ q_loc Q ++ [qn]) = (if g_full g then g_fst g else qfirst L (q_loc Q ++ [qn]))).
             { rewrite GFU, GFST. destruct (a_qglob st) eqn:QG0.
               - replace (q_glob Q) with (@nil qbatchc) by (clear -LN2; destruct (q_glob Q); [reflexivity| cbn in LN2; discriminate]). reflexivity.
               - apply qfirst_app. destruct (q_glob Q); [cbn in LN2; discriminate| discriminate]. }
             rewrite FE, <- GQB. exact GC'.
          -- unfold abatches. apply abatches_to_app; [exact LN2|]. split.
             ++ (* [comment removed for export] *)
                rewrite hd_qaddrs by (intros Enil; apply app_eq_nil in Enil; destruct Enil as [_ Enil]; discriminate).
                destruct (a_qglob st) as [|bg0 lg0] eqn:QG0.
                ** replace (q_glob Q) with (@nil qbatchc) by (clear -LN2; destruct (q_glob Q); [reflexivity| cbn in LN2; discriminate]). exact I.
                ** rewrite <- QG0 in *.
                   assert (GNE : a_qglob st <> []) by (rewrite QG0; discriminate).
                   assert (QG : a_qglob st = removelast (a_qglob st) ++ [List.last (a_qglob st) dummy_batch]) by (apply app_removelast_last; exact GNE).
                   assert (LQg : (0 < length (q_glob Q))%nat) by (rewrite LN2, QG0; cbn; clear; lia).
                   assert (QQg : q_glob Q = removelast (q_glob Q) ++ [List.last (q_glob Q) dummy_qb]) by (apply app_removelast_last; clear -LQg; destruct (q_glob Q); [cbn in LQg; clear -LQg; lia| discriminate]).
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
                       { intros E. apply in_split in Hq. (nd_pre Hq 3%nat; intros gs1 gs2 EQg; nd_post).
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
                       (nd_pre (BGEO qgz INgz) 4%nat; intros _ _ F3 F4; nd_post). pose proof (SEPQ qgz INgz) as SQ. pose proof (BLST qgz INgz NGL) as DL.
                       pose proof (KDIS qgz INgz EA) as DE.
                       assert (D8 : forall A8 kk, abatch_addr L (qb_slot qgz) + 8 <= A8 -> A8 + kk <= abatch_addr L (qb_slot qgz) + 8192 -> 0 <= kk ->
                                  disjoint_from (Wf (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) A8 kk).
                       { intros A8 kk HA HK KK0. apply Kres; clear -F3 F4 RES RHI SQ DL DE EEB GLS ABUB S8 EUB HA HK KK0; lia. }
                       pose proof Y1 as Y1'. rw_split Y1' 1%nat YN YR.
                       eapply cells_frame in YR; [| exact MUn | exact WM | cbn [cells_size csize Nat.add]; apply D8; clear; lia].
                       rw_join GLN YR YH.
                       split; [exact YH|]. split; [| split; [| split; [exact Y4| split; [exact Y5| exact Y6]]]].
                       --- eapply u64arr_frame; [exact Y2 | exact MUn | exact WM |]. rewrite length_map, qhdrs_length by exact Y5. rewrite <- Y4.
                           apply D8; unfold Q_BATCH in Y6; clear -Y6; lia.
                       --- eapply junk_frame; [exact Y3 | exact MUn | exact WM |]. intros Hp. apply D8; unfold Q_BATCH, Q_BATCH_BYTES in *; clear -Y6 Hp; lia.
             ++ exact ABL'.
        * exact (qcoupled_drain L st2 st' X' (mkQConc (q_loc Q ++ [qn]) (q_glob Q) true pend) true CP2 QL3 QG3).
        * exact NUM'.
      + (* [comment removed for export] *)
        pose proof (NDR NDRN) as EST.
        assert (GD : g_drain g = false) by (rewrite GDR; apply Z.ltb_ge; rewrite <- QB2; exact NDRN).
        unfold tcache_post in QC'. rewrite GD in DKP', QC'.
        exists (mkQConc (q_loc Q ++ [qn]) (q_glob Q) true pend). unfold AQUAR_at. cbn [q_loc q_glob q_ia].
        rewrite EST, QL2, QG2, QB2, QGB2.
        split; [exact QK'|]. split; [| split; [| split; [exact IA'| split]]].
        * split; [| exact ABL'].
          rewrite length_app. cbn [length]. rewrite Nat2Z.inj_add. change (Z.of_nat 1) with 1. rewrite QLST'. exact QC'.
        * split; [rewrite <- GNB, <- GFST, <- GL, <- GQB; exact DKP'|].
          unfold abatches. eapply abatches_to_frame; [exact MUn | exact WM | exact ABG |].
          intros q Hq. assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; right; exact Hq).
          apply BFR; [exact INq | exact (GNL q Hq) | rewrite EGL; unfold dk_glst; rewrite GD; exact (GNL q Hq)].
        * first [rewrite EST | idtac]. exact CP2.
        * first [rewrite <- EST | idtac]. exact NUM'. }
  idtac "CHECKPOINT-E".
  (* [comment removed for export] *)
  assert (HBK : forall blk, In blk LB -> disjoint_from (Wf (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) (ab_addr blk) (ab_size blk)).
  { intros [[q|cls] A' n'] Hin; cbn [ab_addr ab_size].
    - destruct (proj1 BL q A' n' Hin) as [(b & Hb & Sb & Ub & Nb)|(mb & msz & Lp & EUA & Gs)].
      + assert (NEq : xb_st b <> BQuar) by (rewrite Sb; discriminate).
        pose proof (other_key (AHQm DI ASEC AFK Q) L st X m BQuar c k n b1 ctx l1 l2 AR XB b Hb NEq) as NE1.
        destruct (busy_slot_range L st X b WF Hb) as [HCb HKb].
        pose proof (awf_fits L st X b WF Hb) as FIT. unfold xb_fits in FIT. rewrite Sb in FIT.
        pose proof (busy_of_In_nodup L st X b WF Hb) as BOF.
        unfold xb_user, xb_alloc in Ub. subst A' n'.
        set (cb := xb_class b) in *. set (kb := xb_slot b) in *.
        (pose proof (slot_geo L st X cb kb ALO WF HCb HKb) as ndP__; nd_pre ndP__ 12%nat; intros T16 TM16 TAL P1 P2 P3 P4 P5 P6 P7 P8 _; nd_post).
        pose proof (slots_sep_any L st X cb kb c k ALO WF HCb HC HKb KR ltac:(clear -NE1; lia)) as D9. rewrite <- EAB, <- ES in D9.
        assert (DQ : forall q', In q' (q_loc Q ++ q_glob Q) ->
            aslot_addr L cb kb + size_of_class cb <= abatch_addr L (qb_slot q') \/ abatch_addr L (qb_slot q') + 8192 <= aslot_addr L cb kb).
        { intros q' Hq'. (nd_pre (bslot_busy L st X Q CP q' Hq') 5%nat; intros yq Hyq Syq Cyq Kyq; nd_post).
          assert (NE : cb <> K_BATCH_CLASS \/ kb <> qb_slot q').
          { destruct (Z.eq_dec cb K_BATCH_CLASS) as [E1|NE0]; [| left; exact NE0]. right. intros E2.
            pose proof (busy_of_In_nodup L st X yq WF Hyq) as BY. rewrite Cyq, Kyq, <- E1, <- E2, BOF in BY. injection BY as EE. subst yq. rewrite Sb in Syq. discriminate. }
          pose proof (slots_sep_any L st X cb kb K_BATCH_CLASS (qb_slot q') ALO WF HCb (K24) HKb (bslot_range L st X Q WF CP q' Hq') NE) as D.
          rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
        assert (DK24 : enq_is_app st = false -> aslot_addr L cb kb + size_of_class cb <= abatch_addr L k24 \/ abatch_addr L k24 + 8192 <= aslot_addr L cb kb).
        { intros EA2. (nd_pre (NEWF EA2) 4%nat; intros _ NB KK _; nd_post).
          assert (NE : cb <> K_BATCH_CLASS \/ kb <> k24).
          { destruct (Z.eq_dec cb K_BATCH_CLASS) as [E1|NE0]; [| left; exact NE0]. right. intros E2. rewrite <- E1, <- E2, BOF in NB. discriminate. }
          pose proof (slots_sep_any L st X cb kb K_BATCH_CLASS k24 ALO WF HCb (K24) HKb KK NE) as D.
          rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
        assert (DL : lst = 0 \/ aslot_addr L cb kb + size_of_class cb <= lst \/ lst + 8192 <= aslot_addr L cb kb).
        { destruct LSTF as [Z0|((q' & Hq' & Eq') & _)]; [left; exact Z0| right]. rewrite Eq'. apply DQ. apply in_or_app; left; exact Hq'. }
        assert (DE : eb = lst \/ aslot_addr L cb kb + size_of_class cb <= eb \/ eb + 8192 <= aslot_addr L cb kb).
        { destruct EBK as [E|[EA2 E]]; [left; exact E| right]. rewrite E. exact (DK24 EA2). }
        assert (DG : gl = lst \/ gl = 0 \/ aslot_addr L cb kb + size_of_class cb <= gl \/ gl + 8192 <= aslot_addr L cb kb).
        { destruct GLF as [[_ E]|(_ & _ & [Z0|((q' & Hq' & Eq') & _)])]; [left; exact E| right; left; exact Z0| right; right].
          rewrite Eq'. apply DQ. apply in_or_app; right; exact Hq'. }
        apply Kres; [clear -P5 RSP FIT; lia | clear -P6 RSP FIT; unfold K_SPACE_SIZE in *; lia | clear -FIT; lia
                    | clear -D9 FIT ABUB S8 EUB; lia | clear -DL FIT P5 RSP RES RHI; lia | clear -DE DL FIT P5 RSP RES RHI; lia | clear -DG DL FIT P5 RSP RES RHI; lia].
      + (* [comment removed for export] *)
        cbn [sec_wf1] in Gs. (nd_pre Gs 7%nat; intros Gs1 Gs2 Gs3 Gs4 Gs5 Gs6 (Ct & Cc & Cr & Cp & Cn & Cs & Cf & Cd); nd_post).
        pose proof (sec_facts n' ltac:(clear -Gs5; lia) Gs6) as SF. subst A'. unfold SEC_UOFF, K_HIGH_MEM in *.
        unfold ablk, KLS, AIMG_HI in Gs2.   (* [comment removed for export] *)
        apply Kobj; clear -Gs2 Gs3 Gs4 Gs5 SF Ct Cr Cn Cs; lia.
    - (nd_pre (FKD cls A' n' Hin) 3%nat; intros K1 K2 K3; nd_post). atop_facts.
      pose proof D_t_f as DTF; unbox DTF. pose proof D_f_res as DFR; unbox DFR. pose proof D_n_f as DNF; unbox DNF. pose proof D_s_f as DSF; unbox DSF.
      apply Kobj; [clear -K1 K3 FKO FKi FBND; lia | clear -K3 FKO FKi FBND; lia | exact K2 | clear -K1 K3 DTF; lia
                  | clear -K1 K3 DFR; lia | clear -K1 K3 DNF; lia | clear -K1 K3 DSF; lia]. }
  assert (HFS : forall cls FA sz, In (mkABlock (ABFake cls) FA sz) LB -> forall a', FA <= a' < FA + sz ->
      disjoint_from (Wf (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) (shad a') 1).
  { intros cls FA sz Hin a' Ha'.
    (nd_pre (FKD cls FA sz Hin) 3%nat; intros K1 K2 K3; nd_post). atop_facts.
    apply Kshad; [rewrite shad_div; unfold ASHOFF; clear -K1 FKO FKi FBND Ha'; Z.div_mod_to_equations; lia
                 | rewrite shad_div; unfold ASHOFF; clear -K3 FKO FKi FBND Ha'; Z.div_mod_to_equations; lia | clear; lia |].
    pose proof D_f_res as DFR; unbox DFR. destruct DFR as [D|D].
    - left. rewrite (shad_div a'), (shad_div UB). clear -D Ha' K3 RSP G5 ABUB UB16'. Z.div_mod_to_equations. lia.
    - right. rewrite EGQ, shlen_div, (shad_div a'), (shad_div UB). unfold K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
      clear -D Ha' K1 RSP G6 UBS RUP8 UB16'. Z.div_mod_to_equations. lia. }
  (* [comment removed for export] *)
  assert (TLSK : forall TA tk, ATPv + -200 <= TA -> TA + tk <= ATPv + 312 -> 0 <= tk ->
      disjoint_from (Wf (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) TA tk).
  { intros TA tk TH1 TH2 TH3. pose proof ATPv_img as TI. apply Kimg; clear -TH1 TH2 TH3 TI; unfold AIMG_HI; lia. }
  assert (TLSS : forall a', ATPv + -200 <= a' < ATPv + 312 ->
      disjoint_from (Wf (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) (shad a') 1).
  { intros a' Ha'. pose proof ATPv_img as TI. apply Klow; clear -Ha' TI; try (rewrite shad_div; unfold ASHOFF); try Z.div_mod_to_equations; lia. }
  assert (PSP : shad UB + gq <= shad ATOP).
  { rewrite EGQ, shlen_div, (shad_div UB), (shad_div ATOP). atop_facts. clear -UBS G8 ABCE CEIL LO RUP8 UB16'. Z.div_mod_to_equations. lia. }
  (* [comment removed for export] *)
  exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
  split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split.
  { eapply (aheap_pres_free CI); [exact KF | exact CI_OK | exact MUn | exact WM | exact HBK | exact HFS | exact PSP | exact TLSK | exact TLSS | apply Klow; unfold AIMSH_LO, AIMSH_LEN; clear; lia
      | rewrite <- (ao_ahm_eq L ALO); unfold AAHM_SZ; pose proof (ao_ahm L ALO) as OAH; pose proof (aobj_img _ _ OAH ltac:(clear; lia)) as OAHI;
      pose proof (ad_ahm_t L ALO) as DA1; pose proof (ad_ahm_res L ALO) as DA2; pose proof (ad_ahm_nodes L ALO) as DA3; pose proof (ad_ahm_store L ALO) as DA4;
      unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI, adisj in OAH, OAHI, DA1, DA2, DA3, DA4; apply Kobj; clear -OAH OAHI DA1 DA2 DA3 DA4; lia]. }
  split; [exact ALO|]. split; [exact (arng_core L RNG st st' SC (sec_chunks_qperm st st' ELIVE (st_after_enq_qfilt is_sec st (CPrim c n) eq_refl)) ARNG)|]. split; [| exact HFK'].
  exists X'. split; [| exact BL'].
  split; [exact WF'|]. split; [exact RT'|]. split; [exact INST'|]. split; [exact THR'|]. split; [exact CLS'|].
  split; [exact HQ'|]. split; [exact HS'|]. split; [exact DEP'|]. split; [exact HRO'|]. split; [exact HRT2'|]. split; [exact AVL'| exact RT3'].
Qed.
End Zd1.
#[using="HL CI_OK"] Theorem store_freeR : ltac:(let t := eval cbv delta [store_freeR__stmt] in store_freeR__stmt in exact t).
Proof. exact store_freeR__body. Qed.

End S.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Exec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepStore__A3W.ARepStore.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AFreeModel.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.AFreeGeo.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRead.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tail.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_afree_icpt.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.F_afree_arep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_tabscan__A3W.AFreeStoreK.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.AFreeStore.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_fast__A3W.F_afree_arepR.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac sg_set := let GG := fresh "GG" in (match goal with |- ?G => set (GG := G) end).
Local Ltac sg_unset := match goal with |- ?G => is_var G; subst G end.
Local Ltac sg_destr := sg_set; repeat match goal with H : _ /\ _ |- _ => destruct H end; sg_unset.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation Wf sp t UB gq nodes store lst eb gl :=
  ([(sp - 4096, sp); (0xab708, 0xab730); (0xafc00, 0x130c30); (0x13e488, 0x13e48c); (ADEPOT_LO, ADEPOT_HI);
    (t + 80, t + 112); (t + 2128, t + 2132); (t + 2784, t + 2792); (t + 2800, t + 3169);
    (UB - 16, UB + 8); (shad UB, shad UB + gq);
    (nodes, nodes + 1048576); (store, store + 8388608);
    (lst, lst + qsz lst); (eb, eb + 8192); (gl, gl + 8)]%Z) (only parsing).      (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac fu_drop_fake := repeat match goal with H : context [al_fake _] |- _ => clear H end.
Ltac fu_drop_dtls := repeat match goal with H : context [al_dtls _] |- _ => clear H end.
Ltac fu_drop_tls := repeat match goal with H : context [ATPv] |- _ => clear H | H : context [kt_img] |- _ => clear H end.
Ltac fu_focus :=
  lazymatch goal with
  | |- context [al_fake _] => fu_drop_dtls; fu_drop_tls
  | |- context [al_dtls _] => fu_drop_fake; fu_drop_tls
  | |- context [ATPv] => fu_drop_fake; fu_drop_dtls
  | |- _ => fu_drop_fake; fu_drop_dtls; fu_drop_tls
  end.
Ltac fu_lia := first [solve [fu_focus; lia] | lia].
(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
(* [comment removed for export] *)
#[using="Type"] Local Lemma aobj_int : forall a n, aobj a n -> 0x10000 <= n ->
  6307840 <= a /\ a + n <= ATOP /\ exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof.
  intros a n H Hn. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. (nd_pre H 5%nat; intros H1 H2 H3 H4 H5; nd_post).
  split; [lia|]. split; [lia|]. destruct H4; [exists 0 | exists 1]; lia.
Qed.
#[using="Type"] Local Lemma aobj4_int : forall a, aobj a 4096 ->
  4096 <= a /\ a + 4096 <= ATOP
  /\ (exists k, 0 <= k <= 1 /\ a + 4096 <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a)
  /\ (exists j, 0 <= j <= 1 /\ a + 4096 <= 65536 + j * 18446744073709551616 /\ 6307840 * j <= a).
Proof.
  intros a H. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. (nd_pre H 5%nat; intros H1 H2 H3 H4 H5; nd_post).
  split; [lia|]. split; [lia|]. split; [destruct H4; [exists 0 | exists 1]; lia | destruct H5 as [_ [H5|H5]]; [exists 0 | exists 1]; lia].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma ek_pre_b_hi : forall ek RNG t nb lst n hm m, ek_pre ek RNG t nb lst n hm m -> 0x10007fff8000 <= ek_b ek lst.
Proof.
  intros ek RNG t nb lst n hm m EK.
  destruct ek as [nx bsz cnt hs cnt24' maxc' csz' stj' | full nx bsz cnt24 maxc csz stj idxw chunks spacebeg b hs0]; cbn [ek_pre ek_b] in *.
  - (nd_pre EK 16%nat; intros NB1 LB CNT BSZ BSZN NX LA LEN LJ L0 L1 DTL DHL CR' STS' RL; nd_post). exact L0.
  - (nd_pre EK 20%nat; intros FULL SB CR CH LCH CNT NTH IXS STS HB BJ SBP B0 BL1 DTB DTL DBL DHB DHL RB; nd_post). exact B0.
Qed.

#[using="Type"] Lemma xbatch_free : forall X k24 c', xc_free (x_cls (xbatch X k24) c') = xc_free (x_cls X c').
Proof. intros. unfold xbatch. cbn. destruct (Z.eqb_spec c' K_BATCH_CLASS) as [->|]; reflexivity. Qed.
#[using="Type"] Lemma xbatch_cache : forall X k24 c',
  xc_cache (x_cls (xbatch X k24) c') = if c' =? K_BATCH_CLASS then removelast (xc_cache (x_cls X K_BATCH_CLASS)) else xc_cache (x_cls X c').
Proof. intros. unfold xbatch. cbn. destruct (Z.eqb_spec c' K_BATCH_CLASS) as [->|]; reflexivity. Qed.

#[using="Type"] Lemma ablocks_xbatchR : forall L st st' X LB k24, a_live st' = a_live st -> ablocks L st X LB -> ablocks L st' (xbatch X k24) LB.
Proof.
  intros L st st' X LB k24 EL B. eapply ablocks_mono; [exact B| | intros; rewrite EL; assumption].
  intros b p Hb _. unfold xbatch. cbn. right. exact Hb.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma sec_same_core : forall st s, same_core st s -> Permutation (sec_chunks_of s) (sec_chunks_of st) -> sec_same st s.
Proof.
  intros st s (E1 & E2 & E3 & E4 & E5 & E6 & E7 & _) P. unfold sec_same. rewrite E7, E6, E5, E1.
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [intros; tauto| exact P].
Qed.

#[using="Type"] Lemma qnum_freeR : forall st ch,
  qnum st -> 0 <= chunk_size ch ->
  let st2 := st_enq st ch in
  (Q_CACHE < a_qloc_bytes st2 -> a_qglob_bytes st2 + a_qloc_bytes st2 <= Q_MAX) ->
  qnum (st_after st2)
  /\ a_qloc_bytes st2 = batches_bytes (a_qloc st2) /\ a_qglob_bytes st2 = a_qglob_bytes st /\ a_qglob st2 = a_qglob st
  /\ Forall (fun b => Q_BATCH_BYTES <= b_size b) (a_qloc st2 ++ a_qglob st2).
Proof.
  intros st ch (N1 & N2 & N3 & N4 & N5) NN st2 NOREC.
  assert (S2 : a_qloc_bytes st2 = batches_bytes (a_qloc st2) /\ a_qglob_bytes st2 = a_qglob_bytes st /\ a_qglob st2 = a_qglob st
               /\ Forall (fun b => Q_BATCH_BYTES <= b_size b) (a_qloc st2 ++ a_qglob st2)).
  { subst st2. unfold st_enq. destruct (enq_app st ch) as [s|] eqn:E.
    - (nd_pre (enq_app_Some st ch s E) 5%nat; intros l bl QL NF ndR1__; nd_post; revert ndR1__; intros ->). cbn -[batches_bytes Z.add].
      cbn -[batches_bytes Z.add] in QL |- *. rewrite QL in N1, N3.
      rewrite batches_bytes_app, batches_bytes_cons, batches_bytes_nil in N1 |- *. cbn [b_size].
      split; [lia|]. split; [reflexivity|]. split; [reflexivity|].
      rewrite <- app_assoc in N3 |- *. apply Forall_app in N3. destruct N3 as [F1 F2]. inversion F2; subst.
      apply Forall_app. split; [exact F1|]. constructor; [cbn; lia| assumption].
    - (pose proof (enq_new_core ch st) as ndP__; nd_pre ndP__ 7%nat; intros _ G1 G2 _ L1 L2 _; nd_post). rewrite G1, G2, L1, L2. cbn -[batches_bytes Z.add].
      rewrite batches_bytes_app, batches_bytes_cons, batches_bytes_nil. cbn [b_size].
      split; [lia|]. split; [reflexivity|]. split; [reflexivity|].
      rewrite <- app_assoc. apply Forall_app in N3. destruct N3 as [F1 F2].
      apply Forall_app. split; [exact F1|]. constructor; [cbn; unfold Q_BATCH_BYTES; lia| exact F2]. }
  split; [| exact S2]. (nd_pre S2 4%nat; intros B1 B2 B3 B4; nd_post).
  unfold st_after, qnum. destruct (Z.ltb_spec Q_CACHE (a_qloc_bytes st2)) as [LT|GE]; cbn -[batches_bytes Z.add].
  - specialize (NOREC LT). rewrite B2, B3 in *. rewrite ?batches_bytes_app, ?batches_bytes_nil, ?app_nil_r, ?Z.add_0_r.
    split; [reflexivity|]. split; [lia|]. split; [| unfold Q_CACHE; lia].
    apply Forall_app in B4. destruct B4 as [F1 F2]. apply Forall_app. split; [exact F2| exact F1].
  - rewrite B2, B3 in *. repeat split; try assumption; lia.
Qed.

(* [comment removed for export] *)
Section ChunkQ.
Variables (L : alayout) (st : astate) (X : aconc) (m : amem) (c k n b1 ctx : Z) (l1 l2 : list xbusy).
Hypothesis ALO : alayout_ok L.
Hypothesis WF : awf L st X.
Hypothesis XB : x_busy X = l1 ++ bany BQuar c k n b1 ctx :: l2.
Hypothesis CLS : aslots L st X m c /\ aslot_shadow L st X m c.
Let S := size_of_class c.
Let AB := aslot_addr L c k.
Let UB := AB + rz_size n.

#[using="rc tlsI st X b1 ctx l1 l2 ALO WF XB CLS"] Lemma read_chunk_q :
     junk_at m (UB + 8) (S - rz_size n - 8)
  /\ (16 < rz_size n -> rw_cells asegs m AB [C8 (Z_to_bv 64 AMAGIC); C8 (Z_to_bv 64 (UB - 16))] /\ junk_at m (AB + 16) (rz_size n - 32))
  /\ rw_cells asegs m (shad AB) [CB (Z.to_nat (shlen (rz_size n))) (repeat (Z_to_bv 8 0xfa) (Z.to_nat (shlen (rz_size n))))]
  /\ rw_cells asegs m (shad UB + shlen (rup n 8)) [CB (Z.to_nat (shlen S - shlen (rz_size n) - shlen (rup n 8)))
                                                      (repeat (Z_to_bv 8 0xfa) (Z.to_nat (shlen S - shlen (rz_size n) - shlen (rup n 8))))].
Proof.
  destruct (any_range L st X BQuar c k n b1 ctx l1 l2 XB WF) as [HC KR]. destruct CLS as [[SL _] [SH _]].
  (pose proof (any_facts L st X BQuar c k n b1 ctx l1 l2 XB WF ltac:(discriminate)) as ndP__; nd_pre ndP__ 5%nat; intros N0 FIT0 B10 AT0 CTX0; nd_post).
  specialize (SL k KR). specialize (SH k KR). rewrite (busy_of_X_self_g L st X BQuar c k n b1 ctx l1 l2 XB WF) in SL, SH.
  unfold aslot_busy in SL. cbn [xb_st xb_class xb_n xb_b1 xb_ctx bany bstate_byte xb_alloc xb_slot] in SL.
  (nd_pre SL 3%nat; intros LH [stb [E HDR]] UJ; nd_post). injection E as <-.
  (pose proof (chunk_geo L st X c k n ALO WF HC KR (proj1 N0) FIT0) as ndP__; nd_pre ndP__ 14%nat; intros _ _ _ _ _ _ _ _ _ _ _ _ _ S8; nd_post).
  destruct (junk_split m _ 8 (S - rz_size n - 8) ltac:(replace (8 + (S - rz_size n - 8)) with (S - rz_size n) by lia; exact UJ) ltac:(lia) ltac:(subst S; lia)) as [U8 UR].
  subst S AB UB. replace (aslot_addr L c k + rz_size n - 16) with (aslot_addr L c k + rz_size n + -16) by lia.
  split; [exact UR|]. split; [exact LH|].
  (pose proof (chunk_shadow_geo L st X c k n ALO WF HC KR (proj1 N0) FIT0) as ndP__; nd_pre ndP__ 6%nat; intros SE G2 GE G0 GF _; nd_post).
  cbn [slot_shadow_bytes xb_n xb_st bany] in SH.
  pose proof (rz_size_facts n (proj1 N0)) as [RZ1 _].
  pose proof (shlen_nonneg (rz_size n) ltac:(lia)) as SRZ. pose proof (shlen_nonneg (n + 7) ltac:(lia)) as SG7.
  assert (LB : length (repeat (Z_to_bv 8 253) (Z.to_nat (granules n))) = Z.to_nat (granules n)) by (apply repeat_length).
  replace (Z.to_nat (shlen (size_of_class c))) with
    (Z.to_nat (shlen (rz_size n)) + Z.to_nat (granules n) + Z.to_nat (shlen (size_of_class c) - shlen (rz_size n) - granules n))%nat in SH
    by (generalize SRZ SG7 GF; clear; unfold granules; intros; lia).
  (nd_pre (cb_split3_gen m _ _ _ _ _ _ _ ltac:(apply repeat_length) LB ltac:(apply repeat_length) SH) 3%nat; intros SHA SHU SHR; nd_post).
  rewrite Z2Nat.id in SHU by lia. rewrite Z2Nat.id in SHR by lia. rewrite Z2Nat.id in SHR by (generalize SG7; clear; unfold granules; intros; lia).
  rewrite <- SE in SHU, SHR. rewrite <- GE in SHU, SHR.
  split; [exact SHA| exact SHR].
Qed.
End ChunkQ.

(* [comment removed for export] *)
#[using="Type"] Lemma qcoupled_new_pend : forall L st X Q c k n b1 ctx l1 l2 s' k24 cnt sz ia pend,
  x_busy X = l1 ++ bany BQuar c k n b1 ctx :: l2 -> awf L st X -> qcoupled L st X Q ->
  q_pend Q = (c, k) :: pend ->
  c_count (get_cls st K_BATCH_CLASS) = cnt -> 0 < cnt ->
  nth_error (xc_cache (x_cls X K_BATCH_CLASS)) (Z.to_nat (cnt - 1)) = Some k24 ->
  0 <= k24 < ndist st K_BATCH_CLASS -> ~ In k24 (map qb_slot (q_loc Q ++ q_glob Q)) ->
  a_qloc s' = a_qloc st ++ [mkABatch 1 sz [CPrim c n]] -> a_qglob s' = a_qglob st ->
  qcoupled L s' (xbatch X k24) (mkQConc (q_loc Q ++ [mkQB k24 [k]]) (q_glob Q) ia pend).
Proof.
  intros L st X Q c k n b1 ctx l1 l2 s' k24 cnt sz ia pend XB WF CP PEND CNT POS NK KK NIB QL' QG'.
  pose proof CP as CP0. (nd_pre CP0 8%nat; intros LN1 LN2 OK ND1 ND2 BS PS NN; nd_post).
  unfold qcoupled. cbn [q_loc q_glob q_pend]. rewrite QL', QG'.
  rewrite PEND in ND1, PS.
  set (es := qentries (a_qloc st) (q_loc Q) ++ qentries (a_qglob st) (q_glob Q)) in *.
  assert (ESE : qentries (a_qloc st ++ [mkABatch 1 sz [CPrim c n]]) (q_loc Q ++ [mkQB k24 [k]]) ++ qentries (a_qglob st) (q_glob Q)
                = (qentries (a_qloc st) (q_loc Q) ++ [(CPrim c n, k)]) ++ qentries (a_qglob st) (q_glob Q)).
  { rewrite qentries_app by exact LN1. cbn [qentries combine b_chunks qb_ks app]. rewrite ?app_nil_r. reflexivity. }
  rewrite ESE.
  assert (PE : Permutation ((qentries (a_qloc st) (q_loc Q) ++ [(CPrim c n, k)]) ++ qentries (a_qglob st) (q_glob Q)) ((CPrim c n, k) :: es)).
  { subst es. rewrite <- app_assoc. cbn [app]. apply Permutation_sym. apply Permutation_middle. }
  assert (PI : Permutation (qprim_ids ((qentries (a_qloc st) (q_loc Q) ++ [(CPrim c n, k)]) ++ qentries (a_qglob st) (q_glob Q)) ++ pend)
                           (qprim_ids es ++ (c, k) :: pend)).
  { eapply Permutation_trans; [apply Permutation_app_tail; apply qprim_ids_perm; exact PE|]. cbn [qprim_ids flat_map fst snd app]. apply Permutation_middle. }
  assert (PB : Permutation (map qb_slot ((q_loc Q ++ [mkQB k24 [k]]) ++ q_glob Q)) (k24 :: map qb_slot (q_loc Q ++ q_glob Q))).
  { rewrite !map_app. cbn [map qb_slot]. rewrite <- app_assoc. cbn [app]. apply Permutation_sym. apply Permutation_middle. }
  split; [rewrite !length_app; cbn; lia|]. split; [exact LN2|]. split.
  { eapply Permutation_Forall; [apply Permutation_sym; exact PE|]. constructor.
    - unfold qentry_ok. cbn [fst snd]. exists b1, ctx. unfold xbatch. cbn [x_busy]. right. rewrite XB. apply in_or_app. right. left. reflexivity.
    - eapply Forall_impl; [| exact OK]. intros [ch k'] HOK. unfold qentry_ok in *. cbn [fst snd] in *.
      destruct ch as [c' n'| mb ms n']; [| exact I]. (nd_pre HOK 3%nat; intros b1' ctx' Hin; nd_post). exists b1', ctx'. unfold xbatch. cbn [x_busy]. right. exact Hin. }
  split; [eapply Permutation_NoDup'; [apply Permutation_sym; exact PI| exact ND1]|].
  split.
  { eapply Permutation_NoDup'; [apply Permutation_sym; exact PB|]. constructor; [exact NIB| exact ND2]. }
  split.
  { intros k0. split.
    - intros H. apply (Permutation_in _ PB) in H. destruct H as [<-|H].
      + exists (bbatch k24). unfold xbatch, bbatch. cbn. split; [left; reflexivity|]. auto.
      + apply (BS k0) in H. (nd_pre H 5%nat; intros y Hy Sy Cy Ky; nd_post). exists y. unfold xbatch. cbn [x_busy In]. split; [right; exact Hy|]. auto.
    - intros (y & Hy & Sy & Cy & Ky). eapply Permutation_in; [apply Permutation_sym; exact PB|].
      unfold xbatch in Hy. cbn [x_busy In] in Hy. destruct Hy as [<-|Hy].
      + left. cbn in Ky. exact Ky.
      + right. apply (BS k0). exists y. auto. }
  split.
  { intros c0 k0. rewrite (Permutation_in' eq_refl PI). rewrite (PS c0 k0). unfold xbatch. cbn [x_busy In].
    split; intros (y & Hy & Sy & Cy & Ky); exists y.
    - split; [right; exact Hy|]. auto.
    - destruct Hy as [<-|Hy]; [cbn in Sy; discriminate|]. auto. }
  eapply Permutation_Forall; [apply Permutation_sym; exact PB|]. constructor; [lia| exact NN].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section S.
Variable DI : ADepotIface.
Variables (ASEC : alayout -> astate -> aconc -> amem -> Prop) (AFK : alayout -> list ablock -> amem -> Prop).
Hypothesis HL : ahole_laws (AHQ DI ASEC AFK).
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI
                                  /\ (snd iv <= 0xab670 \/ 0xab730 <= fst iv)
                                  /\ (snd iv <= 0xafc00 \/ 0x130c30 <= fst iv)
                                  /\ (snd iv <= 0x13e488 \/ 0x13e48c <= fst iv)) CI.

Definition store_freeR__stmt : Prop := store_freeR_stmt DI ASEC AFK CI.
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'store_freeR__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'store_freeR__stmt 1).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'store_freeR__stmt 2).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'store_freeR__stmt 3).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'store_freeR__stmt 4).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'store_freeR__stmt 5).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'store_freeR__stmt 6).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'store_freeR__stmt 7).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'store_freeR__stmt 8).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'store_freeR__stmt 9).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'store_freeR__stmt 10).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'store_freeR__stmt 11).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'store_freeR__stmt 12).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'store_freeR__stmt 13).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'store_freeR__stmt 14).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'store_freeR__stmt 15).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'store_freeR__stmt 16).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'store_freeR__stmt 17).
Variable F : ltac2:(SecDietF.SzSecF.ty 'store_freeR__stmt 18).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'store_freeR__stmt 19).
Variable m : ltac2:(SecDietF.SzSecF.ty 'store_freeR__stmt 20).
Variable st : ltac2:(SecDietF.SzSecF.ty 'store_freeR__stmt 21).
Variable LB : ltac2:(SecDietF.SzSecF.ty 'store_freeR__stmt 22).
Variable X : ltac2:(SecDietF.SzSecF.ty 'store_freeR__stmt 23).
Variable Q : ltac2:(SecDietF.SzSecF.ty 'store_freeR__stmt 24).
Variable c : ltac2:(SecDietF.SzSecF.ty 'store_freeR__stmt 25).
Variable k : ltac2:(SecDietF.SzSecF.ty 'store_freeR__stmt 26).
Variable n : ltac2:(SecDietF.SzSecF.ty 'store_freeR__stmt 27).
Variable b1 : ltac2:(SecDietF.SzSecF.ty 'store_freeR__stmt 28).
Variable ctx : ltac2:(SecDietF.SzSecF.ty 'store_freeR__stmt 29).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'store_freeR__stmt 30).
Variable k24 : ltac2:(SecDietF.SzSecF.ty 'store_freeR__stmt 31).
Variable l1 : ltac2:(SecDietF.SzSecF.ty 'store_freeR__stmt 32).
Variable l2 : ltac2:(SecDietF.SzSecF.ty 'store_freeR__stmt 33).
Variable stj : ltac2:(SecDietF.SzSecF.ty 'store_freeR__stmt 34).
Variable chunks : ltac2:(SecDietF.SzSecF.ty 'store_freeR__stmt 35).
Let st2 := st_enq st (CPrim c n).
Let ek := ek_of L st X Q n k24 stj chunks.
Let g := g_of L st Q (ek_delta ek n).
Let S := size_of_class c.
Let AB := aslot_addr L c k.
Let UB := AB + rz_size n.
Let lst := qlast L (q_loc Q).
Let eb := ek_b ek lst.
Let gl := dk_glst g lst.
Let gq := shlen (rup n 8).
Let st' := st_after st2.
#[using="HL CI_OK st2 ek g S AB UB lst eb gl gq st'"] Lemma store_freeR__body : ltac:(let T := type of (fun (h : store_freeR__stmt) => h L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st LB X Q c k n b1 ctx lo k24 l1 l2 stj chunks) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (ra, (sp, (gp, (tp, (s0, (s1, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (F, (fc, (m, (st, (LB, (X, (Q, (c, (k, (n, (b1, (ctx, (lo, (k24, (l1, (l2, (stj, chunks)))))))))))))))))))))))))))))))))))) as _.
  unfold store_freeR_stmt. 
  cbv zeta. intros ALO ARNG AR BL HFK XB N1 [pend PEND] EA NK0 NB0 KK0 NIB0 JK0 FSH0 CIN0 POS0 NOREC EK DK CEIL LO ms' PM. unfold AFREE_STACK in LO.
  assert (NEWF : enq_is_app st = false ->
        nth_error (xc_cache (x_cls X K_BATCH_CLASS)) (Z.to_nat (c_count (get_cls st K_BATCH_CLASS) - 1)) = Some k24
     /\ busy_of X K_BATCH_CLASS k24 = None /\ 0 <= k24 < ndist st K_BATCH_CLASS
     /\ ~ In k24 (map qb_slot (q_loc Q ++ q_glob Q))
     /\ junk_at m (abatch_addr L k24) 8192 /\ fill_at m (shad (abatch_addr L k24)) (shlen 8192) 0xfa
     /\ a_cinit st = true /\ 0 < c_count (get_cls st K_BATCH_CLASS)) by (intros _; repeat (split; [assumption|]); exact POS0).
  clear NK0 NB0 KK0 NIB0 JK0 FSH0 CIN0 POS0.
  chg (st_enq st (CPrim c n)) st2.
  chg (ek_of L st X Q n k24 stj chunks) ek.
  chg (g_of L st Q (ek_delta ek n)) g.
  (* [comment removed for export] *)
  pose proof AR as AR0. (nd_pre AR0 12%nat; intros WF RT INST THR CLS HQ HS HD HRO HRT2 AVL RT3; nd_post).
  cbn [ah_quar ah_sec ah_depot AHQm] in HQ, HS, HD. rename HQ into AQ.
  (nd_pre THR 6%nat; intros T0 T40 CACHES CSTATS STATS0 UNW; nd_post).
  destruct (any_range L st X BQuar c k n b1 ctx l1 l2 XB WF) as [HC KR].
  (pose proof (any_facts L st X BQuar c k n b1 ctx l1 l2 XB WF ltac:(discriminate)) as ndP__; nd_pre ndP__ 5%nat; intros N0 FIT0 B10 AT0 CTX0; nd_post).
  (pose proof (chunk_geo L st X c k n ALO WF HC KR (proj1 N0) FIT0) as ndP__; nd_pre ndP__ 14%nat; intros HM16 UB16 ABUB ABHM HLO UBS ABCE HHI N65 NQM ABLO RUP RUP8 S8; nd_post).
  (pose proof (slot_geo L st X c k ALO WF HC KR) as ndP__; nd_pre ndP__ 13%nat; intros S16 SM16 AL16 G1 G2 G3 G4 G5 G6 G7 G8 R8 M8; nd_post).
  (pose proof (slot_sep_objects L st X c k ALO WF HC KR) as ndP__; nd_pre ndP__ 5%nat; intros DT DC DN DSO DF; nd_post).
  (pose proof (chunk_shadow_geo L st X c k n ALO WF HC KR (proj1 N0) FIT0) as ndP__; nd_pre ndP__ 9%nat; intros SE GR3 GE G0 GFS SHLO SHHI SHM1 SHM2; nd_post).
  pose proof (rz_size_facts n (proj1 N0)) as [RZ1 RZ2].
  (pose proof (alayout_t L ALO) as ndP__; nd_pre ndP__ 4%nat; intros TL1 TL2 TL3 TL4; nd_post).
  (pose proof (alayout_ctx L ALO) as ndP__; nd_pre ndP__ 5%nat; intros CL1 CL2 CL3 CL4 CL5; nd_post).
  (pose proof (alayout_depot L ALO) as ndP__; nd_pre ndP__ 10%nat; intros DL1 DL2 DL3 DL4 DL5 DL6 DL7 DL8 DL9 DL10; nd_post).
  (pose proof (alayout_stack L ALO) as ndP__; nd_pre ndP__ 3%nat; intros STK1 STK2 STK3; nd_post).
  (pose proof (alayout_space L ALO) as ndP__; nd_pre ndP__ 4%nat; intros SP1 SP2 SP3 SP4; nd_post).
  pose proof (ao_res L ALO) as RES. pose proof (ao_t L ALO) as OT. pose proof (ao_ctx L ALO) as OC. pose proof (ao_nodes L ALO) as ON. pose proof (ao_store L ALO) as OS.
  (pose proof (aobj4_int _ OT) as ndP__; nd_pre ndP__ 4%nat; intros _ _ [kT TBND] [jT TIMG]; nd_post).   (* [comment removed for export] *)
  (pose proof (aobj_int _ _ OC ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros Ci _ [kC CBND]; nd_post). (pose proof (aobj_int _ _ ON ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros Ni _ [kN NBND]; nd_post).
  (pose proof (aobj_int _ _ OS ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros Si _ [kS SBND]; nd_post). pose proof (ao_res_hi L ALO) as RHI.
  unfold aobj in RES, OT, OC, ON, OS. pose proof (ao_space L ALO) as RSP.
  pose proof (ad_t_res L ALO) as D_t_res. pose proof (ad_nodes_res L ALO) as D_n_res. pose proof (ad_store_res L ALO) as D_s_res.
  pose proof (ad_ctx_res L ALO) as D_c_res. pose proof (ad_ctx_nodes L ALO) as D_c_n. pose proof (ad_ctx_store L ALO) as D_c_s.
  unfold adisj in D_t_res, D_n_res, D_s_res, D_c_res, D_c_n, D_c_s.
  assert (D_c_t : al_ctx L + 65536 <= al_t L \/ al_t L + 4096 <= al_ctx L) by (pose proof (ad_t_ctx L ALO) as X1; unfold adisj in X1; clear -X1; lia).
  box DL7. box DL8. box DL9. box DL10. box D_t_res. box D_n_res. box D_s_res. box D_c_res. box D_c_n. box D_c_s. box D_c_t. box CL5.
  box DT. box DC. box DN. box DSO. box DF.
  word_range sp SPR.
  chg (size_of_class c) S. chg (aslot_addr L c k) AB. chg (AB + rz_size n) UB.
  assert (EAB : AB = aslot_addr L c k) by reflexivity. assert (EUB : UB = AB + rz_size n) by reflexivity. assert (ES : S = size_of_class c) by reflexivity.
  assert (EHM : fhm L c k n = UB - 16) by (unfold fhm; subst AB UB; clear; lia).
  assert (UB16' : UB mod 8 = 0) by (clear -UB16; Z.div_mod_to_equations; lia).
  rewrite EHM in PM.
  (* [comment removed for export] *)
  (nd_pre (read_chunk_q L st X m c k n b1 ctx l1 l2 ALO WF XB (conj (proj1 (proj2 (proj2 (CLS c HC)))) (proj2 (proj2 (proj2 (CLS c HC)))))) 4%nat; intros UJR LH SHA SHR; nd_post).
  fold AB in UJR, LH, SHA, SHR. fold UB in UJR, LH, SHR. fold S in UJR, SHR.
  (* [comment removed for export] *)
  pose proof AQ as AQ0. (nd_pre AQ0 6%nat; intros [QK MX] [QC ABL] [GCQ ABG] (FL & IAS & IAM) CP NUM; nd_post).
  pose proof NUM as NUM0. (nd_pre NUM0 5%nat; intros NB1 NB2 NF NC NM; nd_post).
  pose proof CP as CP0. (nd_pre CP0 7%nat; intros LN1 LN2 _ _ ND2 BSI _; nd_post).
  (* [comment removed for export] *)
  assert (CNT : enq_app st (CPrim c n) = None -> 0 < c_count (get_cls st K_BATCH_CLASS)) by (intros _; exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (NEWF EA))))))))).
  assert (EAPP0 : enq_app st (CPrim c n) = None).
  { destruct (enq_app st (CPrim c n)) as [sx|] eqn:EAPP; [exfalso| reflexivity].
    assert (EA1 : enq_is_app st = true) by (apply (proj2 (enq_is_app_spec st (CPrim c n))); eexists; exact EAPP). congruence. }
  assert (SB : a_qloc_bytes st2 = a_qloc_bytes st + ek_delta ek n /\ a_qglob_bytes st2 = a_qglob_bytes st /\ a_qglob st2 = a_qglob st).
  { subst st2 ek. unfold st_enq, ek_of. rewrite EAPP0, EA. cbn [ek_delta]. (pose proof (enq_new_core (CPrim c n) st) as ndP__; nd_pre ndP__ 7%nat; intros _ G1' G2' _ _ L2' _; nd_post).
    rewrite G1', G2', L2'. cbn [chunk_size]. unfold Q_BATCH_BYTES. repeat split; try reflexivity. clear; lia. }
  (nd_pre SB 3%nat; intros SB1 SB2 SB3; nd_post).
  assert (ED0 : 0 <= ek_delta ek n /\ ek_delta ek n <= n + 8192) by (subst ek; unfold ek_of; rewrite EA; cbn [ek_delta]; lia).
  assert (EBK : ek_b ek (qlast L (q_loc Q)) = qlast L (q_loc Q) \/ (enq_is_app st = false /\ ek_b ek (qlast L (q_loc Q)) = abatch_addr L k24)).
  { subst ek. unfold ek_of. rewrite EA; cbn [ek_b]. right; split; reflexivity. }
  assert (EBB : ek_b ek (qlast L (q_loc Q)) = qlast L (q_loc Q)
      \/ exists kk, ek_b ek (qlast L (q_loc Q)) = abatch_addr L kk /\ 0 <= kk < ndist st K_BATCH_CLASS /\ ~ In kk (map qb_slot (q_loc Q ++ q_glob Q))).
  { destruct EBK as [E|[EA2 E]]; [left; exact E| right; exists k24]. (nd_pre (NEWF EA2) 5%nat; intros NK NB KK NIB _; nd_post). split; [exact E|]. split; [exact KK| exact NIB]. }
  (nd_pre (read_dk (AHQm DI ASEC AFK Q) L st X Q m RNG BQuar c k n b1 ctx l1 l2 ALO ARNG AR AQ XB ltac:(discriminate) (ek_b ek (qlast L (q_loc Q))) (ek_delta ek n) ek
              (proj1 ED0) EBB ltac:(rewrite <- SB1, <- SB2; exact NOREC) eq_refl) 4%nat; intros _ _ GL GLST; nd_post).
  fold g in GL, GLST.
  chg (qlast L (q_loc Q)) lst. chg (ek_b ek lst) eb. chg (dk_glst g lst) gl. chg (shlen (rup n 8)) gq.
  (* [comment removed for export] *)
  assert (BGEO : forall q, In q (q_loc Q ++ q_glob Q) ->
      aregion L K_BATCH_CLASS <= abatch_addr L (qb_slot q) /\ abatch_addr L (qb_slot q) + 8192 <= aregion L K_BATCH_CLASS + c_allocated_user (get_cls st K_BATCH_CLASS)
      /\ al_res L + 4096 <= abatch_addr L (qb_slot q) /\ abatch_addr L (qb_slot q) + 8192 <= al_res L + 137439023104).
  { intros q Hq. (pose proof (slot_geo L st X K_BATCH_CLASS (qb_slot q) ALO WF (K24) (bslot_range L st X Q WF CP q Hq)) as ndP__; nd_pre ndP__ 10%nat; intros _ _ _ Q1 Q2 Q3 Q4 Q5 Q6 _; nd_post).
    rewrite size_of_class_24 in Q2, Q6. unfold abatch_addr. unfold K_SPACE_SIZE in Q6. change (2^37) with 137438953472 in Q6.
    generalize Q1 Q2 Q5 Q6 RSP; clear; intros. lia. }
  assert (A24 : c_allocated_user (get_cls st K_BATCH_CLASS) <= K_FREEARR_OFF).
  { destruct WF as (_ & _ & _ & _ & _ & PERC & _). (nd_pre (PERC K_BATCH_CLASS (K24)) 3%nat; intros Q1 Q2 _; nd_post). lia. }
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
  { subst eb. destruct EBK as [E|[EA2 E]].
    - rewrite E. destruct LSTF as [Z0|(_ & FF)]; [left; exact Z0| right; exact FF].
    - right. rewrite E. (nd_pre (NEWF EA2) 4%nat; intros _ _ KK _; nd_post). (pose proof (slot_geo L st X K_BATCH_CLASS k24 ALO WF (K24) KK) as ndP__; nd_pre ndP__ 10%nat; intros _ _ _ Q1 Q2 Q3 Q4 Q5 Q6 _; nd_post).
      rewrite size_of_class_24 in Q2, Q6. unfold abatch_addr. unfold K_SPACE_SIZE in Q6. change (2^37) with 137438953472 in Q6.
      generalize Q1 Q2 Q5 Q6 RSP; clear; intros. lia. }
  (* [comment removed for export] *)
  (nd_pre PM 19%nat; intros id t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' sj' ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 18%nat; intros MU WM MI' ST' IDR HDR' FC' SH' QC' EKP DKP STATS' LSJ' UW' FL' IAS' IAM' DEP'; nd_post).
  fold lst in MU, QC', EKP, DKP, EBK. fold eb in MU, EBK. fold gl in MU. fold gq in MU, SH'.
  replace (UB - 16 + 16) with UB in MU, FC', SH' by (clear; lia).
  assert (ELST : lst = qlast L (q_loc Q)) by reflexivity. assert (EEB : eb = ek_b ek lst) by reflexivity.
  assert (EGL : gl = dk_glst g lst) by reflexivity. assert (EGQ : gq = shlen (rup n 8)) by reflexivity.
  clearbody lst eb gl gq.
  (* [comment removed for export] *)
  assert (MUn : munch (Wf (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) m m').
  { eapply munch_weaken; [| exact MU]. solve_sub_fp sp. }
  clear MU.
  assert (EBNZ : 0x10007fff8000 <= eb) by (rewrite EEB; exact (ek_pre_b_hi _ _ _ _ _ _ _ _ EK)).   (* [comment removed for export] *)
  assert (KF : kfactsF (bv_unsigned sp) (al_t L) AB S UB gq (al_nodes L) (al_store L) (al_res L) (al_ctx L) lo (shlen (rz_size n)) (shlen S) lst eb gl).
  { unfold kfactsF. unfold K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
    assert (GQ1 : 1 <= gq) by (rewrite EGQ, shlen_div; generalize RUP RUP8 N1; clear; intros; Z.div_mod_to_equations; lia).
    generalize CEIL LO OT OC ON OS RES RHI RSP G5 G6 ABUB UBS S8 RUP EUB SHLO SE GR3 GQ1 GFS GE SHHI LSTF EBF GLF EBNZ. clear. intros.
    unfold iclr, AIMG_LO, AIMG_HI in *.   (* [comment removed for export] *)
    (destruct LSTF as [Z0|(_ & FF)]; [rewrite (qsz_eq0 lst Z0) | rewrite (qsz_pos lst) by (atop_facts; lia)]);
    (destruct EBF as [Z1|FF1]; [exfalso; atop_facts; lia|]); destruct GLF as [[_ Z2]|(_ & _ & [Z2|(_ & FF2)])];
    sg_destr; repeat split; first [assumption | lia]. }
  pose proof (KF_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Kimg.
  pose proof (KF_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Klow.
  pose proof (KF_hi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Khi.
  pose proof (KF_shad _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Kshad.
  pose proof (KF_ctx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF (unbxF D_c_t) (unbxF D_c_res) (unbxF D_c_n) (unbxF D_c_s)) as Kctx.
  pose proof (KF_t _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF (unbxF D_t_res) (unbxF DL7) (unbxF DL8)) as Kt.
  pose proof (KF_res _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF (unbxF D_t_res) (unbxF D_n_res) (unbxF D_s_res)) as Kres.
  pose proof (KF_obj _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Kobj.
  pose proof (KF_objL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as KobjL.      (* [comment removed for export] *)
  pose proof (ad_tls_t L ALO) as D_l_t. pose proof (ad_tls_res L ALO) as D_l_r. pose proof (ad_tls_nodes L ALO) as D_l_n. pose proof (ad_tls_store L ALO) as D_l_s.
  unfold adisj in D_l_t, D_l_r, D_l_n, D_l_s. pose proof atp_lin as TLN. pose proof atop_range as ATR0.
  (* [comment removed for export] *)
  assert (SC : same_core st (st_after st2) /\ a_cinit (st_after st2) = a_cinit st /\ a_live (st_after st2) = a_live st /\ a_next (st_after st2) = a_next st
               /\ a_space_beg (st_after st2) = a_space_beg st /\ a_ptr_array (st_after st2) = a_ptr_array st
               /\ (enq_is_app st = true -> a_cls (st_after st2) = a_cls st)
               /\ (enq_is_app st = false -> a_cls (st_after st2) = <[ K_BATCH_CLASS := cls_set_count (c_count (get_cls st K_BATCH_CLASS) - 1) (get_cls st K_BATCH_CLASS) ]> (a_cls st))).
  { pose proof (st_after_core st2) as [SC2 CL2'].
    assert (SC1 : same_core st st2 /\ (enq_is_app st = true -> a_cls st2 = a_cls st) /\ (enq_is_app st = false -> a_cls st2 = <[ K_BATCH_CLASS := cls_set_count (c_count (get_cls st K_BATCH_CLASS) - 1) (get_cls st K_BATCH_CLASS) ]> (a_cls st))).
    { subst st2. unfold st_enq. rewrite EAPP0.
      (pose proof (enq_new_core (CPrim c n) st) as ndP__; nd_pre ndP__ 7%nat; intros C1 _ _ _ _ _ C7; nd_post). split; [exact C1|].
      split; [| intros _; exact C7]. intros EA'. exfalso. congruence. }
    (nd_pre SC1 3%nat; intros SC1 CLa CLb; nd_post). pose proof (same_core_trans _ _ _ SC1 SC2) as SC3.
    pose proof SC3 as SC0. (nd_pre SC0 8%nat; intros F1 F2 F3 F4 F5 F6 F7 _; nd_post).
    split; [exact SC3|]. split; [exact F3|]. split; [exact F1|]. split; [exact F2|]. split; [exact F4|]. split; [exact F5|].
    split; [intros EA2; rewrite CL2'; exact (CLa EA2)| intros EA2; rewrite CL2'; exact (CLb EA2)]. }
  (nd_pre SC 8%nat; intros SC ECIN ELIVE ENEXT ESB EPA CLa CLb; nd_post).
  pose proof SC as SC0. (nd_pre SC0 12%nat; intros _ _ _ _ _ ENRES ENSEC GCo M24a M24b M24c M24d; nd_post).
  chg (st_after st2) st'.
  set (X' := xbatch X k24).
  assert (GC24 : get_cls st' K_BATCH_CLASS = (if enq_is_app st then get_cls st K_BATCH_CLASS else cls_set_count (c_count (get_cls st K_BATCH_CLASS) - 1) (get_cls st K_BATCH_CLASS))).
  { unfold get_cls at 1. rewrite EA. rewrite (CLb EA), lookup_insert_eq; reflexivity. }
  assert (GCo' : forall c', c' <> K_BATCH_CLASS -> get_cls st' c' = get_cls st c') by (intros c' NE; rewrite (GCo c' NE); reflexivity).
  assert (NDS : forall c', ndist st' c' = ndist st c').
  { intros c'. unfold ndist. destruct (Z.eq_dec c' K_BATCH_CLASS) as [->|NE]; [rewrite M24b; reflexivity| rewrite (GCo' c' NE); reflexivity]. }
  assert (MC' : forall c', max_count st' c' = max_count st c') by (intros c'; unfold max_count; rewrite ECIN; reflexivity).
  (* [comment removed for export] *)
  assert (WF' : awf L st' X').
  { subst X'. (nd_pre (NEWF EA) 8%nat; intros NK NB KK NIB JK FSH CIN POS; nd_post).
    apply (awf_xbatch L st X k24 (c_count (get_cls st K_BATCH_CLASS)) WF eq_refl POS NK).
    + exact ESB. + exact EPA. + exact ECIN. + exact ELIVE. + exact ENEXT.
    + intros c' NE. rewrite (GCo' c' NE). reflexivity.
    + rewrite GC24, EA. reflexivity. }
  (* [comment removed for export] *)
  assert (RT' : arep_rt L m').
  { eapply arep_rt_frame; [exact MUn | exact WM | exact RT |]. unfold rt_hulls, ATP88, ATSD.
    (first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kctx; clear; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kctx; clear; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |])] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]). apply Forall_nil. }
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
      + destruct (CACHES K_BATCH_CLASS Hc') as [tail (CR & CH & LCH)]. unfold acache_cells. cbv zeta.
        rewrite GC24, MC', ECIN, EA. subst X'. rewrite xbatch_cache, Z.eqb_refl.
        replace (acache_addr L K_BATCH_CLASS) with (al_t L + 2128) in CR, CH |- * by (unfold acache_addr, K_BATCH_CLASS; clear; lia).
        subst ek. unfold ek_of in EKP. rewrite EA in EKP; cbn [ek_post negb] in EKP |- *.
        * destruct EKP as (CR' & _). (nd_pre (NEWF EA) 8%nat; intros NK NB KK NIB JK FSH CIN POS; nd_post).
          cbn [c_count cls_set_count]. exists (Z_to_bv 64 (acompact K_BATCH_CLASS k24) :: tail).
          pose proof (cache24_split L st X k24 (c_count (get_cls st K_BATCH_CLASS)) WF eq_refl POS NK) as [CACHE LRL].
          split; [exact CR'|]. split.
          -- eapply u32arr_frame; [| exact MUn | exact WM |].
             ++ rewrite CACHE, map_app in CH. cbn [map] in CH. rewrite <- app_assoc in CH. cbn [app] in CH. exact CH.
             ++ rewrite length_app, length_map. cbn [length].
                replace (length (removelast (xc_cache (x_cls X K_BATCH_CLASS))) + Datatypes.S (length tail))%nat with 16%nat
                  by (rewrite CACHE, length_app in LCH; cbn [length] in LCH; clear -LCH; lia).
                apply Kt; clear; lia.
          -- cbn [length]. rewrite CACHE, length_app in LCH. cbn [length] in LCH. clear -LCH. lia.
      + eapply acache_cells_frame; [exact MUn | exact WM | exact (CACHES c' Hc') | rewrite (GCo' c' NE); reflexivity | exact ECIN | |].
        * subst X'. rewrite xbatch_cache. destruct (Z.eqb_spec c' K_BATCH_CLASS) as [E|_]; [exfalso; exact (NE E)|]. reflexivity.
        * unfold acache_addr. unfold K_NUM_CLASSES, K_BATCH_CLASS in *. apply Kt; clear -Hc' NE; lia.
    - apply (junk_merge m' (al_t L + 2768) 16 16); [| | clear; lia | clear; lia].
      + eapply junk_frame; [exact (proj1 (junk_split m (al_t L + 2768) 16 16 CSTATS ltac:(clear; lia) ltac:(clear; lia))) | exact MUn | exact WM | intros _; apply Kt; clear; lia].
      + apply (junk_merge m' (al_t L + 2768 + 16) 8 8); [| | clear; lia | clear; lia].
        * replace (al_t L + 2768 + 16) with (al_t L + 2784) by (clear; lia).
          assert (STJ' : exists w : word, rw_cells asegs m' (al_t L + 2784) [C8 w]).
          { subst ek. unfold ek_of in EKP. rewrite EA in EKP; cbn [ek_post] in EKP. (nd_pre EKP 3%nat; intros _ STS' _; nd_post). exact STS'. }
          destruct STJ' as [w STS']. pose proof (junk_of_cells m' _ _ STS') as J. cbn in J. exact J.
        * replace (al_t L + 2768 + 16 + 8) with (al_t L + 2792) by (clear; lia).
          eapply junk_frame; [| exact MUn | exact WM | intros _; apply Kt; clear; lia].
          pose proof (junk_split m (al_t L + 2768) 16 16 CSTATS ltac:(clear; lia) ltac:(clear; lia)) as [_ CSb].
          pose proof (junk_split m (al_t L + 2768 + 16) 8 8 CSb ltac:(clear; lia) ltac:(clear; lia)) as [_ CSc].
          replace (al_t L + 2768 + 16 + 8) with (al_t L + 2792) in CSc by (clear; lia). exact CSc.
    - exists sj'. split; [exact STATS' | exact LSJ'].
    - exact UW'. }
  (* [comment removed for export] *)
  assert (SEPQ : forall q, In q (q_loc Q ++ q_glob Q) -> AB + S <= abatch_addr L (qb_slot q) \/ abatch_addr L (qb_slot q) + 8192 <= AB).
  { intros q Hq. (nd_pre (bslot_busy L st X Q CP q Hq) 5%nat; intros yq Hyq Syq Cyq Kyq; nd_post).
    pose proof (slots_sep_any L st X c k K_BATCH_CLASS (qb_slot q) ALO WF HC (K24) KR (bslot_range L st X Q WF CP q Hq)
                  ltac:(rewrite <- Cyq, <- Kyq; apply (other_key (AHQm DI ASEC AFK Q) L st X m BQuar c k n b1 ctx l1 l2 AR XB); [exact Hyq| rewrite Syq; discriminate])) as D.
    rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
  assert (SEPK : enq_is_app st = false -> AB + S <= abatch_addr L k24 \/ abatch_addr L k24 + 8192 <= AB).
  { intros EA2. (nd_pre (NEWF EA2) 4%nat; intros NK NB KK _; nd_post).
    pose proof (slots_sep_any L st X c k K_BATCH_CLASS k24 ALO WF HC (K24) KR KK
                  ltac:(destruct (Z.eq_dec c K_BATCH_CLASS) as [->|NE]; [right| left; exact NE]; intros ->;
                        pose proof (busy_of_X_self_g L st X BQuar K_BATCH_CLASS k24 n b1 ctx l1 l2 XB WF) as E'; rewrite NB in E'; discriminate)) as D.
    rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
  assert (SEPL : lst = 0 \/ (AB + S <= lst \/ lst + 8192 <= AB)).
  { destruct LSTF as [Z0|((q & Hq & Eq) & _)]; [left; exact Z0| right; rewrite Eq; apply SEPQ; apply in_or_app; left; exact Hq]. }
  assert (SEPE : eb = 0 \/ (AB + S <= eb \/ eb + 8192 <= AB)).
  { subst eb. destruct EBK as [E|[EA2 E]]; rewrite E; [exact SEPL| right; exact (SEPK EA2)]. }
  assert (SEPG : gl = 0 \/ (AB + S <= gl \/ gl + 8192 <= AB)).
  { destruct GLF as [[_ ->]|(_ & _ & [Z0|((q & Hq & Eq) & _)])]; [exact SEPL| left; exact Z0| right; rewrite Eq; apply SEPQ; apply in_or_app; right; exact Hq]. }
  (* [comment removed for export] *)
  assert (BDIS : forall q1 q2, In q1 (q_loc Q ++ q_glob Q) -> In q2 (q_loc Q ++ q_glob Q) ->
      abatch_addr L (qb_slot q1) = abatch_addr L (qb_slot q2) \/ abatch_addr L (qb_slot q1) + 8192 <= abatch_addr L (qb_slot q2) \/ abatch_addr L (qb_slot q2) + 8192 <= abatch_addr L (qb_slot q1)).
  { intros q1 q2 H1 H2. destruct (Z.eq_dec (qb_slot q1) (qb_slot q2)) as [E|NE]; [left; rewrite E; reflexivity| right].
    pose proof (slots_disjoint L K_BATCH_CLASS (qb_slot q1) (qb_slot q2) ltac:(pose proof (bslot_range L st X Q WF CP q1 H1); lia)
                  ltac:(pose proof (bslot_range L st X Q WF CP q2 H2); lia) NE ltac:(rewrite size_of_class_24; lia)) as D.
    rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
  assert (KDIS : forall q, In q (q_loc Q ++ q_glob Q) -> enq_is_app st = false ->
      abatch_addr L k24 + 8192 <= abatch_addr L (qb_slot q) \/ abatch_addr L (qb_slot q) + 8192 <= abatch_addr L k24).
  { intros q Hq EA2. (nd_pre (NEWF EA2) 5%nat; intros NK NB KK NIB _; nd_post).
    assert (NE : k24 <> qb_slot q) by (intros ->; apply NIB; apply in_map; exact Hq).
    pose proof (slots_disjoint L K_BATCH_CLASS k24 (qb_slot q) ltac:(lia) ltac:(pose proof (bslot_range L st X Q WF CP q Hq); lia) NE ltac:(rewrite size_of_class_24; lia)) as D.
    rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
  (* [comment removed for export] *)
  assert (RC : forall c1 c2, c1 < c2 -> aregion L c1 + K_REGION <= aregion L c2) by (intros; apply regions_sep; assumption).
  assert (CLS' : forall c'', 1 <= c'' < K_NUM_CLASSES ->
      aregion_cells L st' m' c'' /\ afreearray L st' X' m' c'' /\ aslots L st' X' m' c'' /\ aslot_shadow L st' X' m' c'').
  { intros c'' Hc''. (nd_pre (CLS c'' Hc'') 4%nat; intros REG FARR SLOTS SHADOW; nd_post).
    pose proof WF as WF0. (nd_pre WF0 7%nat; intros _ _ SAL _ _ PERC _; nd_post).
    (nd_pre (PERC c'' Hc'') 12%nat; intros Q1 Q2 Q3 Q4 Q5 Q6 Q7 QLENF QLENC QCNTB QND QRANGE; nd_post).
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
    (nd_pre RI 4%nat; intros RI1 RI2 RI3 RI4; nd_post).
    (* [comment removed for export] *)
    assert (PC0 : aregion L c <= AB /\ AB + S <= aregion L c + K_FREEARR_OFF /\ AB + S <= aregion L c + c_allocated_user (get_cls st c)) by (clear -G1 G2 G3 G4; lia).
    split; [| split; [| split]].
    - eapply aregion_cells_frame; [exact MUn | exact WM | exact REG | exact EC1 | exact EC2 | exact EC3 | exact EC4 |].
      unfold aregion_info, ARI_STRIDE, K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
      apply Kres; try (clear -Hc'' RSP G6 S8 EUB; lia).
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
      + subst X'. apply xbatch_free.
      + assert (FA1 : aregion L c'' + K_FREEARR_OFF <= afreearr L c'' /\ afreearr L c'' + c_mapped_free_array (get_cls st c'') <= aregion L c'' + K_REGION).
        { unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q6. lia. }
        destruct FA1 as [FA1 FA2].
        apply Kres; [clear -RI1 FA1; unfold K_FREEARR_OFF in *; lia | clear -RI2 RI3 FA2; lia | clear -Q5 Q6; lia | | | |].
        * pose proof (farr_vs_user L c'' c _ _ AB S (proj1 PC0) (proj1 (proj2 PC0)) FA1 FA2) as D. clear -D ABUB S8 EUB. lia.
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
        * rewrite shad_div. unfold ASHOFF, K_FREEARR_OFF in *. clear -RI1 FA1 RES RHI. Z.div_mod_to_equations. lia.
        * rewrite shad_div, shlen_div. unfold ASHOFF, K_SPACE_SIZE in *. clear -RI2 RI3 FA2 RES RHI. Z.div_mod_to_equations. lia.
        * apply shlen_nonneg. clear -Q5 Q6. lia.
        * pose proof (farr_vs_user L c'' c _ _ UB (rup n 8) ltac:(clear -PC0 ABUB; lia) ltac:(clear -PC0 UBS; lia) FA1 FA2) as D.
          assert (AM : afreearr L c'' mod 8 = 0) by (unfold afreearr, K_FREEARR_OFF; clear -RM''; Z.div_mod_to_equations; lia).
          rewrite EGQ. destruct D as [D|D]; [left; apply shad_sep; [exact D| exact AM] | right; apply shad_sep; [exact D| clear -UB16; Z.div_mod_to_equations; lia]].
    - (* [comment removed for export] *)
      eapply (aslots_update_gen L _ m m' MUn WM st st' X X' c''); [exact SLOTS | apply NDS | exact EC3 | exact EC4 | |].
      + intros k'' Hk''.
        (pose proof (slot_geo L st X c'' k'' ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) Hk'') as ndP__; nd_pre ndP__ 12%nat; intros T16 TM16 TAL P1 P2 P3 P4 P5 P6 P7 P8 _; nd_post).
        assert (D1 : (c'' = c /\ k'' = k) \/ (c'' <> c \/ k'' <> k)) by (clear; lia). destruct D1 as [[Ec Ek]|NE1].
        * (* [comment removed for export] *)
          subst c'' k''. right.
          subst X'. rewrite (busy_of_xbatch' X k24 c k).
          assert (NOK : ((K_BATCH_CLASS =? c) && (k24 =? k)) = false).
          { destruct (Z.eqb_spec K_BATCH_CLASS c) as [E1'|]; [| reflexivity]. destruct (Z.eqb_spec k24 k) as [E2'|]; [| reflexivity]. exfalso.
            (nd_pre (NEWF EA) 3%nat; intros _ NB _; nd_post). pose proof (busy_of_X_self_g L st X BQuar c k n b1 ctx l1 l2 XB WF) as E'. rewrite <- E1', <- E2', NB in E'. discriminate. }
          rewrite NOK, (busy_of_X_self_g L st X BQuar c k n b1 ctx l1 l2 XB WF).
          unfold aslot_busy, bany. cbn [xb_st xb_class xb_n xb_b1 xb_ctx xb_slot bstate_byte]. unfold xb_user, xb_hdr, xb_alloc. cbn [xb_class xb_slot xb_n].
          rewrite <- EAB. fold S. rewrite <- EUB.
          split; [| split].
          -- intros R16. pose proof (rz_gt16 n (proj1 N0) R16) as R32. destruct (LH R16) as [LC LJ]. split.
             ++ eapply cells_frame; [exact LC | exact MUn | exact WM |]. cbn [cells_size csize Nat.add].
                apply Kres; clear -G5 G6 RSP RES RHI S16 EUB R32 S8 SEPL SEPE SEPG; unfold K_SPACE_SIZE in *; lia.
             ++ eapply junk_frame; [exact LJ | exact MUn | exact WM |]. intros Hp.
                apply Kres; clear -G5 G6 RSP RES RHI S16 EUB R32 S8 SEPL SEPE SEPG Hp; unfold K_SPACE_SIZE in *; lia.
          -- exists 3. split; [reflexivity|]. exact HDR'.
          -- replace (S - rz_size n) with (8 + (S - rz_size n - 8)) by (clear; lia).
             apply (junk_merge m' UB 8 (S - rz_size n - 8)); [| | clear; lia | clear -S8; lia].
             ++ pose proof (junk_of_cells m' _ _ FC') as J. cbn in J. exact J.
             ++ eapply junk_frame; [exact UJR | exact MUn | exact WM |]. intros Hp.
                apply Kres; clear -G5 G6 RSP RES RHI S16 EUB ABUB S8 SEPL SEPE SEPG Hp; unfold K_SPACE_SIZE in *; lia.
        * (* [comment removed for export] *)
          assert (T2 : (c =? c'') && (k =? k'') = false).
          { destruct (Z.eqb_spec c c'') as [E|]; [| reflexivity]. destruct (Z.eqb_spec k k'') as [E'|]; [| reflexivity]. exfalso. clear -NE1 E E'. lia. }
          assert (D2 : (enq_is_app st = false /\ c'' = K_BATCH_CLASS /\ k'' = k24) \/ (enq_is_app st = true \/ c'' <> K_BATCH_CLASS \/ k'' <> k24))
            by (rewrite EA; clear; lia).
          destruct D2 as [(EA2 & E24 & EK24)|NE2].
          -- (* [comment removed for export] *)
             subst c'' k''. right.
             subst X'. rewrite (busy_of_xbatch' X k24 K_BATCH_CLASS k24). rewrite !Z.eqb_refl. cbn [andb].
             unfold aslot_busy, bbatch. cbn [xb_st xb_class xb_slot]. unfold xb_alloc. cbn [xb_class xb_slot]. rewrite size_of_class_24.
             subst ek. unfold ek_of in EKP. rewrite EA in EKP. cbn [ek_post] in EKP. (nd_pre EKP 6%nat; intros _ _ BC BA [bsb BJ] _; nd_post).
             fold (abatch_addr L k24) in BC, BA, BJ |- *. change (aslot_addr L K_BATCH_CLASS k24) with (abatch_addr L k24).
             replace 8192 with (24 + (8 * Z.of_nat (length [Z_to_bv 64 (UB - 16)]) + (8192 - 24 - 8 * 1))) by (cbn; lia).
             apply junk_merge; [| | clear; lia| cbn; clear; lia].
             ++ pose proof (junk_of_cells m' _ _ BC) as J. cbn in J. exact J.
             ++ apply junk_merge; [apply junk_of_u64arr; exact BA | | cbn; clear; lia | clear; lia].
                cbn [length Z.of_nat Pos.of_succ_nat]. eexists. exact BJ.
          -- assert (T1 : (K_BATCH_CLASS =? c'') && (k24 =? k'') = false).
             { destruct (Z.eqb_spec K_BATCH_CLASS c'') as [E|]; [| reflexivity]. destruct (Z.eqb_spec k24 k'') as [E'|]; [| reflexivity]. exfalso.
               destruct NE2 as [NE|[NE|NE]]; [congruence| apply NE; symmetry; exact E| apply NE; symmetry; exact E']. }
             assert (BX : busy_of X' c'' k'' = busy_of X c'' k'').
             { subst X'. rewrite (busy_of_xbatch' X k24 c'' k''), T1. reflexivity. }
             (* [comment removed for export] *)
             assert (BQ : forall q, In q (q_loc Q ++ q_glob Q) -> c'' = K_BATCH_CLASS -> aslot_addr L c'' k'' = abatch_addr L (qb_slot q) ->
                 exists yq, busy_of X c'' k'' = Some yq /\ xb_st yq = BBatch /\ xb_class yq = K_BATCH_CLASS /\ xb_slot yq = k''
                            /\ junk_at m (abatch_addr L (qb_slot q)) 8192 /\ k'' = qb_slot q).
             { intros q Hq -> EQA. (nd_pre (bslot_busy L st X Q CP q Hq) 5%nat; intros yq Hyq Syq Cyq Kyq; nd_post).
               assert (EK' : k'' = qb_slot q) by (unfold abatch_addr, aslot_addr in EQA; rewrite size_of_class_24 in EQA; clear -EQA; lia). subst k''.
               exists yq. pose proof (busy_of_In_nodup L st X yq WF Hyq) as BY. rewrite Cyq, Kyq in BY.
               split; [exact BY|]. split; [exact Syq|]. split; [exact Cyq|]. split; [exact Kyq|]. split; [| reflexivity].
               destruct SLOTS as [SLK _]. specialize (SLK (qb_slot q) Hk''). rewrite BY in SLK. unfold aslot_busy in SLK. rewrite Syq in SLK.
               unfold xb_alloc in SLK. rewrite Cyq, Kyq, size_of_class_24 in SLK. exact SLK. }
             assert (D3 : (c'' = K_BATCH_CLASS /\ lst <> 0 /\ aslot_addr L c'' k'' = lst) \/ (c'' <> K_BATCH_CLASS \/ lst = 0 \/ aslot_addr L c'' k'' <> lst)) by (clear; lia).
             destruct D3 as [(E24 & LNZ & EL)|NE3].
             ++ (* [comment removed for export] *)
                right. rewrite BX. destruct LSTF as [Z0|((q & Hq & Eq) & F1 & F2 & F3 & F4)]; [exfalso; exact (LNZ Z0)|].
                (nd_pre (BQ q ltac:(apply in_or_app; left; exact Hq) E24 ltac:(rewrite EL; exact Eq)) 7%nat; intros yq BY Syq Cyq Kyq JQ EKQ; nd_post).
                rewrite BY. unfold aslot_busy. rewrite Syq. unfold xb_alloc. rewrite Cyq, Kyq, size_of_class_24, <- E24, EL.
                assert (QNE : a_qloc st <> []) by (intros QL0; apply LNZ; rewrite ELST; replace (q_loc Q) with (@nil qbatchc) by (clear -QL0 LN1; destruct (q_loc Q); [reflexivity| rewrite QL0 in LN1; cbn in LN1; discriminate]); reflexivity).
                subst ek. unfold ek_of in EKP, EK. rewrite EA in EKP, EK; cbn [ek_post ek_pre] in EKP, EK.
                ** destruct (a_qloc st) as [|b0 bs0] eqn:QL0; [exfalso; exact (QNE eq_refl)|]. rewrite <- QL0 in *.
                   (nd_pre EKP 6%nat; intros _ _ _ _ _ [LB' LA']; nd_post). destruct EK as ((_ & _ & _ & _ & _ & _ & _ & LEN0 & _) & _).
                   rewrite ELST in LB', LA' |- *.
                   replace 8192 with (24 + 8 * Z.of_nat (length (map (Z_to_bv 64) (qhdrs L (b_chunks (List.last (a_qloc st) dummy_batch)) (qb_ks (List.last (q_loc Q) dummy_qb))))))
                     by (rewrite LEN0; clear; lia).
                   apply junk_merge; [| apply junk_of_u64arr; exact LA' | clear; lia| rewrite LEN0; clear; lia].
                   pose proof (junk_of_cells m' _ _ LB') as J. cbn in J. exact J.
             ++ assert (D4 : (g_drain g = true /\ c'' = K_BATCH_CLASS /\ gl <> 0 /\ aslot_addr L c'' k'' = gl /\ gl <> lst)
                           \/ (g_drain g = false \/ c'' <> K_BATCH_CLASS \/ gl = 0 \/ aslot_addr L c'' k'' <> gl \/ gl = lst)) by (destruct (g_drain g); clear; lia).
                destruct D4 as [(GD & E24 & GNZ & EG & GNL)|NE4].
                ** (* [comment removed for export] *)
                   right. rewrite BX. destruct GLF as [[GD' _]|(_ & GQL & [Z0|((q & Hq & Eq) & F1 & F2 & F3 & F4)])]; [congruence| exfalso; exact (GNZ Z0)|].
                   (nd_pre (BQ q ltac:(apply in_or_app; right; exact Hq) E24 ltac:(rewrite EG; exact Eq)) 7%nat; intros yq BY Syq Cyq Kyq JQ EKQ; nd_post).
                   rewrite BY. unfold aslot_busy. rewrite Syq. unfold xb_alloc. rewrite Cyq, Kyq, size_of_class_24, <- E24, EG.
                   (* [comment removed for export] *)
                   assert (GNE : a_qglob st <> []) by (intros QG0; clear -QG0 Hq LN2; destruct (q_glob Q) eqn:QQ0; [destruct Hq| rewrite QG0 in LN2; cbn in LN2; discriminate]).
                   unfold dk_post in DKP. rewrite GD in DKP. (nd_pre DKP 3%nat; intros _ _ GLN; nd_post).
                   assert (GF : g_full g = true) by (subst g; unfold g_of; cbn [g_full]; clear -GNE; destruct (a_qglob st); [exfalso; exact (GNE eq_refl)| reflexivity]).
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
                       { destruct EBK as [E|[EA2 E]]; [left; exact E| right]. rewrite E, Eq. exact (KDIS q ltac:(apply in_or_app; right; exact Hq) EA2). }
                       apply Kres; clear -F3 F4 RES RHI SEPG GNZ DL DE ABUB S8 EUB; lia.
                ** (* [comment removed for export] *)
                   left. split; [exact BX|]. split.
                   +++ assert (DW9 : aslot_addr L c'' k'' + size_of_class c'' <= AB \/ AB + S <= aslot_addr L c'' k'').
                       { pose proof (slots_sep_any L st X c'' k'' c k ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) HC Hk'' KR NE1) as D.
                         rewrite <- EAB, <- ES in D. exact D. }
                       assert (DQ : forall q, In q (q_loc Q ++ q_glob Q) -> (c'' <> K_BATCH_CLASS \/ aslot_addr L c'' k'' <> abatch_addr L (qb_slot q)) ->
                           aslot_addr L c'' k'' + size_of_class c'' <= abatch_addr L (qb_slot q) \/ abatch_addr L (qb_slot q) + 8192 <= aslot_addr L c'' k'').
                       { intros q Hq NE. pose proof (slots_sep_any L st X c'' k'' K_BATCH_CLASS (qb_slot q) ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) (K24) Hk''
                                       (bslot_range L st X Q WF CP q Hq) ltac:(destruct NE as [NE|NE]; [left; exact NE| destruct (Z.eq_dec c'' K_BATCH_CLASS) as [->|NC']; [right| left; exact NC']];
                                                                                    intros EKK; apply NE; rewrite EKK; reflexivity)) as D.
                         rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
                       assert (DW13 : lst = 0 \/ aslot_addr L c'' k'' + size_of_class c'' <= lst \/ lst + 8192 <= aslot_addr L c'' k'').
                       { destruct LSTF as [Z0|((ql & Hql & Eql) & _)]; [left; exact Z0| right]. rewrite Eql. apply DQ; [apply in_or_app; left; exact Hql|].
                         destruct NE3 as [NE|[Z0|NE]]; [left; exact NE| exfalso| right; rewrite <- Eql; exact NE].
                         rewrite Eql in Z0. (nd_pre (BGEO ql ltac:(apply in_or_app; left; exact Hql)) 4%nat; intros _ _ B3 _; nd_post). clear -Z0 B3 RES RHI. lia. }
                       assert (DW14 : eb = lst \/ aslot_addr L c'' k'' + size_of_class c'' <= eb \/ eb + 8192 <= aslot_addr L c'' k'').
                       { destruct EBK as [E|[EA2 E]]; [left; exact E| right]. rewrite E. (nd_pre (NEWF EA2) 4%nat; intros _ _ KK _; nd_post).
                         pose proof (slots_sep_any L st X c'' k'' K_BATCH_CLASS k24 ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) (K24) Hk'' KK
                                       ltac:(destruct NE2 as [NE|[NE|NE]]; [rewrite EA in NE; discriminate| left; exact NE| right; exact NE])) as D.
                         rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
                       assert (DW15 : gl = lst \/ gl = 0 \/ aslot_addr L c'' k'' + size_of_class c'' <= gl \/ gl + 8192 <= aslot_addr L c'' k'').
                       { destruct GLF as [[_ E]|(GD & GQL & [Z0|((q & Hq & Eq) & _)])]; [left; exact E| right; left; exact Z0| right; right].
                         rewrite Eq. apply DQ; [apply in_or_app; right; exact Hq|].
                         destruct NE4 as [NE|[NE|[NE|[NE|NE]]]]; [congruence| left; exact NE| | right; rewrite <- Eq; exact NE| ].
                         - exfalso. rewrite Eq in NE. (nd_pre (BGEO q ltac:(apply in_or_app; right; exact Hq)) 4%nat; intros _ _ B3 _; nd_post). clear -NE B3 RES RHI. lia.
                         - rewrite NE in *. destruct NE3 as [NE'|[Z0|NE']]; [left; exact NE'| exfalso| right; rewrite <- Eq; exact NE'].
                           rewrite Eq in Z0. (nd_pre (BGEO q ltac:(apply in_or_app; right; exact Hq)) 4%nat; intros _ _ B3 _; nd_post). clear -Z0 B3 RES RHI. lia. }
                       apply Kres; [clear -P5 RSP; lia | clear -P6 RSP; unfold K_SPACE_SIZE in *; lia | clear -T16; lia | clear -DW9 ABUB S8 EUB; lia
                                   | clear -DW13 P5 RSP RES RHI; lia | clear -DW14 DW13 P5 RSP RES RHI; lia | clear -DW15 DW13 P5 RSP RES RHI; lia].
                   +++ intros b Hb. (nd_pre (busy_of_Some_facts X c'' k'' b Hb) 3%nat; intros IB CB' KB'; nd_post). split; [exact CB'|]. split; [exact KB'|]. exact (awf_fits L st X b WF IB).
      + intros POS''.
        set (AU := aregion L c'' + c_allocated_user (get_cls st c'')) in *.
        assert (U0 : aregion L c'' <= AU /\ AU + (c_mapped_user (get_cls st c'') - c_allocated_user (get_cls st c'')) <= aregion L c'' + K_FREEARR_OFF) by (subst AU; clear -Q1 Q2; lia).
        destruct U0 as [U0 U0'].
        assert (U1 : c'' = c -> aregion L c + c_allocated_user (get_cls st c) <= AU) by (intros E; subst AU; rewrite <- E; clear; lia).
        assert (U2 : c'' = K_BATCH_CLASS -> aregion L K_BATCH_CLASS + c_allocated_user (get_cls st K_BATCH_CLASS) <= AU) by (intros E; subst AU; rewrite <- E; clear; lia).
        idtac "UND1".
        apply Kres; [clear -RI4 Q1 U0; lia | subst AU; clear -Q1 Q2 RI2 RI3; unfold K_FREEARR_OFF, K_REGION, K_SPACE_SIZE in *; lia | clear -POS''; lia | | | |].
        * pose proof (undist_vs_user L c'' c _ _ AB S (c_allocated_user (get_cls st c)) (proj1 PC0) (proj2 (proj2 PC0)) ltac:(clear -G3 G4; lia) U1 U0 U0') as D.
          clear -D ABUB S8 EUB. lia.
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
      + intros k'' Hk''.
        (pose proof (slot_geo L st X c'' k'' ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) Hk'') as ndP__; nd_pre ndP__ 12%nat; intros T16 TM16 TAL P1 P2 P3 P4 P5 P6 P7 P8 _; nd_post).
        assert (D1 : (c'' = c /\ k'' = k) \/ (c'' <> c \/ k'' <> k)) by (clear; lia). destruct D1 as [[Ec Ek]|NE1].
        * (* [comment removed for export] *)
          subst c'' k''. right.
          subst X'. rewrite (busy_of_xbatch' X k24 c k).
          assert (NOK : ((K_BATCH_CLASS =? c) && (k24 =? k)) = false).
          { destruct (Z.eqb_spec K_BATCH_CLASS c) as [E1'|]; [| reflexivity]. destruct (Z.eqb_spec k24 k) as [E2'|]; [| reflexivity]. exfalso.
            (nd_pre (NEWF EA) 3%nat; intros _ NB _; nd_post). pose proof (busy_of_X_self_g L st X BQuar c k n b1 ctx l1 l2 XB WF) as E'. rewrite <- E1', <- E2', NB in E'. discriminate. }
          rewrite NOK, (busy_of_X_self_g L st X BQuar c k n b1 ctx l1 l2 XB WF).
          unfold slot_shadow_bytes, bany. cbn [xb_n xb_st]. rewrite <- EAB. fold S.
          (* [comment removed for export] *)
          eapply cells_frame in SHA; [| exact MUn | exact WM | cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by (clear -GR3; lia);
                                       apply Kshad; [clear -SHLO; lia| clear -SHHI GR3 GFS SE G0 GE; lia| clear -GR3; lia| left; clear -SE; lia]].
          eapply cells_frame in SHR; [| exact MUn | exact WM | cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by (clear -GFS GE GR3; unfold granules in *; lia);
                                       apply Kshad; [clear -SHLO SE GR3 G0 EGQ; lia| clear -SHHI GR3 GFS SE G0 GE EGQ; lia| clear -GFS GE GR3; unfold granules in *; lia| right; clear -EGQ; lia]].
          rewrite EGQ in SH'.
          replace (shad UB) with (shad AB + Z.of_nat (Z.to_nat (shlen (rz_size n)))) in SH' by (clear -SE GR3; lia).
          rewrite EGQ in SHR, G0.
          replace (shad UB + shlen (rup n 8)) with (shad AB + Z.of_nat (Z.to_nat (shlen (rz_size n))) + Z.of_nat (Z.to_nat (shlen (rup n 8)))) in SHR by (clear -SE GR3 G0; lia).
          pose proof (cb_app m' _ _ _ _ _ SHA (cb_app m' _ _ _ _ _ SH' SHR)) as FIN.
          assert (GE' : shlen (rup n 8) = granules n) by (rewrite <- EGQ; exact GE). rewrite <- GE'.
          replace (Z.to_nat (shlen (rz_size n)) + (Z.to_nat (shlen (rup n 8)) + Z.to_nat (shlen S - shlen (rz_size n) - shlen (rup n 8))))%nat with (Z.to_nat (shlen S)) in FIN
            by (clear -GR3 G0 GE' GFS; unfold granules in *; lia).
          rewrite <- ?app_assoc in FIN. rewrite <- ?app_assoc. exact FIN.
        * left.
          assert (T2 : (c =? c'') && (k =? k'') = false).
          { destruct (Z.eqb_spec c c'') as [E|]; [| reflexivity]. destruct (Z.eqb_spec k k'') as [E'|]; [| reflexivity]. exfalso. clear -NE1 E E'. lia. }
          split.
          -- subst X'. rewrite (busy_of_xbatch' X k24 c'' k'').
             destruct ((K_BATCH_CLASS =? c'') && (k24 =? k'')) eqn:T1; [| reflexivity].
             destruct (Z.eqb_spec K_BATCH_CLASS c'') as [<-|]; [| discriminate]. destruct (Z.eqb_spec k24 k'') as [<-|]; [| discriminate].
             (nd_pre (NEWF EA) 3%nat; intros _ NB _; nd_post). rewrite NB. rewrite size_of_class_24. rewrite slot_shadow_bbatch by (clear; change (shlen 8192) with 1024; lia).
             reflexivity.
          -- assert (DW : aslot_addr L c'' k'' + size_of_class c'' <= AB \/ AB + S <= aslot_addr L c'' k'').
             { pose proof (slots_sep_any L st X c'' k'' c k ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) HC Hk'' KR NE1) as D.
               rewrite <- EAB, <- ES in D. exact D. }
             pose proof (slot_aligned L c'' k'' SAL ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia)) as AL''.
             apply Kshad.
             ++ rewrite shad_div. unfold ASHOFF. clear -P7 RES RHI. Z.div_mod_to_equations. lia.
             ++ rewrite shad_div, shlen_div. unfold ASHOFF in *. clear -P8 T16. Z.div_mod_to_equations. lia.
             ++ apply shlen_nonneg. clear -T16; lia.
             ++ rewrite EGQ. destruct DW as [D|D].
                ** left. eapply Z.le_trans; [apply shad_sep; [exact D| clear -AL''; Z.div_mod_to_equations; lia]|]. clear -SE GR3; lia.
                ** right. apply shad_sep; [clear -D UBS; lia| exact UB16'].
      + intros POS''.
        set (AU := aregion L c'' + c_allocated_user (get_cls st c'')) in *.
        assert (U0 : aregion L c'' <= AU /\ AU + (c_mapped_user (get_cls st c'') - c_allocated_user (get_cls st c'')) <= aregion L c'' + K_FREEARR_OFF) by (subst AU; clear -Q1 Q2; lia).
        destruct U0 as [U0 U0'].
        assert (U1 : c'' = c -> aregion L c + c_allocated_user (get_cls st c) <= AU) by (intros E; subst AU; rewrite <- E; clear; lia).
        pose proof (undist_vs_user L c'' c _ _ UB (rup n 8) (c_allocated_user (get_cls st c)) ltac:(clear -PC0 ABUB; lia) ltac:(clear -PC0 UBS; lia) ltac:(clear -G3 G4; lia) U1 U0 U0') as D.
        assert (AM : AU mod 8 = 0) by (subst AU; pose proof (mod16_of_class _ _ Q3 QS16 ltac:(clear -QS; lia)) as AM; clear -AM RM''; Z.div_mod_to_equations; lia).
        apply Kshad.
        * rewrite shad_div. unfold ASHOFF. clear -U0 RI4 RES RHI. Z.div_mod_to_equations. lia.
        * rewrite shad_div, shlen_div. unfold ASHOFF, K_FREEARR_OFF, K_REGION, K_SPACE_SIZE in *. clear -U0' RI2 RI3 RES RHI. Z.div_mod_to_equations. lia.
        * clear -POS''; lia.
        * rewrite EGQ. destruct D as [D|D]; [left; apply shad_sep; [exact D| exact AM] | right; apply shad_sep; [exact D| exact UB16']].
  }
  (* [comment removed for export] *)
  assert (AVL' : forall c'', 1 <= c'' < K_NUM_CLASSES -> ashadow_avail L st' m' c'').
  { intros c'' Hc''. pose proof WF as WF0. (nd_pre WF0 7%nat; intros _ _ SAL _ _ PERC _; nd_post).
    (nd_pre (PERC c'' Hc'') 8%nat; intros Q1 Q2 Q3 Q4 Q5 Q6 Q7 _; nd_post).
    pose proof (size_of_class_facts c'' Hc'') as [QS QS16]. pose proof (aregion_mod L c'' SAL) as RM''.
    assert (EC2 : c_mapped_free_array (get_cls st' c'') = c_mapped_free_array (get_cls st c'')) by (destruct (Z.eq_dec c'' K_BATCH_CLASS) as [->|NE]; [exact M24d| rewrite (GCo' c'' NE); reflexivity]).
    assert (EC4 : c_mapped_user (get_cls st' c'') = c_mapped_user (get_cls st c'')) by (destruct (Z.eq_dec c'' K_BATCH_CLASS) as [->|NE]; [exact M24a| rewrite (GCo' c'' NE); reflexivity]).
    unfold K_NUM_CLASSES in Hc''.
    assert (RI : al_res L + 4096 <= aregion L c'' /\ aregion L c'' + K_REGION <= al_space_beg L + K_SPACE_SIZE /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
    { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc'' RSP. lia. }
    (nd_pre RI 3%nat; intros RI1 RI2 RI3; nd_post).
    assert (PC0 : aregion L c <= AB /\ AB + S <= aregion L c + K_FREEARR_OFF /\ AB + S <= aregion L c + c_allocated_user (get_cls st c)) by (clear -G1 G2 G3 G4; lia).
    eapply ashadow_avail_frame; [exact MUn | exact WM | exact (AVL c'' ltac:(unfold K_NUM_CLASSES; exact Hc'')) | exact EC4 | exact EC2 | |].
    - intros POS''. set (AU := aregion L c'' + c_mapped_user (get_cls st c'')) in *.
      assert (U0 : aregion L c'' <= AU /\ AU + (K_FREEARR_OFF - c_mapped_user (get_cls st c'')) <= aregion L c'' + K_FREEARR_OFF) by (subst AU; clear -Q1 Q2; lia).
      destruct U0 as [U0 U0'].
      assert (U1 : c'' = c -> aregion L c + c_mapped_user (get_cls st c) <= AU) by (intros E; subst AU; rewrite <- E; clear; lia).
      pose proof (undist_vs_user L c'' c _ _ UB (rup n 8) (c_mapped_user (get_cls st c)) ltac:(clear -PC0 ABUB; lia) ltac:(clear -PC0 UBS G3; lia) G4 U1 U0 U0') as D.
      assert (AM : AU mod 8 = 0) by (subst AU; generalize Q4 RM''; clear; unfold K_USER_MAP; intros; Z.div_mod_to_equations; lia).
      apply Kshad.
      + rewrite shad_div. unfold ASHOFF. clear -U0 RI1 RES RHI. Z.div_mod_to_equations. lia.
      + rewrite shad_div, shlen_div. unfold ASHOFF, K_FREEARR_OFF, K_REGION, K_SPACE_SIZE in *. clear -U0' RI2 RI3 RES RHI. Z.div_mod_to_equations. lia.
      + clear -POS''; lia.
      + rewrite EGQ. destruct D as [D|D]; [left; apply shad_sep; [exact D| exact AM] | right; apply shad_sep; [exact D| exact UB16']].
    - intros POS''. set (AU := afreearr L c'' + c_mapped_free_array (get_cls st c'')) in *.
      assert (FA : aregion L c'' + K_FREEARR_OFF <= AU /\ AU + (K_FREEARR_MAX - c_mapped_free_array (get_cls st c'')) <= aregion L c'' + K_REGION).
      { subst AU. unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q5 Q6. lia. }
      destruct FA as [FA1 FA2].
      pose proof (farr_vs_user L c'' c _ _ UB (rup n 8) ltac:(clear -PC0 ABUB; lia) ltac:(clear -PC0 UBS; lia) FA1 FA2) as D.
      assert (AM : AU mod 8 = 0) by (subst AU; generalize Q7 RM''; clear; unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAP; intros; Z.div_mod_to_equations; lia).
      apply Kshad.
      + rewrite shad_div. unfold ASHOFF, K_FREEARR_OFF in *. clear -FA1 RI1 RES RHI. Z.div_mod_to_equations. lia.
      + rewrite shad_div, shlen_div. unfold ASHOFF, K_SPACE_SIZE in *. clear -FA2 RI2 RI3 RES RHI. Z.div_mod_to_equations. lia.
      + clear -POS''; lia.
      + rewrite EGQ. destruct D as [D|D]; [left; apply shad_sep; [exact D| exact AM] | right; apply shad_sep; [exact D| exact UB16']]. }
  (* [comment removed for export] *)
  assert (HS' : ASEC L st' X' m').
  { eapply (hs_frame _ HL L st st' X X' m m'); [exact HS | exact MUn | exact WM | |].
    - unfold sec_untouched, aknown. unfold AINSTANCE, K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
      assert (SHB : 2201439137792 <= shad UB /\ shad UB + gq <= 17594333495296) by (clear -SHLO SHHI SE GR3 GFS GE EGQ G0; lia).
      (* [comment removed for export] *)
      assert (SHB1 : shad (al_space_beg L) + 536870912 <= shad (aregion L c)).
      { rewrite !shad_div. unfold aregion, K_REGION, K_NUM_CLASSES in *. change (2^32) with 4294967296 in *. clear -HC. Z.div_mod_to_equations. lia. }
      assert (SHB2 : shad (aregion L c) + shlen (c_mapped_user (get_cls st c)) <= shad (al_space_beg L) + 17179869184).
      { (pose proof (alayout_space L ALO) as ndP__; nd_pre ndP__ 4%nat; intros _ _ SPal _; nd_post). rewrite !shad_div, shlen_div. unfold aregion, K_REGION, K_ALIGN, K_FREEARR_OFF, K_NUM_CLASSES in *. change (2^32) with 4294967296 in *.
        clear -HC G4 SPal. Z.div_mod_to_equations. lia. }
      (* [comment removed for export] *)
      apply Forall_cons; [cbn [fst snd]; intros a Ha; do 4 right; left; clear -Ha CEIL LO; lia |].
      do 4 (apply Forall_cons; [cbn [fst snd]; intros a Ha; left; left; clear -Ha; unfold AIMG_HI, AINSTANCE; lia |]).   (* [comment removed for export] *)
      do 4 (apply Forall_cons; [cbn [fst snd]; intros a Ha; do 5 right; left; clear -Ha OT TBND TIMG; lia |]).
      apply Forall_cons; [cbn [fst snd]; intros a Ha; do 7 right; left; clear -Ha G5 G6 ABUB S8 EUB RSP; lia |].
      apply Forall_cons; [cbn [fst snd]; intros a Ha; right; left; clear -Ha SE GR3 GFS GE EGQ G0 SHM1 SHM2 SHB1 SHB2; lia |].
      apply Forall_cons; [cbn [fst snd]; intros a Ha; do 8 right; left; clear -Ha; lia |].
      apply Forall_cons; [cbn [fst snd]; intros a Ha; do 9 right; left; clear -Ha; lia |].
      apply Forall_cons; [cbn [fst snd]; intros a Ha; clear -Ha RES RHI RSP LSTF; destruct LSTF as [Z0|(_ & _ & _ & F3 & F4)]; [rewrite Z0, qsz_0 in Ha; left; left; unfold AIMG_HI, AINSTANCE; lia| pose proof (qsz_bound lst); do 7 right; left; lia] |].   (* [comment removed for export] *)
      apply Forall_cons; [cbn [fst snd]; intros a Ha; clear -Ha RES RHI RSP EBF EBNZ; destruct EBF as [Z1|(_ & _ & E3 & E4)]; [exfalso; lia| do 7 right; left; lia] |].
      apply Forall_cons; [cbn [fst snd]; intros a Ha; clear -Ha RES RHI RSP LSTF GLF; destruct GLF as [[_ Z2]|(_ & _ & [Z2|(_ & _ & _ & H3 & H4)])];
        [ subst gl; destruct LSTF as [Z0|(_ & _ & _ & F3 & F4)]; [left; left; unfold AIMG_HI, AINSTANCE; lia| do 7 right; left; lia] | left; left; unfold AIMG_HI, AINSTANCE; lia | do 7 right; left; lia] |].
      apply Forall_nil.
    - exact (sec_same_core st st' SC (sec_chunks_qperm st st' ELIVE (st_after_enq_qfilt is_sec st (CPrim c n) eq_refl))). }
  assert (BL' : ablocks L st' X' LB) by (subst X'; exact (ablocks_xbatchR L st st' X LB k24 ELIVE BL)).
  assert (FKD : forall cls FA sz, In (mkABlock (ABFake cls) FA sz) LB -> al_fake L <= FA /\ 0 <= sz /\ FA + sz <= al_fake L + 11571200)
    by (intros cls FA sz Hin; exact (proj1 (proj2 BL) cls FA sz Hin)).
  pose proof (ao_fake L ALO) as FKO. (pose proof (aobj_int _ _ FKO ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros FKi FKa [kF FBND]; nd_post). unfold aobj in FKO.   (* [comment removed for export] *)
  pose proof (ad_t_fake L ALO) as D_t_f. pose proof (ad_fake_res L ALO) as D_f_res. pose proof (ad_nodes_fake L ALO) as D_n_f. pose proof (ad_store_fake L ALO) as D_s_f.
  unfold adisj in D_t_f, D_f_res, D_n_f, D_s_f. box D_t_f. box D_f_res. box D_n_f. box D_s_f.
  assert (HFK' : AFK L LB m').
  { eapply (hf_frame _ HL L LB m m'); [exact HFK | exact MUn | exact WM |].
    - pose proof (ao_dtls L ALO) as DTO. (pose proof (aobj4_int _ DTO) as ndP__; nd_pre ndP__ 4%nat; intros _ _ [kD DBND] [jD DIMG]; nd_post). unfold aobj in DTO.   (* [comment removed for export] *)
      pose proof (ad_t_dtls L ALO) as D1. pose proof (ad_dtls_res L ALO) as D2. pose proof (ad_nodes_dtls L ALO) as D3. pose proof (ad_store_dtls L ALO) as D4.
      unfold adisj in D1, D2, D3, D4.
      unfold fake_untouched. unfold K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
      assert (SHF : (shad (al_fake L) + shlen 11571200 <= shad UB \/ shad UB + gq <= shad (al_fake L))
                    /\ 2148239360 <= shad (al_fake L) /\ shad (al_fake L) + shlen 11571200 <= 17594333495296).   (* [comment removed for export] *)
      { split; [| rewrite shad_div, shlen_div; unfold ASHOFF; pose proof atop_range as AR8; clear -FKO FKi FBND AR8; Z.div_mod_to_equations; lia].
        pose proof D_f_res as DFR. unbox DFR. rewrite EGQ. destruct DFR as [D|D].
        - left. apply shad_sep; [| clear -FKO FKi FBND; Z.div_mod_to_equations; lia]. clear -D RSP G5 ABUB. lia.
        - right. apply shad_sep; [| exact UB16']. clear -D RSP G6 UBS. lia. }
      (nd_pre SHF 3%nat; intros SHF1 SHF2 SHF3; nd_post).
      assert (SHB : 2201439137792 <= shad UB /\ shad UB + gq <= 17594333495296) by (clear -SHLO SHHI SE GR3 GFS GE EGQ G0; lia).
      pose proof D_t_f as DTF; unbox DTF. pose proof D_f_res as DFR; unbox DFR. pose proof D_n_f as DNF; unbox DNF. pose proof D_s_f as DSF; unbox DSF.
      assert (LSTR : (lst = 0 /\ qsz lst = 8) \/ (al_res L + 4096 <= lst /\ lst + 8192 <= al_res L + 137439023104 /\ qsz lst = 8192))   (* [comment removed for export] *)
        by (destruct LSTF as [Z0|(_ & _ & _ & F3 & F4)]; [left; split; [exact Z0| apply qsz_eq0; exact Z0]| right; split; [exact F3| split; [exact F4| apply qsz_pos; clear -F3 RES RHI; lia]]]).
      assert (EBR : al_res L + 4096 <= eb /\ eb + 8192 <= al_res L + 137439023104) by (destruct EBF as [Z0|(_ & _ & F3 & F4)]; [exfalso; clear -Z0 EBNZ; lia| split; assumption]).   (* [comment removed for export] *)
      assert (GLRR : gl = lst \/ gl = 0 \/ (al_res L + 4096 <= gl /\ gl + 8192 <= al_res L + 137439023104))
        by (destruct GLF as [[_ Z2]|(_ & _ & [Z2|(_ & _ & _ & H3 & H4)])]; [left; exact Z2| right; left; exact Z2| right; right; split; assumption]).
      (apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 EBR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 LSTR GLRR D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | idtac]]]]]]]]]]]]]]]]).
      apply Forall_nil. }
  (* [comment removed for export] *)
  assert (GNB : g_nb g = Z.of_nat (length (a_qglob st))) by reflexivity.
  assert (GFST : g_fst g = qfirst L (q_glob Q)) by reflexivity.
  assert (GQB : g_qb g = a_qglob_bytes st) by reflexivity.
  assert (GFU : g_full g = match a_qglob st with [] => false | _ :: _ => true end) by reflexivity.
  destruct DKP as [MX' DKP'].
  (pose proof (qnum_freeR st (CPrim c n) NUM ltac:(cbn [chunk_size]; clear -N1; lia) NOREC) as ndP__; nd_pre ndP__ 5%nat; intros NUM' NB2a NB2b NB2c NF2; nd_post).
  fold st2 st' in NUM', NB2a, NB2b, NB2c, NF2.
  pose proof (st_after_q st2) as [DRN NDR]. fold st' in DRN, NDR.
  assert (QK' : aquar_glob_const m').
  { split; [| exact MX']. eapply cells_frame; [exact QK | exact MUn | exact WM |]. cbn [cells_size csize Nat.add]. apply Kimg; clear; unfold AQ_MAX, AIMG_HI; lia. }
  assert (IA' : aintal true m').
  { split; [exact FL'|]. split; [exact IAS'|]. intros _ j Hj. apply IAM'. revert Hj. clear. unfold AIA_MAP1_LEN. cbn. lia. }
  (* [comment removed for export] *)
  assert (BLST : forall q, In q (q_loc Q ++ q_glob Q) -> abatch_addr L (qb_slot q) <> lst ->
      abatch_addr L (qb_slot q) + 8192 <= lst \/ lst + 8192 <= abatch_addr L (qb_slot q) \/ lst = 0).
  { intros q Hq NE. destruct LSTF as [Z0|((ql & Hql & Eql) & _)]; [right; right; exact Z0|].
    destruct (BDIS q ql Hq ltac:(apply in_or_app; left; exact Hql)) as [E|E]; [exfalso; apply NE; rewrite Eql; exact E| rewrite Eql].
    destruct E as [E|E]; [left; exact E| right; left; exact E]. }
  assert (BFR : forall q, In q (q_loc Q ++ q_glob Q) -> abatch_addr L (qb_slot q) <> lst -> abatch_addr L (qb_slot q) <> gl ->
      disjoint_from (Wf (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) (abatch_addr L (qb_slot q)) 8192).
  { intros q Hq NL NG. (nd_pre (BGEO q Hq) 4%nat; intros _ _ F3 F4; nd_post). pose proof (SEPQ q Hq) as SQ. pose proof (BLST q Hq NL) as DL.
    assert (DE : eb = lst \/ abatch_addr L (qb_slot q) + 8192 <= eb \/ eb + 8192 <= abatch_addr L (qb_slot q)).
    { destruct EBK as [E|[EA2 E]]; [left; exact E| right]. rewrite E.
      destruct (KDIS q Hq EA2) as [D|D]; [right; exact D| left; exact D]. }
    assert (DG : gl = lst \/ gl = 0 \/ abatch_addr L (qb_slot q) + 8192 <= gl \/ gl + 8192 <= abatch_addr L (qb_slot q)).
    { destruct GLF as [[_ E]|(_ & _ & [Z0|((qg & Hqg & Eqg) & _)])]; [left; exact E| right; left; exact Z0| right; right].
      destruct (BDIS q qg Hq ltac:(apply in_or_app; right; exact Hqg)) as [E|E]; [exfalso; apply NG; rewrite Eqg; exact E| rewrite Eqg; exact E]. }
    apply Kres; clear -F3 F4 RES RHI SQ DL DE DG ABUB S8 EUB; lia. }
  assert (HQ' : AQUAR L st' X' m').
  { subst ek. unfold ek_of in EKP, EK, QC', DKP', EEB, SB1, GDR, GL, GLST.
    rewrite EA in EKP, EK, QC', DKP', EEB, SB1, GDR, GLST; cbn [ek_nb ek_fst ek_lst ek_delta ek_b ek_post ek_pre] in EKP, EK, QC', DKP', EEB, SB1, GDR, GL, GLST.
    - (* [comment removed for export] *)
      (nd_pre (NEWF EA) 8%nat; intros NK24 NB24 KK24 NIB JK FK CIN POS; nd_post).
      (nd_pre EKP 6%nat; intros C24' [stj' SJ'] NBc NAc [bs NJc] OLDc; nd_post).
      pose proof EAPP0 as EAPP.
      set (nbt := mkABatch 1 (n + 8192) [CPrim c n]) in *.
      set (qn := mkQB k24 [k]) in *.
      assert (Q2 : a_qloc st2 = a_qloc st ++ [nbt] /\ a_qloc_bytes st2 = a_qloc_bytes st + (n + 8192) /\ a_qglob st2 = a_qglob st /\ a_qglob_bytes st2 = a_qglob_bytes st).
      { subst st2. unfold st_enq. rewrite EAPP. (pose proof (enq_new_core (CPrim c n) st) as ndP__; nd_pre ndP__ 7%nat; intros _ E1 E2 _ E3 E4 _; nd_post).
        rewrite E1, E2, E3, E4. subst nbt. cbn [chunk_size]. unfold Q_BATCH_BYTES.
        split; [reflexivity|]. split; [clear; lia|]. split; reflexivity. }
      (nd_pre Q2 4%nat; intros QL2 QB2 QG2 QGB2; nd_post).
      assert (FSTE : (if match a_qloc st with [] => false | _ :: _ => true end then qfirst L (q_loc Q) else abatch_addr L k24) = qfirst L (q_loc Q ++ [qn])).
      { rewrite qfirst_app_r. subst qn; cbn [qb_slot]. generalize LN1. clear. generalize (a_qloc st) (q_loc Q).
        intros [|x1 r1] [|x2 r2] LL; cbn in LL; first [reflexivity | discriminate]. }
      rewrite FSTE in QC'. rewrite FSTE in DKP'.
      assert (QLST' : qlast L (q_loc Q ++ [qn]) = abatch_addr L k24) by (subst qn; apply qlast_app1).
      (* [comment removed for export] *)
      assert (GNL : forall q, In q (q_glob Q) -> abatch_addr L (qb_slot q) <> lst).
      { intros q Hq E. assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; right; exact Hq).
        destruct LSTF as [Z0|((q' & Hq' & Eq') & _)].
        - (nd_pre (BGEO q INq) 4%nat; intros _ _ F3 _; nd_post). clear -F3 RES RHI E Z0. lia.
        - apply in_split in Hq. (nd_pre Hq 3%nat; intros gs1 gs2 EQg; nd_post). apply in_split in Hq'. (nd_pre Hq' 3%nat; intros qs1 qs2 EQl; nd_post).
          apply (bslots_nodup_split L st X Q CP qs1 q' (qs2 ++ gs1) q gs2); [rewrite EQl, EQg; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; reflexivity|].
          pose proof (bslot_range L st X Q WF CP q INq). pose proof (bslot_range L st X Q WF CP q' ltac:(apply in_or_app; left; rewrite EQl; apply in_or_app; right; left; reflexivity)).
          rewrite Eq' in E. unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia. }
      (* [comment removed for export] *)
      assert (ABO' : abatches_to L m' (a_qloc st) (q_loc Q) (abatch_addr L k24)).
      { destruct (a_qloc st) as [|b0 l0] eqn:QL0.
        - replace (q_loc Q) with (@nil qbatchc) by (clear -LN1; destruct (q_loc Q); [reflexivity| cbn in LN1; discriminate]). exact I.
        - cbv iota beta in OLDc. destruct OLDc as [OLD1 OLD2]. rewrite <- QL0 in *.
          assert (LNE : a_qloc st <> []) by (rewrite QL0; discriminate).
          assert (QL : a_qloc st = removelast (a_qloc st) ++ [List.last (a_qloc st) dummy_batch]) by (apply app_removelast_last; exact LNE).
          assert (LQ : (0 < length (q_loc Q))%nat) by (rewrite LN1, QL0; cbn; clear; lia).
          assert (QQ : q_loc Q = removelast (q_loc Q) ++ [List.last (q_loc Q) dummy_qb]) by (apply app_removelast_last; clear -LQ; destruct (q_loc Q); [cbn in LQ; clear -LQ; lia| discriminate]).
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
            { rewrite QLST. intros E. apply in_split in Hq. (nd_pre Hq 3%nat; intros qs1 qs2 EQl; nd_post).
              apply (bslots_nodup_split L st X Q CP qs1 q qs2 qz (q_glob Q)); [rewrite QQ, EQl; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; reflexivity|].
              pose proof (bslot_range L st X Q WF CP q INq). pose proof (bslot_range L st X Q WF CP qz ltac:(apply in_or_app; left; rewrite QQ; apply in_or_app; right; left; reflexivity)).
              unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia. }
            apply BFR; [exact INq | exact NEq |].
            destruct GLF as [[_ E]|(GD & GQL & [Z0|((qg & Hqg & Eqg) & _)])]; [rewrite E; exact NEq| rewrite Z0; (nd_pre (BGEO q INq) 4%nat; intros _ _ F3 _; nd_post); clear -F3 RES RHI; lia|].
            rewrite Eqg. intros E. apply in_split in Hq. (nd_pre Hq 3%nat; intros qs1 qs2 EQl; nd_post). apply in_split in Hqg. (nd_pre Hqg 3%nat; intros gs1 gs2 EQg; nd_post).
            apply (bslots_nodup_split L st X Q CP qs1 q (qs2 ++ [qz] ++ gs1) qg gs2); [rewrite QQ, EQl, EQg; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; reflexivity|].
            pose proof (bslot_range L st X Q WF CP q INq). pose proof (bslot_range L st X Q WF CP qg ltac:(apply in_or_app; right; rewrite EQg; apply in_or_app; right; left; reflexivity)).
            unfold abatch_addr, aslot_addr in E. rewrite size_of_class_24 in E. clear -E. lia.
          + cbn [abatches_to]. split; [| exact I].
            unfold abatch_cells. cbv zeta. change (hd (abatch_addr L k24) (qaddrs L [])) with (abatch_addr L k24). rewrite <- QLST.
            split; [rewrite FULL; exact OLD1|]. split; [exact OLD2|]. split; [| split; [exact Z4| split; [exact Z5| exact Z6]]].
            rewrite FULL. replace (Q_BATCH_BYTES - 24 - 8 * Q_BATCH) with 0 by reflexivity. unfold Q_BATCH. apply junk_nil; (destruct LSTF as [Z0|(_ & _ & _ & F3 & F4)]; [clear -Z0; lia | atop_facts; clear -F3 F4 RES RHI; lia]). }
      (* [comment removed for export] *)
      assert (ABN' : abatch_cells L m' nbt qn 0).
      { unfold abatch_cells. cbv zeta. subst nbt qn. cbn [qb_slot qb_ks b_size b_count b_chunks]. rewrite qhdrs_cons. cbn [qhdrs app map qhdr]. rewrite <- EAB, <- EUB.
        split; [exact NBc|]. split; [exact NAc|]. split; [exists bs; unfold Q_BATCH_BYTES; exact NJc|]. split; [reflexivity|]. split; [reflexivity| unfold Q_BATCH; clear; lia]. }
      assert (ABL' : abatches_to L m' (a_qloc st ++ [nbt]) (q_loc Q ++ [qn]) 0).
      { apply abatches_to_app; [exact LN1|]. split; [cbn [qaddrs map hd]; subst qn; cbn [qb_slot]; exact ABO'|]. cbn [abatches_to]. split; [exact ABN'| exact I]. }
      assert (CP2 : qcoupled L st2 X' (mkQConc (q_loc Q ++ [qn]) (q_glob Q) true pend)).
      { subst X' qn nbt.
        apply (qcoupled_new_pend L st X Q c k n b1 ctx l1 l2 st2 k24 (c_count (get_cls st K_BATCH_CLASS)) (n + 8192) true pend XB WF CP PEND eq_refl POS NK24 KK24 NIB QL2 QG2). }
      destruct (Z.lt_ge_cases Q_CACHE (a_qloc_bytes st2)) as [DR|NDRN].
      + (* [comment removed for export] *)
        (nd_pre (DRN DR) 4%nat; intros QL3 QB3 QG3 QGB3; nd_post).
        assert (GD : g_drain g = true) by (rewrite GDR; apply Z.ltb_lt; rewrite <- QB2; exact DR).
        unfold tcache_post in QC'. rewrite GD in DKP', QC'.
        destruct DKP' as [GC' GLN].
        exists (mkQConc [] (q_glob Q ++ (q_loc Q ++ [qn])) true pend). unfold AQUAR_at. cbn [q_loc q_glob q_ia].
        rewrite QL3, QB3, QG3, QGB3, QL2, QG2, QB2, QGB2.
        split; [exact QK'|]. split; [| split; [| split; [exact IA'| split]]].
        * split; [cbn [length qfirst qlast qaddrs map hd last Z.of_nat]; exact QC'| exact I].
        * split.
          -- rewrite length_app, Nat2Z.inj_add, <- GNB. rewrite length_app. cbn [length]. rewrite Nat2Z.inj_add. change (Z.of_nat 1) with 1.
             rewrite qlast_app by (intros Enil; apply app_eq_nil in Enil; destruct Enil as [_ Enil]; discriminate). rewrite QLST'.
             assert (FE : qfirst L (q_glob Q ++ q_loc Q ++ [qn]) = (if g_full g then g_fst g else qfirst L (q_loc Q ++ [qn]))).
             { rewrite GFU, GFST. destruct (a_qglob st) eqn:QG0.
               - replace (q_glob Q) with (@nil qbatchc) by (clear -LN2; destruct (q_glob Q); [reflexivity| cbn in LN2; discriminate]). reflexivity.
               - apply qfirst_app. destruct (q_glob Q); [cbn in LN2; discriminate| discriminate]. }
             rewrite FE, <- GQB. exact GC'.
          -- unfold abatches. apply abatches_to_app; [exact LN2|]. split.
             ++ (* [comment removed for export] *)
                rewrite hd_qaddrs by (intros Enil; apply app_eq_nil in Enil; destruct Enil as [_ Enil]; discriminate).
                destruct (a_qglob st) as [|bg0 lg0] eqn:QG0.
                ** replace (q_glob Q) with (@nil qbatchc) by (clear -LN2; destruct (q_glob Q); [reflexivity| cbn in LN2; discriminate]). exact I.
                ** rewrite <- QG0 in *.
                   assert (GNE : a_qglob st <> []) by (rewrite QG0; discriminate).
                   assert (QG : a_qglob st = removelast (a_qglob st) ++ [List.last (a_qglob st) dummy_batch]) by (apply app_removelast_last; exact GNE).
                   assert (LQg : (0 < length (q_glob Q))%nat) by (rewrite LN2, QG0; cbn; clear; lia).
                   assert (QQg : q_glob Q = removelast (q_glob Q) ++ [List.last (q_glob Q) dummy_qb]) by (apply app_removelast_last; clear -LQg; destruct (q_glob Q); [cbn in LQg; clear -LQg; lia| discriminate]).
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
                       { intros E. apply in_split in Hq. (nd_pre Hq 3%nat; intros gs1 gs2 EQg; nd_post).
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
                       (nd_pre (BGEO qgz INgz) 4%nat; intros _ _ F3 F4; nd_post). pose proof (SEPQ qgz INgz) as SQ. pose proof (BLST qgz INgz NGL) as DL.
                       pose proof (KDIS qgz INgz EA) as DE.
                       assert (D8 : forall A8 kk, abatch_addr L (qb_slot qgz) + 8 <= A8 -> A8 + kk <= abatch_addr L (qb_slot qgz) + 8192 -> 0 <= kk ->
                                  disjoint_from (Wf (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) A8 kk).
                       { intros A8 kk HA HK KK0. apply Kres; clear -F3 F4 RES RHI SQ DL DE EEB GLS ABUB S8 EUB HA HK KK0; lia. }
                       pose proof Y1 as Y1'. rw_split Y1' 1%nat YN YR.
                       eapply cells_frame in YR; [| exact MUn | exact WM | cbn [cells_size csize Nat.add]; apply D8; clear; lia].
                       rw_join GLN YR YH.
                       split; [exact YH|]. split; [| split; [| split; [exact Y4| split; [exact Y5| exact Y6]]]].
                       --- eapply u64arr_frame; [exact Y2 | exact MUn | exact WM |]. rewrite length_map, qhdrs_length by exact Y5. rewrite <- Y4.
                           apply D8; unfold Q_BATCH in Y6; clear -Y6; lia.
                       --- eapply junk_frame; [exact Y3 | exact MUn | exact WM |]. intros Hp. apply D8; unfold Q_BATCH, Q_BATCH_BYTES in *; clear -Y6 Hp; lia.
             ++ exact ABL'.
        * exact (qcoupled_drain L st2 st' X' (mkQConc (q_loc Q ++ [qn]) (q_glob Q) true pend) true CP2 QL3 QG3).
        * exact NUM'.
      + (* [comment removed for export] *)
        pose proof (NDR NDRN) as EST.
        assert (GD : g_drain g = false) by (rewrite GDR; apply Z.ltb_ge; rewrite <- QB2; exact NDRN).
        unfold tcache_post in QC'. rewrite GD in DKP', QC'.
        exists (mkQConc (q_loc Q ++ [qn]) (q_glob Q) true pend). unfold AQUAR_at. cbn [q_loc q_glob q_ia].
        rewrite EST, QL2, QG2, QB2, QGB2.
        split; [exact QK'|]. split; [| split; [| split; [exact IA'| split]]].
        * split; [| exact ABL'].
          rewrite length_app. cbn [length]. rewrite Nat2Z.inj_add. change (Z.of_nat 1) with 1. rewrite QLST'. exact QC'.
        * split; [rewrite <- GNB, <- GFST, <- GL, <- GQB; exact DKP'|].
          unfold abatches. eapply abatches_to_frame; [exact MUn | exact WM | exact ABG |].
          intros q Hq. assert (INq : In q (q_loc Q ++ q_glob Q)) by (apply in_or_app; right; exact Hq).
          apply BFR; [exact INq | exact (GNL q Hq) | rewrite EGL; unfold dk_glst; rewrite GD; exact (GNL q Hq)].
        * first [rewrite EST | idtac]. exact CP2.
        * first [rewrite <- EST | idtac]. exact NUM'. }
  idtac "CHECKPOINT-E".
  (* [comment removed for export] *)
  assert (HBK : forall blk, In blk LB -> disjoint_from (Wf (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) (ab_addr blk) (ab_size blk)).
  { intros [[q|cls] A' n'] Hin; cbn [ab_addr ab_size].
    - destruct (proj1 BL q A' n' Hin) as [(b & Hb & Sb & Ub & Nb)|(mb & msz & Lp & EUA & Gs)].
      + assert (NEq : xb_st b <> BQuar) by (rewrite Sb; discriminate).
        pose proof (other_key (AHQm DI ASEC AFK Q) L st X m BQuar c k n b1 ctx l1 l2 AR XB b Hb NEq) as NE1.
        destruct (busy_slot_range L st X b WF Hb) as [HCb HKb].
        pose proof (awf_fits L st X b WF Hb) as FIT. unfold xb_fits in FIT. rewrite Sb in FIT.
        pose proof (busy_of_In_nodup L st X b WF Hb) as BOF.
        unfold xb_user, xb_alloc in Ub. subst A' n'.
        set (cb := xb_class b) in *. set (kb := xb_slot b) in *.
        (pose proof (slot_geo L st X cb kb ALO WF HCb HKb) as ndP__; nd_pre ndP__ 12%nat; intros T16 TM16 TAL P1 P2 P3 P4 P5 P6 P7 P8 _; nd_post).
        pose proof (slots_sep_any L st X cb kb c k ALO WF HCb HC HKb KR ltac:(clear -NE1; lia)) as D9. rewrite <- EAB, <- ES in D9.
        assert (DQ : forall q', In q' (q_loc Q ++ q_glob Q) ->
            aslot_addr L cb kb + size_of_class cb <= abatch_addr L (qb_slot q') \/ abatch_addr L (qb_slot q') + 8192 <= aslot_addr L cb kb).
        { intros q' Hq'. (nd_pre (bslot_busy L st X Q CP q' Hq') 5%nat; intros yq Hyq Syq Cyq Kyq; nd_post).
          assert (NE : cb <> K_BATCH_CLASS \/ kb <> qb_slot q').
          { destruct (Z.eq_dec cb K_BATCH_CLASS) as [E1|NE0]; [| left; exact NE0]. right. intros E2.
            pose proof (busy_of_In_nodup L st X yq WF Hyq) as BY. rewrite Cyq, Kyq, <- E1, <- E2, BOF in BY. injection BY as EE. subst yq. rewrite Sb in Syq. discriminate. }
          pose proof (slots_sep_any L st X cb kb K_BATCH_CLASS (qb_slot q') ALO WF HCb (K24) HKb (bslot_range L st X Q WF CP q' Hq') NE) as D.
          rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
        assert (DK24 : enq_is_app st = false -> aslot_addr L cb kb + size_of_class cb <= abatch_addr L k24 \/ abatch_addr L k24 + 8192 <= aslot_addr L cb kb).
        { intros EA2. (nd_pre (NEWF EA2) 4%nat; intros _ NB KK _; nd_post).
          assert (NE : cb <> K_BATCH_CLASS \/ kb <> k24).
          { destruct (Z.eq_dec cb K_BATCH_CLASS) as [E1|NE0]; [| left; exact NE0]. right. intros E2. rewrite <- E1, <- E2, BOF in NB. discriminate. }
          pose proof (slots_sep_any L st X cb kb K_BATCH_CLASS k24 ALO WF HCb (K24) HKb KK NE) as D.
          rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
        assert (DL : lst = 0 \/ aslot_addr L cb kb + size_of_class cb <= lst \/ lst + 8192 <= aslot_addr L cb kb).
        { destruct LSTF as [Z0|((q' & Hq' & Eq') & _)]; [left; exact Z0| right]. rewrite Eq'. apply DQ. apply in_or_app; left; exact Hq'. }
        assert (DE : eb = lst \/ aslot_addr L cb kb + size_of_class cb <= eb \/ eb + 8192 <= aslot_addr L cb kb).
        { destruct EBK as [E|[EA2 E]]; [left; exact E| right]. rewrite E. exact (DK24 EA2). }
        assert (DG : gl = lst \/ gl = 0 \/ aslot_addr L cb kb + size_of_class cb <= gl \/ gl + 8192 <= aslot_addr L cb kb).
        { destruct GLF as [[_ E]|(_ & _ & [Z0|((q' & Hq' & Eq') & _)])]; [left; exact E| right; left; exact Z0| right; right].
          rewrite Eq'. apply DQ. apply in_or_app; right; exact Hq'. }
        apply Kres; [clear -P5 RSP FIT; lia | clear -P6 RSP FIT; unfold K_SPACE_SIZE in *; lia | clear -FIT; lia
                    | clear -D9 FIT ABUB S8 EUB; lia | clear -DL FIT P5 RSP RES RHI; lia | clear -DE DL FIT P5 RSP RES RHI; lia | clear -DG DL FIT P5 RSP RES RHI; lia].
      + (* [comment removed for export] *)
        cbn [sec_wf1] in Gs. (nd_pre Gs 7%nat; intros Gs1 Gs2 Gs3 Gs4 Gs5 Gs6 (Ct & Cc & Cr & Cp & Cn & Cs & Cf & Cd); nd_post).
        pose proof (sec_facts n' ltac:(clear -Gs5; lia) Gs6) as SF. subst A'. unfold SEC_UOFF, K_HIGH_MEM in *.
        unfold ablk, KLS, AIMG_HI in Gs2.   (* [comment removed for export] *)
        apply Kobj; clear -Gs2 Gs3 Gs4 Gs5 SF Ct Cr Cn Cs; lia.
    - (nd_pre (FKD cls A' n' Hin) 3%nat; intros K1 K2 K3; nd_post). atop_facts.
      pose proof D_t_f as DTF; unbox DTF. pose proof D_f_res as DFR; unbox DFR. pose proof D_n_f as DNF; unbox DNF. pose proof D_s_f as DSF; unbox DSF.
      apply Kobj; [clear -K1 K3 FKO FKi FBND; lia | clear -K3 FKO FKi FBND; lia | exact K2 | clear -K1 K3 DTF; lia
                  | clear -K1 K3 DFR; lia | clear -K1 K3 DNF; lia | clear -K1 K3 DSF; lia]. }
  assert (HFS : forall cls FA sz, In (mkABlock (ABFake cls) FA sz) LB -> forall a', FA <= a' < FA + sz ->
      disjoint_from (Wf (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) (shad a') 1).
  { intros cls FA sz Hin a' Ha'.
    (nd_pre (FKD cls FA sz Hin) 3%nat; intros K1 K2 K3; nd_post). atop_facts.
    apply Kshad; [rewrite shad_div; unfold ASHOFF; clear -K1 FKO FKi FBND Ha'; Z.div_mod_to_equations; lia
                 | rewrite shad_div; unfold ASHOFF; clear -K3 FKO FKi FBND Ha'; Z.div_mod_to_equations; lia | clear; lia |].
    pose proof D_f_res as DFR; unbox DFR. destruct DFR as [D|D].
    - left. rewrite (shad_div a'), (shad_div UB). clear -D Ha' K3 RSP G5 ABUB UB16'. Z.div_mod_to_equations. lia.
    - right. rewrite EGQ, shlen_div, (shad_div a'), (shad_div UB). unfold K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
      clear -D Ha' K1 RSP G6 UBS RUP8 UB16'. Z.div_mod_to_equations. lia. }
  (* [comment removed for export] *)
  assert (TLSK : forall TA tk, ATPv + -200 <= TA -> TA + tk <= ATPv + 312 -> 0 <= tk ->
      disjoint_from (Wf (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) TA tk).
  { intros TA tk TH1 TH2 TH3. pose proof ATPv_img as TI. apply Kimg; clear -TH1 TH2 TH3 TI; unfold AIMG_HI; lia. }
  assert (TLSS : forall a', ATPv + -200 <= a' < ATPv + 312 ->
      disjoint_from (Wf (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L) lst eb gl) (shad a') 1).
  { intros a' Ha'. pose proof ATPv_img as TI. apply Klow; clear -Ha' TI; try (rewrite shad_div; unfold ASHOFF); try Z.div_mod_to_equations; lia. }
  assert (PSP : shad UB + gq <= shad ATOP).
  { rewrite EGQ, shlen_div, (shad_div UB), (shad_div ATOP). atop_facts. clear -UBS G8 ABCE CEIL LO RUP8 UB16'. Z.div_mod_to_equations. lia. }
  (* [comment removed for export] *)
  exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
  split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split.
  { eapply (aheap_pres_free CI); [exact KF | exact CI_OK | exact MUn | exact WM | exact HBK | exact HFS | exact PSP | exact TLSK | exact TLSS | apply Klow; unfold AIMSH_LO, AIMSH_LEN; clear; lia
      | rewrite <- (ao_ahm_eq L ALO); unfold AAHM_SZ; pose proof (ao_ahm L ALO) as OAH; pose proof (aobj_img _ _ OAH ltac:(clear; lia)) as OAHI;
      pose proof (ad_ahm_t L ALO) as DA1; pose proof (ad_ahm_res L ALO) as DA2; pose proof (ad_ahm_nodes L ALO) as DA3; pose proof (ad_ahm_store L ALO) as DA4;
      unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI, adisj in OAH, OAHI, DA1, DA2, DA3, DA4; apply Kobj; clear -OAH OAHI DA1 DA2 DA3 DA4; lia]. }
  split; [exact ALO|]. split; [exact (arng_core L RNG st st' SC (sec_chunks_qperm st st' ELIVE (st_after_enq_qfilt is_sec st (CPrim c n) eq_refl)) ARNG)|]. split; [| exact HFK'].
  exists X'. split; [| exact BL'].
  split; [exact WF'|]. split; [exact RT'|]. split; [exact INST'|]. split; [exact THR'|]. split; [exact CLS'|].
  split; [exact HQ'|]. split; [exact HS'|]. split; [exact DEP'|]. split; [exact HRO'|]. split; [exact HRT2'|]. split; [exact AVL'| exact RT3'].
Qed.
End Zd1.
#[using="HL CI_OK"] Theorem store_freeR : ltac:(let t := eval cbv delta [store_freeR__stmt] in store_freeR__stmt in exact t).
Proof. exact store_freeR__body. Qed.

End S.
End CANSEC1.
End TwB.
End AFreeStoreR.
