(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF ITreeA StepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg AProto ABase ABytes AQConst AKitQ AMalloc_iface ADepot_iface ARep ARepQ ARepQP ALayout AHeapP ARepKit ARepFrame
     AKit AKit2 AModelFacts AFreeModel AFreeRep AFreeGeo AFreeRead F_apoison F_aalloc_s F_aalloc1 F_afree_tail F_afree_icpt.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
Lemma rw_cells_addr_eq : forall m A A' cs, rw_cells bsegs m A cs -> A = A' -> rw_cells bsegs m A' cs.
Proof. intros m A A' cs H <-. exact H. Qed.

Section S.
(* [comment removed for export] *)
Variable DI : ADepotIface.
Variables (ASEC : alayout -> astate -> aconc -> amem -> Prop) (AFK : alayout -> list ablock -> amem -> Prop).
Definition AHQ : aholes := mkAHoles AQUAR ASEC (ADEPOT DI) AFK.
Hypothesis HL : ahole_laws AHQ.
(* [comment removed for export] *)
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI
                                  /\ (snd iv <= 0xcc970 \/ 0xcca30 <= fst iv)
                                  /\ (snd iv <= 0xd0f00 \/ 0x151f30 <= fst iv)
                                  /\ (snd iv <= 0x15f788 \/ 0x15f78c <= fst iv)) CI.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition store_free_stmt : Prop :=
  forall (L : alayout) (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : amem) (st : astate) (LB : list ablock) (X : aconc) (Q : qconc) (p : aptr) (c k n b1 ctx A lo k24 : Z)
         (l1 l2 : list xbusy) (stj : word) (chunks : list word),
  let ch := CPrim c n in
  let st1 := set_live (delete p (a_live st)) st in
  let st2 := st_enq st1 ch in
  let ek := ek_of L st X Q n k24 stj chunks in
  let g := g_of L st Q (ek_delta ek n) in
  alayout_ok L -> arng L RNG st -> AREP AHQ L st X m -> AQUAR_at L st X Q m -> ablocks L st X LB -> AFK L LB m ->
  x_busy X = l1 ++ bfreed p c k n b1 ctx :: l2 -> In (HB p A n) LB -> 1 <= n ->
  (enq_is_app st = false ->
        nth_error (xc_cache (x_cls X K_BATCH_CLASS)) (Z.to_nat (c_count (get_cls st K_BATCH_CLASS) - 1)) = Some k24
     /\ busy_of X K_BATCH_CLASS k24 = None /\ 0 <= k24 < ndist st K_BATCH_CLASS
     /\ ~ In k24 (map qb_slot (q_loc Q ++ q_glob Q))
     /\ junk_at m (abatch_addr L k24) 8192 /\ fill_at m (shad (abatch_addr L k24)) (shlen 8192) 0xfa
     /\ a_cinit st = true /\ 0 < c_count (get_cls st K_BATCH_CLASS)) ->
  (Q_CACHE < a_qloc_bytes st2 -> a_qglob_bytes st2 + a_qloc_bytes st2 <= Q_MAX) ->
  ek_pre ek RNG (al_t L) (Z.of_nat (length (a_qloc st))) (qlast L (q_loc Q)) n (fhm L c k n) m ->
  dk_pre ek g RNG (al_t L) (qlast L (q_loc Q)) (fhm L c k n) (a_qloc_bytes st + ek_delta ek n) m ->
  ATOP <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
  forall ms',
    free_fast_post DI L ek g ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (al_t L) (fhm L c k n) n
                   (Z.of_nat (length (a_qloc st))) (qfirst L (q_loc Q)) (qlast L (q_loc Q)) (a_qloc_bytes st) b1 ctx lo m ms' ->
    afree_post CI (AHEAP_P AHQ) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB p lo m (st_after st2) RNG ms'.
Hypothesis STORE : store_free_stmt.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem afree_fast : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (p : aptr) (A n lo : Z) (tr : list Z) (c : Z),
  (* [comment removed for export] *)
  (a_live st) !! p = Some (CPrim c n) -> 1 <= n ->
  let st1 := set_live (delete p (a_live st)) st in
  let st2 := st_enq st1 (CPrim c n) in
  (enq_app st1 (CPrim c n) = None -> 0 < c_count (get_cls st K_BATCH_CLASS)) ->
  (Q_CACHE < a_qloc_bytes st2 -> a_qglob_bytes st2 + a_qloc_bytes st2 <= Q_MAX) ->
  (* [comment removed for export] *)
  AHEAP_P AHQ L RNG st LB m -> In (HB p A n) LB ->
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 A ->
  aunw m L RNG lo AFREE_PC sp s0 ra tr ->
  bv_unsigned s0 <> bv_unsigned sp + 8 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AFREE_PC ->
  bv_unsigned sp mod 16 = 0 ->
  rng RNG lo (bv_unsigned sp - lo) ->
  implS bsegs RNG (aembed ATOP (afree st (Some p)))
        (epostF (afree_post CI (AHEAP_P AHQ) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB p lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AFREE_SYM) fc None m (seg_rom bsegs)).
Proof.
  intros until c. intros LIVE N1 st1 st2 CNT NOREC AH HIN MI ST BOT LO TP Ha0 AUNW S0NE RA4 RANE SP16 RSTK.
  assert (UNWX : exists trt, afree_unw RNG lo m (al_top L) sp s0 ra trt /\ In (AFREE_PC :: trt) (al_U L)).
  { destruct AUNW as [(BT & UC & LTR & TRU & RTOP)|(TOPLE & SPLT & TRU)]; [exists (bv_unsigned ra :: tr); split; [left; exists tr; split; [reflexivity|]; split; [exact UC|]; split; [exact LTR|]; split; [exact BT| exact RTOP]| exact TRU] | exists (@nil Z); split; [right; auto| exact TRU]]. }
  destruct UNWX as (trt & FUNW & TRU).
  destruct AH as (ALO & ARNG & [X [AR BL]] & HFK).
  pose proof AR as AR0. destruct AR0 as (WF & RT & INST & THR & CLS & HQ & HS & HD & HRO & HRT2 & AVL & RT3).
  cbn [ah_quar ah_sec ah_depot AHQ] in HQ, HS, HD. destruct HQ as [Q AQ].
  (* [comment removed for export] *)
  pose proof BL as BL0. destruct BL0 as (BH & _).
  pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVEB & FRESH & UNIQ).
  destruct (BH p A n HIN) as [(y & Hy & Sy & Uy & Ny)|(mb & msz & Lp & _)]; [| exfalso; rewrite LIVE in Lp; discriminate].
  destruct (BUSY y Hy) as [CLy My]. rewrite Sy in My. destruct My as (_ & _ & _ & _ & _ & M5). rewrite LIVE in M5.
  injection M5 as Cy Ny'. clear Ny'.
  destruct (in_split _ _ Hy) as (l1 & l2 & XB).
  destruct y as [yc yk yn yst yb1 yctx]. cbn in Sy, Uy, Ny, Cy, CLy. subst yst yn yc.
  rename yk into k. rename yb1 into b1. rename yctx into ctx.
  change ({| xb_class := c; xb_slot := k; xb_n := n; xb_st := BLive p; xb_b1 := b1; xb_ctx := ctx |}) with (bfreed p c k n b1 ctx) in XB.
  unfold xb_user, xb_alloc in Uy. cbn [xb_class xb_slot xb_n] in Uy.
  (* [comment removed for export] *)
  destruct (freed_range L st X p c k n b1 ctx l1 l2 WF XB) as [HC KR].
  pose proof (freed_live L st X p c k n b1 ctx l1 l2 XB WF) as (_ & N0 & FIT0 & B10 & AT0 & CTX0).
  pose proof (chunk_geo L st X c k n ALO WF HC KR (proj1 N0) FIT0) as (HM16 & UB16 & ABUB & ABHM & HLO & UBS & ABCE & HHI & N65 & NQM & ABLO & RUP & RUP8 & S8).
  pose proof (slot_sep_objects L st X c k ALO WF HC KR) as (DT & DC & DN & DSO & DF).
  destruct (slot_rng L st X c k ALO WF HC KR RNG ARNG) as [RSL RSS].
  pose proof ARNG as ARNG0. destruct ARNG0 as (RIMG & RT4 & RCTX & RNO & RSTO & RRI & RFK & RSFK & RDT & RCLS & RPA & RSECS & RPSH).
  pose proof (chunk_shadow_geo L st X c k n ALO WF HC KR (proj1 N0) FIT0) as (SE & G2 & GE & G0 & GFS & SHLO & SHHI & _).
  pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4).
  pose proof (alayout_ctx L ALO) as (CL1 & CL2 & CL3 & CL4 & CL5).
  pose proof (alayout_depot L ALO) as (DL1 & DL2 & DL3 & DL4 & DL5 & DL6 & DL7 & DL8 & DL9 & DL10).
  pose proof (alayout_stack L ALO) as (STK1 & STK2 & STK3).
  assert (SP47 : bv_unsigned sp < 2^47) by (eapply afree_unw_sp47; [exact FUNW| exact STK2]).
  set (AB := aslot_addr L c k) in *. set (UB := AB + rz_size n) in *.
  assert (EHM : fhm L c k n = UB - 16) by (unfold fhm; subst AB UB; lia).
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
  destruct (CACHES K_BATCH_CLASS (K24)) as [tail (CR & CH & LCH)].
  replace (acache_addr L K_BATCH_CLASS) with (al_t L + 2128) in CR by (unfold acache_addr, K_BATCH_CLASS; lia).
  destruct (junk_split m (al_t L + 2768) 16 16 CSTATS ltac:(lia) ltac:(lia)) as [CSa CSb].
  destruct (junk_split m (al_t L + 2768 + 16) 8 8 CSb ltac:(lia) ltac:(lia)) as [CS8 CSc].
  replace (al_t L + 2768 + 16) with (al_t L + 2784) in CS8 by lia.
  destruct (c8_of_junk m _ CS8) as [stj STS].
  (* [comment removed for export] *)
  destruct (read_chunk L st X m p c k n b1 ctx l1 l2 ALO WF XB (conj (proj1 (proj2 (proj2 (CLS c HC)))) (proj2 (proj2 (proj2 (CLS c HC))))))
    as (HDR & [uw HUW] & UJR & LH & SHA & SHU & SHR).
  fold AB in HDR, HUW, UJR, LH, SHA, SHU, SHR. fold UB in HDR, HUW, UJR, LH, SHU, SHR.
  (* [comment removed for export] *)
  pose proof AQ as AQ0. destruct AQ0 as ([QK MX] & [QC ABL] & [GCQ ABG] & (FL & IAS & IAM) & CP & NUM).
  destruct NUM as (NB1 & NB2 & NF & NC & NM).
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
    - destruct (read_ek_app AHQ L st X Q m RNG (BLive p) c k n b1 ctx l1 l2 ALO ARNG AR AQ XB ltac:(discriminate) stj [] 0 EA
                (Z_to_bv 64 0) (Z_to_bv 64 0) 0 CR STS) as (EK & ES & ED & EB & _).
      specialize (SB 0 stj [] ltac:(intros E; exfalso; change (enq_app st1 (CPrim c n) = None) in E; assert (EA1 : enq_is_app st1 = true) by exact EA;
                    destruct (proj1 (enq_is_app_spec st1 (CPrim c n)) EA1) as [s Hs]; congruence)).
      cbn [chunk_size] in SB. destruct SB as (SB1 & SB2 & _).
      exists 0, []. cbv zeta. split; [exact EK|]. split; [exact ES|]. split; [rewrite ED; lia|]. split; [exact SB1|]. split; [exact SB2|].
      split; [left; exact EB|]. intros; discriminate.
    - assert (POS : 0 < c_count (get_cls st K_BATCH_CLASS)).
      { apply CNT. destruct (enq_app st1 (CPrim c n)) eqn:E; [| reflexivity]. exfalso.
        assert (EA1 : enq_is_app st1 = true) by (apply (proj2 (enq_is_app_spec st1 (CPrim c n))); eexists; exact E).
        change (enq_is_app st1) with (enq_is_app st) in EA1. congruence. }
      destruct (read_ek_new AHQ L st X Q m RNG (BLive p) c k n b1 ctx l1 l2 ALO ARNG AR AQ XB ltac:(discriminate) stj EA POS STS)
        as (k24 & chunks & EK & ES & ED & EB & NK & NB & KK & NIB & JK & FSH & CIN & _).
      specialize (SB k24 stj chunks ltac:(intros _; exact POS)). cbn [chunk_size] in SB. destruct SB as (SB1 & SB2 & _).
      exists k24, chunks. cbv zeta. split; [exact EK|]. split; [exact ES|]. split; [rewrite ED; lia|]. split; [exact SB1|]. split; [exact SB2|].
      split; [right; exists k24; split; [exact EB|]; split; [exact KK| exact NIB]|].
      intros _. repeat (split; [assumption|]). exact POS. }
  destruct EKX as (k24 & chunks & EKX). cbv zeta in EKX. destruct EKX as (EK & ES & ED0 & SB1 & SB2 & EBB & NEWF).
  set (ek := ek_of L st X Q n k24 stj chunks) in *.
  (* [comment removed for export] *)
  destruct (read_dk AHQ L st X Q m RNG (BLive p) c k n b1 ctx l1 l2 ALO ARNG AR AQ XB ltac:(discriminate) (ek_b ek (qlast L (q_loc Q))) (ek_delta ek n) ek ED0 EBB
              ltac:(rewrite <- SB1, <- SB2; exact NOREC) eq_refl) as (DK & DS & GL & GLST).
  set (g := g_of L st Q (ek_delta ek n)) in *.
  (* [comment removed for export] *)
  rewrite (afree_fast_eq st p (CPrim c n) LIVE ltac:(cbn [chunk_size]; exact NQM) CNT NOREC).
  apply implS_ret.
  (* [comment removed for export] *)
  assert (AB64 : forall q, In q (q_loc Q ++ q_glob Q) -> 0 <= abatch_addr L (qb_slot q) < 2^64).
  { intros q Hq. pose proof (bslot_geo L st X ALO WF (qb_slot q) (bslot_range L st X Q WF CP q Hq)) as (B0 & B1 & _). atop_facts. lia. }
  assert (LF64 : 0 <= qfirst L (q_loc Q) < 2^64).
  { destruct (qfirst_cases L (q_loc Q)) as [-> |(q & Hq & ->)]; [lia| apply AB64; apply in_or_app; left; exact Hq]. }
  assert (LL64 : 0 <= qlast L (q_loc Q) < 2^64).
  { destruct (qlast_cases L (q_loc Q)) as [-> |(q & Hq & ->)]; [lia| apply AB64; apply in_or_app; left; exact Hq]. }
  assert (DELTA : ek_delta ek n <= n + 8192) by (subst ek; unfold ek_of; destruct (enq_is_app st); cbn [ek_delta]; lia).
  (* [comment removed for export] *)
  unfold AIMG_HI, AFREE_STACK, UDEPTH, Q_MAX, Q_CACHE in *.
  box DT. box DC. box DN. box DSO. box DF. box CL5. box DL7. box DL8. box DL9. box DL10.
  eapply evtF_mono.
  { eapply (free_fast_spec DI L (q_ia Q) ek g RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m
              (al_t L) (al_ctx L) (fhm L c k n) n b1 ctx lo (al_top L) (al_bot L)
              (Z.of_nat (length (a_qloc st))) (qfirst L (q_loc Q)) (qlast L (q_loc Q)) (a_qloc_bytes st) uw sj (block_shadow_bytes n) trt).
    all: rewrite ?EHM.
    all: try lazymatch goal with
         | |- stk _ _ _ _ => first [exact ST | exact IAS]
         | |- ablk _ (_ + 16 + rup _ 8) => first [assumption | unfold ablk; right; generalize HLO HHI; try generalize EHM; clear; unfold fhm; intros; lia]   (* [comment removed for export] *)
         | |- mem_inv _ _ => exact MI
         | |- allocA_cells _ _ _ => unfold allocA_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
         | |- poison_cells _ => unfold poison_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
         | |- ADEPOT _ _ _ => exact HD
         | |- afree_unw _ _ _ _ _ _ => exact FUNW
         | |- In _ _ => exact TRU
         | |- u64arr _ _ _ _ => exact STATS
         | |- ek_pre _ _ _ _ _ _ _ _ => exact EK
         | |- ek_seps _ _ _ _ => exact ES
         | |- dk_pre _ _ _ _ _ _ _ _ => exact DK
         | |- dk_seps _ _ _ => exact DS
         | |- _ = true -> _ => exact IAM
         | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact HDR
         | |- rw_cells _ _ (shad _) _ => eapply rw_cells_addr_eq; [exact SHU| f_equal; lia]
         | |- rw_cells _ _ (_ + 80) _ => exact QC
         | |- rw_cells _ _ (_ - 16 + 16) [C8 _] => eapply rw_cells_addr_eq; [exact HUW| lia]
         end.
    all: try lazymatch goal with
         | |- rw_cells _ _ _ [C8 _; C8 _; C8 _] => first [exact T0 | exact QK]
         | |- rw_cells _ _ _ _ => assumption
         | |- @eq word _ _ => first [exact TP | rewrite Ha0, <- Uy; subst AB UB; apply Z_to_bv_eqm; first [(generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LL64 ED0 DELTA RA4; clear; intros; lia) | lia] | reflexivity]   (* [comment removed for export] *)
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
