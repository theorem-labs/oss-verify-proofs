(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* reloc14 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import ExecF ITreeA StepF.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_agrees_alloc_forced_only.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_agrees_alloc_forced_only.AsanW Require Import AImg AProto ABase ABytes AQConst AKitQ AMalloc_iface ADepot_iface ARep ARepQ ARepQP ALayout AHeapP
     AFreeGeo AFreeModel AFreeModelR AFreeModelC AFreeRep AFreeRead ARefill_iface ARefillP ASec F_afree_arep F_afree_arepR AFreeMid AFreeRefillP
     ASF_kit ASF_refill ASF_mid ASF_all.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Section S.
Variable DI : ADepotIface.
Variable AFK : alayout -> list ablock -> amem -> Prop.
Hypothesis HL : ahole_laws (AHQ DI ASEC_of AFK).
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI
                                  /\ (snd iv <= 0x9e670 \/ 0x9e730 <= fst iv)
                                  /\ (snd iv <= 0xa2c00 \/ 0x123c30 <= fst iv)
                                  /\ (snd iv <= 0x131488 \/ 0x13148c <= fst iv)) CI.
Hypothesis CI_OK2 : Forall (fun iv => snd iv <= AINSTANCE \/ AINSTANCE + 728 <= fst iv) CI.

Lemma prim_live_small : forall L RNG st LB m p A n c,
  AHEAP_P (AHQ DI ASEC_of AFK) L RNG st LB m -> In (HB p A n) LB -> (a_live st) !! p = Some (CPrim c n) -> n <= Q_MAX.
Proof.
  intros L RNG st LB m p A n c AH HIN LIVE.
  destruct AH as (ALO & ARNG & [X [AR BL]] & HFK).
  destruct AR as (WF & _).
  destruct BL as (BH & _).
  pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVEB & FRESH & UNIQ).
  destruct (BH p A n HIN) as [(y & Hy & Sy & Uy & Ny)|(mb & msz & Lp & _)]; [| exfalso; rewrite LIVE in Lp; discriminate].
  destruct (BUSY y Hy) as [CLy My]. rewrite Sy in My. destruct My as (_ & _ & _ & _ & _ & M5). rewrite LIVE in M5.
  injection M5 as Cy Ny'. clear Ny'.
  destruct (in_split _ _ Hy) as (l1 & l2 & XB).
  destruct y as [yc yk yn yst yb1 yctx]. cbn in Sy, Uy, Ny, Cy, CLy. subst yst yn yc.
  change ({| xb_class := c; xb_slot := yk; xb_n := n; xb_st := BLive p; xb_b1 := yb1; xb_ctx := yctx |}) with (bfreed p c yk n yb1 yctx) in XB.
  destruct (freed_range L st X p c yk n yb1 yctx l1 l2 WF XB) as [HC KR].
  pose proof (freed_live L st X p c yk n yb1 yctx l1 l2 XB WF) as (_ & N0 & FIT0 & _).
  pose proof (chunk_geo L st X c yk n ALO WF HC KR (proj1 N0) FIT0) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & NQM & _).
  exact NQM.
Qed.

Lemma REFILLP : forall Q1, refill_stmt (AHQm DI ASEC_of AFK Q1).
Proof. intros Q1. exact (arefillP (AHQm DI ASEC_of AFK Q1) (AHQm_laws DI ASEC_of AFK HL Q1)). Qed.

Lemma enq_new_sizes : forall (st : astate) (p : aptr) (ch : achunk), enq_is_app st = false ->
  let st1 := set_live (delete p (a_live st)) st in
  a_qloc_bytes (st_enq st1 ch) = a_qloc_bytes st + chunk_size ch + Q_BATCH_BYTES /\ a_qglob_bytes (st_enq st1 ch) = a_qglob_bytes st.
Proof.
  intros st p ch EA st1.
  assert (EAPP : enq_app st1 ch = None).
  { destruct (enq_app st1 ch) as [s'|] eqn:E; [exfalso| reflexivity].
    assert (EA1 : enq_is_app st1 = true) by (apply (proj2 (enq_is_app_spec _ ch)); eexists; exact E).
    change (enq_is_app st1) with (enq_is_app st) in EA1. congruence. }
  unfold st_enq. rewrite EAPP.
  pose proof (enq_new_core ch st1) as (_ & G1 & G2 & _ & _ & L2 & _). rewrite G2, L2. split; reflexivity.
Qed.

Theorem afree_prim_total : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (p : aptr) (A n lo : Z) (tr : list Z) (c : Z),
  (a_live st) !! p = Some (CPrim c n) -> 1 <= n ->
  AHEAP_P (AHQ DI ASEC_of AFK) L RNG st LB m -> In (HB p A n) LB ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 A ->
  aunw m L RNG lo AFREE_PC sp s0 ra tr ->
  bv_unsigned s0 <> bv_unsigned sp + 8 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AFREE_PC ->
  bv_unsigned sp mod 16 = 0 ->
  rng RNG lo (bv_unsigned sp - lo) ->
  implS asegs RNG (aembed ATOP (afree st (Some p)))
        (epostF (afree_post CI (AHEAP_P (AHQ DI ASEC_of AFK)) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB p lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AFREE_SYM) fc None m (seg_rom asegs)).
Proof.
  intros until c. intros LIVE N1. intros.
  pose proof (prim_live_small _ _ _ _ _ _ _ _ _ H H0 LIVE) as NQM.
  set (st1 := set_live (delete p (a_live st)) st).
  set (st2 := st_enq st1 (CPrim c n)).
  destruct (Z.lt_ge_cases Q_CACHE (a_qloc_bytes st2)) as [QC1|QC0];
    [destruct (Z.lt_ge_cases Q_MAX (a_qglob_bytes st2 + a_qloc_bytes st2)) as [REC|NR]|].
  -
    destruct (Z.lt_ge_cases 0 (c_count (get_cls st K_BATCH_CLASS))) as [POS|Z0].
    + rewrite (afree_rec_eq st p (CPrim c n) LIVE ltac:(cbn [chunk_size]; exact NQM) (fun _ => POS) QC1 REC), aembed_aundef_. apply implF_ret_unr.
    + destruct (enq_is_app st) eqn:EA.
      * assert (CNT : enq_app st1 (CPrim c n) = None -> 0 < c_count (get_cls st1 K_BATCH_CLASS)).
        { intros E. exfalso. assert (EA1 : enq_is_app st1 = true) by exact EA.
          destruct (proj1 (enq_is_app_spec st1 (CPrim c n)) EA1) as [s Hs]. congruence. }
        rewrite (afree_rec_eq st p (CPrim c n) LIVE ltac:(cbn [chunk_size]; exact NQM) CNT QC1 REC), aembed_aundef_. apply implF_ret_unr.
      * assert (CNT0 : c_count (get_cls st K_BATCH_CLASS) = 0).
        { pose proof H as AH. destruct AH as (_ & _ & [X [AR _]] & _). destruct AR as (WF & _).
          destruct WF as (_ & _ & _ & _ & _ & PERC & _). destruct (PERC K_BATCH_CLASS (K24)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CNTB & _). lia. }
        destruct (enq_new_sizes st p (CPrim c n) EA) as [EL EG]. cbv zeta in EL, EG. cbn [chunk_size] in EL. unfold Q_BATCH_BYTES in EL.
        unfold st2, st1 in QC1, REC. rewrite EL in QC1. rewrite EL, EG in REC.
        eapply (afree_rec_refill DI ASEC_of AFK CI (mid_kit DI ASEC_of AFK HL CI CI_OK) REFILLP); try eassumption.
        -- generalize QC1; clear; intros; lia.
        -- generalize REC; clear; intros; lia.
  -
    eapply (afree_norecycle DI ASEC_of AFK HL CI CI_OK CI_OK2); try eassumption. intros _. exact NR.
  -
    eapply (afree_norecycle DI ASEC_of AFK HL CI CI_OK CI_OK2); try eassumption. intros LT. exfalso. subst st2 st1. lia.
Qed.

Theorem afree_sec_total : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (p : aptr) (A n lo : Z) (tr : list Z) (mb ms : Z),
  (a_live st) !! p = Some (CSec mb ms n) ->
  AHEAP_P (AHQ DI ASEC_of AFK) L RNG st LB m -> In (HB p A n) LB ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 A ->
  aunw m L RNG lo AFREE_PC sp s0 ra tr ->
  bv_unsigned s0 <> bv_unsigned sp + 8 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AFREE_PC ->
  bv_unsigned sp mod 16 = 0 ->
  rng RNG lo (bv_unsigned sp - lo) ->
  implS asegs RNG (aembed ATOP (afree st (Some p)))
        (epostF (afree_post CI (AHEAP_P (AHQ DI ASEC_of AFK)) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB p lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AFREE_SYM) fc None m (seg_rom asegs)).
Proof.
  intros until ms. intros LIVE. intros.
  destruct (Z.le_gt_cases n Q_MAX) as [NQM|GT].
  2: {
       destruct (afree_big_eq st p (CSec mb ms n) LIVE ltac:(cbn [chunk_size]; lia)) as [k0 EQ]. rewrite EQ, aembed_aundef_. apply implF_ret_unr. }
  set (st1 := set_live (delete p (a_live st)) st).
  set (st2 := st_enq st1 (CSec mb ms n)).
  destruct (Z.lt_ge_cases Q_CACHE (a_qloc_bytes st2)) as [QC1|QC0];
    [destruct (Z.lt_ge_cases Q_MAX (a_qglob_bytes st2 + a_qloc_bytes st2)) as [REC|NR]|].
  - destruct (Z.lt_ge_cases 0 (c_count (get_cls st K_BATCH_CLASS))) as [POS|Z0].
    + rewrite (afree_rec_eq st p (CSec mb ms n) LIVE ltac:(cbn [chunk_size]; exact NQM) (fun _ => POS) QC1 REC), aembed_aundef_. apply implF_ret_unr.
    + destruct (enq_is_app st) eqn:EA.
      * assert (CNT : enq_app st1 (CSec mb ms n) = None -> 0 < c_count (get_cls st1 K_BATCH_CLASS)).
        { intros E. exfalso. assert (EA1 : enq_is_app st1 = true) by exact EA.
          destruct (proj1 (enq_is_app_spec st1 (CSec mb ms n)) EA1) as [s Hs]. congruence. }
        rewrite (afree_rec_eq st p (CSec mb ms n) LIVE ltac:(cbn [chunk_size]; exact NQM) CNT QC1 REC), aembed_aundef_. apply implF_ret_unr.
      * assert (CNT0 : c_count (get_cls st K_BATCH_CLASS) = 0).
        { pose proof H as AH. destruct AH as (_ & _ & [X [AR _]] & _). destruct AR as (WF & _).
          destruct WF as (_ & _ & _ & _ & _ & PERC & _). destruct (PERC K_BATCH_CLASS (K24)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CNTB & _). lia. }
        destruct (enq_new_sizes st p (CSec mb ms n) EA) as [EL EG]. cbv zeta in EL, EG. cbn [chunk_size] in EL. unfold Q_BATCH_BYTES in EL.
        unfold st2, st1 in QC1, REC. rewrite EL in QC1. rewrite EL, EG in REC.
        eapply (afree_sec_rec_refill DI AFK CI (mid_kitS DI AFK HL CI CI_OK) (REFILLS DI AFK HL)); try eassumption.
        -- generalize QC1; clear; intros; lia.
        -- generalize REC; clear; intros; lia.
  - eapply (afree_sec_norecycle DI AFK HL CI CI_OK CI_OK2); try eassumption. intros _. exact NR.
  - eapply (afree_sec_norecycle DI AFK HL CI CI_OK CI_OK2); try eassumption. intros LT. exfalso. subst st2 st1. lia.
Qed.

Theorem afree_total : afree_stmt CI (AHEAP_P (AHQ DI ASEC_of AFK)).
Proof.
  unfold afree_stmt. intros until tr. intros AH HIN. intros.
  pose proof AH as AH0. destruct AH0 as (ALO & ARNG & [X [AR BL]] & HFK).
  destruct (proj1 BL p A n HIN) as [(b & Hb & Sb & Ub & Nb)|(mb & ms & Lp & _)].
  - pose proof AR as AR0. destruct AR0 as (WF & _). pose proof WF as WF0. destruct WF0 as (_ & _ & _ & _ & _ & _ & _ & BUSY & _).
    destruct (BUSY b Hb) as [CLb M]. rewrite Sb in M. destruct M as (Nb1 & _ & _ & _ & _ & LIVE). rewrite Nb in Nb1, LIVE.
    eapply afree_prim_total with (c := xb_class b); try eassumption. lia.
  - eapply afree_sec_total; eassumption.
Qed.
End S.
End CANSEC1.
