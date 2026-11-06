(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr Tac Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Ledger Hull Restrict EvtAcct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt_u2d ARt_3ti ARt_fpo ARt_png.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt_u2d.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt_u2d OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt_3ti OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt_fpo OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt_png OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt_u2d.ARt_srv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt_u2d.ARt_a0k.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import AMalq4j AMalghy.   (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState ADepotM.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic ARtStmts ARtS4t2 AMTac AMallocA AMallocH AMalmys AMal9l1 AMalgue AMaly5g AMal93m AMaldga AMalkbe AMal8cv AMalzuh AMallbq.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AMallbq.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ASecZ ACor4x6.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtS4t2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMallocA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMallocH OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMalmys OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMal9l1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMalgue OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMaly5g OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMal93m OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMaldga OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMalkbe OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMal8cv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMalzuh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMallbq OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMallbq.AMaljju OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ASecZ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ACor4x6.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma natz_len_range : forall (A : Type) (l : list A) (a b : nat) (za zb : Z),
  Z.of_nat a = za -> Z.of_nat b = zb -> (a <= length l <= b)%nat -> (za <= Z.of_nat (length l) <= zb)%Z.
Proof. intros A l a b za zb <- <- H. split; apply Nat2Z.inj_le; apply H. Qed.
Lemma natz_len_le : forall (A : Type) (l : list A) (b : nat) (zb : Z), Z.of_nat b = zb -> (length l <= b)%nat -> (Z.of_nat (length l) <= zb)%Z.
Proof. intros A l b zb <- H. apply Nat2Z.inj_le; exact H. Qed.
Local Ltac natz_pos_lit p := lazymatch p with xH => idtac | xO ?q => natz_pos_lit q | xI ?q => natz_pos_lit q end.
Local Ltac natz_z_lit z := lazymatch z with Z0 => idtac | Zpos ?p => natz_pos_lit p end.   (* [comment removed for export] *)
Local Ltac natz_kl :=
  repeat match goal with
  | H : (?a <= @length ?A ?l <= ?b)%nat |- _ =>
      let za := eval vm_compute in (Z.of_nat a) in let zb := eval vm_compute in (Z.of_nat b) in
      natz_z_lit za; natz_z_lit zb;
      let Hz := fresh "KLz" in
      pose proof (natz_len_range A l a b za zb (@eq_refl Z za) (@eq_refl Z zb) H) as Hz; clear H
  | H : (@length ?A ?l <= ?b)%nat |- _ =>
      let zb := eval vm_compute in (Z.of_nat b) in
      natz_z_lit zb;
      let Hz := fresh "KLz" in
      pose proof (natz_len_le A l b zb (@eq_refl Z zb) H) as Hz; clear H
  end.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Zifyk6b.   (* [comment removed for export] *)
Local Ltac Zify.zify_pre_hook ::= natz_kl; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Zifyk6b.zon_hook.
(* [comment removed for export] *)

Notation wz z := (Z_to_bv 64 z) (only parsing).
Ltac kung_all := unfold kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes, kShadowOffset, kRegionSize, kSpaceSize, kFreeArrayOffset,
                        kHighShadowMapBeg, kSpaceReserve, kMaxSize in *.

(* [comment removed for export] *)
Section BridgeRC.
Context {Clg : Ceiling}.
  Hypothesis RZL : rzlog_stmt.
  Hypothesis GT : get_thread_stmt.
  Hypothesis TSS : thread_stats_stmt.
  Hypothesis PS : poison_stmt.
  Hypothesis DPS : depot_put_stmt depot_repL.
  Hypothesis BLK : classid_blk_stmt.
  Hypothesis BLK2 : classid_blk2_stmt.

  #[using="BLK2 BLK DPS PS TSS GT RZL"] Theorem alloc_refill_c :
    forall (rac spa gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (md : Model) (A : AState) (n canfill stkobj lo hi : Z) (key : list Z) (T : TSet),
      alloc_core_pre rac spa tp m md A n canfill stkobj lo hi key ->
      (* [comment removed for export] *)
      n <= kMaxPrimaryUser -> a_cache_inited A = true -> pk_chunks (a_cache A (class_of n)) = [] ->
      refill_count (class_of n) <= Z.of_nat (length (rg_free (a_reg A (class_of n)))) ->
      alloc_core_K1v rac spa gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md A n canfill lo hi T ->
      srealizes (cl_segs LPA) (mkCfg (alloc_entry_ms rac spa gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n stkobj canfill) md) T.
  Proof.
    intros until T. intros PRE NP CI EMP ENOUGH K1.
    (first [ dand25 PRE as AI MI NRQ NCAP LIM NLV TINY SCRED PCRED CF TPE CLO LOSA SAHI HI47 SPA RAC2 ST SM SOLO SOHI TRC TRB KEYU KR | destruct PRE as (AI & MI & NRQ & NCAP & LIM & NLV & TINY & SCRED & PCRED & CF & TPE & CLO & LOSA & SAHI & HI47 & SPA & RAC2 & ST & SM & SOLO & SOHI & TRC & TRB & KEYU & KR) ]).   (* [comment removed for export] *)
    subst tp. unfold alloc_entry_ms. cbn [cl_segs cl_malloc_pc LPA] in MI, K1 |- *.
    assert (NR : 1 <= n <= kMaxPrimaryUser) by (clear - NRQ NP; lia).
    pose proof (ai_wf _ _ _ _ _ _ _ AI) as WF0.
    pose proof alloc_ceiling_val as CE. pose proof (zr_word spa) as SPR; unfold inr64 in SPR. pose proof (zr_word rac) as RAR; unfold inr64 in RAR.
    (first [ pose proof ((ref_kidx A m md n AI NR ENOUGH)) as dR_2; dand4 dR_2 as KIN KB KNE FNE | pose proof (ref_kidx A m md n AI NR ENOUGH) as (KIN & KB & KNE & FNE) ]).
    set (fr := rg_free (a_reg A (class_of n))) in *.
    set (kidx := refK A n).
    assert (KID : kidx = nth (length fr - 1) fr 0) by reflexivity.
    rewrite <- KID in KIN, KB.
    (first [ pose proof ((hit_class n NR)) as dR_3; dand5 dR_3 as CR HC FIT CSR CM32 | pose proof (hit_class n NR) as (CR & HC & FIT & CSR & CM32) ]).
    (first [ pose proof ((ref_k A n NR)) as dR_4; dand4 dR_4 as MK2 KR2 KS MR | pose proof (ref_k A n NR) as (MK2 & KR2 & KS & MR) ]).
    (first [ pose proof ((free_geom A m md n kidx AI NR KIN)) as dR_5; dand16 dR_5 as ABE ABA ABQ ABR1 ABR2 RZ8 SB1 SB2 RB1 RB2 FIT2 _ _ _ KWR ABU | pose proof (free_geom A m md n kidx AI NR KIN) as (ABE & ABA & ABQ & ABR1 & ABR2 & RZ8 & SB1 & SB2 & RB1 & RB2 & FIT2 & _ & _ & _ & KWR & ABU) ]).
    (first [ pose proof ((hit_place A m md AI)) as dR_6; dand7 dR_6 as TH1 TH2 THRA CT1 CT2 TOPR BOTR | pose proof (hit_place A m md AI) as (TH1 & TH2 & THRA & CT1 & CT2 & TOPR & BOTR) ]).
    (first [ pose proof ((hit_sep A m md AI)) as dR_7; dand13 dR_7 as SEP_thr SEP_ctx SEP_tc SEP_n0 SEP_f0 SEP_n0t SEP_f0t SEP_n0c SEP_f0c DN01 DN02 DF01 DF02 | pose proof (hit_sep A m md AI) as (SEP_thr & SEP_ctx & SEP_tc & SEP_n0 & SEP_f0 & SEP_n0t & SEP_f0t & SEP_n0c & SEP_f0c & DN01 & DN02 & DF01 & DF02) ]).
    (first [ pose proof ((ref_sep A m md n AI)) as dR_8; dand5 dR_8 as SEP_tr SEP_rs SEP_cri SEP_n0r SEP_f0r | pose proof (ref_sep A m md n AI) as (SEP_tr & SEP_rs & SEP_cri & SEP_n0r & SEP_f0r) ]).
    (first [ pose proof ((ref_ri A m md n AI)) as dR_9; dand7 dR_9 as RIE RIL RIH RIAL SBAL _ _ | pose proof (ref_ri A m md n AI) as (RIE & RIL & RIH & RIAL & SBAL & _ & _) ]).
    (first [ pose proof ((ref_PC A m md n AI NR CI EMP)) as dR_10; dex1 dR_10 as ks; destruct dR_10 as [LKS PC] | pose proof ((ref_PC A m md n AI NR CI EMP)) as dR_10; dand3 dR_10 as ks LKS PC | destruct (ref_PC A m md n AI NR CI EMP) as (ks & LKS & PC) ]).
    (first [ pose proof ((ref_region A m md n AI NR ENOUGH)) as dR_11; dex1 dR_11 as na; dand4 dR_11 as MX NFC NAL FARR | pose proof ((ref_region A m md n AI NR ENOUGH)) as dR_11; dand5 dR_11 as na MX NFC NAL FARR | destruct (ref_region A m md n AI NR ENOUGH) as (na & MX & NFC & NAL & FARR) ]). fold fr in NFC, FARR.
    pose proof (ref_ws_len A n NR ENOUGH) as LWS. pose proof LWS as WSL. pose proof (ref_ws_last A m md n AI NR ENOUGH) as KW. fold fr in LWS, WSL, KW. rewrite <- KID in KW.
    (first [ pose proof ((hit_stats A m md n AI NR)) as dR_12; dex5 dR_12 as statv v0 v1 v2 vs; dand4 dR_12 as STA STS STA2 LVS | pose proof ((hit_stats A m md n AI NR)) as dR_12; dand9 dR_12 as statv v0 v1 v2 vs STA STS STA2 LVS | destruct (hit_stats A m md n AI NR) as (statv & v0 & v1 & v2 & vs & STA & STS & STA2 & LVS) ]).
    (first [ pose proof ((free_HDR A m md n kidx AI NR KIN)) as dR_13; dex5 dR_13 as b0w b1w h2 w4 d8; rename dR_13 into HDR | pose proof ((free_HDR A m md n kidx AI NR KIN)) as dR_13; dand6 dR_13 as b0w b1w h2 w4 d8 HDR | destruct (free_HDR A m md n kidx AI NR KIN) as (b0w & b1w & h2 & w4 & d8 & HDR) ]).
    (first [ pose proof ((free_ABH A m md n kidx AI NR KIN)) as dR_14; dex2 dR_14 as j0 j1; rename dR_14 into ABH | pose proof ((free_ABH A m md n kidx AI NR KIN)) as dR_14; dand3 dR_14 as j0 j1 ABH | destruct (free_ABH A m md n kidx AI NR KIN) as (j0 & j1 & ABH) ]).
    destruct (free_USR A m md n kidx AI NR KIN) as (uj & USR).
    pose proof (Z_div_mod_eq_full n 8) as NDE. pose proof (Z.mod_pos_bound n 8 ltac:(lia)) as ER.
    (first [ pose proof ((free_SH A m md n kidx AI NR KIN (n / 8) (n mod 8) NDE ER)) as dR_15; dex2 dR_15 as olds oldp; dand4 dR_15 as SHA SHU OL SHP | pose proof ((free_SH A m md n kidx AI NR KIN (n / 8) (n mod 8) NDE ER)) as dR_15; dand6 dR_15 as olds oldp SHA SHU OL SHP | destruct (free_SH A m md n kidx AI NR KIN (n / 8) (n mod 8) NDE ER) as (olds & oldp & SHA & SHU & OL & SHP) ]).
    (first [ pose proof ((hit_depot_wf A m md AI)) as dR_16; dand5 dR_16 as DND DLEN DTOT3 DKEY _ | pose proof (hit_depot_wf A m md AI) as (DND & DLEN & DTOT3 & DKEY & _) ]).
    pose proof (hit_DR A m md AI) as DR0.
    pose proof (hit_TC A m md AI) as TC. pose proof (hit_tsd A m md AI) as [TSD1 TSD2].
    (* [comment removed for export] *)
    (first [ pose proof ((sec_dkeys A WF0)) as dR_17; dand3 dR_17 as DK1 _ DK3 | pose proof (sec_dkeys A WF0) as (DK1 & _ & DK3) ]).
    assert (KL : (1 <= length key <= 255)%nat) by exact (proj1 (Forall_forall _ _) DK1 key KEYU).
    assert (DTOT : depot_total (a_depot A) + 1 + Z.of_nat (length key) < kStackStoreBlockFrames).
    { (first [ pose proof ((wfD A WF0)) as dR_18; dand3 dR_18 as INC NDd _ | destruct (wfD A WF0) as (INC & NDd & _) ]).
      assert (INC' : incl (a_depot A) (p_dkeys (a_pl A))) by (intros k Hk; exact (proj1 (Forall_forall _ _) INC k Hk)).
      (first [ pose proof ((depot_universe_bounds _ _ DK1 DK3 NDd INC')) as dR_19; dand3 dR_19 as L1 _ L3 | pose proof (depot_universe_bounds _ _ DK1 DK3 NDd INC') as (L1 & _ & L3) ]). unfold kStackStoreBlockFrames. clear - L1 L3 KL. lia. }
    (* [comment removed for export] *)
    assert (LO : alloc_ceiling <= lo /\ lo <= bv_unsigned spa - 1024) by (clear - CLO LOSA; lia).
    assert (CEIL : alloc_ceiling <= bv_unsigned spa - 1024) by (clear - CLO LOSA; lia).
    assert (SPR' : bv_unsigned spa + 65536 < 2^64) by (clear - SAHI HI47; lia).
    assert (NR64 : 1 <= n <= 64512) by (clear - NR; unfold kMaxPrimaryUser in NR; lia).
    assert (NDE' : n = 8 * (n / 8) + n mod 8) by (clear - NDE; lia).
    assert (SOA : bv_unsigned spa <= stkobj /\ stkobj + 2064 <= 2^47) by (clear - SOLO SOHI HI47; lia).
    assert (TSDL : 0x5e7b28 <= pa_tsd /\ pa_tsd + 8 <= 0x60a000) by (unfold pa_tsd; lia).
    assert (TPL : bv_unsigned (cl_tp LPA) = 0x5e7bd8) by (cbn [cl_tp LPA]; rewrite unsigned_lit by lia; reflexivity).
    assert (KWR' : bv_unsigned (wz (kidx * class_size (class_of n) / kCompactPtrScale)) < 2^32) by (rewrite unsigned_lit by lia; lia).
    assert (ABE' : chunk_addr (a_sb A) (class_of n) kidx = a_sb A + class_of n * 2^32 + 16 * bv_unsigned (wz (kidx * class_size (class_of n) / kCompactPtrScale))) by (rewrite unsigned_lit by lia; exact ABE).
    assert (DRF : forall D' (m1 m2 : mem), depot_repL AL_pboth rsegs D' (p_nodes0 (a_pl A)) (p_frames0 (a_pl A)) m1 ->
              (forall a, ACells.depot_foot AL_pboth (p_nodes0 (a_pl A)) (p_frames0 (a_pl A)) a -> m2 (Z_to_bv 64 a) = m1 (Z_to_bv 64 a)) ->
              depot_repL AL_pboth rsegs D' (p_nodes0 (a_pl A)) (p_frames0 (a_pl A)) m2).
    { intros D' m1 m2 H1 H2. exact (depot_repL_agree AL_pboth rsegs D' _ _ m1 m2 H1 H2). }
    (* [comment removed for export] *)
    assert (NNF : Z.shiftr (max_count (class_of n)) 1 <= Z.of_nat (length fr)) by (rewrite KS; exact ENOUGH).
    pose proof (ref_nf A m md n AI NR ENOUGH) as ((_ & NFH) & _). fold fr in NFH.
    rewrite <- KS in FARR, LWS, KW.
    (* [comment removed for export] *)
    pose proof (alloc_refill rac spa gp (cl_tp LPA) t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc
                  (aview_of (pa_hull A) m) lo n stkobj canfill pa_tsd (p_ctx (a_pl A)) (p_thr (a_pl A))
                  (class_of n) (max_count (class_of n)) (a_sb A) (chunk_addr (a_sb A) (class_of n) kidx)
                  (chunk_addr (a_sb A) (class_of n) kidx / 8) (rz_size n / 8) (n / 8) (n mod 8) (p_nodes0 (a_pl A)) (p_frames0 (a_pl A))
                  (a_ri A) (Z.of_nat (length fr))
                  ks (ref_ws (a_sb A) (class_of n) fr (Z.shiftr (max_count (class_of n)) 1)) b0w b1w (wz (kidx * class_size (class_of n) / kCompactPtrScale)) statv na h2 w4 d8 j0 j1 v0 v1 v2 vs (a_depot A) key olds uj oldp depot_repL
                  MI ST LO SPA SPR' NR64 NDE' ER CF SOA RZL GT TSS PS DPS BLK BLK2
                  (hit_INI A m md AI) (hit_RSS A m md AI) (hit_RZm A m md AI) (hit_MUM A m md AI) (hit_PCo A m md AI)
                  (hit_AF1 A m md AI) (hit_AF2 A m md AI) (hit_AF44 A m md AI) (hit_AF52 A m md AI) (hit_LS1 A m md AI) (hit_LS2 A m md AI)
                  (hit_HK A m md AI) (hit_SBc A m md AI)
                  TC (hit_TH0 A m md AI) (hit_CT8 A m md AI) (conj TH1 TH2) THRA (conj CT1 CT2) TSDL TPL
                  (conj SB1 SB2) SEP_thr SEP_ctx SEP_tc
                  HC PC LKS MR (ref_CRI A m md n AI NR) (conj RIL RIH) RIAL SBAL SEP_tr SEP_rs SEP_cri SEP_n0r SEP_f0r
                  MX NFC NAL FARR LWS NNF NFH KW KWR' ABU STA STS STA2 LVS
                  ABE' ABA ABQ (conj ABR1 ABR2) RZ8 HDR (fun _ => ABH) SHA SHU OL SHP USR
                  DR0 DND DLEN DTOT (conj DN01 DN02) (conj DF01 DF02) SEP_n0 SEP_f0 SEP_n0t SEP_f0t SEP_n0c SEP_f0c DRF
                  KL KR TRC TRB) as EV.
    (* [comment removed for export] *)
    destruct (asI_minv A m md AI) as [HMI HH].
    eapply (srz_evt_restrict rsegs (pa_hull A) (asI_hull_segs A m md AI) pa_wx _ (pa_eager A) _ _ md T HMI HH).
    { rewrite restrict_MS. exact EV. }
    intros msr' md' HQ HI' Hsame Hcl.
    (first [ dex21 HQ as t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' statv' vc' v0' v1' v2' v' md0; dand22 HQ as -> MU WM' MI' ST' Ppc Psta Pmx Pnf Pna Pfa Psts Psta2 Phdr Plch Pshz Pshw Pshe Pusr Pdr Pmu2 WM2 | dand36 HQ as t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' statv' vc' v0' v1' v2' v' md0 -> MU WM' MI' ST' Ppc Psta Pmx Pnf Pna Pfa Psts Psta2 Phdr dR_HQ_t0; dand8 dR_HQ_t0 as Plch Pshz Pshw Pshe Pusr Pdr Pmu2 WM2 | destruct HQ as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & statv' & vc' & v0' & v1' & v2' & v' & md0
                    & -> & MU & WM' & MI' & ST' & Ppc & Psta & Pmx & Pnf & Pna & Pfa & Psts & Psta2 & Phdr & Plch & Pshz & Pshw & Pshe & Pusr & Pdr & Pmu2 & WM2) ]).
    (* [comment removed for export] *)
    rewrite KS in Ppc, Pnf.
    rewrite unrestrict_MS. cbn [ms_mem] in Hcl.
    pose proof (same_but_materialized_frame _ _ Hsame) as FRM.
    assert (VIEW : aview_of (pa_hull A) (munrestrict (hidc (pa_hull A)) m v') = v').
    { unfold aview_of. rewrite mrestrict_munrestrict. apply mrestrict_clean_id. exact Hcl. }
    assert (NN : forall a, 0 <= a -> (a + 1 <= 0x10000 \/ 0x60a000 <= a) -> a < 2^64 -> aview_of (pa_hull A) m (wz a) <> None -> v' (wz a) <> None).
    { intros a H0 H1 H2. apply (wmono_NN _ _ a WM'); clear - H0 H1 H2; lia. }
    pose proof (b1_final_ok (bv_unsigned b1w) ltac:(pose proof (bv_unsigned_in_range _ b1w); lia)) as [B1R B1M].
    pose proof (rf_u_fresh A m md n AI NR ENOUGH) as FR. fold kidx in FR. (first [ pose proof ((hit_u_range A n kidx NR)) as dR_21; dand3 dR_21 as UR1 UR2 UE | pose proof (hit_u_range A n kidx NR) as (UR1 & UR2 & UE) ]).
    assert (IDR : 0 <= snd (depot_putC (a_depot A) key) < 2^32) by (pose proof (depot_putC_id_range (a_depot A) key) as X; clear - X DLEN; lia).
    assert (SMW : mapped (aview_of (pa_hull A) m) lo (hi - lo)).
    { intros i Hi. destruct (Z_lt_le_dec (lo + i) (bv_unsigned spa)) as [L|GE].
      - (first [ dand3 ST as _ _ ST3 | destruct ST as (_ & _ & ST3) ]). destruct (ST3 (lo + i) ltac:(clear - Hi L; lia)) as [X _]. unfold wview, wa in X.
        intros E. apply X. rewrite E. cbn [cl_segs LPA]. rewrite unsigned_lit by (clear - Hi L CLO CE SPR; lia).
        rewrite (pa_find_segment_none (lo + i) 1); [reflexivity| clear - Hi L CLO CE SPR; lia| right; clear - Hi L CLO CE SPR; lia].
      - replace (lo + i) with (bv_unsigned spa + (lo + i - bv_unsigned spa)) by lia. apply SM. clear - Hi GE; lia. }
    rewrite <- UE.
    (* [comment removed for export] *)
    pose proof (ref_fetched_length fr (refill_count (class_of n)) ltac:(lia)) as FL.
    set (fetched := ref_fetched fr (refill_count (class_of n))) in FL.
    set (ks' := ref_ws (a_sb A) (class_of n) fr (refill_count (class_of n)) ++ skipn (Z.to_nat (refill_count (class_of n))) ks) in Ppc.
    assert (LKS' : length ks' = 16%nat) by (subst ks'; rewrite app_length, length_skipn, WSL; clear - LKS KR2; lia).
    assert (KSF : firstn (length fetched) ks' = map (fun k => wz (k * class_size (class_of n) / kCompactPtrScale)) fetched).
    { subst ks' fetched. rewrite FL. rewrite firstn_app, WSL, Nat.sub_diag, firstn_O, app_nil_r.
      rewrite firstn_all2 by (rewrite WSL; lia). reflexivity. }
    replace (refill_count (class_of n) - 1) with (Z.of_nat (length fetched) - 1) in Ppc by (rewrite FL; clear - KR2; lia).
    pose proof (GEO A m md n spa AI NR ENOUGH CEIL) as G. fold kidx in G.
    eapply (K1 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' (hit_user A n kidx) (refA A n key) (munrestrict (hidc (pa_hull A)) m v') md').
    - (* [comment removed for export] *)
      constructor.
      + exact (ref_WF A m md n key AI NR CI EMP ENOUGH KEYU LIM NLV TINY PCRED).   (* [comment removed for export] *)
      + change (ahull_of pa_image_ivs AL_pboth (refA A n key)) with (pa_hull (refA A n key)). rewrite ref_hull, VIEW.
        exact (ref_arepr A m md n key spa v' AI NR CI ENOUGH CEIL MU NN md0 ks' _ _ LKS' KSF Ppc Pmx Pnf B1R B1M IDR Phdr Plch Pshz Pshe Pdr Pmu2).
      + cbn [refA a_pl a_reg a_sec]. apply (ref_hidden A m md n spa v' lo AI NR ENOUGH CLO (proj2 LO) MU WM'). exact (ai_hidden _ _ _ _ _ _ _ AI).
      + cbn [refA a_pl]. exact (ai_extra _ _ _ _ _ _ _ AI).
      + cbn [refA a_pl a_reg a_sec]. apply aledger_ref. exact (aledger_sbm _ _ _ _ md md' Hsame (ai_ledger _ _ _ _ _ _ _ AI)).   (* [comment removed for export] *)
      + change (ahull_of pa_image_ivs AL_pboth (refA A n key)) with (pa_hull (refA A n key)). change (aeager_of (refA A n key)) with (pa_eager (refA A n key)).
        change (alhull_of AL_pboth (refA A n key)) with (pa_lhull (refA A n key)).
        rewrite ref_hull, ref_lhull, ref_eager. exact HI'.
      + (first [ dand18 FRM as _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HLT _ | destruct FRM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HLT & _) ]). rewrite HLT. exact HH.
      + (* [comment removed for export] *) cbn [refA a_pl a_sec]. rewrite (same_but_materialized_vmmaps _ _ Hsame). exact (ai_cover _ _ _ _ _ _ _ AI).
      + (* [comment removed for export] *) rewrite (same_but_materialized_vmmaps _ _ Hsame). exact (ai_ceil _ _ _ _ _ _ _ AI).
    - (* [comment removed for export] *)
      rewrite ref_hull, VIEW. exact MI'.
    - (* [comment removed for export] *)
      unfold amd_frame. (first [ dand18 FRM as X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13 X14 X15 X16 X17 Xr | destruct FRM as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15 & X16 & X17 & Xr) ]).
      rewrite X2, X17, HH. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; first [assumption| reflexivity].
    - rewrite ref_hull. apply hull_le_refl.
    - intros ff. reflexivity.
    - reflexivity.
    - reflexivity.
    - (* [comment removed for export] *)
      intros c0 [VR VC] [X|X]; [exfalso; clear - X NR; lia|]. split.
      + cbn [refA a_reg]. unfold ref_reg. rewrite (proj2 (Z.eqb_neq c0 (class_of n)) X). exact VR.
      + cbn [refA a_cache]. unfold ref_cache. rewrite (proj2 (Z.eqb_neq c0 (class_of n)) X). exact VC.
    - rewrite UE. clear - G. kung_all. lia.
    - unfold as_live, as_live_. rewrite FR. reflexivity.
    - unfold as_live, as_live_. cbn [refA a_livemap]. fold kidx. rewrite lookup_insert_eq. reflexivity.
    - intros q Hq. unfold as_live, as_live_. cbn [refA a_livemap]. fold kidx. rewrite lookup_insert_ne by congruence. reflexivity.
    - unfold as_livebytes. cbn [refA a_livemap]. fold kidx. rewrite (as_livebytes_insert _ _ _ FR). cbn [li_n]. lia.
    - unfold as_tinycred. cbn [refA a_tiny]. unfold is_tiny. reflexivity.
    - unfold as_nlive. cbn [refA a_livemap]. fold kidx. rewrite (as_nlive_insert _ _ _ FR). reflexivity.
    - unfold as_seccred. cbn [refA a_scred]. destruct (Z.ltb_spec kMaxPrimaryUser n); lia.
    - (* [comment removed for export] *)
      unfold as_primcred. cbn [refA a_pcred]. rewrite (prim_cost_primary n NP). reflexivity.
    - (* [comment removed for export] *) intros _ X. exfalso. clear - X NR. lia.
    - (* [comment removed for export] *) split; [intros _| intros _; exact NP]. rewrite UE. change (p_sb (a_pl A)) with (a_sb A). clear - ABR1 ABR2 G NR. kung_all. lia.
    - (* [comment removed for export] *)
      rewrite ref_hull, VIEW.
      exact (ref_frame_ok A m md n key spa v' lo hi AI NR ENOUGH CLO (proj2 LO) SAHI HI47 MU WM' SMW).
    - (* [comment removed for export] *)
      rewrite ref_hull, VIEW. intros i Hi. cbn [cl_errno LPA]. unfold mrd.
      rewrite (AGimg A m md n spa v' AI NR ENOUGH CEIL MU (6191924 + i)); [reflexivity| clear - Hi; lia| clear - Hi; lia].
    - (* [comment removed for export] *)
      rewrite ref_hull, VIEW. intros a Ha.
      (first [ pose proof ((USH A m md n spa AI NR ENOUGH CEIL)) as dR_25; dand4 dR_25 as U1 U2 U3 _ | pose proof (USH A m md n spa AI NR ENOUGH CEIL) as (U1 & U2 & U3 & _) ]). pose proof (div8_ceil n ltac:(lia)) as DC. pose proof (conj RIL RIH) as RI.
      fold kidx in U3. fold kidx.
      apply (AGW A m n spa v' MU); [clear - Ha HI47 SPR; lia|].
      apply (W_shape A m md n spa AI NR ENOUGH CEIL); fold kidx; clear - Ha HI47 SPR G U3 DC CE RI; kung_all; lia.
    - rewrite ref_hull, VIEW. exact ST'.
  Qed.
End BridgeRC.

(* [comment removed for export] *)
Section Closed.
Context {Clg : Ceiling}.
  Theorem alloc_refill_c_closed :
    forall (rac spa gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (md : Model) (A : AState) (n canfill stkobj lo hi : Z) (key : list Z) (T : TSet),
      alloc_core_pre rac spa tp m md A n canfill stkobj lo hi key ->
      n <= kMaxPrimaryUser -> a_cache_inited A = true -> pk_chunks (a_cache A (class_of n)) = [] ->
      refill_count (class_of n) <= Z.of_nat (length (rg_free (a_reg A (class_of n)))) ->
      alloc_core_K1v rac spa gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md A n canfill lo hi T ->
      srealizes (cl_segs LPA) (mkCfg (alloc_entry_ms rac spa gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n stkobj canfill) md) T.
  Proof. exact (alloc_refill_c rzlog_ok get_thread_ok thread_stats_ok poison_ok depot_put_ok classid_blk_ok classid_blk2_ok). Qed.

  (* [comment removed for export] *)
  Theorem alloc_refill_cE_closed :
    forall (rac spa gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (md : Model) (A : AState) (n canfill stkobj lo hi : Z) (key : list Z) (T : TSet),
      alloc_core_pre rac spa tp m md A n canfill stkobj lo hi key ->
      n <= kMaxPrimaryUser -> pk_chunks (a_cache A (class_of n)) = [] ->
      refill_count (class_of n) <= Z.of_nat (length (rg_free (a_reg A (class_of n)))) ->
      alloc_core_K1v rac spa gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md A n canfill lo hi T ->
      srealizes (cl_segs LPA) (mkCfg (alloc_entry_ms rac spa gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n stkobj canfill) md) T.
  Proof.
    intros until T. intros PRE NP EMP ENOUGH K1. destruct (a_cache_inited A) eqn:CI; [eapply alloc_refill_c_closed; eassumption|].
    exfalso. (first [ dand4 PRE as AI _ NRQ _ | destruct PRE as (AI & _ & NRQ & _) ]). eapply (refill0_vacuous A m md n AI); [clear - NRQ NP; lia| exact CI| exact ENOUGH].
  Qed.
End Closed.
