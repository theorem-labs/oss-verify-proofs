(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.GcFlush11.  (* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtMem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatLeaf_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtRuns ArtRunsMem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatCls_b BatCellEx_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtBridge. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatInv_b BatInvMalloc_b BatLift_b BatWrapKit_b BatFsInv_b BatFsInvLaws_b BatIfaceLaws_b BatInvFrame_b BatIfaceFrame_b BatWrapC_b BatWrapVis_b BatWrapC2_b BatWrapRng_b BatWrapStrlen_b BatWrapMemI_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Section IL.
Variables MAPS0 RESV0 NOACC0 : list (word * word).
Variables BASE BUDGET : Z.
Variable rn : art_run.
Variable L : asan_layout.
Variable IL : icpt_layout.
Hypothesis HLsegs : hl_segs L = ASEGS.
Hypothesis HLlo : hl_img_lo L = 0x10000.
Hypothesis HLhi : hl_img_hi L = 0x696000.
Hypothesis HILglobals : icl_globals IL = ART_GLOBALS.
Hypothesis HILpoison : icl_poison IL = [(0x231c0, 0x23980); (0x13bfc0, 0x13c580)].
#[local] Abbreviation RI := (art_ri_inv art_fsg MAPS0 RESV0 NOACC0 BASE BUDGET art_fsinv rn).
#[local] Abbreviation HI := (art_iface art_fsg MAPS0 RESV0 NOACC0 BASE BUDGET art_fsinv rn).

#[using="Type"] Lemma art_shadow_allowed_sub : forall A a n a' n', shadow_allowed A a n -> a <= a' -> a' + n' <= a + n -> 0 < n' -> shadow_allowed A a' n'.
Proof. intros A a n a' n' SA H1 H2 H3 x Hx. apply SA. exact (in_shadow_of_sub a n a' n' x H1 H2 H3 Hx). Qed.

#[using="Type"] Theorem art_law_shadow_defined : rt_shadow_defined HI.
Proof.
  intros LB FF LK cr A M V (G & _ & FS & _) x Hx. destruct (fsinv_cs _ _ _ _ _ FS) as (_ & _ & _ & _ & _ & _ & _ & _ & SD).
  pose proof (SD (Z_to_bv 64 x)) as X. rewrite art_u_lit in X by (unfold LOWSH_LO, LOWSH_HI, HIGHSH_LO, HIGHSH_HI in Hx; lia). apply X.
  unfold in_shadow_rw, LSH_LO, LSH_HI, HSH_LO, HSH_HI. unfold LOWSH_LO, LOWSH_HI, HIGHSH_LO, HIGHSH_HI in Hx. exact Hx.
Qed.

#[using="HILglobals"] Theorem art_law_globals : rt_globals IL HI.
Proof.
  intros LB FF LK cr A M V (G & _ & FS & _ & _ & CLI & _). rewrite HILglobals.
  destruct (fsinv_cs _ _ _ _ _ FS) as (_ & _ & _ & _ & _ & _ & _ & GL & _).
  destruct (art_cli_facts _ _ _ _ _ _ CLI) as (_ & _ & IMGSH & _).
  unfold ART_GLOBALS in *. rewrite !Forall_cons_iff in *. cbn [fst snd] in *.
  destruct GL as (g1 & g2 & g3 & g4 & g5 & g6 & g7 & g8 & g9 & g10 & g11 & g12 & g13 & g14 & g15 & g16 & g17 & g18 & g19 & g20 & g21 & g22 & g23 & _).
  assert (SA : forall u n, 0x10000 <= u -> u + n <= 0x696000 -> 0 < n -> shadow_allowed A u n).
  { intros u n H1 H2 H3. apply (art_shadow_allowed_sub A 0x10000 (0x696000 - 0x10000)); [exact IMGSH | lia | lia | lia]. }
  repeat (split; [split; [assumption | apply SA; lia] |]). apply Forall_nil.
Qed.

#[using="HLlo HLhi HILpoison"] Theorem art_law_img_shadow : rt_img_shadow L IL HI.
Proof.
  intros LB FF LK cr A M V (G & _ & FS & _ & _ & CLI & _) a n Ha Hn Hp AV. rewrite HLlo in Ha. rewrite HLhi in Hn. rewrite HILpoison in AV.
  rewrite !Forall_cons_iff in AV. cbn [fst snd] in AV. destruct AV as (P1 & P2 & _).
  destruct (fsinv_cs _ _ _ _ _ FS) as (_ & _ & _ & _ & _ & _ & SH & _).
  destruct (art_cli_facts _ _ _ _ _ _ CLI) as (_ & _ & IMGSH & _).
  split; [|apply (art_shadow_allowed_sub A 0x10000 (0x696000 - 0x10000)); [exact IMGSH | lia | lia | lia]].
  intros x (X1 & X2). apply SH. unfold HeapIfaceA.S, HeapIfaceA.SB in *.
  assert (D1 : 0x10000 / 8 <= a / 8) by (apply Z.div_le_mono; lia). assert (D2 : (a + n - 1) / 8 <= (0x696000 - 1) / 8) by (apply Z.div_le_mono; lia).
  change (0x10000 / 8) with 8192 in *. change ((0x696000 - 1) / 8) with 863231 in *. change (0x696000 / 8) with 863232. change (0x231c0 / 8) with 17976. change (0x23980 / 8) with 18224. change (0x13bfc0 / 8) with 161784. change (0x13c580 / 8) with 161968. change (0x231e0 / 8) with 17980. change (0x23220 / 8) with 17988. change (0x232a0 / 8) with 18004. change (0x23300 / 8) with 18016. change (0x23780 / 8) with 18160. change (0x23880 / 8) with 18192.
  assert (Q1 : a + n <= 0x231c0 -> (a + n - 1) / 8 < 17976) by (intros Q; apply Z.div_lt_upper_bound; lia).
  assert (Q2 : 0x23980 <= a -> 18224 <= a / 8) by (intros Q; apply Z.div_le_lower_bound; lia).
  assert (Q5 : a + n <= 0x13bfc0 -> (a + n - 1) / 8 < 161784) by (intros Q; apply Z.div_lt_upper_bound; lia).
  assert (Q6 : 0x13c580 <= a -> 161968 <= a / 8) by (intros Q; apply Z.div_le_lower_bound; lia).
  clear - X1 X2 D1 D2 P1 P2 Q1 Q2 Q5 Q6. lia.
Qed.

(* [comment removed for export] *)
Hypothesis HLtp : hl_tp L = rn_tp rn.
Hypothesis HILctx : icl_ctxslot IL = 0x6951b8.
Hypothesis Htsd : rn_tsd rn = 0x6951b8.
Hypothesis Hkey0 : rn_key rn = 0.
Hypothesis HLroimg : forall a, hl_rt_ro L a -> 0x10000 <= a < 0x696000.
Hypothesis HLst : forall a, art_zone_statics a -> hl_rt_static L a.
Hypothesis HLtls : forall a, (rn_tp rn - 88 <= a < rn_tp rn - 80 \/ rn_tsd rn + 8 * rn_key rn <= a < rn_tsd rn + 8 * rn_key rn + 8
                              \/ 0x673cf8 <= a < 0x673d00 \/ 0x673d28 <= a < 0x673d30 \/ rn_tp rn <= a < rn_tp rn + 8
                              \/ rn_tp rn + rn_loff rn <= a < rn_tp rn + rn_loff rn + 4) -> hl_rt_static L a.
Hypothesis HLro : forall a, 0x10000 <= a < 0x139000 -> hl_rt_ro L a.
Hypothesis HLcs : forall a, (0x1392d8 <= a < 0x1392e0 \/ 0x1393a0 <= a < 0x1393b8 \/ rn_tp rn + 8 <= a < rn_tp rn + 16) -> hl_rt_static L a.

#[using="HLsegs HLlo HLhi HLtp HILctx Htsd Hkey0 HLroimg HLst HLtls HLro"] Theorem art_law_tls : rt_tls L (rn_ar rn) IL HI.
Proof.
  intros LB FF LK cr A M model (G & REPr & FS & BV & _ & CLI & KN & LZ & EG). cbn [vml_of fst snd] in *.
  change (mkH (m_vm_lazy model) A) with (bhid A model) in REPr. set (Mr0 := mrestrict (bhid A model) M) in *.
  pose proof (BINV_live _ _ _ _ _ _ _ _ _ _ _ _ BV) as LIVEOK.
  pose proof REPr as (ROK & STAT & THR & _). destruct STAT as (_ & _ & TSD & _). destruct TSD as (_ & _ & _ & T4 & T5 & _). destruct THR as (WT & _).
  destruct (fsinv_cs _ _ _ _ _ FS) as ((Q1 & Q2 & Q3) & _ & _ & _ & C4 & C5 & _).
  pose proof (art_cli_hi rn LB FF LK A M CLI) as (HI1 & HI2).
  assert (GEOX : (4096 <= rn_t rn /\ rn_t rn + 4096 <= rn_HI rn /\ (rn_t rn + 4096 <= 0x10000 \/ 0x696000 <= rn_t rn) /\ (rn_t rn + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= rn_t rn))
                 /\ (4096 <= rn_ctx rn /\ rn_ctx rn + 4096 <= rn_HI rn /\ (rn_ctx rn + 4096 <= 0x10000 \/ 0x696000 <= rn_ctx rn) /\ (rn_ctx rn + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= rn_ctx rn))
                 /\ (4096 <= rn_dtls rn /\ rn_dtls rn + 4096 <= rn_HI rn /\ (rn_dtls rn + 4096 <= 0x10000 \/ 0x696000 <= rn_dtls rn) /\ (rn_dtls rn + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= rn_dtls rn))
                 /\ ((rn_t rn + 4096 <= rn_ctx rn \/ rn_ctx rn + 4096 <= rn_t rn) /\ (rn_dtls rn + 4096 <= rn_t rn \/ rn_t rn + 4096 <= rn_dtls rn) /\ (rn_dtls rn + 4096 <= rn_ctx rn \/ rn_ctx rn + 4096 <= rn_dtls rn))
                 /\ ((rn_blk rn + 8388608 <= rn_t rn \/ rn_t rn + 4096 <= rn_blk rn) /\ (rn_t rn + 4096 <= rn_kbase rn \/ rn_kbase rn + 0x2000011000 <= rn_t rn) /\ (rn_parr rn + 8388608 <= rn_t rn \/ rn_t rn + 4096 <= rn_parr rn))
                 /\ ((rn_blk rn + 8388608 <= rn_ctx rn \/ rn_ctx rn + 4096 <= rn_blk rn) /\ (rn_ctx rn + 4096 <= rn_kbase rn \/ rn_kbase rn + 0x2000011000 <= rn_ctx rn) /\ (rn_parr rn + 8388608 <= rn_ctx rn \/ rn_ctx rn + 4096 <= rn_parr rn))
                 /\ ((rn_dtls rn + 4096 <= rn_blk rn \/ rn_blk rn + 8388608 <= rn_dtls rn) /\ (rn_dtls rn + 4096 <= rn_kbase rn \/ rn_kbase rn + 0x2000011000 <= rn_dtls rn) /\ (rn_dtls rn + 4096 <= rn_parr rn \/ rn_parr rn + 8388608 <= rn_dtls rn))
                 /\ (0x10000 <= rn_tsd rn /\ rn_tsd rn + 1024 <= 0x696000)).
  { clear - ROK. rok_open ROK. geo_open GEO. destruct D3 as (_ & D3a & _). unfold BIGSHADOW_LO, BIGSHADOW_HI in D3a. unfold apart in *. change (2 ^ 23) with 8388608 in *.
    repeat split; assumption. }
  destruct GEOX as ((Gt1 & Gt2 & Gt3 & Gt4) & (Gc1 & Gc2 & Gc3 & Gc4) & (Gd1 & Gd2 & Gd3 & Gd4) & (Atc & Adt & Adc) & (Lt1 & Lt2 & Lt3) & (Lc1 & Lc2 & Lc3) & (Ld1 & Ld2 & Ld3) & (Gs1 & Gs2)).
  (* [comment removed for export] *)
  assert (NLZ : forall a, rn_ctx rn <= a < rn_ctx rn + 4096 \/ rn_t rn <= a < rn_t rn + 4096 \/ rn_dtls rn <= a < rn_dtls rn + 4096 ->
                page_in_ranges (page_base (Z_to_bv 64 a)) (m_vm_lazy model) = false).
  { intros a Ha. destruct (page_in_ranges (page_base (Z_to_bv 64 a)) (m_vm_lazy model)) eqn:E; [|reflexivity]. exfalso.
    destruct LZ as (L1 & _). pose proof (L1 _ E) as Z. rewrite art_u_lit in Z by (clear - Ha Gc1 Gc2 Gt1 Gt2 Gd1 Gd2 HI2; lia).
    unfold art_lazy_zone in Z. change (2 ^ 23) with 8388608 in Z.
    destruct Z as [Z | [Z | [[Z | Z] _]]]; clear - Z Ha Gt4 Gc4 Gd4 Lt1 Lt2 Lt3 Lc1 Lc2 Lc3 Ld1 Ld2 Ld3; (clear - Gc4 Gd4 Gt4 Ha Lc1 Lc2 Lc3 Ld1 Ld2 Ld3 Lt1 Lt2 Lt3 Z a rn; lia). }
  assert (VIS : forall a (n : nat), (rn_ctx rn <= a /\ a + Z.of_nat n <= rn_ctx rn + 4096) \/ (rn_t rn <= a /\ a + Z.of_nat n <= rn_t rn + 4096) -> art_vis (bhid A model) a (Z.of_nat n)).
  { intros a n Ha x Hx. apply (art_vis_notlazy A model). rewrite <- (Z_to_bv_bv_unsigned 64 x). apply NLZ. clear - Ha Hx. lia. }
  (* [comment removed for export] *)
  assert (C1f : cellA M 0x6951b8 8 (rn_ctx rn)).
  { replace (rn_tsd rn + 8 * rn_key rn) with 0x6951b8 in T4 by (rewrite Htsd, Hkey0; reflexivity).
    apply (proj1 (art_cell_vis (bhid A model) M 0x6951b8 8 (rn_ctx rn) ltac:(lia) ltac:(cbn; lia) (art_img_vis art_fsg rn G A (m_vm_lazy model) 0x6951b8 8 ROK LZ ltac:(lia) ltac:(lia)))). exact T4. }
  assert (C2f : cellA M (rn_ctx rn + 152) 8 (rn_t rn)).
  { apply (proj1 (art_cell_vis (bhid A model) M (rn_ctx rn + 152) 8 (rn_t rn) ltac:(clear - Gc1; lia) ltac:(cbn; clear - Gc2 HI2; lia) (VIS (rn_ctx rn + 152) 8%nat ltac:(left; cbn; lia)))). exact T5. }
  destruct (art_cell_exists Mr0 (rn_t rn + 48) 8 ltac:(lia) ltac:(cbn; clear - Gt3; lia) ltac:(clear - Gt1; lia) ltac:(cbn; clear - Gt2 HI2; lia)
              ltac:(intros d k Hd Hk; replace (rn_t rn + 48 + d) with (rn_t rn + (48 + d)) by ring; apply WT; [clear - Hd; lia | cbn in Hk; clear - Hd Hk; lia])) as (tbv & Rtb & Ctb).
  destruct (art_cell_exists Mr0 (rn_t rn + 56) 8 ltac:(lia) ltac:(cbn; clear - Gt3; lia) ltac:(clear - Gt1; lia) ltac:(cbn; clear - Gt2 HI2; lia)
              ltac:(intros d k Hd Hk; replace (rn_t rn + 56 + d) with (rn_t rn + (56 + d)) by ring; apply WT; [clear - Hd; lia | cbn in Hk; clear - Hd Hk; lia])) as (tev & Rte & Cte).
  assert (C3f : cellA M (rn_t rn + 48) 8 tbv).
  { apply (proj1 (art_cell_vis (bhid A model) M (rn_t rn + 48) 8 tbv ltac:(clear - Gt1; lia) ltac:(cbn; clear - Gt2 HI2; lia) (VIS (rn_t rn + 48) 8%nat ltac:(right; cbn; lia)))). exact Ctb. }
  assert (C4f : cellA M (rn_t rn + 56) 8 tev).
  { apply (proj1 (art_cell_vis (bhid A model) M (rn_t rn + 56) 8 tev ltac:(clear - Gt1; lia) ltac:(cbn; clear - Gt2 HI2; lia) (VIS (rn_t rn + 56) 8%nat ltac:(right; cbn; lia)))). exact Cte. }
  exists (rn_ctx rn), (rn_t rn), tbv, tev, (rn_dtls rn). rewrite HLsegs, HILctx, HLtp, HLlo, HLhi.
  assert (HIeq : ahl_ceil (rn_ar rn) = rn_HI rn) by reflexivity. rewrite HIeq.
  split; [exact C1f|]. split; [exact C2f|]. split; [exact C3f|]. split; [exact C4f|]. split; [exact C4|]. split; [exact C5|].
  split; [exact Gc1|]. split; [clear - Gc2; lia|]. split; [exact Gt1|]. split; [clear - Gt2; lia|]. split; [exact Gd1|]. split; [exact Gd2|].
  split; [exact Rtb|]. split; [exact Rte|].
  split; [clear - Gc3; lia|]. split; [clear - Gt3; lia|]. split; [exact Gd3|].
  split; [clear - Atc; lia|]. split; [clear - Adc; lia|]. split; [clear - Adt; lia|].
  intros a Ha. split; [|apply NLZ; clear - Ha; lia].
  (* [comment removed for export] *)
  assert (KSP : rn_kbase rn < rn_spb rn /\ rn_spb rn + 2 ^ 37 <= rn_kbase rn + 0x2000011000).
  { clear - ROK. rok_open ROK. geo_open GEO. change (2 ^ 37) with 137438953472. lia. }
  change (2 ^ 37) with 137438953472 in KSP.
  assert (NB : forall o, (o = rn_t rn \/ o = rn_ctx rn) -> o <= a < o + 4096 -> ~ in_block LB a).
  { intros o Ho Hoa (b & Hb & R). destruct (art_block_geo rn G LB FF LK A M Mr0 REPr CLI b Hb) as (_ & [K|(p & Hp & K1 & K2)]).
    - change (2 ^ 37) with 137438953472 in K. destruct Ho as [-> | ->]; [clear - Hoa R K KSP Lt2 | clear - Hoa R K KSP Lc2]; lia.
    - destruct (art_live_facts MAPS0 RESV0 rn G LIVEOK KN p Hp) as (_ & _ & _ & _ & _ & _ & LO).
      destruct Ho as [-> | ->].
      + pose proof (LO (rn_t rn, 4096) ltac:(unfold art_objs; left; reflexivity)) as At. cbn [fst snd] in At. unfold apart in At. clear - Hoa R K1 K2 At. lia.
      + pose proof (LO (rn_ctx rn, 4096) ltac:(unfold art_objs; right; left; reflexivity)) as At. cbn [fst snd] in At. unfold apart in At. clear - Hoa R K1 K2 At. lia. }
  assert (PRIV : art_private L (rn_ar rn) LB FF a).
  { destruct Ha as [Ha | [Ha | Ha]].
    - apply (art_priv_zone MAPS0 RESV0 rn L HLlo HLhi HLst HLtls HLro G LB FF LK A M Mr0 REPr FS CLI LIVEOK KN a).
      + unfold art_alloc_zone. right; right; left. clear - Ha. lia.
      + apply (NB (rn_ctx rn)); [right; reflexivity | clear - Ha; lia].
    - destruct (Z_lt_le_dec a (rn_t rn + 72)) as [X1 | X1]; [|destruct (Z_lt_le_dec a (rn_t rn + 80)) as [X2 | X2]].
      + apply (art_priv_zone MAPS0 RESV0 rn L HLlo HLhi HLst HLtls HLro G LB FF LK A M Mr0 REPr FS CLI LIVEOK KN a).
        * unfold art_alloc_zone, art_zone_thread. right; left. clear - Ha X1. lia.
        * apply (NB (rn_t rn)); [left; reflexivity | clear - Ha; lia].
      + apply (art_priv_fs3 MAPS0 RESV0 rn L HLlo HLhi HLtls G LB FF LK A M Mr0 REPr FS CLI LIVEOK KN a).
        * unfold fs_zone3. right; left. clear - X1 X2. lia.
        * intros (f & Hf & C & _). pose proof (fsinv_frame_in rn _ FF LK M FS f ltac:(apply in_or_app; left; exact Hf)) as (I1 & I2 & I3).
          pose proof (fsinv_geo _ _ _ _ _ FS) as (_ & _ & _ & _ & _ & Aft & _). unfold FS_BYTES in *. clear - C I1 I2 Aft Ha. lia.
      + apply (art_priv_zone MAPS0 RESV0 rn L HLlo HLhi HLst HLtls HLro G LB FF LK A M Mr0 REPr FS CLI LIVEOK KN a).
        * unfold art_alloc_zone, art_zone_thread. right; left. clear - Ha X2. lia.
        * apply (NB (rn_t rn)); [left; reflexivity | clear - Ha; lia].
    - exact (art_priv_dtls MAPS0 RESV0 rn L HLlo HLhi G LB FF LK A M Mr0 REPr FS CLI LIVEOK KN a Ha). }
  (* [comment removed for export] *)
  intros sp scr CL.
  assert (APPA : (a < 0x7fff7000 \/ 0x10007fff8000 <= a) /\ a < rn_HI rn /\ ~ (0x10000 <= a < 0x696000)) by (clear - Ha Gt2 Gt3 Gt4 Gc2 Gc3 Gc4 Gd2 Gd3 Gd4; lia).
  destruct APPA as (AP1 & AP2 & AP3).
  destruct PRIV as [NC | [RO | (b & Hb & BS)]].
  - apply NC. unfold aclient, aclient_g in *. destruct CL as [H|[H|[H|[H|[H|[H|H]]]]]].
    + left; exact H.
    + exfalso. rewrite HIeq in H. clear - H AP2. lia.
    + right; right; left. exact H.
    + do 3 right; left; exact H.
    + do 4 right; left; exact H.
    + do 5 right; left; exact H.
    + do 6 right; exact H.
  - pose proof (HLroimg a RO). clear - H AP3. lia.
  - pose proof CLI as (CB & _). destruct (CB b Hb) as (K1 & _ & _ & K4 & K5 & _). rewrite HIeq in K5.
    destruct BS as (X1 & X2). pose proof (art_S_lo (fst b) ltac:(clear - K1; lia)). pose proof (art_S_hi (fst b + snd b - 1) ltac:(clear - K5 HI2; lia)). clear - X1 X2 H H0 AP1. lia.
Qed.
End IL.
