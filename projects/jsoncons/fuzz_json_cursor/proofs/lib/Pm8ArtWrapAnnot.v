(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare ShapeAlg SpinAlg AsanAcct RefMemcpyLib MemSplit StreamSim HeapIface HeapIfaceA PmHeapIfaceA PmShadowW IcptIfaceA PmIcptIfaceA ArtMem ArtRuns ArtRunsMem Pm8ArtCls Pm8ArtLeaf Pm8ArtCellEx Pm8ArtImgCell Pm8ArtPoison Pm8ArtDepot
     ArtBridge Pm8ArtInv Pm8ArtInvMalloc Pm8ArtLift Pm8ArtWrapKit Pm8ArtFsInv Pm8ArtFsInvLaws Pm8ArtIfaceLaws Pm8ArtInvFrame Pm8ArtIfaceFrame Pm8RegionPoisoned Pm8ArtFp.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import Pm8ArtWrapC Pm8ArtWrapVis Pm8ArtWrapC2 Pm8ArtWrapRng.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmShadowStep Pm8ArtInvFrameS Pm8ArtWrapC2s Pm8Annot.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Section WAN.
Variables MAPS0 RESV0 NOACC0 : list (word * word).
Variables BASE BUDGET : Z.
Variable rn : art_run.
Variable scfg : SpuriousCfg.
Hypothesis Hwx : wx_segs_nowrap ASEGS.
Variable L : asan_layout.
Hypothesis HLsegs : hl_segs L = ASEGS.
Hypothesis HLlo : hl_img_lo L = 0x10000.
Hypothesis HLhi : hl_img_hi L = 0x6b3000.
#[local] Abbreviation RI := (art_ri_inv art_fsg MAPS0 RESV0 NOACC0 BASE BUDGET art_fsinv rn).
Context {fx : PropExec.FPState}.

Theorem art_wrap_annotate : forall (R : bvmap 5 word) (M : word -> option byte) (model : Model)
    (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (u n om nm : Z) (Kt : ShapeAlg.TSet),
  let sp := U (getr R 2) in
  RI LB FF LK cr A M (vml_of model) -> m_halted model = None -> MInv A model ->
  In (u, n) LB -> getr R 10 = Z_to_bv 64 u -> getr R 11 = Z_to_bv 64 (u + n) -> getr R 12 = Z_to_bv 64 (u + om) -> getr R 13 = Z_to_bv 64 (u + nm) ->
  0 <= om <= n -> 0 <= nm <= n -> n <= 2 ^ 18 ->
  shadow_cont M u n om ->
  Hoare.ret_ok (getr R 1) ->
  astack_ok L (rn_ar rn) M 4096 sp ->
  Kt [] ->
  (forall (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model),
      regs_preserved R R' -> shadow_cont M' u n nm ->
      (forall a, 0 <= a < 2 ^ 64 -> aclient L (rn_ar rn) LB FF sp 4096 a -> ~ in_shadow_of u n a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
      (forall a, sp - 4096 <= a < sp -> M' (Z_to_bv 64 a) <> None) ->
      (forall a : word, M a <> None -> M' a <> None) ->
      model_rt model model' -> MInv A model' -> RI LB FF LK cr A M' (vml_of model') ->
      srealizes ASEGS scfg (mkCfg (mkst R' (getr R 1) M' (seg_rom ASEGS)) model') Kt) ->
  srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x82c5c) M (seg_rom ASEGS)) model) Kt.
Proof.
  intros R M model LB FF LK cr A u n om nm Kt sp INV Hhalt HMI HB H10 H11 H12 H13 Hom Hnm Hn18 SC0 Hret AST KT0 CONT.
  destruct (art_ri_open MAPS0 RESV0 NOACC0 BASE BUDGET rn LB FF LK cr A M model INV Hhalt HMI) as (G & REPr & FS & B0 & CRED & CLI & KN & LZ & EG).
  set (Mr0 := mrestrict (bhid A model) M) in *.
  destruct AST as (S16 & SHI & SLE & STOP & SWR & SDEF). fold sp in S16, SHI, SLE, SWR, SDEF. rewrite HLsegs in SWR.
  assert (HIeq : ahl_ceil (rn_ar rn) = rn_HI rn) by reflexivity. rewrite HIeq in SHI.
  pose proof (art_cli_hi rn LB FF LK A M CLI) as (HI1 & HI2).
  pose proof (art_cli_facts rn LB FF LK A M CLI) as (_ & _ & _ & SPT16).
  pose proof REPr as (ROK & STAT & THR & _).
  pose proof CLI as (CB & _).
  destruct (CB (u, n) HB) as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & _). cbn [fst snd] in K1, K2, K3, K4, K5, K6, K7, K8, K9. rewrite HIeq in K5.
  assert (U8 : u mod 8 = 0).
  { pose proof (Z.div_mod u 16 ltac:(lia)) as D. rewrite K3, Z.add_0_r in D. rewrite D. replace (16 * (u / 16)) with ((2 * (u / 16)) * 8) by ring. apply Z_mod_mult. }
  assert (SPR : 0x10007fff8000 <= sp - 2192 /\ sp < 2 ^ 47) by (clear - SHI HI1 SLE SPT16; lia).
  destruct STAT as (PC & LAY & TSD & _ & _ & _ & TLSG & S8).
  destruct THR as (_ & _ & _ & _ & _ & _ & _ & LSAN0).
  assert (W0 : wrA Mr0 (sp - 4096) 4096).
  { apply (art_stack_wr art_fsg rn G A (m_vm_lazy model) M sp 4096 ROK LZ ltac:(clear - SHI; lia) ltac:(clear; lia) ltac:(clear - SPR; lia)). exact SWR. }
  assert (W2192 : wrA Mr0 (sp - 2192) 2192) by (apply (wr_sub _ _ _ _ _ _ W0); lia).
  assert (CDCO : cellA Mr0 0x15a218 1 1) by conj_find S8.
  assert (CVP : cellA Mr0 0x153188 8 0x1ec458) by conj_find S8.
  assert (CV : cellA Mr0 0x1ec458 4 0) by conj_find S8.

  set (g := (n + 7) / 8).
  assert (Qg : n / 8 <= g /\ 1 <= g /\ 8 * g < n + 8 /\ n <= 8 * g) by (unfold g; pose proof (Z.div_mod n 8 ltac:(lia)); pose proof (Z.mod_pos_bound n 8 ltac:(lia)); pose proof (Z.div_mod (n + 7) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(lia)); lia).
  assert (ESu : HeapIfaceA.S u = 0x7fff8000 + u / 8) by (unfold HeapIfaceA.S, HeapIfaceA.SB; ring).
  assert (Eend : HeapIfaceA.S (u + n - 1) = HeapIfaceA.S u + (g - 1)).
  { unfold HeapIfaceA.S, g. replace (u + n - 1) with (u + (n - 1)) by ring. rewrite (sstep_div u (n - 1) U8).
    assert ((n - 1) / 8 = (n + 7) / 8 - 1); [|lia]. replace (n + 7) with (n - 1 + 1 * 8) by ring. rewrite Z.div_add by lia. ring. }
  assert (INSH : forall j, 0 <= j < g -> in_shadow_of u n (HeapIfaceA.S u + j)) by (intros j Hj; unfold in_shadow_of; rewrite Eend; lia).
  assert (VSH : forall j, 0 <= j < g -> bhid A model (Z_to_bv 64 (HeapIfaceA.S u + j)) = false) by (intros j Hj; exact (art_vis_shadow A model u n _ K9 (INSH j Hj))).
  assert (IDX : forall j, 0 <= j < g -> j < n / 8 \/ (j = n / 8 /\ n mod 8 <> 0)).
  { intros j Hj. unfold g in Hj. pose proof (Z.div_mod n 8 ltac:(lia)). pose proof (Z.mod_pos_bound n 8 ltac:(lia)). pose proof (Z.div_mod (n + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(lia)). lia. }
  assert (SHR : 0x7fff8000 <= HeapIfaceA.S u /\ HeapIfaceA.S u + g <= 0x10007fff8000).
  { rewrite ESu. assert (0 <= u / 8) by (apply Z.div_pos; lia). assert ((u + n + 7) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; clear - K5 HI2; lia). change (2 ^ 47 / 8) with (2 ^ 44) in *.
    replace (u + n + 7) with (u + (n + 7)) in H0 by ring. rewrite (sstep_div u (n + 7) U8) in H0. fold g in H0. lia. }
  assert (WSH : wrA Mr0 (0x7fff8000 + u / 8) ((u + n - u + 7) / 8)).
  { replace (u + n - u + 7) with (n + 7) by ring. fold g. rewrite <- ESu. apply (art_wr_of_defined ASEGS Mr0); [clear - SHR; lia | clear - SHR; lia |].
    intros x Hx. set (j := U x - HeapIfaceA.S u). assert (Ex : x = Z_to_bv 64 (HeapIfaceA.S u + j)) by (unfold j; replace (HeapIfaceA.S u + (U x - HeapIfaceA.S u)) with (U x) by ring; symmetry; apply Z_to_bv_bv_unsigned).
    rewrite Ex. unfold Mr0, mrestrict. rewrite (VSH j ltac:(unfold j; lia)). destruct (shadow_blk_w_def M u n K8 j ltac:(unfold j; lia) (IDX j ltac:(unfold j; lia))) as (v & Bv). unfold byte_at in Bv. rewrite Bv. discriminate. }
  assert (HAPP : (8 <= u /\ u + n <= 0x7fff8000) \/ (kHighMemBeg <= u /\ u + n <= kHighMemEnd + 1)).
  { destruct K6 as (_ & [Lo|Hi] & Top); unfold BIGSHADOW_LO, BIGSHADOW_HI, kHighMemBeg, kHighMemEnd in *; [left|right]; lia. }
  assert (HEND : (u + n) mod 8 <> 0 -> exists sv, cellA Mr0 (0x7fff8000 + (u + n) / 8) 1 sv /\ (sv = 252 \/ (1 <= sv <= 7 /\ sv <= (u + n) mod 8))).
  { rewrite (sstep_mod u n U8), (sstep_div u n U8). intros N0. destruct SC0 as (Z0 & P0 & F0).
    assert (Hj : 0 <= n / 8 < g) by (split; [apply Z.div_pos; lia|unfold g; pose proof (Z.div_mod n 8 ltac:(lia)); pose proof (Z.mod_pos_bound n 8 ltac:(lia)); pose proof (Z.div_mod (n + 7) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(lia)); lia]).
    assert (TOR : forall v, 0 <= v < 256 -> byte_at M (HeapIfaceA.S u + n / 8) v -> cellA Mr0 (0x7fff8000 + (u / 8 + n / 8)) 1 v).
    { intros v Hv Bv. replace (0x7fff8000 + (u / 8 + n / 8)) with (HeapIfaceA.S u + n / 8) by (rewrite ESu; ring). apply art_cell1_of_byte; [exact Hv|]. unfold Mr0, mrestrict. rewrite (VSH _ Hj). exact Bv. }
    assert (Qo : om / 8 <= n / 8 /\ (om / 8 = n / 8 -> om mod 8 <= n mod 8) /\ 0 <= om mod 8 < 8 /\ (om mod 8 = 0 -> (om + 7) / 8 = om / 8) /\ (om / 8 < n / 8 -> (om + 7) / 8 <= n / 8)).
    { pose proof (Z.div_mod n 8 ltac:(lia)). pose proof (Z.mod_pos_bound n 8 ltac:(lia)). pose proof (Z.div_mod om 8 ltac:(lia)). pose proof (Z.mod_pos_bound om 8 ltac:(lia)).
      pose proof (Z.div_mod (om + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (om + 7) 8 ltac:(lia)). lia. }
    destruct Qo as (Q1 & Q2 & Q3 & Q4 & Q5).
    destruct (Z.eq_dec (om / 8) (n / 8)) as [E|NE]; [destruct (Z.eq_dec (om mod 8) 0) as [E0|N8]|].
    - exists 252. split; [apply TOR; [lia|]; apply (F0 (n / 8)); unfold g in Hj; lia|left; reflexivity].
    - exists (om mod 8). split; [apply TOR; [lia|]; rewrite <- E; exact (P0 N8)|right; split; [lia|exact (Q2 E)]].
    - exists 252. split; [apply TOR; [lia|]; apply (F0 (n / 8)); unfold g in Hj; lia|left; reflexivity]. }
  destruct (@ann_run fx Mr0 (seg_rom ASEGS) (getr R 1) sp u (u + n) (u + om) (u + nm) SPR W2192
              ltac:(repeat split; first [lia | exact U8 | clear - K5 HI2; lia]) LAY CDCO CVP CV HAPP Hret WSH HEND R eq_refl ltac:(unfold sp; symmetry; apply Z_to_bv_bv_unsigned) H10 H11 H12 H13)
    as (R1 & Mr1 & RUN & KCS & GR1 & FR1 & FL1 & PT1).

  assert (SC1 : shadow_cont Mr1 u n nm).
  { apply (shadow_cont_step Mr0 Mr1 u n om nm ltac:(lia) U8 Hom Hnm).
    - apply (shadow_cont_tr M Mr0 u n om Hom); [|exact SC0]. intros j v Hj0 Hj Bv. unfold byte_at, Mr0, mrestrict. rewrite (VSH j); [exact Bv|]. split; [exact Hj0|]. apply (proj1 (sbw_idx_iff n j ltac:(lia))). exact Hj.
    - intros j Hj X1 X2. apply FR1.
      + rewrite art_u_lit by (clear - Hj SHR; fold g in Hj; lia). clear - Hj SHR SPR. fold g in Hj. lia.
      + rewrite art_u_lit by (clear - Hj SHR; fold g in Hj; lia). intros (NE & RG). apply X1. split; [exact NE|]. rewrite ESu in RG. unfold sstep_lo, sstep_hi. unfold ann_lo, ann_hi in RG. clear - RG. lia.
      + rewrite art_u_lit by (clear - Hj SHR; fold g in Hj; lia). intros (NE & NM & EQ). apply X2. split; [exact NE|]. split; [exact NM|]. rewrite ESu in EQ. clear - EQ. lia.
    - intros NE gi Hg. unfold HeapIfaceA.SB. exact (FL1 NE gi Hg).
    - intros NE NM. unfold HeapIfaceA.SB. exact (PT1 NE NM). }
  assert (LOHI : u / 8 <= ann_lo (u + om) (u + nm) /\ ann_hi (u + om) (u + nm) <= u / 8 + g /\ (nm mod 8 <> 0 -> nm / 8 < g) /\ 0 <= nm / 8).
  { assert (Q1 : 0 <= om / 8 /\ 0 <= nm / 8) by (split; apply Z.div_pos; lia).
    assert (Q2 : nm / 8 <= g /\ (om + 7) / 8 <= g /\ (nm + 7) / 8 <= g) by (unfold g; repeat split; apply Z.div_le_mono; lia).
    assert (Q3 : 0 <= (nm + 7) / 8) by (apply Z.div_pos; lia).
    assert (Q4 : nm mod 8 <> 0 -> nm / 8 < (nm + 7) / 8) by (pose proof (Z.div_mod nm 8 ltac:(lia)); pose proof (Z.mod_pos_bound nm 8 ltac:(lia)); pose proof (Z.div_mod (nm + 7) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (nm + 7) 8 ltac:(lia)); lia).
    unfold ann_lo, ann_hi. rewrite <- !Z.add_assoc. rewrite !(sstep_div u _ U8). destruct (u + om <? u + nm); clear - Q1 Q2 Q3 Q4; lia. }
  destruct LOHI as (LO1 & HI1' & PT1' & NM0).
  assert (GEOX : (rn_t rn + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= rn_t rn) /\ (ar_fs (rn_ar rn) + FS_BYTES <= 0x7fff7000 \/ 0x10007fff8000 <= ar_fs (rn_ar rn))
                 /\ (rn_dtls rn + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= rn_dtls rn) /\ rn_tp rn + 16 <= 0x7fff7000
                 /\ (0x10000 <= rn_tp rn + rn_loff rn /\ rn_tp rn + rn_loff rn + 4 <= 0x6b3000)).
  { pose proof ROK as ROK'. rok_open ROK'. geo_open GEO. destruct Fapp as (_ & Fap & _). destruct D3 as (_ & D3a & _). unfold BIGSHADOW_LO, BIGSHADOW_HI in *.
    split; [exact G10|]. split; [exact Fap|]. split; [exact D3a|]. split; [clear - G20; lia|]. split; assumption. }
  destruct GEOX as (Gt & Gf & Gd & Gtp & GL).
  set (FP := fun x => sp - 2192 <= x < sp \/ in_shadow_of u n x).
  assert (FPSHR : forall x, in_shadow_of u n x -> 0x7fff8000 <= x < 0x10007fff8000) by (intros x (X1 & X2); rewrite Eend in X2; clear - X1 X2 SHR Qg; lia).
  apply (art_wrap_pure2s MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Hwx Kt R (Z_to_bv 64 0x82c5c) M model G LB FF LK cr A FP u n
           (fun fx' R' pc1 Mr' => fx' = fx /\ pc1 = getr R 1 /\ keeps_cs R R' /\ shadow_cont Mr' u n nm) REPr FS B0 CRED CLI KN LZ EG HB).
  - exists fx, R1, (getr R 1), Mr1. split. { replace (Z_to_bv 64 0x82c5c : word) with (0x82c5c%bv : word) by (apply bv_eq; reflexivity). exact RUN. }
    split; [exact GR1|].
    split. { intros x NF. apply FR1; [intros X; apply NF; left; exact X| |].
             - intros (_ & RG). apply NF. right. unfold in_shadow_of. rewrite Eend, ESu. clear - RG LO1 HI1'. lia.
             - intros (_ & NM & EQ). apply NF. right. unfold in_shadow_of. rewrite Eend, ESu. rewrite (sstep_mod u nm U8) in NM. rewrite (sstep_div u nm U8) in EQ. specialize (PT1' NM). clear - EQ PT1' NM0. lia. }
    split. { apply (art_cell_agree ASEGS Mr0 Mr1 _ 4%nat 0); [|clear - GL; lia|cbn; clear - GL; lia|exact LSAN0].
             intros x Hx. cbn in Hx. apply FR1; [clear - Hx GL SPR; lia| |].
             - intros (_ & RG). clear - RG Hx GL LO1 K1. assert (0 <= u / 8) by (apply Z.div_pos; lia). lia.
             - intros (_ & _ & EQ). rewrite (sstep_div u nm U8) in EQ. clear - EQ Hx GL NM0 K1. assert (0 <= u / 8) by (apply Z.div_pos; lia). lia. }
    split; [exists nm; split; [exact Hnm|exact SC1]|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact KCS|exact SC1].
  -
    intros x [Hx | Hx] Z; [exfalso|right; exact Hx].
    pose proof (art_zone_below MAPS0 RESV0 NOACC0 BASE BUDGET rn G LB A M Mr0 model x REPr KN B0 (or_introl Z)) as ZB. clear - ZB Hx SHI. lia.
  -
    intros x HF Z3. exfalso. pose proof (art_fs_zone3_below rn G LB _ x REPr Z3) as ZB.
    destruct HF as [Hx | Hx]; [clear - ZB Hx SHI; lia |]. apply FPSHR in Hx.
    unfold fs_zone3 in Z3. clear - Z3 Hx Gt Gf Gtp. unfold FS_BYTES in *. lia.
  -
    intros x HF Zc. pose proof (art_cs_zone_below rn G LB FF LK M Mr0 x REPr FS Zc) as ZB.
    destruct HF as [Hx | Hx]; [clear - ZB Hx SHI; lia |]. pose proof (FPSHR x Hx) as RX.
    unfold cs_zone in Zc. destruct Zc as [Zc|[Zc|[Zc|[Zc|Zc]]]]; [clear - Zc RX; lia|clear - Zc RX; lia|clear - Zc RX Gtp; lia|clear - Zc RX Gd; lia|].
    destruct Hx as (X1 & X2). change (HeapIfaceA.S 0x10000) with 2147459072 in Zc. change (HeapIfaceA.S 0x6b3000) with 2148328960 in Zc.
    destruct K2 as [Lo|Hi].
    + assert (HeapIfaceA.S (u + n - 1) < 2147459072); [|clear - H X2 Zc; lia]. unfold HeapIfaceA.S, HeapIfaceA.SB. assert ((u + n - 1) / 8 < 8192) by (apply Z.div_lt_upper_bound; clear - Lo; lia). lia.
    + pose proof (art_S_mono _ _ Hi) as MM. change (HeapIfaceA.S 7024640) with 2148328960 in MM. clear - MM X1 Zc. lia.
  -
    intros b x Hb Nb Hx HF. pose proof (art_block_shadow_below rn LB FF LK A M b x CLI Hb Hx) as B1.
    destruct HF as [X | X]; [clear - X B1 SHI HI1; lia|].
    destruct (CB b Hb) as (Kb1 & _ & Kb3 & Kb4 & _ & _ & _ & _ & _ & Kb10 & _).
    pose proof (Kb10 (u, n) (art_lb_remove_keep (fst b) LB (u, n) HB ltac:(cbn [fst]; intros E; apply Nb; symmetry; exact E))) as AP. cbn [fst snd] in AP.
    assert (B8 : fst b mod 8 = 0).
    { pose proof (Z.div_mod (fst b) 16 ltac:(lia)) as D. rewrite Kb3, Z.add_0_r in D. rewrite D. replace (16 * (fst b / 16)) with ((2 * (fst b / 16)) * 8) by ring. apply Z_mod_mult. }
    destruct Hx as (Y1 & Y2). destruct X as (X1 & X2). unfold HeapIfaceA.S in *.
    pose proof (Z.div_mod u 8 ltac:(lia)) as Du. rewrite U8, Z.add_0_r in Du. pose proof (Z.div_mod (fst b) 8 ltac:(lia)) as Db. rewrite B8, Z.add_0_r in Db.
    destruct AP as [AP|AP].
    + assert ((fst b + snd b - 1) / 8 < u / 8) by (apply Z.div_lt_upper_bound; [lia|]; clear - AP Du; lia). clear - H Y2 X1. lia.
    + assert ((u + n - 1) / 8 < fst b / 8) by (apply Z.div_lt_upper_bound; [lia|]; clear - AP Db; lia). clear - H Y1 X2. lia.
  -
    intros fx2 R' pc1 Mr' M1 model' (Efx & Epc & KCS' & SCr) RI' GROW FRM VIS1 HID RT MI'. subst pc1 fx2.
    apply (CONT R' M1 model' (keeps_cs_preserved R R' KCS')); [ | | | exact GROW | exact RT | exact MI' | exact RI'].
    + apply (shadow_cont_tr Mr' M1 u n nm Hnm); [|exact SCr]. intros j v Hj0 Hj Bv. unfold byte_at in *. rewrite VIS1; [exact Bv|].
      apply VSH. split; [exact Hj0|]. apply (proj1 (sbw_idx_iff n j ltac:(lia))). exact Hj.
    + intros a Ra Ha NS. apply FRM. rewrite art_u_lit by exact Ra. unfold FP. intros [X | X]; [|exact (NS X)].
      apply (art_cls_off_scratch rn LB FF LK A M CLI L HLlo HLhi (g_fs art_fsg G) FS sp 4096 a ltac:(clear - SHI; lia) (or_intror Ha)). clear - X. lia.
    + intros a Ha. apply GROW.
      assert (WM : wrA M (sp - 4096) 4096) by (intros d m0 Hd Hm; apply SWR; assumption).
      pose proof (art_wr_wview ASEGS M (sp - 4096) 4096 ltac:(clear - SHI HI1; lia) ltac:(clear - SPR; lia) WM (Z_to_bv 64 a)) as Vw. rewrite art_u_lit in Vw by (clear - Ha SPR; lia). specialize (Vw ltac:(clear - Ha; lia)).
      rewrite art_wview_off in Vw by (rewrite art_u_lit by (clear - Ha SPR; lia); right; clear - Ha SHI HI1; lia). exact Vw.
Qed.
End WAN.
