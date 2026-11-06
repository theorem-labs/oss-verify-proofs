(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct RefMemcpyLib MemSplit HeapIface HeapIfaceA PmHeapIfaceA ArtMem ArtRuns ArtRunsMem Pm9ArtCls Pm9ArtLeaf Pm9ArtCellEx Pm9ArtImgCell Pm9ArtPoison
     ArtBridge Pm9ArtInv Pm9ArtInvMalloc Pm9ArtLift Pm9ArtWrapKit Pm9ArtFsInv Pm9ArtFsInvLaws Pm9ArtIfaceLaws Pm9ArtInvFrame Pm9ArtIfaceFrame Pm9RegionPoisoned Pm9StackFree5 AsanPlanSoundSums.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import Pm9ArtWrapC Pm9ArtWrapVis Pm9ArtWrapC2 Pm9ArtWrapRng Pm9ArtSmallocKit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Section WSF.
Variables MAPS0 RESV0 NOACC0 : list (word * word).
Variables BASE BUDGET : Z.
Variable rn : art_run.
Variable scfg : SpuriousCfg.
Hypothesis Hwx : wx_segs_nowrap ASEGS.
Variable L : asan_layout.
Hypothesis HLsegs : hl_segs L = ASEGS.
Hypothesis HLlo : hl_img_lo L = 0x10000.
Hypothesis HLhi : hl_img_hi L = 0x6b4000.
#[local] Abbreviation RI := (art_ri_inv art_fsg MAPS0 RESV0 NOACC0 BASE BUDGET art_fsinv rn).
Context {fx : PropExec.FPState}.

Theorem art_wrap_sfree5 : forall (R : bvmap 5 word) (M : word -> option byte) (model : Model)
    (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (F rs : Z) (K : ShapeAlg.TSet),
  let sp := U (getr R 2) in
  RI LB FF LK cr A M (vml_of model) -> m_halted model = None -> MInv A model ->
  In (F, 5, rs) FF -> getr R 10 = Z_to_bv 64 F ->
  getr R 4 = Z_to_bv 64 (rn_tp rn) -> Hoare.ret_ok (getr R 1) ->
  astack_ok L (rn_ar rn) M 512 sp ->
  (forall a, 0x103a8 <= a < 0x103a8 + 8 -> M (Z_to_bv 64 a) = None) ->
  K [] ->
  (forall (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model),
      regs_preserved R R' ->
      (forall j, 0 <= j < ff_bytes 5 / 8 -> byte_at M' (HeapIfaceA.S F + j) FS_AFTER_RETURN) ->
      (forall a, 0 <= a < 2 ^ 64 -> aclient L (rn_ar rn) LB FF sp 512 a -> ~ in_shadow_of F (ff_bytes 5) a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
      (forall a, sp - 512 <= a < sp -> M' (Z_to_bv 64 a) <> None) ->
      (forall a : word, M a <> None -> M' a <> None) ->
      model_rt model model' -> MInv A model' ->
      RI LB (ff_remove F FF) LK cr A M' (vml_of model') ->
      srealizes ASEGS scfg (mkCfg (mkst R' (getr R 1) M' (seg_rom ASEGS)) model') K) ->
  srealizes ASEGS scfg (mkCfg (mkst R (0x65888 : word) M (seg_rom ASEGS)) model) K.
Proof.
  intros R M model LB FF LK cr A F rs K sp INV Hhalt HMI HIN H10 H4 Hret AST ROC KT0 CONT.
  destruct (art_ri_open MAPS0 RESV0 NOACC0 BASE BUDGET rn LB FF LK cr A M model INV Hhalt HMI) as (G & REPr & FS & B0 & CRED & CLI & KN & LZ & EG).
  set (Mr0 := mrestrict (bhid A model) M) in *.
  destruct AST as (S16 & SHI & SLE & STOP & SWR & SDEF). fold sp in S16, SHI, SLE, SWR, SDEF. rewrite HLsegs in SWR.
  assert (HIeq : ahl_ceil (rn_ar rn) = rn_HI rn) by reflexivity. rewrite HIeq in SHI.
  pose proof (art_cli_hi rn LB FF LK A M CLI) as (HI1 & HI2).
  pose proof REPr as (ROK & STAT & THR & _).
  set (fs := ar_fs (rn_ar rn)) in *.
  pose proof CLI as (CB & _ & SAst & SAfs & _). fold fs in SAfs.
  assert (HIdef : rn_HI rn = ar_sptop (rn_ar rn) - 8388608) by reflexivity.

  pose proof FS as (FGEO & WFS & _ & _ & _ & _ & _ & ND & FRS & _ & _). fold fs in WFS, FRS.
  pose proof FGEO as (Gm & _). fold fs in Gm.
  assert (GEOX : (4096 <= rn_t rn /\ rn_t rn + 4096 <= rn_HI rn /\ (rn_t rn + 4096 <= 0x10000 \/ 0x6b4000 <= rn_t rn) /\ (rn_t rn + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= rn_t rn))
                 /\ (4096 <= rn_ctx rn /\ rn_ctx rn + 4096 <= rn_HI rn /\ (rn_ctx rn + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= rn_ctx rn))
                 /\ (0x67fbe8 <= rn_tp rn - 88 /\ rn_tp rn + 8 <= 0x6b4000 /\ 0x10000 <= rn_tsd rn /\ rn_tsd rn + 1024 <= 0x6b4000 /\ 0 <= rn_key rn < 128)
                 /\ (4096 <= fs /\ fs + FS_BYTES <= rn_HI rn /\ (fs + FS_BYTES <= 0x7fff7000 \/ 0x10007fff8000 <= fs) /\ (fs + FS_BYTES <= 0x10000 \/ 0x6b4000 <= fs))
                 /\ (0x10000 <= rn_tp rn + rn_loff rn /\ rn_tp rn + rn_loff rn + 4 <= 0x6b4000)
                 /\ (4096 <= rn_dtls rn /\ rn_dtls rn + 4096 <= rn_HI rn /\ (rn_dtls rn + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= rn_dtls rn) /\ apart (rn_dtls rn) 4096 fs FS_BYTES)).
  { pose proof ROK as ROK'. rok_open ROK'. geo_open GEO. destruct Fapp as (_ & Fap & _). unfold BIGSHADOW_LO, BIGSHADOW_HI in Fap. fold fs in Fap, Fhi, Fimg, Flo.
    destruct D3 as (_ & D3a & _). unfold BIGSHADOW_LO, BIGSHADOW_HI in D3a. fold fs in Adf.
    split; [repeat split; assumption|]. split; [repeat split; assumption|]. split; [repeat split; first [assumption | lia]|]. split; [repeat split; assumption|]. split; [split; assumption|]. repeat split; assumption. }
  destruct GEOX as ((Gt1 & Gt2 & Gt3 & Gt4) & (Gc1 & Gc2 & Gc3) & (Gp1 & Gp2 & Gs1 & Gs2 & Gk) & (Gf1 & Gf2 & Gf3 & Gf4) & (Gl1 & Gl2) & (Gd1 & Gd2 & Gd3 & Gd4)).
  unfold apart, FS_BYTES in Gd4.
  unfold FS_BYTES in Gf2, Gf3, Gf4.
  assert (Gf0 : 0x6b4000 <= fs) by (clear - Gf1 Gf4; lia).

  assert (HIN' : In (F, 5, rs) (FF ++ LK)) by (apply in_or_app; left; exact HIN).
  destruct (FRS (F, 5, rs) HIN') as (_ & (i & (Hi & EFi) & CFP) & _). unfold ff_class, ff_addr in Hi, EFi, CFP. cbn [fst snd] in Hi, EFi, CFP.
  change (ff_bytes 5) with 2048 in *.
  pose proof (fs_flag_below_frames fs 5 i ltac:(lia) Hi) as FLR. set (fl := fs_flag fs 5 i) in *.
  pose proof (fsinv_frame_in rn _ FF LK M FS (F, 5, rs) HIN') as (IN1 & IN2 & _). unfold ff_class, ff_addr in IN1, IN2. cbn [fst snd] in IN1, IN2. change (ff_bytes 5) with 2048 in IN2. fold fs in IN1, IN2. unfold FS_BYTES in IN2.
  assert (FLO : fs + 36864 <= F). { rewrite EFi. pose proof (fs_frame_above_flags fs 5 i ltac:(lia) ltac:(lia)) as AB. lia. }
  assert (F8 : F = 8 * (F / 8)).
  { rewrite EFi. unfold fs_frame. change (ff_bytes 5) with 2048. pose proof (Z.div_mod fs 4096 ltac:(lia)) as D. rewrite Gm, Z.add_0_r in D. rewrite D.
    replace (4096 * (fs / 4096) + 4096 + 32768 + 5 * 2 ^ 20 + i * 2048) with ((512 * (fs / 4096) + 4608 + 5 * 2 ^ 17 + i * 256) * 8) by (change (2 ^ 20) with 1048576; change (2 ^ 17) with 131072; ring).
    rewrite Z.div_mul by lia. ring. }
  set (sh := HeapIfaceA.S F).
  assert (LAZY : forall w : word, page_in_ranges (page_base w) (m_vm_lazy model) = true ->
            0x6b4000 <= U w /\ U w < rn_HI rn /\ ~ in_block LB (U w) /\ ~ (ar_fs (rn_ar rn) <= U w < ar_fs (rn_ar rn) + FS_BYTES)).
  { intros w Hw. destruct LZ as (L1 & _). destruct (art_lazy_zone_bounds art_fsg rn G (U w) ROK (L1 w Hw)) as (B1 & B2).
    split; [lia|]. split; [exact (proj2 B1)|]. split; [|exact B2]. intros (b & Hb & Hr). rewrite (proj2 EG b w Hb Hr) in Hw. discriminate Hw. }
  assert (VFS : forall x : word, fs <= U x < fs + 11571200 -> bhid A model x = false).
  { intros x Hx. apply (art_vis_byte rn LB A model LAZY). right; right; right. unfold FS_BYTES. exact Hx. }
  assert (VIMG : forall x : word, U x < 0x6b4000 -> bhid A model x = false).
  { intros x Hx. apply (art_vis_byte rn LB A model LAZY). left. exact Hx. }

  pose proof (art_S_lo fs ltac:(clear - Gf1; lia)) as SLfs. pose proof (art_S_hi (fs + 11571200) ltac:(clear - Gf2 HI2; lia)) as SHfs0.
  assert (FS8 : fs = 8 * (fs / 8)).
  { assert (D : fs = 4096 * (fs / 4096)) by (pose proof (Z.div_mod fs 4096 ltac:(lia)) as D; clear - D Gm; lia).
    rewrite D at 2. replace (4096 * (fs / 4096)) with (512 * (fs / 4096) * 8) by ring. rewrite Z.div_mul by lia. clear - D. lia. }
  assert (FS8' : 8 * ((fs + 11571200) / 8) = fs + 11571200).
  { rewrite FS8 at 1. replace (8 * (fs / 8) + 11571200) with ((fs / 8 + 1446400) * 8) by ring. rewrite Z.div_mul by lia. clear - FS8. lia. }
  assert (SHR : HeapIfaceA.S fs <= sh /\ sh + 256 <= HeapIfaceA.S (fs + 11571200)).
  { unfold sh, HeapIfaceA.S. rewrite F8. rewrite <- FS8'. rewrite FS8 at 1. replace (8 * (F / 8)) with (F / 8 * 8) by ring. replace (8 * (fs / 8)) with (fs / 8 * 8) by ring.
    replace (8 * ((fs + 11571200) / 8)) with ((fs + 11571200) / 8 * 8) by ring. rewrite !Z.div_mul by lia.
    assert (fs / 8 <= F / 8) by (apply Z.div_le_mono; clear - FLO; lia). assert (F / 8 + 256 <= (fs + 11571200) / 8).
    { apply Z.div_le_lower_bound; [lia|]. rewrite F8 in IN2. clear - IN2. lia. }
    clear - H H0. lia. }
  assert (VSHF : forall x : word, HeapIfaceA.S fs <= U x < HeapIfaceA.S (fs + 11571200) -> bhid A model x = false).
  { intros x Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply (art_vis_shadow A model fs FS_BYTES _ SAfs). unfold in_shadow_of, FS_BYTES.
    assert (E : HeapIfaceA.S (fs + 11571200 - 1) = HeapIfaceA.S (fs + 11571200) - 1).
    { unfold HeapIfaceA.S. rewrite FS8. replace (8 * (fs / 8) + 11571200 - 1) with (7 + (fs / 8 + 1446399) * 8) by ring. replace (8 * (fs / 8) + 11571200) with ((fs / 8 + 1446400) * 8) by ring.
      rewrite Z.div_add, Z.div_mul by lia. change (7 / 8) with 0. ring. }
    rewrite E. clear - Hx. lia. }
  assert (WSHF : wrA Mr0 (HeapIfaceA.S fs) (HeapIfaceA.S (fs + 11571200) - HeapIfaceA.S fs)).
  { apply (art_wr_of_defined ASEGS Mr0); [clear - SLfs; lia | clear - SHfs0; lia |]. intros x Hx. unfold Mr0, mrestrict. rewrite (VSHF x ltac:(clear - Hx; lia)).
    apply (bi_shdef _ _ _ _ _ _ _ _ _ _ _ B0 x). unfold in_shadow_rw, LSH_LO, LSH_HI, HSH_LO, HSH_HI. destruct Gf3 as [LOW | HIGH].
    - left. pose proof (art_S_mono _ _ LOW) as MM. change (HeapIfaceA.S 2147446784) with 2415881728 in MM. clear - Hx SLfs MM. lia.
    - right. pose proof (art_S_mono _ _ HIGH) as MM. change (HeapIfaceA.S 17594333495296) with 2201439137792 in MM. clear - Hx SHfs0 MM. lia. }
  assert (SHAPP : sh + 256 <= 0x10007fff8000 /\ 0x7fff8000 <= sh).
  { destruct SHR as (S1 & S2). unfold HeapIfaceA.S, HeapIfaceA.SB in *. assert (0 <= fs / 8) by (apply Z.div_pos; lia). clear - S1 S2 SHfs0 H. unfold HeapIfaceA.S, HeapIfaceA.SB in SHfs0. lia. }
  assert (SHIMG : 2148329472 <= sh). { destruct SHR as (S1 & _). pose proof (art_S_mono _ _ Gf0) as MM. change (HeapIfaceA.S 0x6b4000) with 2148329472 in MM. clear - S1 MM. lia. }
  assert (GL : 0x10000 <= rn_tp rn + rn_loff rn /\ rn_tp rn + rn_loff rn + 4 <= 0x6b4000) by (split; [exact Gl1 | exact Gl2]).
  assert (ESH : sh = (Pm9RegionPoisoned.SB + F / 8)%Z) by (unfold sh, HeapIfaceA.S, HeapIfaceA.SB, Pm9RegionPoisoned.SB; ring).
  assert (HAPP0 : in_app F) by (unfold in_app, LOWEND, HIGHBEG, HIGHEND; clear - FLO IN2 Gf1 Gf2 Gf3 HI2; lia).
  assert (HSf0 : (0x6b4000 <= F)%Z /\ (F + 2048 <= sp - 16 \/ sp <= F)%Z) by (clear - FLO Gf0 IN2 Gf2 SHI; lia).
  assert (HFl0 : (0x6b4000 <= fl)%Z /\ (fl + 1 < 2 ^ 64)%Z /\ (fl + 1 <= sp - 16 \/ sp <= fl)%Z) by (clear - FLR Gf0 Gf2 HI2 SHI; lia).
  assert (HSs0 : (0x1000000 <= sp - 16)%Z /\ (sp < 2 ^ 64)%Z) by (clear - SHI HI1 SLE HI2 HIdef; lia).
  assert (HShdj0 : (sh + 256 <= sp - 16 \/ sp <= sh)%Z) by (left; clear - SHAPP SHI HI1; lia).
  assert (HFlsh0 : (fl + 1 <= sh \/ sh + 256 <= fl)%Z).
  { destruct Gf3 as [LOW | HIGH]; [left; clear - LOW FLR SHAPP; lia | right; clear - HIGH FLR SHAPP; lia]. }
  set (FP := fun x => sp - 16 <= x < sp \/ x = fl \/ sh <= x < sh + 256).
  apply (art_wrap_pure3 MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Hwx (art_alloc_rep_frame_law_proved art_fsg MAPS0 RESV0) K R (0x65888 : word) M model G LB FF LK cr A FP
           (fun R' pc1 Mr' => pc1 = getr R 1 /\ keeps_cs R R' /\ Mr' = sf5_mem Mr0 (getr R 1) sp fl sh PATV R)
           (g_fs art_fsg G) (ff_remove F FF) LK REPr FS B0 CRED CLI KN LZ EG).
  -
    assert (W0 : wrA Mr0 (sp - 512) 512).
    { apply (art_stack_wr art_fsg rn G A (m_vm_lazy model) M sp 512 ROK LZ ltac:(clear - SHI; lia) ltac:(clear; lia) ltac:(clear - SLE HI2 HIdef; lia)). exact SWR. }
    assert (HOK : store_ok ASEGS Mr0 (Z_to_bv 64 (sp - 16)) 16 = true).
    { replace (sp - 16) with (sp - 512 + 496) by ring. apply W0; [lia | cbn; lia]. }
    assert (WFSr : wrA Mr0 fs 11571200).
    { apply (proj2 (art_wr_vis (bhid A model) M fs 11571200 ltac:(clear - Gf1; lia) ltac:(clear - Gf2 HI2; lia) ltac:(intros x Hx; apply VFS; exact Hx))). exact WFS. }
    assert (CFPr : cellA Mr0 (F + 2048 - 8) 8 fl).
    { apply (proj2 (art_cell_vis (bhid A model) M (F + 2048 - 8) 8 fl ltac:(clear - IN1 Gf1; lia) ltac:(cbn; clear - IN2 Gf2 HI2; lia) ltac:(intros x Hx; apply VFS; cbn in Hx; clear - Hx IN1 IN2; lia))). exact CFP. }
    replace (F + 2048 - 8) with (F + 2040) in CFPr by ring. unfold cell in CFPr.
    destruct STAT as (_ & LAY & _).
    assert (HGr : rt_layout_globs Mr0).
    { destruct LAY as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & _). unfold rt_layout_globs.
      repeat split; [lit_cell A1 | lit_cell A2 | lit_cell A3 | lit_cell A4 | lit_cell A5 | lit_cell A6 | lit_cell A7 | lit_cell A8]. }
    assert (HFLOK : store_ok ASEGS Mr0 (Z_to_bv 64 fl) 1 = true).
    { replace fl with (fs + (fl - fs)) by ring. apply WFSr; [clear - FLR; lia | cbn; clear - FLR; lia]. }
    assert (HSHOK : store_ok ASEGS Mr0 (Z_to_bv 64 sh) 256 = true).
    { replace sh with (HeapIfaceA.S fs + (sh - HeapIfaceA.S fs)) by ring. apply WSHF; [clear - SHR; lia | cbn; clear - SHR; lia]. }
    assert (HPAT : forall M' : word -> option byte, (forall x : word, (U x < 0x6b4000)%Z -> M' x = Mr0 x) -> rdn ASEGS M' (0x103a8 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 PATV))).
    { intros M' AG. apply sf5_pat_read. intros x Hx. rewrite (AG x ltac:(clear - Hx; lia)). unfold Mr0, mrestrict. destruct (bhid A model x); [reflexivity|].
      rewrite <- (Z_to_bv_bv_unsigned 64 x). apply ROC. exact Hx. }
    destruct (@sfree5_run fx Mr0 (seg_rom ASEGS) (getr R 2) (getr R 1) sp F fl sh PATV eq_refl Hret HSs0 HOK HGr HAPP0 HSf0 ESH CFPr HFl0 HFLOK HSHOK HShdj0 HPAT R H10 eq_refl eq_refl)
      as (R' & RUN & Q2 & Q1 & Q8 & KB).
    destruct (@sfree5_desc Mr0 (getr R 1) sp F fl sh PATV HSs0 HAPP0 HSf0 ESH HFl0 HShdj0 HFlsh0 R eq_refl) as (DG & DO & DFL & DSH).
    assert (FRr : forall x : word, ~ FP (U x) -> sf5_mem Mr0 (getr R 1) sp fl sh PATV R x = Mr0 x).
    { intros x Hx. apply DO. unfold sf5_fp. exact Hx. }
    exists R', (getr R 1), (sf5_mem Mr0 (getr R 1) sp fl sh PATV R). split; [exact RUN|]. split; [exact DG|]. split; [exact FRr|].
    split.
    { destruct THR as (_ & _ & _ & _ & _ & _ & _ & LSAN0). apply (Pm9ArtAllocG.cell_agree Mr0 _); [| clear - GL; lia | cbn; clear - GL; lia | exact LSAN0].
      intros x Hx. cbn in Hx. apply FRr. unfold FP. clear - Hx GL SHI HI1 FLR Gf0 SHAPP. lia. }
    split; [reflexivity|]. split; [|reflexivity].
    apply (sf5_keeps_cs R R' KB Q1 Q2 Q8).
  -
    intros x [Hx | [Hx | Hx]] Z; exfalso.
    + pose proof (art_zone_below MAPS0 RESV0 NOACC0 BASE BUDGET rn G LB A M Mr0 model x REPr KN B0 (or_introl Z)) as ZB. clear - ZB Hx SHI. lia.
    + apply (art_zone_off_fs MAPS0 RESV0 NOACC0 BASE BUDGET rn G LB A M Mr0 model x REPr KN B0 Z). fold fs. unfold FS_BYTES. clear - Hx FLR. lia.
    + apply (art_zone_off_fs_shadow MAPS0 RESV0 NOACC0 BASE BUDGET rn G LB A M Mr0 model x REPr KN B0 Z). fold fs. unfold FS_BYTES. clear - Hx SHR. lia.
  -
    intros b x Hb Hx HF. pose proof (art_block_shadow_below rn LB FF LK A M b x CLI Hb Hx) as B1.
    destruct (CB b Hb) as (K1 & _ & _ & K4 & K5 & _ & _ & _ & _ & _ & _ & K12 & _). fold fs in K12. unfold FS_BYTES in K12.
    pose proof (art_S_lo (fst b) ltac:(clear - K1; lia)) as B2. pose proof Hx as (Hx1 & _).
    destruct HF as [X | [X | X]]; [clear - X B1 SHI HI1; lia | clear - X Hx1 B1 B2 Gf3 FLR; lia |].
    exact (art_shadow_apart (fst b) (snd b) fs 11571200 x (eq_sym FS8) FS8' K4 K12 Hx ltac:(clear - X SHR; lia)).
  -
    intros R' pc1 Mr' M1 (Epc & KCS & EM) GROW FR1 VIS1.
    destruct (@sfree5_desc Mr0 (getr R 1) sp F fl sh PATV HSs0 HAPP0 HSf0 ESH HFl0 HShdj0 HFlsh0 R eq_refl) as (DG & DO & DFL & DSH).
    split.
    + apply (art_fsinv_release_proved rn (g_fs art_fsg G) FF LK M M1 F 5 rs FS HIN GROW).
      * exists i. split; [exact Hi|]. split; [exact EFi|]. fold fs. fold fl. split.
        -- apply (Pm9ArtAllocG.cell_agree Mr' M1); [| clear - FLR Gf1; lia | cbn; clear - FLR Gf2 HI2; lia |].
           ++ intros x Hx. cbn in Hx. apply VIS1. apply VFS. clear - Hx FLR. lia.
           ++ rewrite EM. unfold cell. rewrite Pm9ArtFsInv.le1_zero. exact DFL.
        -- intros x NE Z3 NIF. apply FR1. unfold FP. intros [X | [X | X]]; [| exact (NE X) |].
           ++ pose proof (art_fs_zone3_below rn G LB _ (U x) REPr Z3) as ZB. clear - ZB X SHI. lia.
           ++ unfold fs_zone3, FS_BYTES in Z3. fold fs in Z3. clear - Z3 X SHAPP Gf3 Gt4 Gp1 Gp2. lia.
      * intros x Zc. apply FR1. unfold FP. destruct (fsinv_cs _ _ _ _ _ FS) as ((Q1c & _) & _).
        pose proof (art_cs_zone_below rn G LB FF LK M Mr0 (U x) REPr FS Zc) as CB1.
        unfold cs_zone in Zc. change (HeapIfaceA.S 0x10000) with 2147459072 in Zc. change (HeapIfaceA.S 0x6b4000) with 2148329472 in Zc.
        intros [X | [X | X]]; [clear - CB1 X SHI; lia | clear - Zc X FLR Gf0 Gf3 Gf4 Gd4 Q1c Gp1; lia | clear - Zc X SHAPP SHIMG Q1c Gd3 Gp1; lia].
    + intros b Hb f Hf. destruct (CB b Hb) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & K11 & _). apply K11.
      apply in_app_or in Hf. apply in_or_app. destruct Hf as [Hf | Hf]; [left; eapply ff_remove_in; exact Hf | right; exact Hf].
  -
    intros R' pc1 Mr' M1 model' (Epc & KCS & EM) RI' GROW FR1 VIS1 HID RT MI'. subst pc1.
    destruct (@sfree5_desc Mr0 (getr R 1) sp F fl sh PATV HSs0 HAPP0 HSf0 ESH HFl0 HShdj0 HFlsh0 R eq_refl) as (DG & DO & DFL & DSH).
    apply (CONT R' M1 model' (keeps_cs_preserved R R' KCS)); [ | | | | exact RT | exact MI' | exact RI'].
    +
      intros j Hj. change (2048 / 8) with 256 in Hj. unfold byte_at. fold sh.
      assert (Rx : 0 <= sh + j < 2 ^ 64) by (clear - Hj SHAPP; lia).
      rewrite (VIS1 _ (VSHF (Z_to_bv 64 (sh + j)) ltac:(rewrite art_u_lit by exact Rx; clear - Hj SHR; lia))). rewrite EM. exact (DSH j Hj).
    +
      intros a Ra Ha NS. apply FR1. rewrite art_u_lit by exact Ra. unfold FP. intros [X | [X | X]].
      * apply (art_cls_off_scratch rn LB FF LK A M CLI L HLlo HLhi (g_fs art_fsg G) FS sp 512 a ltac:(clear - SHI; lia) (or_intror Ha)). clear - X. lia.
      *
        subst a.
        assert (NSH : forall y z, 0 <= y -> y + z <= 2 ^ 47 -> 0 < z -> ~ in_shadow_of y z fl).
        { intros y z Hy Hyz Hz (X1 & X2). pose proof (art_S_lo y Hy). pose proof (art_S_hi (y + z - 1) ltac:(lia)). clear - X1 X2 H H0 FLR Gf1 Gf3. lia. }
        destruct Ha as [H | [H | [H | [H | [H | [H | H]]]]]]; rewrite ?HLlo, ?HLhi in H.
        -- destruct H as (b & Hb & Rb). destruct (CB b Hb) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & K12 & _). fold fs in K12. unfold FS_BYTES in K12. clear - Rb K12 FLR. lia.
        -- rewrite HIeq in H. clear - H Gf2 FLR. lia.
        -- clear - H Gf0 FLR. lia.
        -- destruct H as (f & Hf & R1 & _). pose proof (fsinv_frame_in rn _ FF LK M FS f ltac:(apply in_or_app; left; exact Hf)) as (I1 & _).
           destruct (fsinv_slot rn _ FF LK M FS f ltac:(apply in_or_app; left; exact Hf)) as (Kf & i' & Hi' & Af).
           pose proof (fs_frame_above_flags fs (ff_class f) i' ltac:(clear - Kf; lia) ltac:(clear - Hi'; lia)) as AB. fold fs in Af. rewrite <- Af in AB. clear - R1 AB FLR. lia.
        -- apply (NSH (rn_HI rn) (2 ^ 47 - rn_HI rn) ltac:(clear - HI1; lia) ltac:(lia) ltac:(clear - HI2; lia) H).
        -- destruct H as (f & Hf & H). pose proof (fsinv_frame_in rn _ FF LK M FS f ltac:(apply in_or_app; left; exact Hf)) as (I1 & I2 & I3). fold fs in I1, I2. unfold FS_BYTES in I2.
           apply (NSH (ff_addr f) (ff_bytes (ff_class f)) ltac:(clear - I1 Gf1; lia) ltac:(clear - I2 Gf2 HI2; lia) I3 H).
        -- destruct H as (b & Hb & H). destruct (CB b Hb) as (K1 & _ & _ & K4 & K5 & _). rewrite HIeq in K5. apply (NSH (fst b) (snd b) ltac:(clear - K1; lia) ltac:(clear - K5 HI2; lia) K4 H).
      * apply NS. unfold in_shadow_of. fold sh.
        assert (E1 : HeapIfaceA.S (F + 2048 - 1) = sh + 255).
        { unfold sh, HeapIfaceA.S. rewrite F8 at 1. replace (8 * (F / 8) + 2048 - 1) with (7 + (F / 8 + 255) * 8) by ring. rewrite Z.div_add by lia. change (7 / 8) with 0. ring. }
        rewrite E1. clear - X. lia.
    + intros a Ha. apply GROW.
      assert (WM : wrA M (sp - 512) 512) by (intros d k Hd Hk; apply SWR; assumption).
      pose proof (art_wr_wview ASEGS M (sp - 512) 512 ltac:(clear - SHI HI1; lia) ltac:(clear - SLE HI2 HIdef; lia) WM (Z_to_bv 64 a)) as V. rewrite art_u_lit in V by (clear - Ha SHI HI1 SLE HI2 HIdef; lia). specialize (V ltac:(clear - Ha; lia)).
      rewrite art_wview_off in V by (rewrite art_u_lit by (clear - Ha SHI HI1 SLE HI2 HIdef; lia); right; clear - Ha SHI HI1; lia). exact V.
    + exact GROW.
Qed.
End WSF.

Lemma lit_sfree5 : Z_to_bv 64 0x65888 = (0x65888%bv : word). Proof. apply bv_eq. reflexivity. Qed.
Theorem art_asfree5 : forall MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg, wx_segs_nowrap ASEGS -> forall L : asan_layout,
  hl_segs L = ASEGS -> hl_img_lo L = 0x10000 -> hl_img_hi L = 0x6b4000 -> hl_tp L = rn_tp rn -> hl_scr_stack_malloc L = 512 ->
  astack_free_spec L (rn_ar rn) scfg (art_iface art_fsg MAPS0 RESV0 NOACC0 BASE BUDGET art_fsinv rn) 0x65888 0x103a8 5.
Proof.
  intros MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Hwx L HLsegs HLlo HLhi HLtp HLscr fx R M model LB FF LK cr A F rs K. cbv zeta.
  intros INV Hh HMI HIN H10 H4 Hret AST ROC KT0 POST. rewrite HLsegs, HLscr in *. rewrite lit_sfree5. rewrite HLtp in H4.
  apply (art_wrap_sfree5 MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Hwx L HLsegs HLlo HLhi R M model LB FF LK cr A F rs K INV Hh HMI HIN H10 H4 Hret AST ROC KT0).
  intros R' M' model' RP SH FR SD GR RT MI' RI'. exact (POST R' M' model' RP SH FR SD GR RT MI' RI').
Qed.
