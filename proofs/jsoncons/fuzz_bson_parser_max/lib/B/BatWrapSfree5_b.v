(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct RefMemcpyLib MemSplit HeapIface HeapIfaceA HeapIfaceABx ArtMem ArtRuns ArtRunsMem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatCls_b BatLeaf_b BatCellEx_b BatImgCell_b BatPoison_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtBridge. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatInv_b BatInvMalloc_b BatLift_b BatWrapKit_b BatFsInv_b BatFsInvLaws_b BatIfaceLaws_b BatInvFrame_b BatIfaceFrame_b Ba0RegionPoisoned_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatWrapC_b BatWrapVis_b BatWrapC2_b BatWrapRng_b BatSmallocKit_b BatAllocG_b BatSfree5_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Section WS.
Variables MAPS0 RESV0 NOACC0 : list (word * word).
Variables BASE BUDGET : Z.
Variable rn : art_run.
Variable scfg : SpuriousCfg.
Hypothesis Hwx : wx_segs_nowrap ASEGS.
Variable L : asan_layout.
Hypothesis HLsegs : hl_segs L = ASEGS.
Hypothesis HLlo : hl_img_lo L = 0x10000.
Hypothesis HLhi : hl_img_hi L = 0x696000.
#[local] Abbreviation RI := (art_ri_inv art_fsg MAPS0 RESV0 NOACC0 BASE BUDGET art_fsinv rn).
Context {fx : PropExec.FPState}.

#[using="Hwx HLsegs HLlo HLhi"] Theorem art_wrap_sfree5 : forall (R : bvmap 5 word) (M : word -> option byte) (model : Model)
    (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (K : ShapeAlg.TSet) (F rs : Z),
  let sp := U (getr R 2) in
  let ar := rn_ar rn in
  RI LB FF LK cr A M (vml_of model) -> m_halted model = None -> MInv A model ->
  In (F, 5, rs) FF -> getr R 10 = Z_to_bv 64 F ->
  getr R 4 = Z_to_bv 64 (rn_tp rn) -> Hoare.ret_ok (getr R 1) ->
  astack_ok L ar M 16 sp -> K [] ->
  (forall (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model),
      regs_preserved R R' ->
      (forall j, 0 <= j < ff_bytes 5 / 8 -> byte_at M' (HeapIfaceA.S F + j) 245) ->
      (forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF sp 16 a -> ~ in_shadow_of F (ff_bytes 5) a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
      (forall a, sp - 16 <= a < sp -> M' (Z_to_bv 64 a) <> None) ->
      model_rt model model' -> MInv A model' ->
      RI LB (ff_remove F FF) LK cr A M' (vml_of model') ->
      srealizes ASEGS scfg (mkCfg (mkst R' (getr R 1) M' (seg_rom ASEGS)) model') K) ->
  srealizes ASEGS scfg (mkCfg (mkst R (0x5e2e8 : word) M (seg_rom ASEGS)) model) K.
Proof.
  intros R M model LB FF LK cr A K F rs sp ar INV Hhalt HMI HF H10 H4 Hret AST KT0 CONT. subst ar.
  destruct (art_ri_open MAPS0 RESV0 NOACC0 BASE BUDGET rn LB FF LK cr A M model INV Hhalt HMI) as (G & REPr & FS & B0 & CRED & CLI & KN & LZ & EG).
  set (Mr0 := mrestrict (bhid A model) M) in *.
  destruct AST as (S16 & SHI & SLE & STOP & SWR & SDEF). fold sp in S16, SHI, SLE, SWR, SDEF. rewrite HLsegs in SWR.
  assert (HIeq : ahl_ceil (rn_ar rn) = rn_HI rn) by reflexivity. rewrite HIeq in SHI.
  pose proof (art_cli_hi rn LB FF LK A M CLI) as (HI1 & HI2).
  pose proof REPr as (ROK & STAT & THR & _).
  set (fs := ar_fs (rn_ar rn)) in *.
  pose proof CLI as (CB & _ & SAst & SAfs & C5 & C6 & C7 & C8 & C9 & _). fold fs in SAfs. rewrite HIeq in C5, C6, SAst.
  assert (HIdef : rn_HI rn = ar_sptop (rn_ar rn) - 8388608) by reflexivity.
  (* [comment removed for export] *)
  assert (GEOX : (4096 <= fs /\ fs + FS_BYTES <= rn_HI rn /\ (fs + FS_BYTES <= 0x7fff7000 \/ 0x10007fff8000 <= fs) /\ (fs + FS_BYTES <= 0x10000 \/ 0x696000 <= fs))
                 /\ (0x10000 <= rn_tp rn + rn_loff rn /\ rn_tp rn + rn_loff rn + 4 <= 0x696000)
                 /\ (apart (rn_dtls rn) 4096 fs FS_BYTES /\ (rn_dtls rn + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= rn_dtls rn))
                 /\ (4096 <= rn_t rn /\ rn_t rn + 4096 <= rn_HI rn /\ (rn_t rn + 4096 <= 0x10000 \/ 0x696000 <= rn_t rn) /\ (rn_t rn + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= rn_t rn))
                 /\ (0x661b28 <= rn_tp rn - 88 /\ rn_tp rn + 8 <= 0x696000)).
  { pose proof ROK as ROK'. rok_open ROK'. geo_open GEO. destruct Fapp as (_ & Fap & _). unfold BIGSHADOW_LO, BIGSHADOW_HI in Fap. fold fs in Fap, Fhi, Fimg, Flo, Adf.
    destruct D3 as (_ & D3a & _). unfold BIGSHADOW_LO, BIGSHADOW_HI in D3a.
    repeat split; first [assumption | lia]. }
  destruct GEOX as ((Gf1 & Gf2 & Gf3 & Gf4) & (Gl1 & Gl2) & (Gd4 & Gd3) & (Gt1 & Gt2 & Gt3 & Gt4) & (Gp1 & Gp2)).
  unfold apart, FS_BYTES in Gd4. unfold FS_BYTES in Gf2, Gf3, Gf4.
  assert (Gf0 : 0x696000 <= fs) by (clear - Gf1 Gf4; lia).
  assert (LAZY : forall w : word, page_in_ranges (page_base w) (m_vm_lazy model) = true ->
            0x696000 <= U w /\ U w < rn_HI rn /\ ~ in_block LB (U w) /\ ~ (ar_fs (rn_ar rn) <= U w < ar_fs (rn_ar rn) + FS_BYTES)).
  { intros w Hw. destruct LZ as (L1 & _). destruct (art_lazy_zone_bounds art_fsg rn G (U w) ROK (L1 w Hw)) as (B1 & B2).
    split; [lia|]. split; [exact (proj2 B1)|]. split; [|exact B2]. intros (b & Hb & Hr). rewrite (proj2 EG b w Hb Hr) in Hw. discriminate Hw. }
  assert (VFS : forall x : word, fs <= U x < fs + 11571200 -> bhid A model x = false).
  { intros x Hx. apply (art_vis_byte rn LB A model LAZY). right; right; right. unfold FS_BYTES. exact Hx. }
  (* [comment removed for export] *)
  pose proof FS as (FGEO & WFS & _ & _ & _ & _ & _ & ND & FRS & FLG & CST). fold fs in WFS, FRS, FLG.
  destruct (FRS (F, 5, rs) ltac:(apply in_or_app; left; exact HF)) as (KC5 & (i & (SLi & SLa) & CSF) & _).
  unfold ff_class, ff_addr in SLi, SLa, CSF. cbn [fst snd] in SLi, SLa, CSF.
  set (fl := fs_flag fs 5 i) in *.
  pose proof (fs_flag_range fs 5 i ltac:(lia) SLi) as FLR. fold fl in FLR. unfold fs_nfr in FLR. change (2 ^ (14 - 5)) with 512 in FLR.
  pose proof (fs_frame_range fs 5 i ltac:(lia) SLi) as (FRR1 & FRR2). rewrite <- SLa in FRR1, FRR2. change (ff_bytes 5) with 2048 in FRR2.
  assert (F8 : F mod 8 = 0).
  { rewrite SLa. unfold fs_frame. change (ff_bytes 5) with 2048. change (2 ^ 20) with 1048576.
    pose proof FGEO as (Gm & _). fold fs in Gm. assert (D : fs = 4096 * (fs / 4096)) by (pose proof (Z.div_mod fs 4096 ltac:(lia)) as D; clear - D Gm; lia).
    rewrite D. replace (4096 * (fs / 4096) + 4096 + 32768 + 5 * 1048576 + i * 2048) with ((512 * (fs / 4096) + 512 + 4096 + 5 * 131072 + i * 256) * 8) by ring. apply Z_mod_mult. }
  assert (ESF : HeapIfaceA.S F = Ba0RegionPoisoned_b.SB + F / 8) by (unfold HeapIfaceA.S, HeapIfaceA.SB, Ba0RegionPoisoned_b.SB; ring).
  (* [comment removed for export] *)
  assert (W0 : wrA Mr0 (sp - 16) 16).
  { apply (art_stack_wr art_fsg rn G A (m_vm_lazy model) M sp 16 ROK LZ ltac:(clear - SHI; lia) ltac:(clear; lia) ltac:(clear - SLE HI2 HIdef; lia)). exact SWR. }
  assert (WFSr : wrA Mr0 fs 11571200).
  { apply (proj2 (art_wr_vis (bhid A model) M fs 11571200 ltac:(clear - Gf1; lia) ltac:(clear - Gf2 HI2; lia) ltac:(intros x Hx; apply VFS; exact Hx))). exact WFS. }
  assert (FSV : forall a (n : nat) v, cellA M a n v -> fs <= a -> a + Z.of_nat n <= fs + 11571200 -> cellA Mr0 a n v).
  { intros a n v C A1 A2. apply (proj2 (art_cell_vis (bhid A model) M a n v ltac:(clear - A1 Gf1; lia) ltac:(clear - A2 Gf2 HI2; lia) ltac:(intros x Hx; apply VFS; clear - Hx A1 A2; lia))). exact C. }
  assert (CF0 : cellA Mr0 (F + 2040) 8 fl) by (apply FSV; [replace (F + 2040) with (F + ff_bytes 5 - 8) by (change (ff_bytes 5) with 2048; ring); exact CSF|clear - FRR1; lia|cbn; clear - FRR2; lia]).
  assert (WFL : wrA Mr0 fl 1) by (intros d k Hd Hk; replace (fl + d) with (fs + (fl - fs + d)) by ring; apply WFSr; clear - Hd Hk FLR; lia).
  destruct STAT as (PC & LAY & TSD & _ & _ & _ & TLSG & S8).
  assert (CR : cellA Mr0 0x10380 8 SF5W) by (unfold SF5W; conj_find S8).
  destruct THR as (WT & _ & _ & _ & _ & _ & _ & LSAN0).
  (* [comment removed for export] *)
  pose proof (art_S_lo fs ltac:(clear - Gf1; lia)) as SLfs. pose proof (art_S_hi (fs + 11571200) ltac:(clear - Gf2 HI2; lia)) as SHfs0.
  assert (SHfs : HeapIfaceA.S (fs + 11571200) <= 0x10007fff8000) by (clear - SHfs0; lia).
  assert (FS8 : fs = 8 * (fs / 8)).
  { pose proof FGEO as (Gm & _). fold fs in Gm. assert (D : fs = 4096 * (fs / 4096)) by (pose proof (Z.div_mod fs 4096 ltac:(lia)) as D; clear - D Gm; lia).
    rewrite D at 2. replace (4096 * (fs / 4096)) with (512 * (fs / 4096) * 8) by ring. rewrite Z.div_mul by lia. clear - D. lia. }
  assert (FS8' : 8 * ((fs + 11571200) / 8) = fs + 11571200).
  { rewrite FS8 at 1. replace (8 * (fs / 8) + 11571200) with ((fs / 8 + 1446400) * 8) by ring. rewrite Z.div_mul by lia. clear - FS8. lia. }
  assert (VSHF : forall x : word, HeapIfaceA.S fs <= U x < HeapIfaceA.S (fs + 11571200) -> bhid A model x = false).
  { intros x Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply (art_vis_shadow A model fs FS_BYTES _ SAfs). unfold in_shadow_of, FS_BYTES.
    assert (E : HeapIfaceA.S (fs + 11571200 - 1) = HeapIfaceA.S (fs + 11571200) - 1).
    { unfold HeapIfaceA.S. rewrite FS8. replace (8 * (fs / 8) + 11571200 - 1) with (7 + (fs / 8 + 1446399) * 8) by ring. replace (8 * (fs / 8) + 11571200) with ((fs / 8 + 1446400) * 8) by ring.
      rewrite Z.div_add, Z.div_mul by lia. change (7 / 8) with 0. ring. }
    rewrite E. clear - Hx. lia. }
  assert (WSHF : wrA Mr0 (HeapIfaceA.S fs) (HeapIfaceA.S (fs + 11571200) - HeapIfaceA.S fs)).
  { apply (art_wr_of_defined ASEGS Mr0); [clear - SLfs; lia | clear - SHfs; lia |]. intros x Hx. unfold Mr0, mrestrict. rewrite (VSHF x ltac:(clear - Hx; lia)).
    apply (bi_shdef _ _ _ _ _ _ _ _ _ _ _ B0 x). unfold in_shadow_rw, LSH_LO, LSH_HI, HSH_LO, HSH_HI. destruct Gf3 as [LOW | HIGH].
    - left. pose proof (art_S_mono _ _ LOW) as MM. change (HeapIfaceA.S 2147446784) with 2415881728 in MM. clear - Hx SLfs MM. lia.
    - right. pose proof (art_S_mono _ _ HIGH) as MM. change (HeapIfaceA.S 17594333495296) with 2201439137792 in MM. clear - Hx SHfs0 MM. lia. }
  (* [comment removed for export] *)
  assert (SF8 : 8 * (F / 8) = F) by (pose proof (Z.div_mod F 8 ltac:(lia)) as D; rewrite F8 in D; clear - D; lia).
  assert (SF8' : 8 * ((F + 2048) / 8) = F + 2048) by (rewrite <- SF8 at 1; replace (8 * (F / 8) + 2048) with ((F / 8 + 256) * 8) by ring; rewrite Z.div_mul by lia; clear - SF8; lia).
  assert (SHF : HeapIfaceA.S fs <= HeapIfaceA.S F /\ HeapIfaceA.S F + 256 <= HeapIfaceA.S (fs + 11571200)).
  { pose proof (art_S_mono fs F ltac:(clear - FRR1; lia)) as M1. pose proof (art_S_mono (F + 2048) (fs + 11571200) ltac:(clear - FRR2; lia)) as M2.
    unfold HeapIfaceA.S in *. clear - M1 M2 SF8 SF8'. lia. }
  destruct SHF as (SHF1 & SHF2).
  assert (WS : wrA Mr0 (Ba0RegionPoisoned_b.SB + F / 8) 256).
  { rewrite <- ESF. intros d k Hd Hk. replace (HeapIfaceA.S F + d) with (HeapIfaceA.S fs + (HeapIfaceA.S F - HeapIfaceA.S fs + d)) by ring. apply WSHF; clear - Hd Hk SHF1 SHF2; lia. }
  assert (HA : in_app F) by (unfold in_app, LOWEND, HIGHBEG, HIGHEND; clear - Gf1 Gf2 Gf3 HI2 FRR1 FRR2; destruct Gf3; [left|right]; lia).
  assert (Hsp2 : getr R 2 = Z_to_bv 64 sp) by (unfold sp; rewrite Z_to_bv_bv_unsigned; reflexivity).
  (* [comment removed for export] *)
  destruct (art_sfree5_run R Mr0 (seg_rom ASEGS) (getr R 1) sp F fl eq_refl Hret Hsp2 H10
              ltac:(clear - SHI HI1; lia) ltac:(clear - SLE STOP C8 HIdef; lia) HA ltac:(clear - FRR1 Gf0; lia) ltac:(clear - FRR2 Gf2 HI2; lia) ltac:(clear - FLR Gf0 Gf2 HI2; lia)
              W0 ltac:(unfold apart; clear - FRR2 Gf2 SHI; lia) ltac:(unfold apart; clear - FLR Gf2 SHI; lia) CF0 WFL LAY CR WS
              ltac:(unfold apart; rewrite <- ESF; clear - SHF2 SHfs SHI HI1; lia) ltac:(unfold apart; rewrite <- ESF; clear - SHF1 SHF2 SLfs SHfs FLR Gf3; lia))
    as (R' & RUN & KCS).
  set (Mr' := sf5_fill (Wn 1 (sf5_frame Mr0 sp (U (getr R 1)) (U (getr R 8))) fl 0) (Ba0RegionPoisoned_b.SB + F / 8) 32) in *.
  set (FP := fun x => (sp - 16 <= x < sp) \/ x = fl \/ (HeapIfaceA.S F <= x < HeapIfaceA.S F + 256)).
  set (g := g_fs art_fsg G) in *.
  assert (FRr : forall x : word, ~ FP (U x) -> Mr' x = Mr0 x).
  { intros x Hx. unfold Mr'. rewrite sf5_fill_outside; [|rewrite <- ESF; clear - SLfs SHF1; lia|cbn; rewrite <- ESF; clear - SHF2 SHfs; lia|cbn; rewrite <- ESF; clear - Hx; unfold FP in Hx; lia].
    rewrite Wn_outside; [|clear - FLR Gf0; lia|cbn; clear - FLR Gf2 HI2; lia|cbn; clear - Hx; unfold FP in Hx; lia].
    unfold sf5_frame. rewrite !Wn_outside by (cbn; clear - Hx SHI HI1 SLE STOP C8 HIdef; unfold FP in Hx; lia). reflexivity. }
  assert (GRr : mem_grows Mr0 Mr') by (unfold Mr'; eapply mem_grows_trans; [|apply sf5_fill_grows]; eapply mem_grows_trans; [|apply Wn_grows]; unfold sf5_frame; eapply mem_grows_trans; apply Wn_grows).
  (* [comment removed for export] *)
  assert (FPCL : forall x, FP x -> (sp - 16 <= x < sp) \/ (fs <= x < fs + 11571200) \/ (HeapIfaceA.S fs <= x < HeapIfaceA.S (fs + 11571200))).
  { intros x [X|[X|X]]; [left; exact X|right; left; clear - X FLR; lia|right; right; clear - X SHF1 SHF2; lia]. }
  assert (FPSHx : forall b x, In b LB -> in_shadow_of (fst b) (snd b) x -> ~ FP x).
  { intros b x Hb Hx HFP. pose proof (art_block_shadow_below rn LB FF LK A M b x CLI Hb Hx) as B1.
    destruct (CB b Hb) as (K1 & _ & _ & K4 & K5 & _ & _ & _ & _ & _ & _ & K12 & _). fold fs in K12. unfold FS_BYTES in K12.
    pose proof (art_S_lo (fst b) ltac:(clear - K1; lia)) as B2. pose proof Hx as (Hx1 & _).
    destruct (FPCL _ HFP) as [Y | [Y | Y]]; [clear - Y B1 SHI HI1; lia|clear - Y Hx1 B1 B2 Gf3; lia|].
    exact (art_shadow_apart (fst b) (snd b) fs 11571200 x (eq_sym FS8) FS8' K4 K12 Hx Y). }
  apply (art_wrap_pure3 MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Hwx (art_alloc_rep_frame_law_proved art_fsg MAPS0 RESV0) K R (0x5e2e8 : word) M model G LB FF LK cr A FP
           (fun R1 pc1 M1 => pc1 = getr R 1 /\ R1 = R' /\ M1 = Mr') g (ff_remove F FF) LK REPr FS B0 CRED CLI KN LZ EG).
  - (* [comment removed for export] *)
    exists R', (getr R 1), Mr'. split; [exact RUN|]. split; [exact GRr|]. split; [exact FRr|].
    split; [|split; [reflexivity|split; reflexivity]].
    apply (BatAllocG_b.cell_agree Mr0 Mr'); [|clear - Gl1; lia|cbn; clear - Gl2; lia|exact LSAN0].
    intros x Hx. cbn in Hx. apply FRr. unfold FP. clear - Hx Gl1 Gl2 SHI HI1 FLR Gf0 SLfs SHF1. lia.
  - (* [comment removed for export] *)
    intros x HFP Z; exfalso. destruct (FPCL _ HFP) as [Y | [Y | Y]].
    + pose proof (art_zone_below MAPS0 RESV0 NOACC0 BASE BUDGET rn G LB A M Mr0 model x REPr KN B0 (or_introl Z)) as ZB. clear - ZB Y SHI. lia.
    + apply (art_zone_off_fs MAPS0 RESV0 NOACC0 BASE BUDGET rn G LB A M Mr0 model x REPr KN B0 Z). fold fs. unfold FS_BYTES. exact Y.
    + apply (art_zone_off_fs_shadow MAPS0 RESV0 NOACC0 BASE BUDGET rn G LB A M Mr0 model x REPr KN B0 Z). fold fs. unfold FS_BYTES. exact Y.
  - exact FPSHx.
  - (* [comment removed for export] *)
    intros R1 pc1 M0 M1 (Epc & ER & EM) GROW FR1 VIS1. subst pc1 R1 M0.
    assert (TOM1 : forall a (n : nat) v, cellA Mr' a n v -> fs <= a -> a + Z.of_nat n <= fs + 11571200 -> cellA M1 a n v).
    { intros a n v C A1 A2. apply (BatAllocG_b.cell_agree Mr' M1); [| clear - A1 Gf1; lia | clear - A2 Gf2 HI2; lia | exact C].
      intros x Hx. apply VIS1. apply VFS. clear - Hx A1 A2. lia. }
    assert (C0 : cellA M1 fl 1 0).
    { apply TOM1; [|clear - FLR; lia|cbn; clear - FLR; lia]. unfold Mr'. apply sf5_fill_cell; [rewrite <- ESF; clear - SLfs SHF1; lia|cbn; rewrite <- ESF; clear - SHF2 SHfs; lia|clear - FLR Gf0; lia|cbn; clear - FLR Gf2 HI2; lia| |apply cell_Wn_hit; [clear - FLR Gf0; lia|cbn; clear - FLR Gf2 HI2; lia]].
      unfold apart. cbn. rewrite <- ESF. clear - SHF1 SHF2 SLfs SHfs FLR Gf3. lia. }
    split.
    + apply (art_fsinv_release_fl rn g FF LK M M1 F 5 rs fl FS HF); [exact CSF|clear - FLR Gf0 Gf2 HI2; lia|exact GROW|exact C0| |].
      * intros x NE Z3 NF. apply FR1. unfold FP. intros [X | [X | X]]; [|exact (NE X)|].
        -- pose proof (art_fs_zone3_below rn G LB _ (U x) REPr Z3) as ZB. clear - ZB X SHI. lia.
        -- unfold fs_zone3, FS_BYTES in Z3. fold fs in Z3. pose proof ROK as ROK'. rok_open ROK'. geo_open GEO. clear - Z3 X SHF1 SHF2 SLfs SHfs Gf3 Gt4 Gp2. lia.
      * intros x Zc. apply FR1. unfold FP. pose proof (art_cs_zone_below rn G LB FF LK M Mr0 (U x) REPr FS Zc) as CB1.
        unfold cs_zone in Zc. change (HeapIfaceA.S 0x10000) with 2147459072 in Zc. change (HeapIfaceA.S 0x696000) with 2148314112 in Zc.
        destruct CST as ((Q1 & Q2 & Q3) & _).
        intros [X | [X | X]]; [clear - CB1 X SHI; lia| |].
        -- clear - Zc X FLR Gf0 Gf3 Gd4 Q1. lia.
        -- pose proof (art_S_mono _ _ Gf0) as MM. change (HeapIfaceA.S 6905856) with 2148314112 in MM. clear - Zc X MM SHF1 SHF2 SLfs SHfs Gd3 Q1. lia.
    + intros b Hb f Hf. destruct (CB b Hb) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & K11 & _). apply K11.
      apply in_app_iff in Hf. apply in_app_iff. destruct Hf as [Hf|Hf]; [left; exact (ff_remove_in F FF f Hf)|right; exact Hf].
  - (* [comment removed for export] *)
    intros R1 pc1 M0 M1 model' (Epc & ER & EM) RI' GROW FR1 VIS1 HID RT MI'. subst pc1 R1 M0.
    apply (CONT R' M1 model').
    + apply keeps_cs_preserved. exact KCS.
    + intros j Hj. change (ff_bytes 5 / 8) with 256 in Hj. unfold byte_at. rewrite ESF.
      rewrite (VIS1 (Z_to_bv 64 (Ba0RegionPoisoned_b.SB + F / 8 + j))) by (apply VSHF; rewrite art_u_lit by (rewrite <- ESF; clear - Hj SLfs SHF1 SHF2 SHfs; lia); rewrite <- ESF; clear - Hj SHF1 SHF2; lia).
      unfold Mr'. apply sf5_fill_inside; [rewrite <- ESF; clear - SLfs SHF1; lia|cbn; rewrite <- ESF; clear - SHF2 SHfs; lia|cbn; clear - Hj; lia].
    + intros a Ra Ha NS. apply FR1. rewrite art_u_lit by exact Ra. unfold FP. intros [X | [X | X]].
      * apply (art_cls_off_scratch rn LB FF LK A M CLI L HLlo HLhi g FS sp 16 a ltac:(clear - SHI; lia) (or_intror Ha)). clear - X. lia.
      * (* [comment removed for export] *)
        subst a. pose proof (fsinv_frame_in rn _ _ _ _ FS) as FIN.
        assert (NSH : forall y z, 0 <= y -> y + z <= 2 ^ 47 -> 0 < z -> ~ in_shadow_of y z fl).
        { intros y z Hy Hyz Hz (X1 & X2). pose proof (art_S_lo y Hy). pose proof (art_S_hi (y + z - 1) ltac:(lia)). clear - X1 X2 H H0 Gf0 Gf3 FLR. lia. }
        destruct Ha as [H | [H | [H | [H | [H | [H | H]]]]]]; rewrite ?HLlo, ?HLhi in H.
        -- destruct H as (b & Hb & Rb). destruct (CB b Hb) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & K12 & _). fold fs in K12. unfold FS_BYTES in K12. clear - Rb K12 FLR. lia.
        -- rewrite HIeq in H. clear - H Gf2 FLR. lia.
        -- clear - H Gf0 FLR. lia.
        -- destruct H as (f & Hf & R1 & _). destruct (FIN f ltac:(apply in_or_app; left; exact Hf)) as (I1 & _). fold fs in I1. clear - R1 I1 FLR. lia.
        -- rewrite HIeq in H. apply (NSH (rn_HI rn) (2 ^ 47 - rn_HI rn)); [clear - HI1; lia|clear; lia|clear - HI2 C5 C6 C8 C9 HIdef; lia|exact H].
        -- destruct H as (f & Hf & Sh). destruct (FIN f ltac:(apply in_or_app; left; exact Hf)) as (I1 & I2 & I3). fold fs in I1, I2. unfold FS_BYTES in I2.
           exact (NSH (ff_addr f) (ff_bytes (ff_class f)) ltac:(clear - I1 Gf1; lia) ltac:(clear - I2 Gf2 HI2; lia) I3 Sh).
        -- destruct H as (b & Hb & Sh). destruct (CB b Hb) as (K1 & _ & _ & K4 & K5 & _). rewrite HIeq in K5. exact (NSH (fst b) (snd b) ltac:(clear - K1; lia) ltac:(clear - K5 HI2; lia) K4 Sh).
      * apply NS. unfold in_shadow_of. change (ff_bytes 5) with 2048.
        assert (E1 : HeapIfaceA.S (F + 2048 - 1) = HeapIfaceA.S F + 255).
        { unfold HeapIfaceA.S. set (q := F / 8) in *. replace (F + 2048 - 1) with (q * 8 + 2047) by (clear - SF8; lia). rewrite Z.div_add_l by lia. change (2047 / 8) with 255. clear. lia. }
        rewrite E1. clear - X. lia.
    + intros a Ha. apply GROW.
      assert (WM2 : wrA M (sp - 16) 16) by (intros d k Hd Hk; apply SWR; assumption).
      pose proof (art_wr_wview ASEGS M (sp - 16) 16 ltac:(clear - SHI HI1; lia) ltac:(clear - SLE STOP C8 HIdef; lia) WM2 (Z_to_bv 64 a)) as V.
      rewrite art_u_lit in V by (clear - Ha SHI HI1 SLE STOP C8 HIdef; lia). specialize (V ltac:(clear - Ha; lia)).
      rewrite art_wview_off in V by (rewrite art_u_lit by (clear - Ha SHI HI1 SLE STOP C8 HIdef; lia); right; clear - Ha SHI HI1; lia). exact V.
    + exact RT.
    + exact MI'.
    + exact RI'.
Qed.
End WS.
