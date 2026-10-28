(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct RefMemcpyLib MemSplit MemsetLib HeapIface HeapIfaceA HeapIfaceABx ArtMem ArtRuns ArtRunsMem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatCls_b BatLeaf_b BatCellEx_b BatImgCell_b BatPoison_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtBridge. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatInv_b BatInvMalloc_b BatLift_b BatWrapKit_b BatFsInv_b BatFsInvLaws_b BatIfaceLaws_b BatInvFrame_b Ba0RegionPoisoned_b Ba0HandleNoReturn_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import AsanPlanSoundSums.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatWrapC_b BatWrapVis_b BatWrapC2_b BatWrapRng_b BatWrapMemset_b BatFsInvLaws2_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Lemma art_rseg_10408 : art_rseg_ok ASEGS (Z_to_bv 64 0x10460) 8 = true.
Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Lemma art_cell_10408 : forall M : word -> option byte, exists v, 0 <= v < 2 ^ 64 /\ cellA M 0x10460 8 v.
Proof.
  intros M. destruct (art_rdn_defined_v 8 M 0x10460 ltac:(lia) ltac:(cbn; lia)) as (bs & R & Lb).
  { intros x Hx. right. apply (art_rseg_pt ASEGS 8 (Z_to_bv 64 0x10460)); [rewrite art_u_lit by lia; cbn; lia | exact art_rseg_10408 | rewrite art_u_lit by lia; exact Hx]. }
  exists (bytes_le_to_Z bs). split.
  - pose proof (PropExec.bytes_le_to_Z_bound bs) as B. pose proof (PropExec.bytes_le_to_Z_nonneg bs) as B0. rewrite Lb in B. split; [exact B0|exact B].
  - unfold cell. rewrite R. f_equal. symmetry. apply APSX.word_to_le_bytes_of_bytes_n; [exact Lb|lia].
Qed.

Ltac cell_goal H := first [lit_cell H | rewrite <- le1_one; lit_cell H | rewrite <- BatFsInv_b.le1_zero; lit_cell H].

Section WH.
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

#[using="Hwx HLsegs HLlo HLhi"] Theorem art_wrap_hnr : forall (R : bvmap 5 word) (M : word -> option byte) (model : Model)
    (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (K : ShapeAlg.TSet),
  let sp := U (getr R 2) in
  RI LB FF LK cr A M (vml_of model) -> m_halted model = None -> MInv A model ->
  getr R 4 = Z_to_bv 64 (rn_tp rn) -> Hoare.ret_ok (getr R 1) ->
  astack_ok L (rn_ar rn) M 4160 sp -> K [] ->
  (forall (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (lo : Z),
      regs_preserved R R' ->
      sp - 4160 - 4096 <= lo <= sp -> lo mod 4096 = 0 ->
      shadow_zero M' lo ((ar_stack_top (rn_ar rn) - lo) / 8) ->
      (forall a, 0 <= a < 2 ^ 64 -> aclient L (rn_ar rn) LB FF sp 4160 a ->
                 ~ in_shadow_of lo (ar_stack_top (rn_ar rn) - lo) a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
      (forall a, sp - 4160 <= a < sp -> M' (Z_to_bv 64 a) <> None) ->
      model_rt model model' -> MInv A model' ->
      RI LB FF LK cr A M' (vml_of model') ->
      srealizes ASEGS scfg (mkCfg (mkst R' (getr R 1) M' (seg_rom ASEGS)) model') K) ->
  srealizes ASEGS scfg (mkCfg (mkst R (0x811e8 : word) M (seg_rom ASEGS)) model) K.
Proof.
  intros R M model LB FF LK cr A K sp INV Hhalt HMI H4 Hret AST KT0 CONT.
  destruct (art_ri_open MAPS0 RESV0 NOACC0 BASE BUDGET rn LB FF LK cr A M model INV Hhalt HMI) as (G & REPr & FS & B0 & CRED & CLI & KN & LZ & EG).
  set (Mr0 := mrestrict (bhid A model) M) in *.
  destruct AST as (S16 & SHI & SLE & STOP & SWR & SDEF). fold sp in S16, SHI, SLE, SWR, SDEF. rewrite HLsegs in SWR.
  assert (HIeq : ahl_ceil (rn_ar rn) = rn_HI rn) by reflexivity. rewrite HIeq in SHI.
  pose proof (art_cli_hi rn LB FF LK A M CLI) as (HI1 & HI2).
  pose proof REPr as (ROK & STAT & THR & _).
  set (fs := ar_fs (rn_ar rn)) in *. set (top := ar_stack_top (rn_ar rn)) in *. set (bot := ar_stack_bottom (rn_ar rn)) in *.
  set (B := sp - 4160 - (sp - 4160) mod 4096). set (n := top - B).
  (* [comment removed for export] *)
  pose proof CLI as (CB & _ & SAst & _ & C5 & C6 & C7 & C8 & C9 & _). fold top in C8, C9. fold bot in C5, C6, C7, C9. rewrite HIeq in C5, C6.
  pose proof (Z.mod_pos_bound (sp - 4160) 4096 ltac:(lia)) as Bm.
  assert (BR : sp - 8255 <= B <= sp - 4160) by (unfold B; clear - Bm; lia).
  assert (B4096 : B mod 4096 = 0). { unfold B. rewrite Zminus_mod, Z.mod_mod by lia. rewrite Z.sub_diag. reflexivity. }
  assert (T8 : top mod 8 = 0).
  { pose proof (Z.div_mod bot 4096 ltac:(lia)) as D. rewrite C7, Z.add_0_r in D. rewrite C9, D.
    replace (4096 * (bot / 4096) + 8388608) with ((512 * (bot / 4096) + 1048576) * 8) by ring. apply Z_mod_mult. }
  assert (B8 : B mod 8 = 0).
  { pose proof (Z.div_mod B 4096 ltac:(lia)) as D. rewrite B4096, Z.add_0_r in D. rewrite D. replace (4096 * (B / 4096)) with ((512 * (B / 4096)) * 8) by ring. apply Z_mod_mult. }
  assert (HIdef : rn_HI rn = ar_sptop (rn_ar rn) - 8388608) by reflexivity.
  assert (NR : 64 <= n < 2 ^ 26) by (unfold n; clear - BR C5 C6 C9 SHI SLE HI2 HIdef; lia).
  assert (HIB : rn_HI rn <= B) by (clear - BR SHI; lia).
  assert (EB8 : B = 8 * (B / 8)) by (pose proof (Z.div_mod B 8 ltac:(lia)) as D; rewrite B8 in D; lia).
  assert (ET8 : top = 8 * (top / 8)) by (pose proof (Z.div_mod top 8 ltac:(lia)) as D; rewrite T8 in D; lia).
  assert (EN8 : n / 8 = top / 8 - B / 8). { unfold n. rewrite ET8, EB8 at 1. replace (8 * (top / 8) - 8 * (B / 8)) with ((top / 8 - B / 8) * 8) by ring. apply Z.div_mul. lia. }
  assert (En : n = top - B) by reflexivity.
  assert (SHR : 17594064011264 <= BatPoison_b.SB + B / 8 /\ BatPoison_b.SB + B / 8 + n / 8 <= 0x10007fff8000 /\ 0 < n / 8 /\ HeapIfaceA.S (rn_HI rn) <= BatPoison_b.SB + B / 8).
  { unfold BatPoison_b.SB, HeapIfaceA.S, HeapIfaceA.SB. rewrite EN8.
    assert (D1 : rn_HI rn / 8 <= B / 8) by (apply Z.div_le_mono; clear - HIB; lia).
    assert (D2 : 0x7fff7f800000 / 8 <= rn_HI rn / 8) by (apply Z.div_le_mono; clear - HI1; lia). change (0x7fff7f800000 / 8) with 17591916560384 in D2.
    clear - EB8 ET8 C8 NR En D1 D2. lia. }
  (* [comment removed for export] *)
  assert (GEOX : (4096 <= rn_t rn /\ rn_t rn + 4096 <= rn_HI rn /\ (rn_t rn + 4096 <= 0x10000 \/ 0x696000 <= rn_t rn) /\ (rn_t rn + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= rn_t rn))
                 /\ (4096 <= rn_ctx rn /\ rn_ctx rn + 4096 <= rn_HI rn /\ (rn_ctx rn + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= rn_ctx rn))
                 /\ (0x661b28 <= rn_tp rn - 88 /\ rn_tp rn + 8 <= 0x696000 /\ 0x10000 <= rn_tsd rn /\ rn_tsd rn + 1024 <= 0x696000 /\ 0 <= rn_key rn < 128)
                 /\ (4096 <= fs /\ fs + FS_BYTES <= rn_HI rn /\ (fs + FS_BYTES <= 0x7fff7000 \/ 0x10007fff8000 <= fs) /\ (fs + FS_BYTES <= 0x10000 \/ 0x696000 <= fs))
                 /\ (0x10000 <= rn_tp rn + rn_loff rn /\ rn_tp rn + rn_loff rn + 4 <= 0x696000)
                 /\ (4096 <= rn_dtls rn /\ rn_dtls rn + 4096 <= rn_HI rn /\ (rn_dtls rn + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= rn_dtls rn) /\ apart (rn_dtls rn) 4096 fs FS_BYTES)).
  { pose proof ROK as ROK'. rok_open ROK'. geo_open GEO. destruct Fapp as (_ & Fap & _). unfold BIGSHADOW_LO, BIGSHADOW_HI in Fap. fold fs in Fap, Fhi, Fimg, Flo.
    destruct D3 as (_ & D3a & _). unfold BIGSHADOW_LO, BIGSHADOW_HI in D3a. fold fs in Adf.
    split; [repeat split; assumption|]. split; [repeat split; assumption|]. split; [repeat split; first [assumption | lia]|]. split; [repeat split; assumption|]. split; [split; assumption|]. repeat split; assumption. }
  destruct GEOX as ((Gt1 & Gt2 & Gt3 & Gt4) & (Gc1 & Gc2 & Gc3) & (Gp1 & Gp2 & Gs1 & Gs2 & Gk) & (Gf1 & Gf2 & Gf3 & Gf4) & (Gl1 & Gl2) & (Gd1 & Gd2 & Gd3 & Gd4)).
  unfold apart, FS_BYTES in Gd4.
  unfold FS_BYTES in Gf2, Gf3, Gf4.
  assert (LAZY : forall w : word, page_in_ranges (page_base w) (m_vm_lazy model) = true ->
            0x696000 <= U w /\ U w < rn_HI rn /\ ~ in_block LB (U w) /\ ~ (ar_fs (rn_ar rn) <= U w < ar_fs (rn_ar rn) + FS_BYTES)).
  { intros w Hw. destruct LZ as (L1 & _). destruct (art_lazy_zone_bounds art_fsg rn G (U w) ROK (L1 w Hw)) as (B1 & B2).
    split; [lia|]. split; [exact (proj2 B1)|]. split; [|exact B2]. intros (b & Hb & Hr). rewrite (proj2 EG b w Hb Hr) in Hw. discriminate Hw. }
  set (FP := fun x => sp - 160 <= x < sp \/ BatPoison_b.SB + B / 8 <= x < BatPoison_b.SB + B / 8 + n / 8 \/ x = fs + 96).
  destruct SHR as (SH1 & SH2 & SH3 & SH4).
  (* [comment removed for export] *)
  assert (VSH : forall x : word, BatPoison_b.SB + B / 8 <= U x < BatPoison_b.SB + B / 8 + n / 8 -> bhid A model x = false).
  { intros x Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply (art_vis_shadow A model _ _ _ SAst). unfold in_shadow_of, HeapIfaceA.S, HeapIfaceA.SB. rewrite HIeq.
    unfold BatPoison_b.SB, HeapIfaceA.S, HeapIfaceA.SB in *.
    assert (E47 : (rn_HI rn + (2 ^ 47 - rn_HI rn) - 1) / 8 = 17592186044415). { replace (rn_HI rn + (2 ^ 47 - rn_HI rn) - 1) with (2 ^ 47 - 1) by ring. reflexivity. }
    rewrite E47. clear - Hx SH2 SH4. lia. }
  assert (VFS : forall x : word, fs <= U x < fs + 11571200 -> bhid A model x = false).
  { intros x Hx. apply (art_vis_byte rn LB A model LAZY). right; right; right. unfold FS_BYTES. exact Hx. }
  pose proof FS as (_ & WFS & _ & CT72 & _). fold fs in WFS, CT72.
  apply (art_wrap_pure3 MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Hwx (art_alloc_rep_frame_law_proved art_fsg MAPS0 RESV0) K R (0x811e8 : word) M model G LB FF LK cr A FP
           (fun R' pc1 Mr' => pc1 = getr R 1 /\ keeps_cs R R' /\ hnr_post Mr0 sp fs B n Mr')
           (FSGH (fg_hint (g_fs art_fsg G)) true) FF LK REPr FS B0 CRED CLI KN LZ EG).
  - (* [comment removed for export] *)
    assert (W0 : wrA Mr0 (sp - 4160) 4160).
    { apply (art_stack_wr art_fsg rn G A (m_vm_lazy model) M sp 4160 ROK LZ ltac:(clear - SHI; lia) ltac:(lia) ltac:(clear - SLE HI2 HIdef; lia)). exact SWR. }
    assert (HOK : store_ok ASEGS Mr0 (Z_to_bv 64 (sp - 160)) 160 = true).
    { replace (sp - 160) with (sp - 4160 + 4000) by ring. apply W0; [lia | cbn; lia]. }
    assert (WFSr : wrA Mr0 fs 11571200).
    { apply (proj2 (art_wr_vis (bhid A model) M fs 11571200 ltac:(clear - Gf1; lia) ltac:(clear - Gf2 HI2; lia) ltac:(intros x Hx; apply VFS; exact Hx))). exact WFS. }
    assert (HWFS : store_ok ASEGS Mr0 (Z_to_bv 64 (fs + 96)) 1 = true) by (apply WFSr; [lia | cbn; lia]).
    destruct STAT as (PC & LAY & TSD & _ & _ & _ & _ & S8).
    destruct TSD as (T1 & T2 & T3 & T4 & T5 & _).
    pose proof THR as (_ & _ & _ & _ & _ & _ & _ & THR0).
    destruct THR as (WT & _ & _ & TH8 & TH16 & TH40 & _).
    assert (INITED : cellA Mr0 0x140918 1 1) by conj_find S8.
    assert (CPU : cellA Mr0 0x137500 8 1) by conj_find S8.
    assert (CPG1 : cellA Mr0 0x1374a0 8 0x1cf6e0) by conj_find PC.
    assert (CPG2 : cellA Mr0 0x1cf6e0 8 4096) by conj_find PC.
    destruct (art_cell_10408 Mr0) as (pat & Rpat & CPAT).
    assert (CT72r : cellA Mr0 (rn_t rn + 72) 8 fs).
    { apply (proj2 (art_cell_vis (bhid A model) M (rn_t rn + 72) 8 fs ltac:(clear - Gt1; lia) ltac:(cbn; clear - Gt2 HI2; lia)
                      (art_vis_sub (bhid A model) (rn_t rn) 4096 (rn_t rn + 72) (Z.of_nat 8) (art_vis_of_wr (bhid A model) M (rn_t rn) 4096 ltac:(clear - Gt1; lia) ltac:(clear - Gt2 HI2; lia) Gt3 WT) ltac:(lia) ltac:(cbn; lia)))). exact CT72. }
    assert (HWSH : wrA Mr0 (BatPoison_b.SB + B / 8) (n / 8)).
    { apply (art_wr_of_defined ASEGS Mr0 (BatPoison_b.SB + B / 8) (n / 8) ltac:(clear - SH1; lia) ltac:(clear - SH2; lia)). intros x Hx. unfold Mr0, mrestrict. rewrite (VSH x Hx).
      apply (bi_shdef _ _ _ _ _ _ _ _ _ _ _ B0 x). right. unfold HSH_LO, HSH_HI. clear - Hx SH1 SH2. lia. }
    assert (CELLS : forall M' : word -> option byte,
              (forall x : word, U x < sp - 160 \/ sp <= U x -> ~ (BatPoison_b.SB + B / 8 <= U x < BatPoison_b.SB + B / 8 + n / 8) -> M' x = Mr0 x) ->
              forall a (k : nat) v, cellA Mr0 a k v -> 0 <= a -> a + Z.of_nat k <= rn_HI rn -> (a + Z.of_nat k <= 0x7fff7000 \/ 0x10007fff8000 <= a) -> cellA M' a k v).
    { intros M' AG a k v C Ha Hk Happ. apply (BatAllocG_b.cell_agree Mr0 M'); [| exact Ha | clear - Hk HI2; lia | exact C].
      intros x Hx. apply AG; [left; clear - Hx Hk SHI; lia | clear - Hx Happ SH1 SH2; lia]. }
    destruct (@hnr_run fx Mr0 (seg_rom ASEGS) (getr R 2) (getr R 1) sp (rn_tp rn) (rn_key rn) (rn_tsd rn) (rn_ctx rn) (rn_t rn) top bot fs 1 pat 0x1cf6e0 B n) with (regs := R)
      as (R' & Mr' & RUN & Q2 & Q1 & KCS & POST).
    + reflexivity.
    + exact Hret.
    + clear - SHI HI1 SLE HI2 HIdef. lia.
    + exact HOK.
    + clear - Gp1 Gp2. lia.
    + clear - Gk. lia.
    + clear - Gs1 Gs2 Gk. lia.
    + clear - Gc1 Gc2 HI2. lia.
    + clear - Gt1 Gt2 HI2. lia.
    + split; [clear - C9; lia | split; [clear - C5 HI1; lia | exact T8]].
    + reflexivity.
    + reflexivity.
    + clear - NR. lia.
    + unfold BatPoison_b.kHighMemBeg, BatPoison_b.kHighMemEnd. clear - HIB HI1 C8. lia.
    + clear - Gf1 Gf2 Gf3 HI2 SHI SH1 SH2. lia.
    + exact HWFS.
    + lia.
    + exact Rpat.
    + clear - SHI HI1. lia.
    + exact LAY.
    + exact HWSH.
    + unfold apart. left. clear - SH2 SHI HI1. lia.
    + (* [comment removed for export] *)
      intros M' AG. pose proof (CELLS M' (fun x H1 _ => AG x H1)) as CL.
      pose proof (CL _ _ _ INITED ltac:(lia) ltac:(cbn; clear - HI1; lia) ltac:(left; cbn; lia)) as X1.
      pose proof (CL _ _ _ CPU ltac:(lia) ltac:(cbn; clear - HI1; lia) ltac:(left; cbn; lia)) as X2.
      pose proof (CL _ _ _ CPAT ltac:(lia) ltac:(cbn; clear - HI1; lia) ltac:(left; cbn; lia)) as X3.
      pose proof (CL _ _ _ T1 ltac:(lia) ltac:(cbn; clear - HI1; lia) ltac:(left; cbn; lia)) as X4.
      pose proof (CL _ _ _ T2 ltac:(lia) ltac:(cbn; clear - HI1; lia) ltac:(left; cbn; lia)) as X5.
      pose proof (CL _ _ _ T3 ltac:(clear - Gp1; lia) ltac:(cbn; clear - Gp2 HI1; lia) ltac:(left; cbn; clear - Gp2; lia)) as X6.
      pose proof (CL _ _ _ T4 ltac:(clear - Gs1 Gk; lia) ltac:(cbn; clear - Gs2 Gk HI1; lia) ltac:(left; cbn; clear - Gs2 Gk; lia)) as X7.
      pose proof (CL _ _ _ T5 ltac:(clear - Gc1; lia) ltac:(cbn; clear - Gc2; lia) ltac:(cbn; clear - Gc3; lia)) as X8.
      pose proof (CL _ _ _ CPG1 ltac:(lia) ltac:(cbn; clear - HI1; lia) ltac:(left; cbn; lia)) as X9.
      pose proof (CL _ _ _ CPG2 ltac:(lia) ltac:(cbn; clear - HI1; lia) ltac:(left; cbn; lia)) as X10.
      pose proof (CL _ _ _ TH40 ltac:(clear - Gt1; lia) ltac:(cbn; clear - Gt2; lia) ltac:(cbn; clear - Gt4; lia)) as X11.
      pose proof (CL _ _ _ TH8 ltac:(clear - Gt1; lia) ltac:(cbn; clear - Gt2; lia) ltac:(cbn; clear - Gt4; lia)) as X12.
      pose proof (CL _ _ _ TH16 ltac:(clear - Gt1; lia) ltac:(cbn; clear - Gt2; lia) ltac:(cbn; clear - Gt4; lia)) as X13.
      pose proof (CL _ _ _ CT72r ltac:(clear - Gt1; lia) ltac:(cbn; clear - Gt2; lia) ltac:(cbn; clear - Gt4; lia)) as X14.
      repeat split; [cell_goal X1 | cell_goal X2 | cell_goal X3 | cell_goal X4 | cell_goal X5 | cell_goal X6 | cell_goal X7 | cell_goal X8 | cell_goal X9 | cell_goal X10
                     | cell_goal X11 | cell_goal X12 | cell_goal X13 | cell_goal X14].
    + (* [comment removed for export] *)
      intros M' AG. pose proof (CELLS M' AG) as CL.
      pose proof (CL _ _ _ T1 ltac:(lia) ltac:(cbn; clear - HI1; lia) ltac:(left; cbn; lia)) as X4.
      pose proof (CL _ _ _ T2 ltac:(lia) ltac:(cbn; clear - HI1; lia) ltac:(left; cbn; lia)) as X5.
      pose proof (CL _ _ _ T3 ltac:(clear - Gp1; lia) ltac:(cbn; clear - Gp2 HI1; lia) ltac:(left; cbn; clear - Gp2; lia)) as X6.
      pose proof (CL _ _ _ T4 ltac:(clear - Gs1 Gk; lia) ltac:(cbn; clear - Gs2 Gk HI1; lia) ltac:(left; cbn; clear - Gs2 Gk; lia)) as X7.
      pose proof (CL _ _ _ T5 ltac:(clear - Gc1; lia) ltac:(cbn; clear - Gc2; lia) ltac:(cbn; clear - Gc3; lia)) as X8.
      pose proof (CL _ _ _ TH40 ltac:(clear - Gt1; lia) ltac:(cbn; clear - Gt2; lia) ltac:(cbn; clear - Gt4; lia)) as X11.
      pose proof (CL _ _ _ CT72r ltac:(clear - Gt1; lia) ltac:(cbn; clear - Gt2; lia) ltac:(cbn; clear - Gt4; lia)) as X14.
      repeat split; [cell_goal X4 | cell_goal X5 | cell_goal X6 | cell_goal X7 | cell_goal X8 | cell_goal X11 | cell_goal X14].
    + exact H4.
    + reflexivity.
    + reflexivity.
    + (* [comment removed for export] *)
      destruct POST as (MF & EM & MFO & MFG).
      assert (K8 : Z.of_nat (Z.to_nat (n / 8)) = n / 8) by (rewrite Z2Nat.id by (clear - SH3; lia); reflexivity).
      assert (FRr : forall x : word, ~ FP (U x) -> Mr' x = Mr0 x).
      { intros x Hx. unfold FP in Hx. rewrite EM.
        rewrite (Wn_outside 1 MF (fs + 96) 1 x ltac:(clear - Gf1; lia) ltac:(cbn; clear - Gf2 HI2; lia) ltac:(cbn; clear - Hx; lia)).
        rewrite (MFO x ltac:(clear - Hx; lia)).
        apply (Wf_outside Mr0 (BatPoison_b.SB + B / 8) (Z.to_nat (n / 8)) 0 x ltac:(clear - SH1; lia) ltac:(rewrite K8; clear - SH2; lia)). rewrite K8. clear - Hx. lia. }
      exists R', (getr R 1), Mr'. split; [exact RUN|].
      split. { rewrite EM. eapply mem_grows_trans; [exact MFG | apply Wn_grows]. }
      split; [exact FRr|].
      split.
      { pose proof THR0 as CL. apply (BatAllocG_b.cell_agree Mr0 Mr'); [| clear - Gl1; lia | cbn; clear - Gl2; lia | exact CL].
        intros x Hx. cbn in Hx. apply FRr. unfold FP. clear - Hx Gl1 Gl2 SHI HI1 SH1 Gf4. lia. }
      split; [reflexivity|]. split; [exact KCS|]. exists MF. repeat split; assumption.
  - (* [comment removed for export] *)
    intros x [Hx | [Hx | Hx]] Z; exfalso.
    + pose proof (art_zone_below MAPS0 RESV0 NOACC0 BASE BUDGET rn G LB A M Mr0 model x REPr KN B0 (or_introl Z)). clear - H Hx SHI. lia.
    + apply (art_zone_not_stack_shadow MAPS0 RESV0 NOACC0 BASE BUDGET rn G LB A M Mr0 model x REPr KN B0 Z). clear - Hx SH2 SH4. lia.
    + apply (art_zone_off_fs MAPS0 RESV0 NOACC0 BASE BUDGET rn G LB A M Mr0 model x REPr KN B0 Z). fold fs. unfold FS_BYTES. clear - Hx. lia.
  - (* [comment removed for export] *)
    intros b x Hb Hx HF. pose proof (art_block_shadow_below rn LB FF LK A M b x CLI Hb Hx) as B1.
    destruct (CB b Hb) as (K1 & _ & _ & K4 & K5 & _). rewrite HIeq in K5.
    pose proof (art_S_lo (fst b) ltac:(clear - K1; lia)) as B2. unfold in_shadow_of in Hx.
    destruct HF as [X | [X | X]].
    + clear - X B1 SHI HI1. lia.
    + assert (HI8 : rn_HI rn mod 8 = 0).
      { pose proof CLI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & C13). rewrite HIdef.
        pose proof (Z.div_mod (ar_sptop (rn_ar rn)) 16 ltac:(lia)) as D. rewrite C13, Z.add_0_r in D. rewrite D.
        replace (16 * (ar_sptop (rn_ar rn) / 16) - 8388608) with ((2 * (ar_sptop (rn_ar rn) / 16) - 1048576) * 8) by ring. apply Z_mod_mult. }
      assert (LT : (fst b + snd b - 1) / 8 < rn_HI rn / 8).
      { apply Z.div_lt_upper_bound; [lia|]. pose proof (Z.div_mod (rn_HI rn) 8 ltac:(lia)) as D. rewrite HI8, Z.add_0_r in D. clear - D K5. lia. }
      unfold HeapIfaceA.S, HeapIfaceA.SB in *. clear - X Hx LT SH4. lia.
    + clear - X Hx B1 B2 Gf1 Gf3. lia.
  - (* [comment removed for export] *)
    intros R' pc1 Mr' M1 (Epc & KCS & (MF & EM & MFO & MFG)) GROW FR1 VIS1. split.
    + apply (art_fsinv_set_gc rn (g_fs art_fsg G) FF LK M M1 true FS GROW); fold fs.
      * intros x Z3 NE. apply FR1. unfold FP. intros [X | [X | X]]; [| | exact (NE X)].
        -- pose proof (art_fs_zone3_below rn G LB _ (U x) REPr Z3). clear - H X SHI. lia.
        -- unfold fs_zone3, FS_BYTES in Z3. fold fs in Z3. clear - Z3 X SH1 SH2 Gf3 Gt4 Gp1 Gp2. lia.
      * intros x Zc. apply FR1. unfold FP. destruct (fsinv_cs _ _ _ _ _ FS) as ((Q1 & _) & _).
        pose proof (art_cs_zone_below rn G LB FF LK M Mr0 (U x) REPr FS Zc) as CB1.
        unfold cs_zone in Zc. change (HeapIfaceA.S 0x10000) with 2147459072 in Zc. change (HeapIfaceA.S 0x696000) with 2148314112 in Zc.
        intros [X | [X | X]]; [clear - CB1 X SHI; lia | clear - Zc X SH1 SH2 Q1 Gd3; lia | clear - Zc X Gf3 Gf4 Gd4 Q1 Gp1; lia].
      * apply (BatAllocG_b.cell_agree Mr' M1); [| clear - Gf1; lia | cbn; clear - Gf2 HI2; lia |].
        -- intros x Hx. cbn in Hx. apply VIS1. apply VFS. clear - Hx. lia.
        -- rewrite EM. apply (cell_Wn_hit ASEGS 1 MF (fs + 96) 1); [clear - Gf1; lia | cbn; clear - Gf2 HI2; lia].
    + intros b Hb. destruct (CB b Hb) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & K11 & _). exact K11.
  - (* [comment removed for export] *)
    intros R' pc1 Mr' M1 model' (Epc & KCS & (MF & EM & MFO & MFG)) RI' GROW FR1 VIS1 HID RT MI'. subst pc1.
    assert (K8 : Z.of_nat (Z.to_nat (n / 8)) = n / 8) by (rewrite Z2Nat.id by (clear - SH3; lia); reflexivity).
    apply (CONT R' M1 model' B (keeps_cs_preserved R R' KCS)); [clear - BR; lia | exact B4096 | | | | exact RT | exact MI' | exact RI'].
    + intros j Hj. fold n in Hj. unfold byte_at. replace (HeapIfaceA.S B + j) with (BatPoison_b.SB + B / 8 + j) by (unfold HeapIfaceA.S, HeapIfaceA.SB, BatPoison_b.SB; ring).
      assert (Rx : 0 <= BatPoison_b.SB + B / 8 + j < 2 ^ 64) by (clear - Hj SH1 SH2; lia).
      rewrite (VIS1 _ (VSH (Z_to_bv 64 (BatPoison_b.SB + B / 8 + j)) ltac:(rewrite art_u_lit by exact Rx; clear - Hj; lia))).
      rewrite EM. rewrite (Wn_outside 1 MF (fs + 96) 1 _ ltac:(clear - Gf1; lia) ltac:(cbn; clear - Gf2 HI2; lia) ltac:(rewrite art_u_lit by exact Rx; cbn; clear - Hj SH1 SH2 Gf1 Gf3; lia)).
      rewrite (MFO _ ltac:(rewrite art_u_lit by exact Rx; left; clear - Hj SH2 SHI HI1; lia)).
      apply (Wf_inside Mr0 (BatPoison_b.SB + B / 8) (Z.to_nat (n / 8)) 0 j ltac:(clear - SH1; lia) ltac:(rewrite K8; clear - SH2; lia) ltac:(rewrite K8; exact Hj)).
    + intros a Ra Ha NS. apply FR1. rewrite art_u_lit by exact Ra. unfold FP. intros [X | [X | X]].
      * apply (art_cls_off_scratch rn LB FF LK A M CLI L HLlo HLhi (g_fs art_fsg G) FS sp 4160 a ltac:(clear - SHI; lia) (or_intror Ha)). clear - X. lia.
      * apply NS. unfold in_shadow_of, HeapIfaceA.S, HeapIfaceA.SB. unfold BatPoison_b.SB in X.
        assert (E1 : (B + (top - B) - 1) / 8 = top / 8 - 1).
        { replace (B + (top - B) - 1) with (top - 1) by ring. rewrite ET8 at 1. replace (8 * (top / 8) - 1) with (7 + (top / 8 - 1) * 8) by ring. rewrite Z.div_add by lia. reflexivity. }
        fold top. rewrite E1. clear - X EN8. lia.
      * (* [comment removed for export] *)
        subst a. pose proof (art_S_lo 0 ltac:(lia)) as S0. 
        assert (NSH : forall y z, 0 <= y -> y + z <= 2 ^ 47 -> 0 < z -> ~ in_shadow_of y z (fs + 96)).
        { intros y z Hy Hyz Hz (X1 & X2). pose proof (art_S_lo y Hy). pose proof (art_S_hi (y + z - 1) ltac:(lia)). clear - X1 X2 H H0 Gf1 Gf3. lia. }
        destruct Ha as [H | [H | [H | [H | [H | [H | H]]]]]]; rewrite ?HLlo, ?HLhi in H.
        -- destruct H as (b & Hb & Rb). destruct (CB b Hb) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & K12 & _). fold fs in K12. unfold FS_BYTES in K12. clear - Rb K12. lia.
        -- rewrite HIeq in H. clear - H Gf2. lia.
        -- clear - H Gf4. lia.
        -- destruct H as (f & Hf & R1 & _). pose proof (fsinv_frame_in rn _ FF LK M FS f ltac:(apply in_or_app; left; exact Hf)) as (I1 & _). fold fs in I1. clear - R1 I1. lia.
        -- apply (NSH (rn_HI rn) (2 ^ 47 - rn_HI rn) ltac:(clear - HI1; lia) ltac:(lia) ltac:(clear - HI2; lia) H).
        -- destruct H as (f & Hf & H). pose proof (fsinv_frame_in rn _ FF LK M FS f ltac:(apply in_or_app; left; exact Hf)) as (I1 & I2 & I3). fold fs in I1, I2. unfold FS_BYTES in I2.
           apply (NSH (ff_addr f) (ff_bytes (ff_class f)) ltac:(clear - I1 Gf1; lia) ltac:(clear - I2 Gf2 HI2; lia) I3 H).
        -- destruct H as (b & Hb & H). destruct (CB b Hb) as (K1 & _ & _ & K4 & K5 & _). rewrite HIeq in K5. apply (NSH (fst b) (snd b) ltac:(clear - K1; lia) ltac:(clear - K5 HI2; lia) K4 H).
    + intros a Ha. apply GROW.
      assert (WM : wrA M (sp - 4160) 4160) by (intros d k Hd Hk; apply SWR; assumption).
      pose proof (art_wr_wview ASEGS M (sp - 4160) 4160 ltac:(clear - SHI HI1; lia) ltac:(clear - SLE HI2 HIdef; lia) WM (Z_to_bv 64 a)) as V. rewrite art_u_lit in V by (clear - Ha SHI HI1 SLE HI2 HIdef; lia). specialize (V ltac:(clear - Ha; lia)).
      rewrite art_wview_off in V by (rewrite art_u_lit by (clear - Ha SHI HI1 SLE HI2 HIdef; lia); right; clear - Ha SHI HI1; lia). exact V.
Qed.

(* [comment removed for export] *)
Hypothesis HLtp : hl_tp L = rn_tp rn.
Hypothesis HLnr : hl_handle_no_return L = 0x811e8.
Hypothesis HLscrnr : hl_scr_no_return L = 4160.
#[using="Type"] Lemma lit_80dd0 : Z_to_bv 64 0x811e8 = (0x811e8%bv : word). Proof. apply bv_eq. reflexivity. Qed.
End WH.

Theorem art_ahnr : forall MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg, wx_segs_nowrap ASEGS -> forall L : asan_layout,
  hl_segs L = ASEGS -> hl_img_lo L = 0x10000 -> hl_img_hi L = 0x696000 -> hl_tp L = rn_tp rn -> hl_handle_no_return L = 0x811e8 -> hl_scr_no_return L = 4160 ->
  ahandle_no_return_spec L (rn_ar rn) scfg (art_iface art_fsg MAPS0 RESV0 NOACC0 BASE BUDGET art_fsinv rn).
Proof.
  intros MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Hwx L HLsegs HLlo HLhi HLtp HLnr HLscrnr fx R M model LB FF LK cr A K. cbv zeta.
  intros INV Hh HMI H4 Hret AST KT0 POST. rewrite HLsegs, HLscrnr in *. rewrite HLnr, lit_80dd0. rewrite HLtp in H4.
  apply (art_wrap_hnr MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Hwx L HLsegs HLlo HLhi R M model LB FF LK cr A K INV Hh HMI H4 Hret AST KT0).
  intros R' M' model' lo RP LO L4 SZ FR SD RT MI' RI'. apply (POST R' M' model' lo RP LO L4 SZ FR SD RT MI' RI').
Qed.
