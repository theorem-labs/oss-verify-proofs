(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare ShapeAlg SpinAlg AsanAcct RefMemcpyLib MemSplit StreamSim HeapIface HeapIfaceA IcptIfaceA ArtMem ArtRuns ArtRunsMem ArtCls ArtLeaf ArtCellEx ArtImgCell ArtPoison ArtDepot
     ArtBridge ArtInv ArtInvMalloc ArtLift ArtWrapKit ArtFsInv ArtFsInvLaws ArtIfaceLaws ArtInvFrame ArtIfaceFrame L5Defs L5KnA.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import ArtWrapC ArtWrapVis ArtWrapC2 ArtWrapC2x ArtWrapRng As0DrvP_icStrerror22r.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

(* [comment removed for export] *)
Lemma se_fetch_ret : exists w, fetch_word ASEGS (Z_to_bv 64 0x521d8) = Some w /\ is_ecall w = false /\ decode_any w = Some (Jalr 0%bv 1%bv 0%bv, 4%Z).
Proof. eexists. split; [vm_compute; reflexivity | split; [vm_compute; reflexivity | vm_refl_bv]]. Qed.
Lemma se_wseg_lsan : wseg_ok ASEGS (Z_to_bv 64 0x610d18) 4 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma se_msg : word_to_le_bytes 4 (Z_to_bv 64 1635151433) ++ word_to_le_bytes 4 (Z_to_bv 64 543451500) ++ word_to_le_bytes 4 (Z_to_bv 64 1969713761)
               ++ word_to_le_bytes 4 (Z_to_bv 64 1953391981) ++ [Z_to_bv 8 0] = map (Z_to_bv 8) EINVAL_MSG.
Proof. vm_compute. repeat (apply f_equal2; [apply bv_eq; reflexivity|]). reflexivity. Qed.

Lemma se_addr : forall a n, 0 <= a -> a + Z.of_nat n < 2 ^ 64 -> (Z_to_bv 64 a + nat_to_word n)%bv = Z_to_bv 64 (a + Z.of_nat n).
Proof.
  intros a n Ha Hn. apply bv_eq. unfold nat_to_word. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite (Z.mod_small a) by lia. rewrite (Z.mod_small (Z.of_nat n)) by lia. rewrite !Z.mod_small by lia. reflexivity.
Qed.

Section WSE.
Variables MAPS0 RESV0 NOACC0 : list (word * word).
Variables BASE BUDGET : Z.
Variable rn : art_run.
Variable scfg : SpuriousCfg.
Hypothesis Hwx : wx_segs_nowrap ASEGS.
Variable L : asan_layout.
Hypothesis HLsegs : hl_segs L = ASEGS.
Hypothesis HLlo : hl_img_lo L = 0x10000.
Hypothesis HLhi : hl_img_hi L = 0x633000.
Hypothesis Htp : rn_tp rn = 0x610d08.
Hypothesis HLoff16 : rn_loff rn = 0x10.
Hypothesis Hkey0 : rn_key rn = 0.
Hypothesis Htsd : rn_tsd rn = 0x6320b0.
Hypothesis HLlsan : forall a, 0x610d18 <= a < 0x610d1c -> hl_rt_static L a.
#[local] Abbreviation RI := (art_ri_inv art_fsg MAPS0 RESV0 NOACC0 BASE BUDGET art_fsinv rn).
Context {fx : PropExec.FPState}.

Theorem art_wrap_strerror22 : forall (R : bvmap 5 word) (M : word -> option byte) (model : Model)
    (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (Kt : ShapeAlg.TSet),
  let sp := U (getr R 2) in
  RI LB FF LK cr A M (vml_of model) -> m_halted model = None -> MInv A model ->
  getr R 10 = Z_to_bv 64 22 -> getr R 11 = Z_to_bv 64 (sp + 16) -> getr R 12 = Z_to_bv 64 1024 ->
  getr R 4 = Z_to_bv 64 (rn_tp rn) -> Hoare.ret_ok (getr R 1) ->
  astack_ok L (rn_ar rn) M 4320 sp -> sp + 128 <= ar_sptop (rn_ar rn) ->
  (forall d (m : nat), 0 <= d -> d + Z.of_nat m <= 17 -> store_ok ASEGS M (Z_to_bv 64 (sp + 16 + d)) m = true) ->
  (forall x, in_shadow_of (sp - 64) 192 x -> byte_at M x 0) ->
  cell_is ASEGS M 0x610cd8 8 0x630fd0 -> cell_is ASEGS M 0x630ff8 8 0 ->
  (forall a, 0x10000 <= a < 0xd7000 -> M (Z_to_bv 64 a) = None) ->
  Kt [] ->
  (forall (fx' : PropExec.FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model),
      getr R' 10 = Z_to_bv 64 0 -> regs_preserved R R' ->
      rdn ASEGS M' (Z_to_bv 64 (sp + 16)) 17 = Some (map (Z_to_bv 8) EINVAL_MSG) ->
      (forall a, 0 <= a < 2 ^ 64 -> aclient L (rn_ar rn) LB FF sp 4320 a -> ~ (sp + 16 <= a < sp + 33) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
      (forall a, sp - 4320 <= a < sp -> M' (Z_to_bv 64 a) <> None) ->
      (forall a : word, M a <> None -> M' a <> None) ->
      model_rt model model' -> MInv A model' -> RI LB FF LK cr A M' (vml_of model') ->
      srealizes ASEGS scfg (mkCfg (@mkst fx' R' (getr R 1) M' (seg_rom ASEGS)) model') Kt) ->
  srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x4dc04) M (seg_rom ASEGS)) model) Kt.
Proof.
  intros R M model LB FF LK cr A Kt sp INV Hhalt HMI H10 H11 H12 H4 Hret AST SPTOP BUFW SHZ CM1 CM2 ROC KT0 CONT.
  destruct (art_ri_open MAPS0 RESV0 NOACC0 BASE BUDGET rn LB FF LK cr A M model INV Hhalt HMI) as (G & REPr & FS & B0 & CRED & CLI & KN & LZ & EG).
  set (Mr0 := mrestrict (bhid A model) M) in *.
  destruct AST as (S16 & SHI & SLE & STOP & SWR & SDEF). fold sp in S16, SHI, SLE, SWR, SDEF. rewrite HLsegs in SWR.
  assert (HIeq : ahl_ceil (rn_ar rn) = rn_HI rn) by reflexivity. rewrite HIeq in SHI.
  pose proof (art_cli_hi rn LB FF LK A M CLI) as (HI1 & HI2).
  pose proof REPr as (ROK & STAT & THR & _).
  pose proof CLI as (CB & _ & SAst & SAfs & _ & _ & _ & _ & _ & _ & SAimg & _). rewrite HIeq in SAst.
  assert (HIdef : rn_HI rn = ar_sptop (rn_ar rn) - 8388608) by reflexivity.
  assert (SPR : 140735332491488 <= sp <= 140737488355200) by (clear - SHI HI1 SPTOP STOP; lia).
  assert (LAZY : forall w : word, page_in_ranges (page_base w) (m_vm_lazy model) = true ->
            0x633000 <= U w /\ U w < rn_HI rn /\ ~ in_block LB (U w) /\ ~ (ar_fs (rn_ar rn) <= U w < ar_fs (rn_ar rn) + FS_BYTES)).
  { intros w Hw. destruct LZ as (L1 & _). destruct (art_lazy_zone_bounds art_fsg rn G (U w) ROK (L1 w Hw)) as (B1 & B2).
    split; [lia|]. split; [exact (proj2 B1)|]. split; [|exact B2]. intros (b & Hb & Hr). rewrite (proj2 EG b w Hb Hr) in Hw. discriminate Hw. }
  assert (VIMG : forall x : word, U x < 0x633000 -> bhid A model x = false) by (intros x Hx; apply (art_vis_byte rn LB A model LAZY); left; exact Hx).
  assert (VSTK : forall x : word, rn_HI rn <= U x -> bhid A model x = false) by (intros x Hx; apply (art_vis_byte rn LB A model LAZY); right; left; exact Hx).
  assert (IMGV : forall a (n : nat) v, cellA M a n v -> 0 <= a -> a + Z.of_nat n <= 0x633000 -> cellA Mr0 a n v).
  { intros a n v C A1 A2. apply (proj2 (art_cell_vis (bhid A model) M a n v A1 ltac:(clear - A2; lia) ltac:(intros x Hx; apply VIMG; clear - Hx A2; lia))). exact C. }
  (* [comment removed for export] *)
  destruct STAT as (PC & LAY & TSD & _ & _ & _ & TLSG & S8).
  destruct THR as (_ & _ & _ & _ & _ & _ & _ & LSAN0). rewrite Htp, HLoff16 in LSAN0. change (6360328 + 16) with 6360344 in LSAN0.
  destruct (fsinv_cs _ _ _ _ _ FS) as ((Q1 & Q2 & Q3) & CS1 & CS2 & CS3 & _ & _ & ISH & _).
  assert (E8 : sp = 8 * (sp / 8)).
  { pose proof (Z.div_mod sp 16 ltac:(lia)) as D. rewrite S16, Z.add_0_r in D. rewrite D at 2. replace (16 * (sp / 16)) with (2 * (sp / 16) * 8) by ring. rewrite Z.div_mul by lia. clear - D. lia. }
  assert (W0 : wrA Mr0 (sp - 4320) 4320).
  { apply (art_stack_wr art_fsg rn G A (m_vm_lazy model) M sp 4320 ROK LZ ltac:(clear - SHI; lia) ltac:(clear; lia) ltac:(clear - SPTOP STOP; lia)). exact SWR. }
  assert (DEFR : forall a n, rn_HI rn <= a -> a + n <= 2 ^ 47 -> wrA Mr0 a n -> L5.defined Mr0 a n).
  { intros a n A1 A2 W i Hi. pose proof (art_wr_wview ASEGS Mr0 a n ltac:(clear - A1 HI1; lia) ltac:(clear - A2; lia) W (Z_to_bv 64 (a + i))) as Vw.
    rewrite art_u_lit in Vw by (clear - Hi A1 A2 HI1; lia). specialize (Vw ltac:(clear - Hi; lia)).
    rewrite art_wview_off in Vw by (rewrite art_u_lit by (clear - Hi A1 A2 HI1; lia); right; clear - Hi A1 HI1; lia). exact Vw. }
  assert (IMC : L5.img_clear Mr0 65536 880640).
  { intros i Hi. unfold Mr0, mrestrict. destruct (bhid A model (Z_to_bv 64 i)); [reflexivity | apply ROC; clear - Hi; lia]. }
  assert (ZSH : L5KA.zeros_at Mr0 (sp / 8 + 2147450872) 24).
  { intros i Hi. assert (Rx : 0 <= sp / 8 + 2147450872 + i < 2 ^ 64) by (clear - Hi E8 SPR; lia).
    assert (INS : in_shadow_of (sp - 64) 192 (sp / 8 + 2147450872 + i)).
    { unfold in_shadow_of, HeapIfaceA.S, HeapIfaceA.SB.
      assert (D1 : (sp - 64) / 8 = sp / 8 - 8) by (rewrite E8 at 1; replace (8 * (sp / 8) - 64) with ((sp / 8 - 8) * 8) by ring; apply Z.div_mul; lia).
      assert (D2 : (sp - 64 + 192 - 1) / 8 = sp / 8 + 15) by (rewrite E8 at 1; replace (8 * (sp / 8) - 64 + 192 - 1) with (7 + (sp / 8 + 15) * 8) by ring; rewrite Z.div_add by lia; reflexivity).
      rewrite D1, D2. clear - Hi. lia. }
    unfold Mr0, mrestrict. rewrite (art_vis_shadow A model (rn_HI rn) (2 ^ 47 - rn_HI rn) _ SAst).
    - exact (SHZ _ INS).
    - apply (in_shadow_of_sub (rn_HI rn) (2 ^ 47 - rn_HI rn) (sp - 64) 192); [clear - SHI; lia | clear - SPTOP STOP; lia | lia | exact INS]. }
  assert (C0 : L5.u64_at ASEGS Mr0 2147469904 0).
  { apply (cell_zero_bytes Mr0 2147469904 8 ltac:(right; reflexivity) ltac:(lia) ltac:(cbn; lia)). intros jj Hjj. cbn in Hjj. unfold byte_at, Mr0, mrestrict.
    rewrite (art_vis_shadow A model 0x10000 (0x633000 - 0x10000) _ SAimg).
    - apply ISH. right; left. change (HeapIfaceA.S 0x22ba0) with 2147468660. change (HeapIfaceA.S 0xda2a0) with 2147562580. clear - Hjj. lia.
    - unfold in_shadow_of. change (HeapIfaceA.S 65536) with 2147459072. change (HeapIfaceA.S (65536 + (6500352 - 65536) - 1)) with 2148263423. clear - Hjj. lia. }
  assert (WB : L5.writable ASEGS Mr0 (sp + 16) 17).
  { intros d m Hd Hm. apply (art_rng_store_ok A M model (sp + 16 + d) m ltac:(clear - Hd SPR; lia) ltac:(clear - Hd Hm SPR; lia)); [|apply BUFW; assumption].
    intros x Hx. apply VSTK. clear - Hx Hd SHI. lia. }
  assert (DB : L5.defined Mr0 (sp + 16) 17) by (apply DEFR; [clear - SHI; lia | clear - SPTOP STOP; lia | exact WB]).
  assert (WL : L5.writable ASEGS Mr0 6360344 4).
  { intros d m Hd Hm. apply (store_ok_window ASEGS Mr0 (Z_to_bv 64 0x610d18) (Z_to_bv 64 (6360344 + d)) 4%nat m 0x610d18 (0x610d18 + 4));
      first [exact se_wseg_lsan | reflexivity | lia | (rewrite art_u_lit by lia; lia)]. }
  assert (INITED : cellA Mr0 0xde818 1 1) by conj_find S8.
  assert (I99 : cellA Mr0 0xde819 1 1) by conj_find S8.
  assert (F3E3 : cellA Mr0 0x16f763 1 1) by conj_find S8.
  assert (RMS : cellA Mr0 0xd7810 8 0xcb728) by conj_find S8.
  assert (LSB : cellA Mr0 0xddb38 8 ArtPoison.SB) by conj_find LAY.
  assert (CS1r : cellA Mr0 0xd7690 8 0xcbe10) by (apply (IMGV _ _ _ CS1); [lia | cbn; lia]).
  assert (CS2r : cellA Mr0 0xd7718 8 0xbd164) by (apply (IMGV _ _ _ CS2); [lia | cbn; lia]).
  assert (CS3r : cellA Mr0 0xd7720 8 0xcbd78) by (apply (IMGV _ _ _ CS3); [lia | cbn; lia]).
  assert (CM1r : cellA Mr0 0x610cd8 8 0x630fd0) by (apply (IMGV _ _ _ CM1); [lia | cbn; lia]).
  assert (CM2r : cellA Mr0 0x630ff8 8 0) by (apply (IMGV _ _ _ CM2); [lia | cbn; lia]).
  assert (RG : forall (i : nat) (r : bv 5), bv_unsigned r = Z.of_nat i -> Z_to_bv 5 (Z.of_nat i) = r) by (intros i r E; rewrite <- E; apply Z_to_bv_bv_unsigned).
  assert (R2 : getr R (Z_to_bv 5 (Z.of_nat 2)) = Z_to_bv 64 sp) by (rewrite (RG 2%nat 2%bv eq_refl); unfold sp; symmetry; apply Z_to_bv_bv_unsigned).
  destruct (AS0DRVP_icStrerror22r.icStrerror22r_conc fx R Mr0 (fun _ => sp)) as (fx' & R1 & Mr1 & GR1 & FRW & _ & RUN1 & KEPT & _ & E10 & _ & _ & _ & _ & _ & _ & _ & B32 & B28 & B24 & B20 & B16 & BLS).
  { clear - SPR. lia. }
  { exact R2. }
  { rewrite (RG 4%nat 4%bv eq_refl). rewrite H4, Htp. reflexivity. }
  { rewrite (RG 10%nat 10%bv eq_refl). exact H10. }
  { rewrite (RG 11%nat 11%bv eq_refl). exact H11. }
  { rewrite (RG 12%nat 12%bv eq_refl). exact H12. }
  { exact SPR. }
  { exact S16. }
  { exact W0. }
  { apply DEFR; [clear - SHI; lia | clear - SPTOP STOP; lia | exact W0]. }
  { exact IMC. }
  { exact ZSH. }
  { exact C0. }
  { exact WB. }
  { exact DB. }
  { exact WL. }
  { apply cell_rdn1; [lia | exact INITED]. }
  { exact CS3r. }
  { exact LSAN0. }
  { exact CS2r. }
  { exact CM1r. }
  { exact CM2r. }
  { exact CS1r. }
  { apply cell_rdn1; [lia | exact F3E3]. }
  { exact LSB. }
  { apply cell_rdn1; [lia | exact I99]. }
  { exact RMS. }
  (* [comment removed for export] *)
  assert (KP : forall (i : nat) (r : bv 5), bv_unsigned r = Z.of_nat i -> In i AS0DRVP_icStrerror22r.KS_icStrerror22r -> getr R1 r = getr R r).
  { intros i r E Hi. rewrite <- (RG i r E). apply KEPT. exact Hi. }
  assert (RA1 : getr R1 1 = getr R 1) by (apply (KP 1%nat 1%bv eq_refl); clear; vm_compute; solve [repeat first [left; reflexivity | right]]).
  assert (RUN2 : msteps ASEGS (@mkst fx R (Z_to_bv 64 0x4dc04) Mr0 (seg_rom ASEGS)) (@mkst fx' R1 (getr R 1) Mr1 (seg_rom ASEGS))).
  { eapply msteps_trans; [exact RUN1|]. destruct se_fetch_ret as (w & Fw & Ew & Dw).
    eapply mst_step; [reflexivity | | apply mst_refl].
    rewrite (@step_jalr_x0 fx' ASEGS R1 (Z_to_bv 64 0x521d8) Mr1 (seg_rom ASEGS) w 1%bv 0%bv (getr R 1) Fw Ew Dw RA1).
    change (bv_signed (0%bv : bv 12)) with 0. rewrite (Hret : v_jalr (getr R 1) 0 = getr R 1). reflexivity. }
  (* [comment removed for export] *)
  assert (GEOX : (rn_t rn + 4096 <= 0x10000 \/ 0x633000 <= rn_t rn) /\ (ar_fs (rn_ar rn) + FS_BYTES <= 0x10000 \/ 0x633000 <= ar_fs (rn_ar rn))
                 /\ (rn_dtls rn + 4096 <= 0x10000 \/ 0x633000 <= rn_dtls rn) /\ 4096 <= ar_fs (rn_ar rn)).
  { pose proof ROK as ROK'. rok_open ROK'. geo_open GEO. repeat split; assumption. }
  destruct GEOX as (Gt3 & Gf4 & Gd5 & Gf1).
  assert (ZLS : forall x, art_alloc_zone art_fsg rn G x -> ~ (6360344 <= x < 6360348)).
  { intros x Z X. pose proof ROK as ROK'. rok_open ROK'. geo_open GEO.
    pose proof (art_live_of_binv MAPS0 RESV0 NOACC0 BASE BUDGET rn _ _ _ _ B0 KN) as LIVE.
    unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in Papp. unfold apart in *.
    destruct Z as [Z | [Z | [Z | [Z | [Z | [Z | [Z | [Z | [Z | [Z | [Z | Z]]]]]]]]]]].
    - unfold art_zone_statics in Z. clear - Z X. lia.
    - unfold art_zone_thread in Z. clear - Z X G9. lia.
    - clear - Z X G15. lia.
    - unfold art_zone_kspace in Z. clear - Z X Khi. lia.
    - destruct Z as [Z | (p & Hp & Z)]; [clear - Z X Plo; lia|]. destruct (LIVE p Hp) as (L1 & L2 & L3 & L4 & L5).
      specialize (L5 (0xd7000, 0x55c000) ltac:(unfold art_objs; do 10 right; left; reflexivity)). unfold apart in L5. cbn [fst snd] in L5. clear - Z X L5. lia.
    - unfold art_zone_depot, dprivD in Z. clear - Z X Il2 Iblk. lia.
    - assert (SR : 0x7fff8000 <= x).
      { destruct Z as [Z | (p & Hp & Z)].
        - pose proof (art_S_lo (rn_kbase rn) ltac:(clear - Khi; lia)). clear - Z H. lia.
        - destruct (LIVE p Hp) as (L1 & _). pose proof (art_S_lo (fst p) ltac:(clear - L1; lia)). clear - Z H. lia. }
      clear - SR X. lia.
    - clear - Z X. lia.
    - rewrite Htp in Z. clear - Z X. lia.
    - rewrite Htsd, Hkey0 in Z. clear - Z X. lia.
    - clear - Z X. lia.
    - clear - Z X. lia. }
  set (FP := fun x => sp - 4320 <= x < sp \/ sp + 16 <= x < sp + 33 \/ 6360344 <= x < 6360348).
  apply (art_wrap_pure2x MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Hwx (art_alloc_rep_frame_law_proved art_fsg MAPS0 RESV0) Kt R (Z_to_bv 64 0x4dc04) M model G LB FF LK cr A FP
           (fun _ R' pc1 Mr' => pc1 = getr R 1 /\ getr R' 10 = Z_to_bv 64 0 /\ regs_preserved R R' /\ rdn ASEGS Mr' (Z_to_bv 64 (sp + 16)) 17 = Some (map (Z_to_bv 8) EINVAL_MSG))
           REPr FS B0 CRED CLI KN LZ EG).
  - (* [comment removed for export] *)
    exists fx', R1, (getr R 1), Mr1. split; [exact RUN2|]. split; [exact GR1|].
    split. { intros x Hx. unfold FP in Hx. apply FRW; intros X; apply Hx; clear - X; lia. }
    split. { rewrite Htp, HLoff16. exact BLS. }
    split; [reflexivity|]. split; [rewrite <- (RG 10%nat 10%bv eq_refl); exact E10|]. split.
    + intros r Hr. unfold callee_saved_idx in Hr. cbn [In] in Hr.
      assert (RR : forall k : nat, bv_unsigned r = Z.of_nat k -> In k AS0DRVP_icStrerror22r.KS_icStrerror22r -> getr R1 r = getr R r) by (intros k E Hk; exact (KP k r E Hk)).
      destruct Hr as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]]]]]]]]; symmetry in E;
        [apply (RR 2%nat) | apply (RR 3%nat) | apply (RR 4%nat) | apply (RR 8%nat) | apply (RR 9%nat) | apply (RR 18%nat) | apply (RR 19%nat) | apply (RR 20%nat) | apply (RR 21%nat)
         | apply (RR 22%nat) | apply (RR 23%nat) | apply (RR 24%nat) | apply (RR 25%nat) | apply (RR 26%nat) | apply (RR 27%nat)]; first [exact E | clear; vm_compute; solve [repeat first [left; reflexivity | right]]].
    + rewrite <- se_msg.
      assert (AD : forall k (n : nat) r, 0 <= k -> r = k + Z.of_nat n -> r <= 33 -> (Z_to_bv 64 (sp + k) + nat_to_word n)%bv = Z_to_bv 64 (sp + r)).
      { intros k n r Hk1 -> Hk2. rewrite se_addr by (clear - Hk1 Hk2 SPR; lia). f_equal. ring. }
      change 17%nat with (4 + (4 + (4 + (4 + 1))))%nat.
      apply rdn_app; [exact B16|]. rewrite (AD 16 4%nat 20) by (cbn; lia). apply rdn_app; [exact B20|]. rewrite (AD 20 4%nat 24) by (cbn; lia).
      apply rdn_app; [exact B24|]. rewrite (AD 24 4%nat 28) by (cbn; lia). apply rdn_app; [exact B28|]. rewrite (AD 28 4%nat 32) by (cbn; lia). exact B32.
  - (* [comment removed for export] *)
    intros x [Hx | [Hx | Hx]] Z; exfalso.
    + pose proof (art_zone_below MAPS0 RESV0 NOACC0 BASE BUDGET rn G LB A M Mr0 model x REPr KN B0 (or_introl Z)) as ZB. clear - ZB Hx SHI. lia.
    + pose proof (art_zone_below MAPS0 RESV0 NOACC0 BASE BUDGET rn G LB A M Mr0 model x REPr KN B0 (or_introl Z)) as ZB. clear - ZB Hx SHI. lia.
    + exact (ZLS x Z Hx).
  - (* [comment removed for export] *)
    intros x HF Z3. exfalso. pose proof (art_fs_zone3_below rn G LB _ x REPr Z3) as ZB.
    destruct HF as [Hx | [Hx | Hx]]; [clear - ZB Hx SHI; lia | clear - ZB Hx SHI; lia |].
    unfold fs_zone3 in Z3. rewrite Htp in Z3. clear - Z3 Hx Gt3 Gf4. unfold FS_BYTES in *. lia.
  - (* [comment removed for export] *)
    intros x HF Zc. pose proof (art_cs_zone_below rn G LB FF LK M Mr0 x REPr FS Zc) as ZB.
    destruct HF as [Hx | [Hx | Hx]]; [clear - ZB Hx SHI; lia | clear - ZB Hx SHI; lia |].
    unfold cs_zone in Zc. rewrite Htp in Zc. change (HeapIfaceA.S 0x10000) with 2147459072 in Zc. clear - Zc Hx Gd5. lia.
  - (* [comment removed for export] *)
    intros b x Hb Hx HF. pose proof (art_block_shadow_below rn LB FF LK A M b x CLI Hb Hx) as B1.
    destruct (CB b Hb) as (K1 & _). pose proof (art_S_lo (fst b) ltac:(clear - K1; lia)) as B2. destruct Hx as (Hx1 & _).
    destruct HF as [X | [X | X]]; [clear - X B1 SHI HI1; lia | clear - X B1 SHI HI1; lia | clear - X Hx1 B2; lia].
  - (* [comment removed for export] *)
    intros fx2 R' pc1 Mr' M1 model' (Epc & E10' & RP & MSG) RI' GROW FR1 VIS1 HID RT MI'. subst pc1.
    apply (CONT fx2 R' M1 model' E10' RP); [ | | | exact GROW | exact RT | exact MI' | exact RI'].
    + rewrite <- MSG. apply rdn_ext; [rewrite art_u_lit by (clear - SPR; lia); cbn; clear - SPR; lia|].
      intros x Hx. rewrite art_u_lit in Hx by (clear - SPR; lia). cbn in Hx. apply VIS1. apply VSTK. clear - Hx SHI. lia.
    + intros a Ra Ha NB. apply FR1. rewrite art_u_lit by exact Ra. unfold FP. intros [X | [X | X]].
      * apply (art_cls_off_scratch rn LB FF LK A M CLI L HLlo HLhi (g_fs art_fsg G) FS sp 4320 a ltac:(clear - SHI; lia) (or_intror Ha)). clear - X. lia.
      * exact (NB X).
      * (* [comment removed for export] *)
        pose proof (fsinv_frame_in rn _ _ _ _ FS) as FIN.
        destruct Ha as [H | [H | [H | [H | [H | [H | H]]]]]]; rewrite ?HLlo, ?HLhi in H.
        -- destruct H as (b & Hb & Rb). destruct (CB b Hb) as (_ & K2 & _). clear - Rb K2 X. lia.
        -- rewrite HIeq in H. clear - H X HI1. lia.
        -- destruct H as (_ & NS). apply NS. apply HLlsan. clear - X. lia.
        -- destruct H as (f & Hf & R1' & _). destruct (FIN f ltac:(apply in_or_app; left; exact Hf)) as (I1 & I2 & _). unfold FS_BYTES in I2. clear - R1' I1 I2 X Gf4. unfold FS_BYTES in Gf4. lia.
        -- destruct H as (H1' & _). pose proof (art_S_lo (rn_HI rn) ltac:(clear - HI1; lia)) as SL. rewrite HIeq in H1'. clear - H1' SL X. lia.
        -- destruct H as (f & Hf & (H1' & _)). destruct (FIN f ltac:(apply in_or_app; left; exact Hf)) as (I1 & _). pose proof (art_S_lo (ff_addr f) ltac:(clear - I1 Gf1; lia)) as SL. clear - H1' SL X. lia.
        -- destruct H as (b & Hb & (H1' & _)). destruct (CB b Hb) as (K1 & _). pose proof (art_S_lo (fst b) ltac:(clear - K1; lia)) as SL. clear - H1' SL X. lia.
    + intros a Ha. apply GROW.
      assert (WM : wrA M (sp - 4320) 4320) by (intros d m Hd Hm; apply SWR; assumption).
      pose proof (art_wr_wview ASEGS M (sp - 4320) 4320 ltac:(clear - SHI HI1; lia) ltac:(clear - SPTOP STOP; lia) WM (Z_to_bv 64 a)) as Vw. rewrite art_u_lit in Vw by (clear - Ha SPR; lia). specialize (Vw ltac:(clear - Ha; lia)).
      rewrite art_wview_off in Vw by (rewrite art_u_lit by (clear - Ha SPR; lia); right; clear - Ha SHI HI1; lia). exact Vw.
Qed.
End WSE.
