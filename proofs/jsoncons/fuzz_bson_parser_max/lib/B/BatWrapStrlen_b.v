(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct RefMemcpyLib HeapIface HeapIfaceA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtMem ArtRuns ArtRunsMem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatCls_b BatCellEx_b BatPoison_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtBridge. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatInv_b BatInvMalloc_b BatLift_b BatWrapKit_b BatFsInv_b BatFsInvLaws_b BatIfaceLaws_b BatInvFrame_b Ba0RegionPoisoned_b Ba0AsanMemcpy_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.muslA Require Import Ba0Memchr_b Ba0SegStrlen_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0StrlenIcpt_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatWrapC_b BatWrapVis_b BatWrapC2_b BatWrapRng_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
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

#[using="Hwx HLsegs HLlo HLhi"] Theorem art_wrap_strlen : forall (R : bvmap 5 word) (M : word -> option byte) (model : Model)
    (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (s K : Z) (buf : list byte) (Kt : ShapeAlg.TSet),
  let sp := U (getr R 2) in
  RI LB FF LK cr A M (vml_of model) -> m_halted model = None -> MInv A model ->
  getr R 10 = Z_to_bv 64 s -> Hoare.ret_ok (getr R 1) ->
  astack_ok L (rn_ar rn) M 2304 sp ->
  0 <= s -> s + Z.of_nat (length buf) <= 2 ^ 47 -> 0 <= K < 2 ^ 27 ->
  rdn ASEGS M (Z_to_bv 64 s) (length buf) = Some buf ->
  (s + K) / 8 * 8 + 8 <= s + Z.of_nat (length buf) ->
  nth (Z.to_nat K) buf (Z_to_bv 8 0) = Z_to_bv 8 0 ->
  (forall j, (j < Z.to_nat K)%nat -> nth j buf (Z_to_bv 8 0) <> Z_to_bv 8 0) ->
  (forall i, 0 <= i < Z.of_nat (length buf) -> hl_img_lo L <= s + i < hl_img_hi L \/ aclient L (rn_ar rn) LB FF sp 2304 (s + i)) ->
  (forall a, 0x103b0 <= a < 0x103d0 -> M (Z_to_bv 64 a) = None) ->
  aacc M s (K + 1) -> app_rng (rn_ar rn) s (K + 1) ->
  Kt [] ->
  (forall (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model),
      getr R' 10 = Z_to_bv 64 K -> regs_preserved R R' ->
      (forall a, 0 <= a < 2 ^ 64 -> aclient L (rn_ar rn) LB FF sp 2304 a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
      (forall a, sp - 2304 <= a < sp -> M' (Z_to_bv 64 a) <> None) ->
      (forall a : word, M a <> None -> M' a <> None) ->
      model_rt model model' -> MInv A model' ->
      RI LB FF LK cr A M' (vml_of model') ->
      srealizes ASEGS scfg (mkCfg (mkst R' (getr R 1) M' (seg_rom ASEGS)) model') Kt) ->
  srealizes ASEGS scfg (mkCfg (mkst R (0x6336c : word) M (seg_rom ASEGS)) model) Kt.
Proof.
  intros R M model LB FF LK cr A s K buf Kt sp INV Hhalt HMI H10 Hret AST Hs0 Hs47 HK RD WIN NUL NZ CLS RO AACC APPR KT0 CONT.
  destruct (art_ri_open MAPS0 RESV0 NOACC0 BASE BUDGET rn LB FF LK cr A M model INV Hhalt HMI) as (G & REPr & FS & B0 & CRED & CLI & KN & LZ & EG).
  set (Mr0 := mrestrict (bhid A model) M) in *.
  destruct AST as (S16 & SHI & SLE & STOP & SWR & SDEF). fold sp in S16, SHI, SLE, SWR, SDEF. rewrite HLsegs in SWR.
  assert (HIeq : ahl_ceil (rn_ar rn) = rn_HI rn) by reflexivity. rewrite HIeq in SHI.
  change (2 ^ 27) with 134217728 in HK.
  pose proof (art_cli_hi rn LB FF LK A M CLI) as (HI1 & HI2).
  pose proof REPr as (ROK & STAT & _).
  assert (LEN1 : K + 1 <= Z.of_nat (length buf)).
  { pose proof (Z.div_mod (s + K) 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (s + K) 8 ltac:(lia)). clear - WIN D H. lia. }
  assert (LAZY : forall w : word, page_in_ranges (page_base w) (m_vm_lazy model) = true ->
            0x696000 <= U w /\ U w < rn_HI rn /\ ~ in_block LB (U w) /\ ~ (ar_fs (rn_ar rn) <= U w < ar_fs (rn_ar rn) + FS_BYTES)).
  { intros w Hw. destruct LZ as (L1 & _). destruct (art_lazy_zone_bounds art_fsg rn G (U w) ROK (L1 w Hw)) as (B1 & B2).
    split; [lia|]. split; [exact (proj2 B1)|]. split; [|exact B2]. intros (b & Hb & Hr). rewrite (proj2 EG b w Hb Hr) in Hw. discriminate Hw. }
  assert (OFFSCR : forall i, 0 <= i < Z.of_nat (length buf) -> ~ (sp - 2304 <= s + i < sp)).
  { intros i Hi. apply (art_cls_off_scratch rn LB FF LK A M CLI L HLlo HLhi (g_fs art_fsg G) FS sp 2304 (s + i) ltac:(lia) (CLS i Hi)). }
  assert (HDJ : s + Z.of_nat (length buf) <= sp - 2216 \/ sp <= s).
  { destruct (art_rng_off_window s (Z.of_nat (length buf)) (sp - 2304) sp ltac:(clear - LEN1 HK; lia) ltac:(lia) OFFSCR) as [X | X]; [left; lia | right; exact X]. }
  destruct (art_rng_facts rn LB FF LK A M model LAZY CLI L HLlo HLhi (g_fs art_fsg G) FS (bi_shdef _ _ _ _ _ _ _ _ _ _ _ B0) sp 2304 s (K + 1) Hs0 ltac:(clear - HK; lia) ltac:(clear - HK; lia)
              ltac:(intros i Hi; apply CLS; clear - Hi LEN1; lia) AACC APPR) as (_ & (FL1 & FL2) & HZS & (kS & HLS & HkS) & HWS).
  set (FP := fun x => sp - 2216 <= x < sp).
  apply (art_wrap_pure2 MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Hwx (art_alloc_rep_frame_law_proved art_fsg MAPS0 RESV0) Kt R (0x6336c : word) M model G LB FF LK cr A FP
           (fun R' pc1 Mr' => pc1 = getr R 1 /\ getr R' 10 = Z_to_bv 64 K /\ keeps_cs R R') REPr FS B0 CRED CLI KN LZ EG).
  - (* [comment removed for export] *)
    assert (VISB : art_vis (bhid A model) s (Z.of_nat (length buf))).
    { intros x Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x).
      apply (art_aclient_vis rn LB FF LK A M model LAZY CLI L HLlo HLhi (g_fs art_fsg G) FS sp 2304 (U x)); [pose proof (u64_range x); lia|].
      replace (U x) with (s + (U x - s)) by ring. apply CLS. clear - Hx. lia. }
    assert (HSLEN : slenH Mr0 (Z_to_bv 64 s) buf K).
    { constructor.
      - exact (art_rng_rdn A M model s (length buf) buf Hs0 ltac:(clear - Hs47; lia) VISB RD).
      - rewrite art_u_lit by (clear - Hs0 Hs47; lia). exact WIN.
      - rewrite art_u_lit by (clear - Hs0 Hs47; lia). clear - Hs47. lia.
      - clear - HK. lia.
      - rewrite NUL. reflexivity.
      - intros j Hj E. apply (NZ j Hj). apply bv_eq. rewrite E. reflexivity.
      - intros i Hi. unfold Mr0, mrestrict. rewrite (RO i Hi). destruct (bhid A model (Z_to_bv 64 i)); reflexivity. }
    assert (W0 : wrA Mr0 (sp - 2304) 2304).
    { apply (art_stack_wr art_fsg rn G A (m_vm_lazy model) M sp 2304 ROK LZ ltac:(lia) ltac:(lia) ltac:(lia)). exact SWR. }
    assert (HOK : store_ok ASEGS Mr0 (Z_to_bv 64 (sp - 2216)) 2216 = true).
    { replace (sp - 2216) with (sp - 2304 + 88) by ring. apply W0; [lia | cbn; lia]. }
    destruct STAT as (_ & LAY & _ & _ & _ & _ & _ & S8).
    assert (HGL : rt_layout_globs Mr0).
    { destruct LAY as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & _). unfold rt_layout_globs. repeat split; [lit_cell A1 | lit_cell A2 | lit_cell A3 | lit_cell A4 | lit_cell A5 | lit_cell A6 | lit_cell A7 | lit_cell A8]. }
    assert (VIMG : forall a (n : nat), 0x10000 <= a -> a + Z.of_nat n <= 0x696000 -> art_vis (bhid A model) a (Z.of_nat n)).
    { intros a n H1 H2 x Hx. apply (art_vis_byte rn LB A model LAZY). left. lia. }
    assert (HIC : sl_icpt_globs Mr0).
    { destruct LAY as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & A13 & _).
      assert (INITED : cellA Mr0 0x140918 1 1) by conj_find S8.
      assert (C2r : cellA Mr0 0x1d1863 1 1) by conj_find S8.
      destruct (fsinv_cs _ _ _ _ _ FS) as (_ & CS1 & _).
      assert (C1r : cellA Mr0 0x1392d8 8 0x12a1e8) by (apply (proj2 (art_cell_vis (bhid A model) M 0x1392d8 8 0x12a1e8 ltac:(lia) ltac:(cbn; lia) (VIMG 0x1392d8 8%nat ltac:(lia) ltac:(cbn; lia)))); exact CS1).
      unfold sl_icpt_globs. repeat split.
      - rewrite <- le1_one. lit_cell INITED.
      - lit_cell C1r.
      - lit_cell A13.
      - rewrite <- le1_one. lit_cell C2r. }
    set (fS := Ba0RegionPoisoned_b.SB + s / 8) in *. set (lS := Ba0RegionPoisoned_b.SB + (s + (K + 1) - 1) / 8) in *.
    assert (HKK : 0 <= K /\ K + 1 <= 2 ^ 40) by (clear - HK; lia).
    assert (HSs : 16777216 <= sp - 2216 /\ sp < 2 ^ 64) by (clear - SHI SLE STOP HI1; lia).
    assert (HSH : lS + 8 <= sp - 2216) by (clear - FL2 SHI; lia).
    destruct (wrap_strlen_run Mr0 (seg_rom ASEGS) (getr R 2) (getr R 1) s K (K + 1) sp buf kS fS lS (fS - fS mod 8) (lS - lS mod 8)
                eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl HKK (art_rng_app8 rn LB FF LK A M CLI s (K + 1) Hs0 ltac:(clear - HK; lia) APPR) HSs HSH HSLEN HDJ HOK Hret HGL HIC
                (fun _ => HZS) (fun _ => HLS) HkS (fun _ => HWS) R H10 eq_refl eq_refl)
      as (R' & M' & RUN & Q10 & Q2 & Q1 & KCS & OA & GRr).
    exists R', (getr R 1), M'. split; [exact RUN|]. split; [exact GRr|].
    assert (FRr : forall x : word, ~ FP (U x) -> M' x = Mr0 x) by (intros x Hx; apply OA; unfold FP in Hx; clear - Hx; lia).
    split; [exact FRr|]. split; [|split; [reflexivity | split; [exact Q10 | exact KCS]]].
    apply (art_lsan_kept rn G LB Mr0 M' FP REPr FRr). intros x Hx. unfold FP in Hx. clear - Hx SHI. lia.
  - intros x Hx Z. exfalso. pose proof (art_zone_below MAPS0 RESV0 NOACC0 BASE BUDGET rn G LB A M Mr0 model x REPr KN B0 (or_introl Z)). unfold FP in Hx. clear - H Hx SHI. lia.
  - intros x Hx Z3. exfalso. pose proof (art_fs_zone3_below rn G LB _ x REPr Z3). unfold FP in Hx. clear - H Hx SHI. lia.
  - intros x Hx Zc. pose proof (art_cs_zone_below rn G LB FF LK M Mr0 x REPr FS Zc). unfold FP in Hx. clear - H Hx SHI. lia.
  - intros b x Hb Hx X. pose proof (art_block_shadow_below rn LB FF LK A M b x CLI Hb Hx). unfold FP in X. clear - H X SHI HI1. lia.
  - (* [comment removed for export] *)
    intros R' pc1 Mr' M1 model' (Epc & Q10 & KCS) RI' GROW FR1 VIS HID RT MI'. subst pc1.
    apply (CONT R' M1 model' Q10 (keeps_cs_preserved R R' KCS)); [ | | exact GROW | exact RT | exact MI' | exact RI'].
    + intros a Ra Ha. apply FR1. rewrite art_u_lit by exact Ra. unfold FP. intros X.
      apply (art_cls_off_scratch rn LB FF LK A M CLI L HLlo HLhi (g_fs art_fsg G) FS sp 2304 a ltac:(clear - SHI; lia) (or_intror Ha)). clear - X. lia.
    + intros a Ha. apply GROW.
      assert (WM : wrA M (sp - 2304) 2304) by (intros d k Hd Hk; apply SWR; assumption).
      pose proof (art_wr_wview ASEGS M (sp - 2304) 2304 ltac:(clear - SHI HI1; lia) ltac:(clear - SLE STOP; lia) WM (Z_to_bv 64 a)) as V. rewrite art_u_lit in V by (clear - Ha SHI HI1 SLE STOP; lia). specialize (V ltac:(clear - Ha; lia)).
      rewrite art_wview_off in V by (rewrite art_u_lit by (clear - Ha SHI HI1 SLE STOP; lia); right; clear - Ha SHI HI1; lia). exact V.
Qed.
End WS.

Lemma lit_62f54 : Z_to_bv 64 0x6336c = (0x6336c%bv : word). Proof. apply bv_eq. reflexivity. Qed.

(* [comment removed for export] *)
Theorem art_astrlen : forall MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg, wx_segs_nowrap ASEGS -> forall (L : asan_layout) (IL : icpt_layout),
  hl_segs L = ASEGS -> hl_img_lo L = 0x10000 -> hl_img_hi L = 0x696000 ->
  icl_strlen IL = 0x6336c -> icl_scr_strlen IL = 2304 -> icl_ro_lo IL = 0x103b0 -> icl_ro_hi IL = 0x103d0 ->
  astrlen_spec L (rn_ar rn) IL scfg (art_iface art_fsg MAPS0 RESV0 NOACC0 BASE BUDGET art_fsinv rn).
Proof.
  intros MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Hwx L IL HLsegs HLlo HLhi E1 E2 E3 E4 fx R M model LB FF LK cr A s K buf Kt. cbv zeta.
  intros INV Hh HMI H10 H4 Hret AST Hs0 Hs47 HK RD WIN NUL NZ CLS RO AACC APPR KT0 POST.
  rewrite HLsegs, E2 in *. rewrite E3, E4 in RO. rewrite E1, lit_62f54.
  apply (art_wrap_strlen MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Hwx L HLsegs HLlo HLhi R M model LB FF LK cr A s K buf Kt INV Hh HMI H10 Hret AST Hs0 Hs47 HK RD WIN NUL NZ CLS RO AACC APPR KT0).
  intros R' M' model' Q10 RP FR SD GR RT MI' RI'. apply (POST R' M' model' Q10 RP FR SD GR RT MI' RI').
Qed.
