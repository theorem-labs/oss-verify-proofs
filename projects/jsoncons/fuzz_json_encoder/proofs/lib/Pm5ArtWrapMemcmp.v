(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct RefMemcpyLib HeapIface HeapIfaceA PmHeapIfaceA IcptIfaceA PmIcptIfaceA ArtMem ArtRuns ArtRunsMem Pm5ArtCls Pm5ArtCellEx Pm5ArtPoison
     ArtBridge Pm5ArtInv Pm5ArtInvMalloc Pm5ArtLift Pm5ArtWrapKit Pm5ArtFsInv Pm5ArtFsInvLaws Pm5ArtIfaceLaws Pm5ArtInvFrame Pm5RegionPoisoned Pm5AsanMemcpy Pm5MemcmpMicI Pm5MemcmpIcptI Pm5MemcmpIcptO.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import Pm5ArtWrapC Pm5ArtWrapVis Pm5ArtWrapC2 Pm5ArtWrapRng.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Section WMC.
Variables MAPS0 RESV0 NOACC0 : list (word * word).
Variables BASE BUDGET : Z.
Variable rn : art_run.
Variable scfg : SpuriousCfg.
Hypothesis Hwx : wx_segs_nowrap ASEGS.
Variable L : asan_layout.
Hypothesis HLsegs : hl_segs L = ASEGS.
Hypothesis HLlo : hl_img_lo L = 0x10000.
Hypothesis HLhi : hl_img_hi L = 0x6c4000.
#[local] Abbreviation RI := (art_ri_inv art_fsg MAPS0 RESV0 NOACC0 BASE BUDGET art_fsinv rn).
Context {fx : PropExec.FPState}.

Theorem art_wrap_bcmp : forall (R : bvmap 5 word) (M : word -> option byte) (model : Model)
    (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (p q n : Z) (b1 b2 : list byte) (Kt : ShapeAlg.TSet),
  let sp := U (getr R 2) in
  RI LB FF LK cr A M (vml_of model) -> m_halted model = None -> MInv A model ->
  getr R 10 = Z_to_bv 64 p -> getr R 11 = Z_to_bv 64 q -> getr R 12 = Z_to_bv 64 n -> 0 <= n <= 2 ^ 27 ->
  Hoare.ret_ok (getr R 1) ->
  astack_ok L (rn_ar rn) M 8192 sp ->
  0 <= p -> p + n <= 2 ^ 47 -> 0 <= q -> q + n <= 2 ^ 47 ->
  rdn ASEGS M (Z_to_bv 64 p) (Z.to_nat n) = Some b1 -> rdn ASEGS M (Z_to_bv 64 q) (Z.to_nat n) = Some b2 ->
  (forall i, 0 <= i < n -> hl_img_lo L <= p + i < hl_img_hi L \/ aclient L (rn_ar rn) LB FF sp 8192 (p + i)) ->
  (forall i, 0 <= i < n -> hl_img_lo L <= q + i < hl_img_hi L \/ aclient L (rn_ar rn) LB FF sp 8192 (q + i)) ->
  aacc M p n -> aacc M q n -> app_rng (rn_ar rn) p n -> app_rng (rn_ar rn) q n ->
  Kt [] ->
  (forall (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model),
      getr R' 10 = Z_to_bv 64 (memcmp_val b1 b2) -> regs_preserved R R' ->
      (forall a, 0 <= a < 2 ^ 64 -> aclient L (rn_ar rn) LB FF sp 8192 a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
      (forall a, sp - 8192 <= a < sp -> M' (Z_to_bv 64 a) <> None) ->
      (forall a : word, M a <> None -> M' a <> None) ->
      model_rt model model' -> MInv A model' ->
      RI LB FF LK cr A M' (vml_of model') ->
      srealizes ASEGS scfg (mkCfg (mkst R' (getr R 1) M' (seg_rom ASEGS)) model') Kt) ->
  srealizes ASEGS scfg (mkCfg (mkst R (0x6c200 : word) M (seg_rom ASEGS)) model) Kt.
Proof.
  intros R M model LB FF LK cr A p q n b1 b2 Kt sp INV Hhalt HMI H10 H11 H12 Hn Hret AST Hp0 Hp47 Hq0 Hq47 RD1 RD2 CLS1 CLS2 AACC1 AACC2 APPR1 APPR2 KT0 CONT.
  destruct (art_ri_open MAPS0 RESV0 NOACC0 BASE BUDGET rn LB FF LK cr A M model INV Hhalt HMI) as (G & REPr & FS & B0 & CRED & CLI & KN & LZ & EG).
  set (Mr0 := mrestrict (bhid A model) M) in *.
  destruct AST as (S16 & SHI & SLE & STOP & SWR & SDEF). fold sp in S16, SHI, SLE, SWR, SDEF. rewrite HLsegs in SWR.
  assert (HIeq : ahl_ceil (rn_ar rn) = rn_HI rn) by reflexivity. rewrite HIeq in SHI.
  change (2 ^ 27) with 134217728 in Hn.
  pose proof (art_cli_hi rn LB FF LK A M CLI) as (HI1 & HI2).
  pose proof REPr as (ROK & STAT & _).
  assert (LAZY : forall w : word, page_in_ranges (page_base w) (m_vm_lazy model) = true ->
            0x6c4000 <= U w /\ U w < rn_HI rn /\ ~ in_block LB (U w) /\ ~ (ar_fs (rn_ar rn) <= U w < ar_fs (rn_ar rn) + FS_BYTES)).
  { intros w Hw. destruct LZ as (L1 & _). destruct (art_lazy_zone_bounds art_fsg rn G (U w) ROK (L1 w Hw)) as (B1 & B2).
    split; [lia|]. split; [exact (proj2 B1)|]. split; [|exact B2]. intros (b & Hb & Hr). rewrite (proj2 EG b w Hb Hr) in Hw. discriminate Hw. }
  (* [comment removed for export] *)
  assert (OFF1 : forall i, 0 <= i < n -> ~ (sp - 8192 <= p + i < sp)).
  { intros i Hi. apply (art_cls_off_scratch rn LB FF LK A M CLI L HLlo HLhi (g_fs art_fsg G) FS sp 8192 (p + i) ltac:(lia) (CLS1 i Hi)). }
  assert (HDJ1 : 0 < n -> p + n <= sp - 4552 \/ sp <= p).
  { intros Hn0. destruct (art_rng_off_window p n (sp - 8192) sp Hn0 ltac:(lia) OFF1) as [X | X]; [left; lia | right; exact X]. }
  set (f1 := Pm5RegionPoisoned.SB + p / 8). set (l1 := Pm5RegionPoisoned.SB + (p + n - 1) / 8).
  assert (D471 : p + n + 16 <= 2 ^ 47).
  { destruct APPR1 as (_ & _ & TOP). destruct (art_cli_facts _ _ _ _ _ _ CLI) as (_ & _ & _ & T16). clear - TOP T16. lia. }
  assert (HSH1 : l1 + 8 <= sp - 4552).
  { unfold l1, Pm5RegionPoisoned.SB. assert ((p + n - 1) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; clear - D471; lia). change (2 ^ 47 / 8) with 17592186044416 in *. clear - H SHI HI1. lia. }
  assert (RNG1 : art_vis (bhid A model) p n
                /\ (0 < n -> forall x : word, f1 <= U x < l1 -> Mr0 x = Some (Z_to_bv 8 0))
                /\ (exists kL, (0 < n -> Mr0 (Z_to_bv 64 l1) = Some (Z_to_bv 8 kL)) /\ (kL = 0 \/ (p + n - 1) mod 8 < kL <= 7))
                /\ (0 < n <= 64 -> exists w0 w1, rdn ASEGS Mr0 (Z_to_bv 64 (f1 - f1 mod 8)) 8 = Some w0 /\ rdn ASEGS Mr0 (Z_to_bv 64 (l1 - l1 mod 8)) 8 = Some w1)).
  { destruct (Z_lt_le_dec 0 n) as [Np | Nz].
    - destruct (art_rng_facts rn LB FF LK A M model LAZY CLI L HLlo HLhi (g_fs art_fsg G) FS (bi_shdef _ _ _ _ _ _ _ _ _ _ _ B0) sp 8192 p n Hp0 Np ltac:(clear - Hn; lia) CLS1 AACC1 APPR1)
        as (VIS & _ & HZ & (kL & HL & HkL) & HW).
      split; [exact VIS|]. split; [intros _; exact HZ|]. split; [exists kL; split; [intros _; exact HL | exact HkL]|]. intros _. exact HW.
    - split; [intros x Hx; exfalso; clear - Hx Nz; lia|]. split; [intros X; exfalso; clear - X Nz; lia|].
      split; [exists 0; split; [intros X; exfalso; clear - X Nz; lia | left; reflexivity]|]. intros X; exfalso; clear - X Nz; lia. }
  destruct RNG1 as (VIS1 & HZ1 & (k1 & HL1 & Hk1) & HW1).
  (* [comment removed for export] *)
  assert (OFF2 : forall i, 0 <= i < n -> ~ (sp - 8192 <= q + i < sp)).
  { intros i Hi. apply (art_cls_off_scratch rn LB FF LK A M CLI L HLlo HLhi (g_fs art_fsg G) FS sp 8192 (q + i) ltac:(lia) (CLS2 i Hi)). }
  assert (HDJ2 : 0 < n -> q + n <= sp - 4552 \/ sp <= q).
  { intros Hn0. destruct (art_rng_off_window q n (sp - 8192) sp Hn0 ltac:(lia) OFF2) as [X | X]; [left; lia | right; exact X]. }
  set (f2 := Pm5RegionPoisoned.SB + q / 8). set (l2 := Pm5RegionPoisoned.SB + (q + n - 1) / 8).
  assert (D472 : q + n + 16 <= 2 ^ 47).
  { destruct APPR2 as (_ & _ & TOP). destruct (art_cli_facts _ _ _ _ _ _ CLI) as (_ & _ & _ & T16). clear - TOP T16. lia. }
  assert (HSH2 : l2 + 8 <= sp - 4552).
  { unfold l2, Pm5RegionPoisoned.SB. assert ((q + n - 1) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; clear - D472; lia). change (2 ^ 47 / 8) with 17592186044416 in *. clear - H SHI HI1. lia. }
  assert (RNG2 : art_vis (bhid A model) q n
                /\ (0 < n -> forall x : word, f2 <= U x < l2 -> Mr0 x = Some (Z_to_bv 8 0))
                /\ (exists kL, (0 < n -> Mr0 (Z_to_bv 64 l2) = Some (Z_to_bv 8 kL)) /\ (kL = 0 \/ (q + n - 1) mod 8 < kL <= 7))
                /\ (0 < n <= 64 -> exists w0 w1, rdn ASEGS Mr0 (Z_to_bv 64 (f2 - f2 mod 8)) 8 = Some w0 /\ rdn ASEGS Mr0 (Z_to_bv 64 (l2 - l2 mod 8)) 8 = Some w1)).
  { destruct (Z_lt_le_dec 0 n) as [Np | Nz].
    - destruct (art_rng_facts rn LB FF LK A M model LAZY CLI L HLlo HLhi (g_fs art_fsg G) FS (bi_shdef _ _ _ _ _ _ _ _ _ _ _ B0) sp 8192 q n Hq0 Np ltac:(clear - Hn; lia) CLS2 AACC2 APPR2)
        as (VIS & _ & HZ & (kL & HL & HkL) & HW).
      split; [exact VIS|]. split; [intros _; exact HZ|]. split; [exists kL; split; [intros _; exact HL | exact HkL]|]. intros _. exact HW.
    - split; [intros x Hx; exfalso; clear - Hx Nz; lia|]. split; [intros X; exfalso; clear - X Nz; lia|].
      split; [exists 0; split; [intros X; exfalso; clear - X Nz; lia | left; reflexivity]|]. intros X; exfalso; clear - X Nz; lia. }
  destruct RNG2 as (VIS2 & HZ2 & (k2 & HL2 & Hk2) & HW2).
  set (FP := fun x => sp - 4552 <= x < sp).
  apply (art_wrap_pure2 MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Hwx (art_alloc_rep_frame_law_proved art_fsg MAPS0 RESV0) Kt R (0x6c200 : word) M model G LB FF LK cr A FP
           (fun R' pc1 Mr' => pc1 = getr R 1 /\ getr R' 10 = Z_to_bv 64 (memcmp_val b1 b2) /\ keeps_cs R R') REPr FS B0 CRED CLI KN LZ EG).
  - (* [comment removed for export] *)
    assert (RD1r : rdn ASEGS Mr0 (Z_to_bv 64 p) (Z.to_nat n) = Some b1).
    { apply (art_rng_rdn A M model p (Z.to_nat n) b1 Hp0 ltac:(rewrite Z2Nat.id by (clear - Hn; lia); clear - Hp47; lia)); [|exact RD1]. rewrite Z2Nat.id by (clear - Hn; lia). exact VIS1. }
    assert (RD2r : rdn ASEGS Mr0 (Z_to_bv 64 q) (Z.to_nat n) = Some b2).
    { apply (art_rng_rdn A M model q (Z.to_nat n) b2 Hq0 ltac:(rewrite Z2Nat.id by (clear - Hn; lia); clear - Hq47; lia)); [|exact RD2]. rewrite Z2Nat.id by (clear - Hn; lia). exact VIS2. }
    assert (W0 : wrA Mr0 (sp - 8192) 8192).
    { apply (art_stack_wr art_fsg rn G A (m_vm_lazy model) M sp 8192 ROK LZ ltac:(lia) ltac:(lia) ltac:(lia)). exact SWR. }
    assert (HOK : store_ok ASEGS Mr0 (Z_to_bv 64 (sp - 4552)) 4552 = true).
    { replace (sp - 4552) with (sp - 8192 + (8192 - 4552)) by ring. apply W0; [lia | cbn; lia]. }
    destruct STAT as (_ & LAY & _ & _ & _ & _ & _ & S8).
    assert (HGL : rt_layout_globs Mr0).
    { destruct LAY as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & _). unfold rt_layout_globs. repeat split; [lit_cell A1 | lit_cell A2 | lit_cell A3 | lit_cell A4 | lit_cell A5 | lit_cell A6 | lit_cell A7 | lit_cell A8]. }
    assert (HIC : mcmp_icpt_globs Mr0).
    { destruct LAY as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & A13 & _).
      assert (C1r : cellA Mr0 0x1ff3e6 1 1) by conj_find S8.
      assert (C2r : cellA Mr0 0x1ff3e7 1 1) by conj_find S8.
      unfold mcmp_icpt_globs. repeat split.
      - lit_cell A13.
      - rewrite <- le1_one. lit_cell C1r.
      - rewrite <- le1_one. lit_cell C2r. }
    assert (INITED : cellA Mr0 0x16e498 1 1) by conj_find S8.
    assert (HCI : icptI_globs Mr0).
    { assert (C3r : cellA Mr0 0x166378 8 0x156488) by conj_find S8.
      unfold icptI_globs. split; [rewrite <- le1_one; lit_cell INITED | lit_cell C3r]. }
    assert (HCO : icptO_globs Mr0).
    { assert (C4r : cellA Mr0 0x166380 8 0x1563b8) by conj_find S8.
      unfold icptO_globs. split; [rewrite <- le1_one; lit_cell INITED | lit_cell C4r]. }
    assert (HSs : 0x1000000 <= sp - 4552 /\ sp < 2 ^ 64) by (clear - SHI SLE STOP HI1; lia).
    destruct (wrap_bcmp_pk Mr0 (seg_rom ASEGS) (getr R 2) (getr R 1) p q n sp b1 b2 k1 f1 l1 (f1 - f1 mod 8) (l1 - l1 mod 8) k2 f2 l2 (f2 - f2 mod 8) (l2 - l2 mod 8)
                eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(clear - Hn; lia)
                (art_rng_app8 rn LB FF LK A M CLI p n Hp0 ltac:(clear - Hn; lia) APPR1) (art_rng_app8 rn LB FF LK A M CLI q n Hq0 ltac:(clear - Hn; lia) APPR2)
                HSs HSH1 HSH2 HDJ1 HDJ2 HOK RD1r RD2r Hret HGL HIC HCO HCI HZ1 HL1 Hk1 HW1 HZ2 HL2 Hk2 HW2 R H10 H11 H12 eq_refl eq_refl)
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
      apply (art_cls_off_scratch rn LB FF LK A M CLI L HLlo HLhi (g_fs art_fsg G) FS sp 8192 a ltac:(clear - SHI; lia) (or_intror Ha)). clear - X. lia.
    + intros a Ha. apply GROW.
      assert (WM : wrA M (sp - 8192) 8192) by (intros d k Hd Hk; apply SWR; assumption).
      pose proof (art_wr_wview ASEGS M (sp - 8192) 8192 ltac:(clear - SHI HI1; lia) ltac:(clear - SLE STOP; lia) WM (Z_to_bv 64 a)) as V. rewrite art_u_lit in V by (clear - Ha SHI HI1 SLE STOP; lia). specialize (V ltac:(clear - Ha; lia)).
      rewrite art_wview_off in V by (rewrite art_u_lit by (clear - Ha SHI HI1 SLE STOP; lia); right; clear - Ha SHI HI1; lia). exact V.
Qed.

Theorem art_wrap_memcmp : forall (R : bvmap 5 word) (M : word -> option byte) (model : Model)
    (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (p q n : Z) (b1 b2 : list byte) (Kt : ShapeAlg.TSet),
  let sp := U (getr R 2) in
  RI LB FF LK cr A M (vml_of model) -> m_halted model = None -> MInv A model ->
  getr R 10 = Z_to_bv 64 p -> getr R 11 = Z_to_bv 64 q -> getr R 12 = Z_to_bv 64 n -> 0 <= n <= 2 ^ 27 ->
  Hoare.ret_ok (getr R 1) ->
  astack_ok L (rn_ar rn) M 8192 sp ->
  0 <= p -> p + n <= 2 ^ 47 -> 0 <= q -> q + n <= 2 ^ 47 ->
  rdn ASEGS M (Z_to_bv 64 p) (Z.to_nat n) = Some b1 -> rdn ASEGS M (Z_to_bv 64 q) (Z.to_nat n) = Some b2 ->
  (forall i, 0 <= i < n -> hl_img_lo L <= p + i < hl_img_hi L \/ aclient L (rn_ar rn) LB FF sp 8192 (p + i)) ->
  (forall i, 0 <= i < n -> hl_img_lo L <= q + i < hl_img_hi L \/ aclient L (rn_ar rn) LB FF sp 8192 (q + i)) ->
  aacc M p n -> aacc M q n -> app_rng (rn_ar rn) p n -> app_rng (rn_ar rn) q n ->
  Kt [] ->
  (forall (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model),
      getr R' 10 = Z_to_bv 64 (memcmp_val b1 b2) -> regs_preserved R R' ->
      (forall a, 0 <= a < 2 ^ 64 -> aclient L (rn_ar rn) LB FF sp 8192 a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
      (forall a, sp - 8192 <= a < sp -> M' (Z_to_bv 64 a) <> None) ->
      (forall a : word, M a <> None -> M' a <> None) ->
      model_rt model model' -> MInv A model' ->
      RI LB FF LK cr A M' (vml_of model') ->
      srealizes ASEGS scfg (mkCfg (mkst R' (getr R 1) M' (seg_rom ASEGS)) model') Kt) ->
  srealizes ASEGS scfg (mkCfg (mkst R (0x6c1fc : word) M (seg_rom ASEGS)) model) Kt.
Proof.
  intros R M model LB FF LK cr A p q n b1 b2 Kt sp INV Hhalt HMI H10 H11 H12 Hn Hret AST Hp0 Hp47 Hq0 Hq47 RD1 RD2 CLS1 CLS2 AACC1 AACC2 APPR1 APPR2 KT0 CONT.
  destruct (art_ri_open MAPS0 RESV0 NOACC0 BASE BUDGET rn LB FF LK cr A M model INV Hhalt HMI) as (G & REPr & FS & B0 & CRED & CLI & KN & LZ & EG).
  set (Mr0 := mrestrict (bhid A model) M) in *.
  destruct AST as (S16 & SHI & SLE & STOP & SWR & SDEF). fold sp in S16, SHI, SLE, SWR, SDEF. rewrite HLsegs in SWR.
  assert (HIeq : ahl_ceil (rn_ar rn) = rn_HI rn) by reflexivity. rewrite HIeq in SHI.
  change (2 ^ 27) with 134217728 in Hn.
  pose proof (art_cli_hi rn LB FF LK A M CLI) as (HI1 & HI2).
  pose proof REPr as (ROK & STAT & _).
  assert (LAZY : forall w : word, page_in_ranges (page_base w) (m_vm_lazy model) = true ->
            0x6c4000 <= U w /\ U w < rn_HI rn /\ ~ in_block LB (U w) /\ ~ (ar_fs (rn_ar rn) <= U w < ar_fs (rn_ar rn) + FS_BYTES)).
  { intros w Hw. destruct LZ as (L1 & _). destruct (art_lazy_zone_bounds art_fsg rn G (U w) ROK (L1 w Hw)) as (B1 & B2).
    split; [lia|]. split; [exact (proj2 B1)|]. split; [|exact B2]. intros (b & Hb & Hr). rewrite (proj2 EG b w Hb Hr) in Hw. discriminate Hw. }
  (* [comment removed for export] *)
  assert (OFF1 : forall i, 0 <= i < n -> ~ (sp - 8192 <= p + i < sp)).
  { intros i Hi. apply (art_cls_off_scratch rn LB FF LK A M CLI L HLlo HLhi (g_fs art_fsg G) FS sp 8192 (p + i) ltac:(lia) (CLS1 i Hi)). }
  assert (HDJ1 : 0 < n -> p + n <= sp - 2312 \/ sp <= p).
  { intros Hn0. destruct (art_rng_off_window p n (sp - 8192) sp Hn0 ltac:(lia) OFF1) as [X | X]; [left; lia | right; exact X]. }
  set (f1 := Pm5RegionPoisoned.SB + p / 8). set (l1 := Pm5RegionPoisoned.SB + (p + n - 1) / 8).
  assert (D471 : p + n + 16 <= 2 ^ 47).
  { destruct APPR1 as (_ & _ & TOP). destruct (art_cli_facts _ _ _ _ _ _ CLI) as (_ & _ & _ & T16). clear - TOP T16. lia. }
  assert (HSH1 : l1 + 8 <= sp - 2312).
  { unfold l1, Pm5RegionPoisoned.SB. assert ((p + n - 1) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; clear - D471; lia). change (2 ^ 47 / 8) with 17592186044416 in *. clear - H SHI HI1. lia. }
  assert (RNG1 : art_vis (bhid A model) p n
                /\ (0 < n -> forall x : word, f1 <= U x < l1 -> Mr0 x = Some (Z_to_bv 8 0))
                /\ (exists kL, (0 < n -> Mr0 (Z_to_bv 64 l1) = Some (Z_to_bv 8 kL)) /\ (kL = 0 \/ (p + n - 1) mod 8 < kL <= 7))
                /\ (0 < n <= 64 -> exists w0 w1, rdn ASEGS Mr0 (Z_to_bv 64 (f1 - f1 mod 8)) 8 = Some w0 /\ rdn ASEGS Mr0 (Z_to_bv 64 (l1 - l1 mod 8)) 8 = Some w1)).
  { destruct (Z_lt_le_dec 0 n) as [Np | Nz].
    - destruct (art_rng_facts rn LB FF LK A M model LAZY CLI L HLlo HLhi (g_fs art_fsg G) FS (bi_shdef _ _ _ _ _ _ _ _ _ _ _ B0) sp 8192 p n Hp0 Np ltac:(clear - Hn; lia) CLS1 AACC1 APPR1)
        as (VIS & _ & HZ & (kL & HL & HkL) & HW).
      split; [exact VIS|]. split; [intros _; exact HZ|]. split; [exists kL; split; [intros _; exact HL | exact HkL]|]. intros _. exact HW.
    - split; [intros x Hx; exfalso; clear - Hx Nz; lia|]. split; [intros X; exfalso; clear - X Nz; lia|].
      split; [exists 0; split; [intros X; exfalso; clear - X Nz; lia | left; reflexivity]|]. intros X; exfalso; clear - X Nz; lia. }
  destruct RNG1 as (VIS1 & HZ1 & (k1 & HL1 & Hk1) & HW1).
  (* [comment removed for export] *)
  assert (OFF2 : forall i, 0 <= i < n -> ~ (sp - 8192 <= q + i < sp)).
  { intros i Hi. apply (art_cls_off_scratch rn LB FF LK A M CLI L HLlo HLhi (g_fs art_fsg G) FS sp 8192 (q + i) ltac:(lia) (CLS2 i Hi)). }
  assert (HDJ2 : 0 < n -> q + n <= sp - 2312 \/ sp <= q).
  { intros Hn0. destruct (art_rng_off_window q n (sp - 8192) sp Hn0 ltac:(lia) OFF2) as [X | X]; [left; lia | right; exact X]. }
  set (f2 := Pm5RegionPoisoned.SB + q / 8). set (l2 := Pm5RegionPoisoned.SB + (q + n - 1) / 8).
  assert (D472 : q + n + 16 <= 2 ^ 47).
  { destruct APPR2 as (_ & _ & TOP). destruct (art_cli_facts _ _ _ _ _ _ CLI) as (_ & _ & _ & T16). clear - TOP T16. lia. }
  assert (HSH2 : l2 + 8 <= sp - 2312).
  { unfold l2, Pm5RegionPoisoned.SB. assert ((q + n - 1) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; clear - D472; lia). change (2 ^ 47 / 8) with 17592186044416 in *. clear - H SHI HI1. lia. }
  assert (RNG2 : art_vis (bhid A model) q n
                /\ (0 < n -> forall x : word, f2 <= U x < l2 -> Mr0 x = Some (Z_to_bv 8 0))
                /\ (exists kL, (0 < n -> Mr0 (Z_to_bv 64 l2) = Some (Z_to_bv 8 kL)) /\ (kL = 0 \/ (q + n - 1) mod 8 < kL <= 7))
                /\ (0 < n <= 64 -> exists w0 w1, rdn ASEGS Mr0 (Z_to_bv 64 (f2 - f2 mod 8)) 8 = Some w0 /\ rdn ASEGS Mr0 (Z_to_bv 64 (l2 - l2 mod 8)) 8 = Some w1)).
  { destruct (Z_lt_le_dec 0 n) as [Np | Nz].
    - destruct (art_rng_facts rn LB FF LK A M model LAZY CLI L HLlo HLhi (g_fs art_fsg G) FS (bi_shdef _ _ _ _ _ _ _ _ _ _ _ B0) sp 8192 q n Hq0 Np ltac:(clear - Hn; lia) CLS2 AACC2 APPR2)
        as (VIS & _ & HZ & (kL & HL & HkL) & HW).
      split; [exact VIS|]. split; [intros _; exact HZ|]. split; [exists kL; split; [intros _; exact HL | exact HkL]|]. intros _. exact HW.
    - split; [intros x Hx; exfalso; clear - Hx Nz; lia|]. split; [intros X; exfalso; clear - X Nz; lia|].
      split; [exists 0; split; [intros X; exfalso; clear - X Nz; lia | left; reflexivity]|]. intros X; exfalso; clear - X Nz; lia. }
  destruct RNG2 as (VIS2 & HZ2 & (k2 & HL2 & Hk2) & HW2).
  set (FP := fun x => sp - 2312 <= x < sp).
  apply (art_wrap_pure2 MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Hwx (art_alloc_rep_frame_law_proved art_fsg MAPS0 RESV0) Kt R (0x6c1fc : word) M model G LB FF LK cr A FP
           (fun R' pc1 Mr' => pc1 = getr R 1 /\ getr R' 10 = Z_to_bv 64 (memcmp_val b1 b2) /\ keeps_cs R R') REPr FS B0 CRED CLI KN LZ EG).
  - (* [comment removed for export] *)
    assert (RD1r : rdn ASEGS Mr0 (Z_to_bv 64 p) (Z.to_nat n) = Some b1).
    { apply (art_rng_rdn A M model p (Z.to_nat n) b1 Hp0 ltac:(rewrite Z2Nat.id by (clear - Hn; lia); clear - Hp47; lia)); [|exact RD1]. rewrite Z2Nat.id by (clear - Hn; lia). exact VIS1. }
    assert (RD2r : rdn ASEGS Mr0 (Z_to_bv 64 q) (Z.to_nat n) = Some b2).
    { apply (art_rng_rdn A M model q (Z.to_nat n) b2 Hq0 ltac:(rewrite Z2Nat.id by (clear - Hn; lia); clear - Hq47; lia)); [|exact RD2]. rewrite Z2Nat.id by (clear - Hn; lia). exact VIS2. }
    assert (W0 : wrA Mr0 (sp - 8192) 8192).
    { apply (art_stack_wr art_fsg rn G A (m_vm_lazy model) M sp 8192 ROK LZ ltac:(lia) ltac:(lia) ltac:(lia)). exact SWR. }
    assert (HOK : store_ok ASEGS Mr0 (Z_to_bv 64 (sp - 2312)) 2312 = true).
    { replace (sp - 2312) with (sp - 8192 + (8192 - 2312)) by ring. apply W0; [lia | cbn; lia]. }
    destruct STAT as (_ & LAY & _ & _ & _ & _ & _ & S8).
    assert (HGL : rt_layout_globs Mr0).
    { destruct LAY as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & _). unfold rt_layout_globs. repeat split; [lit_cell A1 | lit_cell A2 | lit_cell A3 | lit_cell A4 | lit_cell A5 | lit_cell A6 | lit_cell A7 | lit_cell A8]. }
    assert (HIC : mcmp_icpt_globs Mr0).
    { destruct LAY as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & A13 & _).
      assert (C1r : cellA Mr0 0x1ff3e6 1 1) by conj_find S8.
      assert (C2r : cellA Mr0 0x1ff3e7 1 1) by conj_find S8.
      unfold mcmp_icpt_globs. repeat split.
      - lit_cell A13.
      - rewrite <- le1_one. lit_cell C1r.
      - rewrite <- le1_one. lit_cell C2r. }
    assert (INITED : cellA Mr0 0x16e498 1 1) by conj_find S8.
    assert (HCI : icptI_globs Mr0).
    { assert (C3r : cellA Mr0 0x166378 8 0x156488) by conj_find S8.
      unfold icptI_globs. split; [rewrite <- le1_one; lit_cell INITED | lit_cell C3r]. }
    assert (HSs : 0x1000000 <= sp - 2312 /\ sp < 2 ^ 64) by (clear - SHI SLE STOP HI1; lia).
    destruct (wrap_memcmp_pk Mr0 (seg_rom ASEGS) (getr R 2) (getr R 1) p q n sp b1 b2 k1 f1 l1 (f1 - f1 mod 8) (l1 - l1 mod 8) k2 f2 l2 (f2 - f2 mod 8) (l2 - l2 mod 8)
                eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(clear - Hn; lia)
                (art_rng_app8 rn LB FF LK A M CLI p n Hp0 ltac:(clear - Hn; lia) APPR1) (art_rng_app8 rn LB FF LK A M CLI q n Hq0 ltac:(clear - Hn; lia) APPR2)
                HSs HSH1 HSH2 HDJ1 HDJ2 HOK RD1r RD2r Hret HGL HIC HCI HZ1 HL1 Hk1 HW1 HZ2 HL2 Hk2 HW2 R H10 H11 H12 eq_refl eq_refl)
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
      apply (art_cls_off_scratch rn LB FF LK A M CLI L HLlo HLhi (g_fs art_fsg G) FS sp 8192 a ltac:(clear - SHI; lia) (or_intror Ha)). clear - X. lia.
    + intros a Ha. apply GROW.
      assert (WM : wrA M (sp - 8192) 8192) by (intros d k Hd Hk; apply SWR; assumption).
      pose proof (art_wr_wview ASEGS M (sp - 8192) 8192 ltac:(clear - SHI HI1; lia) ltac:(clear - SLE STOP; lia) WM (Z_to_bv 64 a)) as V. rewrite art_u_lit in V by (clear - Ha SHI HI1 SLE STOP; lia). specialize (V ltac:(clear - Ha; lia)).
      rewrite art_wview_off in V by (rewrite art_u_lit by (clear - Ha SHI HI1 SLE STOP; lia); right; clear - Ha SHI HI1; lia). exact V.
Qed.
End WMC.

Lemma lit_64c30 : Z_to_bv 64 0x6c200 = (0x6c200%bv : word). Proof. apply bv_eq. reflexivity. Qed.
Lemma lit_64c2c : Z_to_bv 64 0x6c1fc = (0x6c1fc%bv : word). Proof. apply bv_eq. reflexivity. Qed.

(* [comment removed for export] *)
Theorem art_abcmp_at : forall MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg, wx_segs_nowrap ASEGS -> forall (L : asan_layout),
  hl_segs L = ASEGS -> hl_img_lo L = 0x10000 -> hl_img_hi L = 0x6c4000 ->
  amemcmp_spec_at L (rn_ar rn) scfg (art_iface art_fsg MAPS0 RESV0 NOACC0 BASE BUDGET art_fsinv rn) 0x6c200 8192.
Proof.
  intros MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Hwx L HLsegs HLlo HLhi fx R M model LB FF LK cr A p q n b1 b2 Kt. cbv zeta.
  intros INV Hh HMI H10 H11 H12 Hn H4 Hret AST Hp0 Hp47 Hq0 Hq47 RD1 RD2 CLS1 CLS2 AACC1 AACC2 APPR1 APPR2 KT0 POST.
  rewrite HLsegs in *. rewrite lit_64c30.
  apply (art_wrap_bcmp MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Hwx L HLsegs HLlo HLhi R M model LB FF LK cr A p q n b1 b2 Kt INV Hh HMI H10 H11 H12 Hn Hret AST Hp0 Hp47 Hq0 Hq47 RD1 RD2 CLS1 CLS2 AACC1 AACC2 APPR1 APPR2 KT0).
  intros R' M' model' Q10 RP FR SD GR RT MI' RI'. apply (POST R' M' model' Q10 RP FR SD GR RT MI' RI').
Qed.
Theorem art_amemcmp_at : forall MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg, wx_segs_nowrap ASEGS -> forall (L : asan_layout),
  hl_segs L = ASEGS -> hl_img_lo L = 0x10000 -> hl_img_hi L = 0x6c4000 ->
  amemcmp_spec_at L (rn_ar rn) scfg (art_iface art_fsg MAPS0 RESV0 NOACC0 BASE BUDGET art_fsinv rn) 0x6c1fc 8192.
Proof.
  intros MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Hwx L HLsegs HLlo HLhi fx R M model LB FF LK cr A p q n b1 b2 Kt. cbv zeta.
  intros INV Hh HMI H10 H11 H12 Hn H4 Hret AST Hp0 Hp47 Hq0 Hq47 RD1 RD2 CLS1 CLS2 AACC1 AACC2 APPR1 APPR2 KT0 POST.
  rewrite HLsegs in *. rewrite lit_64c2c.
  apply (art_wrap_memcmp MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Hwx L HLsegs HLlo HLhi R M model LB FF LK cr A p q n b1 b2 Kt INV Hh HMI H10 H11 H12 Hn Hret AST Hp0 Hp47 Hq0 Hq47 RD1 RD2 CLS1 CLS2 AACC1 AACC2 APPR1 APPR2 KT0).
  intros R' M' model' Q10 RP FR SD GR RT MI' RI'. apply (POST R' M' model' Q10 RP FR SD GR RT MI' RI').
Qed.
