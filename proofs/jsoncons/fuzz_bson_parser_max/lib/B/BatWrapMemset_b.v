(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct RefMemcpyLib MemSplit MemsetLib HeapIface HeapIfaceA HeapIfaceABx ArtMem ArtRuns ArtRunsMem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatCls_b BatCellEx_b BatPoison_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtBridge. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatInv_b BatInvMalloc_b BatLift_b BatWrapKit_b BatFsInv_b BatFsInvLaws_b BatIfaceLaws_b Ba0RegionPoisoned_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatWrapC_b BatWrapVis_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0AsanMemset_b BatWrapC2_b BatWrapRng_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).


Section WMS.
Variables MAPS0 RESV0 NOACC0 : list (word * word).
Variables BASE BUDGET : Z.
Variable rn : art_run.
Variable scfg : SpuriousCfg.
Hypothesis Hwx : wx_segs_nowrap ASEGS.
Hypothesis AFL : art_alloc_rep_frame_law art_fsg MAPS0 RESV0.
Variable L : asan_layout.
Hypothesis HLsegs : hl_segs L = ASEGS.
Hypothesis HLlo : hl_img_lo L = 0x10000.
Hypothesis HLhi : hl_img_hi L = 0x696000.
Hypothesis HLroimg : forall a, hl_rt_ro L a -> 0x10000 <= a < 0x696000.
Hypothesis HLstimg : forall a, hl_rt_static L a -> 0x10000 <= a < 0x696000.
Hypothesis HLlsan : forall a, rn_tp rn + rn_loff rn <= a < rn_tp rn + rn_loff rn + 4 -> hl_rt_static L a.
#[local] Abbreviation RI := (art_ri_inv art_fsg MAPS0 RESV0 NOACC0 BASE BUDGET art_fsinv rn).
Hypothesis PRIVZ : forall (G : art_gs art_fsg) LB FF LK A (M Mr : word -> option byte) lazy,
  art_alloc_rep art_fsg rn G LB Mr -> art_fsinv rn (g_fs art_fsg G) FF LK M -> art_client_ok rn LB FF LK A M ->
  live_ok MAPS0 RESV0 (rn_HI rn) (art_live (g_log art_fsg G)) -> art_kn_ok MAPS0 RESV0 rn -> art_lazy_ok art_fsg rn G A lazy -> art_eager_ok LB A lazy ->
  forall a, art_alloc_zone art_fsg rn G a -> ~ in_block LB a -> art_private L (rn_ar rn) LB FF a.
Hypothesis PRIVF : forall (G : art_gs art_fsg) LB FF LK A (M Mr : word -> option byte) lazy,
  art_alloc_rep art_fsg rn G LB Mr -> art_fsinv rn (g_fs art_fsg G) FF LK M -> art_client_ok rn LB FF LK A M ->
  live_ok MAPS0 RESV0 (rn_HI rn) (art_live (g_log art_fsg G)) -> art_kn_ok MAPS0 RESV0 rn -> art_lazy_ok art_fsg rn G A lazy -> art_eager_ok LB A lazy ->
  forall a, fs_zone3 rn a -> ~ in_fframe FF a -> art_private L (rn_ar rn) LB FF a.
Hypothesis PRIVCS : forall (G : art_gs art_fsg) LB FF LK A (M Mr : word -> option byte) lazy,
  art_alloc_rep art_fsg rn G LB Mr -> art_fsinv rn (g_fs art_fsg G) FF LK M -> art_client_ok rn LB FF LK A M ->
  live_ok MAPS0 RESV0 (rn_HI rn) (art_live (g_log art_fsg G)) -> art_kn_ok MAPS0 RESV0 rn -> art_lazy_ok art_fsg rn G A lazy -> art_eager_ok LB A lazy ->
  forall a, cs_zone rn a -> art_private L (rn_ar rn) LB FF a.                      (* [comment removed for export] *)
Context {fx : PropExec.FPState}.

#[using="Hwx AFL HLsegs HLlo HLhi HLroimg HLstimg HLlsan PRIVZ PRIVF PRIVCS"] Theorem art_wrap_memset : forall (R : bvmap 5 word) (M : word -> option byte) (model : Model)
    (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (dst c n : Z) (K : ShapeAlg.TSet),
  let sp := U (getr R 2) in
  RI LB FF LK cr A M (vml_of model) -> m_halted model = None -> MInv A model ->
  getr R 10 = Z_to_bv 64 dst -> getr R 12 = Z_to_bv 64 n -> 0 <= n <= 2 ^ 27 ->
  Hoare.ret_ok (getr R 1) ->
  astack_ok L (rn_ar rn) M 2560 sp ->
  aacc M dst n -> (forall i, 0 <= i < n -> aclientw L (rn_ar rn) LB FF sp 2560 (dst + i)) ->
  (forall i (m : nat), 0 <= i -> i + Z.of_nat m <= n -> store_ok ASEGS M (Z_to_bv 64 (dst + i)) m = true) ->
  K [] -> app_rng (rn_ar rn) dst n ->
  getr R 11 = Z_to_bv 64 c ->
  (forall (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model),
      getr R' 10 = Z_to_bv 64 dst -> regs_preserved R R' ->
      (forall i, 0 <= i < n -> exists v, v = c mod 256 /\ byte_at M' (dst + i) v) ->
      (forall a, 0 <= a < 2 ^ 64 -> aclient L (rn_ar rn) LB FF sp 2560 a -> ~ (dst <= a < dst + n) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
      (forall a, sp - 2560 <= a < sp -> M' (Z_to_bv 64 a) <> None) ->
      model_rt model model' -> MInv A model' ->
      RI LB FF LK cr A M' (vml_of model') ->
      srealizes ASEGS scfg (mkCfg (mkst R' (getr R 1) M' (seg_rom ASEGS)) model') K) ->
  srealizes ASEGS scfg (mkCfg (mkst R (0x78130 : word) M (seg_rom ASEGS)) model) K.
Proof.
  intros R M model LB FF LK cr A dst c n K sp INV Hhalt HMI H10 H12 Hn Hret AST AACC CLW DOK KT0 APPR H11 CONT.
  pose proof (proj1 APPR) as Hd0.
  destruct (art_ri_open MAPS0 RESV0 NOACC0 BASE BUDGET rn LB FF LK cr A M model INV Hhalt HMI) as (G & REPr & FS & B0 & CRED & CLI & KN & LZ & EG).
  set (Mr0 := mrestrict (bhid A model) M) in *.
  destruct AST as (S16 & SHI & SLE & STOP & SWR & SDEF). fold sp in S16, SHI, SLE, SWR, SDEF. rewrite HLsegs in SWR.
  assert (HIeq : ahl_ceil (rn_ar rn) = rn_HI rn) by reflexivity. rewrite HIeq in SHI.
  change (2 ^ 27) with 134217728 in Hn.
  pose proof (art_cli_hi rn LB FF LK A M CLI) as (HI1 & HI2).
  pose proof REPr as (ROK & STAT & _).
  assert (LAZY : forall w : word, page_in_ranges (page_base w) (m_vm_lazy model) = true ->
            0x696000 <= U w /\ U w < rn_HI rn /\ ~ in_block LB (U w) /\ ~ (ar_fs (rn_ar rn) <= U w < ar_fs (rn_ar rn) + FS_BYTES)).
  { intros w Hw. destruct LZ as (L1 & _). destruct (art_lazy_zone_bounds art_fsg rn G (U w) ROK (L1 w Hw)) as (B1 & B2).
    split; [lia|]. split; [exact (proj2 B1)|]. split; [|exact B2]. intros (b & Hb & Hr). rewrite (proj2 EG b w Hb Hr) in Hw. discriminate Hw. }
  assert (CLS : forall i, 0 <= i < n -> hl_img_lo L <= dst + i < hl_img_hi L \/ aclient L (rn_ar rn) LB FF sp 2560 (dst + i)).
  { intros i Hi. right. apply aclientw_client. exact (CLW i Hi). }
  assert (OFF : forall i, 0 <= i < n -> ~ (sp - 2560 <= dst + i < sp)).
  { intros i Hi. apply (art_cls_off_scratch rn LB FF LK A M CLI L HLlo HLhi (g_fs art_fsg G) FS sp 2560 (dst + i) ltac:(lia) (CLS i Hi)). }
  assert (HDJ : 0 < n -> dst + n <= sp - 2200 \/ sp <= dst).
  { intros Hn0. destruct (art_rng_off_window dst n (sp - 2560) sp Hn0 ltac:(lia) OFF) as [X | X]; [left; lia | right; exact X]. }
  assert (APPD : (dst + n <= BIGSHADOW_LO \/ BIGSHADOW_HI <= dst)) by exact (proj1 (proj2 APPR)).
  set (FP := fun x => sp - 2200 <= x < sp \/ dst <= x < dst + n).
  apply (art_wrap_pure2 MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Hwx AFL K R (0x78130 : word) M model G LB FF LK cr A FP
           (fun R' pc1 Mr' => pc1 = getr R 1 /\ getr R' 10 = Z_to_bv 64 dst /\ keeps_cs R R'
                              /\ (forall i, 0 <= i < n -> Mr' (Z_to_bv 64 (dst + i)) = Some (Z_to_bv 8 (c mod 256))))
           REPr FS B0 CRED CLI KN LZ EG).
  - (* [comment removed for export] *)
    assert (W0 : wrA Mr0 (sp - 2560) 2560).
    { apply (art_stack_wr art_fsg rn G A (m_vm_lazy model) M sp 2560 ROK LZ ltac:(lia) ltac:(lia) ltac:(lia)). exact SWR. }
    assert (HOK : store_ok ASEGS Mr0 (Z_to_bv 64 (sp - 2200)) 2200 = true).
    { replace (sp - 2200) with (sp - 2560 + 360) by ring. apply W0; [lia | cbn; lia]. }
    assert (VIMG : forall a (k : nat), 0x10000 <= a -> a + Z.of_nat k <= 0x696000 -> art_vis (bhid A model) a (Z.of_nat k)).
    { intros a k H1 H2 x Hx. apply (art_vis_byte rn LB A model LAZY). left. lia. }
    destruct STAT as (_ & LAY & _ & _ & _ & _ & _ & S8). 
    assert (HGL : rt_layout_globs Mr0).
    { destruct LAY as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & _). unfold rt_layout_globs. repeat split; [lit_cell A1 | lit_cell A2 | lit_cell A3 | lit_cell A4 | lit_cell A5 | lit_cell A6 | lit_cell A7 | lit_cell A8]. }
    assert (C1 : cellA Mr0 0x138028 8 0x140919) by conj_find S8.
    assert (C2 : cellA Mr0 0x140919 1 1) by conj_find S8.
    assert (HIC : ms_icpt_globs Mr0).
    { destruct LAY as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & A12 & _). unfold ms_icpt_globs. repeat split.
      - lit_cell C1.
      - rewrite <- le1_one. lit_cell C2.
      - lit_cell A12. }
    set (f := Ba0RegionPoisoned_b.SB + dst / 8). set (l := Ba0RegionPoisoned_b.SB + (dst + n - 1) / 8).
    assert (D47 : dst + n + 16 <= 2 ^ 47).
    { destruct APPR as (_ & _ & TOP). destruct (art_cli_facts _ _ _ _ _ _ CLI) as (_ & _ & _ & T16). clear - TOP T16. lia. }
    assert (HSH : l + 8 <= sp - 2200).
    { unfold l, Ba0RegionPoisoned_b.SB. assert ((dst + n - 1) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; clear - D47; lia). change (2 ^ 47 / 8) with 17592186044416 in *. clear - H SHI HI1. lia. }
    assert (RNG : art_vis (bhid A model) dst n
                  /\ (0 < n -> forall x : word, f <= U x < l -> Mr0 x = Some (Z_to_bv 8 0))
                  /\ (exists kL, (0 < n -> Mr0 (Z_to_bv 64 l) = Some (Z_to_bv 8 kL)) /\ (kL = 0 \/ (dst + n - 1) mod 8 < kL <= 7))
                  /\ (0 < n <= 64 -> exists w0 w1, rdn ASEGS Mr0 (Z_to_bv 64 (f - f mod 8)) 8 = Some w0 /\ rdn ASEGS Mr0 (Z_to_bv 64 (l - l mod 8)) 8 = Some w1)).
    { destruct (Z_lt_le_dec 0 n) as [Np | Nz].
      - destruct (art_rng_facts rn LB FF LK A M model LAZY CLI L HLlo HLhi (g_fs art_fsg G) FS (bi_shdef _ _ _ _ _ _ _ _ _ _ _ B0) sp 2560 dst n Hd0 Np ltac:(clear - Hn; lia) CLS AACC APPR)
          as (VIS & _ & HZ & (kL & HL & HkL) & HW).
        split; [exact VIS|]. split; [intros _; exact HZ|]. split; [exists kL; split; [intros _; exact HL | exact HkL]|]. intros _. exact HW.
      - split; [intros x Hx; exfalso; clear - Hx Nz; lia|]. split; [intros X; exfalso; clear - X Nz; lia|].
        split; [exists 0; split; [intros X; exfalso; clear - X Nz; lia | left; reflexivity]|]. intros X; exfalso; clear - X Nz; lia. }
    destruct RNG as (VIS & HZ & (kL & HL & HkL) & HW).
    assert (HAPP : (0 <= dst /\ dst + n + 8 <= LOWEND) \/ (HIGHBEG <= dst /\ dst + n + 8 <= HIGHEND)).
    { exact (art_rng_app8 rn LB FF LK A M CLI dst n Hd0 ltac:(clear - Hn; lia) APPR). }
    assert (HDST : store_ok ASEGS Mr0 (Z_to_bv 64 dst) (Z.to_nat n) = true).
    { apply (art_rng_store_ok A M model dst (Z.to_nat n) Hd0 ltac:(rewrite Z2Nat.id by (clear - Hn; lia); clear - D47; lia)).
      - rewrite Z2Nat.id by (clear - Hn; lia). exact VIS.
      - pose proof (DOK 0 (Z.to_nat n) ltac:(lia) ltac:(rewrite Z2Nat.id by (clear - Hn; lia); lia)) as X. rewrite Z.add_0_r in X. exact X. }
    assert (HSs : 0x1000000 <= sp - 2200 /\ sp < 2 ^ 64) by (clear - SHI SLE STOP HI1; lia).
    destruct (@asan_memset_run fx Mr0 (seg_rom ASEGS) (getr R 2) (getr R 1) (getr R 11) dst n sp kL f l (f - f mod 8) (l - l mod 8)
                eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(clear - Hn; lia) HAPP HSs HSH HDJ HOK HDST Hret HGL HIC HZ HL HkL HW R H10 eq_refl H12 eq_refl eq_refl)
      as (R' & Mj & RUN & Q10 & Q2 & Q1 & KCS & OA & GRr).
    set (Mf := wbytes Mj (Z_to_bv 64 dst) (repeat (cbyte (getr R 11)) (Z.to_nat n))) in *.
    assert (LENR : Z.of_nat (length (repeat (cbyte (getr R 11)) (Z.to_nat n))) = n) by (rewrite repeat_length, Z2Nat.id by (clear - Hn; lia); reflexivity).
    assert (FRr : forall x : word, ~ FP (U x) -> Mf x = Mr0 x).
    { intros x Hx. unfold FP in Hx. pose proof (u64_range x) as Rx.
      assert (E1 : Mf x = Mj x).
      { unfold Mf. destruct (Z_lt_le_dec (U x) dst) as [Lt | Ge].
        - apply wbytes_below; [rewrite LENR, art_u_lit by (clear - Hd0 D47 Hn; lia); clear - D47 Hd0 Hn; lia | rewrite art_u_lit by (clear - Hd0 D47 Hn; lia); exact Lt].
        - apply wbytes_above. rewrite LENR, art_u_lit by (clear - Hd0 D47 Hn; lia). clear - Hx Ge. lia. }
      rewrite E1. apply OA. clear - Hx. lia. }
    exists R', (getr R 1), Mf. split; [exact RUN|].
    split. { eapply mem_grows_trans; [exact GRr | apply wbytes_grows]. }
    split; [exact FRr|].
    split.
    { (* [comment removed for export] *)
      pose proof REPr as (_ & _ & (_ & _ & _ & _ & _ & _ & _ & CL) & _).
      assert (GEOL : 0x10000 <= rn_tp rn + rn_loff rn /\ rn_tp rn + rn_loff rn + 4 <= 0x696000).
      { pose proof ROK as ROK'. rok_open ROK'. geo_open GEO. clear - Hloff Hloff' Hloff'' Htpd G1 G2 Espb G4. lia. }
      apply (BatAllocG_b.cell_agree Mr0 Mf); [| clear - GEOL; lia | cbn; clear - GEOL; lia | exact CL].
      intros x Hx. cbn in Hx. apply FRr. unfold FP. intros [X | X]; [clear - X Hx GEOL SHI HI1; lia|].
      apply (art_clientw_not_static rn LB FF LK A M CLI L (g_fs art_fsg G) FS HLstimg sp 2560 (U x)).
      - replace (U x) with (dst + (U x - dst)) by ring. apply CLW. clear - X. lia.
      - unfold BIGSHADOW_LO. left. clear - Hx GEOL. lia.
      - apply HLlsan. clear - Hx. lia. }
    split; [reflexivity|]. split; [exact Q10|]. split; [exact KCS|].
    intros i Hi. unfold Mf. rewrite (wbytes_inside _ Mj (Z_to_bv 64 dst) (Z_to_bv 64 (dst + i))).
    + rewrite H11, cbyte_Z. rewrite !art_u_lit by (clear - Hd0 D47 Hi; lia). rewrite nth_repeat_lt by (clear - Hi; lia).
      f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. rewrite Z.mod_mod by lia. reflexivity.
    + rewrite LENR, art_u_lit by (clear - Hd0 D47 Hn; lia). clear - D47 Hd0 Hn. lia.
    + rewrite LENR, !art_u_lit by (clear - Hd0 D47 Hi; lia). clear - Hi. lia.
  - (* [comment removed for export] *)
    intros x [Hx | Hx] Z.
    + exfalso. pose proof (art_zone_below MAPS0 RESV0 NOACC0 BASE BUDGET rn G LB A M Mr0 model x REPr KN B0 (or_introl Z)). clear - H Hx SHI. lia.
    + destruct (in_block_dec LB x) as [IB | NB]; [exact IB | exfalso].
      apply (art_clientw_not_private rn LB FF LK A M CLI L (g_fs art_fsg G) FS HLroimg sp 2560 x).
      * replace x with (dst + (x - dst)) by ring. apply CLW. clear - Hx. lia.
      * unfold BIGSHADOW_LO, BIGSHADOW_HI in *. clear - APPD Hx. lia.
      * exact (PRIVZ G LB FF LK A M Mr0 (m_vm_lazy model) REPr FS CLI (bi_live _ _ _ _ _ _ _ _ _ _ _ B0) KN LZ EG x Z NB).
  - (* [comment removed for export] *)
    intros x [Hx | Hx] Z3.
    + exfalso. pose proof (art_fs_zone3_below rn G LB _ x REPr Z3). clear - H Hx SHI. lia.
    + destruct (in_fframe_dec FF x) as [IB | NB]; [exact IB | exfalso].
      apply (art_clientw_not_private rn LB FF LK A M CLI L (g_fs art_fsg G) FS HLroimg sp 2560 x).
      * replace x with (dst + (x - dst)) by ring. apply CLW. clear - Hx. lia.
      * unfold BIGSHADOW_LO, BIGSHADOW_HI in *. clear - APPD Hx. lia.
      * exact (PRIVF G LB FF LK A M Mr0 (m_vm_lazy model) REPr FS CLI (bi_live _ _ _ _ _ _ _ _ _ _ _ B0) KN LZ EG x Z3 NB).
  - (* [comment removed for export] *)
    intros x [Hx | Hx] Zc.
    + pose proof (art_cs_zone_below rn G LB FF LK M Mr0 x REPr FS Zc). clear - H Hx SHI. lia.
    + apply (art_clientw_not_private rn LB FF LK A M CLI L (g_fs art_fsg G) FS HLroimg sp 2560 x).
      * replace x with (dst + (x - dst)) by ring. apply CLW. clear - Hx. lia.
      * unfold BIGSHADOW_LO, BIGSHADOW_HI in *. clear - APPD Hx. lia.
      * exact (PRIVCS G LB FF LK A M Mr0 (m_vm_lazy model) REPr FS CLI (bi_live _ _ _ _ _ _ _ _ _ _ _ B0) KN LZ EG x Zc).
  - (* [comment removed for export] *)
    intros b x Hb Hx [X | X].
    + pose proof (art_block_shadow_below rn LB FF LK A M b x CLI Hb Hx). clear - H X SHI HI1. lia.
    + pose proof (art_block_shadow_below rn LB FF LK A M b x CLI Hb Hx) as B1. pose proof CLI as (CB & _). destruct (CB b Hb) as (K1 & _).
      unfold in_shadow_of in Hx. pose proof (art_S_lo (fst b) ltac:(clear - K1; lia)) as B2. unfold BIGSHADOW_LO, BIGSHADOW_HI in APPD. clear - APPD X B1 B2 Hx. lia.
  - (* [comment removed for export] *)
    intros R' pc1 Mr' M1 model' (Epc & Q10 & KCS & BYTES) RI' GROW FR1 VIS1 HID RT MI'. subst pc1.
    assert (VISD : forall i, 0 <= i < n -> bhid A model (Z_to_bv 64 (dst + i)) = false).
    { intros i Hi. apply (art_aclient_vis rn LB FF LK A M model LAZY CLI L HLlo HLhi (g_fs art_fsg G) FS sp 2560 (dst + i)); [|exact (CLS i Hi)].
      destruct APPR as (_ & _ & TOP). destruct (art_cli_facts _ _ _ _ _ _ CLI) as (_ & _ & _ & T16). clear - TOP T16 Hd0 Hi. lia. }
    apply (CONT R' M1 model' Q10 (keeps_cs_preserved R R' KCS)); [ | | | exact RT | exact MI' | exact RI'].
    + intros i Hi. exists (c mod 256). split; [reflexivity|]. unfold byte_at. rewrite (VIS1 _ (VISD i Hi)). exact (BYTES i Hi).
    + intros a Ra Ha ND. apply FR1. rewrite art_u_lit by exact Ra. unfold FP. intros [X | X]; [|exact (ND X)].
      apply (art_cls_off_scratch rn LB FF LK A M CLI L HLlo HLhi (g_fs art_fsg G) FS sp 2560 a ltac:(clear - SHI; lia) (or_intror Ha)). clear - X. lia.
    + intros a Ha. apply GROW.
      assert (WM : wrA M (sp - 2560) 2560) by (intros d k Hd Hk; apply SWR; assumption).
      pose proof (art_wr_wview ASEGS M (sp - 2560) 2560 ltac:(clear - SHI HI1; lia) ltac:(clear - SLE STOP; lia) WM (Z_to_bv 64 a)) as V. rewrite art_u_lit in V by (clear - Ha SHI HI1 SLE STOP; lia). specialize (V ltac:(clear - Ha; lia)).
      rewrite art_wview_off in V by (rewrite art_u_lit by (clear - Ha SHI HI1 SLE STOP; lia); right; clear - Ha SHI HI1; lia). exact V.
Qed.
End WMS.
