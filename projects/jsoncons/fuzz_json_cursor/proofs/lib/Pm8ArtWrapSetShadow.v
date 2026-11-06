(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct RefMemcpyLib MemSplit MemsetLib HeapIface HeapIfaceA PmHeapIfaceA IcptIfaceA PmIcptIfaceA ArtMem ArtRuns ArtRunsMem Pm8ArtCls Pm8ArtCellEx Pm8ArtPoison
     ArtBridge Pm8ArtInv Pm8ArtInvMalloc Pm8ArtLift Pm8ArtWrapKit Pm8ArtFsInv Pm8ArtFsInvLaws Pm8ArtIfaceLaws Pm8ArtInvFrame Pm8ArtIfaceFrame Pm8RegionPoisoned.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import Pm8ArtWrapC Pm8ArtWrapVis.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import Pm8SetShadow Pm8ArtWrapC2 Pm8ArtWrapRng.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Section WSS.
Variables MAPS0 RESV0 NOACC0 : list (word * word).
Variables BASE BUDGET : Z.
Variable rn : art_run.
Variable scfg : SpuriousCfg.
Hypothesis Hwx : wx_segs_nowrap ASEGS.
Hypothesis AFL : art_alloc_rep_frame_law art_fsg MAPS0 RESV0.
Variable L : asan_layout.
Hypothesis HLsegs : hl_segs L = ASEGS.
Hypothesis HLlo : hl_img_lo L = 0x10000.
Hypothesis HLhi : hl_img_hi L = 0x6b3000.
Hypothesis HLroimg : forall a, hl_rt_ro L a -> 0x10000 <= a < 0x6b3000.
Hypothesis HLstimg : forall a, hl_rt_static L a -> 0x10000 <= a < 0x6b3000.
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
  forall a, cs_zone rn a -> art_private L (rn_ar rn) LB FF a.
Context {fx : PropExec.FPState}.
Variables (pcw : word) (v : Z).
Hypothesis Hv : 0 <= v < 256.
Hypothesis RUNX : forall (mem0 rom : word -> option byte) (ra : word) (sa n : Z),
  0 <= n -> (0 <= sa /\ sa + n < 2 ^ 64) -> store_ok ASEGS mem0 (Z_to_bv 64 sa) (Z.to_nat n) = true -> Hoare.ret_ok ra -> setsh_globs mem0 ->
  forall regs, getr regs 10 = Z_to_bv 64 sa -> getr regs 11 = Z_to_bv 64 n -> getr regs 1 = ra ->
  exists regs', msteps ASEGS (mkst regs pcw mem0 rom) (mkst regs' ra (wbytes mem0 (Z_to_bv 64 sa) (repeat (Z_to_bv 8 v) (Z.to_nat n))) rom) /\ keeps_cs regs regs'.

Theorem art_wrap_setshadow : forall (R : bvmap 5 word) (M : word -> option byte) (model : Model)
    (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (f : fframe) (sa n : Z) (K : ShapeAlg.TSet),
  let sp := U (getr R 2) in
  RI LB FF LK cr A M (vml_of model) -> m_halted model = None -> MInv A model ->
  getr R 10 = Z_to_bv 64 sa -> getr R 11 = Z_to_bv 64 n ->
  In f FF -> 0 <= n -> HeapIfaceA.S (ff_addr f) <= sa -> sa + n <= HeapIfaceA.S (ff_addr f) + ff_bytes (ff_class f) / 8 ->
  Hoare.ret_ok (getr R 1) -> astack_ok L (rn_ar rn) M 256 sp -> K [] ->
  (forall (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model),
      regs_preserved R R' ->
      (forall j, 0 <= j < n -> byte_at M' (sa + j) v) ->
      (forall a, 0 <= a < 2 ^ 64 -> aclient L (rn_ar rn) LB FF sp 256 a -> ~ (sa <= a < sa + n) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
      (forall a, sp - 256 <= a < sp -> M' (Z_to_bv 64 a) <> None) ->
      (forall a : word, M a <> None -> M' a <> None) ->
      model_rt model model' -> MInv A model' ->
      RI LB FF LK cr A M' (vml_of model') ->
      srealizes ASEGS scfg (mkCfg (mkst R' (getr R 1) M' (seg_rom ASEGS)) model') K) ->
  srealizes ASEGS scfg (mkCfg (mkst R pcw M (seg_rom ASEGS)) model) K.
Proof.
  intros R M model LB FF LK cr A f sa n K sp INV Hhalt HMI H10 H11 Hf Hn LO HIb Hret AST KT0 CONT.
  destruct (art_ri_open MAPS0 RESV0 NOACC0 BASE BUDGET rn LB FF LK cr A M model INV Hhalt HMI) as (G & REPr & FS & B0 & CRED & CLI & KN & LZ & EG).
  set (Mr0 := mrestrict (bhid A model) M) in *.
  destruct AST as (S16 & SHI & SLE & STOP & SWR & SDEF). fold sp in S16, SHI, SLE, SWR, SDEF. rewrite HLsegs in SWR.
  assert (HIeq : ahl_ceil (rn_ar rn) = rn_HI rn) by reflexivity. rewrite HIeq in SHI.
  pose proof (art_cli_hi rn LB FF LK A M CLI) as (HI1 & HI2).
  pose proof REPr as (ROK & STAT & _).
  assert (LAZY : forall w : word, page_in_ranges (page_base w) (m_vm_lazy model) = true ->
            0x6b3000 <= U w /\ U w < rn_HI rn /\ ~ in_block LB (U w) /\ ~ (ar_fs (rn_ar rn) <= U w < ar_fs (rn_ar rn) + FS_BYTES)).
  { intros w Hw. destruct LZ as (L1 & _). destruct (art_lazy_zone_bounds art_fsg rn G (U w) ROK (L1 w Hw)) as (B1 & B2).
    split; [lia|]. split; [exact (proj2 B1)|]. split; [|exact B2]. intros (b & Hb & Hr). rewrite (proj2 EG b w Hb Hr) in Hw. discriminate Hw. }

  pose proof (fsinv_geo rn _ FF LK M FS) as (FG1 & FG2 & FG3 & FG4 & (FG5a & FG5b & FG5c) & _).
  pose proof (fsinv_frame_in rn _ FF LK M FS f ltac:(apply in_or_app; left; exact Hf)) as (I1 & I2 & I3).
  destruct (fsinv_slot rn _ FF LK M FS f ltac:(apply in_or_app; left; exact Hf)) as ((KC1 & _) & _).
  set (fs := ar_fs (rn_ar rn)) in *. set (F := ff_addr f) in *. set (B := ff_bytes (ff_class f)) in *.
  assert (B64 : exists m, B = 64 * m /\ 0 < m).
  { exists (2 ^ ff_class f). unfold B, ff_bytes. split; [reflexivity | apply Z.pow_pos_nonneg; lia]. }
  destruct B64 as (mB & EB & PB).
  assert (B8 : B / 8 = 8 * mB) by (rewrite EB; replace (64 * mB) with (8 * mB * 8) by ring; apply Z.div_mul; lia).
  assert (FS8 : 8 * (fs / 8) = fs) by (clear - FG1; lia).
  assert (FSE8 : 8 * ((fs + FS_BYTES) / 8) = fs + FS_BYTES) by (unfold FS_BYTES; clear - FG1; lia).
  assert (SF : HeapIfaceA.S fs <= HeapIfaceA.S F /\ HeapIfaceA.S F + B / 8 <= HeapIfaceA.S (fs + FS_BYTES)).
  { unfold HeapIfaceA.S. split.
    - assert (fs / 8 <= F / 8) by (apply Z.div_le_mono; lia). lia.
    - assert (F / 8 + 8 * mB <= (fs + FS_BYTES) / 8); [|lia]. apply Z.div_le_lower_bound; [lia|].
      pose proof (Z.mul_div_le F 8 ltac:(lia)). lia. }
  assert (SHR : forall x, sa <= x < sa + n -> in_shadow_of F B x).
  { intros x Hx. unfold in_shadow_of, HeapIfaceA.S in *. split; [lia|].
    assert (F / 8 + 8 * mB - 1 <= (F + B - 1) / 8); [|lia]. apply Z.div_le_lower_bound; [lia|]. pose proof (Z.mul_div_le F 8 ltac:(lia)). lia. }
  assert (XR : forall x, sa <= x < sa + n -> 0x7fff8000 <= x < 0x10007fff8000 /\ in_shadow_rw x).
  { intros x Hx. destruct SF as (SF1 & SF2). unfold HeapIfaceA.S, HeapIfaceA.SB, BIGSHADOW_LO, BIGSHADOW_HI, in_shadow_rw, LSH_LO, LSH_HI, HSH_LO, HSH_HI, FS_BYTES in *.
    pose proof (Z.div_pos fs 8 ltac:(lia) ltac:(lia)).
    destruct FG5b as [LOW | HIGH].
    - assert ((fs + 11571200) / 8 <= 0x7fff7000 / 8) by (apply Z.div_le_mono; lia). change (0x7fff7000 / 8) with 268430848 in *. lia.
    - assert (0x10007fff8000 / 8 <= fs / 8) by (apply Z.div_le_mono; lia). change (0x10007fff8000 / 8) with 2199291686912 in *.
      assert ((fs + 11571200) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia). change (2 ^ 47 / 8) with 17592186044416 in *. lia. }
  assert (CLW : forall x, sa <= x < sa + n -> aclientw L (rn_ar rn) LB FF sp 256 x).
  { intros x Hx. unfold aclientw, aclient_g. do 5 right. left. exists f. split; [exact Hf | exact (SHR x Hx)]. }
  assert (BSX : forall b x, In b LB -> in_shadow_of (fst b) (snd b) x -> ~ (sa <= x < sa + n)).
  { intros b x Hb Hx X. pose proof CLI as (CB & _). destruct (CB b Hb) as (_ & _ & _ & K4 & _ & _ & _ & _ & _ & _ & _ & K12 & _).
    apply (art_shadow_apart (fst b) (snd b) fs FS_BYTES x FS8 FSE8 K4 K12 Hx). destruct SF as (SF1 & SF2). lia. }
  assert (NP : forall x, sa <= x < sa + n -> ~ art_private L (rn_ar rn) LB FF x).
  { intros x Hx [NC | [RO | (b & Hb & BS)]].
    - apply NC. unfold aclient, aclient_g. do 5 right. left. exists f. split; [exact Hf | exact (SHR x Hx)].
    - pose proof (HLroimg x RO). destruct (XR x Hx) as (X1 & _). lia.
    - exact (BSX b x Hb BS Hx). }
  assert (VISD : forall x, sa <= x < sa + n -> bhid A model (Z_to_bv 64 x) = false).
  { intros x Hx. destruct (XR x Hx) as (X1 & _). apply (art_aclient_vis rn LB FF LK A M model LAZY CLI L HLlo HLhi (g_fs art_fsg G) FS sp 256 x); [lia|].
    right. apply aclientw_client. exact (CLW x Hx). }
  assert (SA0 : 0x7fff8000 <= sa /\ sa + n <= 0x10007fff8000).
  { destruct SF as (SF1 & SF2). unfold HeapIfaceA.S, HeapIfaceA.SB, FS_BYTES in *. pose proof (Z.div_pos fs 8 ltac:(lia) ltac:(lia)).
    assert ((fs + 11571200) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; unfold FS_BYTES in FG5c; lia). change (2 ^ 47 / 8) with 17592186044416 in *. lia. }
  set (FP := fun x => sa <= x < sa + n).
  apply (art_wrap_pure2 MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Hwx AFL K R pcw M model G LB FF LK cr A FP
           (fun R' pc1 Mr' => pc1 = getr R 1 /\ keeps_cs R R' /\ (forall j, 0 <= j < n -> Mr' (Z_to_bv 64 (sa + j)) = Some (Z_to_bv 8 v)))
           REPr FS B0 CRED CLI KN LZ EG).
  -
    destruct STAT as (_ & LAY & _).
    assert (HGL : setsh_globs Mr0).
    { destruct LAY as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & A11 & A12 & _). unfold setsh_globs. split; [lit_cell A11 | lit_cell A12]. }
    destruct SA0 as (SA1 & SA2).
    assert (HDST : store_ok ASEGS Mr0 (Z_to_bv 64 sa) (Z.to_nat n) = true).
    { apply (art_rng_store_ok A M model sa (Z.to_nat n) ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia)).
      - rewrite Z2Nat.id by lia. intros x Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply VISD. exact Hx.
      - apply store_ok_of_all; [rewrite art_u_lit by lia; rewrite Z2Nat.id by lia; lia|].
        intros x Hx. rewrite art_u_lit in Hx by lia. rewrite Z2Nat.id in Hx by lia.
        rewrite art_wview_off by (right; lia). apply (bi_shdef _ _ _ _ _ _ _ _ _ _ _ B0 x). exact (proj2 (XR (U x) Hx)). }
    destruct (RUNX Mr0 (seg_rom ASEGS) (getr R 1) sa n Hn ltac:(lia) HDST Hret HGL R H10 H11 eq_refl) as (R' & RUN & KCS).
    set (Mf := wbytes Mr0 (Z_to_bv 64 sa) (repeat (Z_to_bv 8 v) (Z.to_nat n))) in *.
    assert (LENR : Z.of_nat (length (repeat (Z_to_bv 8 v : byte) (Z.to_nat n))) = n) by (rewrite repeat_length, Z2Nat.id by lia; reflexivity).
    assert (FRr : forall x : word, ~ FP (U x) -> Mf x = Mr0 x).
    { intros x Hx. unfold FP in Hx. pose proof (u64_range x) as Rx. unfold Mf. destruct (Z_lt_le_dec (U x) sa) as [Lt | Ge].
      - apply wbytes_below; [rewrite LENR, art_u_lit by lia; lia | rewrite art_u_lit by lia; exact Lt].
      - apply wbytes_above. rewrite LENR, art_u_lit by lia. lia. }
    exists R', (getr R 1), Mf. split; [exact RUN|]. split; [apply wbytes_grows|]. split; [exact FRr|].
    split.
    {
      pose proof REPr as (_ & _ & (_ & _ & _ & _ & _ & _ & _ & CL) & _).
      assert (GEOL : 0x10000 <= rn_tp rn + rn_loff rn /\ rn_tp rn + rn_loff rn + 4 <= 0x6b3000).
      { pose proof ROK as ROK'. rok_open ROK'. geo_open GEO. clear - Hloff Hloff' Hloff'' Htpd G1 G2 Espb G4. lia. }
      apply (Pm8ArtAllocG.cell_agree Mr0 Mf); [| clear - GEOL; lia | cbn; clear - GEOL; lia | exact CL].
      intros x Hx. cbn in Hx. apply FRr. unfold FP. clear - Hx GEOL SA1. lia. }
    split; [reflexivity|]. split; [exact KCS|].
    intros j Hj. unfold Mf. rewrite (wbytes_inside _ Mr0 (Z_to_bv 64 sa) (Z_to_bv 64 (sa + j))).
    + rewrite !art_u_lit by lia. rewrite nth_repeat_lt by lia. reflexivity.
    + rewrite LENR, art_u_lit by lia. lia.
    + rewrite LENR, !art_u_lit by lia. lia.
  -
    intros x Hx Z. destruct (in_block_dec LB x) as [IB | NB]; [exact IB | exfalso].
    exact (NP x Hx (PRIVZ G LB FF LK A M Mr0 (m_vm_lazy model) REPr FS CLI (bi_live _ _ _ _ _ _ _ _ _ _ _ B0) KN LZ EG x Z NB)).
  -
    intros x Hx Z3. destruct (in_fframe_dec FF x) as [IB | NB]; [exact IB | exfalso].
    exact (NP x Hx (PRIVF G LB FF LK A M Mr0 (m_vm_lazy model) REPr FS CLI (bi_live _ _ _ _ _ _ _ _ _ _ _ B0) KN LZ EG x Z3 NB)).
  -
    intros x Hx Zc. exact (NP x Hx (PRIVCS G LB FF LK A M Mr0 (m_vm_lazy model) REPr FS CLI (bi_live _ _ _ _ _ _ _ _ _ _ _ B0) KN LZ EG x Zc)).
  -
    intros b x Hb Hx X. exact (BSX b x Hb Hx X).
  -
    intros R' pc1 Mr' M1 model' (Epc & KCS & BYTES) RI' GROW FR1 VIS1 HID RT MI'. subst pc1.
    apply (CONT R' M1 model' (keeps_cs_preserved R R' KCS)); [ | | | exact GROW | exact RT | exact MI' | exact RI'].
    + intros j Hj. unfold byte_at. rewrite (VIS1 _ (VISD (sa + j) ltac:(lia))). exact (BYTES j Hj).
    + intros a Ra Ha ND. apply FR1. rewrite art_u_lit by exact Ra. exact ND.
    + intros a Ha. apply GROW.
      assert (WM : wrA M (sp - 256) 256) by (intros d k Hd Hk; apply SWR; assumption).
      pose proof (art_wr_wview ASEGS M (sp - 256) 256 ltac:(clear - SHI HI1; lia) ltac:(clear - SLE STOP; lia) WM (Z_to_bv 64 a)) as V. rewrite art_u_lit in V by (clear - Ha SHI HI1 SLE STOP; lia). specialize (V ltac:(clear - Ha; lia)).
      rewrite art_wview_off in V by (rewrite art_u_lit by (clear - Ha SHI HI1 SLE STOP; lia); right; clear - Ha SHI HI1; lia). exact V.
Qed.
End WSS.

Section WSSI.
Variables MAPS0 RESV0 NOACC0 : list (word * word).
Variables BASE BUDGET : Z.
Variable rn : art_run.
Variable scfg : SpuriousCfg.
Hypothesis Hwx : wx_segs_nowrap ASEGS.
Variable L : asan_layout.
Hypothesis HLsegs : hl_segs L = ASEGS.
Hypothesis HLlo : hl_img_lo L = 0x10000.
Hypothesis HLhi : hl_img_hi L = 0x6b3000.
Hypothesis HLscrmem : hl_scr_mem L = 2560.
Hypothesis HLroimg : forall a, hl_rt_ro L a -> 0x10000 <= a < 0x6b3000.
Hypothesis HLstimg : forall a, hl_rt_static L a -> 0x10000 <= a < 0x6b3000.
Hypothesis HLst : forall a, art_zone_statics a -> hl_rt_static L a.
Hypothesis HLtls : forall a, (rn_tp rn - 88 <= a < rn_tp rn - 80 \/ rn_tsd rn + 8 * rn_key rn <= a < rn_tsd rn + 8 * rn_key rn + 8
                              \/ 0x690a48 <= a < 0x690a50 \/ 0x690a78 <= a < 0x690a80 \/ rn_tp rn <= a < rn_tp rn + 8
                              \/ rn_tp rn + rn_loff rn <= a < rn_tp rn + rn_loff rn + 4) -> hl_rt_static L a.
Hypothesis HLro : forall a, 0x10000 <= a < 0x154000 -> hl_rt_ro L a.
Hypothesis HLcs : forall a, (0x154f68 <= a < 0x154f70 \/ 0x155030 <= a < 0x155048 \/ rn_tp rn + 8 <= a < rn_tp rn + 16) -> hl_rt_static L a.
#[local] Abbreviation HI := (art_iface art_fsg MAPS0 RESV0 NOACC0 BASE BUDGET art_fsinv rn).

Let AFL : art_alloc_rep_frame_law art_fsg MAPS0 RESV0 := art_alloc_rep_frame_law_proved art_fsg MAPS0 RESV0.
Let HLlsan : forall a, rn_tp rn + rn_loff rn <= a < rn_tp rn + rn_loff rn + 4 -> hl_rt_static L a.
Proof. intros a Ha. apply HLtls. do 5 right. exact Ha. Qed.
Let PRIVZ : forall (G : art_gs art_fsg) LB FF LK A (M Mr : word -> option byte) (lazy : list (word * word)),
  art_alloc_rep art_fsg rn G LB Mr -> art_fsinv rn (g_fs art_fsg G) FF LK M -> art_client_ok rn LB FF LK A M ->
  live_ok MAPS0 RESV0 (rn_HI rn) (art_live (g_log art_fsg G)) -> art_kn_ok MAPS0 RESV0 rn -> art_lazy_ok art_fsg rn G A lazy -> art_eager_ok LB A lazy ->
  forall a, art_alloc_zone art_fsg rn G a -> ~ in_block LB a -> art_private L (rn_ar rn) LB FF a.
Proof. intros G LB FF LK A M Mr lazy REP FS CLI LV KN _ _. exact (art_priv_zone MAPS0 RESV0 rn L HLlo HLhi HLst HLtls HLro G LB FF LK A M Mr REP FS CLI LV KN). Qed.
Let PRIVF : forall (G : art_gs art_fsg) LB FF LK A (M Mr : word -> option byte) (lazy : list (word * word)),
  art_alloc_rep art_fsg rn G LB Mr -> art_fsinv rn (g_fs art_fsg G) FF LK M -> art_client_ok rn LB FF LK A M ->
  live_ok MAPS0 RESV0 (rn_HI rn) (art_live (g_log art_fsg G)) -> art_kn_ok MAPS0 RESV0 rn -> art_lazy_ok art_fsg rn G A lazy -> art_eager_ok LB A lazy ->
  forall a, fs_zone3 rn a -> ~ in_fframe FF a -> art_private L (rn_ar rn) LB FF a.
Proof. intros G LB FF LK A M Mr lazy REP FS CLI LV KN _ _. exact (art_priv_fs3 MAPS0 RESV0 rn L HLlo HLhi HLtls G LB FF LK A M Mr REP FS CLI LV KN). Qed.
Let PRIVCS : forall (G : art_gs art_fsg) LB FF LK A (M Mr : word -> option byte) (lazy : list (word * word)),
  art_alloc_rep art_fsg rn G LB Mr -> art_fsinv rn (g_fs art_fsg G) FF LK M -> art_client_ok rn LB FF LK A M ->
  live_ok MAPS0 RESV0 (rn_HI rn) (art_live (g_log art_fsg G)) -> art_kn_ok MAPS0 RESV0 rn -> art_lazy_ok art_fsg rn G A lazy -> art_eager_ok LB A lazy ->
  forall a, cs_zone rn a -> art_private L (rn_ar rn) LB FF a.
Proof. intros G LB FF LK A M Mr lazy REP FS CLI LV KN _ _. exact (art_priv_cs MAPS0 RESV0 rn L HLlo HLhi HLcs G LB FF LK A M Mr REP FS CLI LV KN). Qed.

Lemma art_asetsh_at : forall (pc : Z) (pcw : word) (v : Z), Z_to_bv 64 pc = pcw -> 0 <= v < 256 ->
  (forall (fx : PropExec.FPState) (mem0 rom : word -> option byte) (ra : word) (sa n : Z),
     0 <= n -> (0 <= sa /\ sa + n < 2 ^ 64) -> store_ok ASEGS mem0 (Z_to_bv 64 sa) (Z.to_nat n) = true -> Hoare.ret_ok ra -> setsh_globs mem0 ->
     forall regs, getr regs 10 = Z_to_bv 64 sa -> getr regs 11 = Z_to_bv 64 n -> getr regs 1 = ra ->
     exists regs', msteps ASEGS (@mkst fx regs pcw mem0 rom) (@mkst fx regs' ra (wbytes mem0 (Z_to_bv 64 sa) (repeat (Z_to_bv 8 v) (Z.to_nat n))) rom) /\ keeps_cs regs regs') ->
  aset_shadow_spec L (rn_ar rn) scfg HI pc v 256.
Proof using All.
  intros pc pcw v Epc Hv RUN fx R M model LB FF LK cr A f sa n K. cbv zeta.
  intros INV Hh HMI H10 H11 Hf Hn LO HIb Hret AST KT0 POST. rewrite HLsegs in *. rewrite Epc.
  apply (art_wrap_setshadow MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Hwx AFL L HLsegs HLlo HLhi HLroimg PRIVZ PRIVF PRIVCS pcw v Hv (RUN fx)
           R M model LB FF LK cr A f sa n K INV Hh HMI H10 H11 Hf Hn LO HIb Hret AST KT0).
  intros R' M' model' RP BY FR SD GR RT MI' RI'. apply (POST R' M' model' RP BY FR SD GR RT MI' RI').
Qed.
Theorem art_asetsh_00 : aset_shadow_spec L (rn_ar rn) scfg HI 0x829e4 0 256.
Proof using All. apply (art_asetsh_at 0x829e4 (0x829e4 : word) 0 ltac:(apply bv_eq; reflexivity) ltac:(lia)). intros fx. exact (@setsh_00_run fx). Qed.
Theorem art_asetsh_f5 : aset_shadow_spec L (rn_ar rn) scfg HI 0x82aec 245 256.
Proof using All. apply (art_asetsh_at 0x82aec (0x82aec : word) 245 ltac:(apply bv_eq; reflexivity) ltac:(lia)). intros fx. exact (@setsh_f5_run fx). Qed.
Theorem art_asetsh_f8 : aset_shadow_spec L (rn_ar rn) scfg HI 0x82b04 248 256.
Proof using All. apply (art_asetsh_at 0x82b04 (0x82b04 : word) 248 ltac:(apply bv_eq; reflexivity) ltac:(lia)). intros fx. exact (@setsh_f8_run fx). Qed.
End WSSI.
