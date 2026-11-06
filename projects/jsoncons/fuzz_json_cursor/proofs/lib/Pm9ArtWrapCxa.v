(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare ShapeAlg SpinAlg AsanAcct RefMemcpyLib MemSplit StreamSim HeapIface HeapIfaceA PmHeapIfaceA IcptIfaceA PmIcptIfaceA ArtMem ArtRuns ArtRunsMem Pm9ArtCls Pm9ArtLeaf Pm9ArtCellEx Pm9ArtImgCell Pm9ArtPoison Pm9ArtDepot
     ArtBridge Pm9ArtInv Pm9ArtInvMalloc Pm9ArtLift Pm9ArtWrapKit Pm9ArtFsInv Pm9ArtFsInvLaws Pm9ArtIfaceLaws Pm9ArtInvFrame Pm9ArtIfaceFrame Pm9RegionPoisoned.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import Pm9ArtWrapC Pm9ArtWrapVis Pm9ArtWrapC2 Pm9ArtWrapC2x Pm9ArtWrapRng.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import Pm9CxaIcpt.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Lemma wcx_wseg_lsan : wseg_ok ASEGS (Z_to_bv 64 0x691da0) 4 = true.
Proof. vmc_refl. Qed.
Lemma wcx_lit1 : forall (Mx : word -> option byte) (w : word) a v, w = Z_to_bv 64 a -> 0 <= v < 256 -> cellA Mx a 1 v -> rdn ASEGS Mx w 1%nat = Some [Z_to_bv 8 v].
Proof. intros Mx w a v -> Hv C. apply cell_rdn1; assumption. Qed.

Section WCX.
Variables MAPS0 RESV0 NOACC0 : list (word * word).
Variables BASE BUDGET : Z.
Variable rn : art_run.
Variable scfg : SpuriousCfg.
Hypothesis Hwx : wx_segs_nowrap ASEGS.
Variable L : asan_layout.
Hypothesis HLsegs : hl_segs L = ASEGS.
Hypothesis HLlo : hl_img_lo L = 0x10000.
Hypothesis HLhi : hl_img_hi L = 0x6b4000.
Hypothesis Htp : rn_tp rn = 0x691d90.
Hypothesis HLoff16 : rn_loff rn = 0x10.
Hypothesis Hkey0 : rn_key rn = 0.
Hypothesis Htsd : rn_tsd rn = 0x6b3248.
Hypothesis HLlsan : forall a, 0x691da0 <= a < 0x691da4 -> hl_rt_static L a.
#[local] Abbreviation RI := (art_ri_inv art_fsg MAPS0 RESV0 NOACC0 BASE BUDGET art_fsinv rn).
Context {fx : PropExec.FPState}.

Theorem art_wrap_cxa_atexit : forall (R : bvmap 5 word) (M : word -> option byte) (model : Model)
    (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (f arg : Z) (hs : list (Z * Z)) (Kt : ShapeAlg.TSet),
  let sp := U (getr R 2) in
  RI LB FF LK cr A M (vml_of model) -> m_halted model = None -> MInv A model ->
  getr R 10 = Z_to_bv 64 f -> getr R 11 = Z_to_bv 64 arg -> 0 <= f < 2 ^ 64 -> 0 <= arg < 2 ^ 64 ->
  getr R 4 = Z_to_bv 64 (rn_tp rn) -> Hoare.ret_ok (getr R 1) ->
  astack_ok L (rn_ar rn) M 512 sp ->
  atexit_state_at ASEGS 0x6b1de0 M hs -> Z.of_nat (length hs) + 2 <= 32 -> hs <> [] ->
  cell_is ASEGS M 0x6b2023 1 0 ->
  (forall d (m : nat), 0 <= d -> d + Z.of_nat m <= ATEXIT_TAB_BYTES -> store_ok ASEGS M (Z_to_bv 64 (0x6b1de0 + d)) m = true) ->
  Kt [] ->
  (forall (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model),
      getr R' 10 = Z_to_bv 64 0 -> regs_preserved R R' ->
      atexit_state_at ASEGS 0x6b1de0 M' (hs ++ [(f, arg); (0x7503c, 0)]) ->
      (forall a, 0 <= a < 2 ^ 64 -> aclient L (rn_ar rn) LB FF sp 512 a -> ~ (0x6b1de0 <= a < 0x6b1de0 + ATEXIT_TAB_BYTES) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
      (forall a, sp - 512 <= a < sp -> M' (Z_to_bv 64 a) <> None) ->
      (forall a : word, M a <> None -> M' a <> None) ->
      model_rt model model' -> MInv A model' -> RI LB FF LK cr A M' (vml_of model') ->
      srealizes ASEGS scfg (mkCfg (mkst R' (getr R 1) M' (seg_rom ASEGS)) model') Kt) ->
  srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x6a9ec) M (seg_rom ASEGS)) model) Kt.
Proof.
  intros R M model LB FF LK cr A f arg hs Kt sp INV Hhalt HMI H10 H11 Hf Harg H4 Hret AST TAB HLEN HNE CNL TABW KT0 CONT.
  destruct (art_ri_open MAPS0 RESV0 NOACC0 BASE BUDGET rn LB FF LK cr A M model INV Hhalt HMI) as (G & REPr & FS & B0 & CRED & CLI & KN & LZ & EG).
  set (Mr0 := mrestrict (bhid A model) M) in *.
  destruct AST as (S16 & SHI & SLE & STOP & SWR & SDEF). fold sp in S16, SHI, SLE, SWR, SDEF. rewrite HLsegs in SWR.
  assert (HIeq : ahl_ceil (rn_ar rn) = rn_HI rn) by reflexivity. rewrite HIeq in SHI.
  pose proof (art_cli_hi rn LB FF LK A M CLI) as (HI1 & HI2).
  pose proof REPr as (ROK & STAT & THR & _).
  pose proof CLI as (CB & _ & SAst & SAfs & _ & _ & _ & _ & _ & _ & SAimg & _). rewrite HIeq in SAst.
  assert (HIdef : rn_HI rn = ar_sptop (rn_ar rn) - 8388608) by reflexivity.
  assert (SPR : 0x7fff7f800000 + 4608 <= sp <= 2 ^ 47) by (clear - SHI HI1 SLE STOP; lia).
  assert (LAZY : forall w : word, page_in_ranges (page_base w) (m_vm_lazy model) = true ->
            0x6b4000 <= U w /\ U w < rn_HI rn /\ ~ in_block LB (U w) /\ ~ (ar_fs (rn_ar rn) <= U w < ar_fs (rn_ar rn) + FS_BYTES)).
  { intros w Hw. destruct LZ as (L1 & _). destruct (art_lazy_zone_bounds art_fsg rn G (U w) ROK (L1 w Hw)) as (B1 & B2).
    split; [lia|]. split; [exact (proj2 B1)|]. split; [|exact B2]. intros (b & Hb & Hr). rewrite (proj2 EG b w Hb Hr) in Hw. discriminate Hw. }
  assert (VIMG : forall x : word, U x < 0x6b4000 -> bhid A model x = false) by (intros x Hx; apply (art_vis_byte rn LB A model LAZY); left; exact Hx).
  assert (VSTK : forall x : word, rn_HI rn <= U x -> bhid A model x = false) by (intros x Hx; apply (art_vis_byte rn LB A model LAZY); right; left; exact Hx).
  assert (IMGV : forall a (n : nat) v, cellA M a n v -> 0 <= a -> a + Z.of_nat n <= 0x6b4000 -> cellA Mr0 a n v).
  { intros a n v C A1 A2. apply (proj2 (art_cell_vis (bhid A model) M a n v A1 ltac:(clear - A2; lia) ltac:(intros x Hx; apply VIMG; clear - Hx A2; lia))). exact C. }

  destruct STAT as (PC & LAY & TSD & _ & _ & _ & TLSG & S8).
  destruct THR as (_ & _ & _ & _ & _ & _ & _ & LSAN0). rewrite Htp, HLoff16 in LSAN0. change (6888848 + 16) with 6888864 in LSAN0.
  assert (W0 : wrA Mr0 (sp - 512) 512).
  { apply (art_stack_wr art_fsg rn G A (m_vm_lazy model) M sp 512 ROK LZ ltac:(clear - SHI; lia) ltac:(clear; lia) ltac:(clear - SPR; lia)). exact SWR. }
  assert (INITED : cellA Mr0 0x15e9d8 1 1) by conj_find S8.
  assert (LOFF : cellA Mr0 0x155160 8 (rn_loff rn)) by conj_find S8. rewrite HLoff16 in LOFF.
  assert (REAL : cellA Mr0 0x1564c8 8 0x1351b4) by conj_find S8.
  set (n := Z.of_nat (length hs)).
  assert (Hn : 0 < n /\ n + 1 < 32). { unfold n. destruct hs; [contradiction|]. cbn [length] in *. lia. }
  destruct TAB as (TFIN & TLOCK & TREST). assert (TR : cell_is ASEGS M (0x6b1de0 + 16) 8 (0x6b1de0 + 24) /\ cell_is ASEGS M (0x6b1de0 + 8) 4 n /\ cell_is ASEGS M (0x6b1de0 + 24) 8 0
      /\ (forall i f0 a0, nth_error hs i = Some (f0, a0) -> cell_is ASEGS M (0x6b1de0 + 32 + 8 * Z.of_nat i) 8 f0 /\ cell_is ASEGS M (0x6b1de0 + 288 + 8 * Z.of_nat i) 8 a0)).
  { destruct hs as [|h0 t0]; [contradiction|]. destruct TREST as (_ & T1 & T2 & T3 & T4). split; [exact T1|]. split; [exact T2|]. split; [exact T3|exact T4]. }
  clear TREST. destruct TR as (THEAD & TSLOT & TNEXT & TENT).
  assert (WL : store_ok ASEGS Mr0 (0x691da0 : word) 4%nat = true).
  { apply (store_ok_window ASEGS Mr0 (Z_to_bv 64 0x691da0) (0x691da0 : word) 4%nat 4%nat 0x691da0 (0x691da0 + 4)); first [exact wcx_wseg_lsan | reflexivity | lia | (vm_compute; intuition discriminate)]. }
  assert (WTAB : forall d (m : nat), 0 <= d -> d + Z.of_nat m <= 544 -> store_ok ASEGS Mr0 (Z_to_bv 64 (0x6b1de0 + d)) m = true).
  { intros d m Hd Hm. apply (art_rng_store_ok A M model (0x6b1de0 + d) m ltac:(clear - Hd; lia) ltac:(clear - Hd Hm; lia)); [|apply TABW; unfold ATEXIT_TAB_BYTES; assumption].
    intros x Hx. apply VIMG. clear - Hx Hd Hm. lia. }
  assert (Hs96 : 0x1000000 <= sp - 96 /\ sp < 2 ^ 64) by (clear - SPR; lia).
  assert (OK96 : store_ok ASEGS Mr0 (Z_to_bv 64 (sp - 96)) 96%nat = true).
  { replace (sp - 96) with (sp - 512 + 416) by ring. apply W0; [lia | cbn; lia]. }
  destruct (cxi_run Mr0 (seg_rom ASEGS) (getr R 2) (getr R 1) sp f arg n eq_refl Hret Hs96 OK96 Hn Hf Harg
              ltac:(apply (wcx_lit1 Mr0 _ 0x15e9d8 1); [apply bv_eq; reflexivity | lia | exact INITED])
              ltac:(lit_cell LOFF) ltac:(lit_cell LSAN0) WL ltac:(lit_cell REAL)
              ltac:(apply (wcx_lit1 Mr0 _ 0x6b2023 0); [apply bv_eq; reflexivity | lia | exact (IMGV _ _ _ CNL ltac:(lia) ltac:(cbn; lia))])
              ltac:(apply (wcx_lit1 Mr0 _ 0x6b1de0 0); [apply bv_eq; reflexivity | lia | exact (IMGV _ _ _ TFIN ltac:(lia) ltac:(cbn; lia))])
              ltac:(pose proof (IMGV _ _ _ THEAD ltac:(lia) ltac:(cbn; lia)) as X; lit_cell X)
              ltac:(pose proof (IMGV _ _ _ TSLOT ltac:(lia) ltac:(cbn; lia)) as X; lit_cell X)
              ltac:(pose proof (IMGV _ _ _ TLOCK ltac:(lia) ltac:(cbn; lia)) as X; lit_cell X)
              WTAB R H10 H11 eq_refl eq_refl ltac:(rewrite H4, Htp; apply bv_eq; reflexivity))
    as (R1 & Mr1 & RUN & GR1 & FR1 & RDF & RDA & RDF2 & RDA2 & RDS & RDC & E10 & KCS).

  assert (GEOX : (rn_t rn + 4096 <= 0x10000 \/ 0x6b4000 <= rn_t rn) /\ (ar_fs (rn_ar rn) + FS_BYTES <= 0x10000 \/ 0x6b4000 <= ar_fs (rn_ar rn))
                 /\ (rn_dtls rn + 4096 <= 0x10000 \/ 0x6b4000 <= rn_dtls rn) /\ 4096 <= ar_fs (rn_ar rn)).
  { pose proof ROK as ROK'. rok_open ROK'. geo_open GEO. repeat split; assumption. }
  destruct GEOX as (Gt3 & Gf4 & Gd5 & Gf1).
  assert (ZLS : forall x, art_alloc_zone art_fsg rn G x -> ~ (6888864 <= x < 6888868 \/ 0x6b1de0 <= x < 0x6b1de0 + 544)).
  { intros x Z X. pose proof ROK as ROK'. rok_open ROK'. geo_open GEO.
    pose proof (art_live_of_binv MAPS0 RESV0 NOACC0 BASE BUDGET rn _ _ _ _ B0 KN) as LIVE.
    unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in Papp. unfold apart in *.
    destruct Z as [Z | [Z | [Z | [Z | [Z | [Z | [Z | [Z | [Z | [Z | [Z | Z]]]]]]]]]]].
    - unfold art_zone_statics in Z. clear - Z X. lia.
    - unfold art_zone_thread in Z. clear - Z X G9. lia.
    - clear - Z X G15. lia.
    - unfold art_zone_kspace in Z. clear - Z X Khi. lia.
    - destruct Z as [Z | (p & Hp & Z)]; [clear - Z X Plo; lia|]. destruct (LIVE p Hp) as (L1 & L2 & L3 & L4 & L5).
      specialize (L5 (0x156000, 0x55e000) ltac:(unfold art_objs; do 10 right; left; reflexivity)). unfold apart in L5. cbn [fst snd] in L5. clear - Z X L5. lia.
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
  set (FP := cxi_fp sp n).
  assert (FPC : forall x, FP x -> sp - 96 <= x < sp \/ 6888864 <= x < 6888868 \/ 0x6b1de0 <= x < 0x6b1de0 + 544).
  { intros x X. unfold FP, cxi_fp in X. clear - X Hn. lia. }
  apply (art_wrap_pure2x MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Hwx (art_alloc_rep_frame_law_proved art_fsg MAPS0 RESV0) Kt R (Z_to_bv 64 0x6a9ec) M model G LB FF LK cr A FP
           (fun fx' R' pc1 Mr' => fx' = fx /\ pc1 = getr R 1 /\ getr R' 10 = Z_to_bv 64 0 /\ keeps_cs R R'
              /\ rdn ASEGS Mr' (Z_to_bv 64 (0x6b1de0 + 32 + 8 * n)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 f))
              /\ rdn ASEGS Mr' (Z_to_bv 64 (0x6b1de0 + 288 + 8 * n)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 arg))
              /\ rdn ASEGS Mr' (Z_to_bv 64 (0x6b1de0 + 32 + 8 * (n + 1))) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x7503c))
              /\ rdn ASEGS Mr' (Z_to_bv 64 (0x6b1de0 + 288 + 8 * (n + 1))) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
              /\ rdn ASEGS Mr' (Z_to_bv 64 (0x6b1de0 + 8)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 (n + 2))))
           REPr FS B0 CRED CLI KN LZ EG).
  -
    exists fx, R1, (getr R 1), Mr1. split. { replace (Z_to_bv 64 0x6a9ec : word) with (0x6a9ec%bv : word) by (apply bv_eq; reflexivity). exact RUN. }
    split; [exact GR1|]. split; [exact FR1|].
    split. { rewrite Htp, HLoff16. unfold cell. replace (Z_to_bv 64 (6888848 + 16) : word) with (0x691da0%bv : word) by (apply bv_eq; reflexivity). exact RDC. }
    repeat (split; [first [reflexivity | assumption]|]). assumption.
  -
    intros x HF Z. exfalso. destruct (FPC x HF) as [Hx | Hx].
    + pose proof (art_zone_below MAPS0 RESV0 NOACC0 BASE BUDGET rn G LB A M Mr0 model x REPr KN B0 (or_introl Z)) as ZB. clear - ZB Hx SHI. lia.
    + exact (ZLS x Z Hx).
  -
    intros x HF Z3. exfalso. pose proof (art_fs_zone3_below rn G LB _ x REPr Z3) as ZB.
    destruct (FPC x HF) as [Hx | Hx]; [clear - ZB Hx SHI; lia |].
    unfold fs_zone3 in Z3. rewrite Htp in Z3. clear - Z3 Hx Gt3 Gf4. unfold FS_BYTES in *. lia.
  -
    intros x HF Zc. pose proof (art_cs_zone_below rn G LB FF LK M Mr0 x REPr FS Zc) as ZB.
    destruct (FPC x HF) as [Hx | Hx]; [clear - ZB Hx SHI; lia |].
    unfold cs_zone in Zc. rewrite Htp in Zc. change (HeapIfaceA.S 0x10000) with 2147459072 in Zc. clear - Zc Hx Gd5. lia.
  -
    intros b x Hb Hx HF. pose proof (art_block_shadow_below rn LB FF LK A M b x CLI Hb Hx) as B1.
    destruct (CB b Hb) as (K1 & _). pose proof (art_S_lo (fst b) ltac:(clear - K1; lia)) as B2. destruct Hx as (Hx1 & _).
    destruct (FPC x HF) as [X | X]; [clear - X B1 SHI HI1; lia | clear - X Hx1 B2; lia].
  -
    intros fx2 R' pc1 Mr' M1 model' (Efx & Epc & E10' & KCS' & QF & QA & QF2 & QA2 & QS) RI' GROW FRM VIS1 HID RT MI'. subst pc1 fx2.
    assert (NEWC : forall a (k : nat) v, 0 <= a -> a + Z.of_nat k <= 0x6b4000 -> rdn ASEGS Mr' (Z_to_bv 64 a) k = Some (word_to_le_bytes k (Z_to_bv 64 v)) -> cell_is ASEGS M1 a k v).
    { intros a k v A1 A2 RD. unfold cell_is. rewrite <- RD. apply rdn_ext; [rewrite art_u_lit by (clear - A1 A2; lia); clear - A1 A2; lia|].
      intros x Hx. rewrite art_u_lit in Hx by (clear - A1 A2; lia). apply VIS1. apply VIMG. clear - Hx A2. lia. }
    assert (OLDC : forall a (k : nat) v, 0 <= a -> a + Z.of_nat k <= 0x6b4000 -> (forall z, a <= z < a + Z.of_nat k -> ~ FP z) -> cell_is ASEGS M a k v -> cell_is ASEGS M1 a k v).
    { intros a k v A1 A2 NF C. apply (art_cell_agree ASEGS M M1 a k v); [|exact A1|clear - A2; lia|exact C]. intros x Hx. apply FRM. apply NF. exact Hx. }
    apply (CONT R' M1 model' E10' (keeps_cs_preserved R R' KCS')); [ | | | exact GROW | exact RT | exact MI' | exact RI'].
    +
      unfold atexit_state_at.
      split. { apply OLDC; [lia | cbn; lia | | exact TFIN]. intros z Hz. unfold FP, cxi_fp. cbn in Hz. clear - Hz Hn SPR. lia. }
      split. { apply OLDC; [lia | cbn; lia | | exact TLOCK]. intros z Hz. unfold FP, cxi_fp. cbn in Hz. clear - Hz Hn SPR. lia. }
      assert (LEN : Z.of_nat (length (hs ++ [(f, arg); (0x7503c, 0)])) = n + 2) by (rewrite length_app; cbn [length]; unfold n; lia).
      remember (hs ++ [(f, arg); (0x7503c, 0)]) as hs2 eqn:EH. destruct hs2 as [|h1 t1]; [destruct hs; discriminate EH|]. cbv iota.
      split; [rewrite LEN; clear - Hn; lia|].
      split. { apply OLDC; [lia | cbn; lia | | exact THEAD]. intros z Hz. unfold FP, cxi_fp. cbn in Hz. clear - Hz Hn SPR. lia. }
      split. { rewrite LEN. apply NEWC; [lia | cbn; lia | exact QS]. }
      split. { apply OLDC; [lia | cbn; lia | | exact TNEXT]. intros z Hz. unfold FP, cxi_fp. cbn in Hz. clear - Hz Hn SPR. lia. }
      intros i f0 a0 Hi. rewrite EH in Hi.
      destruct (Nat.lt_ge_cases i (length hs)) as [Lo | Hi'].
      * rewrite nth_error_app1 in Hi by exact Lo. destruct (TENT i f0 a0 Hi) as (C1 & C2).
        split; (apply OLDC; [lia | cbn; unfold n in Hn; lia | | assumption]); intros z Hz; unfold FP, cxi_fp; cbn in Hz; unfold n in *; clear - Hz Hn SPR Lo; lia.
      * rewrite nth_error_app2 in Hi by exact Hi'. destruct (i - length hs)%nat as [|[|k]] eqn:Ei; cbn [nth_error] in Hi.
        -- injection Hi as <- <-. assert (Ein : Z.of_nat i = n) by (unfold n; lia). rewrite Ein.
           split; (apply NEWC; [clear - Hn; lia | cbn; clear - Hn; lia | assumption]).
        -- injection Hi as <- <-. assert (Ein : Z.of_nat i = n + 1) by (unfold n; lia). rewrite Ein.
           split; (apply NEWC; [clear - Hn; lia | cbn; clear - Hn; lia | assumption]).
        -- destruct k; discriminate Hi.
    + intros a Ra Ha NB. apply FRM. rewrite art_u_lit by exact Ra. intros HF. destruct (FPC a HF) as [X | [X | X]].
      * apply (art_cls_off_scratch rn LB FF LK A M CLI L HLlo HLhi (g_fs art_fsg G) FS sp 512 a ltac:(clear - SHI; lia) (or_intror Ha)). clear - X. lia.
      *
        pose proof (fsinv_frame_in rn _ _ _ _ FS) as FIN.
        destruct Ha as [H | [H | [H | [H | [H | [H | H]]]]]]; rewrite ?HLlo, ?HLhi in H.
        -- destruct H as (b & Hb & Rb). destruct (CB b Hb) as (_ & K2 & _). clear - Rb K2 X. lia.
        -- rewrite HIeq in H. clear - H X HI1. lia.
        -- destruct H as (_ & NS). apply NS. apply HLlsan. clear - X. lia.
        -- destruct H as (f1 & Hf1 & R1' & _). destruct (FIN f1 ltac:(apply in_or_app; left; exact Hf1)) as (I1 & I2 & _). unfold FS_BYTES in I2. clear - R1' I1 I2 X Gf4. unfold FS_BYTES in Gf4. lia.
        -- destruct H as (H1' & _). pose proof (art_S_lo (rn_HI rn) ltac:(clear - HI1; lia)) as SL. rewrite HIeq in H1'. clear - H1' SL X. lia.
        -- destruct H as (f1 & Hf1 & (H1' & _)). destruct (FIN f1 ltac:(apply in_or_app; left; exact Hf1)) as (I1 & _). pose proof (art_S_lo (ff_addr f1) ltac:(clear - I1 Gf1; lia)) as SL. clear - H1' SL X. lia.
        -- destruct H as (b & Hb & (H1' & _)). destruct (CB b Hb) as (K1 & _). pose proof (art_S_lo (fst b) ltac:(clear - K1; lia)) as SL. clear - H1' SL X. lia.
      * apply NB. unfold ATEXIT_TAB_BYTES. exact X.
    + intros a Ha. apply GROW.
      assert (WM : wrA M (sp - 512) 512) by (intros d m Hd Hm; apply SWR; assumption).
      pose proof (art_wr_wview ASEGS M (sp - 512) 512 ltac:(clear - SHI HI1; lia) ltac:(clear - SPR; lia) WM (Z_to_bv 64 a)) as Vw. rewrite art_u_lit in Vw by (clear - Ha SPR; lia). specialize (Vw ltac:(clear - Ha; lia)).
      rewrite art_wview_off in Vw by (rewrite art_u_lit by (clear - Ha SPR; lia); right; clear - Ha SHI HI1; lia). exact Vw.
Qed.

Theorem art_wrap_atcxa : forall (R : bvmap 5 word) (M : word -> option byte) (model : Model)
    (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (Kt : ShapeAlg.TSet),
  let sp := U (getr R 2) in
  RI LB FF LK cr A M (vml_of model) -> m_halted model = None -> MInv A model ->
  Hoare.ret_ok (getr R 1) ->
  astack_ok L (rn_ar rn) M 512 sp ->
  Kt [] ->
  (forall (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model),
      regs_preserved R R' ->
      (forall a, 0 <= a < 2 ^ 64 -> aclient L (rn_ar rn) LB FF sp 512 a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
      (forall a, sp - 512 <= a < sp -> M' (Z_to_bv 64 a) <> None) ->
      (forall a : word, M a <> None -> M' a <> None) ->
      model_rt model model' -> MInv A model' -> RI LB FF LK cr A M' (vml_of model') ->
      srealizes ASEGS scfg (mkCfg (mkst R' (getr R 1) M' (seg_rom ASEGS)) model') Kt) ->
  srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x7503c) M (seg_rom ASEGS)) model) Kt.
Proof.
  intros R M model LB FF LK cr A Kt sp INV Hhalt HMI Hret AST KT0 CONT.
  destruct (art_ri_open MAPS0 RESV0 NOACC0 BASE BUDGET rn LB FF LK cr A M model INV Hhalt HMI) as (G & REPr & FS & B0 & CRED & CLI & KN & LZ & EG).
  set (Mr0 := mrestrict (bhid A model) M) in *.
  destruct AST as (S16 & SHI & SLE & STOP & SWR & SDEF). fold sp in S16, SHI, SLE, SWR, SDEF. rewrite HLsegs in SWR.
  assert (HIeq : ahl_ceil (rn_ar rn) = rn_HI rn) by reflexivity. rewrite HIeq in SHI.
  pose proof (art_cli_hi rn LB FF LK A M CLI) as (HI1 & HI2).
  pose proof REPr as (ROK & STAT & THR & _).
  pose proof CLI as (CB & _).
  assert (SPR : 0x7fff7f800000 + 4608 <= sp <= 2 ^ 47) by (clear - SHI HI1 SLE STOP; lia).
  destruct STAT as (PC & LAY & TSD & _ & _ & _ & TLSG & S8).
  destruct THR as (_ & _ & _ & _ & _ & _ & _ & LSAN0).
  assert (W0 : wrA Mr0 (sp - 512) 512).
  { apply (art_stack_wr art_fsg rn G A (m_vm_lazy model) M sp 512 ROK LZ ltac:(clear - SHI; lia) ltac:(clear; lia) ltac:(clear - SPR; lia)). exact SWR. }
  assert (FLG : cellA Mr0 0x1544f8 8 0x15b4f8) by conj_find LAY.
  assert (CIO : cellA Mr0 0x15b514 1 0) by conj_find S8.
  assert (Hs96 : 0x1000000 <= sp - 96 /\ sp < 2 ^ 64) by (clear - SPR; lia).
  assert (OK96 : store_ok ASEGS Mr0 (Z_to_bv 64 (sp - 96)) 96%nat = true).
  { replace (sp - 96) with (sp - 512 + 416) by ring. apply W0; [lia | cbn; lia]. }
  destruct (hnd_run Mr0 (seg_rom ASEGS) (getr R 2) (getr R 1) sp eq_refl Hret Hs96 OK96 ltac:(lit_cell FLG)
              ltac:(apply (wcx_lit1 Mr0 _ 0x15b514 0); [apply bv_eq; reflexivity | lia | exact CIO]) R eq_refl eq_refl) as (R1 & RUN & KCS).
  set (Mr1 := hnd_mem Mr0 (getr R 1) sp R) in *.
  assert (GL : 0x10000 <= rn_tp rn + rn_loff rn /\ rn_tp rn + rn_loff rn + 4 <= 0x6b4000).
  { pose proof ROK as ROK'. rok_open ROK'. geo_open GEO. split; assumption. }
  set (FP := fun x => sp - 96 <= x < sp).
  apply (art_wrap_pure2x MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Hwx (art_alloc_rep_frame_law_proved art_fsg MAPS0 RESV0) Kt R (Z_to_bv 64 0x7503c) M model G LB FF LK cr A FP
           (fun fx' R' pc1 Mr' => fx' = fx /\ pc1 = getr R 1 /\ keeps_cs R R') REPr FS B0 CRED CLI KN LZ EG).
  - exists fx, R1, (getr R 1), Mr1. split. { replace (Z_to_bv 64 0x7503c : word) with (0x7503c%bv : word) by (apply bv_eq; reflexivity). exact RUN. }
    split; [apply hnd_grows|]. split. { intros x Hx. unfold Mr1. apply hnd_frame; [exact Hs96 | exact Hx]. }
    split. { apply (art_cell_agree ASEGS Mr0 Mr1 _ 4%nat 0); [|clear - GL; lia|cbn; clear - GL; lia|exact LSAN0].
             intros x Hx. unfold Mr1. apply hnd_frame; [exact Hs96|]. cbn in Hx. clear - Hx GL SPR. lia. }
    repeat split; assumption.
  - intros x Hx Z. exfalso. pose proof (art_zone_below MAPS0 RESV0 NOACC0 BASE BUDGET rn G LB A M Mr0 model x REPr KN B0 (or_introl Z)) as ZB. unfold FP in Hx. clear - ZB Hx SHI. lia.
  - intros x Hx Z3. exfalso. pose proof (art_fs_zone3_below rn G LB _ x REPr Z3) as ZB. unfold FP in Hx. clear - ZB Hx SHI. lia.
  - intros x Hx Zc. pose proof (art_cs_zone_below rn G LB FF LK M Mr0 x REPr FS Zc) as ZB. unfold FP in Hx. clear - ZB Hx SHI. lia.
  - intros b x Hb Hx HF. pose proof (art_block_shadow_below rn LB FF LK A M b x CLI Hb Hx) as B1. unfold FP in HF. clear - HF B1 SHI HI1. lia.
  - intros fx2 R' pc1 Mr' M1 model' (Efx & Epc & KCS') RI' GROW FRM VIS1 HID RT MI'. subst pc1 fx2.
    apply (CONT R' M1 model' (keeps_cs_preserved R R' KCS')); [ | | exact GROW | exact RT | exact MI' | exact RI'].
    + intros a Ra Ha. apply FRM. rewrite art_u_lit by exact Ra. unfold FP. intros X.
      apply (art_cls_off_scratch rn LB FF LK A M CLI L HLlo HLhi (g_fs art_fsg G) FS sp 512 a ltac:(clear - SHI; lia) (or_intror Ha)). clear - X. lia.
    + intros a Ha. apply GROW.
      assert (WM : wrA M (sp - 512) 512) by (intros d m Hd Hm; apply SWR; assumption).
      pose proof (art_wr_wview ASEGS M (sp - 512) 512 ltac:(clear - SHI HI1; lia) ltac:(clear - SPR; lia) WM (Z_to_bv 64 a)) as Vw. rewrite art_u_lit in Vw by (clear - Ha SPR; lia). specialize (Vw ltac:(clear - Ha; lia)).
      rewrite art_wview_off in Vw by (rewrite art_u_lit by (clear - Ha SPR; lia); right; clear - Ha SHI HI1; lia). exact Vw.
Qed.

Theorem art_wrap_ret_handler : forall (pc0 : Z) (w : bv 32), fetch_word ASEGS (Z_to_bv 64 pc0) = Some w -> is_ecall w = false -> decode_any w = Some (Jalr 0%bv 1%bv 0%bv, 4%Z) ->
  forall (R : bvmap 5 word) (M : word -> option byte) (model : Model)
    (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (Kt : ShapeAlg.TSet),
  RI LB FF LK cr A M (vml_of model) -> m_halted model = None -> MInv A model ->
  Hoare.ret_ok (getr R 1) ->
  Kt [] ->
  (forall (M' : word -> option byte) (model' : Model),
      (forall a : word, M' a = M a) ->
      model_rt model model' -> MInv A model' -> RI LB FF LK cr A M' (vml_of model') ->
      srealizes ASEGS scfg (mkCfg (mkst R (getr R 1) M' (seg_rom ASEGS)) model') Kt) ->
  srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 pc0) M (seg_rom ASEGS)) model) Kt.
Proof.
  intros pc0 w Fw Ew Dw R M model LB FF LK cr A Kt INV Hhalt HMI Hret KT0 CONT.
  destruct (art_ri_open MAPS0 RESV0 NOACC0 BASE BUDGET rn LB FF LK cr A M model INV Hhalt HMI) as (G & REPr & FS & B0 & CRED & CLI & KN & LZ & EG).
  set (Mr0 := mrestrict (bhid A model) M) in *.
  pose proof REPr as (ROK & STAT & THR & _). destruct THR as (_ & _ & _ & _ & _ & _ & _ & LSAN0).
  apply (art_wrap_pure2x MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Hwx (art_alloc_rep_frame_law_proved art_fsg MAPS0 RESV0) Kt R (Z_to_bv 64 pc0) M model G LB FF LK cr A (fun _ => False)
           (fun fx' R' pc1 Mr' => fx' = fx /\ pc1 = getr R 1 /\ R' = R) REPr FS B0 CRED CLI KN LZ EG).
  - exists fx, R, (getr R 1), Mr0. split.
    { fold Mr0. eapply mst_step; [reflexivity | | apply mst_refl].
      rewrite (@step_jalr_x0 fx ASEGS R (Z_to_bv 64 pc0) Mr0 (seg_rom ASEGS) w 1%bv 0%bv (getr R 1) Fw Ew Dw eq_refl).
      change (bv_signed (0%bv : bv 12)) with 0. rewrite (Hret : v_jalr (getr R 1) 0 = getr R 1). reflexivity. }
    split; [apply mem_grows_refl|]. split; [intros x _; reflexivity|]. split; [exact LSAN0|]. repeat split.
  - intros x [].
  - intros x [].
  - intros x [].
  - intros b x _ _ [].
  - intros fx2 R' pc1 Mr' M1 model' (Efx & Epc & ER) RI' GROW FRM VIS1 HID RT MI'. subst pc1 fx2 R'.
    apply (CONT M1 model'); [ | exact RT | exact MI' | exact RI']. intros a. apply FRM. intros [].
Qed.
End WCX.
