(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatSim StoreOk AsanAcct HeapIface HeapIfaceA HeapIfaceABx ArtMem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatLeaf_b BatPoison_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtRuns ArtRunsMem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatCls_b BatFp_b BatDepot_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtBridge. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatInv_b BatLift_b
     BatFsInv_b BatFsInvLaws_b BatIfaceLaws_b BatInvFrame_b BatIfaceFrame_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIfaceABx ShadowRLawsB.      (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Section Release.
Variables MAPS0 RESV0 NOACC0 : list (word * word).
Variables BASE BUDGET : Z.
Variable rn : art_run.
Variable L : asan_layout.
Hypothesis HLsegs : hl_segs L = ASEGS.
Hypothesis HLlo : hl_img_lo L = 0x10000.
Hypothesis HLhi : hl_img_hi L = 0x696000.
Hypothesis HLst : forall a, art_zone_statics a -> hl_rt_static L a.
Hypothesis HLtls : forall a, (rn_tp rn - 88 <= a < rn_tp rn - 80 \/ rn_tsd rn + 8 * rn_key rn <= a < rn_tsd rn + 8 * rn_key rn + 8
                              \/ 0x673cf8 <= a < 0x673d00 \/ 0x673d28 <= a < 0x673d30 \/ rn_tp rn <= a < rn_tp rn + 8
                              \/ rn_tp rn + rn_loff rn <= a < rn_tp rn + rn_loff rn + 4) -> hl_rt_static L a.
Hypothesis HLro : forall a, 0x10000 <= a < 0x139000 -> hl_rt_ro L a.
Hypothesis HLcs : forall a, (0x1392d8 <= a < 0x1392e0 \/ 0x1393a0 <= a < 0x1393b8 \/ rn_tp rn + 8 <= a < rn_tp rn + 16) -> hl_rt_static L a.   (* [comment removed for export] *)

(* [comment removed for export] *)
#[using="HLlo HLhi"] Lemma art_aclientw_not_bshadow : forall (G : art_gs art_fsg) LB FF LK A (M Mr : word -> option byte) a,
  art_alloc_rep art_fsg rn G LB Mr -> art_fsinv rn (g_fs art_fsg G) FF LK M -> art_client_ok rn LB FF LK A M ->
  aclientw L (rn_ar rn) LB FF 0 0 a -> ~ block_shadow LB a.
Proof.
  intros G LB FF LK A M Mr a REP FS CLI CW (b & Hb & SH).
  destruct (art_hi_bounds rn G LB Mr REP) as (HI1 & HI2). destruct (art_fs_facts rn G LB Mr REP) as (F1 & F2 & F3 & F4).
  assert (HIeq : ahl_ceil (rn_ar rn) = rn_HI rn) by reflexivity.
  pose proof CLI as (CB & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CS16). destruct (CB b Hb) as (B1 & B2 & B3 & B4 & B5 & B6 & _ & _ & _ & _ & B11 & _). rewrite HIeq in B5.
  pose proof (art_shadow_of_range (fst b) (snd b) a ltac:(lia) B4 ltac:(lia) SH) as RA.
  unfold aclientw, aclient_g in CW. destruct CW as [(x & Hx & C)|[(C & _)|[(C & _)|[(f & Hf & C & _)|[C|[(f & Hf & C)|(x & _ & [])]]]]]].
  - destruct (CB x Hx) as (_ & _ & _ & _ & _ & (_ & X6 & _) & _). unfold BIGSHADOW_LO, BIGSHADOW_HI in X6. lia.
  - rewrite HIeq in C. lia.
  - rewrite HLlo, HLhi in C. lia.
  - destruct (art_frame_facts rn G FF LK M FS f Hf) as (K1 & K2 & K3). unfold FS_BYTES in *. lia.
  - (* [comment removed for export] *)
    destruct C as (C1 & _). destruct SH as (_ & S2). unfold HeapIfaceA.S in *.
    assert (E8 : 8 * (ahl_ceil (rn_ar rn) / 8) = ahl_ceil (rn_ar rn)).
    { pose proof (Z.div_mod (ar_sptop (rn_ar rn)) 16 ltac:(lia)) as D. rewrite CS16, Z.add_0_r in D.
      assert (E : ar_sptop (rn_ar rn) - 8388608 = (2 * (ar_sptop (rn_ar rn) / 16) - 1048576) * 8) by lia. rewrite E at 1. rewrite Z.div_mul by lia. lia. }
    assert ((fst b + snd b - 1) / 8 < ahl_ceil (rn_ar rn) / 8) by (apply Z.div_lt_upper_bound; [lia|rewrite E8, HIeq; lia]). lia.
  - destruct (art_frame_facts rn G FF LK M FS f Hf) as (K1 & K2 & K3).
    destruct (art_fsinv_wf_proved rn (g_fs art_fsg G) FF LK M FS) as (WF1 & _). destruct (WF1 f Hf) as (_ & _ & Wm & Wc & _).
    assert (AP : fst b + snd b <= ff_addr f \/ ff_addr f + ff_bytes (ff_class f) <= fst b) by (apply B11; apply in_or_app; left; exact Hf).
    assert (E64 : exists q, ff_addr f = 8 * q /\ ff_bytes (ff_class f) = 8 * (ff_bytes (ff_class f) / 8) /\ 0 < ff_bytes (ff_class f) / 8).
    { destruct Wc as [E|[E|[E|[E|[E|[E|[]]]]]]]; rewrite <- E in *.      (* [comment removed for export] *)
      - change (ff_bytes 0) with 64 in *. pose proof (Z.div_mod (ff_addr f) 64 ltac:(lia)) as D. rewrite Wm in D. exists (8 * (ff_addr f / 64)). split; [lia|split; reflexivity].
      - change (ff_bytes 1) with 128 in *. pose proof (Z.div_mod (ff_addr f) 128 ltac:(lia)) as D. rewrite Wm in D. exists (16 * (ff_addr f / 128)). split; [lia|split; reflexivity].
      - change (ff_bytes 2) with 256 in *. pose proof (Z.div_mod (ff_addr f) 256 ltac:(lia)) as D. rewrite Wm in D. exists (32 * (ff_addr f / 256)). split; [lia|split; reflexivity].
      - change (ff_bytes 3) with 512 in *. pose proof (Z.div_mod (ff_addr f) 512 ltac:(lia)) as D. rewrite Wm in D. exists (64 * (ff_addr f / 512)). split; [lia|split; reflexivity].
      - change (ff_bytes 4) with 1024 in *. pose proof (Z.div_mod (ff_addr f) 1024 ltac:(lia)) as D. rewrite Wm in D. exists (128 * (ff_addr f / 1024)). split; [lia|split; reflexivity].
      - change (ff_bytes 5) with 2048 in *. pose proof (Z.div_mod (ff_addr f) 2048 ltac:(lia)) as D. rewrite Wm in D. exists (256 * (ff_addr f / 2048)). split; [lia|split; reflexivity]. }
    destruct E64 as (q & Eq & Eb & Hb8).
    assert (E2' : 8 * ((ff_addr f + ff_bytes (ff_class f)) / 8) = ff_addr f + ff_bytes (ff_class f)).
    { rewrite Eq. rewrite Eb at 1. replace (8 * q + 8 * (ff_bytes (ff_class f) / 8)) with ((q + ff_bytes (ff_class f) / 8) * 8) by lia. rewrite Z.div_mul by lia. lia. }
    assert (C' : HeapIfaceA.S (ff_addr f) <= a < HeapIfaceA.S (ff_addr f + ff_bytes (ff_class f))).
    { destruct C as (C1 & C2). split; [exact C1|]. unfold HeapIfaceA.S in *.
      assert ((ff_addr f + ff_bytes (ff_class f) - 1) / 8 < (ff_addr f + ff_bytes (ff_class f)) / 8) by (apply Z.div_lt_upper_bound; [lia|rewrite E2'; lia]). lia. }
    apply (art_shadow_apart (fst b) (snd b) (ff_addr f) (ff_bytes (ff_class f)) a); [rewrite Eq; rewrite (Z.mul_comm 8 q), Z.div_mul by lia; lia|exact E2'|exact B4|lia|exact SH|exact C'].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_zone_not_fs : forall (G : art_gs art_fsg) LB (Mr : word -> option byte) a, art_alloc_rep art_fsg rn G LB Mr ->
  live_ok MAPS0 RESV0 (rn_HI rn) (art_live (g_log art_fsg G)) -> art_kn_ok MAPS0 RESV0 rn ->
  art_alloc_zone art_fsg rn G a -> ~ (ar_fs (rn_ar rn) <= a < ar_fs (rn_ar rn) + FS_BYTES).
Proof.
  intros G LB Mr a REP LIVEOK KN Z IN. pose proof REP as (ROK & _). rok_open ROK. geo_open GEO. destruct Fapp as (_ & Fap & _). unfold BIGSHADOW_LO, BIGSHADOW_HI in Fap.
  assert (GF : forall p, In p (art_live (g_log art_fsg G)) -> apart (fst p) (snd p) (ar_fs (rn_ar rn)) FS_BYTES /\ 0 < fst p /\ fst p + snd p <= rn_HI rn /\ 0 < snd p).
  { intros p Hp. destruct LIVEOK as (LO & _). destruct (LO p Hp) as (P0 & P1 & _ & _ & P4 & _ & P6). split; [|split; [exact P0|split; [exact P4|exact P1]]].
    destruct (KN (ar_fs (rn_ar rn), FS_BYTES) ltac:(cbn; tauto)) as (q & Hq & Q1 & Q2). specialize (P6 q Hq). cbn [fst snd] in *. unfold apart. lia. }
  assert (SHR : forall y, 0 <= y <= 2 ^ 47 -> 0x7fff8000 <= HeapIfaceA.S y <= 0x10007fff8000).
  { intros y Hy. unfold HeapIfaceA.S, HeapIfaceA.SB. pose proof (Z.div_pos y 8 ltac:(lia) ltac:(lia)). assert (y / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia). lia. }
  destruct Z as [Z|[Z|[Z|[Z|[Z|[Z|[Z|[Z|[Z|[Z|[Z|Z]]]]]]]]]]].
  - unfold art_zone_statics in Z. clear - Z IN Fimg. unfold FS_BYTES in *. lia.
  - destruct Z as (Z & _). clear - Z IN Aft. unfold apart, FS_BYTES in *. lia.
  - clear - Z IN Afc. unfold apart, FS_BYTES in *. lia.
  - unfold art_zone_kspace in Z. clear - Z IN Afkb. unfold apart, FS_BYTES in *. lia.
  - destruct Z as [Z|(p & Hp & Z)]; [clear - Z IN Afp; unfold apart, FS_BYTES in *; lia|]. destruct (GF p Hp) as (AP & _). clear - Z IN AP. unfold apart, FS_BYTES in *. lia.
  - unfold art_zone_depot, dprivD in Z. clear - Z IN Fimg Afl Afb. unfold apart, FS_BYTES in *. lia.
  - destruct Z as [Z|(p & Hp & Z)].
    + pose proof (SHR (rn_kbase rn) ltac:(clear - Khi Kend G2; lia)). pose proof (SHR (rn_kbase rn + 0x2000011000) ltac:(clear - Khi Kend G2; lia)). clear - Z IN Fap H H0. unfold FS_BYTES in *. lia.
    + destruct (GF p Hp) as (_ & P0 & P4 & P1). pose proof (SHR (fst p) ltac:(clear - P0 P1 P4 G2; lia)). pose proof (SHR (fst p + snd p) ltac:(clear - P0 P1 P4 G2; lia)).
      clear - Z IN Fap H H0. unfold FS_BYTES in *. lia.
  - clear - Z IN Fimg. unfold FS_BYTES in *. lia.
  - clear - Z IN Fimg G19 G20 Htpd. unfold FS_BYTES in *. lia.
  - clear - Z IN Fimg G21 G22 Hkey. unfold FS_BYTES in *. lia.
  - clear - Z IN Fimg. unfold FS_BYTES in *. lia.
  - clear - Z IN Fimg. unfold FS_BYTES in *. lia.
Qed.

(* [comment removed for export] *)
Hypothesis HLroi : forall a, hl_rt_ro L a -> 0x10000 <= a < 0x696000.
#[using="HLroi"] Lemma art_aclientw_not_ro : forall (G : art_gs art_fsg) LB FF LK A (M Mr : word -> option byte) a,
  art_alloc_rep art_fsg rn G LB Mr -> art_fsinv rn (g_fs art_fsg G) FF LK M -> art_client_ok rn LB FF LK A M ->
  aclientw L (rn_ar rn) LB FF 0 0 a -> ~ hl_rt_ro L a.
Proof.
  intros G LB FF LK A M Mr a REP FS CLI CW RO. pose proof (HLroi a RO) as IMG.
  destruct (art_hi_bounds rn G LB Mr REP) as (HI1 & HI2). destruct (art_fs_facts rn G LB Mr REP) as (F1 & F2 & F3 & F4).
  assert (HIeq : ahl_ceil (rn_ar rn) = rn_HI rn) by reflexivity. destruct CLI as (CB & _).
  unfold aclientw, aclient_g in CW. destruct CW as [(x & Hx & C)|[(C & _)|[(_ & C)|[(f & Hf & C & _)|[C|[(f & Hf & C)|(x & _ & [])]]]]]].
  - destruct (CB x Hx) as (_ & X2 & _). lia.
  - rewrite HIeq in C. lia.
  - apply C. right. exact RO.
  - destruct (art_frame_facts rn G FF LK M FS f Hf) as (K1 & K2 & K3). unfold FS_BYTES in *. lia.
  - pose proof (art_shadow_of_range (ahl_ceil (rn_ar rn)) (2 ^ 47 - ahl_ceil (rn_ar rn)) a ltac:(rewrite HIeq; lia) ltac:(rewrite HIeq; lia) ltac:(lia) C). lia.
  - destruct (art_frame_facts rn G FF LK M FS f Hf) as (K1 & K2 & K3). pose proof (art_shadow_of_range (ff_addr f) (ff_bytes (ff_class f)) a ltac:(lia) K3 ltac:(unfold FS_BYTES in *; lia) C). lia.
Qed.

#[local] Abbreviation RI := (art_ri_inv art_fsg MAPS0 RESV0 NOACC0 BASE BUDGET art_fsinv rn).

#[using="HLlo HLhi HLst HLtls HLro HLcs"] Theorem art_release_core : forall LB FF LK cr A (M M' : word -> option byte) V F k rs fl,
  RI LB FF LK cr A M V -> In (F, k, rs) FF -> cellA M (F + ff_bytes k - 8) 8 fl ->
  (forall a, 0 <= a < 2 ^ 64 -> a <> fl -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a) \/ (aclientw L (rn_ar rn) LB FF 0 0 a /\ ~ hl_rt_ro L a)) ->
  cellA M' fl 1 0 -> mem_grows M M' ->
  RI LB (ff_remove F FF) LK cr A M' V.
Proof.
  intros LB FF LK cr A M M' V F k rs fl (G & REP & FS & BV & CRED & CLI & KN & LZ & EG) HF CF DIFF C0 MONO.
  pose proof (BINV_live _ _ _ _ _ _ _ _ _ _ _ _ BV) as LIVEOK.
  set (H := mkH (snd V) A) in *. set (Mr := mrestrict H M) in *.
  (* [comment removed for export] *)
  set (fa := fl mod 2 ^ 64). assert (Rfa : 0 <= fa < 2 ^ 64) by (unfold fa; apply Z.mod_pos_bound; lia).
  assert (Efa : Z_to_bv 64 fa = Z_to_bv 64 fl) by (unfold fa; apply art_zb_mod64).
  assert (CFa : cellA M (F + ff_bytes k - 8) 8 fa) by (unfold fa; apply art_cell_norm; exact CF).
  assert (C0a : cellA M' fa 1 0) by (unfold cell in *; rewrite Efa; exact C0).
  assert (DIFFa : forall a, 0 <= a < 2 ^ 64 -> a <> fa -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a) \/ (aclientw L (rn_ar rn) LB FF 0 0 a /\ ~ hl_rt_ro L a)).
  { intros a Ha Ne. apply DIFF; [exact Ha|]. intros E. subst a. apply Ne. unfold fa. symmetry. apply Z.mod_small. exact Ha. }
  (* [comment removed for export] *)
  assert (FLOC : ar_fs (rn_ar rn) <= fa < ar_fs (rn_ar rn) + FS_BYTES).
  { pose proof FS as (GEOF & _ & _ & _ & _ & _ & _ & _ & FR & _). destruct (FR (F, k, rs) ltac:(apply in_or_app; left; exact HF)) as (K1 & (i & (Hi & _) & Ci) & _).
    unfold ff_class, ff_addr in *. cbn [fst snd] in *. destruct GEOF as (_ & G2 & G3 & _). pose proof (art_hi_bounds rn G LB Mr REP) as (_ & HI2).
    pose proof (fs_flag_range (ar_fs (rn_ar rn)) k i ltac:(lia) Hi) as FR1. assert (0 < fs_nfr k) by (apply fs_nfr_pos; lia).
    assert (fs_nfr k <= 16384). { unfold fs_nfr. assert (Ek : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5) by lia. destruct Ek as [Ek|[Ek|[Ek|[Ek|[Ek|Ek]]]]]; rewrite Ek; cbn; lia. }
    assert (E : fa = fs_flag (ar_fs (rn_ar rn)) k i) by (apply (cell8_inj M (F + ff_bytes k - 8)); [exact CFa|exact Ci|exact Rfa|unfold FS_BYTES in *; lia]).
    rewrite E. unfold FS_BYTES in *. lia. }
  (* [comment removed for export] *)
  assert (PV : forall x : word, U x <> fa -> art_private L (rn_ar rn) LB FF (U x) -> M' x = M x).
  { intros x Ne Hp. destruct (DIFFa (U x) (u64_range x) Ne) as [E|(CW & NRO)]; [rewrite Z_to_bv_bv_unsigned in E; exact E|exfalso].
    destruct Hp as [NC|[RO|BS]]; [exact (NC (aclientw_client _ _ _ _ _ _ _ CW))|exact (NRO RO)|].
    exact (art_aclientw_not_bshadow G LB FF LK A M Mr (U x) REP FS CLI CW BS). }
  assert (NFA : forall x : word, ~ (ar_fs (rn_ar rn) <= U x < ar_fs (rn_ar rn) + FS_BYTES) -> U x <> fa) by (intros x NI E; apply NI; rewrite E; exact FLOC).
  exists G.
  split.
  { apply (art_alloc_rep_frame_law_proved art_fsg MAPS0 RESV0 rn G LB Mr (mrestrict H M') REP).
    - intros x Dx. unfold Mr, mrestrict in *. destruct (H x); [exact Dx|apply MONO; exact Dx].
    - intros x Zx NB. unfold Mr, mrestrict. destruct (H x) eqn:E; [reflexivity|]. apply PV.
      + apply NFA. exact (art_zone_not_fs G LB Mr (U x) REP LIVEOK KN Zx).
      + exact (art_priv_zone MAPS0 RESV0 rn L HLlo HLhi HLst HLtls HLro G LB FF LK A M Mr REP FS CLI LIVEOK KN (U x) Zx NB).
    - pose proof REP as (ROK & _ & (_ & _ & _ & _ & _ & _ & _ & C7) & _). rok_open ROK. geo_open GEO.
      apply (art_cell_agree ASEGS Mr (mrestrict H M')); [|clear - Hloff Hloff' G19; lia|cbn; clear - Hloff''; lia|exact C7].
      intros x Hx. unfold Mr, mrestrict. destruct (H x) eqn:E; [reflexivity|]. cbn in Hx. apply PV.
      + apply NFA. clear - Hx Fimg Hloff' Hloff''. unfold FS_BYTES in *. lia.
      + destruct (art_hi_bounds rn G LB Mr REP) as (HI1 & _).
        apply (art_priv_app rn L HLlo HLhi G LB FF LK A M Mr REP FS CLI); [clear - Hx Hloff'' HI1; lia| |right; left; apply HLtls; clear - Hx; lia| |clear - Hx Hloff''; lia].
        * intros (b & Hb & R). destruct CLI as (CB & _). destruct (CB b Hb) as (_ & B2 & _). clear - Hx R B2 Hloff' Hloff''. lia.
        * intros (f & Hf & C & _). destruct (art_frame_facts rn G FF LK M FS f Hf) as (K1 & K2 & K3). clear - Hx C K1 K2 Fimg Hloff' Hloff''. unfold FS_BYTES in *. lia.
    - exact LIVEOK.
    - exact KN. }
  split.
  { apply (art_fsinv_release_fl rn (g_fs art_fsg G) FF LK M M' F k rs fa FS HF CFa Rfa MONO C0a).
    - intros x Ne Z3 NF. apply PV; [exact Ne|]. exact (art_priv_fs3 MAPS0 RESV0 rn L HLlo HLhi HLtls G LB FF LK A M Mr REP FS CLI LIVEOK KN (U x) Z3 NF).
    - intros x Z. apply PV; [apply NFA; exact (art_cs_not_fs rn G LB FF LK M Mr REP FS (U x) Z)|].
      exact (art_priv_cs MAPS0 RESV0 rn L HLlo HLhi HLcs G LB FF LK A M Mr REP FS CLI LIVEOK KN (U x) Z). }
  split.
  { destruct BV as (AW & LO & BF). split; [exact AW|]. split; [exact LO|]. intros model E1 E2 Hh Hm.
    apply (art_binv_mem _ _ _ _ _ _ _ _ _ M M' model (BF model E1 E2 Hh Hm)); [|exact MONO].
    intros x Hx. unfold bhid in Hx. rewrite E2 in Hx. apply PV.
    - apply NFA. pose proof REP as (ROK & _). destruct LZ as (L1 & _). unfold mkH in Hx. apply andb_prop in Hx as [Hl _].
      exact (proj2 (art_lazy_zone_bounds art_fsg rn G (U x) ROK (L1 x Hl))).
    - exact (art_priv_hidden rn L HLlo HLhi G LB FF LK A M Mr (snd V) REP FS CLI LZ EG x Hx). }
  split; [exact CRED|].
  split.
  { destruct (art_hi_bounds rn G LB Mr REP) as (HI1 & HI2). destruct (art_fs_facts rn G LB Mr REP) as (F1 & F2 & F3 & F4).
    assert (HIeq : ahl_ceil (rn_ar rn) = rn_HI rn) by reflexivity.
    destruct CLI as (CB & CREST). split; [|exact CREST]. intros b Hb. destruct (CB b Hb) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & BREST).
    repeat (split; [assumption|]). split; [intros i Hi; apply MONO; exact (B7 i Hi)|]. rewrite HIeq in B5.
    split; [|split; [exact B9|split; [exact B10|split; [|exact BREST]]]].
    - assert (T : forall j v, 0 <= j -> (j < snd b / 8 \/ (j = snd b / 8 /\ snd b mod 8 <> 0)) -> byte_at M (HeapIfaceA.S (fst b) + j) v -> byte_at M' (HeapIfaceA.S (fst b) + j) v).
      { intros j v Hj0 Hj B. pose proof (art_S_blk_hi (fst b) (snd b) j B4 Hj) as H1.
        pose proof (art_S_range47 (fst b) ltac:(clear - B1 B4 B5 HI2; lia)) as H0. pose proof (art_S_range47 (fst b + snd b - 1) ltac:(clear - B1 B4 B5 HI2; lia)) as H2.
        set (a := HeapIfaceA.S (fst b) + j) in *. assert (Ra : 0 <= a < 2 ^ 64) by (clear - Hj0 H0 H1 H2; lia).
        unfold byte_at in *. rewrite (PV (Z_to_bv 64 a)); [exact B| |]; rewrite art_u_lit by exact Ra.
        - intros E. clear - E FLOC F4 Hj0 H0 H1 H2. unfold FS_BYTES in *. lia.
        - right; right. exists b. split; [exact Hb|]. split; [clear - Hj0; lia|exact H1]. }
      apply (shadow_blkR_tby M M' (fst b) (snd b) B4); [intros j Hj0 Hj v Bv; exact (T j v Hj0 Hj Bv)|exact B8].
    - intros f Hf. apply B11. apply in_app_iff in Hf. apply in_app_iff. destruct Hf as [Hf|Hf]; [left; exact (ff_remove_in F FF f Hf)|right; exact Hf]. }
  split; [exact KN|]. split; [exact LZ|exact EG].
Qed.

(* [comment removed for export] *)
#[using="HLsegs HLlo HLhi HLst HLtls HLro HLcs HLroi"] Theorem art_law_release_frame : rt_release_frame L (rn_ar rn) (art_iface art_fsg MAPS0 RESV0 NOACC0 BASE BUDGET art_fsinv rn).
Proof.
  intros LB FF LK cr A M M' V F k rs fl RIH HF CF DIFF C0 MONO. rewrite HLsegs in *.
  apply (art_release_core LB FF LK cr A M M' V F k rs fl RIH HF CF); [|exact C0|exact MONO].
  intros a Ha Ne. destruct (DIFF a Ha Ne) as [E|CW]; [left; exact E|right]. split; [exact CW|].
  destruct RIH as (G & REP & FS & _ & _ & CLI & _). exact (art_aclientw_not_ro G LB FF LK A M _ a REP FS CLI CW).
Qed.
End Release.
