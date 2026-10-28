(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct RefMemcpyLib MemSplit HeapIface HeapIfaceA HeapIfaceABx ArtMem ArtRuns ArtRunsMem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatCls_b BatLeaf_b BatCellEx_b BatImgCell_b BatPoison_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtBridge. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatInv_b BatInvMalloc_b BatLift_b BatWrapKit_b BatFsInv_b BatFsInvLaws_b BatIfaceLaws_b BatInvFrame_b BatIfaceFrame_b Ba0RegionPoisoned_b Ba0TlsGetAddr_b Ba0FakeStackGCC_b Ba0Fsm1Gen_b Ba0FsmRunU_b Ba0FsmRunU05_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import AsanPlanSoundSums.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatWrapC_b BatWrapVis_b BatWrapC2_b BatWrapRng_b BatFsInvLaws2_b BatFsInvLaws3_b BatSmallocSel_b BatSmallocKit_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

(* [comment removed for export] *)
Lemma sm_class_facts : forall k, 0 <= k <= 5 ->      (* [comment removed for export] *)
  fs_nfr k = 2 ^ (14 - k) /\ ff_bytes k = 2 ^ (6 + k) /\ ff_bytes k / 8 = 2 ^ (3 + k) /\ 64 <= ff_bytes k <= 2048 /\ 512 <= fs_nfr k <= 16384 /\ 8 <= 2 ^ (3 + k) <= 256.      (* [comment removed for export] *)
Proof. intros k Hk. assert (E : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5) by lia. destruct E as [->|[->|[->|[->|[->| ->]]]]]; vm_compute; intuition congruence. Qed.
Lemma sm_fl_eq : forall fs c i, gc_fl fs c i = fs_flag fs c i.  Proof. reflexivity. Qed.
Lemma sm_fr_eq : forall fs c i, 0 <= c -> gc_fr fs c i = fs_frame fs c i.
Proof. intros fs c i Hc. unfold gc_fr, fs_frame, ff_bytes. rewrite Z.pow_add_r by lia. change (2 ^ 6) with 64. ring. Qed.
Lemma sm_valid : forall c i, gc_valid c i <-> (0 <= c <= 10 /\ 0 <= i < fs_nfr c).  Proof. intros c i. unfold gc_valid, fs_nfr. tauto. Qed.

Ltac cell_goal H := first [lit_cell H | rewrite <- le1_one; lit_cell H | rewrite <- BatFsInv_b.le1_zero; lit_cell H].

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
Hypothesis Htp : rn_tp rn = 0x673d00.
Variable k : Z.
Variable entry : word.
Hypothesis Hk : 0 <= k <= 5.
Hypothesis RUNU : fsm_run_u k entry.
#[local] Abbreviation RI := (art_ri_inv art_fsg MAPS0 RESV0 NOACC0 BASE BUDGET art_fsinv rn).
Context {fx : PropExec.FPState}.

#[using="Hwx HLsegs HLlo HLhi Htp Hk RUNU"] Theorem art_wrap_smalloc : forall (R : bvmap 5 word) (M : word -> option byte) (model : Model)
    (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (K : ShapeAlg.TSet),
  let sp := U (getr R 2) in
  let ar := rn_ar rn in
  RI LB FF LK cr A M (vml_of model) -> m_halted model = None -> MInv A model ->
  getr R 4 = Z_to_bv 64 (rn_tp rn) -> Hoare.ret_ok (getr R 1) ->
  astack_ok L ar M 512 sp -> ff_room k FF LK -> (forall f, In f FF -> sp + 32 <= ff_rs f) -> K [] ->
  (forall (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (F fl : Z) (LK' : list fframe),
      getr R' 10 = Z_to_bv 64 F -> regs_preserved R R' ->
      ar_fs ar <= F /\ F + ff_bytes k <= ar_fs ar + FS_BYTES /\ F mod ff_bytes k = 0 /\ app_mem F (ff_bytes k) /\ F + ff_bytes k <= ahl_ceil ar ->
      (F + ff_bytes k <= hl_img_lo L \/ hl_img_hi L <= F) ->
      fframes_apart F (ff_bytes k) (FF ++ LK') -> (forall b, In b LB -> F + ff_bytes k <= fst b \/ fst b + snd b <= F) ->
      incl LK' LK -> defined M' F (ff_bytes k) -> cell_is ASEGS M' (F + ff_bytes k - 8) 8 fl ->
      ar_fs ar <= fl < ar_fs ar + FS_BYTES -> ~ aclient L ar LB ((F, k, sp + 32) :: FF) 0 0 fl ->
      (F + ff_bytes k <= fl \/ fl + 1 <= F) -> store_ok ASEGS M' (Z_to_bv 64 fl) 1 = true ->
      shadow_zero M' F (ff_bytes k / 8) -> aheap_pres L ar LB FF sp 512 M M' ->
      model_rt model model' -> MInv A model' -> RI LB ((F, k, sp + 32) :: FF) LK' cr A M' (vml_of model') ->
      srealizes ASEGS scfg (mkCfg (mkst R' (getr R 1) M' (seg_rom ASEGS)) model') K) ->
  srealizes ASEGS scfg (mkCfg (mkst R entry M (seg_rom ASEGS)) model) K.
Proof.
  intros R M model LB FF LK cr A K sp ar INV Hhalt HMI H4 Hret AST ROOM FFP KT0 CONT. subst ar.
  destruct (art_ri_open MAPS0 RESV0 NOACC0 BASE BUDGET rn LB FF LK cr A M model INV Hhalt HMI) as (G & REPr & FS & B0 & CRED & CLI & KN & LZ & EG).
  set (Mr0 := mrestrict (bhid A model) M) in *.
  destruct AST as (S16 & SHI & SLE & STOP & SWR & SDEF). fold sp in S16, SHI, SLE, SWR, SDEF. rewrite HLsegs in SWR.
  assert (HIeq : ahl_ceil (rn_ar rn) = rn_HI rn) by reflexivity. rewrite HIeq in SHI.
  pose proof (art_cli_hi rn LB FF LK A M CLI) as (HI1 & HI2).
  pose proof REPr as (ROK & STAT & THR & _).
  set (fs := ar_fs (rn_ar rn)) in *. set (top := ar_stack_top (rn_ar rn)) in *. set (bot := ar_stack_bottom (rn_ar rn)) in *.
  pose proof CLI as (CB & _ & SAst & SAfs & C5 & C6 & C7 & C8 & C9 & _). fold top in C8, C9. fold bot in C5, C6, C7, C9. fold fs in SAfs. rewrite HIeq in C5, C6, SAst.
  assert (HIdef : rn_HI rn = ar_sptop (rn_ar rn) - 8388608) by reflexivity.
  destruct (sm_class_facts k Hk) as (ENF & EFB & EFB8 & FBR & NFR & SHB).
  (* [comment removed for export] *)
  assert (GEOX : (4096 <= rn_t rn /\ rn_t rn + 4096 <= rn_HI rn /\ (rn_t rn + 4096 <= 0x10000 \/ 0x696000 <= rn_t rn) /\ (rn_t rn + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= rn_t rn))
                 /\ (4096 <= rn_ctx rn /\ rn_ctx rn + 4096 <= rn_HI rn /\ (rn_ctx rn + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= rn_ctx rn))
                 /\ (0x661b28 <= rn_tp rn - 88 /\ rn_tp rn + 8 <= 0x696000 /\ 0x10000 <= rn_tsd rn /\ rn_tsd rn + 1024 <= 0x696000 /\ 0 <= rn_key rn < 128)
                 /\ (4096 <= fs /\ fs + FS_BYTES <= rn_HI rn /\ (fs + FS_BYTES <= 0x7fff7000 \/ 0x10007fff8000 <= fs) /\ (fs + FS_BYTES <= 0x10000 \/ 0x696000 <= fs))
                 /\ (0x10000 <= rn_tp rn + rn_loff rn /\ rn_tp rn + rn_loff rn + 4 <= 0x696000)
                 /\ (4096 <= rn_dtls rn /\ rn_dtls rn + 4096 <= rn_HI rn /\ (rn_dtls rn + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= rn_dtls rn) /\ apart (rn_dtls rn) 4096 fs FS_BYTES
                     /\ (rn_dtls rn + 4096 <= 0x10000 \/ 0x696000 <= rn_dtls rn))
                 /\ ((rn_dtls rn + 4096 <= rn_blk rn \/ rn_blk rn + 8388608 <= rn_dtls rn) /\ (rn_dtls rn + 4096 <= rn_kbase rn \/ rn_kbase rn + 0x2000011000 <= rn_dtls rn) /\ (rn_dtls rn + 4096 <= rn_parr rn \/ rn_parr rn + 8388608 <= rn_dtls rn))).
  { pose proof ROK as ROK'. rok_open ROK'. geo_open GEO. destruct Fapp as (_ & Fap & _). unfold BIGSHADOW_LO, BIGSHADOW_HI in Fap. fold fs in Fap, Fhi, Fimg, Flo.
    destruct D3 as (_ & D3a & _). unfold BIGSHADOW_LO, BIGSHADOW_HI in D3a. fold fs in Adf.
    split; [repeat split; assumption|]. split; [repeat split; assumption|]. split; [repeat split; first [assumption | lia]|]. split; [repeat split; assumption|]. split; [split; assumption|]. split; [repeat split; assumption|].
    unfold apart in Adb, Adk, Adp. change (2 ^ 23) with 8388608 in Adb, Adp. repeat split; assumption. }
  destruct GEOX as ((Gt1 & Gt2 & Gt3 & Gt4) & (Gc1 & Gc2 & Gc3) & (Gp1 & Gp2 & Gs1 & Gs2 & Gk) & (Gf1 & Gf2 & Gf3 & Gf4) & (Gl1 & Gl2) & (Gd1 & Gd2 & Gd3 & Gd4 & Gd5) & (Ld1 & Ld2 & Ld3)).
  unfold apart, FS_BYTES in Gd4. unfold FS_BYTES in Gf2, Gf3, Gf4.
  assert (Gf0 : 0x696000 <= fs) by (clear - Gf1 Gf4; lia).
  assert (Gf2' : fs + 4096 + 32768 + 11 * 2 ^ 20 <= rn_HI rn) by (clear - Gf2; lia).
  assert (Gf3' : fs + 4096 + 32768 + 11 * 2 ^ 20 <= 0x7fff7000 \/ 0x10007fff8000 <= fs) by (clear - Gf3; lia).
  assert (LAZY : forall w : word, page_in_ranges (page_base w) (m_vm_lazy model) = true ->
            0x696000 <= U w /\ U w < rn_HI rn /\ ~ in_block LB (U w) /\ ~ (ar_fs (rn_ar rn) <= U w < ar_fs (rn_ar rn) + FS_BYTES)).
  { intros w Hw. destruct LZ as (L1 & _). destruct (art_lazy_zone_bounds art_fsg rn G (U w) ROK (L1 w Hw)) as (B1 & B2).
    split; [lia|]. split; [exact (proj2 B1)|]. split; [|exact B2]. intros (b & Hb & Hr). rewrite (proj2 EG b w Hb Hr) in Hw. discriminate Hw. }
  assert (VFS : forall x : word, fs <= U x < fs + 11571200 -> bhid A model x = false).
  { intros x Hx. apply (art_vis_byte rn LB A model LAZY). right; right; right. unfold FS_BYTES. exact Hx. }
  assert (VIMG : forall x : word, U x < 0x696000 -> bhid A model x = false).
  { intros x Hx. apply (art_vis_byte rn LB A model LAZY). left. exact Hx. }
  (* [comment removed for export] *)
  set (g := g_fs art_fsg G) in *.
  pose proof FS as (FGEO & WFS & CTP & CT72 & C88 & C96 & CHINT & ND & FRS & FLG & CST). fold fs in WFS, CTP, CT72, C88, C96, CHINT, FRS, FLG.
  destruct (CHINT k ltac:(lia)) as (CHk & Hh). set (h := fg_hint g k) in *. set (gcb := fg_gc g) in *.
  set (Lst := FF ++ LK) in *.
  set (flag := sl_flag fs Lst). set (rs := sl_rs fs Lst).
  set (gsc := (gcb && (sp <=? top))%bool).                                   (* [comment removed for export] *)
  destruct (sl_least_free fs FF LK gsc sp bot k h Hk ROOM) as (j & Hj & FREEj & TAKEN).
  set (pos := (h + j) mod fs_nfr k) in *.
  assert (Hpos : 0 <= pos < fs_nfr k) by (apply Z.mod_pos_bound; lia).
  set (F := gc_fr fs k pos).
  assert (EF : F = fs_frame fs k pos) by (apply sm_fr_eq; lia).
  assert (VP : gc_valid k pos) by (apply sm_valid; split; [lia | exact Hpos]).
  set (colb := sl_colb gsc sp bot).
  set (LK' := List.filter (fun f => negb (colb f)) LK).
  assert (FFNC : forall f, In f FF -> colb f = false).
  { intros f Hf. unfold colb, sl_colb. pose proof (FFP f Hf) as P. assert (E : (ff_rs f - 32 <? sp) = false) by (apply Z.ltb_ge; clear - P; lia). rewrite E. apply andb_false_r. }
  assert (INC' : forall f, In f (FF ++ LK') -> In f Lst).
  { intros f Hf. apply in_app_or in Hf. apply in_or_app. destruct Hf as [Hf | Hf]; [left; exact Hf | right; apply filter_In in Hf; exact (proj1 Hf)]. }
  (* [comment removed for export] *)
  assert (FREE : forall f, In f (FF ++ LK') -> ~ (ff_class f = k /\ ff_addr f = fs_frame fs k pos)).
  { intros f Hf [E1 E2]. pose proof (INC' f Hf) as HfL.
    destruct (sl_find_uniq fs Lst ND k pos f HfL E1 E2) as [T _]. pose proof (sl_cols_frame fs Lst gsc sp bot ND k pos f HfL E1 E2) as EC.
    unfold sl_taken in FREEj. fold pos Lst in FREEj. rewrite T in FREEj. cbn [Z.eqb negb andb] in FREEj. apply negb_false_iff in FREEj. rewrite EC in FREEj. fold colb in FREEj.
    apply in_app_or in Hf. destruct Hf as [Hf | Hf]; [rewrite (FFNC f Hf) in FREEj; discriminate FREEj|].
    apply filter_In in Hf. destruct Hf as [_ Hf]. rewrite FREEj in Hf. discriminate Hf. }
  (* [comment removed for export] *)
  assert (COLEQ : forall c i, fsm_colg gcb sp top bot flag rs c i <-> sl_cols fs Lst gsc sp bot c i = true).
  { intros c i. rewrite sl_cols_true. unfold fsm_colg, gc_col, gsc. fold flag rs. rewrite andb_true_iff, Z.leb_le. clear. tauto. }
  (* [comment removed for export] *)
  assert (W0 : wrA Mr0 (sp - 512) 512).
  { apply (art_stack_wr art_fsg rn G A (m_vm_lazy model) M sp 512 ROK LZ ltac:(clear - SHI; lia) ltac:(clear; lia) ltac:(clear - SLE HI2 HIdef; lia)). exact SWR. }
  assert (HOK : store_ok ASEGS Mr0 (Z_to_bv 64 (sp - 208)) 208 = true).
  { replace (sp - 208) with (sp - 512 + 304) by ring. apply W0; [lia | cbn; lia]. }
  assert (WFSr : wrA Mr0 fs 11571200).
  { apply (proj2 (art_wr_vis (bhid A model) M fs 11571200 ltac:(clear - Gf1; lia) ltac:(clear - Gf2 HI2; lia) ltac:(intros x Hx; apply VFS; exact Hx))). exact WFS. }
  assert (FSV : forall a (n : nat) v, cellA M a n v -> fs <= a -> a + Z.of_nat n <= fs + 11571200 -> cellA Mr0 a n v).
  { intros a n v C A1 A2. apply (proj2 (art_cell_vis (bhid A model) M a n v ltac:(clear - A1 Gf1; lia) ltac:(clear - A2 Gf2 HI2; lia) ltac:(intros x Hx; apply VFS; clear - Hx A1 A2; lia))). exact C. }
  assert (IMGV : forall a (n : nat) v, cellA M a n v -> 0 <= a -> a + Z.of_nat n <= 0x696000 -> cellA Mr0 a n v).
  { intros a n v C A1 A2. apply (proj2 (art_cell_vis (bhid A model) M a n v A1 ltac:(clear - A2; lia) ltac:(intros x Hx; apply VIMG; clear - Hx A2; lia))). exact C. }
  (* [comment removed for export] *)
  destruct STAT as (PC & LAY & TSD & _ & _ & _ & TLSG & S8).
  destruct TSD as (T1 & T2 & T3 & T4 & T5 & _). destruct TLSG as (GOTN & CDTV & CENT).
  destruct THR as (WT & _ & _ & TH8 & TH16 & TH40 & _ & LSAN0). fold top in TH8. fold bot in TH16.
  assert (INITED : cellA Mr0 0x140918 1 1) by conj_find S8.
  assert (GOTTLS : cellA Mr0 0x1393c0 8 0x12a8e4) by conj_find S8.
  assert (VGOT : cellA Mr0 0x137510 8 0x1cf6d8) by conj_find S8.
  assert (VERB : cellA Mr0 0x1cf6d8 4 0) by conj_find S8.
  assert (DTO : cellA Mr0 0x1382c8 8 8) by conj_find S8.
  assert (ITGA : cellA Mr0 0x1d17f1 1 1) by conj_find S8.
  assert (FLGOT : cellA Mr0 0x1374b0 8 0x1d1768) by conj_find LAY.
  assert (G40 : cellA Mr0 0x1374b8 8 0x13d438) by conj_find LAY.
  destruct (art_cell_exists Mr0 (rn_t rn + 48) 8 ltac:(lia) ltac:(cbn; clear - Gt3; lia) ltac:(clear - Gt1; lia) ltac:(cbn; clear - Gt2 HI2; lia)
              ltac:(intros d m Hd Hm; replace (rn_t rn + 48 + d) with (rn_t rn + (48 + d)) by ring; apply WT; [clear - Hd; lia | cbn in Hm; clear - Hd Hm; lia])) as (tbv & Rtb & Ctb).
  destruct (art_cell_exists Mr0 (rn_t rn + 56) 8 ltac:(lia) ltac:(cbn; clear - Gt3; lia) ltac:(clear - Gt1; lia) ltac:(cbn; clear - Gt2 HI2; lia)
              ltac:(intros d m Hd Hm; replace (rn_t rn + 56 + d) with (rn_t rn + (56 + d)) by ring; apply WT; [clear - Hd; lia | cbn in Hm; clear - Hd Hm; lia])) as (tev & Rte & Cte).
  (* [comment removed for export] *)
  assert (G35 : exists g35, 0 <= g35 < 2 ^ 64 /\ cellA Mr0 0x10380 8 g35).
  { destruct (art_rdn_defined_v 8 Mr0 0x10380 ltac:(lia) ltac:(cbn; lia)) as (bs & Rb & Lb).
    { intros x Hx. right. apply (art_rseg_pt ASEGS 8 (Z_to_bv 64 0x10380)); [rewrite art_u_lit by lia; cbn; lia | vm_compute; reflexivity | rewrite art_u_lit by lia; exact Hx]. }
    exists (bytes_le_to_Z bs). split.
    - pose proof (PropExec.bytes_le_to_Z_bound bs) as Bb. pose proof (PropExec.bytes_le_to_Z_nonneg bs) as B0'. rewrite Lb in Bb. split; [exact B0' | exact Bb].
    - unfold cell. rewrite Rb. f_equal. symmetry. apply AsanPlanSoundSums.APSX.word_to_le_bytes_of_bytes_n; [exact Lb | lia]. }
  destruct G35 as (g35 & Rg35 & CG35).
  (* [comment removed for export] *)
  destruct CST as ((Q1 & Q2 & Q3) & _ & _ & _ & CS4 & CS5 & _).
  assert (CS4r : cellA Mr0 (rn_tp rn + 8) 8 (rn_dtls rn)) by (apply (IMGV _ _ _ CS4); [clear - Gp1; lia | cbn; clear - Q1; lia]).
  assert (NLZD : forall x : word, rn_dtls rn <= U x < rn_dtls rn + 4096 -> bhid A model x = false).
  { intros x Hx. apply (art_vis_notlazy A model). destruct (page_in_ranges (page_base x) (m_vm_lazy model)) eqn:E; [|reflexivity]. exfalso.
    destruct LZ as (L1 & _). pose proof (L1 _ E) as Z. unfold art_lazy_zone in Z. change (2 ^ 23) with 8388608 in Z.
    destruct Z as [Z | [Z | [[Z | Z] _]]]; clear - Z Hx Gd3 Ld1 Ld2 Ld3; lia. }
  assert (CS5r : cellA Mr0 (rn_dtls rn + 24) 8 (rn_tp rn)).
  { apply (proj2 (art_cell_vis (bhid A model) M (rn_dtls rn + 24) 8 (rn_tp rn) ltac:(clear - Gd1; lia) ltac:(cbn; clear - Gd2 HI2; lia) ltac:(intros x Hx; apply NLZD; cbn in Hx; clear - Hx; lia))). exact CS5. }
  (* [comment removed for export] *)
  pose proof (gc_shz_facts fs Gf0 ltac:(clear - Gf2 HI2; lia) Gf3') as (ZZ1 & ZZ2 & ZZ3 & ZZ4).
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
    { unfold HeapIfaceA.S. pose proof FGEO as (Gm & _). fold fs in Gm.
      assert (D : fs = 4096 * (fs / 4096)) by (pose proof (Z.div_mod fs 4096 ltac:(lia)) as D; clear - D Gm; lia).
      assert (E8 : fs = 8 * (fs / 8)). { rewrite D at 2. replace (4096 * (fs / 4096)) with (512 * (fs / 4096) * 8) by ring. rewrite Z.div_mul by lia. clear - D. lia. }
      rewrite E8. replace (8 * (fs / 8) + 11571200 - 1) with (7 + (fs / 8 + 1446399) * 8) by ring. replace (8 * (fs / 8) + 11571200) with ((fs / 8 + 1446400) * 8) by ring.
      rewrite Z.div_add, Z.div_mul by lia. change (7 / 8) with 0. ring. }
    rewrite E. clear - Hx. lia. }
  assert (WSHF : wrA Mr0 (HeapIfaceA.S fs) (HeapIfaceA.S (fs + 11571200) - HeapIfaceA.S fs)).
  { pose proof (art_S_lo fs ltac:(clear - Gf1; lia)) as SL. pose proof (art_S_hi (fs + 11571200) ltac:(clear - Gf2 HI2; lia)) as SH.
    apply (art_wr_of_defined ASEGS Mr0); [clear - SL; lia | clear - SH; lia |]. intros x Hx. unfold Mr0, mrestrict. rewrite (VSHF x ltac:(clear - Hx; lia)).
    apply (bi_shdef _ _ _ _ _ _ _ _ _ _ _ B0 x). unfold in_shadow_rw, LSH_LO, LSH_HI, HSH_LO, HSH_HI. destruct Gf3 as [LOW | HIGH].
    - left. pose proof (art_S_mono _ _ LOW) as MM. change (HeapIfaceA.S 2147446784) with 2415881728 in MM. clear - Hx SL MM. lia.
    - right. pose proof (art_S_mono _ _ HIGH) as MM. change (HeapIfaceA.S 17594333495296) with 2201439137792 in MM. clear - Hx SH MM. lia. }
  set (colg := fsm_colg gcb sp top bot flag rs).
  set (gb := (gcb && (top <? sp))%bool).
  set (g' := FSGH (fun c => if c =? k then (h + j + 1) mod 2 ^ 64 else fg_hint g c) gb).
  set (FP := fun x => sp - 208 <= x < sp \/ fsm_fp_u k fs pos F colg x).
  (* [comment removed for export] *)
  assert (SHF : forall c i, gc_valid c i -> HeapIfaceA.S fs <= gc_sh fs c i /\ gc_sh fs c i + 2 ^ (3 + c) <= HeapIfaceA.S (fs + 11571200)).
  { intros c i V. pose proof (gc_sh_range fs c i V) as [S1 S2]. unfold gc_shz_lo, gc_shz_hi in S1, S2.
    pose proof (art_S_mono fs (fs + 4096 + 32768) ltac:(lia)) as MM. unfold HeapIfaceA.S, HeapIfaceA.SB, Ba0RegionPoisoned_b.SB in *.
    replace (fs + 4096 + 32768 + 11 * 2 ^ 20) with (fs + 11571200) in S2 by lia. clear - S1 S2 MM. lia. }
  pose proof (gc_fr_range fs k pos VP) as [FRR1 FRR2]. fold F in FRR1, FRR2. rewrite <- EFB in FRR2.
  pose proof (gc_fl_range fs k pos VP) as FLR.
  assert (FPCL : forall x, fsm_fp_u k fs pos F colg x -> (fs <= x < fs + 11571200) \/ (HeapIfaceA.S fs <= x < HeapIfaceA.S (fs + 11571200))).
  { intros x FPx. unfold fsm_fp_u in FPx. rewrite <- EFB in FPx.
    destruct FPx as [X | [X | [X | [X | [X | [X | (c & i & V & _ & X)]]]]]].
    - left. clear - X Hk. lia.
    - left. clear - X. lia.
    - left. clear - X FLR. lia.
    - left. clear - X FRR1 FRR2 FBR. lia.
    - left. clear - X FRR1 FRR2 FBR. lia.
    - right. destruct (SHF k pos VP) as [S1 S2]. unfold gc_sh in S1, S2. fold F in S1, S2. clear - X S1 S2. lia.
    - destruct X as [X | X]; [left; pose proof (gc_fl_range fs c i V); clear - X H; lia | right; destruct (SHF c i V) as [S1 S2]; unfold gc_insh in X; clear - X S1 S2; lia]. }
  (* [comment removed for export] *)
  assert (COLF : forall c i, gc_valid c i -> colg c i -> exists f, In f LK /\ colb f = true /\ fs_slot fs f i /\ ff_class f = c).
  { intros c i V C. apply COLEQ in C. pose proof (proj1 (sl_cols_true fs Lst gsc sp bot c i) C) as (_ & NZ & _).
    destruct (sl_find fs Lst c i NZ) as (f & Hf & E1 & E2 & _). pose proof (sl_cols_frame fs Lst gsc sp bot ND c i f Hf E1 E2) as EC. rewrite C in EC. fold colb in EC.
    exists f. split; [|split; [symmetry; exact EC | split; [|exact E1]]].
    - apply in_app_or in Hf. destruct Hf as [Hf | Hf]; [rewrite (FFNC f Hf) in EC; discriminate EC | exact Hf].
    - apply sm_valid in V. split; [rewrite E1; exact (proj2 V) | rewrite E1; exact E2]. }
  assert (FPSHx : forall b x, In b LB -> in_shadow_of (fst b) (snd b) x -> ~ FP x).
  { intros b x Hb Hx HF. pose proof (art_block_shadow_below rn LB FF LK A M b x CLI Hb Hx) as B1.
  destruct (CB b Hb) as (K1 & _ & _ & K4 & K5 & _ & _ & _ & _ & _ & _ & K12 & _). fold fs in K12. unfold FS_BYTES in K12.
  pose proof (art_S_lo (fst b) ltac:(clear - K1; lia)) as B2. pose proof Hx as (Hx1 & _).
  destruct HF as [X | X]; [clear - X B1 SHI HI1; lia|].
  destruct (FPCL _ X) as [Y | Y]; [clear - Y Hx1 B1 B2 Gf3; lia|].
  exact (art_shadow_apart (fst b) (snd b) fs 11571200 x (eq_sym FS8) FS8' K4 K12 Hx Y). }
  apply (art_wrap_pure3 MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Hwx (art_alloc_rep_frame_law_proved art_fsg MAPS0 RESV0) K R entry M model G LB FF LK cr A FP
           (fun R' pc1 Mr' => pc1 = getr R 1 /\ getr R' 10 = Z_to_bv 64 F /\ keeps_cs R R' /\ fsm_post_u (fsm_gbf gcb sp top) k Mr0 Mr' (sp - 208) sp sp fs h j pos F colg)
           g' ((F, k, sp + 32) :: FF) LK' REPr FS B0 CRED CLI KN LZ EG).
  - (* [comment removed for export] *)
    assert (CELLS : forall M' : word -> option byte, (forall x : word, U x < sp - 208 \/ sp <= U x -> M' x = Mr0 x) ->
              forall a (n : nat) v, cellA Mr0 a n v -> 0 <= a -> a + Z.of_nat n <= rn_HI rn -> cellA M' a n v).
    { intros M' AG a n v C Ha Hn. apply (BatAllocG_b.cell_agree Mr0 M'); [| exact Ha | clear - Hn HI2; lia | exact C]. intros x Hx. apply AG. left. clear - Hx Hn SHI. lia. }
    #[local] Ltac etr := match goal with |- context [?f (2 ^ 64 - 2048) 6767872] => change (f (2 ^ 64 - 2048) 6767872) with 6765824 end.
    assert (SHOKF : forall c i, gc_valid c i -> store_ok ASEGS Mr0 (Z_to_bv 64 (gc_sh fs c i)) (Z.to_nat (2 ^ (3 + c))) = true).
    { intros c i V. destruct (SHF c i V) as [S1 S2]. pose proof (gc_pow_facts c (proj1 V)) as (_ & _ & P3 & _).
      replace (gc_sh fs c i) with (HeapIfaceA.S fs + (gc_sh fs c i - HeapIfaceA.S fs)) by ring. apply WSHF; [clear - S1; lia | rewrite Z2Nat.id by lia; clear - S2; lia]. }
    destruct (RUNU fx Mr0 (seg_rom ASEGS) (getr R 2) (getr R 1) (getr R 10) sp (rn_tp rn) 1 (2 ^ 64 - 2048) 0x673d20 0x674500 (rn_key rn) (rn_tsd rn) (rn_ctx rn) (rn_t rn) tbv tev
                0x1d1768 0x1cf6d8 0 8 (rn_dtls rn) (rn_tp rn))
      with (fs := fs) (h := h) (j := j) (pos := pos) (ff := F) (top := top) (botth := bot) (g40 := 0x13d438) (g35 := g35) (flag := flag) (rs := rs) (gcb := gcb) (regs := R)
      as (R' & Mr' & RUN & QR10 & QR2 & QR1 & KCS & POST).
    + reflexivity.
    + exact Hret.
    + clear - SHI HI1 SLE HI2 HIdef. lia.
    + exact HOK.
    + rewrite Htp. lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + clear - Gk. lia.
    + clear - Gs1 Gs2 Gk. lia.
    + clear - Gc1 Gc2 HI2. lia.
    + clear - Gt1 Gt2 HI2. lia.
    + split; assumption.
    + lia.
    + lia.
    + lia.
    + rewrite Htp. lia.
    + clear - Gd1 Gd2 HI2. lia.
    + rewrite Htp. lia.
    + (* [comment removed for export] *)
      intros M' AG. pose proof (CELLS M' AG) as CL. unfold tls_cells.
      pose proof (CL _ _ _ INITED ltac:(lia) ltac:(cbn; clear - HI1; lia)) as X1.
      pose proof (CL _ _ _ GOTTLS ltac:(lia) ltac:(cbn; clear - HI1; lia)) as X2.
      assert (X3 : rdn ASEGS M' (Z_to_bv 64 0x1382b8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 1))).
      { rewrite <- art_desc_md. apply art_rdn_none_img; [lia | cbn; lia |]. intros x Hx. cbn in Hx. rewrite AG by (left; clear - Hx SHI HI1; lia).
        rewrite <- (Z_to_bv_bv_unsigned 64 x). apply GOTN. clear - Hx. lia. }
      assert (X4 : rdn ASEGS M' (Z_to_bv 64 (0x1382b8 + 8)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (2 ^ 64 - 2048)))).
      { rewrite <- art_desc_off. apply art_rdn_none_img; [lia | cbn; lia |]. intros x Hx. cbn in Hx. rewrite AG by (left; clear - Hx SHI HI1; lia).
        rewrite <- (Z_to_bv_bv_unsigned 64 x). apply GOTN. clear - Hx. lia. }
      pose proof (CL _ _ _ CDTV ltac:(lia) ltac:(cbn; clear - HI1; lia)) as X5.
      pose proof (CL _ _ _ CENT ltac:(lia) ltac:(cbn; clear - HI1; lia)) as X6.
      pose proof (CL _ _ _ T1 ltac:(lia) ltac:(cbn; clear - HI1; lia)) as X7.
      pose proof (CL _ _ _ T2 ltac:(lia) ltac:(cbn; clear - HI1; lia)) as X8.
      pose proof (CL _ _ _ T3 ltac:(clear - Gp1; lia) ltac:(cbn; clear - Gp2 HI1; lia)) as X9.
      pose proof (CL _ _ _ T4 ltac:(clear - Gs1 Gk; lia) ltac:(cbn; clear - Gs2 Gk HI1; lia)) as X10.
      pose proof (CL _ _ _ T5 ltac:(clear - Gc1; lia) ltac:(cbn; clear - Gc2; lia)) as X11.
      pose proof (CL _ _ _ Ctb ltac:(clear - Gt1; lia) ltac:(cbn; clear - Gt2; lia)) as X12.
      pose proof (CL _ _ _ Cte ltac:(clear - Gt1; lia) ltac:(cbn; clear - Gt2; lia)) as X13.
      pose proof (CL _ _ _ FLGOT ltac:(lia) ltac:(cbn; clear - HI1; lia)) as X14.
      pose proof (CL _ _ _ ITGA ltac:(lia) ltac:(cbn; clear - HI1; lia)) as X15.
      pose proof (CL _ _ _ VGOT ltac:(lia) ltac:(cbn; clear - HI1; lia)) as X16.
      pose proof (CL _ _ _ VERB ltac:(lia) ltac:(cbn; clear - HI1; lia)) as X17.
      pose proof (CL _ _ _ DTO ltac:(lia) ltac:(cbn; clear - HI1; lia)) as X18.
      pose proof (CL _ _ _ CS4r ltac:(clear - Gp1; lia) ltac:(cbn; clear - Q1 HI1; lia)) as X19.
      pose proof (CL _ _ _ CS5r ltac:(clear - Gd1; lia) ltac:(cbn; clear - Gd2; lia)) as X20.
      rewrite Htp in X9, X19, X20 |- *.
      replace (8 + 6765824) with (6765824 + 8) by reflexivity. replace (rn_dtls rn + 16 * 1 + 8) with (rn_dtls rn + 24) by ring.
      change (6765824 - 8) with 6765816. change (6765856 + 8 * 1) with 6765864.
      repeat split; [cell_goal X1 | cell_goal X2 | exact X3 | exact X4 | cell_goal X5 | cell_goal X6 | cell_goal X7 | cell_goal X8 | cell_goal X9 | cell_goal X10 | cell_goal X11
                     | cell_goal X12 | cell_goal X13 | cell_goal X14 | cell_goal X15 | cell_goal X16 | cell_goal X17 | cell_goal X18 | cell_goal X19 | cell_goal X20].
    + clear - Gf1 Gf2 HI2. lia.
    + etr. split; [lia | left; clear - SHI HI1; lia].
    + etr. pose proof (IMGV _ _ _ CTP ltac:(clear - Gp1; lia) ltac:(cbn; clear - Gp2; lia)) as X. rewrite Htp in X. exact X.
    + split; [exact Gf0 | split; [left; clear - Gf2' SHI; lia | clear - Gf2' HI2; lia]].
    + exact Gf3'.
    + left. clear - ZZ4 SHI HI1. lia.
    + exact Hh.
    + rewrite <- ENF. exact Hj.
    + unfold pos. rewrite ENF. reflexivity.
    + reflexivity.
    + pose proof (FSV _ _ _ C96 ltac:(lia) ltac:(cbn; lia)) as X. apply cell_rdn1 in X; [exact X | destruct gcb; lia].
    + exact (FSV _ _ _ C88 ltac:(lia) ltac:(cbn; lia)).
    + exact (FSV _ _ _ CHk ltac:(clear - Hk; lia) ltac:(cbn; clear - Hk; lia)).
    + (* [comment removed for export] *)
      intros c i V. pose proof (gc_fl_range fs c i V) as FR. change (gc_fl fs c i) with (fs_flag fs c i) in FR |- *. apply sm_valid in V. destruct V as [Vc Vi]. destruct (FLG c i Vc Vi) as (b & Cb & B01 & IFF).
      assert (Eb : b = flag c i).
      { unfold flag. destruct (sl_flag_01 fs Lst c i) as [E0 | E1]; rewrite ?E0, ?E1.
        - destruct B01 as [-> | ->]; [reflexivity|]. exfalso. pose proof (proj1 IFF eq_refl) as TK. apply (sl_flag_taken fs Lst c i) in TK. rewrite E0 in TK. discriminate TK.
        - destruct B01 as [-> | ->]; [|reflexivity]. exfalso. pose proof (proj1 (sl_flag_taken fs Lst c i) E1) as TK. apply IFF in TK. discriminate TK. }
      rewrite <- Eb. split; [|destruct B01 as [-> | ->]; lia].
      apply cell_rdn1; [destruct B01 as [-> | ->]; lia|]. apply (FSV _ _ _ Cb); [clear - FR; lia | cbn; clear - FR; lia].
    + (* [comment removed for export] *)
      intros i Hi. pose proof (TAKEN i Hi) as T. unfold sl_taken in T. apply andb_true_iff in T. destruct T as [T1' T2']. rewrite <- ENF. fold Lst in T1', T2'. split.
      * apply negb_true_iff, Z.eqb_neq in T1'. exact T1'.
      * intros C. apply COLEQ in C. rewrite C in T2'. discriminate T2'.
    + (* [comment removed for export] *)
      unfold sl_taken in FREEj. fold pos Lst in FREEj. apply andb_false_iff in FREEj. destruct FREEj as [X | X].
      * left. apply negb_false_iff, Z.eqb_eq in X. exact X.
      * right. apply COLEQ. apply negb_false_iff in X. exact X.
    + (* [comment removed for export] *)
      pose proof (WFSr 0 (Z.to_nat 11571200) ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia)) as X. rewrite Z.add_0_r in X. exact X.
    + (* [comment removed for export] *)
      destruct LAY as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & _). unfold rt_layout_globs.
      repeat split; [lit_cell A1 | lit_cell A2 | lit_cell A3 | lit_cell A4 | lit_cell A5 | lit_cell A6 | lit_cell A7 | lit_cell A8].
    + (* [comment removed for export] *)
      exact (SHOKF k pos VP).
    + (* [comment removed for export] *)
      intros _. clear - C5 C6 C7 C8 C9 SHI HI1. lia.
    + intros _. clear - Gt2 HI2. lia.
    + (* [comment removed for export] *)
      intros _ M' AG. pose proof (CELLS M' AG) as CL.
      pose proof (CL _ _ _ TH40 ltac:(clear - Gt1; lia) ltac:(cbn; clear - Gt2; lia)) as X1.
      pose proof (CL _ _ _ TH8 ltac:(clear - Gt1; lia) ltac:(cbn; clear - Gt2; lia)) as X2.
      pose proof (CL _ _ _ TH16 ltac:(clear - Gt1; lia) ltac:(cbn; clear - Gt2; lia)) as X3.
      pose proof (CL _ _ _ G40 ltac:(lia) ltac:(cbn; clear - HI1; lia)) as X4.
      pose proof (CL _ _ _ CG35 ltac:(lia) ltac:(cbn; clear - HI1; lia)) as X5.
      repeat split; [cell_goal X1 | cell_goal X2 | cell_goal X3 | cell_goal X4 | cell_goal X5].
    + (* [comment removed for export] *)
      intros _ M' AGZ c i V NZ. apply sm_valid in V. destruct V as [Vc Vi].
      destruct (sl_find fs Lst c i NZ) as (f & Hf & E1 & E2 & ERS). fold rs in ERS.
      destruct (FRS f Hf) as (_ & _ & CRS & RSB). pose proof (fs_frame_range fs c i Vc Vi) as FRG. pose proof (ff_bytes_ge64 c ltac:(lia)) as B64.
      rewrite (sm_fr_eq fs c i ltac:(lia)), <- E2, ERS. split; [|clear - RSB; lia].
      apply (BatAllocG_b.cell_agree Mr0 M'); [| clear - FRG E2 Vc Gf1; lia | cbn; clear - FRG E2 Vc B64 Gf2 HI2; lia |].
      * intros x Hx. cbn in Hx. apply AGZ. unfold gc_outz. rewrite E2 in Hx. clear - Hx FRG Vc B64 Gf2 SHI ZZ1. lia.
      * apply (FSV _ _ _ CRS); [clear - FRG E2 Vc; lia | cbn; clear - FRG E2 Vc B64; lia].
    + (* [comment removed for export] *)
      intros c i V (_ & _ & NZ & _). destruct (sl_find fs Lst c i NZ) as (f & Hf & E1 & _). destruct (FRS f Hf) as (KC & _). clear - KC E1. lia.
    + (* [comment removed for export] *)
      intros c i V _. exact (SHOKF c i V).
    + reflexivity.
    + exact H4.
    + reflexivity.
    + reflexivity.
    + (* [comment removed for export] *)
      pose proof POST as (PG & PO & _).
      assert (FRr : forall x : word, ~ FP (U x) -> Mr' x = Mr0 x).
      { intros x Hx. apply PO; [|intros X; apply Hx; right; exact X].
        destruct (Z_lt_dec (U x) (sp - 208)) as [L1|L1]; [left; exact L1|]. destruct (Z_le_dec sp (U x)) as [L2|L2]; [right; exact L2|]. exfalso. apply Hx. left. clear - L1 L2. lia. }
      exists R', (getr R 1), Mr'. split; [exact RUN|]. split; [exact PG|]. split; [exact FRr|]. split.
      { apply (BatAllocG_b.cell_agree Mr0 Mr'); [| clear - Gl1; lia | cbn; clear - Gl2; lia | exact LSAN0]. intros x Hx. cbn in Hx. apply FRr. unfold FP. intros [X | X].
        - clear - X Hx Gl2 SHI HI1. lia.
        - destruct (FPCL _ X) as [Y | Y]; [clear - Y Hx Gl2 Gf0; lia|]. pose proof (art_S_lo fs ltac:(clear - Gf1; lia)) as SL. clear - Y Hx Gl2 SL. lia. }
      split; [reflexivity|]. split; [exact QR10|]. split; [exact KCS | exact POST].
  - (* [comment removed for export] *)
    intros x [Hx | Hx] Z; exfalso.
    + pose proof (art_zone_below MAPS0 RESV0 NOACC0 BASE BUDGET rn G LB A M Mr0 model x REPr KN B0 (or_introl Z)) as ZB. clear - ZB Hx SHI. lia.
    + destruct (FPCL _ Hx) as [Y | Y].
      * apply (art_zone_off_fs MAPS0 RESV0 NOACC0 BASE BUDGET rn G LB A M Mr0 model x REPr KN B0 Z). fold fs. unfold FS_BYTES. exact Y.
      * apply (art_zone_off_fs_shadow MAPS0 RESV0 NOACC0 BASE BUDGET rn G LB A M Mr0 model x REPr KN B0 Z). fold fs. unfold FS_BYTES. exact Y.
  - exact FPSHx.
  - (* [comment removed for export] *)
    intros R' pc1 Mr' M1 (Epc & QR10 & KCS & POST) GROW FR1 VIS1.
    destruct POST as (PG & PO & PH & P96 & PFL & PCF & PRS & PSF & PSH).
    assert (TOM1 : forall a (n : nat) v, cellA Mr' a n v -> fs <= a -> a + Z.of_nat n <= fs + 11571200 -> cellA M1 a n v).
    { intros a n v C A1 A2. apply (BatAllocG_b.cell_agree Mr' M1); [| clear - A1 Gf1; lia | clear - A2 Gf2 HI2; lia | exact C].
      intros x Hx. apply VIS1. apply VFS. clear - Hx A1 A2. lia. }
    split.
    + unfold g'. rewrite EF.
      apply (art_fsinv_alloc_g rn g FF LK M M1 k j colb sp gb FS GROW Hk ltac:(clear - Hj; lia) ltac:(clear - SHI HI1; lia) ltac:(clear - SLE HI2 HIdef; lia) FFNC FREE); fold fs; fold h; fold pos; rewrite <- ?EF.
      * (* [comment removed for export] *)
        intros x Z3 NW. apply FR1. unfold FP. intros [X | X].
        { pose proof (art_fs_zone3_below rn G LB _ (U x) REPr Z3) as ZB. clear - ZB X SHI. lia. }
        assert (NOSH : ~ (HeapIfaceA.S fs <= U x < HeapIfaceA.S (fs + 11571200))).
        { unfold fs_zone3, FS_BYTES in Z3. fold fs in Z3. clear - Z3 SLfs SHfs Gf3 Gt4 Gp2. lia. }
        apply NW. unfold fs_wr. fold fs. rewrite <- EF. unfold fsm_fp_u in X. rewrite <- EFB in X.
        destruct X as [X | [X | [X | [X | [X | [X | (c & i & V & C & X)]]]]]].
        -- left. exact X.
        -- right; left. exact X.
        -- right; right; left. exact X.
        -- do 4 right; left. exact X.
        -- do 5 right. clear - X. lia.
        -- exfalso. apply NOSH. destruct (SHF k pos VP) as [S1 S2]. unfold gc_sh in S1, S2. fold F in S1, S2. clear - X S1 S2. lia.
        -- destruct X as [X | X].
           ++ do 3 right; left. destruct (COLF c i V C) as (f & Hf & CF & SL & EC). exists f, i. rewrite EC. split; [exact Hf | split; [exact CF | split; [exact SL | exact X]]].
           ++ exfalso. apply NOSH. destruct (SHF c i V) as [S1 S2]. unfold gc_insh in X. clear - X S1 S2. lia.
      * (* [comment removed for export] *)
        intros x Zc. apply FR1. unfold FP. pose proof (art_cs_zone_below rn G LB FF LK M Mr0 (U x) REPr FS Zc) as CB1.
        unfold cs_zone in Zc. change (HeapIfaceA.S 0x10000) with 2147459072 in Zc. change (HeapIfaceA.S 0x696000) with 2148314112 in Zc.
        intros [X | X]; [clear - CB1 X SHI; lia|]. destruct (FPCL _ X) as [Y | Y].
        -- clear - Zc Y Gf0 Gf3 Gd4 Q1. lia.
        -- pose proof (art_S_mono _ _ Gf0) as MM. change (HeapIfaceA.S 6905856) with 2148314112 in MM. clear - Zc Y MM SLfs SHfs Gd3 Q1. lia.
      * apply (TOM1 _ 8%nat); [|clear - Hk; lia | cbn; clear - Hk; lia]. unfold cell. rewrite PH. do 2 f_equal. apply art_zb_eq. rewrite Z.mod_mod by lia. reflexivity.
      * apply (TOM1 _ 1%nat); [|lia | cbn; lia]. unfold cell. rewrite P96. unfold fsm_gbf. fold gb. rewrite art_bytes1 by (destruct gb; lia). reflexivity.
      * apply (TOM1 _ 1%nat); [|clear - FLR; change (fs_flag fs k pos) with (gc_fl fs k pos); lia | cbn; change (fs_flag fs k pos) with (gc_fl fs k pos); clear - FLR; lia].
        unfold cell. change (fs_flag fs k pos) with (gc_fl fs k pos). rewrite PFL. rewrite art_bytes1 by lia. reflexivity.
      * intros f i Hf CF SL NE. destruct (FRS f ltac:(apply in_or_app; right; exact Hf)) as (KC & _). destruct SL as [SLi SLa].
        assert (V : gc_valid (ff_class f) i) by (apply sm_valid; split; [clear - KC; lia | exact SLi]).
        assert (C : colg (ff_class f) i).
        { apply COLEQ. rewrite (sl_cols_frame fs Lst gsc sp bot ND (ff_class f) i f ltac:(apply in_or_app; right; exact Hf) eq_refl SLa). exact CF. }
        pose proof (gc_fl_range fs (ff_class f) i V) as FLc.
        apply (TOM1 _ 1%nat); [|change (fs_flag fs (ff_class f) i) with (gc_fl fs (ff_class f) i); clear - FLc; lia | cbn; change (fs_flag fs (ff_class f) i) with (gc_fl fs (ff_class f) i); clear - FLc; lia].
        unfold cell. change (fs_flag fs (ff_class f) i) with (gc_fl fs (ff_class f) i). rewrite (PCF _ _ V C NE). rewrite art_bytes1 by lia. reflexivity.
      * apply (TOM1 _ 8%nat); [exact PRS | clear - FRR1; lia | cbn; clear - FRR2 FBR; lia].
      * apply (TOM1 _ 8%nat); [| clear - FRR1 FBR; lia | cbn; clear - FRR2 FBR; lia]. unfold cell. replace (F + ff_bytes k - 8) with (F + (2 ^ (6 + k) - 8)) by (rewrite EFB; ring). exact PSF.
    + (* [comment removed for export] *)
      intros b Hb f Hf. destruct (CB b Hb) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & K11 & K12 & _). fold fs in K12. unfold FS_BYTES in K12.
      cbn [app] in Hf. destruct Hf as [<- | Hf].
      * unfold ff_addr, ff_class. cbn [fst snd]. clear - K12 FRR1 FRR2. lia.
      * apply K11. apply INC'. exact Hf.
  - (* [comment removed for export] *)
    intros R' pc1 Mr' M1 model' (Epc & QR10 & KCS & POST) RI' GROW FR1 VIS1 HID RT MI'. subst pc1.
    destruct POST as (PG & PO & PH & P96 & PFL & PCF & PRS & PSF & PSH).
    pose proof RI' as (G1 & _ & FS1 & _).
    pose proof (fsinv_frame_in rn _ _ _ _ FS) as FIN.
    assert (FRAP : fframes_apart F (ff_bytes k) (FF ++ LK')).
    { intros f Hf. destruct (fsinv_frames_apart rn _ _ _ _ FS1 (F, k, sp + 32) f ltac:(left; reflexivity) ltac:(right; exact Hf)) as [E | AP].
      - exfalso. apply (FREE f Hf). rewrite <- E. unfold ff_class, ff_addr. cbn [fst snd]. split; [reflexivity | exact EF].
      - unfold apart, ff_addr, ff_class in AP. cbn [fst snd] in AP. unfold ff_addr, ff_class. clear - AP. lia. }
    assert (FR8 : forall c i, 0 <= c <= 10 -> 8 * (gc_fr fs c i / 8) = gc_fr fs c i /\ 8 * ((gc_fr fs c i + 2 ^ (6 + c)) / 8) = gc_fr fs c i + 2 ^ (6 + c)
                                        /\ (gc_fr fs c i + 2 ^ (6 + c)) / 8 = gc_fr fs c i / 8 + 2 ^ (3 + c)).
    { intros c i Hc. pose proof (gc_pow_facts c Hc) as (_ & _ & _ & _ & P5).
      assert (EQ : gc_fr fs c i = (fs / 8 + 4608 + c * 131072 + i * 2 ^ (3 + c)) * 8) by (unfold gc_fr; rewrite P5; rewrite FS8 at 1; ring).
      assert (D8 : gc_fr fs c i / 8 = fs / 8 + 4608 + c * 131072 + i * 2 ^ (3 + c)) by (rewrite EQ; apply Z.div_mul; lia).
      assert (D8' : (gc_fr fs c i + 2 ^ (3 + c) * 8) / 8 = fs / 8 + 4608 + c * 131072 + i * 2 ^ (3 + c) + 2 ^ (3 + c)).
      { replace (gc_fr fs c i + 2 ^ (3 + c) * 8) with ((fs / 8 + 4608 + c * 131072 + i * 2 ^ (3 + c) + 2 ^ (3 + c)) * 8) by (rewrite EQ; ring). apply Z.div_mul. lia. }
      rewrite P5, D8, D8'. split; [rewrite EQ; ring | split; [rewrite EQ; ring | reflexivity]]. }
    destruct (art_fsinv_wf_proved rn _ _ _ _ FS1) as (WF1 & _).
    destruct (WF1 (F, k, sp + 32) ltac:(left; reflexivity)) as (W1a & W1b & W1mod & _ & W1def & _). unfold ff_addr, ff_class in W1a, W1b, W1mod, W1def. cbn [fst snd] in W1a, W1b, W1mod, W1def.
    assert (TOM1 : forall a (n : nat) bs, rdn ASEGS Mr' (Z_to_bv 64 a) n = Some bs -> fs <= a -> a + Z.of_nat n <= fs + 11571200 -> rdn ASEGS M1 (Z_to_bv 64 a) n = Some bs).
    { intros a n bs C A1 A2. rewrite <- C. apply rdn_ext; [rewrite art_u_lit by (clear - A1 A2 Gf1 Gf2 HI2; lia); clear - A2 Gf2 HI2; lia|].
      intros x Hx. rewrite art_u_lit in Hx by (clear - A1 A2 Gf1 Gf2 HI2; lia). apply VIS1. apply VFS. clear - Hx A1 A2. lia. }
    set (fl := fs_flag fs k pos). assert (FLR' : fs + 4096 <= fl < fs + 4096 + 32768) by exact FLR.
    (* [comment removed for export] *)
    assert (SHPC : forall x, fsm_fp_u k fs pos F colg x -> HeapIfaceA.S fs <= x < HeapIfaceA.S (fs + 11571200) ->
              exists b m, 8 * (b / 8) = b /\ 8 * ((b + m) / 8) = b + m /\ HeapIfaceA.S b <= x < HeapIfaceA.S (b + m)
                          /\ (forall f, In f FF -> apart (ff_addr f) (ff_bytes (ff_class f)) b m)).
    { intros x X Y. unfold fsm_fp_u in X. rewrite <- EFB in X.
      assert (NMAP : ~ (fs <= x < fs + 11571200)) by (clear - Y SLfs SHfs Gf3; lia).
      destruct X as [X | [X | [X | [X | [X | [X | (c & i & V & C & X)]]]]]]; try (exfalso; apply NMAP; clear - X Hk FLR FRR1 FRR2 FBR; lia).
      - destruct (FR8 k pos ltac:(clear - Hk; lia)) as (A1 & A2 & A3). fold F in A1, A2, A3.
        exists F, (ff_bytes k). rewrite EFB. split; [exact A1 | split; [exact A2 | split]].
        + unfold HeapIfaceA.S, HeapIfaceA.SB. unfold Ba0RegionPoisoned_b.SB in X. rewrite A3. clear - X. lia.
        + intros f Hf. pose proof (FRAP f ltac:(apply in_or_app; left; exact Hf)) as AP. unfold apart. rewrite <- EFB. clear - AP. lia.
      - destruct X as [X | X]; [exfalso; apply NMAP; pose proof (gc_fl_range fs c i V) as FLc; clear - X FLc; lia|].
        destruct (COLF c i V C) as (f' & Hf' & CF' & (SLi & SLa) & EC). destruct (FR8 c i (proj1 V)) as (A1 & A2 & A3).
        assert (EA : gc_fr fs c i = ff_addr f') by (rewrite SLa, EC; apply sm_fr_eq; exact (proj1 (proj1 V))).
        assert (EB : 2 ^ (6 + c) = ff_bytes (ff_class f')) by (rewrite EC; unfold ff_bytes; rewrite Z.pow_add_r by (clear - V; destruct V; lia); reflexivity).
        exists (ff_addr f'), (ff_bytes (ff_class f')). rewrite <- EA, <- EB. split; [exact A1 | split; [exact A2 | split]].
        + unfold gc_insh, gc_sh in X. unfold HeapIfaceA.S, HeapIfaceA.SB. unfold Ba0RegionPoisoned_b.SB in X. rewrite A3. clear - X. lia.
        + intros f Hf. destruct (fsinv_frames_apart rn _ _ _ _ FS f f' ltac:(apply in_or_app; left; exact Hf) ltac:(apply in_or_app; right; exact Hf')) as [E | AP].
          * exfalso. subst f'. rewrite (FFNC f Hf) in CF'. discriminate CF'.
          * rewrite EA, EB. exact AP. }
    apply (CONT R' M1 model' F fl LK' QR10 (keeps_cs_preserved R R' KCS)).
    + fold fs. unfold FS_BYTES. split; [clear - FRR1; lia|]. split; [clear - FRR2; lia|]. split; [exact W1mod|]. split; [|rewrite HIeq; clear - FRR2 Gf2; lia].
      unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI. clear - FRR1 FRR2 Gf1 Gf2 Gf3 HI2 FBR. lia.
    + rewrite HLlo, HLhi. right. clear - FRR1 Gf0. lia.
    + exact FRAP.
    + intros b Hb. destruct (CB b Hb) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & K12 & _). fold fs in K12. unfold FS_BYTES in K12. clear - K12 FRR1 FRR2. lia.
    + intros f Hf. apply filter_In in Hf. exact (proj1 Hf).
    + exact W1def.
    + unfold cell_is. replace (F + ff_bytes k - 8) with (F + (2 ^ (6 + k) - 8)) by (rewrite EFB; ring). apply TOM1; [exact PSF | clear - FRR1 FBR EFB; lia | cbn; clear - FRR2 FBR EFB; lia].
    + fold fs. unfold FS_BYTES. clear - FLR'. lia.
    + (* [comment removed for export] *)
      assert (NSH : forall y z, 0 <= y -> y + z <= 2 ^ 47 -> 0 < z -> ~ in_shadow_of y z fl).
      { intros y z Hy Hyz Hz (X1 & X2). pose proof (art_S_lo y Hy). pose proof (art_S_hi (y + z - 1) ltac:(lia)). clear - X1 X2 H H0 Gf1 Gf3 FLR'. lia. }
      pose proof (fsinv_frame_in rn _ _ _ _ FS1) as FIN1.
      intros Ha. destruct Ha as [H | [H | [H | [H | [H | [H | H]]]]]]; rewrite ?HLlo, ?HLhi in H.
      * destruct H as (b & Hb & Rb). destruct (CB b Hb) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & K12 & _). fold fs in K12. unfold FS_BYTES in K12. clear - Rb K12 FLR'. lia.
      * rewrite HIeq in H. clear - H Gf2 FLR'. lia.
      * clear - H Gf0 FLR'. lia.
      * destruct H as (f & Hf & R1 & _). destruct (FIN1 f ltac:(apply in_or_app; left; exact Hf)) as (I1 & _). fold fs in I1. clear - R1 I1 FLR'. lia.
      * rewrite HIeq in H. apply (NSH (rn_HI rn) (2 ^ 47 - rn_HI rn) ltac:(clear - HI1; lia) ltac:(lia) ltac:(clear - HI2; lia) H).
      * destruct H as (f & Hf & H). destruct (FIN1 f ltac:(apply in_or_app; left; exact Hf)) as (I1 & I2 & I3). fold fs in I1, I2. unfold FS_BYTES in I2.
        apply (NSH (ff_addr f) (ff_bytes (ff_class f)) ltac:(clear - I1 Gf1; lia) ltac:(clear - I2 Gf2 HI2; lia) I3 H).
      * destruct H as (b & Hb & H). destruct (CB b Hb) as (K1 & _ & _ & K4 & K5 & _). rewrite HIeq in K5. apply (NSH (fst b) (snd b) ltac:(clear - K1; lia) ltac:(clear - K5 HI2; lia) K4 H).
    + right. clear - FLR' FRR1. lia.
    + destruct FS1 as (_ & W1 & _). fold fs in W1. pose proof (W1 (fl - fs) 1%nat ltac:(clear - FLR'; lia) ltac:(unfold FS_BYTES; cbn; clear - FLR'; lia)) as X.
      replace (fs + (fl - fs)) with fl in X by ring. exact X.
    + (* [comment removed for export] *)
      intros jj Hjj. rewrite EFB8 in Hjj. unfold byte_at.
      replace (HeapIfaceA.S F + jj) with (Ba0RegionPoisoned_b.SB + F / 8 + jj) by (unfold HeapIfaceA.S, HeapIfaceA.SB, Ba0RegionPoisoned_b.SB; ring).
      destruct (SHF k pos VP) as [S1 S2]. unfold gc_sh in S1, S2. fold F in S1, S2.
      rewrite VIS1; [exact (PSH jj Hjj)|]. apply VSHF. rewrite art_u_lit by (clear - Hjj S1 S2 SLfs SHfs; lia). clear - Hjj S1 S2. lia.
    + (* [comment removed for export] *)
      split.
      * intros a Ra Ha. apply FR1. rewrite art_u_lit by exact Ra. unfold FP. intros [X | X].
        { apply (art_cls_off_scratch rn LB FF LK A M CLI L HLlo HLhi (g_fs art_fsg G) FS sp 512 a ltac:(clear - SHI; lia) (or_intror Ha)). clear - X. lia. }
        assert (SHR : forall y z, 0 <= y -> y + z <= 2 ^ 47 -> 0 < z -> in_shadow_of y z a -> 0x7fff8000 <= a < 0x10007fff8000).
        { intros y z Hy Hyz Hz (X1 & X2). pose proof (art_S_lo y Hy). pose proof (art_S_hi (y + z - 1) ltac:(lia)). clear - X1 X2 H H0. lia. }
        destruct (FPCL _ X) as [Y | Y].
        -- (* [comment removed for export] *)
           assert (NSHR : ~ (0x7fff8000 <= a < 0x10007fff8000)) by (clear - Y Gf3; lia).
           destruct Ha as [H | [H | [H | [H | [H | [H | H]]]]]]; rewrite ?HLlo, ?HLhi in H.
           ++ destruct H as (b & Hb & Rb). destruct (CB b Hb) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & K12 & _). fold fs in K12. unfold FS_BYTES in K12. clear - Rb K12 Y. lia.
           ++ rewrite HIeq in H. clear - H Gf2 Y. lia.
           ++ clear - H Gf0 Y. lia.
           ++ destruct H as (f & Hf & R1 & R2). destruct (FIN f ltac:(apply in_or_app; left; exact Hf)) as (I1 & _). fold fs in I1.
              pose proof (FRAP f ltac:(apply in_or_app; left; exact Hf)) as AP.
              unfold fsm_fp_u in X. rewrite <- EFB in X.
              destruct X as [X | [X | [X | [X | [X | [X | (c & i & V & C & X)]]]]]]; try (clear - X R1 I1 AP Hk FLR FRR1 FBR; lia).
              ** exfalso. apply NSHR. destruct (SHF k pos VP) as [S1 S2]. unfold gc_sh in S1, S2. fold F in S1, S2. clear - X S1 S2 SLfs SHfs. lia.
              ** destruct X as [X | X]; [pose proof (gc_fl_range fs c i V) as FLc; clear - X R1 I1 FLc; lia|].
                 exfalso. apply NSHR. destruct (SHF c i V) as [S1 S2]. unfold gc_insh in X. clear - X S1 S2 SLfs SHfs. lia.
           ++ rewrite HIeq in H. apply NSHR. apply (SHR (rn_HI rn) (2 ^ 47 - rn_HI rn) ltac:(clear - HI1; lia) ltac:(lia) ltac:(clear - HI2; lia) H).
           ++ destruct H as (f & Hf & H). destruct (FIN f ltac:(apply in_or_app; left; exact Hf)) as (I1 & I2 & I3). fold fs in I1, I2. unfold FS_BYTES in I2.
              apply NSHR. apply (SHR (ff_addr f) (ff_bytes (ff_class f)) ltac:(clear - I1 Gf1; lia) ltac:(clear - I2 Gf2 HI2; lia) I3 H).
           ++ destruct H as (b & Hb & H). destruct (CB b Hb) as (K1 & _ & _ & K4 & K5 & _). rewrite HIeq in K5. apply NSHR. apply (SHR (fst b) (snd b) ltac:(clear - K1; lia) ltac:(clear - K5 HI2; lia) K4 H).
        -- (* [comment removed for export] *)
           assert (INSH : 0x7fff8000 <= a < 0x10007fff8000) by (clear - Y SLfs SHfs; lia).
           destruct (SHPC _ X Y) as (b0 & m0 & A1 & A2 & A3 & A4).
           destruct Ha as [H | [H | [H | [H | [H | [H | H]]]]]]; rewrite ?HLlo, ?HLhi in H.
           ++ destruct H as (b & Hb & Rb). destruct (CB b Hb) as (K1 & _ & _ & _ & _ & (_ & K6 & _) & _). unfold BIGSHADOW_LO, BIGSHADOW_HI in K6. clear - Rb K6 INSH. lia.
           ++ rewrite HIeq in H. clear - H HI1 INSH. lia.
           ++ clear - H INSH. lia.
           ++ destruct H as (f & Hf & R1 & _). destruct (FIN f ltac:(apply in_or_app; left; exact Hf)) as (I1 & I2 & _). fold fs in I1, I2. unfold FS_BYTES in I2. clear - R1 I1 I2 Gf3 INSH. lia.
           ++ rewrite HIeq in H. destruct H as (H1' & _). pose proof (art_S_mono _ _ Gf2) as MM. clear - H1' MM Y. lia.
           ++ destruct H as (f & Hf & H). destruct (FIN f ltac:(apply in_or_app; left; exact Hf)) as (_ & _ & I3).
              exact (art_shadow_apart (ff_addr f) (ff_bytes (ff_class f)) b0 m0 a A1 A2 I3 (A4 f Hf) H A3).
           ++ destruct H as (b & Hb & H). exact (FPSHx b a Hb H (or_intror X)).
      * intros a Ha. apply GROW.
        assert (WM : wrA M (sp - 512) 512) by (intros d m Hd Hm; apply SWR; assumption).
        pose proof (art_wr_wview ASEGS M (sp - 512) 512 ltac:(clear - SHI HI1; lia) ltac:(clear - SLE HI2 HIdef; lia) WM (Z_to_bv 64 a)) as Vw. rewrite art_u_lit in Vw by (clear - Ha SHI HI1 SLE HI2 HIdef; lia). specialize (Vw ltac:(clear - Ha; lia)).
        rewrite art_wview_off in Vw by (rewrite art_u_lit by (clear - Ha SHI HI1 SLE HI2 HIdef; lia); right; clear - Ha SHI HI1; lia). exact Vw.
    + exact RT.
    + exact MI'.
    + exact RI'.
Qed.
End WS.

(* [comment removed for export] *)
Lemma lit_5d814 : Z_to_bv 64 0x5dc2c = (0x5dc2c%bv : word). Proof. apply bv_eq. reflexivity. Qed.
Lemma lit_5d988 : Z_to_bv 64 0x5dda0 = (0x5dda0%bv : word). Proof. apply bv_eq. reflexivity. Qed.
Lemma lit_5db18 : Z_to_bv 64 0x5df30 = (0x5df30%bv : word). Proof. apply bv_eq. reflexivity. Qed.
Lemma lit_5dcc4 : Z_to_bv 64 0x5e0dc = (0x5e0dc%bv : word). Proof. apply bv_eq. reflexivity. Qed.

Theorem art_asmalloc : forall MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg, wx_segs_nowrap ASEGS -> forall L : asan_layout,
  hl_segs L = ASEGS -> hl_img_lo L = 0x10000 -> hl_img_hi L = 0x696000 -> hl_tp L = rn_tp rn -> rn_tp rn = 0x673d00 -> hl_scr_stack_malloc L = 512 ->
  hl_stack_malloc L 0 = 0x5dc2c -> hl_stack_malloc L 1 = 0x5dda0 -> hl_stack_malloc L 3 = 0x5df30 -> hl_stack_malloc L 5 = 0x5e0dc ->
  forall k, In k [0; 1; 3; 5] -> astack_malloc_spec L (rn_ar rn) scfg (art_iface art_fsg MAPS0 RESV0 NOACC0 BASE BUDGET art_fsinv rn) k.      (* [comment removed for export] *)
Proof.
  intros MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Hwx L HLsegs HLlo HLhi HLtp Htp HLscr HL0 HL1 HL3 HL5 k Hk fx R M model LB FF LK cr A K. cbv zeta.
  intros INV Hh HMI H4 Hret AST ROOM FFP KT0 POST. rewrite HLsegs, HLscr in *. rewrite HLtp in H4.
  destruct Hk as [<- | [<- | [<- | [<- | []]]]].
  - rewrite HL0, lit_5d814.
    apply (art_wrap_smalloc MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Hwx L HLsegs HLlo HLhi Htp 0 _ ltac:(lia) fsm_run_u_0 R M model LB FF LK cr A K INV Hh HMI H4 Hret AST ROOM FFP KT0).
    intros R' M' model' F fl LK' E10 RP GEO IMG AP BL INC DEF CFL FLIN NCL FLOUT SOK SZ HP RT MI' RI'. exact (POST R' M' model' F fl LK' E10 RP GEO IMG AP BL INC DEF CFL FLIN NCL FLOUT SOK SZ HP RT MI' RI').
  - rewrite HL1, lit_5d988.
    apply (art_wrap_smalloc MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Hwx L HLsegs HLlo HLhi Htp 1 _ ltac:(lia) fsm_run_u_1 R M model LB FF LK cr A K INV Hh HMI H4 Hret AST ROOM FFP KT0).
    intros R' M' model' F fl LK' E10 RP GEO IMG AP BL INC DEF CFL FLIN NCL FLOUT SOK SZ HP RT MI' RI'. exact (POST R' M' model' F fl LK' E10 RP GEO IMG AP BL INC DEF CFL FLIN NCL FLOUT SOK SZ HP RT MI' RI').
  - rewrite HL3, lit_5db18.
    apply (art_wrap_smalloc MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Hwx L HLsegs HLlo HLhi Htp 3 _ ltac:(lia) fsm_run_u_3 R M model LB FF LK cr A K INV Hh HMI H4 Hret AST ROOM FFP KT0).
    intros R' M' model' F fl LK' E10 RP GEO IMG AP BL INC DEF CFL FLIN NCL FLOUT SOK SZ HP RT MI' RI'. exact (POST R' M' model' F fl LK' E10 RP GEO IMG AP BL INC DEF CFL FLIN NCL FLOUT SOK SZ HP RT MI' RI').
  - rewrite HL5, lit_5dcc4.
    apply (art_wrap_smalloc MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Hwx L HLsegs HLlo HLhi Htp 5 _ ltac:(lia) fsm_run_u_5 R M model LB FF LK cr A K INV Hh HMI H4 Hret AST ROOM FFP KT0).
    intros R' M' model' F fl LK' E10 RP GEO IMG AP BL INC DEF CFL FLIN NCL FLOUT SOK SZ HP RT MI' RI'. exact (POST R' M' model' F fl LK' E10 RP GEO IMG AP BL INC DEF CFL FLIN NCL FLOUT SOK SZ HP RT MI' RI').
Qed.
