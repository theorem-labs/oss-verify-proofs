(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatSim StoreOk ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceABx ArtMem ArtRuns ArtRunsMem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatCls_b BatCellEx_b BatDepot_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtBridge. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatInv_b BatInvMalloc_b BatLift_b BatWrapKit_b
     BatFsInv_b BatFsInvLaws_b BatIfaceLaws_b BatWrapC_b BatWrapVis_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Section Wrap2.
Variables MAPS0 RESV0 NOACC0 : list (word * word).
Variables BASE BUDGET : Z.
Variable rn : art_run.
Variable scfg : SpuriousCfg.
Hypothesis Hwx : wx_segs_nowrap ASEGS.
Hypothesis AFL : art_alloc_rep_frame_law art_fsg MAPS0 RESV0.
Context {fx : PropExec.FPState}.

#[local] Abbreviation RI := (art_ri_inv art_fsg MAPS0 RESV0 NOACC0 BASE BUDGET art_fsinv rn).
#[local] Abbreviation BI := (BInv ASEGS MAPS0 RESV0 NOACC0 (rn_HI rn) BASE BUDGET).

#[using="Hwx AFL"] Theorem art_wrap_pure2 : forall (K : ShapeAlg.TSet) (R : bvmap 5 word) (pc0 : word) (M : word -> option byte) (model : Model)
    (G : art_gs art_fsg) (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (FP : Z -> Prop)
    (Q : bvmap 5 word -> word -> (word -> option byte) -> Prop),
  art_alloc_rep art_fsg rn G LB (mrestrict (bhid A model) M) -> art_fsinv rn (g_fs art_fsg G) FF LK M ->
  BI (g_log art_fsg G) A M model -> art_credit_ok art_fsg BUDGET rn G LB cr -> art_client_ok rn LB FF LK A M ->
  art_kn_ok MAPS0 RESV0 rn -> art_lazy_ok art_fsg rn G A (m_vm_lazy model) -> art_eager_ok LB A (m_vm_lazy model) ->
  (exists R' pc1 Mr', msteps ASEGS (mkst R pc0 (mrestrict (bhid A model) M) (seg_rom ASEGS)) (mkst R' pc1 Mr' (seg_rom ASEGS))
                       /\ mem_grows (mrestrict (bhid A model) M) Mr' /\ (forall x : word, ~ FP (U x) -> Mr' x = mrestrict (bhid A model) M x)
                       /\ cellA Mr' (rn_tp rn + rn_loff rn) 4 0 /\ Q R' pc1 Mr') ->
  (forall x, FP x -> art_alloc_zone art_fsg rn G x -> in_block LB x) ->
  (forall x, FP x -> fs_zone3 rn x -> in_fframe FF x) ->
  (forall x, FP x -> ~ cs_zone rn x) ->                                          (* [comment removed for export] *)
  (forall b x, In b LB -> in_shadow_of (fst b) (snd b) x -> ~ FP x) ->
  (forall R' pc1 Mr' M1 model', Q R' pc1 Mr' ->
       RI LB FF LK cr A M1 (vml_of model') -> mem_grows M M1 -> (forall x : word, ~ FP (U x) -> M1 x = M x) ->
       (forall x : word, bhid A model x = false -> M1 x = Mr' x) -> (forall x : word, bhid A model' x = bhid A model x) ->
       model_rt model model' -> MInv A model' ->
       srealizes ASEGS scfg (mkCfg (mkst R' pc1 M1 (seg_rom ASEGS)) model') K) ->
  srealizes ASEGS scfg (mkCfg (mkst R pc0 M (seg_rom ASEGS)) model) K.
Proof.
  intros K R pc0 M model G LB FF LK cr A FP Q REPr FS B0 CRED CLI KN LZ EG RUN FPAZ FPFS FPCS FPSH CONT.
  destruct RUN as (R' & pc1 & Mr' & MS & GRr & FRr & LSAN & HQ).
  apply (bridge_msteps ASEGS scfg Hwx MAPS0 RESV0 NOACC0 (rn_HI rn) BASE BUDGET (g_log art_fsg G) A (mkst R pc0 M (seg_rom ASEGS)) model
           (mkst R' pc1 Mr' (seg_rom ASEGS)) K B0).
  { rewrite restrict_mkst. exact MS. }
  intros ms' model' Est B1 RT BS. destruct (restrict_eq_mkst _ _ _ _ _ _ Est) as (Ems & EMr0). set (M1 := ms_mem ms') in *. rewrite Ems. assert (EMr : mrestrict (bhid A model') M1 = Mr') by (symmetry; exact EMr0).
  change (ms_mem (mkst R pc0 M (seg_rom ASEGS))) with M in BS.
  pose proof (art_bstep_pure_frame A M M1 model model' Mr' BS EMr) as FRAME.
  pose proof (art_bstep_pure_grows A M M1 model model' Mr' BS EMr GRr) as GROW.
  pose proof (art_bstep_pure_hid A M M1 model model' BS) as HID.
  assert (FR1 : forall x : word, ~ FP (U x) -> M1 x = M x) by (intros x Hx; apply FRAME; apply FRr; exact Hx).
  apply (CONT R' pc1 Mr' M1 model' HQ); [ | exact GROW | exact FR1 | | exact HID | exact RT | exact (bi_minv _ _ _ _ _ _ _ _ _ _ _ B1)].
  - exists G. cbn [vml_of fst snd].
    split. { change (mkH (m_vm_lazy model') A) with (bhid A model'). rewrite EMr. apply (AFL rn G LB _ Mr' REPr GRr).
             - intros x Hz Hb. apply FRr. intros HF. apply Hb. exact (FPAZ _ HF Hz).
             - exact LSAN.
             - exact (bi_live _ _ _ _ _ _ _ _ _ _ _ B0).
             - exact KN. }
    split. { apply (art_fsinv_client_proved rn (g_fs art_fsg G) FF LK M M1 FS GROW).
             - intros x a Hz Hn. apply FR1. intros HF. apply Hn. exact (FPFS _ HF Hz).
             - intros x Hz. apply FR1. intros HF. exact (FPCS _ HF Hz). }
    split. { exact (BINV_intro _ _ _ _ _ _ _ _ _ _ _ B1). }
    split; [exact CRED|].
    split. { apply (art_client_ok_frame rn LB FF LK A M M1 CLI GROW). intros b a Hb Ha.
             pose proof CLI as (C1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & CT). destruct (C1 b Hb) as (K1 & _ & _ & K4 & K5 & _).
             assert (Ra : 0 <= a < 2 ^ 64).
             { unfold in_shadow_of, HeapIfaceA.S in Ha. assert (0 <= fst b / 8) by (apply Z.div_pos; lia).
               assert ((fst b + snd b - 1) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia). change (2 ^ 47 / 8) with 17592186044416 in *. unfold HeapIfaceA.SB in *. lia. }
             pose proof (FR1 (Z_to_bv 64 a)) as X. rewrite art_u_lit in X by exact Ra. apply X. exact (FPSH b a Hb Ha). }
    split; [exact KN|].
    split. { apply (art_lazy_ok_shrink art_fsg rn G A (m_vm_lazy model) (m_vm_lazy model') LZ). exact (art_bstep_pure_lazy A M M1 model model' BS). }
    destruct EG as (AW & EB). split; [exact AW|]. intros b x Hb Hx. destruct (page_in_ranges (page_base x) (m_vm_lazy model')) eqn:E; [|reflexivity].
    pose proof (art_bstep_pure_lazy A M M1 model model' BS x E) as E0. rewrite (EB b x Hb Hx) in E0. discriminate E0.
  - intros x Hx. rewrite (art_bstep_pure_mem A M M1 model model' Mr' BS EMr). rewrite Hx. reflexivity.
Qed.

(* [comment removed for export] *)
Definition art_gs_fs (G : art_gs art_fsg) (g : art_fsg) : art_gs art_fsg :=
  GS art_fsg (g_log art_fsg G) (g_inited art_fsg G) (g_cls art_fsg G) (g_st art_fsg G) (g_sec art_fsg G) (g_sec_committed art_fsg G)
     (g_qt art_fsg G) (g_qg art_fsg G) (g_depot art_fsg G) (g_ia art_fsg G) g.

#[using="Type"] Lemma art_client_ok_frames : forall LB FF LK FF' LK' A (M : word -> option byte), art_client_ok rn LB FF LK A M ->
  (forall b, In b LB -> fframes_apart (fst b) (snd b) (FF' ++ LK')) -> art_client_ok rn LB FF' LK' A M.
Proof.
  intros LB FF LK FF' LK' A M (C1 & CT) AP. split; [|exact CT].
  intros b Hb. destruct (C1 b Hb) as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & _ & K12).
  repeat (split; [assumption|]). split; [exact (AP b Hb) | exact K12].
Qed.

#[using="Hwx AFL"] Theorem art_wrap_pure3 : forall (K : ShapeAlg.TSet) (R : bvmap 5 word) (pc0 : word) (M : word -> option byte) (model : Model)
    (G : art_gs art_fsg) (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (FP : Z -> Prop)
    (Q : bvmap 5 word -> word -> (word -> option byte) -> Prop) (g' : art_fsg) (FF' LK' : list fframe),
  art_alloc_rep art_fsg rn G LB (mrestrict (bhid A model) M) -> art_fsinv rn (g_fs art_fsg G) FF LK M ->
  BI (g_log art_fsg G) A M model -> art_credit_ok art_fsg BUDGET rn G LB cr -> art_client_ok rn LB FF LK A M ->
  art_kn_ok MAPS0 RESV0 rn -> art_lazy_ok art_fsg rn G A (m_vm_lazy model) -> art_eager_ok LB A (m_vm_lazy model) ->
  (exists R' pc1 Mr', msteps ASEGS (mkst R pc0 (mrestrict (bhid A model) M) (seg_rom ASEGS)) (mkst R' pc1 Mr' (seg_rom ASEGS))
                       /\ mem_grows (mrestrict (bhid A model) M) Mr' /\ (forall x : word, ~ FP (U x) -> Mr' x = mrestrict (bhid A model) M x)
                       /\ cellA Mr' (rn_tp rn + rn_loff rn) 4 0 /\ Q R' pc1 Mr') ->
  (forall x, FP x -> art_alloc_zone art_fsg rn G x -> in_block LB x) ->
  (forall b x, In b LB -> in_shadow_of (fst b) (snd b) x -> ~ FP x) ->
  (forall R' pc1 Mr' M1, Q R' pc1 Mr' -> mem_grows M M1 -> (forall x : word, ~ FP (U x) -> M1 x = M x) ->
       (forall x : word, bhid A model x = false -> M1 x = Mr' x) ->
       art_fsinv rn g' FF' LK' M1 /\ (forall b, In b LB -> fframes_apart (fst b) (snd b) (FF' ++ LK'))) ->
  (forall R' pc1 Mr' M1 model', Q R' pc1 Mr' ->
       RI LB FF' LK' cr A M1 (vml_of model') -> mem_grows M M1 -> (forall x : word, ~ FP (U x) -> M1 x = M x) ->
       (forall x : word, bhid A model x = false -> M1 x = Mr' x) -> (forall x : word, bhid A model' x = bhid A model x) ->
       model_rt model model' -> MInv A model' ->
       srealizes ASEGS scfg (mkCfg (mkst R' pc1 M1 (seg_rom ASEGS)) model') K) ->
  srealizes ASEGS scfg (mkCfg (mkst R pc0 M (seg_rom ASEGS)) model) K.
Proof.
  intros K R pc0 M model G LB FF LK cr A FP Q g' FF' LK' REPr FS B0 CRED CLI KN LZ EG RUN FPAZ FPSH NEWFS CONT.
  destruct RUN as (R' & pc1 & Mr' & MS & GRr & FRr & LSAN & HQ).
  apply (bridge_msteps ASEGS scfg Hwx MAPS0 RESV0 NOACC0 (rn_HI rn) BASE BUDGET (g_log art_fsg G) A (mkst R pc0 M (seg_rom ASEGS)) model
           (mkst R' pc1 Mr' (seg_rom ASEGS)) K B0).
  { rewrite restrict_mkst. exact MS. }
  intros ms' model' Est B1 RT BS. destruct (restrict_eq_mkst _ _ _ _ _ _ Est) as (Ems & EMr0). set (M1 := ms_mem ms') in *. rewrite Ems. assert (EMr : mrestrict (bhid A model') M1 = Mr') by (symmetry; exact EMr0).
  change (ms_mem (mkst R pc0 M (seg_rom ASEGS))) with M in BS.
  pose proof (art_bstep_pure_frame A M M1 model model' Mr' BS EMr) as FRAME.
  pose proof (art_bstep_pure_grows A M M1 model model' Mr' BS EMr GRr) as GROW.
  pose proof (art_bstep_pure_hid A M M1 model model' BS) as HID.
  assert (FR1 : forall x : word, ~ FP (U x) -> M1 x = M x) by (intros x Hx; apply FRAME; apply FRr; exact Hx).
  assert (VIS1 : forall x : word, bhid A model x = false -> M1 x = Mr' x).
  { intros x Hx. rewrite (art_bstep_pure_mem A M M1 model model' Mr' BS EMr). rewrite Hx. reflexivity. }
  destruct (NEWFS R' pc1 Mr' M1 HQ GROW FR1 VIS1) as (FS' & AP').
  apply (CONT R' pc1 Mr' M1 model' HQ); [ | exact GROW | exact FR1 | exact VIS1 | exact HID | exact RT | exact (bi_minv _ _ _ _ _ _ _ _ _ _ _ B1)].
  exists (art_gs_fs G g'). cbn [vml_of fst snd].
  split. { change (mkH (m_vm_lazy model') A) with (bhid A model'). rewrite EMr. change (art_alloc_rep art_fsg rn G LB Mr'). apply (AFL rn G LB _ Mr' REPr GRr).
           - intros x Hz Hb. apply FRr. intros HF. apply Hb. exact (FPAZ _ HF Hz).
           - exact LSAN.
           - exact (bi_live _ _ _ _ _ _ _ _ _ _ _ B0).
           - exact KN. }
  split. { exact FS'. }
  split. { exact (BINV_intro _ _ _ _ _ _ _ _ _ _ _ B1). }
  split; [exact CRED|].
  split. { apply (art_client_ok_frames LB FF LK FF' LK' A M1); [|exact AP']. apply (art_client_ok_frame rn LB FF LK A M M1 CLI GROW). intros b a Hb Ha.
           pose proof CLI as (C1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & CT). destruct (C1 b Hb) as (K1 & _ & _ & K4 & K5 & _).
           assert (Ra : 0 <= a < 2 ^ 64).
           { unfold in_shadow_of, HeapIfaceA.S in Ha. assert (0 <= fst b / 8) by (apply Z.div_pos; lia).
             assert ((fst b + snd b - 1) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia). change (2 ^ 47 / 8) with 17592186044416 in *. unfold HeapIfaceA.SB in *. lia. }
           pose proof (FR1 (Z_to_bv 64 a)) as X. rewrite art_u_lit in X by exact Ra. apply X. exact (FPSH b a Hb Ha). }
  split; [exact KN|].
  split. { change (art_lazy_ok art_fsg rn G A (m_vm_lazy model')). apply (art_lazy_ok_shrink art_fsg rn G A (m_vm_lazy model) (m_vm_lazy model') LZ). exact (art_bstep_pure_lazy A M M1 model model' BS). }
  destruct EG as (AW & EB). split; [exact AW|]. intros b x Hb Hx. destruct (page_in_ranges (page_base x) (m_vm_lazy model')) eqn:E; [|reflexivity].
  pose proof (art_bstep_pure_lazy A M M1 model model' BS x E) as E0. rewrite (EB b x Hb Hx) in E0. discriminate E0.
Qed.

#[using="Type"] Lemma art_cs_zone_below : forall (G : art_gs art_fsg) LB FF LK (M Mr : word -> option byte) x, art_alloc_rep art_fsg rn G LB Mr -> art_fsinv rn (g_fs art_fsg G) FF LK M -> cs_zone rn x -> x < rn_HI rn.
Proof.
  intros G LB FF LK M Mr x REP FS Z. pose proof REP as (ROK & _). rok_open ROK. geo_open GEO. destruct (fsinv_cs _ _ _ _ _ FS) as ((Q1 & Q2 & Q3) & _).
  unfold cs_zone in Z. change (HeapIfaceA.S 0x10000) with 2147459072 in Z. change (HeapIfaceA.S 0x696000) with 2148314112 in Z.
  assert (D1' : rn_dtls rn + 4096 <= rn_HI rn) by assumption. clear - Z G1 Q1 D1'. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_zone_not_stack_shadow : forall (G : art_gs art_fsg) LB A (M Mr : word -> option byte) model x,
  art_alloc_rep art_fsg rn G LB Mr -> art_kn_ok MAPS0 RESV0 rn -> BI (g_log art_fsg G) A M model -> art_alloc_zone art_fsg rn G x ->
  ~ (HeapIfaceA.S (rn_HI rn) <= x < 0x10007fff8000).
Proof.
  intros G LB A M Mr model x REP KN B0 Z X. pose proof REP as (ROK & _). rok_open ROK. geo_open GEO.
  pose proof (art_live_of_binv MAPS0 RESV0 NOACC0 BASE BUDGET rn _ _ _ _ B0 KN) as LIVE.
  assert (SHI : 2201439137792 <= x < 0x10007fff8000).
  { unfold HeapIfaceA.S, HeapIfaceA.SB in X. assert (0x10007fff8000 / 8 <= rn_HI rn / 8) by (apply Z.div_le_mono; clear - G1; lia). change (0x10007fff8000 / 8) with 2199291686912 in H. clear - X H. lia. }
  assert (SMONO : forall y, y <= rn_HI rn -> HeapIfaceA.S y <= x) by (intros y Hy; pose proof (art_S_mono y (rn_HI rn) Hy); clear - X H; lia).
  unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in Papp. unfold apart in *.
  destruct Z as [Z | [Z | [Z | [Z | [Z | [Z | [Z | [Z | [Z | [Z | [Z | Z]]]]]]]]]]].
  - unfold art_zone_statics in Z. clear - Z SHI. lia.
  - unfold art_zone_thread in Z. clear - Z SHI G10. lia.
  - clear - Z SHI G16. lia.
  - unfold art_zone_kspace in Z. clear - Z SHI Khi. lia.
  - destruct Z as [Z | (p & Hp & Z)]; [clear - Z SHI Papp; lia|]. destruct (LIVE p Hp) as (L1 & L2 & L3 & L4 & _). clear - Z SHI L4. lia.
  - unfold art_zone_depot, dprivD in Z. clear - Z SHI Al2s Abs. lia.
  - destruct Z as [Z | (p & Hp & Z)].
    + pose proof (SMONO (rn_kbase rn + 0x2000011000) ltac:(clear - Kend; lia)). clear - Z H. lia.
    + destruct (LIVE p Hp) as (L1 & L2 & L3 & _). pose proof (SMONO (fst p + snd p) ltac:(clear - L3; lia)). clear - Z H. lia.
  - clear - Z SHI. lia.
  - clear - Z SHI G20. lia.
  - clear - Z SHI G22 Hkey. lia.
  - clear - Z SHI. lia.
  - clear - Z SHI. lia.
Qed.
#[using="Type"] Lemma art_zone_off_fs : forall (G : art_gs art_fsg) LB A (M Mr : word -> option byte) model x,
  art_alloc_rep art_fsg rn G LB Mr -> art_kn_ok MAPS0 RESV0 rn -> BI (g_log art_fsg G) A M model -> art_alloc_zone art_fsg rn G x ->
  ~ (ar_fs (rn_ar rn) <= x < ar_fs (rn_ar rn) + FS_BYTES).
Proof.
  intros G LB A M Mr model x REP KN B0 Z X. pose proof REP as (ROK & _). rok_open ROK. geo_open GEO.
  pose proof (art_live_of_binv MAPS0 RESV0 NOACC0 BASE BUDGET rn _ _ _ _ B0 KN) as LIVE.
  destruct Fapp as (_ & Fap & _). unfold BIGSHADOW_LO, BIGSHADOW_HI in Fap.
  unfold apart, FS_BYTES in *.
  destruct Z as [Z | [Z | [Z | [Z | [Z | [Z | [Z | [Z | [Z | [Z | [Z | Z]]]]]]]]]]].
  - unfold art_zone_statics in Z. clear - Z X Fimg. lia.
  - unfold art_zone_thread in Z. clear - Z X Aft. lia.
  - clear - Z X Afc. lia.
  - unfold art_zone_kspace in Z. clear - Z X Afkb. lia.
  - destruct Z as [Z | (p & Hp & Z)]; [clear - Z X Afp; lia|]. destruct (LIVE p Hp) as (L1 & L2 & L3 & L4 & L5).
    specialize (L5 (ar_fs (rn_ar rn), 11571200) ltac:(unfold art_objs; do 6 right; left; reflexivity)). unfold apart in L5. cbn [fst snd] in L5. clear - Z X L5. lia.
  - unfold art_zone_depot, dprivD in Z. clear - Z X Fimg Afl Afb. lia.
  - assert (SR : 0x7fff8000 <= x < 0x10007fff8000).
    { destruct Z as [Z | (p & Hp & Z)].
      - pose proof (art_S_lo (rn_kbase rn) ltac:(clear - Khi; lia)). assert ((rn_kbase rn + 0x2000011000) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; clear - Kend G2; lia). change (2 ^ 47 / 8) with 17592186044416 in *. unfold HeapIfaceA.S, HeapIfaceA.SB in *. clear - Z H H0. lia.
      - destruct (LIVE p Hp) as (L1 & L2 & L3 & _). pose proof (art_S_lo (fst p) ltac:(clear - L1; lia)). assert ((fst p + snd p) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; clear - L3 G2; lia). change (2 ^ 47 / 8) with 17592186044416 in *. unfold HeapIfaceA.S, HeapIfaceA.SB in *. clear - Z H H0. lia. }
    clear - SR X Fap. lia.
  - clear - Z X Fimg. lia.
  - clear - Z X Fimg Htpd G20. lia.
  - clear - Z X Fimg G21 G22 Hkey. lia.
  - clear - Z X Fimg. lia.
  - clear - Z X Fimg. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_ri_open : forall LB FF LK cr A M model, RI LB FF LK cr A M (vml_of model) -> m_halted model = None -> MInv A model ->
  exists G, art_alloc_rep art_fsg rn G LB (mrestrict (bhid A model) M) /\ art_fsinv rn (g_fs art_fsg G) FF LK M
            /\ BI (g_log art_fsg G) A M model /\ art_credit_ok art_fsg BUDGET rn G LB cr /\ art_client_ok rn LB FF LK A M
            /\ art_kn_ok MAPS0 RESV0 rn /\ art_lazy_ok art_fsg rn G A (m_vm_lazy model) /\ art_eager_ok LB A (m_vm_lazy model).
Proof.
  intros LB FF LK cr A M model (G & REPr & FS & BV & CRED & CLI & KN & LZ & EG) Hh HMI. cbn [vml_of fst snd] in *.
  exists G. split; [exact REPr|]. split; [exact FS|]. split; [exact (BINV_elim _ _ _ _ _ _ _ _ _ _ _ BV Hh HMI)|].
  split; [exact CRED|]. split; [exact CLI|]. split; [exact KN|]. split; [exact LZ | exact EG].
Qed.
End Wrap2.
