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
     BatFsInv_b BatFsInvLaws_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIfaceABx ShadowRLawsB.      (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

(* [comment removed for export] *)
Section Pure.
Variables (A : list (Z * Z)) (M M1 : word -> option byte) (model model' : Model) (Mr' : word -> option byte).
Hypothesis B : bstep A M model A M1 model' 0 0 false.
Hypothesis E : mrestrict (bhid A model') M1 = Mr'.

#[using="M M1 B"] Lemma art_bstep_pure_hid : forall x, bhid A model' x = bhid A model x.
Proof.
  intros x. destruct B as (_ & B2 & B3 & _). destruct (bhid A model' x) eqn:E1.
  - destruct (B2 x E1) as (H & _). symmetry; exact H.
  - destruct (bhid A model x) eqn:E0; [|reflexivity]. exfalso. specialize (B3 x E0 E1). lia.
Qed.
#[using="model' B E"] Lemma art_bstep_pure_mem : forall x, M1 x = if bhid A model x then M x else Mr' x.
Proof.
  intros x. rewrite <- art_bstep_pure_hid. destruct B as (_ & B2 & _). destruct (bhid A model' x) eqn:E1.
  - exact (proj2 (B2 x E1)).
  - rewrite <- E. unfold mrestrict. rewrite E1. reflexivity.
Qed.
#[using="model' B E"] Lemma art_bstep_pure_frame : forall x, Mr' x = mrestrict (bhid A model) M x -> M1 x = M x.
Proof. intros x H. rewrite art_bstep_pure_mem. unfold mrestrict in H. destruct (bhid A model x); [reflexivity | exact H]. Qed.
#[using="model' B E"] Lemma art_bstep_pure_grows : mem_grows (mrestrict (bhid A model) M) Mr' -> mem_grows M M1.
Proof.
  intros G x Hx. rewrite art_bstep_pure_mem. destruct (bhid A model x) eqn:E0; [exact Hx|]. apply G. unfold mrestrict. rewrite E0. exact Hx.
Qed.
#[using="A M M1 B"] Lemma art_bstep_pure_lazy : forall x : word, page_in_ranges (page_base x) (m_vm_lazy model') = true -> page_in_ranges (page_base x) (m_vm_lazy model) = true.
Proof. intros x H. destruct B as (_ & _ & _ & _ & B5). destruct (B5 x H) as [L | (N & _)]; [exact L | discriminate N]. Qed.
End Pure.

(* [comment removed for export] *)
Section Keep.
Variable FSG : Type.

#[using="Type"] Lemma art_lazy_ok_shrink : forall rn (G : art_gs FSG) A lazy lazy', art_lazy_ok FSG rn G A lazy ->
  (forall x : word, page_in_ranges (page_base x) lazy' = true -> page_in_ranges (page_base x) lazy = true) -> art_lazy_ok FSG rn G A lazy'.
Proof.
  intros rn G A lazy lazy' (L1 & L2 & L3 & L4) SH. split; [|split; [|split; [exact L3 | exact L4]]].
  - intros w Hw. apply L1. apply SH. exact Hw.
  - intros w Hw. destruct (L2 w Hw) as [X | [X | X]]; [left; exact X | right; left; exact X | right; right].
    intros x Hx. specialize (X x Hx). destruct (page_in_ranges (page_base x) lazy') eqn:E1; [|reflexivity]. rewrite (SH x E1) in X. discriminate X.
Qed.

#[using="Type"] Lemma art_shadow_blk_frame : forall (M M1 : word -> option byte) u n, 0 <= u -> u mod 8 = 0 -> 0 < n ->
  (forall a, in_shadow_of u n a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> shadow_blk M u n -> shadow_blk M1 u n.
Proof.
  intros M M1 u n Hu H8 Hn AG (SZ & SP). unfold in_shadow_of, HeapIfaceA.S in AG.
  pose proof (Z.div_mod u 8 ltac:(lia)) as DU. rewrite H8, Z.add_0_r in DU.
  pose proof (Z.div_mod n 8 ltac:(lia)) as DN. pose proof (Z.mod_pos_bound n 8 ltac:(lia)) as RN.
  assert (HI : forall j, 0 <= j -> 8 * j + 1 <= n -> u / 8 + j <= (u + n - 1) / 8).
  { intros j Hj Hjn. apply Z.div_le_lower_bound; lia. }
  split.
  - intros j Hj. unfold byte_at. rewrite AG; [exact (SZ j Hj)|]. unfold HeapIfaceA.S. specialize (HI j ltac:(lia) ltac:(lia)). lia.
  - intros Hm. unfold byte_at. rewrite AG; [exact (SP Hm)|]. unfold HeapIfaceA.S. specialize (HI (n / 8) ltac:(apply Z.div_pos; lia) ltac:(lia)). lia.
Qed.

#[using="Type"] Lemma art_client_ok_frame : forall rn LB FF LK A (M M1 : word -> option byte), art_client_ok rn LB FF LK A M -> mem_grows M M1 ->
  (forall b a, In b LB -> in_shadow_of (fst b) (snd b) a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> art_client_ok rn LB FF LK A M1.
Proof.
  intros rn LB FF LK A M M1 (C1 & CR) GR AG. split; [|exact CR].
  intros b Hb. destruct (C1 b Hb) as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9).
  split; [exact K1|]. split; [exact K2|]. split; [exact K3|]. split; [exact K4|]. split; [exact K5|]. split; [exact K6|].
  split. { intros i Hi. apply GR. exact (K7 i Hi). }
  split; [|exact K9]. apply (shadow_blkR_frame M M1 (fst b) (snd b)); [lia | | lia | intros a Ha; exact (AG b a Hb Ha) | exact K8].
  pose proof (Z.div_mod (fst b) 16 ltac:(lia)) as D. rewrite K3, Z.add_0_r in D. rewrite D. replace (16 * (fst b / 16)) with ((2 * (fst b / 16)) * 8) by ring. apply Z_mod_mult.
Qed.
End Keep.

(* [comment removed for export] *)
Section Wrap.
Variables MAPS0 RESV0 NOACC0 : list (word * word).
Variables BASE BUDGET : Z.
Variable rn : art_run.
Variable scfg : SpuriousCfg.
Hypothesis Hwx : wx_segs_nowrap ASEGS.
Context {fx : PropExec.FPState}.

(* [comment removed for export] *)
Definition art_alloc_zone' (G : art_gs art_fsg) (x : Z) : Prop :=
  art_alloc_zone art_fsg rn G x \/ (rn_tp rn - 88 <= x < rn_tp rn - 80) \/ (rn_tsd rn + 8 * rn_key rn <= x < rn_tsd rn + 8 * rn_key rn + 8).
Definition art_alloc_rep_frame_law' : Prop :=
  forall G LB M M', art_alloc_rep art_fsg rn G LB M -> mem_grows M M' ->
    (forall x : word, art_alloc_zone' G (U x) -> ~ in_block LB (U x) -> M' x = M x) -> cellA M' (rn_tp rn + rn_loff rn) 4 0 -> art_alloc_rep art_fsg rn G LB M'.
Hypothesis AFL : art_alloc_rep_frame_law'.

#[local] Abbreviation RI := (art_ri_inv art_fsg MAPS0 RESV0 NOACC0 BASE BUDGET art_fsinv rn).
#[local] Abbreviation BI := (BInv ASEGS MAPS0 RESV0 NOACC0 (rn_HI rn) BASE BUDGET).

#[using="Hwx AFL"] Theorem art_wrap_pure : forall (K : ShapeAlg.TSet) (R : bvmap 5 word) (pc0 : word) (M : word -> option byte) (model : Model)
    (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (FP : Z -> Prop)
    (Q : bvmap 5 word -> word -> (word -> option byte) -> Prop),
  RI LB FF LK cr A M (vml_of model) -> m_halted model = None -> MInv A model ->
  (forall G, art_alloc_rep art_fsg rn G LB (mrestrict (bhid A model) M) -> art_fsinv rn (g_fs art_fsg G) FF LK M -> art_client_ok rn LB FF LK A M ->
        art_kn_ok MAPS0 RESV0 rn -> art_lazy_ok art_fsg rn G A (m_vm_lazy model) -> BI (g_log art_fsg G) A M model ->
     (exists R' pc1 Mr', msteps ASEGS (mkst R pc0 (mrestrict (bhid A model) M) (seg_rom ASEGS)) (mkst R' pc1 Mr' (seg_rom ASEGS))
                          /\ mem_grows (mrestrict (bhid A model) M) Mr' /\ (forall x : word, ~ FP (U x) -> Mr' x = mrestrict (bhid A model) M x)
                          /\ cellA Mr' (rn_tp rn + rn_loff rn) 4 0 /\ Q R' pc1 Mr')
     /\ (forall x, FP x -> art_alloc_zone' G x -> in_block LB x)) ->
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
  intros K R pc0 M model LB FF LK cr A FP Q INV Hhalt HMI RUN FPFS FPCS FPSH CONT.
  destruct INV as (G & REPr & FS & BV & CRED & CLI & KN & LZ & EG). cbn [vml_of fst snd] in REPr, BV, LZ, EG.
  pose proof (BINV_elim _ _ _ _ _ _ _ _ _ _ _ BV Hhalt HMI) as B0.
  change (mkH (m_vm_lazy model) A) with (bhid A model) in REPr.
  destruct (RUN G REPr FS CLI KN LZ B0) as ((R' & pc1 & Mr' & MS & GRr & FRr & LSAN & HQ) & FPAZ).
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
    split. { change (mkH (m_vm_lazy model') A) with (bhid A model'). rewrite EMr. apply (AFL G LB _ Mr' REPr GRr).
             - intros x Hz Hb. apply FRr. intros HF. apply Hb. exact (FPAZ _ HF Hz).
             - exact LSAN. }
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
    (* [comment removed for export] *)
    destruct EG as (AW & EB). split; [exact AW|]. intros b x Hb Hx. destruct (page_in_ranges (page_base x) (m_vm_lazy model')) eqn:E; [|reflexivity].
    pose proof (art_bstep_pure_lazy A M M1 model model' BS x E) as E0. rewrite (EB b x Hb Hx) in E0. discriminate E0.
  - intros x Hx. rewrite (art_bstep_pure_mem A M M1 model model' Mr' BS EMr). rewrite Hx. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_zone_below : forall (G : art_gs art_fsg) LB A (M Mr : word -> option byte) model x,
  art_alloc_rep art_fsg rn G LB Mr -> art_kn_ok MAPS0 RESV0 rn -> BI (g_log art_fsg G) A M model -> art_alloc_zone' G x -> x < rn_HI rn.
Proof.
  intros G LB A M Mr model x REP KN B0 Z. pose proof REP as (ROK & _). rok_open ROK. geo_open GEO.
  pose proof (art_live_of_binv MAPS0 RESV0 NOACC0 BASE BUDGET rn _ _ _ _ B0 KN) as LIVE.
  assert (SHB : forall y, 0 <= y <= 2 ^ 47 -> HeapIfaceA.S y + 1 < rn_HI rn).
  { intros y Hy. unfold HeapIfaceA.S, HeapIfaceA.SB. assert (y / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia). change (2 ^ 47 / 8) with 17592186044416 in *. lia. }
  destruct Z as [Z | [Z | Z]]; [|lia|lia].
  destruct Z as [Z | [Z | [Z | [Z | [Z | [Z | [Z | Z]]]]]]].
  - unfold art_zone_statics in Z. lia.
  - unfold art_zone_thread in Z. lia.
  - lia.
  - unfold art_zone_kspace in Z. lia.
  - destruct Z as [Z | (p & Hp & Z)]; [lia|]. destruct (LIVE p Hp) as (L1 & L2 & L3 & _). lia.
  - unfold art_zone_depot, dprivD in Z. lia.
  - destruct Z as [Z | (p & Hp & Z)].
    + pose proof (SHB (rn_kbase rn + 0x2000011000) ltac:(lia)). lia.
    + destruct (LIVE p Hp) as (L1 & L2 & L3 & _). pose proof (SHB (fst p + snd p) ltac:(lia)). lia.
  - lia.
Qed.
#[using="Type"] Lemma art_fs_zone3_below : forall (G : art_gs art_fsg) LB (Mr : word -> option byte) x, art_alloc_rep art_fsg rn G LB Mr -> fs_zone3 rn x -> x < rn_HI rn.
Proof.
  intros G LB Mr x REP Z. pose proof REP as (ROK & _). rok_open ROK. geo_open GEO. unfold fs_zone3, FS_BYTES in *. lia.
Qed.
#[using="Type"] Lemma art_block_shadow_below : forall LB FF LK A (M : word -> option byte) b x, art_client_ok rn LB FF LK A M -> In b LB -> in_shadow_of (fst b) (snd b) x -> x < 0x10007fff8000.
Proof.
  intros LB FF LK A M b x CLI Hb Hx. pose proof CLI as (C1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & CT). destruct (C1 b Hb) as (K1 & _ & _ & K4 & K5 & _).
  unfold in_shadow_of, HeapIfaceA.S, HeapIfaceA.SB in Hx. assert ((fst b + snd b - 1) / 8 <= (2 ^ 47 - 8388609) / 8) by (apply Z.div_le_mono; lia). change ((2 ^ 47 - 8388609) / 8) with 17592184995839 in *. lia.
Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma art_lsan_kept : forall (G : art_gs art_fsg) LB (Mr0 Mr' : word -> option byte) (FP : Z -> Prop),
  art_alloc_rep art_fsg rn G LB Mr0 -> (forall x : word, ~ FP (U x) -> Mr' x = Mr0 x) -> (forall x, FP x -> rn_HI rn <= x) -> cellA Mr' (rn_tp rn + rn_loff rn) 4 0.
Proof.
  intros G LB Mr0 Mr' FP REP FR HIFP. pose proof REP as (ROK & _ & (_ & _ & _ & _ & _ & _ & _ & C) & _). rok_open ROK. geo_open GEO.
  apply (BatAllocG_b.cell_agree Mr0 Mr'); [|lia|cbn; lia|exact C]. intros x Hx. apply FR. intros HF. specialize (HIFP _ HF). cbn in Hx. lia.
Qed.
End Wrap.
