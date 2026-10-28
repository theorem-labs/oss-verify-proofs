(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatSim StoreOk ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA ArtMem ArtRuns ArtRunsMem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatCls_b BatCellEx_b BatDepot_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtBridge. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatInv_b BatInvMalloc_b BatLift_b BatWrapKit_b
     BatFsInv_b BatFsInvLaws_b BatIfaceLaws_b BatWrapC_b BatWrapVis_b BatWrapC2_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIfaceABx ShadowRLawsB. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatInvFrameS_b BatWrapFreeA_b BatAnnotate_b BatAnnotateU_b BatAnnotateU2_b BatPoison_b BatWrapRng_b BatAllocG_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import RefMemcpyLib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

(* [comment removed for export] *)
Lemma art_ann_lb_uniq : forall (LB : list (Z * Z)) b b', NoDup (map fst LB) -> In b LB -> In b' LB -> fst b = fst b' -> b = b'.
Proof.
  induction LB as [|x LB IH]; intros b b' ND Hb Hb' E; [destruct Hb|]. cbn [map] in ND. inversion ND as [|? ? NI ND']; subst.
  destruct Hb as [<-|Hb]; destruct Hb' as [<-|Hb']; [reflexivity| | |exact (IH b b' ND' Hb Hb' E)].
  - exfalso. apply NI. apply list_elem_of_In. rewrite E. apply in_map. exact Hb'.
  - exfalso. apply NI. apply list_elem_of_In. rewrite <- E. apply in_map. exact Hb.
Qed.

#[using="Type"] Lemma art_client_ok_frame_sh : forall rn LB FF LK A (M M1 : word -> option byte) b0 c0, art_client_ok rn LB FF LK A M -> mem_grows M M1 ->
  In (b0, c0) LB ->
  (forall b a, In b LB -> fst b <> b0 -> in_shadow_of (fst b) (snd b) a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
  HAJ.shadow_blkR M1 b0 c0 -> art_client_ok rn LB FF LK A M1.
Proof.
  intros rn LB FF LK A M M1 b0 c0 (C1 & CR) GR HB0 AG SB. split; [|exact CR].
  intros b Hb. destruct (C1 b Hb) as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9).
  split; [exact K1|]. split; [exact K2|]. split; [exact K3|]. split; [exact K4|]. split; [exact K5|]. split; [exact K6|].
  split. { intros i Hi. apply GR. exact (K7 i Hi). }
  split; [|exact K9].
  destruct (Z.eq_dec (fst b) b0) as [E|N].
  - pose proof CR as (ND & _). rewrite (art_ann_lb_uniq LB b (b0, c0) ND Hb HB0 E). exact SB.
  - apply (shadow_blkR_frame M M1 (fst b) (snd b)); [lia | | lia | intros a Ha; exact (AG b a Hb N Ha) | exact K8].
    pose proof (Z.div_mod (fst b) 16 ltac:(lia)) as D. rewrite K3, Z.add_0_r in D. rewrite D. replace (16 * (fst b / 16)) with ((2 * (fst b / 16)) * 8) by ring. apply Z_mod_mult.
Qed.

(* [comment removed for export] *)
Section WrapS.
Variables MAPS0 RESV0 NOACC0 : list (word * word).
Variables BASE BUDGET : Z.
Variable rn : art_run.
Variable scfg : SpuriousCfg.
Hypothesis Hwx : wx_segs_nowrap ASEGS.
Context {fx : PropExec.FPState}.

#[local] Abbreviation RI := (art_ri_inv art_fsg MAPS0 RESV0 NOACC0 BASE BUDGET art_fsinv rn).
#[local] Abbreviation BI := (BInv ASEGS MAPS0 RESV0 NOACC0 (rn_HI rn) BASE BUDGET).

#[using="Hwx"] Theorem art_wrap_pure2sh : forall (K : ShapeAlg.TSet) (R : bvmap 5 word) (pc0 : word) (M : word -> option byte) (model : Model)
    (G : art_gs art_fsg) (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (FP : Z -> Prop) (b0 c0 : Z)
    (Q : bvmap 5 word -> word -> (word -> option byte) -> Prop),
  art_alloc_rep art_fsg rn G LB (mrestrict (bhid A model) M) -> art_fsinv rn (g_fs art_fsg G) FF LK M ->
  BI (g_log art_fsg G) A M model -> art_credit_ok art_fsg BUDGET rn G LB cr -> art_client_ok rn LB FF LK A M ->
  art_kn_ok MAPS0 RESV0 rn -> art_lazy_ok art_fsg rn G A (m_vm_lazy model) -> art_eager_ok LB A (m_vm_lazy model) ->
  In (b0, c0) LB -> b0 mod 16 = 0 -> 0 < c0 ->
  (exists R' pc1 Mr', msteps ASEGS (mkst R pc0 (mrestrict (bhid A model) M) (seg_rom ASEGS)) (mkst R' pc1 Mr' (seg_rom ASEGS))
                       /\ mem_grows (mrestrict (bhid A model) M) Mr' /\ (forall x : word, ~ FP (U x) -> Mr' x = mrestrict (bhid A model) M x)
                       /\ cellA Mr' (rn_tp rn + rn_loff rn) 4 0 /\ HAJ.shadow_blkR Mr' b0 c0 /\ Q R' pc1 Mr') ->
  (forall x, FP x -> art_alloc_zone art_fsg rn G x -> in_block LB x \/ in_shadow_of b0 c0 x) ->
  (forall x, FP x -> fs_zone3 rn x -> in_fframe FF x) ->
  (forall x, FP x -> ~ cs_zone rn x) ->
  (forall b x, In b LB -> fst b <> b0 -> in_shadow_of (fst b) (snd b) x -> ~ FP x) ->
  (forall R' pc1 Mr' M1 model', Q R' pc1 Mr' ->
       RI LB FF LK cr A M1 (vml_of model') -> mem_grows M M1 -> (forall x : word, ~ FP (U x) -> M1 x = M x) ->
       (forall x : word, bhid A model x = false -> M1 x = Mr' x) -> (forall x : word, bhid A model' x = bhid A model x) ->
       model_rt model model' -> MInv A model' ->
       srealizes ASEGS scfg (mkCfg (mkst R' pc1 M1 (seg_rom ASEGS)) model') K) ->
  srealizes ASEGS scfg (mkCfg (mkst R pc0 M (seg_rom ASEGS)) model) K.
Proof.
  intros K R pc0 M model G LB FF LK cr A FP b0 c0 Q REPr FS B0 CRED CLI KN LZ EG HB0 Hb0a Hb0n RUN FPAZ FPFS FPCS FPSH CONT.
  destruct RUN as (R' & pc1 & Mr' & MS & GRr & FRr & LSAN & SHr & HQ).
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
  pose proof CLI as (C1 & _). destruct (C1 (b0, c0) HB0) as (K1 & _ & K3 & K4 & K5 & _ & _ & _ & K9 & _). cbn [fst snd] in *.
  assert (SH1 : HAJ.shadow_blkR M1 b0 c0).
  { apply (shadow_blkR_frame Mr' M1 b0 c0); [lia| |lia| |exact SHr].
    - pose proof (Z.div_mod b0 16 ltac:(lia)) as D. rewrite K3, Z.add_0_r in D. rewrite D. replace (16 * (b0 / 16)) with ((2 * (b0 / 16)) * 8) by ring. apply Z_mod_mult.
    - intros a Ha. apply VIS1. exact (art_vis_shadow A model b0 c0 a K9 Ha). }
  apply (CONT R' pc1 Mr' M1 model' HQ); [ | exact GROW | exact FR1 | exact VIS1 | exact HID | exact RT | exact (bi_minv _ _ _ _ _ _ _ _ _ _ _ B1)].
  exists G. cbn [vml_of fst snd].
  split. { change (mkH (m_vm_lazy model') A) with (bhid A model'). rewrite EMr. apply (art_alloc_rep_frame_sh art_fsg MAPS0 RESV0 rn G LB _ Mr' b0 c0 REPr GRr).
           - intros x Hz Hb Hs. apply FRr. intros HF. destruct (FPAZ _ HF Hz) as [X|X]; [exact (Hb X)|exact (Hs X)].
           - exact LSAN.
           - exact (bi_live _ _ _ _ _ _ _ _ _ _ _ B0).
           - exact KN.
           - exact HB0.
           - exact Hb0a.
           - exact Hb0n.
           - exact SHr. }
  split. { apply (art_fsinv_client_proved rn (g_fs art_fsg G) FF LK M M1 FS GROW).
           - intros x a Hz Hn. apply FR1. intros HF. apply Hn. exact (FPFS _ HF Hz).
           - intros x Hz. apply FR1. intros HF. exact (FPCS _ HF Hz). }
  split. { exact (BINV_intro _ _ _ _ _ _ _ _ _ _ _ B1). }
  split; [exact CRED|].
  split. { apply (art_client_ok_frame_sh rn LB FF LK A M M1 b0 c0 CLI GROW HB0); [|exact SH1]. intros b a Hb Nb Ha.
           pose proof CLI as (C1' & _ & _ & _ & _ & _ & _ & _ & _ & _ & CT). destruct (C1' b Hb) as (L1 & _ & _ & L4 & L5 & _).
           assert (Ra : 0 <= a < 2 ^ 64).
           { unfold in_shadow_of, HeapIfaceA.S in Ha. assert (0 <= fst b / 8) by (apply Z.div_pos; lia).
             assert ((fst b + snd b - 1) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia). change (2 ^ 47 / 8) with 17592186044416 in *. unfold HeapIfaceA.SB in *. lia. }
           pose proof (FR1 (Z_to_bv 64 a)) as X. rewrite art_u_lit in X by exact Ra. apply X. exact (FPSH b a Hb Nb Ha). }
  split; [exact KN|].
  split. { apply (art_lazy_ok_shrink art_fsg rn G A (m_vm_lazy model) (m_vm_lazy model') LZ). exact (art_bstep_pure_lazy A M M1 model model' BS). }
  destruct EG as (AW & EB). split; [exact AW|]. intros b x Hb Hx. destruct (page_in_ranges (page_base x) (m_vm_lazy model')) eqn:E; [|reflexivity].
  pose proof (art_bstep_pure_lazy A M M1 model model' BS x E) as E0. rewrite (EB b x Hb Hx) in E0. discriminate E0.
Qed.
End WrapS.

(* [comment removed for export] *)
Lemma art_annB_update : forall (Mo Mn : word -> option byte) b c u u', 0 <= u <= c -> 0 <= u' <= c -> u <> u' ->
  HAJ.ann_shadow Mo b u c ->
  (forall j, 0 <= j < (c + 7) / 8 -> ~ (annU_lo u u' <= j < annU_hi u u') -> Mn (Z_to_bv 64 (HeapIfaceA.S b + j)) = Mo (Z_to_bv 64 (HeapIfaceA.S b + j))) ->
  (forall j, annU_lo u u' <= j < annU_hi u u' -> Mn (Z_to_bv 64 (HeapIfaceA.S b + j)) = Some (Z_to_bv 8 (annval u' j))) ->
  HAJ.ann_shadow Mn b u' c.
Proof.
  intros Mo Mn b c u u' Hu Hu' Ne (Z0 & P0 & F0) KEEP NEW.
  pose proof (annU_div8_facts u ltac:(lia)) as (Du1 & Du2 & Du3 & Du4 & _ & _). pose proof (annU_div8_facts u' ltac:(lia)) as (Dv1 & Dv2 & Dv3 & Dv4 & _ & _).
  pose proof (annU_div8_facts c ltac:(lia)) as (Dc1 & Dc2 & _ & _ & _ & _).
  assert (M1 : u / 8 <= c / 8) by (apply Z.div_le_mono; lia). assert (M2 : u' / 8 <= c / 8) by (apply Z.div_le_mono; lia).
  assert (M3 : (u + 7) / 8 <= (c + 7) / 8) by (apply Z.div_le_mono; lia). assert (M4 : (u' + 7) / 8 <= (c + 7) / 8) by (apply Z.div_le_mono; lia).
  assert (WND : (u < u' -> annU_lo u u' = u / 8 /\ annU_hi u u' = (u' + 7) / 8) /\ (u' < u -> annU_lo u u' = u' / 8 /\ annU_hi u u' = (u + 7) / 8)).
  { unfold annU_lo, annU_hi. rewrite (proj2 (Z.eqb_neq u u') Ne). split; intros Hlt; [rewrite Z.min_l, Z.max_r by lia|rewrite Z.min_r, Z.max_l by lia]; split; reflexivity. }
  assert (VAL0 : forall j, j < u' / 8 -> annval u' j = 0) by (intros j Hj; unfold annval; rewrite (proj2 (Z.ltb_lt j (u' / 8)) Hj); reflexivity).
  assert (VALM : u' mod 8 <> 0 -> annval u' (u' / 8) = u' mod 8).
  { intros E. unfold annval. rewrite Z.ltb_irrefl, Z.eqb_refl, (proj2 (Z.eqb_neq (u' mod 8) 0) E). reflexivity. }
  assert (VALF : forall j, (u' + 7) / 8 <= j -> annval u' j = 252).
  { intros j Hj. unfold annval. rewrite (proj2 (Z.ltb_ge j (u' / 8))) by lia.
    destruct (Z.eq_dec (u' mod 8) 0) as [E|E]; [rewrite E; cbn [Z.eqb negb]; rewrite Bool.andb_false_r; reflexivity|].
    rewrite (proj2 (Z.eqb_neq j (u' / 8))) by (pose proof (Dv4 E); lia). reflexivity. }
  unfold HAJ.ann_shadow, shadow_zero, byte_at in *.
  destruct (Z_lt_le_dec u u') as [Lt|Ge]; [destruct (proj1 WND Lt) as (EL & EH)|destruct (proj2 WND ltac:(lia)) as (EL & EH)]; rewrite EL, EH in KEEP, NEW.
  - (* [comment removed for export] *)
    assert (MM : u / 8 <= u' / 8) by (apply Z.div_le_mono; lia). assert (MM2 : (u + 7) / 8 <= (u' + 7) / 8) by (apply Z.div_le_mono; lia).
    split; [|split].
    + intros j Hj. destruct (Z_lt_ge_dec j (u / 8)) as [Lo|Hi]; [rewrite KEEP by lia; exact (Z0 j ltac:(lia))|]. rewrite NEW by lia. rewrite VAL0 by lia. reflexivity.
    + intros E. rewrite NEW by (pose proof (Dv4 E); lia). rewrite (VALM E). reflexivity.
    + intros j Hj. destruct (Z_lt_ge_dec j ((u' + 7) / 8)) as [Lo|Hi]; [exfalso; lia|]. rewrite KEEP by lia. apply F0. lia.
  - (* [comment removed for export] *)
    assert (MM : u' / 8 <= u / 8) by (apply Z.div_le_mono; lia). assert (MM2 : (u' + 7) / 8 <= (u + 7) / 8) by (apply Z.div_le_mono; lia).
    split; [|split].
    + intros j Hj. rewrite KEEP by lia. exact (Z0 j ltac:(lia)).
    + intros E. rewrite NEW by (pose proof (Dv4 E); lia). rewrite (VALM E). reflexivity.
    + intros j Hj. destruct (Z_lt_ge_dec j ((u + 7) / 8)) as [Lo|Hi]; [rewrite NEW by lia; rewrite VALF by lia; reflexivity|]. rewrite KEEP by lia. apply F0. lia.
Qed.
Lemma art_annB_eq : forall (Mo Mn : word -> option byte) b c u,
  HAJ.ann_shadow Mo b u c ->
  (forall j, 0 <= j < (c + 7) / 8 -> Mn (Z_to_bv 64 (HeapIfaceA.S b + j)) = Mo (Z_to_bv 64 (HeapIfaceA.S b + j))) -> 0 <= u <= c ->
  HAJ.ann_shadow Mn b u c.
Proof.
  intros Mo Mn b c u (Z0 & P0 & F0) KEEP Hu. assert (D2 : u / 8 <= c / 8) by (apply Z.div_le_mono; lia).
  pose proof (annU_div8_facts c ltac:(lia)) as (Dc1 & _). pose proof (annU_div8_facts u ltac:(lia)) as (Du1 & Du2 & Du3 & Du4 & _).
  assert (M3 : (u + 7) / 8 <= (c + 7) / 8) by (apply Z.div_le_mono; lia).
  unfold HAJ.ann_shadow, shadow_zero, byte_at in *.
  split; [|split]; [intros j Hj | intros E; pose proof (Du4 E) | intros j Hj]; rewrite KEEP by lia; [exact (Z0 j Hj)|exact (P0 E)|exact (F0 j Hj)].
Qed.
Lemma art_annB_shadowR : forall (M : word -> option byte) b c u, 0 <= u <= c -> HAJ.ann_shadow M b u c -> HAJ.shadow_blkR M b c.
Proof. intros M b c u Hu AN. right. exists u. split; [exact Hu|exact AN]. Qed.
(* [comment removed for export] *)
Lemma art_annB_last : forall (M : word -> option byte) b c u, 0 <= u <= c -> c mod 8 <> 0 -> HAJ.ann_shadow M b u c ->
  exists v, byte_at M (HeapIfaceA.S b + c / 8) v /\ (v = 252 \/ 1 <= v <= c mod 8).
Proof.
  intros M b c u Hu Hc8 (Z0 & P0 & F0). unfold shadow_zero in Z0.
  pose proof (annU_div8_facts c ltac:(lia)) as (Dc1 & Dc2 & Dc3 & Dc4 & Dc5 & _). pose proof (annU_div8_facts u ltac:(lia)) as (Du1 & Du2 & Du3 & Du4 & Du5 & _).
  pose proof (Dc4 Hc8) as EC. assert (M1 : u / 8 <= c / 8) by (apply Z.div_le_mono; lia).
  pose proof (RD_range u ltac:(lia)) as (R1 & R2 & R3). pose proof (RD_range c ltac:(lia)) as (Q1 & Q2 & Q3).
  pose proof (Z.mod_pos_bound u 8 ltac:(lia)) as Bu. pose proof (Z.mod_pos_bound c 8 ltac:(lia)) as Bc.
  destruct (Z_lt_ge_dec ((u + 7) / 8) (c / 8 + 1)) as [Lo|Hi].
  - exists 252. split; [apply F0; lia|left; reflexivity].
  - assert (Eu : u / 8 = c / 8) by lia.
    assert (Hu8 : u mod 8 <> 0) by (intros E; pose proof (Du3 E); lia).
    exists (u mod 8). rewrite <- Eu. split; [exact (P0 Hu8)|right]. unfold RD in *. lia.
Qed.
Lemma art_cell1_of_byte : forall (M : word -> option byte) a v, 0 <= v < 256 -> byte_at M a v -> cellA M a 1 v.
Proof. intros M a v Hv B. unfold cell, byte_at in *. cbn [rdn]. rewrite B. rewrite art_bytes1 by lia. reflexivity. Qed.

Lemma art_div8_addl : forall b c, b mod 8 = 0 -> (b + c) / 8 = b / 8 + c / 8.
Proof.
  intros b c Hb. pose proof (Z.div_mod b 8 ltac:(lia)) as D. rewrite Hb, Z.add_0_r in D.
  replace (b + c) with (b / 8 * 8 + c) by lia. rewrite Z.div_add_l by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Definition art_ann_place (b c : Z) : Prop := (b + c <= 0x10000 \/ 0x696000 <= b) /\ (b + c <= 0x7fff7000 \/ 0x10007fff8000 <= b).

(* [comment removed for export] *)
Section WA.
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

#[using="Hwx HLsegs HLlo HLhi"] Theorem art_wrap_annotate : forall (R : bvmap 5 word) (M : word -> option byte) (model : Model)
    (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (K : ShapeAlg.TSet) (b c u u' : Z),
  let sp := U (getr R 2) in
  RI LB FF LK cr A M (vml_of model) -> m_halted model = None -> MInv A model ->
  getr R 10 = Z_to_bv 64 b -> getr R 11 = Z_to_bv 64 (b + c) -> getr R 12 = Z_to_bv 64 (b + u) -> getr R 13 = Z_to_bv 64 (b + u') ->
  In (b, c) LB -> b mod 16 = 0 -> 0 <= u <= c -> 0 <= u' <= c ->
  HAJ.ann_shadow M b u c ->
  getr R 4 = Z_to_bv 64 (rn_tp rn) -> Hoare.ret_ok (getr R 1) ->
  astack_ok L (rn_ar rn) M 2304 sp -> K [] ->
  (forall (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (A' : list (Z * Z)),
      regs_preserved R R' -> HAJ.ann_shadow M' b u' c ->
      (forall a, 0 <= a < 2 ^ 64 -> aclient L (rn_ar rn) LB FF sp 2304 a -> ~ in_shadow_of b c a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
      (forall a, in_shadow_of b c a -> M (Z_to_bv 64 a) <> None -> M' (Z_to_bv 64 a) <> None) ->
      (forall a, sp - 2304 <= a < sp -> M' (Z_to_bv 64 a) <> None) ->
      model_rt model model' -> incl A A' -> MInv A' model' ->
      RI LB FF LK cr A' M' (vml_of model') ->
      srealizes ASEGS scfg (mkCfg (mkst R' (getr R 1) M' (seg_rom ASEGS)) model') K) ->
  srealizes ASEGS scfg (mkCfg (mkst R (0x7ba7c : word) M (seg_rom ASEGS)) model) K.
Proof.
  intros R M model LB FF LK cr A K b c u u' sp INV Hhalt HMI H10 H11 H12 H13 Hin Hb16 Hu Hu' ANN H4 Hret AST KT0 CONT.
  destruct (art_ri_open MAPS0 RESV0 NOACC0 BASE BUDGET rn LB FF LK cr A M model INV Hhalt HMI) as (G & REPr & FS & B0 & CRED & CLI & KN & LZ & EG).
  set (Mr0 := mrestrict (bhid A model) M) in *.
  destruct AST as (S16 & SHI & SLE & STOP & SWR & SDEF). fold sp in S16, SHI, SLE, SWR, SDEF. rewrite HLsegs in SWR.
  assert (HIeq : ahl_ceil (rn_ar rn) = rn_HI rn) by reflexivity. rewrite HIeq in SHI.
  pose proof (art_cli_hi rn LB FF LK A M CLI) as (HI1 & HI2).
  pose proof REPr as (ROK & STAT & THR & _).
  pose proof CLI as (CB & _ & _ & _ & CE1 & CE2 & _ & CE4 & CE5 & _). destruct (CB (b, c) Hin) as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13). cbn [fst snd] in *.
  rewrite HIeq in K5, CE1, CE2.
  assert (Hbc : b + c + 8 <= 2 ^ 47) by (clear - K5 CE1 CE2 CE4 CE5; lia).
  (* [comment removed for export] *)
  destruct (art_wfa_kind art_fsg rn G LB Mr0 REPr b c Hin) as (kd & KIND).
  destruct (art_wfa_hdr art_fsg rn G LB Mr0 REPr b c kd KIND) as ((bb & _ & _ & _ & _ & Hc28) & _).
  assert (Hb8 : b mod 8 = 0) by (pose proof (Z.div_mod b 16 ltac:(lia)) as D; rewrite Hb16, Z.add_0_r in D; rewrite D; replace (16 * (b / 16)) with ((2 * (b / 16)) * 8) by ring; apply Z_mod_mult).
  destruct K6 as (_ & K6 & _). unfold BIGSHADOW_LO, BIGSHADOW_HI in K6.
  assert (PLACE : art_ann_place b c) by exact (conj K2 K6). assert (PL2 : annU_place b c) by exact K6. clear K2 K6 K12 K13.
  set (lo := annU_lo u u') in *. set (hi := annU_hi u u') in *.
  assert (ESb : HeapIfaceA.S b = 2147450880 + b / 8) by (unfold HeapIfaceA.S, HeapIfaceA.SB; ring).
  pose proof (annU_div8_facts c ltac:(lia)) as (Dc1 & Dc2 & Dc3 & Dc4 & Dc5 & Dc6).
  assert (Hbd : b = 8 * (b / 8)) by (pose proof (Z.div_mod b 8 ltac:(lia)); lia).
  (* [comment removed for export] *)
  assert (EJ : 0 <= lo <= hi /\ hi <= (c + 7) / 8).
  { unfold lo, hi, annU_lo, annU_hi. assert (0 <= Z.min u u' / 8) by (apply Z.div_pos; lia).
    destruct (u =? u'); [split; [lia|apply Z.div_le_mono; lia]|].
    assert (Z.min u u' / 8 <= (Z.max u u' + 7) / 8) by (apply Z.div_le_mono; lia). assert ((Z.max u u' + 7) / 8 <= (c + 7) / 8) by (apply Z.div_le_mono; lia). lia. }
  destruct EJ as (EJ3 & EJ4).
  assert (SBr : 0 <= b / 8 /\ b / 8 + (c + 7) / 8 <= 2 ^ 44).
  { split; [apply Z.div_pos; lia|]. assert (X : (b + (c + 7)) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
    rewrite (art_div8_addl b (c + 7) Hb8) in X. change (2 ^ 47 / 8) with (2 ^ 44) in X. exact X. }
  (* [comment removed for export] *)
  assert (INSH : forall j, 0 <= j < (c + 7) / 8 -> in_shadow_of b c (HeapIfaceA.S b + j)).
  { intros j Hj. unfold in_shadow_of. split; [lia|]. unfold HeapIfaceA.S.
    assert (b / 8 + j <= (b + c - 1) / 8); [|lia]. apply Z.div_le_lower_bound; [lia|]. pose proof (RU_range c ltac:(lia)) as (X1 & X2). clear - Hbd Hj K4 Dc6 X1. lia. }
  assert (VSH : forall j, 0 <= j < (c + 7) / 8 -> bhid A model (Z_to_bv 64 (HeapIfaceA.S b + j)) = false).
  { intros j Hj. exact (art_vis_shadow A model b c _ K9 (INSH j Hj)). }
  (* [comment removed for export] *)
  assert (WM : wrA M (sp - 2192) 2192). { intros d k Hd Hk. replace (sp - 2192 + d) with (sp - 2304 + (112 + d)) by lia. apply SWR; lia. }
  assert (W0 : wrA Mr0 (sp - 2192) 2192).
  { apply (art_stack_wr art_fsg rn G A (m_vm_lazy model) M sp 2192 ROK LZ ltac:(lia) ltac:(lia) ltac:(lia)). intros d k Hd Hk. apply WM; lia. }
  destruct STAT as (PC & LAY & TSD & _ & _ & _ & _ & S8).
  assert (CF : cellA Mr0 (0x13d438 + 96) 1 1) by conj_find S8.
  assert (CV : cellA Mr0 0x137510 8 0x1cf6d8) by conj_find S8.
  assert (CV0 : cellA Mr0 0x1cf6d8 4 0) by conj_find S8.
  (* [comment removed for export] *)
  assert (WSH : wrA Mr0 (BatPoison_b.SB + b / 8 + lo) (hi - lo)).
  { unfold BatPoison_b.SB. apply art_wr_of_defined; [lia|lia|]. intros x Hx.
    set (j := U x - HeapIfaceA.S b). assert (Ej : x = Z_to_bv 64 (HeapIfaceA.S b + j)) by (unfold j; rewrite <- (Z_to_bv_bv_unsigned 64 x) at 1; f_equal; ring).
    assert (Hj : 0 <= j < (c + 7) / 8) by (unfold j; rewrite ESb; lia).
    unfold Mr0, mrestrict. rewrite Ej, (VSH j Hj).
    assert (Hj' : j < c / 8 \/ (j = c / 8 /\ c mod 8 <> 0)) by (destruct (Z.eq_dec (c mod 8) 0) as [E|E]; [left; rewrite <- (Dc3 E); lia|]; destruct (Z_lt_ge_dec j (c / 8)); [left; lia|right; split; [pose proof (Dc4 E); lia|exact E]]).
    destruct (shadow_blkR_bytes M b c K4 K8 j (proj1 Hj) Hj') as (v0 & Bv). unfold byte_at in Bv. rewrite Bv. discriminate. }
  assert (Hsp2 : getr R 2 = Z_to_bv 64 sp) by (unfold sp; rewrite Z_to_bv_bv_unsigned; reflexivity).
  (* [comment removed for export] *)
  assert (ANN0 : HAJ.ann_shadow Mr0 b u c).
  { apply (art_annB_eq M Mr0 b c u ANN); [|exact Hu]. intros j Hj. unfold Mr0, mrestrict. rewrite (VSH j Hj). reflexivity. }
  assert (LAST : exists v, c mod 8 <> 0 -> cellA Mr0 (BatPoison_b.SB + (b + c) / 8) 1 v /\ (v = 252 \/ 1 <= v <= c mod 8)).
  { destruct (Z.eq_dec (c mod 8) 0) as [E|E]; [exists 0; intros X; exfalso; exact (X E)|].
    destruct (art_annB_last Mr0 b c u Hu E ANN0) as (v & Bv & Hv). exists v. intros _. split; [|exact Hv].
    replace (BatPoison_b.SB + (b + c) / 8) with (HeapIfaceA.S b + c / 8) by (unfold BatPoison_b.SB; rewrite ESb, (art_div8_addl b c Hb8); lia).
    apply art_cell1_of_byte; [pose proof (Z.mod_pos_bound c 8 ltac:(lia)); lia|exact Bv]. }
  destruct LAST as (v & LAST).
  destruct (art_annotateU_run R Mr0 (seg_rom ASEGS) (getr R 1) sp b c u u' v eq_refl Hret Hsp2 H10 H11 H12 H13 K1 Hb8 Hu Hu' Hbc ltac:(clear - Hc28; lia) PL2
              ltac:(lia) ltac:(lia) W0 LAY CF CV CV0 LAST WSH)
    as (R' & Mr' & RUN & Q1 & Q2 & Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & QK & QGR & QFR & QNEW).
  fold lo hi in QFR, QNEW. unfold BatPoison_b.SB in QFR, QNEW.
  (* [comment removed for export] *)
  assert (KEEPj : forall j, 0 <= j < (c + 7) / 8 -> ~ (lo <= j < hi) -> Mr' (Z_to_bv 64 (HeapIfaceA.S b + j)) = Mr0 (Z_to_bv 64 (HeapIfaceA.S b + j))).
  { intros j Hj Nj. apply QFR; rewrite art_u_lit by (rewrite ESb; lia); rewrite ESb; lia. }
  assert (NEWj : forall j, lo <= j < hi -> Mr' (Z_to_bv 64 (HeapIfaceA.S b + j)) = Some (Z_to_bv 8 (annval u' j))).
  { intros j Hj. rewrite ESb. apply QNEW. exact Hj. }
  assert (ANN' : HAJ.ann_shadow Mr' b u' c).
  { destruct (Z.eq_dec u u') as [Eq|Ne].
    - subst u'. apply (art_annB_eq Mr0 Mr' b c u ANN0); [|exact Hu]. intros j Hj. apply KEEPj; [exact Hj|]. unfold lo, hi, annU_lo, annU_hi. rewrite Z.eqb_refl. lia.
    - exact (art_annB_update Mr0 Mr' b c u u' Hu Hu' Ne ANN0 KEEPj NEWj). }
  assert (NBsh : forall x, 2147450880 + b / 8 + lo <= x < 2147450880 + b / 8 + hi -> in_shadow_of b c x).
  { intros x Hx. replace x with (HeapIfaceA.S b + (x - HeapIfaceA.S b)) by ring. apply INSH. rewrite ESb; lia. }
  set (FP := fun x : Z => (sp - 2192 <= x < sp) \/ (2147450880 + b / 8 + lo <= x < 2147450880 + b / 8 + hi)).
  apply (art_wrap_pure2sh MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Hwx K R _ M model G LB FF LK cr A FP b c
           (fun R1 pc1 M1 => pc1 = getr R 1 /\ R1 = R' /\ M1 = Mr') REPr FS B0 CRED CLI KN LZ EG Hin Hb16 K4).
  - (* [comment removed for export] *)
    exists R', (getr R 1), Mr'. split; [exact RUN|]. split; [exact QGR|].
    split. { intros x Hx. apply QFR; intros X; apply Hx; unfold FP; [left|right]; exact X. }
    split. { pose proof THR as (_ & _ & _ & _ & _ & _ & _ & THR0).
             assert (TL : 0x10000 <= rn_tp rn + rn_loff rn /\ rn_tp rn + rn_loff rn + 4 <= 0x696000)
               by (destruct ROK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & T1 & T2 & _); exact (conj T1 T2)).
             apply (BatAllocG_b.cell_agree Mr0 Mr'); [|clear - TL; lia|cbn; clear - TL; lia|exact THR0].
             intros x Hx. cbn in Hx. apply QFR; clear - Hx TL SHI HI1 EJ3 SBr; lia. }
    split; [exact (art_annB_shadowR Mr' b c u' Hu' ANN')|]. split; [reflexivity|split; reflexivity].
  - (* [comment removed for export] *)
    intros x HF Z. destruct HF as [X|X].
    + exfalso. pose proof (art_zone_below MAPS0 RESV0 NOACC0 BASE BUDGET rn G LB A M Mr0 model x REPr KN B0 (or_introl Z)) as ZB. clear - ZB X SHI. lia.
    + right. exact (NBsh x X).
  - (* [comment removed for export] *)
    intros x HF Z3. exfalso. destruct HF as [X|X].
    + pose proof (art_fs_zone3_below rn G LB _ x REPr Z3) as ZB. clear - ZB X SHI. lia.
    + pose proof ROK as ROK'. rok_open ROK'. pose proof GEO as GEO'. geo_open GEO'. destruct Fapp as (_ & Fap & _). unfold BIGSHADOW_LO, BIGSHADOW_HI in Fap. unfold fs_zone3, FS_BYTES in Z3. unfold FS_BYTES in Fap. clear - X Z3 Fap G10 G19 G20 EJ3 EJ4 SBr. lia.
  - (* [comment removed for export] *)
    intros x HF CS. destruct HF as [X|X].
    + pose proof (art_cs_zone_below rn G LB FF LK M Mr0 x REPr FS CS) as CB1. clear - CB1 X SHI. lia.
    + unfold cs_zone in CS. change (HeapIfaceA.S 0x10000) with 2147459072 in CS. change (HeapIfaceA.S 0x696000) with 2148314112 in CS.
      assert (KB : b + c <= 0x10000 -> b / 8 + (c + 7) / 8 <= 0x2000).
      { intros HB. clear - HB Hb8. assert (E1 : (b + (c + 7)) / 8 <= (0x10000 + 7) / 8) by (apply Z.div_le_mono; lia).
        rewrite (art_div8_addl b (c + 7) Hb8) in E1. change ((0x10000 + 7) / 8) with 0x2000 in E1. lia. }
      (* [comment removed for export] *)
      assert (KB' : 0x696000 <= b -> 0x696000 / 8 <= b / 8) by (intros HB; clear - HB; apply Z.div_le_mono; lia).
      lazymatch type of KB' with _ -> ?q <= _ => let v := eval vm_compute in q in change q with v in KB' end.
      destruct PLACE as (K2 & _). pose proof ROK as ROK'. rok_open ROK'. pose proof GEO as GEO'. geo_open GEO'. destruct Fapp as (_ & Fap & _). unfold BIGSHADOW_LO, BIGSHADOW_HI in Fap. unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in D3. clear - X CS K2 KB KB' EJ3 EJ4 D0 D1 D2 D3 G19 G20 SBr. unfold apart in *. lia.
  - (* [comment removed for export] *)
    intros b' x Hb' Nb' Hx HF. destruct HF as [X|X].
    + pose proof (art_block_shadow_below rn LB FF LK A M b' x CLI Hb' Hx) as B1. clear - B1 X SHI HI1. lia.
    + pose proof (K10 b' (art_lb_remove_keep b LB b' Hb' Nb')) as AP. destruct (CB b' Hb') as (L1 & _ & L3 & L4 & _).
      unfold in_shadow_of, HeapIfaceA.S, HeapIfaceA.SB in Hx.
      assert (Hb'8 : fst b' mod 8 = 0) by (pose proof (Z.div_mod (fst b') 16 ltac:(lia)) as D; rewrite L3, Z.add_0_r in D; rewrite D; replace (16 * (fst b' / 16)) with ((2 * (fst b' / 16)) * 8) by ring; apply Z_mod_mult).
      pose proof (Z.div_mod (fst b') 8 ltac:(lia)) as Db'. rewrite Hb'8, Z.add_0_r in Db'.
      destruct AP as [AP|AP].
      * assert (b / 8 + (c + 7) / 8 <= fst b' / 8).
        { pose proof (RU_range c ltac:(clear - K4; lia)) as (RUc & _). clear - AP Hbd Db' Dc6 RUc. lia. }
        clear - X Hx H EJ3 EJ4. lia.
      * assert ((fst b' + snd b' - 1) / 8 < b / 8) by (apply Z.div_lt_upper_bound; clear - Hbd AP L4; lia).
        clear - X Hx H EJ3 EJ4. lia.
  - (* [comment removed for export] *)
    intros R1 pc1 M1 M2 model' (Epc & ER & EM) RI' GROW FR1 VIS1 HID RT MI'. subst pc1 R1 M1.
    apply (CONT R' M2 model' A).
    + apply keeps_cs_preserved. intros r Hr. cbn [callee_saved In] in Hr.
      repeat (destruct Hr as [<-|Hr]; [first [ exact Q1 | rewrite Q2; exact (eq_sym Hsp2) | exact Q8 | exact Q9 | exact Q18 | exact Q19 | exact Q20 | exact Q21
                                             | apply QK; unfold art_ann_kept; tauto ]|]).
      destruct Hr.
    + apply (art_annB_eq Mr' M2 b c u' ANN'); [|exact Hu']. intros j Hj. exact (VIS1 _ (VSH j Hj)).
    + intros a Ra Ha NS. apply FR1. rewrite art_u_lit by exact Ra. unfold FP. intros [X|X].
      * apply (art_cls_off_scratch rn LB FF LK A M CLI L HLlo HLhi (g_fs art_fsg G) FS sp 2304 a ltac:(clear - SHI; lia) (or_intror Ha)). clear - X. lia.
      * exact (NS (NBsh a X)).
    + intros a Ha Hd. apply GROW. exact Hd.
    + intros a Ha. apply GROW.
      assert (WM2 : wrA M (sp - 2304) 2304) by (intros d k Hd Hk; apply SWR; assumption).
      pose proof (art_wr_wview ASEGS M (sp - 2304) 2304 ltac:(clear - SHI HI1; lia) ltac:(clear - SLE STOP; lia) WM2 (Z_to_bv 64 a)) as V.
      rewrite art_u_lit in V by (clear - Ha SHI HI1 SLE STOP; lia). specialize (V ltac:(clear - Ha; lia)).
      rewrite art_wview_off in V by (rewrite art_u_lit by (clear - Ha SHI HI1 SLE STOP; lia); right; clear - Ha SHI HI1; lia). exact V.
    + exact RT.
    + apply incl_refl.
    + exact MI'.
    + exact RI'.
Qed.
End WA.
