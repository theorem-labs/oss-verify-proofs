(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceAEx HeapIfaceAEr
     ArtMem ArtRuns ArtBridge EbtLift EbrDep EarUkey EbrInv EbrInvFreePure EbrFsInv EbrFsInvLaws EbrFsInvLaws4 EbrWrapKit EbrWrapFreeR
     EbrWrapMallocAll EbrWrapFree EbrWrapMemI EbrWrapSmallocI EbrIfaceLaws EbrIfaceInst EbrIfaceInstFree.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Definition art_LR : HAR.layoutR := HAR.LR 0x7ac68 0x7ab08.

Lemma art_credit_le : forall FSG BUDGET rn (G : art_gs FSG) LB cr cr',
  art_credit_ok FSG BUDGET rn G LB cr -> 0 <= fst cr' <= fst cr -> 0 <= snd cr' <= snd cr -> art_credit_ok FSG BUDGET rn G LB cr'.
Proof.
  intros FSG BUDGET rn G LB cr cr' (irr & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & QT & QG) H1 H2.
  exists irr. unfold art_credit_ok.
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; assumption.
Qed.

Lemma art_fsinv_keys : forall rn D g FF LK M, art_fsinv rn g FF LK M -> art_fsinv (art_rn_k rn D) g FF LK M.
Proof. intros rn D g FF LK M H. exact H. Qed.

Lemma ukeyG_frame : forall L ar p0 (M0 M1 : word -> option byte) sp ra s0 K,
  ukeyG L ar p0 M0 sp ra s0 K ->
  (forall a v, sp <= a -> a + 8 <= ar_stack_top ar -> a mod 8 = 0 -> 0 <= v < 2 ^ 64 -> cell_is (hl_segs L) M0 a 8 v -> cell_is (hl_segs L) M1 a 8 v) ->
  ukeyG L ar p0 M1 sp ra s0 K.
Proof.
  intros L ar p0 M0 M1 sp ra s0 K (RC & E & H) TR. exists RC. split; [exact E|]. intros M2 TR2 C8 C16. apply H; [|exact C8|exact C16].
  intros a v H1 H2 H3 H4 C. apply TR2; [exact H1|exact H2|exact H3|exact H4|]. apply TR; assumption.
Qed.

Section Fam.
Variables MAPS0 RESV0 NOACC0 : list (word * word).
Variables BASE BUDGET : Z.
Variable rn : art_run.
Variable scfg : SpuriousCfg.
Hypothesis Halloc : sc_alloc scfg = false.
Hypothesis Hwx : wx_segs_nowrap ASEGS.
Hypothesis STATIC : bridge_static ASEGS MAPS0 RESV0 NOACC0 (art_RES rn) (rn_HI rn) BUDGET LENMAX KMAX.
Hypothesis Htp : rn_tp rn = 0x67a180.
Hypothesis Hkey0 : rn_key rn = 0.
Hypothesis Htsd : rn_tsd rn = 0x69b638.
Hypothesis Hloff : rn_loff rn = 0x10.

Definition art_HIk (D : list (list Z)) : asan_iface := art_iface art_fsg MAPS0 RESV0 NOACC0 BASE BUDGET art_fsinv (art_rn_k rn D).

#[using="Halloc Hwx STATIC Htp Hkey0 Htsd Hloff"]
Theorem art_fam_base : forall D, HAJ.asan_iface_okR art_L (rn_ar rn) art_C scfg (art_HIk D).
Proof.
  intros D.
  exact (art_inst_ok MAPS0 RESV0 NOACC0 BASE BUDGET (art_rn_k rn D) scfg Halloc Hwx STATIC Htp Hkey0 Htsd Hloff
           (art_inst_free MAPS0 RESV0 NOACC0 BASE BUDGET (art_rn_k rn D) scfg Halloc Hwx STATIC Htp)
           (art_inst_smalloc MAPS0 RESV0 NOACC0 BASE BUDGET (art_rn_k rn D) scfg Hwx Htp)).
Qed.

#[using="Type"] Theorem art_fam_weaken : HAR.rt_weakenR art_HIk.
Proof.
  intros D0 D1 LB FF LK cr cr' A M V RI INCL H1 H2.
  assert (RI1 : art_ri_inv art_fsg MAPS0 RESV0 NOACC0 BASE BUDGET art_fsinv (art_rn_k rn D1) LB FF LK cr' A M V).
  { destruct RI as (G & REP & FS & BV & CRED & CLI & KN & LZ & EG). exists G.
    split; [exact REP|]. split; [exact FS|]. split; [exact BV|]. split; [exact (art_credit_le _ _ _ _ _ _ _ CRED H1 H2)|].
    split; [exact CLI|]. split; [exact KN|]. split; [exact LZ|exact EG]. }
  apply (art_ri_inv_keys art_fsg MAPS0 RESV0 NOACC0 BASE BUDGET art_fsinv art_fsinv_keys (art_rn_k rn D1) D0 _ _ _ _ _ _ _ RI1).
  intros k DK. exact (DInvK_incl _ _ _ _ _ _ DK INCL).
Qed.

#[using="Type"] Lemma art_fam_mpost_up : forall D Kt crp fx R M model LB FF LK A n K,
  HAR.amalloc_postG art_L (rn_ar rn) scfg art_HIk D crp fx R M model LB FF LK A n K ->
  HAR.amalloc_postG art_L (rn_ar rn) scfg art_HIk (Kt :: D) crp fx R M model LB FF LK A n K.
Proof.
  intros D Kt crp fx R M model LB FF LK A n K P R' M' model' A' u E0 E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 RI.
  apply (P R' M' model' A' u E0 E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11).
  pose proof RI as (G0 & _ & _ & _ & (irr & W1 & W2 & _) & _).
  apply (art_fam_weaken D (Kt :: D) _ _ _ crp crp _ _ _ RI); [intros k Hk; right; exact Hk | lia | lia].
Qed.
#[using="Type"] Lemma art_fam_fpost_up : forall D Kt crp fx R M model LB FF LK A u K,
  HAR.afree_postG art_L (rn_ar rn) scfg art_HIk D crp fx R M model LB FF LK A u K ->
  HAR.afree_postG art_L (rn_ar rn) scfg art_HIk (Kt :: D) crp fx R M model LB FF LK A u K.
Proof.
  intros D Kt crp fx R M model LB FF LK A u K P R' M' model' A' E1 E2 E3 E4 E5 RI.
  apply (P R' M' model' A' E1 E2 E3 E4 E5).
  pose proof RI as (G0 & _ & _ & _ & (irr & W1 & W2 & _) & _).
  apply (art_fam_weaken D (Kt :: D) _ _ _ crp crp _ _ _ RI); [intros k Hk; right; exact Hk | lia | lia].
Qed.

#[using="Type"] Lemma art_fam_ukey : forall D p0 (R : bvmap 5 word) (M : word -> option byte) (model : Model) LB FF LK cr A scr Kt,
  art_ri_inv art_fsg MAPS0 RESV0 NOACC0 BASE BUDGET art_fsinv (art_rn_k rn D) LB FF LK cr A M (vml_of model) ->
  astack_ok art_L (rn_ar rn) M scr (U (getr R 2%bv)) -> 0 <= scr ->
  HAR.ukey_at art_L (rn_ar rn) p0 R M Kt ->
  ukeyG art_L (rn_ar rn) p0 (mrestrict (mkH (m_vm_lazy model) A) M) (U (getr R 2%bv)) (U (getr R 1%bv)) (U (getr R 8%bv)) Kt.
Proof.
  intros D p0 R M model LB FF LK cr A scr Kt (G & REP & _ & _ & _ & CLI & _ & LZ & _) (S16 & SHI & SLE & STOP & _) Hscr UK.
  cbn [vml_of fst snd] in REP, LZ. pose proof REP as (ROK & _).
  pose proof CLI as (_ & _ & _ & _ & CS1 & CS2 & CS3 & CS4 & _).
  pose proof (bv_unsigned_in_range _ (getr R 8%bv)) as R8. change (bv_modulus 64) with (2 ^ 64) in R8.
  apply (ukeyG_frame art_L (rn_ar rn) p0 M).
  - apply (ukey_ukeyG art_L (rn_ar rn) p0 M _ _ _ Kt UK); [|exact R8].
    replace (U (getr R 2%bv)) with ((2 * (U (getr R 2%bv) / 16)) * 8) by (pose proof (Z.div_mod (U (getr R 2%bv)) 16 ltac:(lia)); lia). apply Z_mod_mult.
  - intros a v Ha Ha8 Hal Hv C. cbn [art_rn_k rn_ar] in CS1, CS2, CS3, CS4.
    assert (H0a : 0 <= a) by lia.
    assert (H8a : a + Z.of_nat 8 < 2 ^ 64) by (change (Z.of_nat 8) with 8; lia).
    assert (VIS : art_vis (mkH (m_vm_lazy model) A) a (Z.of_nat 8)).
    { intros x Hx. apply (art_stack_vis art_fsg (art_rn_k rn D) G A (m_vm_lazy model) ROK LZ x).
      change (rn_HI (art_rn_k rn D)) with (rn_HI rn). change (Z.of_nat 8) with 8 in Hx. unfold rn_HI. lia. }
    unfold cell_is in *. cbn [art_L hl_segs] in C. cbn [art_L hl_segs].
    apply (proj2 (art_cell_vis (mkH (m_vm_lazy model) A) M a 8 v H0a H8a VIS)). exact C.
Qed.

#[using="Halloc Hwx STATIC Htp Hkey0 Htsd Hloff"]
Theorem art_fam_mallocN : HAR.amallocN_spec art_L (rn_ar rn) scfg art_HIk.
Proof.
  intros D fx R M model LB FF LK cr A n K PRE Hn CR POST.
  destruct PRE as (RI & Hhalt & HMI & H10 & H4 & Hret & AST & K0).
  exact (art_wrap_mallocN art_fsg art_fsinv MAPS0 RESV0 NOACC0 BASE BUDGET (art_rn_k rn D) scfg art_L Halloc Hwx STATIC
           eq_refl eq_refl eq_refl (eq_sym Htp) eq_refl eq_refl art_L_statics ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia)
           art_fsinv_frame_law_proved (fun gfs FF0 LK0 M0 FS => art_fsinv_in_proved (art_rn_k rn D) gfs FF0 LK0 M0 FS)
           fx R M model LB FF LK cr A n K RI Hhalt HMI H10 Hn CR H4 Hret AST K0 POST).
Qed.
#[using="Halloc Hwx STATIC Htp Hkey0 Htsd Hloff"]
Theorem art_fam_memsetN : HAR.amemsetN_spec art_L (rn_ar rn) scfg art_HIk.
Proof.
  intros D. exact (art_amemsetN MAPS0 RESV0 NOACC0 BASE BUDGET (art_rn_k rn D) scfg Hwx art_L eq_refl eq_refl eq_refl eq_refl eq_refl
                     (art_L_ro_img0) (art_L_static_img0) art_L_statics (art_L_tls (art_rn_k rn D) Htp Hkey0 Htsd Hloff) art_L_ro (art_L_cs (art_rn_k rn D) Htp) D).
Qed.
#[using="Halloc Hwx STATIC Htp Hkey0 Htsd Hloff"]
Theorem art_fam_memcpyN : HAR.amemcpyN_spec_at art_L (rn_ar rn) scfg art_HIk (hl_asan_memcpy art_L).
Proof.
  intros D. exact (art_amemcpyN MAPS0 RESV0 NOACC0 BASE BUDGET (art_rn_k rn D) scfg Hwx art_L eq_refl eq_refl eq_refl eq_refl eq_refl
                     (art_L_ro_img0) (art_L_static_img0) art_L_statics (art_L_tls (art_rn_k rn D) Htp Hkey0 Htsd Hloff) art_L_ro (art_L_cs (art_rn_k rn D) Htp) D).
Qed.
#[using="Halloc Hwx STATIC Htp Hkey0 Htsd Hloff"]
Theorem art_fam_memmoveN : HAR.amemcpyN_spec_at art_L (rn_ar rn) scfg art_HIk (hl_asan_memmove art_L).
Proof.
  intros D. exact (art_amemmoveN MAPS0 RESV0 NOACC0 BASE BUDGET (art_rn_k rn D) scfg Hwx art_L eq_refl eq_refl eq_refl eq_refl eq_refl
                     (art_L_ro_img0) (art_L_static_img0) art_L_statics (art_L_tls (art_rn_k rn D) Htp Hkey0 Htsd Hloff) art_L_ro (art_L_cs (art_rn_k rn D) Htp) D).
Qed.
#[using="Halloc Hwx STATIC Htp Hkey0 Htsd Hloff"]
Theorem art_fam_mallocL : HAR.amallocL_spec art_L (rn_ar rn) scfg art_LR art_HIk.
Proof.
  intros D fx R M model LB FF LK cr A n K Kt PRE Hn CR UK POST.
  pose proof PRE as (RI & Hhalt & HMI & H10 & H4 & Hret & AST & K0).
  exact (art_wrap_mallocU art_fsg art_fsinv MAPS0 RESV0 NOACC0 BASE BUDGET (art_rn_k rn D) scfg art_L Halloc Hwx STATIC
           eq_refl eq_refl eq_refl (eq_sym Htp) eq_refl eq_refl art_L_statics ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia)
           art_fsinv_frame_law_proved art_fsinv_keys (fun gfs FF0 LK0 M0 FS => art_fsinv_in_proved (art_rn_k rn D) gfs FF0 LK0 M0 FS)
           fx R M model LB FF LK cr A n K Kt false RI Hhalt HMI H10 Hn CR H4 Hret AST K0
           (art_fam_ukey D 0x7ac68 R M model LB FF LK cr A _ Kt RI AST ltac:(cbn; lia) UK) POST).
Qed.
#[using="Halloc Hwx STATIC Htp Hkey0 Htsd Hloff"]
Theorem art_fam_mallocW : HAR.amallocW_spec art_L (rn_ar rn) scfg art_LR art_HIk.
Proof.
  intros D fx R M model LB FF LK cr A n K Kt PRE HnW H1 UK IN POST.
  pose proof PRE as (RI & Hhalt & HMI & H10 & H4 & Hret & AST & K0).
  assert (Hn : 0 < n <= 2 ^ 34) by (change HAR.NW_LO with 64 in HnW; change HAR.NW_HI with 128 in HnW; lia).
  exact (art_wrap_mallocU art_fsg art_fsinv MAPS0 RESV0 NOACC0 BASE BUDGET (art_rn_k rn D) scfg art_L Halloc Hwx STATIC
           eq_refl eq_refl eq_refl (eq_sym Htp) eq_refl eq_refl art_L_statics ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia)
           art_fsinv_frame_law_proved art_fsinv_keys (fun gfs FF0 LK0 M0 FS => art_fsinv_in_proved (art_rn_k rn D) gfs FF0 LK0 M0 FS)
           fx R M model LB FF LK cr A n K Kt true RI Hhalt HMI H10 Hn (conj IN (conj HnW H1)) H4 Hret AST K0
           (art_fam_ukey D 0x7ac68 R M model LB FF LK cr A _ Kt RI AST ltac:(cbn; lia) UK) (art_fam_mpost_up D Kt _ fx R M model LB FF LK A n K POST)).
Qed.
#[using="Halloc Hwx STATIC Htp Hkey0 Htsd Hloff"]
Theorem art_fam_freeL : HAR.afreeL_spec art_L (rn_ar rn) scfg art_LR art_HIk.
Proof.
  intros D fx R M model LB FF LK cr A u n K Kt PRE UK POST.
  pose proof PRE as (RI & Hhalt & HMI & Hin & H10 & H4 & Hret & AST & K0).
  exact (art_wrap_freeU art_fsg art_fsinv MAPS0 RESV0 NOACC0 BASE BUDGET (art_rn_k rn D) scfg art_L Halloc Hwx STATIC
           eq_refl eq_refl eq_refl (eq_sym Htp) eq_refl eq_refl art_L_statics
           art_fsinv_frame_law_proved art_fsinv_keys (fun gfs FF0 LK0 M0 FS => art_fsinv_in_proved (art_rn_k rn D) gfs FF0 LK0 M0 FS)
           (art_fsinv_frame_law2_proved (art_rn_k rn D))
           fx R M model LB FF LK cr A u n K Kt false RI Hhalt HMI Hin H10 H4 Hret AST K0 ltac:(discriminate)
           (art_fam_ukey D 0x7ab08 R M model LB FF LK cr A _ Kt RI AST ltac:(cbn; lia) UK) POST).
Qed.
#[using="Halloc Hwx STATIC Htp Hkey0 Htsd Hloff"]
Theorem art_fam_freeW : HAR.afreeW_spec art_L (rn_ar rn) scfg art_LR art_HIk.
Proof.
  intros D fx R M model LB FF LK cr A u n K Kt PRE HnW UK IN POST.
  pose proof PRE as (RI & Hhalt & HMI & Hin & H10 & H4 & Hret & AST & K0).
  exact (art_wrap_freeU art_fsg art_fsinv MAPS0 RESV0 NOACC0 BASE BUDGET (art_rn_k rn D) scfg art_L Halloc Hwx STATIC
           eq_refl eq_refl eq_refl (eq_sym Htp) eq_refl eq_refl art_L_statics
           art_fsinv_frame_law_proved art_fsinv_keys (fun gfs FF0 LK0 M0 FS => art_fsinv_in_proved (art_rn_k rn D) gfs FF0 LK0 M0 FS)
           (art_fsinv_frame_law2_proved (art_rn_k rn D))
           fx R M model LB FF LK cr A u n K Kt true RI Hhalt HMI Hin H10 H4 Hret AST K0 (fun _ => IN)
           (art_fam_ukey D 0x7ab08 R M model LB FF LK cr A _ Kt RI AST ltac:(cbn; lia) UK) (art_fam_fpost_up D Kt _ fx R M model LB FF LK A u K POST)).
Qed.

#[using="Halloc Hwx STATIC Htp Hkey0 Htsd Hloff"]
Theorem art_fam_ok : HAR.asan_famR_ok art_L (rn_ar rn) art_C scfg art_LR art_HIk.
Proof.
  exact (HAR.AFROK art_L (rn_ar rn) art_C scfg art_LR art_HIk art_fam_base art_fam_weaken art_fam_mallocN art_fam_memsetN art_fam_memcpyN art_fam_memmoveN
           art_fam_mallocL art_fam_freeL art_fam_mallocW art_fam_freeW).
Qed.
End Fam.
