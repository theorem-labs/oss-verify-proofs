(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import Amb PropExec CatExec CatSim SeqExec StoreOk MemSplit Frame Hoare ShapeAlg ShapeLaws Nodes RefNodes
  RefMemcpyLib SRealizes SNodes LibIface LibBudget LibEff U1Layout MmapSim.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import Overlay RunsLib U1CxxTable U1Statics StaticsGen DrvLibContract
  S1SpecConsts S1Spec U1ExitKn U1ExitDefs U1Exit U1Cells U1TargetDefs U1TargetBlocks U1TargetInv U1RKn U1TargetRun.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.

Abbreviation RSEGS := Ubsan.M.loaded_segments.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma NoDup_fst_length_le : forall (l l' : list (Z * Z)),
  NoDup (map fst l) -> (forall x, In x l -> In x l') -> (length l <= length l')%nat.
Proof.
  intros l l' ND Hincl. rewrite <- (length_map fst l), <- (length_map fst l').
  apply NoDup_incl_length; [apply NoDup_ListNoDup; exact ND|]. intros a Ha. apply in_map_iff in Ha as ([a' b] & <- & Hin).
  apply in_map_iff. exists (a', b). split; [reflexivity|]. apply Hincl. exact Hin.
Qed.

Lemma errno_win_val : forall a, errno_win L a <-> 0x102374 <= a < 0x102378.
Proof. intros a. unfold errno_win, zwin. cbn. lia. Qed.

Lemma sx_region_cases : forall a, sx_region U1ST a -> in_runs D_SX a \/ 0x100280 <= a < 0x100288.
Proof. intros a H. apply u1_region in H. destruct H as [H|H]; [left; exact H | right]. unfold zwin in H. cbn in H. lia. Qed.

Lemma sx_region_img : forall a, sx_region U1ST a -> 0xef000 <= a < 0x124000.
Proof.
  intros a H. destruct (sx_region_cases a H) as [Hr|Hr]; [|lia].
  exact (proj1 (dsx_not_static a (in_runs_D_SX_RD a Hr))).
Qed.

Lemma sx_region_not_static : forall a, sx_region U1ST a -> ~ mng_static a.
Proof.
  intros a H. destruct (sx_region_cases a H) as [Hr|Hr].
  - exact (proj1 (proj2 (dsx_not_static a (in_runs_D_SX_RD a Hr)))).
  - unfold mng_static. lia.
Qed.

Lemma errno_not_sx : forall a, errno_win L a -> ~ sx_region U1ST a.
Proof.
  intros a He Hs. pose proof (proj1 (errno_win_val a) He) as He'. destruct (sx_region_cases a Hs) as [Hr|Hr]; [|lia].
  exact (proj2 (proj2 (dsx_not_static a (in_runs_D_SX_RD a Hr))) He).
Qed.

Lemma ro_clear_of_text : forall M, img_clear M 0x10000 0xef000 -> ro_clear L M.
Proof.
  intros M HT w (Hi & Hnrw & Hnq). pose proof (u64_range w) as Uw.
  apply img_iff in Hi. rewrite <- (Z_to_bv_bv_unsigned 64 w). apply HT.
  destruct (Z.lt_ge_cases (bv_unsigned w) 0xef000); [lia|]. exfalso. apply Hnrw.
  exists 0xef000, 0x124000. split; [left; reflexivity | lia].
Qed.

Lemma img_ro_clear_of_text : forall M, img_clear M 0x10000 0xef000 -> img_ro_clear L M.
Proof.
  intros M HT w Hi Hnrw. pose proof (u64_range w) as Uw.
  apply img_iff in Hi. rewrite <- (Z_to_bv_bv_unsigned 64 w). apply HT.
  destruct (Z.lt_ge_cases (bv_unsigned w) 0xef000); [lia|]. exfalso. apply Hnrw.
  exists 0xef000, 0x124000. split; [left; reflexivity | lia].
Qed.

Lemma sx_locale_cell : forall s M, sx_inv U1ST s M -> cell M 0x1023e8 8 0x1226e0.
Proof.
  intros s M (HP & _ & _). unfold cell.
  etransitivity; [unshelve eapply (rdn_of_pins RSEGS D_SX M 8%nat 0x1023e8 _ HP); [ | lia | lia | vm_compute; reflexivity]|].
  f_equal. apply byte_list_eq; vm_compute; reflexivity.
Qed.

Lemma common_cells_lookup :
  Forall (fun c : Z * nat * Z => match c with (a, w, v) =>
    exists zs, lookup_runs D_SX a w = Some zs /\ map (Z_to_bv 8) zs = word_to_le_bytes w (Z_to_bv 64 v) end) exit_cxx_common.
Proof.
  unfold exit_cxx_common.
  repeat (apply Forall_cons; [eexists; split; [vm_compute; reflexivity | apply byte_list_eq; vm_compute; reflexivity] |]).
  apply Forall_nil.
Qed.

Lemma common_cells_range : Forall (fun c : Z * nat * Z => match c with (a, w, v) =>
    0xf0200 <= a /\ a + Z.of_nat w <= 0x1226e0 end) exit_cxx_common.
Proof.
  assert (HA : forallb (fun c : Z * nat * Z => let '(a, w, v) := c in ((0xf0200 <=? a) && (a + Z.of_nat w <=? 0x1226e0))%bool) exit_cxx_common = true)
    by (vm_compute; reflexivity).
  apply Forall_forall. intros [[a w] v] Hin. pose proof (proj1 (forallb_forall _ _) HA _ Hin) as HB.
  cbv beta iota in HB |- *. apply andb_prop in HB as [H0 H1]. apply Z.leb_le in H0, H1. lia.
Qed.

Lemma sx_cxx_common : forall s M, sx_inv U1ST s M -> cells_ok M exit_cxx_common.
Proof.
  intros s M SXI. destruct SXI as (HP & _ & _).
  unfold cells_ok. apply Forall_forall. intros [[a w] v] Hin.
  pose proof (proj1 (Forall_forall _ _) common_cells_lookup _ Hin) as HLk. cbn beta iota in HLk.
  destruct HLk as (zs & HLk & HE).
  pose proof (proj1 (Forall_forall _ _) common_cells_range _ Hin) as HR. cbn beta iota in HR.
  rewrite <- HE. apply (rdn_of_pins RSEGS D_SX M w a zs HP); [lia | lia | exact HLk].
Qed.

Lemma tmem_cxx_t_cells : forall s M sp0 tid k, sx_inv U1ST s M -> tmem sp0 tid k 0 M -> cxx_cells_t_ok M.
Proof.
  intros s M sp0 tid k SXI TM. unfold cxx_cells_t_ok, cells_ok. rewrite exit_cxx_cells_t_split. apply Forall_app. split.
  - exact (sx_cxx_common s M SXI).
  - unfold exit_t_cells. destruct TM as [_ _ _ TS1 TF1 TA1 TCB _ _ _]. unfold cell, AT_SLOT, AT_F1, AT_A1, AT_CALL, AEF_GUARD, AEF_CB in *.
    repeat apply Forall_cons; try apply Forall_nil; assumption.
Qed.

Section TS.
Context {AC : AllocCeiling}.
  Context {AMB : Amb}.
  Variable MI : MallocIface SEGS L.
  Variables (sp0 tid : Z) (content : list byte) (fs0 : Fs) (p cap : Z) (R0 : bvmap 5 word).
  Hypothesis Hsp : 0x7fff80000000 <= sp0 <= 0x800000000000 /\ sp0 mod 16 = 0.
  Hypothesis Hcap : 0x124000 <= p /\ p + cap <= alloc_ceiling /\ 65536 <= cap <= 2 ^ 26.
  Hypothesis HL6 : 6 + hdr_cfglen content <= Z.of_nat (length content) < 2 ^ 26.

  Hypothesis HAC : alloc_ceiling = sp0 - 8388608.

  Definition tn : Z := hdr_paylen content.
  Definition tcfglen : Z := hdr_cfglen content.
  Definition tpayload : list byte := skipn (Z.to_nat (6 + hdr_cfglen content)) content.
  Definition tLV (obj : Z) : list (Z * Z) := if 0 <? tn then [(p, cap); (obj, tn)] else [(p, cap)].

  Lemma cfglen_range : 0 <= hdr_cfglen content < 32768.
  Proof. clear Hsp Hcap HL6. unfold hdr_cfglen. apply Z.mod_pos_bound. lia. Qed.

  Lemma tn_range : 0 <= tn < 2 ^ 26.
  Proof. clear Hsp Hcap. unfold tn, hdr_paylen. pose proof cfglen_range. lia. Qed.

  Lemma tpayload_length : Z.of_nat (length tpayload) = tn.
  Proof. clear Hsp Hcap. unfold tpayload, tn, hdr_paylen. rewrite length_skipn. pose proof cfglen_range. lia. Qed.

  Record tregs (c obj q : Z) (R : bvmap 5 word) : Prop := {
    tg_sp : getr R 2 = Z_to_bv 64 (sp0 - 208);
    tg_gp : getr R 3 = Z_to_bv 64 0x10800;
    tg_tp : getr R 4 = Z_to_bv 64 0x102418;
    tg_s0 : getr R 8 = Z_to_bv 64 tn;
    tg_s1 : getr R 9 = Z_to_bv 64 obj;
    tg_s2 : getr R 18 = Z_to_bv 64 q;
    tg_s4 : getr R 20 = Z_to_bv 64 INITIALIZED;
    tg_s5 : getr R 21 = Z_to_bv 64 c;
    tg_s6 : getr R 22 = Z_to_bv 64 0;
    tg_s7 : getr R 23 = Z_to_bv 64 MINUS2
  }.

  Lemma tregs_kept : forall c obj q R R', tregs c obj q R -> kept R R' -> tregs c obj q R'.
  Proof.
    intros c obj q R R' TG K. clear Hsp Hcap HL6. destruct TG. constructor; (rewrite K; [assumption | cbv; tauto]).
  Qed.

  Record tcore (k : nat) (b : Z) (obj q : Z) (A : AS MI) (M : LibIface.mem) (model : Model) : Prop := {
    tc_mem  : tmem sp0 tid k b M;
    tc_abs  : tabs MI A M model;
    tc_sx   : sx_inv U1ST true M;
    tc_trf  : tr_frame sp0 R0 M;
    tc_mf   : main_frame sp0 M;
    tc_live : forall x, In x (live MI A) <-> In x (tLV obj);
    tc_obj  : (tn = 0 /\ obj = EMPTY /\ q = 0) \/ (0 < tn /\ q = obj /\ obj <> p);
    tc_payload : rdn RSEGS M (Z_to_bv 64 obj) (Z.to_nat tn) = Some tpayload;
    tc_fs   : m_fs model = fs0
  }.

  Lemma tLV_buf : forall obj, In (p, cap) (tLV obj).
  Proof. clear Hsp Hcap HL6. intros obj. unfold tLV. destruct (0 <? tn); left; reflexivity. Qed.

  Lemma tLV_obj : forall obj, 0 < tn -> In (obj, tn) (tLV obj).
  Proof. clear Hsp Hcap HL6. intros obj Hn. unfold tLV. destruct (Z.ltb_spec 0 tn); [right; left; reflexivity | lia]. Qed.

  Lemma tLV_cases : forall obj x, In x (tLV obj) -> x = (p, cap) \/ (x = (obj, tn) /\ 0 < tn).
  Proof.
    clear Hsp Hcap HL6. intros obj x Hx. unfold tLV in Hx. destruct (Z.ltb_spec 0 tn).
    - destruct Hx as [<-|[<-|[]]]; [left; reflexivity | right; split; [reflexivity | lia]].
    - destruct Hx as [<-|[]]. left; reflexivity.
  Qed.

  Lemma tLV_length : forall obj, (length (tLV obj) <= 2)%nat.
  Proof. clear Hsp Hcap HL6. intros obj. unfold tLV. destruct (0 <? tn); cbn; lia. Qed.

  Section Core.
    Variables (k : nat) (b obj q : Z) (A : AS MI) (M : LibIface.mem) (model : Model).
    Hypothesis TC : tcore k b obj q A M model.

    Let AI := ta_ainv MI A M model (tc_abs _ _ _ _ _ _ _ TC).

    Lemma core_live_buf : In (p, cap) (live MI A).
    Proof. apply (tc_live _ _ _ _ _ _ _ TC). apply tLV_buf. Qed.

    Lemma core_live_obj : 0 < tn -> In (obj, tn) (live MI A).
    Proof. intros Hn. apply (tc_live _ _ _ _ _ _ _ TC). apply tLV_obj. exact Hn. Qed.

    Lemma core_live_len : (length (live MI A) <= 2)%nat.
    Proof.
      eapply Nat.le_trans; [|apply (tLV_length obj)].
      apply NoDup_fst_length_le; [exact (ai_live_nodup MI A M model AI)|]. intros x Hx. apply (tc_live _ _ _ _ _ _ _ TC). exact Hx.
    Qed.

    Lemma core_live_bound : forall q' k', In (q', k') (live MI A) -> 0 < k' <= 2 ^ 26.
    Proof.
      clear Hsp. intros q' k' Hin. apply (tc_live _ _ _ _ _ _ _ TC) in Hin. pose proof tn_range.
      destruct (tLV_cases obj _ Hin) as [E|[E Hn]]; injection E as -> ->; lia.
    Qed.

    Lemma core_obj16 : obj mod 16 = 0.
    Proof.
      destruct (tc_obj _ _ _ _ _ _ _ TC) as [(Hn & -> & _)|(Hn & _)]; [reflexivity|].
      destruct (ai_live_block MI A M model obj tn AI (core_live_obj Hn)) as (_ & H & _). exact H.
    Qed.

    Lemma core_obj_range : 0 < tn -> 0 < obj /\ obj + tn <= alloc_ceiling
      /\ (forall a, obj <= a < obj + tn -> ~ owned MI A a /\ ~ in_ranges (ly_img L) a /\ M (Z_to_bv 64 a) <> None).
    Proof.
      clear Hsp Hcap HL6. intros Hn. destruct (ai_live_block MI A M model obj tn AI (core_live_obj Hn)) as (_ & _ & H1 & H2 & H3). repeat split; try lia; apply H3; assumption.
    Qed.

    Lemma core_text : img_clear M 0x10000 0xef000.
    Proof. exact (tm_text _ _ _ _ _ (tc_mem _ _ _ _ _ _ _ TC)). Qed.

    Lemma core_ro_clear : ro_clear L M.
    Proof. apply ro_clear_of_text. apply core_text. Qed.

    Lemma core_img_ro_clear : img_ro_clear L M.
    Proof. apply img_ro_clear_of_text. apply core_text. Qed.

    Lemma core_owned_not_sx : forall a, owned MI A a -> ~ sx_region U1ST a.
    Proof.
      intros a Ho Hs. apply (sx_region_not_static a Hs). apply (ta_own MI A M model (tc_abs _ _ _ _ _ _ _ TC) a Ho).
      apply img_iff. pose proof (sx_region_img a Hs). lia.
    Qed.

    Lemma core_stack_room : forall S, 0 <= S <= 8388608 - 208 -> stack_room RSEGS M (sp0 - 208) S.
    Proof.
      clear Hsp Hcap HL6. intros S HS. unfold stack_room.
      replace (Z_to_bv 64 (sp0 - 208 - S)) with (Z_to_bv 64 (sp0 - 8388608 + (8388608 - 208 - S))) by (f_equal; lia).
      apply (tm_stack _ _ _ _ _ (tc_mem _ _ _ _ _ _ _ TC)); lia.
    Qed.

    Lemma core_win_clear : forall S a, 0 <= S <= 8388608 - 208 -> zwin (sp0 - 208 - S) (sp0 - 208) a ->
      ~ owned MI A a /\ ~ sx_region U1ST a.
    Proof.
      clear Hcap HL6. intros S a HS Hw. unfold zwin in Hw. pose proof ac_bounds_lit as Hcv. split.
      - exact (high_not_owned MI A M model a AI ltac:(lia)).
      - exact (high_not_sx a ltac:(lia)).
    Qed.

    Lemma core_locale : rdn RSEGS M (Z_to_bv 64 0x1023e8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1226e0)).
    Proof. exact (sx_locale_cell true M (tc_sx _ _ _ _ _ _ _ TC)). Qed.

    Lemma core_caps : caps MI A = lib_caps /\ bigcap MI A = LIB_BIGCAP.
    Proof. split; [exact (ta_caps MI A M model (tc_abs _ _ _ _ _ _ _ TC)) | exact (ta_big MI A M model (tc_abs _ _ _ _ _ _ _ TC))]. Qed.

    Lemma core_obj_cases : (tn = 0 /\ obj = EMPTY) \/ (0 < tn /\ In (obj, tn) (live MI A)).
    Proof.
      destruct (tc_obj _ _ _ _ _ _ _ TC) as [(Hn & Ho & _)|(Hn & _)]; [left; split; assumption | right].
      split; [exact Hn | exact (core_live_obj Hn)].
    Qed.
  End Core.

  Lemma sx_transport : forall A M M' model (F : Z -> Prop),
    sx_inv U1ST true M -> tabs MI A M model -> frame_eq F M M' ->
    (forall a, F a -> 0x10000 <= a < 0x124000 -> owned MI A a \/ errno_win L a) ->
    sx_inv U1ST true M'.
  Proof.
    intros A M M' model F SX TA FR HC. clear Hsp Hcap HL6.
    eapply (sx_frame U1ST true M M' SX). eapply frame_eq_same_on; [exact FR|].
    intros a [Hs|Hr] HF.
    - pose proof (sx_region_img a Hs) as Hi. destruct (HC a HF ltac:(lia)) as [Ho|He].
      + apply (sx_region_not_static a Hs). apply (ta_own MI A M model TA a Ho). apply img_iff. lia.
      + exact (errno_not_sx a He Hs).
    - destruct Hr as (lo & hi & Hin & Hr). cbn in Hin. destruct Hin as [E|[]]. injection E as <- <-.
      destruct (HC a HF ltac:(lia)) as [Ho|He].
      + pose proof (ta_own MI A M model TA a Ho ltac:(apply img_iff; lia)) as Hm. unfold mng_static in Hm. lia.
      + apply (proj1 (errno_win_val a)) in He. lia.
  Qed.

  Lemma tcore_after_lib : forall k b obj q A A' (s' : SX U1ST) M M' model model',
    tcore k b obj q A M model ->
    ainv MI A' M' model' -> mstd model' -> m_fs model' = m_fs model -> m_fds model' = m_fds model ->
    sx_inv U1ST s' M' -> sx_le U1ST true s' ->
    (forall x, In x (live MI A') <-> In x (live MI A)) ->
    eff MI A A' M M' (sp0 - 208 - LIB_STACK, sp0 - 208) (sx_region U1ST) ->
    tcore k b obj q A' M' model'.
  Proof.
    intros k b obj q A A' s' M M' model model' TC AI' MS' FS FDS SX' LE LV EF.
    pose proof ac_bounds_lit as Hcv.
    pose proof (ta_ainv MI A M model (tc_abs _ _ _ _ _ _ _ TC)) as AI.
    destruct (tstep_lib MI sp0 tid Hsp HAC k b A A' M M' model model' (tc_mem _ _ _ _ _ _ _ TC) (tc_abs _ _ _ _ _ _ _ TC) AI' MS' FDS EF)
      as (TM' & TA' & AGS).
    assert (Es : s' = true) by (apply LE; reflexivity). subst s'.
    constructor.
    - exact TM'.
    - exact TA'.
    - exact SX'.
    - eapply tr_frame_agree; [ | lia | exact (tc_trf _ _ _ _ _ _ _ TC)]. intros i Hi. apply AGS. lia.
    - eapply main_frame_frame; [lia | lia | | exact (tc_mf _ _ _ _ _ _ _ TC)]. intros i Hi. apply AGS. lia.
    - intros x. rewrite LV. apply (tc_live _ _ _ _ _ _ _ TC).
    - exact (tc_obj _ _ _ _ _ _ _ TC).
    -
      pose proof tn_range as TN.
      destruct (tc_obj _ _ _ _ _ _ _ TC) as [(Hn & Ho & _)|(Hn & _)].
      + rewrite Hn. rewrite Hn in *. cbn. pose proof (tc_payload _ _ _ _ _ _ _ TC) as PL. rewrite Hn in PL. cbn in PL. exact PL.
      + rewrite <- (tc_payload _ _ _ _ _ _ _ TC).
        destruct (core_obj_range k b obj q A M model TC Hn) as (Ho1 & Ho2 & HB).
        assert (HinA' : In (obj, tn) (live MI A')) by (apply LV; apply (core_live_obj k b obj q A M model TC Hn)).
        destruct (ai_live_block MI A' M' model' obj tn AI' HinA') as (_ & _ & _ & _ & HB').
        apply rdn_ext; [rewrite u64_lit by lia; lia|]. intros x Hx. rewrite u64_lit in Hx by lia.
        destruct EF as [C B O FR D OI]. apply FR. intros [H|[H|[H|[H|[H|H]]]]].
        * exact (proj1 (HB (bv_unsigned x) ltac:(lia)) H).
        * exact (proj1 (HB' (bv_unsigned x) ltac:(lia)) H).
        * destruct H as (_ & _ & Hn0). apply (proj2 (proj2 (HB (bv_unsigned x) ltac:(lia)))). exact Hn0.
        * pose proof (sx_region_img _ H). apply (proj1 (proj2 (HB (bv_unsigned x) ltac:(lia)))). apply img_iff. lia.
        * unfold W_of, LIB_STACK in H. cbn [fst snd] in H. lia.
        * apply (proj1 (errno_win_val _)) in H. apply (proj1 (proj2 (HB (bv_unsigned x) ltac:(lia)))). apply img_iff. lia.
    - rewrite FS. exact (tc_fs _ _ _ _ _ _ _ TC).
  Qed.

  Lemma tcore_set_cb : forall k b b' obj q A M M' model,
    tcore k b obj q A M model -> frame_mod M M' aef_region -> cell M' AEF_CB 1 b' -> tcore k b' obj q A M' model.
  Proof.
    intros k b b' obj q A M M' model TC FM HC. pose proof FM as [FE FG]. pose proof ac_bounds_lit as Hcv.
    pose proof (tc_abs _ _ _ _ _ _ _ TC) as TA. pose proof (ta_ainv MI A M model TA) as AI.
    assert (OUTw : forall a : word, bv_unsigned a <> AEF_CB -> M' a = M a).
    { intros a Hne. apply FE. unfold aef_region, AEF_CB in *. cbn [outside]. unfold in_rng. rewrite !u64_lit by lia.
      pose proof (u64_range a). split; [lia | exact I]. }
    assert (OUT : forall i, 0 <= i < 2 ^ 64 -> i <> AEF_CB -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros i Hi Hne. apply OUTw. rewrite u64_lit by lia. exact Hne. }
    assert (AEFd : in_ivs dimg_ivs AEF_CB).
    { unfold dimg_ivs, AEF_CB. apply in_ivs_app. left. exists 0x100254, 0x100255. split; [cbn; tauto | lia]. }
    constructor.
    - eapply (tmem_set_cb sp0 tid Hsp); [exact (tc_mem _ _ _ _ _ _ _ TC) | exact FM | exact HC].
    - constructor; try (destruct TA; assumption).
      eapply (ai_frame MI A M M' model model AI); [ | exact FG | reflexivity | reflexivity].
      intros a Ho. apply OUTw. intros E. apply (dimg_not_owned MI A M model (bv_unsigned a) TA); [rewrite E; exact AEFd | exact Ho].
    - eapply (sx_frame U1ST true M M' (tc_sx _ _ _ _ _ _ _ TC)). intros a [Hs|Hr]; apply OUTw; intros E.
      + apply (dimg_not_sx (bv_unsigned a)); [rewrite E; exact AEFd | exact Hs].
      + destruct Hr as (lo & hi & Hin & Hlh). cbn in Hin. destruct Hin as [E2|[]]. injection E2 as <- <-. unfold AEF_CB in E. lia.
    - eapply tr_frame_agree; [ | lia | exact (tc_trf _ _ _ _ _ _ _ TC)]. intros i Hi. apply OUT; unfold AEF_CB; lia.
    - eapply main_frame_frame; [lia | lia | | exact (tc_mf _ _ _ _ _ _ _ TC)]. intros i Hi. apply OUT; unfold AEF_CB; lia.
    - exact (tc_live _ _ _ _ _ _ _ TC).
    - exact (tc_obj _ _ _ _ _ _ _ TC).
    - rewrite <- (tc_payload _ _ _ _ _ _ _ TC). pose proof tn_range as TNR.
      destruct (tc_obj _ _ _ _ _ _ _ TC) as [(Hn & _ & _)|(Hn & _ & _)]; [rewrite Hn; reflexivity|].
      destruct (core_obj_range _ _ _ _ _ _ _ TC Hn) as (Ho1 & Ho2 & HB).
      apply rdn_ext; [rewrite u64_lit by lia; lia|]. intros x Hx. rewrite u64_lit in Hx by lia.
      apply OUTw. intros E. apply (proj1 (proj2 (HB (bv_unsigned x) ltac:(lia)))). apply img_iff. rewrite E. unfold AEF_CB. cbn. lia.
    - exact (tc_fs _ _ _ _ _ _ _ TC).
  Qed.

End TS.
