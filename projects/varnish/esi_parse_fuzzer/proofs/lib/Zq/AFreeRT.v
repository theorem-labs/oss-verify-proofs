(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Classical_Prop.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Ledger Hull Restrict.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState ADepotM.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AQWf.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AQWf ATransp ATranspR AFreeRS.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AQWf.AQOps OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AQWf OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ATransp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ATranspR OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeRS.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.

Notation wz z := (Z_to_bv 64 z) (only parsing).

Section RT.
Context {Clg : Ceiling}.

  (* [comment removed for export] *)
  Lemma WFT_of_WFR : forall A, WFR A -> WFT A.
  Proof.
    intros A W. destruct W as [rP rM rR rC rX rV rQ (rL1 & rL2 & rL3 & rL4) rS rD rF rB rT rI rE rJ].
    (first [ dand8 rQ as Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 | destruct rQ as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8) ]).
    constructor; rewrite ?rT; try assumption.
    split; [constructor|]. split.
    { apply Forall_app. split; [| exact rL1]. eapply Forall_impl; [| exact Q2]. intros b Hb. exact (wf_batch0_of _ _ _ Hb). }
    repeat (split; [exact I|]). exact (conj rL2 (conj rL3 rL4)).
  Qed.

  (* [comment removed for export] *)
  Lemma owned_casesT : forall A a, WFT A -> pa_owned A a ->
    cl_static LPA a \/ in_regions (runtime_maps A) a \/ in_shadow_maps a.
  Proof.
    intros A a W OW. destruct OW as [[S|[[(IR & _ & _)|[HS|[FS _]]]|[GH _]]]|IS].
    - left. exact S.
    - right; left. exact IR.
    - right; right. exact (heap_shadow_rangeT A a W HS).
    - right; right. exact (fs_shadow_in_mapsT A a W FS).
    - right; right. exact GH.
    - right; right. exact (image_shadow_in_maps a IS).
  Qed.

  Lemma owned_whereT : forall A a, WFT A -> pa_owned A a -> cl_static LPA a \/ heap_zone LPA a.
  Proof.
    intros A a W OW. pose proof alloc_ceiling_val as CE.
    unfold heap_zone, in_image. cbn [cl_image_lo cl_image_hi LPA].
    destruct (owned_casesT A a W OW) as [S|[IR|SM]]; [left; exact S| |]; right.
    - (first [ dex2 IR as b s; destruct IR as [Hin Hab] | dand4 IR as b s Hin Hab | destruct IR as (b & s & Hin & Hab) ]). pose proof (runtime_maps_rangeT A b s a W Hin Hab). cbn [al_image_lo al_image_hi AL_pboth] in H.
      unfold kHighMemBeg, kLowShadowMapBeg in *. lia.
    - unfold in_shadow_maps, kLowShadowMapBeg, kHighShadowMapBeg, kHighShadowMapSize in *. lia.
  Qed.

  (* [comment removed for export] *)

  Lemma owned_below_ceilingT : forall A a, WFT A -> pa_owned A a -> a < alloc_ceiling.
  Proof.
    intros A a W OW. pose proof alloc_ceiling_val. destruct (owned_whereT A a W OW) as [S|HZ].
    - cbn [cl_static LPA] in S. unfold pa_static in S. lia.
    - unfold heap_zone in HZ. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma runtime_maps_ext : forall P reg reg' sec,
    (forall c, 1 <= c <= 30 -> rg_mapped_user (reg' c) = rg_mapped_user (reg c) /\ rg_mapped_fa (reg' c) = rg_mapped_fa (reg c)) ->
    runtime_maps_ P reg' sec = runtime_maps_ P reg sec.
  Proof.
    intros P reg reg' sec E. unfold runtime_maps_. f_equal. f_equal. rewrite !flat_map_concat_map. f_equal.
    apply map_ext_in. intros c Hc. apply in_map_iff in Hc as (n & <- & Hn). apply in_seq in Hn.
    destruct (E (Z.of_nat n) ltac:(lia)) as [E1 E2]. cbv zeta. rewrite E1, E2. reflexivity.
  Qed.
  Lemma heap_shadow_ext : forall sb reg reg' sec a,
    (forall c, 1 <= c <= 30 -> rg_mapped_user (reg' c) = rg_mapped_user (reg c) /\ rg_mapped_fa (reg' c) = rg_mapped_fa (reg c)) ->
    heap_shadow_ sb reg' sec a <-> heap_shadow_ sb reg sec a.
  Proof.
    intros sb reg reg' sec a E. unfold heap_shadow_. cbv zeta.
    split; intros [(c & Hc & X)|[(c & Hc & X)|X]];
      first [ left; exists c; split; [exact Hc|]; destruct (E c Hc) as [E1 E2]; rewrite <- ?E1, <- ?E2; exact X
            | left; exists c; split; [exact Hc|]; destruct (E c Hc) as [E1 E2]; rewrite ?E1, ?E2; exact X
            | right; left; exists c; split; [exact Hc|]; destruct (E c Hc) as [E1 E2]; rewrite <- ?E1, <- ?E2; exact X
            | right; left; exists c; split; [exact Hc|]; destruct (E c Hc) as [E1 E2]; rewrite ?E1, ?E2; exact X
            | right; right; exact X ].
  Qed.
  Lemma owned_iff_ext : forall A A' a,
    a_pl A' = a_pl A -> a_livemap A' = a_livemap A -> a_sec A' = a_sec A -> a_fframes A' = a_fframes A ->
    (forall c, 1 <= c <= 30 -> rg_mapped_user (a_reg A' c) = rg_mapped_user (a_reg A c) /\ rg_mapped_fa (a_reg A' c) = rg_mapped_fa (a_reg A c)) ->
    pa_owned A' a <-> pa_owned A a.
  Proof.
    intros A A' a EP EL ES EF ER. unfold pa_owned, aowned, aowned_, runtime_maps, a_sb, a_fs. rewrite EP, EL, ES, EF.
    rewrite (runtime_maps_ext (a_pl A) (a_reg A) (a_reg A') (a_sec A) ER).
    pose proof (heap_shadow_ext (p_sb (a_pl A)) (a_reg A) (a_reg A') (a_sec A) a ER) as HS. tauto.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition rstep (O1 O2 : Z -> Prop) (lo whi : Z) (v1 v2 : mem) : Prop :=
    (forall a, 0 <= a < 2^64 -> ~ O1 a -> ~ O2 a -> ~ (lo <= a < whi) -> v2 (wz a) = v1 (wz a)) /\
    (forall a, 0 <= a < 2^64 -> ~ in_image LPA a -> v1 (wz a) <> None -> O1 a \/ v2 (wz a) <> None) /\
    mapped v2 lo (whi - lo) /\
    (forall a, 0 <= a < 2^64 -> O2 a -> O1 a \/ (v1 (wz a) = None /\ heap_zone LPA a)) /\
    (forall a, 0 <= a < 2^64 -> O1 a -> ~ O2 a -> v2 (wz a) = None).

  Lemma errno_in_image : forall a, cl_errno LPA <= a < cl_errno LPA + 4 -> in_image LPA a.
  Proof. intros a Ha. unfold in_image. cbn [cl_errno cl_image_lo cl_image_hi LPA] in *. lia. Qed.

  (* [comment removed for export] *)
  Lemma frame_ok_rstep : forall (O0 O1 O2 VIC : Z -> Prop) (lo whi : Z) (v0 v1 v2 : mem),
    (forall a, O1 a -> a < lo) -> (forall a, VIC a -> a < lo) -> (forall a, heap_zone LPA a -> a < lo) ->
    frame_ok LPA O0 O1 whi (whi - lo) VIC nowhere v0 v1 -> rstep O1 O2 lo whi v1 v2 ->
    frame_ok LPA O0 O2 whi (whi - lo) VIC nowhere v0 v2.
  Proof.
    (intros O0 O1 O2 VIC lo whi v0 v1 v2 OB VB HB; (first [ intro dR_3; dand7 dR_3 as F1 F2 F3 F4 F5 F6 F7 | intros (F1 & F2 & F3 & F4 & F5 & F6 & F7) ]); (first [ intro dR_4; dand5 dR_4 as R1 R2 R3 R5 R6 | intros (R1 & R2 & R3 & R5 & R6) ])).
    unfold frame_ok in *. replace (whi - (whi - lo)) with lo in * by lia.
    assert (HZN : forall a, heap_zone LPA a -> ~ in_image LPA a) by (intros a [_ NI]; exact NI).
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits.
    - (* [comment removed for export] *)
      intros a Ha N0 N2 NW NE NV _. destruct (classic (O1 a)) as [O1a|N1].
      + destruct (F5 a Ha O1a) as [O0a|[Va|[V0 HZ]]]; [exact (False_ind _ (N0 O0a))| exact (False_ind _ (NV Va)) |].
        rewrite V0. exact (R6 a Ha O1a N2).
      + rewrite (R1 a Ha N1 N2 NW). exact (F1 a Ha N0 N1 NW NE NV ltac:(intros [])).
    - (* [comment removed for export] *)
      intros a Ha NI Hv0. destruct (F2 a Ha NI Hv0) as [O0a|[Va|Hv1]]; [left; exact O0a| right; left; exact Va|].
      destruct (R2 a Ha NI Hv1) as [O1a|Hv2]; [| right; right; exact Hv2].
      destruct (F5 a Ha O1a) as [O0a|[Va|[V0 _]]]; [left; exact O0a| right; left; exact Va | exfalso; exact (Hv0 V0)].
    - exact R3.
    - intros a Ha [].
    - (* [comment removed for export] *)
      intros a Ha O2a. destruct (classic (O1 a)) as [O1a|N1]; [exact (F5 a Ha O1a)|].
      destruct (R5 a Ha O2a) as [O1a|[V1 HZ]]; [exact (False_ind _ (N1 O1a))|].
      destruct (classic (O0 a)) as [O0a|N0]; [left; exact O0a|]. destruct (classic (VIC a)) as [Va|NV]; [right; left; exact Va|].
      right; right. split; [| exact HZ]. rewrite <- V1. symmetry.
      apply (F1 a Ha N0 N1); [pose proof (HB a HZ); lia| intros E; exact (HZN a HZ (errno_in_image a E))| exact NV| intros []].
    - (* [comment removed for export] *)
      intros a Ha O0a N2. right. destruct (classic (O1 a)) as [O1a|N1]; [exact (R6 a Ha O1a N2)|].
      destruct (F6 a Ha O0a N1) as [[]|V1].
      destruct (classic (lo <= a < whi)) as [W|NW].
      + exfalso. pose proof (F3 (a - lo) ltac:(lia)) as M. replace (lo + (a - lo)) with a in M by lia. exact (M V1).
      + rewrite (R1 a Ha N1 N2 NW). exact V1.
    - (* [comment removed for export] *)
      intros a Ha Va. destruct (classic (O2 a)) as [O2a|N2]; [left; exact O2a|]. right; right.
      destruct (classic (O1 a)) as [O1a|N1]; [exact (R6 a Ha O1a N2)|].
      destruct (F7 a Ha Va) as [O1a|[[]|V1]]; [exact (False_ind _ (N1 O1a))|].
      rewrite (R1 a Ha N1 N2 ltac:(pose proof (VB a Va); lia)). exact V1.
  Qed.

  (* [comment removed for export] *)
  Lemma rstep_window : forall (O : Z -> Prop) lo whi (v1 v2 : mem),
    (forall a, 0 <= a < 2^64 -> ~ (lo <= a < whi) -> v2 (wz a) = v1 (wz a)) ->
    mapped v2 lo (whi - lo) -> (forall a, O a -> a < lo) ->
    rstep O O lo whi v1 v2.
  Proof.
    intros O lo whi v1 v2 AG M OB. unfold rstep. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits.
    - intros a Ha _ _ NW. exact (AG a Ha NW).
    - intros a Ha NI Hv. destruct (classic (lo <= a < whi)) as [W|NW].
      + right. pose proof (M (a - lo) ltac:(lia)) as X. replace (lo + (a - lo)) with a in X by lia. exact X.
      + right. rewrite (AG a Ha NW). exact Hv.
    - exact M.
    - intros a Ha Oa. left. exact Oa.
    - intros a Ha Oa NO. exact (False_ind _ (NO Oa)).
  Qed.

  (* [comment removed for export] *)
  Record RHIST (A0 : AState) (v0 : mem) (md0 : Model) (p n0 spd lo hi : Z) (A : AState) (v : mem) (md : Model) : Prop := {
    rh_pl : a_pl A = a_pl A0;
    rh_frames : a_fframes A = a_fframes A0;
    rh_fhint : a_fhint A = a_fhint A0;
    rh_live : a_livemap A = delete p (a_livemap A0);
    rh_tiny : a_tiny A = a_tiny A0;
    rh_scred : a_scred A = a_scred A0;
    rh_pcred : a_pcred A = a_pcred A0;   (* [comment removed for export] *)
    rh_virgin : forall c, c <> kQuarantineBatchClass -> a_virgin A0 c -> a_virgin A c;
    rh_amd : amd_frame md0 md;
    rh_errno : forall i, 0 <= i < 4 -> v (wz (cl_errno LPA + i)) = v0 (wz (cl_errno LPA + i));
    rh_frame : frame_ok LPA (pa_owned A0) (pa_owned A) spd (spd - lo) (newblk p n0) nowhere v0 v;
    rh_above : forall a, spd <= a < hi -> v (wz a) = v0 (wz a) }.

  (* [comment removed for export] *)
  Lemma RHIST_step : forall A0 v0 md0 p n0 spd lo hi A v md A' v' md',
    RHIST A0 v0 md0 p n0 spd lo hi A v md ->
    WFT A -> WFT A' -> alloc_ceiling <= lo -> lo <= spd -> spd <= hi -> hi <= 2^47 ->
    (forall a, newblk p n0 a -> a < alloc_ceiling) ->
    a_pl A' = a_pl A -> a_fframes A' = a_fframes A -> a_fhint A' = a_fhint A -> a_livemap A' = a_livemap A ->
    a_tiny A' = a_tiny A -> a_scred A' = a_scred A -> a_pcred A' = a_pcred A (* [comment removed for export] *) ->
    (forall c, c <> kQuarantineBatchClass -> a_virgin A c -> a_virgin A' c) ->
    amd_frame md md' ->
    rstep (pa_owned A) (pa_owned A') lo spd v v' ->
    RHIST A0 v0 md0 p n0 spd lo hi A' v' md'.
  Proof.
    intros A0 v0 md0 p n0 spd lo hi A v md A' v' md' H W W' CL LS SH H47 VB EP EF EH EL ET ES EPC VG AM RS.
    pose proof alloc_ceiling_val as CE.
    destruct H as [hP hF hH hL hT hS hPC hV hA hE hFR hAB].
    assert (OB : forall a, pa_owned A a -> a < lo) by (intros a Oa; pose proof (owned_below_ceilingT A a W Oa); lia).
    constructor.
    - rewrite EP. exact hP.
    - rewrite EF. exact hF.
    - rewrite EH. exact hH.
    - rewrite EL. exact hL.
    - rewrite ET. exact hT.
    - rewrite ES. exact hS.
    - rewrite EPC. exact hPC.
    - intros c Hc V0. exact (VG c Hc (hV c Hc V0)).
    - exact (amd_frame_trans _ _ _ hA AM).
    - intros i Hi. rewrite <- (hE i Hi). destruct RS as (R1 & _). apply R1; [cbn [cl_errno LPA]; lia| | | cbn [cl_errno LPA]; lia].
      + intros Oa. pose proof (owned_whereT A _ W Oa) as [St|HZ].
        * exact (proj1 (asI_errno_not_static i Hi) St).
        * destruct HZ as [_ NI]. apply NI. apply errno_in_image. lia.
      + intros Oa. pose proof (owned_whereT A' _ W' Oa) as [St|HZ].
        * exact (proj1 (asI_errno_not_static i Hi) St).
        * destruct HZ as [_ NI]. apply NI. apply errno_in_image. lia.
    - eapply frame_ok_rstep; [exact OB| intros a Va; pose proof (VB a Va); lia| intros a [Ha _]; lia| exact hFR| exact RS].
    - intros a Ha. rewrite <- (hAB a Ha). destruct RS as (R1 & _). apply R1; [lia| | | lia].
      + intros Oa. pose proof (OB a Oa). lia.
      + intros Oa. pose proof (owned_below_ceilingT A' a W' Oa). lia.
  Qed.
End RT.
