(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzArrD BzCMem BzCStream BzCState BzCHuff BzCMtf BzCRebuildF BzCHuffF6 BzCFactsGm BzCSmF1 BzDState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzR5a BzR5bK.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzR5cG.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzR5cW BzR5cE BzR5cS BzR4a BzR4d.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMtf OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCRebuildF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuffF6 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCFactsGm OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCSmF1 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5a OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5bK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5cG.BzR5b OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5cW OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5cE OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5cS OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR4a OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR4d.
Import ListNotations.

From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzParams BzParamsLia.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require CpsOpen.
Module BzR4e.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMtf OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCRebuildF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCFactsGm OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5cS OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR4a.
Import ListNotations.
Local Open Scope Z_scope.

Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzParams OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzParamsLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.
Section ACeilS1. Context {BZP : BzParams}.


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition MTFV (arr1 : zarr) (acc : list Z) : Prop :=
  forall k, (k < length acc)%nat -> mtfv_at arr1 (Z.of_nat k) = nth k acc 0.

Lemma MTFV_emit : forall arr1 acc wr v, MTFV arr1 acc -> wr = Z.of_nat (length acc) -> 0 <= v < 65536 ->
  MTFV (wr16 arr1 (2 * wr) v) (acc ++ [v]).
Proof.
  intros arr1 acc wr v MV W Hv k Hk. rewrite length_app in Hk. cbn [length] in Hk. unfold mtfv_at.
  destruct (Nat.eq_dec k (length acc)) as [->|NE].
  - subst wr. rewrite rd16_wr16_same by exact Hv. rewrite nth_middle. reflexivity.
  - rewrite rd16_wr16_other by lia. rewrite app_nth1 by lia. apply MV. lia.
Qed.

Lemma MTFV_zrun : forall f arr1 mf wr z acc, MTFV arr1 acc -> wr = Z.of_nat (length acc) -> 0 <= z ->
  let '(arr1', mf', wr') := mtf_zrun f arr1 mf wr z in
  MTFV arr1' (acc ++ zdig f z) /\ wr' = Z.of_nat (length (acc ++ zdig f z)).
Proof.
  induction f as [|f IH]; intros arr1 mf wr z acc MV W Hz.
  - cbn [mtf_zrun zdig]. rewrite app_nil_r. split; [exact MV| exact W].
  - rewrite mtf_zrun_S. cbn [zdig]. unfold mtf_emit.
    set (v := if Z.land z 1 =? 0 then BZ_RUNA else BZ_RUNB).
    assert (Ev : (if Z.land z 1 =? 0 then 0 else 1) = v) by (subst v; unfold BZ_RUNA, BZ_RUNB; reflexivity). rewrite Ev.
    assert (Hv : 0 <= v < 65536) by (subst v; unfold BZ_RUNA, BZ_RUNB; destruct (Z.land z 1 =? 0); lia).
    pose proof (MTFV_emit arr1 acc wr v MV W Hv) as MV1.
    destruct (Z.ltb_spec z 2).
    + split; [exact MV1|]. rewrite length_app. cbn [length]. lia.
    + specialize (IH (wr16 arr1 (2 * wr) v) (zincr mf v) (wr + 1) ((z - 2) / 2) (acc ++ [v]) MV1
                     ltac:(rewrite length_app; cbn [length]; lia) ltac:(apply Z.div_pos; lia)).
      destruct (mtf_zrun f _ _ _ _) as [[arr1' mf'] wr']. rewrite <- app_assoc in IH. cbn [app] in IH. exact IH.
Qed.

Section E.
  Variable e : est.
  Hypothesis GF : gm_facts e.
  Let nb : Z := e_nblock e.
  Let nI : Z := gp_nInUse e.
  Let EOB : Z := gp_EOB e.

  (* [comment removed for export] *)
  Definition uval (i : Z) : Z :=
    zget (gp_unseq e) (rd8 (e_arr2 e) (let j := rd32 (e_arr1 e) i - 1 in if j <? 0 then j + e_nblock e else j)).
  Definition ulist (n : nat) : list Z := map (fun i => uval (Z.of_nat i)) (seq 0 n).
  Definition gx (n : nat) : gst := gsteps nI (GST (fun k => k) 0 []) (ulist n).
  (* [comment removed for export] *)
  Definition gsyms : list Z := genc nI EOB (fun k => k) 0 (ulist (Z.to_nat nb)).

  Lemma ulist_S : forall n, ulist (S n) = ulist n ++ [uval (Z.of_nat n)].
  Proof. intros n. unfold ulist. rewrite seq_S, map_app. reflexivity. Qed.
  Lemma ulist_length : forall n, length (ulist n) = n.
  Proof. intros n. unfold ulist. rewrite length_map, length_seq. reflexivity. Qed.
  Lemma uval_range : forall i, 0 <= i < nb -> 0 <= uval i < nI.
  Proof.
    intros i Hi. cps_destruct GF as (BOK1 & BOK2 & NB & DEFI & IU01 & F5 & M1). cps_destruct (maps_facts e GF) as (NI & UB & UJ).
    assert (Enb : nb = e_nblock e) by reflexivity. assert (EnI : nI = gp_nInUse e) by reflexivity.
    unfold uval. pose proof (M1 i ltac:(lia)). apply (fun j H => proj2 (UJ j H)). destruct (Z.ltb_spec (rd32 (e_arr1 e) i - 1) 0); lia.
  Qed.
  Lemma ulist_range : forall n, (Z.of_nat n <= nb) -> Forall (fun u => 0 <= u < nI) (ulist n).
  Proof.
    induction n as [|n IH]; intros Hn; [constructor|]. rewrite ulist_S. apply Forall_app. split; [apply IH; lia|].
    constructor; [apply uval_range; lia| constructor].
  Qed.
  Lemma gx_S : forall n, gx (S n) = gstep nI (gx n) (uval (Z.of_nat n)).
  Proof. intros n. unfold gx. rewrite ulist_S, gsteps_app. reflexivity. Qed.

  (* [comment removed for export] *)
  Definition GX (i : nat) (s : gms) : Prop :=
    GI e (Z.of_nat i) s /\
    (forall k, 0 <= k < nI -> zget (gm_yy s) k = g_M (gx i) k) /\
    gm_zPend s = g_z (gx i) /\ gm_wr s = Z.of_nat (length (g_acc (gx i))) /\ MTFV (gm_arr1 s) (g_acc (gx i)) /\
    MPERM nI (g_M (gx i)).

  Lemma GX_0 : GX 0 (gp_s0 e).
  Proof.
    pose proof (proj1 (maps_facts e GF)) as NI. assert (EnI : nI = gp_nInUse e) by reflexivity.
    split; [apply (gp_s0_GI e GF)|]. unfold gx. cbn [ulist seq map gsteps fold_left g_M g_z g_acc length Z.of_nat gp_s0 gm_yy gm_zPend gm_wr gm_arr1].
    split; [| split; [reflexivity| split; [reflexivity| split; [intros k Hk; cbn in Hk; lia| apply MPERM_id]]]].
    intros k Hk. unfold gp_yy0. rewrite yy_init_get'.
    replace ((0 <=? k) && (k <? 0 + Z.of_nat (Z.to_nat (gp_nInUse e))))%bool with true; [reflexivity|].
    symmetry. apply Bool.andb_true_iff. split; [apply Z.leb_le| apply Z.ltb_lt]; lia.
  Qed.

  Lemma GX_step : forall i s, Z.of_nat i < nb -> GX i s -> GX (S i) (gm_iter (e_arr2 e) (gp_unseq e) nb (Z.of_nat i) s).
  Proof.
    (intros i s Hi; cps_intros (G & YY & ZP & WR & MV & PM)).
    cps_destruct GF as (BOK1 & BOK2 & NB & DEFI & IU01 & F5 & M1). cps_destruct (maps_facts e GF) as (NI & UB & UJ).
    pose proof (gp_EOB_eq e) as EE.
    assert (Enb : nb = e_nblock e) by reflexivity. assert (EnI : nI = gp_nInUse e) by reflexivity. assert (EEOB : EOB = gp_EOB e) by reflexivity.
    split. { replace (Z.of_nat (S i)) with (Z.of_nat i + 1) by lia. apply (gm_iter_GI e GF); [lia| exact G]. }
    cps_pose G as (W0 & Z0 & WZ & YP & MD & SM & BOK & FR & MVB).
    rewrite gx_S. set (g := gx i) in *. set (u := uval (Z.of_nat i)).
    pose proof (uval_range (Z.of_nat i) ltac:(lia)) as Hu. fold u in Hu.
    unfold gm_iter. cbv zeta.
    assert (PTR : rd32 (gm_arr1 s) (Z.of_nat i) = rd32 (e_arr1 e) (Z.of_nat i)) by (unfold rd32; rewrite !FR by lia; reflexivity).
    rewrite !PTR.
    change (zget (gp_unseq e) (rd8 (e_arr2 e) (if rd32 (e_arr1 e) (Z.of_nat i) - 1 <? 0 then rd32 (e_arr1 e) (Z.of_nat i) - 1 + nb else rd32 (e_arr1 e) (Z.of_nat i) - 1)))
      with u.
    cps_pose (mpos_found nI (g_M g) u PM Hu) as (J1 & J2 & J3). set (j := mpos (Z.to_nat nI) (g_M g) u 0) in *.
    unfold gstep. fold j.
    destruct (Z.eqb_spec (zget (gm_yy s) 0) u) as [E0|NE0].
    - (* [comment removed for export] *)
      rewrite (YY 0) in E0 by lia.
      assert (J0 : j = 0) by (destruct (Z.eq_dec j 0); [assumption| exfalso; apply (J3 0); [lia| exact E0]]).
      rewrite J0, Z.eqb_refl. unfold GX. cbn [gm_yy gm_zPend gm_wr gm_arr1 g_M g_z g_acc].
      split; [exact YY|]. split; [rewrite ZP; reflexivity|]. split; [exact WR|]. split; [exact MV| exact PM].
    - assert (J0 : j <> 0) by (intros J0; rewrite J0 in J2; rewrite (YY 0) in NE0 by lia; congruence).
      replace (j =? 0) with false by (symmetry; apply Z.eqb_neq; exact J0).
      (* [comment removed for export] *)
      assert (ZR : let '(arr1, mtfFreq, wr) := (if 0 <? gm_zPend s then mtf_zrun 64 (gm_arr1 s) (gm_mtfFreq s) (gm_wr s) (gm_zPend s - 1)
                                                 else (gm_arr1 s, gm_mtfFreq s, gm_wr s)) in
                   MTFV arr1 (g_acc g ++ zflush (g_z g)) /\ wr = Z.of_nat (length (g_acc g ++ zflush (g_z g))) /\ EMI e arr1 mtfFreq wr).
      { unfold zflush. rewrite <- ZP. destruct (Z.ltb_spec 0 (gm_zPend s)).
        - pose proof (MTFV_zrun 64 (gm_arr1 s) (gm_mtfFreq s) (gm_wr s) (gm_zPend s - 1) (g_acc g) MV WR ltac:(lia)) as ZO.
          pose proof (zrun_ok e GF 64 (gm_arr1 s) (gm_mtfFreq s) (gm_wr s) (gm_zPend s - 1) (GI_EMI e (Z.of_nat i) s G) ltac:(lia)) as ZE.
          destruct (mtf_zrun 64 _ _ _ _) as [[a1 mf1] wr1]. destruct ZO as [ZO1 ZO2]. destruct ZE as [_ ZE]. split; [exact ZO1|]. split; [exact ZO2| exact ZE].
        - rewrite app_nil_r. split; [exact MV|]. split; [exact WR| exact (GI_EMI e (Z.of_nat i) s G)]. }
      destruct (if 0 <? gm_zPend s then _ else _) as [[arr1 mf] wr]. cps_destruct ZR as (ZM & ZW & ZE).
      (* [comment removed for export] *)
      destruct YP as [YR YS].
      assert (N1 : 1 < nI) by (pose proof (proj1 PM 0 ltac:(lia)); lia).
      pose proof (search_ok e 258 (zset (gm_yy s) 1 (zget (gm_yy s) 0)) u (zget (gm_yy s) 1) 1 (gm_yy s) (conj YR YS) Hu ltac:(lia)
                    ltac:(intros k Hk; replace k with 1 by lia; rewrite zget_zset_same, zdef_zset_same; replace (1 - 1) with 0 by lia; split; reflexivity)
                    ltac:(intros k Hk; rewrite zget_zset_other, zdef_zset_other by lia; split; reflexivity) eq_refl N1 ltac:(intros; lia)
                    NE0 ltac:(lia)) as SO.
      destruct (mtf_search 258 (zset (gm_yy s) 1 (zget (gm_yy s) 0)) u (zget (gm_yy s) 1) 1) as [[Y' rtmp'] p']. cps_destruct SO as (R1 & R2 & R3 & R4 & R5).
      (* [comment removed for export] *)
      assert (PJ : p' = j).
      { rewrite (YY p') in R3 by lia. apply (proj2 PM); [lia| lia| rewrite R3, J2; reflexivity]. }
      subst p'. unfold mtf_emit. unfold GX. cbn [gm_yy gm_zPend gm_wr gm_arr1 g_M g_z g_acc].
      split.
      { intros k Hk. rewrite zget_zset. destruct (Z.eqb_spec k 0) as [->|NK].
        - rewrite mtf1_0, R1, <- J2. reflexivity.
        - destruct (Z.le_gt_cases k j).
          + rewrite mtf1_low by lia. destruct (R4 k ltac:(lia)) as [-> _]. apply YY. lia.
          + rewrite mtf1_high by lia. destruct (R5 k ltac:(lia)) as [-> _]. apply YY. lia. }
      split; [reflexivity|]. split; [rewrite ZW, !length_app; cbn [length]; lia|]. split.
      { rewrite app_assoc. apply MTFV_emit; [exact ZM| exact ZW| lia]. }
      apply mtf1_MPERM; [exact PM| lia].
  Qed.

  Lemma GX_all : forall i, Z.of_nat i <= nb -> GX i (gp_st e i).
  Proof.
    induction i as [|i IH]; intros Hi.
    - rewrite gp_st_0. apply GX_0.
    - rewrite gp_st_S. apply GX_step; [lia|]. apply IH. lia.
  Qed.

  (* [comment removed for export] *)
  Theorem generateMTFValues_mtfv :
    let e' := fst (generateMTFValues e znew) in
    e_nMTF e' = Z.of_nat (length gsyms) /\
    (forall k, (k < length gsyms)%nat -> mtfv_at (e_arr1 e') (Z.of_nat k) = nth k gsyms 0) /\
    e_nInUse e' = nI /\ e_unseqToSeq e' = gp_unseq e /\ Forall (fun u => 0 <= u < nI) (ulist (Z.to_nat nb)) /\ 1 <= nI <= 256 /\ EOB = nI + 1.
  Proof.
    cps_destruct GF as (BOK1 & BOK2 & NB & DEFI & IU01 & F5 & M1). cps_destruct (maps_facts e GF) as (NI & UB & UJ). pose proof (gp_EOB_eq e) as EE.
    assert (Enb : nb = e_nblock e) by reflexivity. assert (EnI : nI = gp_nInUse e) by reflexivity. assert (EEOB : EOB = gp_EOB e) by reflexivity.
    cbv zeta. rewrite generateMTFValues_eq.
    cps_pose (GX_all (Z.to_nat nb) ltac:(lia)) as (G & YY & ZP & WR & MV & PM).
    set (s := gp_st e (Z.to_nat nb)) in *. unfold gp_fin.
    assert (ZR : let '(arr1, mtfFreq, wr) := (if 0 <? gm_zPend s then mtf_zrun 64 (gm_arr1 s) (gm_mtfFreq s) (gm_wr s) (gm_zPend s - 1)
                                               else (gm_arr1 s, gm_mtfFreq s, gm_wr s)) in
                 MTFV arr1 (g_acc (gx (Z.to_nat nb)) ++ zflush (g_z (gx (Z.to_nat nb)))) /\ wr = Z.of_nat (length (g_acc (gx (Z.to_nat nb)) ++ zflush (g_z (gx (Z.to_nat nb)))))).
    { unfold zflush. rewrite <- ZP. destruct (Z.ltb_spec 0 (gm_zPend s)).
      - pose proof (MTFV_zrun 64 (gm_arr1 s) (gm_mtfFreq s) (gm_wr s) (gm_zPend s - 1) (g_acc (gx (Z.to_nat nb))) MV WR ltac:(lia)) as ZO.
        destruct (mtf_zrun 64 _ _ _ _) as [[a1 mf1] wr1]. exact ZO.
      - rewrite app_nil_r. split; [exact MV| exact WR]. }
    destruct (if 0 <? gm_zPend s then _ else _) as [[arr1 mf] wr]. destruct ZR as [ZM ZW].
    unfold mtf_emit. cbn [fst e_nMTF e_arr1 e_nInUse e_unseqToSeq].
    assert (GS : gsyms = (g_acc (gx (Z.to_nat nb)) ++ zflush (g_z (gx (Z.to_nat nb)))) ++ [EOB]).
    { unfold gsyms, genc, gfin, gx. rewrite app_assoc. reflexivity. }
    rewrite GS. split; [rewrite ZW, !length_app; cbn [length]; lia|]. split; [apply MTFV_emit; [exact ZM| exact ZW| lia]|].
    split; [reflexivity|]. split; [reflexivity|]. split; [apply ulist_range; lia|]. lia.
  Qed.
End E.

End ACeilS1.
End BzR4e.

Open Scope Z_scope.
From Stdlib Require Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Assign.
  Variable A : Z.
  Hypothesis HA : 2 <= A <= 258.

  Lemma sm_assign_ccode : forall n code len t0, 0 <= t0 ->
    (forall t v, t0 <= t < t0 + Z.of_nat n -> 0 <= v < A -> 1 <= zget len (258 * t + v) <= 20) ->
    let r := sm_assign n code len A t0 in
    (forall t v, t0 <= t < t0 + Z.of_nat n -> 0 <= v < A -> zget r (258 * t + v) = ccode (Lrow len (258 * t)) A v) /\
    (forall p, (forall t, t0 <= t < t0 + Z.of_nat n -> ~ (258 * t <= p < 258 * t + A)) -> zget r p = zget code p).
  Proof.
    induction n as [|n IH]; intros code len t0 Ht0 HL; cbv zeta; cbn [sm_assign].
    - split; [intros; lia| intros; reflexivity].
    - rewrite sm_minmax_eq. pose proof (minmax_len_spec (Z.to_nat A) 0 len (258 * t0) 32 0) as MM.
      destruct (minmax_len (Z.to_nat A) 0 len (258 * t0) 32 0) as [mn mx]. cps_destruct MM as (M1 & M2 & M3 & M4 & M5).
      assert (R : forall v, 0 <= v < A -> 1 <= zget len (258 * t0 + v) <= 20) by (intros; apply HL; lia).
      assert (Bmn : 1 <= mn).
      { destruct M4 as [M4|(v & Hv & M4)]; [lia|]. pose proof (R v ltac:(lia)). lia. }
      pose proof (hbAssignCodes_spec len (258 * t0) (258 * t0) A code mn mx Bmn ltac:(intros i Hi; unfold Lrow; apply M3; lia)) as AS.
      cbv zeta in AS. destruct AS as [A1 A2].
      set (code1 := hbAssignCodes code len (258 * t0) (258 * t0) mn mx A) in *.
      destruct (IH code1 len (t0 + 1) ltac:(lia) ltac:(intros; apply HL; lia)) as [B1 B2].
      split.
      + intros t v Ht Hv. destruct (Z.eq_dec t t0) as [->|NE].
        * rewrite B2 by (intros t' Ht'; lia). apply A1. exact Hv.
        * apply B1; lia.
      + intros p Hp. rewrite B2 by (intros t' Ht'; apply Hp; lia). apply A2. pose proof (Hp t0 ltac:(lia)). lia.
  Qed.
End Assign.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Kraft.
  Variables (A nGroups : Z).
  Hypothesis HA : 2 <= A <= 258.
  Hypothesis HG : 1 <= nGroups <= 6.

  Lemma sm_mklens_kraft : forall nMTF n len rf heap weight parent t0,
    1 <= nMTF <= 4194304 -> RFI A nGroups rf nMTF -> 0 <= t0 -> t0 + Z.of_nat n <= nGroups ->
    let r := fst (fst (fst (sm_mklens n len rf heap weight parent A t0))) in
    forall t, t0 <= t < t0 + Z.of_nat n -> forall k, 1 <= k -> wsum (Lrow r (258 * t)) A k <= 2 ^ k.
  Proof.
    intros nMTF n. induction n as [|n IH]; intros len rf heap weight parent t0 HM RF Ht0 Hn; cbv zeta; intros t Ht.
    - exfalso. lia.
    - cbn [sm_mklens].
      set (h := hbMakeCodeLengths len rf heap weight parent (258 * t0) (258 * t0) A 17).
      destruct (RFI_budget A nGroups HA rf nMTF t0 RF ltac:(lia)) as [FNN FS].
      pose proof (hbMakeCodeLengths_lens A 8388607 (258 * t0) HA ltac:(lia) len rf heap weight parent (258 * t0) FNN ltac:(lia)) as HL.
      cbv zeta in HL. fold h in HL. destruct HL as [LO LF].
      pose proof (hbMakeCodeLengths_kraft A 8388607 (258 * t0) HA ltac:(lia) len rf heap weight parent (258 * t0) FNN ltac:(lia)) as KR.
      fold h in KR.
      pose proof (mklens_spec A nGroups HA nMTF n (hs_len h) rf (hs_heap h) (hs_weight h) (hs_parent h) (t0 + 1) HM RF ltac:(lia) ltac:(lia)) as MS.
      cbv zeta in MS. destruct MS as [R1 R2].
      set (r := fst (fst (fst (sm_mklens n (hs_len h) rf (hs_heap h) (hs_weight h) (hs_parent h) A (t0 + 1))))) in *.
      destruct (Z.eq_dec t t0) as [->|NE].
      + (* [comment removed for export] *)
        assert (RW : forall v, 0 <= v < A -> Lrow r (258 * t0) v = zget (hs_len h) (258 * t0 + v)).
        { intros v Hv. unfold Lrow. apply R2. intros t' Ht'. lia. }
        apply kraft17_KR; [lia| |].
        * intros j Hj. rewrite RW by exact Hj. pose proof (LO (j + 1) ltac:(lia)) as X. replace (258 * t0 + (j + 1) - 1) with (258 * t0 + j) in X by lia. exact X.
        * unfold kraft17 in KR. rewrite (sumF_shift (Z.to_nat A) _ (258 * t0) (258 * t0)) in KR. rewrite Z.sub_diag in KR.
          rewrite (sumF_ext (Z.to_nat A) _ (fun b => 2 ^ (17 - zget (hs_len h) (b + 258 * t0))) 0); [exact KR|].
          intros b Hb. rewrite RW by lia. f_equal. f_equal. f_equal. lia.
      + apply (IH (hs_len h) rf (hs_heap h) (hs_weight h) (hs_parent h) (t0 + 1) HM RF ltac:(lia) ltac:(lia)). lia.
  Qed.
End Kraft.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition mtfv_list (arr1 : zarr) (i : Z) (n : nat) : list Z := map (fun k => mtfv_at arr1 (i + Z.of_nat k)) (seq 0 n).
Lemma mtfv_list_length : forall arr1 i n, length (mtfv_list arr1 i n) = n.
Proof. intros. unfold mtfv_list. rewrite length_map, length_seq. reflexivity. Qed.
Lemma mtfv_list_S : forall arr1 i n, mtfv_list arr1 i (S n) = mtfv_at arr1 i :: mtfv_list arr1 (i + 1) n.
Proof.
  intros. unfold mtfv_list. rewrite <- cons_seq. cbn [map]. rewrite Z.add_0_r. f_equal.
  rewrite <- seq_shift, map_map. apply map_ext. intros a. f_equal. lia.
Qed.
Lemma mtfv_list_nth : forall n arr1 i k, (k < n)%nat -> nth k (mtfv_list arr1 i n) 0 = mtfv_at arr1 (i + Z.of_nat k).
Proof.
  induction n as [|n IH]; intros arr1 i k Hk; [lia|]. rewrite mtfv_list_S. destruct k as [|k]; cbn [nth].
  - rewrite Z.add_0_r. reflexivity.
  - rewrite IH by lia. f_equal. lia.
Qed.
Lemma mtfv_list_app : forall arr1 i n m, mtfv_list arr1 i (n + m) = mtfv_list arr1 i n ++ mtfv_list arr1 (i + Z.of_nat n) m.
Proof.
  intros arr1 i n. revert i. induction n as [|n IH]; intros i m.
  - cbn [mtfv_list seq map app Nat.add]. rewrite Z.add_0_r. reflexivity.
  - cbn [Nat.add]. rewrite !mtfv_list_S, IH. cbn [app]. f_equal. f_equal. f_equal. lia.
Qed.
(* [comment removed for export] *)
Lemma mtfv_list_eq : forall arr1 (xs : list Z),
  (forall k, (k < length xs)%nat -> mtfv_at arr1 (Z.of_nat k) = nth k xs 0) -> mtfv_list arr1 0 (length xs) = xs.
Proof.
  intros arr1 xs H. apply (nth_ext _ _ 0 0); [rewrite mtfv_list_length; reflexivity|].
  intros k Hk. rewrite mtfv_list_length in Hk. rewrite mtfv_list_nth, Z.add_0_l by exact Hk. apply H. exact Hk.
Qed.

(* [comment removed for export] *)
Lemma ws_syms_flat : forall n len code arr1 (sel : Z -> Z) (Lf : Z -> Z -> Z) A t i,
  (forall k, i <= k < i + Z.of_nat n -> sel (k / 50) = t) ->
  (forall v, 0 <= v < A -> Lf t v = zget len (258 * t + v) /\ zget code (258 * t + v) = ccode (Lf t) A v) ->
  (forall k, i <= k < i + Z.of_nat n -> 0 <= mtfv_at arr1 k < A) ->
  ws_syms n len code arr1 t i = ws_sym sel Lf A i (mtfv_list arr1 i n).
Proof.
  induction n as [|n IH]; intros len code arr1 sel Lf A t i HS HC HV; [reflexivity|].
  rewrite mtfv_list_S. cbn [ws_syms ws_sym]. rewrite (HS i) by lia.
  destruct (HC (mtfv_at arr1 i) ltac:(apply HV; lia)) as [E1 E2]. rewrite E1, E2, <- E1.
  f_equal. apply IH; [intros; apply HS; lia| exact HC| intros; apply HV; lia].
Qed.

Theorem ws_data_sym : forall fuel len code arr1 sel nMTF gs selCtr (Lf : Z -> Z -> Z) A nG,
  0 <= gs <= nMTF -> gs = 50 * selCtr -> (Z.to_nat (nMTF - gs) < 50 * fuel)%nat ->
  (forall g, 0 <= g -> 50 * g < nMTF -> 0 <= zget sel g < nG) ->
  (forall t v, 0 <= t < nG -> 0 <= v < A -> Lf t v = zget len (258 * t + v) /\ zget code (258 * t + v) = ccode (Lf t) A v) ->
  (forall k, 0 <= k < nMTF -> 0 <= mtfv_at arr1 k < A) ->
  ws_data fuel len code arr1 sel nMTF gs selCtr = ws_sym (fun g => zget sel g) Lf A gs (mtfv_list arr1 gs (Z.to_nat (nMTF - gs))).
Proof.
  induction fuel as [|f IH]; intros len code arr1 sel nMTF gs selCtr Lf A nG Hgs HS Hf SEL HC HV.
  - exfalso. lia.
  - cbn [ws_data]. destruct (Z.leb_spec nMTF gs) as [LE|GT].
    + replace (Z.to_nat (nMTF - gs)) with 0%nat by lia. reflexivity.
    + unfold BzCState.BZ_G_SIZE. set (ge := if nMTF <=? gs + 50 - 1 then nMTF - 1 else gs + 50 - 1).
      assert (Hge : gs <= ge < nMTF /\ ge <= gs + 49 /\ (ge = nMTF - 1 \/ ge = gs + 49)) by (subst ge; destruct (Z.leb_spec nMTF (gs + 50 - 1)); lia).
      pose proof (SEL selCtr ltac:(lia) ltac:(lia)) as ST.
      replace (Z.to_nat (nMTF - gs)) with (Z.to_nat (ge - gs + 1) + Z.to_nat (nMTF - (ge + 1)))%nat by lia.
      rewrite mtfv_list_app, ws_sym_app, mtfv_list_length.
      replace (gs + Z.of_nat (Z.to_nat (ge - gs + 1))) with (ge + 1) by lia.
      rewrite (ws_syms_flat (Z.to_nat (ge - gs + 1)) len code arr1 (fun g => zget sel g) Lf A (zget sel selCtr) gs).
      * f_equal. cps_destruct Hge as (G1 & G2 & [G3|G3]).
        -- cbn [ws_data]. replace (Z.to_nat (nMTF - (ge + 1))) with 0%nat by lia. destruct f; [reflexivity|]. cbn [ws_data].
           replace (nMTF <=? ge + 1) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
        -- apply (IH len code arr1 sel nMTF (ge + 1) (selCtr + 1) Lf A nG); try lia; try assumption.
      * intros k Hk. cbv beta. f_equal. symmetry. apply (Z.div_unique k 50 selCtr (k - gs)); lia.
      * intros v Hv. apply HC; [exact ST| exact Hv].
      * intros k Hk. apply HV. lia.
Qed.

(* [comment removed for export] *)
Corollary ws_data_sym0 : forall len code arr1 sel nMTF (Lf : Z -> Z -> Z) A nG,
  0 <= nMTF ->
  (forall g, 0 <= g -> 50 * g < nMTF -> 0 <= zget sel g < nG) ->
  (forall t v, 0 <= t < nG -> 0 <= v < A -> Lf t v = zget len (258 * t + v) /\ zget code (258 * t + v) = ccode (Lf t) A v) ->
  (forall k, 0 <= k < nMTF -> 0 <= mtfv_at arr1 k < A) ->
  ws_data (Z.to_nat (nMTF + 1)) len code arr1 sel nMTF 0 0 = ws_sym (fun g => zget sel g) Lf A 0 (mtfv_list arr1 0 (Z.to_nat nMTF)).
Proof.
  intros. rewrite (ws_data_sym (Z.to_nat (nMTF + 1)) len code arr1 sel nMTF 0 0 Lf A nG); try lia; try assumption.
  rewrite Z.sub_0_r. reflexivity.
Qed.
