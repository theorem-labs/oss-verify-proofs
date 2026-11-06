(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore FxSound FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxPlan FxFrame FxDrv FxRgs.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxBacking FxChDen.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcMrg AcDenW AcHand.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.AcShift OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcMrg OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcDenW OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcHand.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section Hand0.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.
Hypothesis Hwx : wx_segs_nowrap segs.

(* [comment removed for export] *)
Definition hval0 (nL : positive) (E : valu) (regs' : bvmap 5 word) : valu :=
  fun x : positive => if Pos.ltb x nL then E x else getr regs' (Z_to_bv 5 (Zpos (x - nL) - 1)).

#[using="Type"] Lemma hand_sden0 : forall L S E msr msr' q K W,
  sden segs E (mrg L S) msr ->
  state_wf L = true -> bases_wf (s_next L) (s_rgs S) = true ->
  (forall i R, In i W -> nth_error (s_rgs L) i = Some R -> rg_kind R <> RO) ->
  ms_pc_val msr' = Z_to_bv 64 q -> ms_svc_pending msr' = None -> ms_resv msr' = None -> ms_fcsr msr' = ms_fcsr msr ->
  (forall r : reg, existsb (Pos.eqb (rkey r)) K = true -> getr (ms_regs msr') r = getr (ms_regs msr) r) ->
  (forall x, ~ (exists i R, In i W /\ nth_error (s_rgs L) i = Some R /\ in_rg (E) R x) ->
     (exists R, In R (s_rgs (mrg L S)) /\ in_rg E R x) -> ms_mem msr' x = ms_mem msr x) ->
  (forall i R j, In i W -> nth_error (s_rgs L) i = Some R -> 0 <= j < rsz (E) R ->
     rd1 segs (ms_mem msr') (Z_to_bv 64 (bv_unsigned (lden (E) (rg_base R)) + j)) <> None /\
     (rg_kind R <> RT -> wview segs (ms_mem msr') (Z_to_bv 64 (bv_unsigned (lden (E) (rg_base R)) + j)) <> None)) ->
  sden segs (hval0 (s_next L) E (ms_regs msr')) (mrg (hand_post L q K W) S) msr'.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L S E msr msr' q K W Hsd HwL HbS HnRO Hpc Hsvc Hrsv Hfcsr Hkeep Hmem Hrw.
  set (nL := s_next L) in *.
  set (E' := hval0 nL E (ms_regs msr')).
  assert (Ha : agree nL E E') by (intros x Hx; unfold E', hval0; rewrite (proj2 (Pos.ltb_lt _ _) Hx); reflexivity).
  assert (HbW : forall R, In R (s_rgs L) -> forall E1 E2, agree nL E1 E2 ->
            lden (E1) (rg_base R) = lden (E2) (rg_base R) /\ rsz (E1) R = rsz (E2) R).
  { intros R HR E1 E2 H12. unfold state_wf in HwL. apply andb_prop in HwL as [HwL _]. apply andb_prop in HwL as [HwL _].
    apply andb_prop in HwL as [_ Hg]. rewrite forallb_forall in Hg. specialize (Hg R HR). unfold rwf in Hg.
    apply andb_prop in Hg as [Hg _]. apply andb_prop in Hg as [Hb Hs].
    unfold rsz. rewrite (lden_agree nL _ _ _ Hb H12), (lden_agree nL _ _ _ Hs H12). split; reflexivity. }
  intros E'' Ha''.
  assert (Ha0 : agree nL E E'') by (intros x Hx; rewrite (Ha x Hx); apply Ha''; cbn [mrg hand_post s_next]; fold nL; lia).
  pose proof (Hsd E'' Ha0) as HdE.
  destruct HdE as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8). cbn [mrg s_pc s_regs s_rgs s_facts s_resv] in B5, B6, B7, B4.
  unfold sden0. cbn [mrg hand_post s_pc s_regs s_rgs s_facts s_resv].
  split; [rewrite Hpc; reflexivity|]. split; [exact Hsvc|]. split; [cbn [rsv_ok]; exact Hrsv|].
  split; [|split; [|split; [|split]]].
  + (* [comment removed for export] *)
    intros r. destruct (decide (r = 0%bv)) as [->|Hr0].
    * unfold getr. rewrite bv_eqb_refl. change (rkey 0%bv) with xH. cbn [rget]. reflexivity.
    * destruct (rkey_succ r Hr0) as (k & Hk1 & Ek).
      assert (Hkk : (1 <= Pos.to_nat (rkey r) - 1 <= 31)%nat) by (rewrite Ek, SuccNat2Pos.id_succ; lia).
      assert (Hnx : rkey r <> xH) by (intros Hc; apply Hr0; apply rkey_1; exact Hc).
      rewrite (hregs_get _ _ _ 31 _ (rkey r) Hkk Hnx).
      destruct (existsb (Pos.eqb (rkey r)) K) eqn:HK.
      -- rewrite (Hkeep r HK). exact (B4 r).
      -- rewrite lden_lvar. rewrite <- (Ha'' (s_next L + rkey r)%positive) by (cbn [mrg hand_post s_next]; lia).
         unfold E', hval0. rewrite (proj2 (Pos.ltb_ge _ _)) by (unfold nL; lia).
         replace (s_next L + rkey r - nL)%positive with (rkey r) by (unfold nL; lia). rewrite rkey_reg. reflexivity.
  + (* [comment removed for export] *)
    apply Forall_app. split.
    * apply Forall_forall. intros R1 HR1. apply In_nth_error in HR1 as (j & Hj).
      destruct (empty_at_nth W (s_rgs L) 0 j R1 Hj) as (R0 & HR0 & ER). cbn [Nat.add] in ER.
      assert (HR0in : In R0 (s_rgs L)) by exact (nth_error_In _ _ HR0).
      apply Forall_app in B5 as [B5L B5S]. rewrite Forall_forall in B5L. pose proof (B5L R0 HR0in) as Hok0.
      destruct (HbW R0 HR0in E E'' Ha0) as [Eb Ez].
      destruct (existsb (Nat.eqb j) W) eqn:HjW.
      -- subst R1. apply existsb_exists in HjW as (i & Hi & Hij). apply Nat.eqb_eq in Hij. subst i.
         pose proof (HnRO j R0 Hi HR0) as HnR.
         destruct Hok0 as (H1 & H2 & _ & _). unfold rg_ok, empty_rg. cbn [rg_base rg_size rg_kind rg_cont]. unfold rsz in *. cbn [rg_size] in *.
         split; [exact H1|]. split; [exact H2|]. split.
         ++ intros i Hi'. rewrite <- Ez in Hi'. destruct (Hrw j R0 i Hi HR0 Hi') as [Hr1 Hr2]. rewrite <- Eb.
            destruct (rg_kind R0); try (split; [exact Hr1 | apply Hr2; discriminate]); try exact Hr1; try (split; [split; [exact Hr1 | apply Hr2; discriminate] | intros; rewrite tget_empty in *; discriminate]).
            all: exfalso; apply HnR; reflexivity.
         ++ intros p v Hp. rewrite tget_empty in Hp. discriminate.
      -- subst R1. apply (rg_ok_mem_eq' segs _ (ms_mem msr)); [exact Hok0|]. intros i Hi. apply Hmem.
         2: { exists R0. split; [cbn [mrg s_rgs]; apply in_or_app; left; exact HR0in|].
              unfold in_rg. rewrite Eb, Ez. destruct Hok0 as (_ & H2 & _).
              rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with two64.
              pose proof (bv_unsigned_in_range _ (lden (E'') (rg_base R0))) as BB. change (bv_modulus 64) with two64 in BB.
              rewrite Z.mod_small by lia. lia. }
         intros (i0 & R2 & Hi0 & HR2 & Hin). assert (Hne : i0 <> j).
         { intros ->. assert (Hc : existsb (Nat.eqb j) W = true) by (apply existsb_exists; exists j; split; [exact Hi0 | apply Nat.eqb_refl]). congruence. }
         pose proof (rgs_disj_nth E'' _ i0 j _ _ (proj1 (proj1 (rgs_disj_app_iff E'' _ _) B6)) Hne
                       HR2 HR0) as HD.
         unfold rg_disj in HD. cbv zeta in HD.
         destruct (HbW R2 (nth_error_In _ _ HR2) E E'' Ha0) as [Eb2 Ez2]. unfold in_rg in Hin. rewrite Eb2, Ez2 in Hin.
         destruct Hok0 as (_ & H2 & _). rewrite Z_to_bv_unsigned in Hin. unfold bv_wrap in Hin. change (bv_modulus 64) with two64 in Hin.
         pose proof (bv_unsigned_in_range _ (lden (E'') (rg_base R0))) as BB. change (bv_modulus 64) with two64 in BB.
         rewrite Z.mod_small in Hin by lia. lia.
    * apply Forall_app in B5 as [_ B5S]. rewrite Forall_forall in B5S |- *. intros R HR.
      apply (rg_ok_mem_eq' segs _ (ms_mem msr)); [exact (B5S R HR)|]. intros i Hi. apply Hmem.
      2: { exists R. split; [cbn [mrg s_rgs]; apply in_or_app; right; exact HR|].
           unfold bases_wf in HbS. rewrite forallb_forall in HbS. destruct (andb_prop _ _ (HbS R HR)) as [Hb1 Hb2].
           unfold in_rg, rsz in *. rewrite (lden_agree nL E E'' _ Hb1 Ha0), (lden_agree nL E E'' _ Hb2 Ha0).
           destruct (B5S R HR) as (_ & H2 & _). unfold rsz in H2.
           rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with two64.
           pose proof (bv_unsigned_in_range _ (lden E'' (rg_base R))) as BB. change (bv_modulus 64) with two64 in BB.
           rewrite Z.mod_small by lia. lia. }
      intros (i0 & R2 & Hi0 & HR2 & Hin).
      apply rgs_disj_app_iff in B6 as (_ & _ & BX). rewrite Forall_forall in BX.
      pose proof (BX R2 (nth_error_In _ _ HR2)) as BX2. rewrite Forall_forall in BX2. specialize (BX2 R HR).
      unfold rg_disj in BX2. cbv zeta in BX2.
      destruct (HbW R2 (nth_error_In _ _ HR2) E E'' Ha0) as [Eb2 Ez2]. unfold in_rg in Hin. rewrite Eb2, Ez2 in Hin.
      destruct (B5S R HR) as (_ & H2 & _). rewrite Z_to_bv_unsigned in Hin. unfold bv_wrap in Hin. change (bv_modulus 64) with two64 in Hin.
      pose proof (bv_unsigned_in_range _ (lden E'' (rg_base R))) as BB. change (bv_modulus 64) with two64 in BB.
      rewrite Z.mod_small in Hin by lia. lia.
  + (* [comment removed for export] *)
    apply (rgs_disj_same_shape E'' (s_rgs L ++ s_rgs S)); [|exact B6].
    rewrite !map_app. f_equal. pose proof (empty_at_shape W (s_rgs L) 0) as Hs. unfold shape in Hs. exact Hs.
  + exact B7.
  + rewrite Hfcsr. exact B8.
Qed.

#[using="Hwx"] Theorem den_hand0 : forall L S E M ms model T q K W,
  DEN segs LIMIT model0 mem0 E (mrg L S) M ms model ->
  state_wf L = true ->
  (forall i R, In i W -> nth_error (s_rgs L) i = Some R -> rg_kind R <> RO) ->
  (exists msr', isteps segs (restrict (Hof E M model) ms) msr' /\ ms_pc_val msr' = Z_to_bv 64 q /\ ms_svc_pending msr' = None /\
     ms_resv msr' = None /\ ms_fcsr msr' = ms_fcsr ms /\
     (forall r : reg, existsb (Pos.eqb (rkey r)) K = true -> getr (ms_regs msr') r = getr (ms_regs ms) r) /\
     (forall x, ~ (exists i R, In i W /\ nth_error (s_rgs L) i = Some R /\ in_rg (E) R x) ->
        ms_mem msr' x = ms_mem (restrict (Hof E M model) ms) x) /\
     (forall i R j, In i W -> nth_error (s_rgs L) i = Some R -> 0 <= j < rsz (E) R ->
        rd1 segs (ms_mem msr') (Z_to_bv 64 (bv_unsigned (lden (E) (rg_base R)) + j)) <> None /\
        (rg_kind R <> RT -> wview segs (ms_mem msr') (Z_to_bv 64 (bv_unsigned (lden (E) (rg_base R)) + j)) <> None))) ->
  (forall E' ms' model', DEN segs LIMIT model0 mem0 E' (mrg (hand_post L q K W) S) M ms' model' ->
     agree (s_next L) E E' -> realizes_cfg segs cfg (mkCfg ms' model') T) ->
  realizes_cfg segs cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins (fun (Hwx : LiaFast.U) => LiaFast.u0).
  intros L S E M ms model T q K W Hd HwL HnRO (msr' & Hst & Hpc & Hsvc & Hrsv & Hfcsr & Hkeep & Hmem & Hrw) Hk.
  pose proof (dn_sden _ _ _ _ _ _ _ _ _ Hd) as Hsd.
  assert (Ha : agree (s_next L) E (hval0 (s_next L) E (ms_regs msr'))) by (intros x Hx; unfold hval0; rewrite (proj2 (Pos.ltb_lt _ _) Hx); reflexivity).
  apply (den_isteps segs cfg LIMIT model0 mem0 Hwx E (mrg L S) M ms model T (mrg (hand_post L q K W) S) msr'
           (hval0 (s_next L) E (ms_regs msr')) Hd Hst).
  - assert (HbS : bases_wf (s_next L) (s_rgs S) = true).
    { pose proof (dn_bases _ _ _ _ _ _ _ _ _ Hd) as Hb. cbn [mrg s_next s_rgs] in Hb. unfold bases_wf in *.
      rewrite forallb_app in Hb. apply andb_prop in Hb as [_ Hb]. exact Hb. }
    apply (hand_sden0 L S E _ msr' q K W Hsd HwL HbS HnRO Hpc Hsvc Hrsv Hfcsr Hkeep); [|exact Hrw].
    intros x Hx _. exact (Hmem x Hx).
  - exact Ha.
  - cbn [mrg hand_post s_next]. lia.
  - intros x Hx. apply Hmem. intros (i0 & R2 & Hi0 & HR2 & Hin). unfold outside in Hx. cbn [mrg s_rgs] in Hx.
    apply Forall_app in Hx as [Hx _]. rewrite Forall_forall in Hx. specialize (Hx R2 (nth_error_In _ _ HR2)).
    unfold in_rg in Hin. unfold rsz in Hx, Hin. lia.
  - cbn [mrg s_rgs hand_post]. unfold shape. rewrite !map_app. f_equal. exact (empty_at_shape W (s_rgs L) 0).
  - intros E2 ms2 model2 HD2 Ha2. exact (Hk E2 ms2 model2 HD2 Ha2).
Qed.
End Hand0.

(* [comment removed for export] *)
Section HandW0.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable model0 : Model.
Hypothesis Hwx : wx_segs_nowrap segs.

#[using="Hwx"] Theorem den_hand_w0 : forall mem0 L S E M ms model T q K W (QM : (word -> option byte) -> Prop),
  DEN segs LIMIT model0 mem0 E (mrg L S) M ms model ->
  state_wf L = true ->
  (forall i R, In i W -> nth_error (s_rgs L) i = Some R -> rg_kind R <> RO) ->
  (exists msr', isteps segs (restrict (Hof E M model) ms) msr' /\ ms_pc_val msr' = Z_to_bv 64 q /\ ms_svc_pending msr' = None /\
     ms_resv msr' = None /\ ms_fcsr msr' = ms_fcsr ms /\
     (forall r : reg, existsb (Pos.eqb (rkey r)) K = true -> getr (ms_regs msr') r = getr (ms_regs ms) r) /\
     (forall x, ~ (exists i R, In i W /\ nth_error (s_rgs L) i = Some R /\ in_rg (E) R x) ->
        (exists R, In R (s_rgs (mrg L S)) /\ in_rg E R x) ->
        ms_mem msr' x = ms_mem (restrict (Hof E M model) ms) x) /\
     (forall w, 0 <= w < two64 -> outside E (s_rgs (mrg L S)) (Z_to_bv 64 w) -> ~ own_pt E M w ->
        ms_mem msr' (Z_to_bv 64 w) = ms_mem (restrict (Hof E M model) ms) (Z_to_bv 64 w)) /\
     (forall w, frz_pt E M w -> ms_mem msr' (Z_to_bv 64 w) = ms_mem (restrict (Hof E M model) ms) (Z_to_bv 64 w)) /\
     (forall i R j, In i W -> nth_error (s_rgs L) i = Some R -> 0 <= j < rsz (E) R ->
        rd1 segs (ms_mem msr') (Z_to_bv 64 (bv_unsigned (lden (E) (rg_base R)) + j)) <> None /\
        (rg_kind R <> RT -> wview segs (ms_mem msr') (Z_to_bv 64 (bv_unsigned (lden (E) (rg_base R)) + j)) <> None)) /\
     QM (ms_mem msr')) ->
  (forall E' ms' model', DEN segs LIMIT model0 (ms_mem ms') E' (mrg (hand_post L q K W) S) M ms' model' ->
     agree (s_next L) E E' -> (forall w, frz_pt E M w -> ms_mem ms' (Z_to_bv 64 w) = mem0 (Z_to_bv 64 w)) ->
     (exists mr, QM mr /\ forall x, Hof E M model x = false -> ms_mem ms' x = mr x) ->
     realizes_cfg segs cfg (mkCfg ms' model') T) ->
  realizes_cfg segs cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins (fun (Hwx : LiaFast.U) => LiaFast.u0).
  intros mem0 L S E M ms model T q K W QM Hd HwL HnRO (msr' & Hst & Hpc & Hsvc & Hrsv & Hfcsr & Hkeep & Hmem & Hown & Hfz & Hrw & HQ) Hk.
  pose proof (dn_sden _ _ _ _ _ _ _ _ _ Hd) as Hsd.
  assert (Ha : agree (s_next L) E (hval0 (s_next L) E (ms_regs msr'))) by (intros x Hx; unfold hval0; rewrite (proj2 (Pos.ltb_lt _ _) Hx); reflexivity).
  assert (HbS : bases_wf (s_next L) (s_rgs S) = true).
  { pose proof (dn_bases _ _ _ _ _ _ _ _ _ Hd) as Hb. cbn [mrg sst_shift s_next s_rgs] in Hb. unfold bases_wf in *.
    rewrite forallb_app in Hb. apply andb_prop in Hb as [_ Hb]. exact Hb. }
  apply (den_isteps_w segs cfg LIMIT model0 Hwx mem0 E (mrg L S) M ms model T (mrg (hand_post L q K W) S) msr'
           (hval0 (s_next L) E (ms_regs msr')) Hd Hst).
  - exact (hand_sden0 segs L S E _ msr' q K W Hsd HwL HbS HnRO Hpc Hsvc Hrsv Hfcsr Hkeep Hmem Hrw).
  - exact Ha.
  - cbn [mrg hand_post s_next]. lia.
  - exact Hown.
  - exact Hfz.
  - cbn [mrg s_rgs hand_post]. unfold shape. rewrite !map_app. f_equal. exact (empty_at_shape W (s_rgs L) 0).
  - intros E2 ms2 model2 HD2 Ha2 Hf2 Hv2. exact (Hk E2 ms2 model2 HD2 Ha2 Hf2 (ex_intro _ (ms_mem msr') (conj HQ Hv2))).
Qed.
End HandW0.
