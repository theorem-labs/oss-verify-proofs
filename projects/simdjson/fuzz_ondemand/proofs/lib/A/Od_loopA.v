(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjOd.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.A Require Import Layout Shadow RT_iface D_defs D_kit D_clx Sj_akit Sj_acps Sj_hkit Sj_rtf Sj_num_akit Sj_num_amem Od_defsA Od_cpsA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section Loop.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable PMc : Model -> Prop.
Hypothesis MST : mat_stable PMc.

Hypothesis HEAD : forall E, od_oka E -> HLASTP E -> od_head_stmt E.
Hypothesis HEXIT : forall E, od_oka E -> od_head_exit_stmt E.
Hypothesis PLUS : forall E, od_oka E -> HLASTP E -> od_plus_stmt E.
Hypothesis DBL : arm_dbl_cps RT PMc.

Notation aevt := (aevt RT PMc).

Lemma od_exit_kc_rebase : forall Σ0 K E mL c m0, od_exit_kc RT PMc Σ0 K E mL c -> od_exit_kc RT PMc Σ0 K (oa_rebase E m0) mL c.
Proof. intros Σ0 K E mL c m0 H. exact H. Qed.

Lemma od_exit_kc_weaken : forall Σ0 Σ1 K E mL c c', od_exit_kc RT PMc Σ0 K E mL c ->
  rt_live RT Σ1 = rt_live RT Σ0 -> rt_frames RT Σ1 = rt_frames RT Σ0 -> rt_sp0 RT Σ1 = rt_sp0 RT Σ0 -> c <= c' ->
  od_exit_kc RT PMc Σ1 K E mL c'.
Proof.
  intros Σ0 Σ1 K E mL c c' H E1 E2 E3 Hc. unfold od_exit_kc in *. intros Σ' m0' st vs6 v224 v248 v304 v312 v328 v344
    xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m1 R LV FRS SP0 CR FRM INV.
  apply (H Σ' m0' st vs6 v224 v248 v304 v312 v328 v344); try assumption; try congruence. lia.
Qed.

Lemma od_exit_k_of_kc : forall Σ K E mL c, od_rt RT Σ E mL -> c <= rt_credit RT Σ ->
  od_exit_kc RT PMc Σ K E mL c -> od_exit_k E (fun ms => aevt Σ K ms).
Proof.
  intros Σ K E mL c R CR KX. unfold od_exit_k.
  intros st vs6 v224 v248 v304 v312 v328 v344 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m1 FRM INV.
  apply evt_done.
  exact (KX Σ (o_m0 E) st vs6 v224 v248 v304 v312 v328 v344 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m1
           (od_rt_self RT Σ E mL R) eq_refl eq_refl eq_refl CR FRM INV).
Qed.

Lemma od_plus_cps : forall (Σ : rts RT) (K : config -> Prop) (E : oaenv) (mL : mem) c st st'
    xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs9 xs10 xs11 xt3 xt4 xF xfc m1,
  od_geo E -> od_rt RT Σ E mL -> HLASTP E -> c <= rt_credit RT Σ ->
  od_arm_out (o_bs E) (o_idxs E) st st' -> frm0 xfc -> ODINV E st' m1 ->
  od_exit_kc RT PMc Σ K E mL c ->
  (forall st'' v344 yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys2 ys9 ys10 ys11 yt3 yt4 yF yfc m2,
     od_next_ok (o_bs E) (o_idxs E) 1 st' st'' -> frm0 yfc -> ODINVh E v344 st'' m2 ->
     aevt Σ K (ODST E OD_HEAD yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys2 ys9 ys10 ys11 yt3 yt4 yF yfc m2)) ->
  aevt Σ K (ODST E OD_PLUS xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs9 xs10 xs11 xt3 xt4 xF xfc m1).
Proof using AF MST HEXIT PLUS.
  intros Σ K E mL c st st' xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs9 xs10 xs11 xt3 xt4 xF xfc m1 G R HL CR AO FRM INV KX HK.
  pose proof (od_oka_of_rt RT AF Σ E mL G R) as OK.
  apply (aevt_evt RT AF PMc MST).
  apply (PLUS E OK HL (fun ms => aevt Σ K ms) st st' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 AO FRM INV).
  unfold od_head_k. intros st'' v344 yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys2 ys9 ys10 ys11 yt3 yt4 yF yfc m2 PRE'' F'' I''.
  destruct PRE'' as [NX|DEAD].
  - apply evt_done. exact (HK st'' v344 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 NX F'' I'').
  - apply (HEXIT E OK (fun ms => aevt Σ K ms) st'' v344); [destruct DEAD as (_ & DD & _); lia| exact F''| exact I''|].
    exact (od_exit_k_of_kc Σ K E mL c R CR KX).
Qed.

Lemma od_pass : forall (Σ : rts RT) (K : config -> Prop) (E : oaenv) (mL : mem) c st0 st v344
    xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs9 xs10 xs11 xt3 xt4 xF xfc m1,
  od_geo E -> od_rt RT Σ E mL -> HLASTP E -> 0 <= c -> c + OD_DBL_CREDIT <= rt_credit RT Σ ->
  od_head_pre E st0 st -> frm0 xfc -> ODINVh E v344 st m1 ->
  od_exit_kc RT PMc Σ K E mL c ->
  (forall (Σ1 : rts RT) m0' st' st'' v344' yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys2 ys9 ys10 ys11 yt3 yt4 yF yfc m2,
     od_rt RT Σ1 (oa_rebase E m0') mL ->
     rt_live RT Σ1 = rt_live RT Σ -> rt_frames RT Σ1 = rt_frames RT Σ -> rt_sp0 RT Σ1 = rt_sp0 RT Σ ->
     rt_credit RT Σ - OD_DBL_CREDIT <= rt_credit RT Σ1 ->
     o_pos st <= o_pos st' -> od_next_ok (o_bs E) (o_idxs E) 1 st' st'' -> frm0 yfc -> ODINVh (oa_rebase E m0') v344' st'' m2 ->
     aevt Σ1 K (ODST (oa_rebase E m0') OD_HEAD yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys2 ys9 ys10 ys11 yt3 yt4 yF yfc m2)) ->
  aevt Σ K (ODST E OD_HEAD xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs9 xs10 xs11 xt3 xt4 xF xfc m1).
Proof using AF MST HEAD HEXIT PLUS DBL.
  intros Σ K E mL c st0 st v344 xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs9 xs10 xs11 xt3 xt4 xF xfc m1 G R HL C0 CR PRE FRM INV KX HK.
  pose proof (od_oka_of_rt RT AF Σ E mL G R) as OK.
  assert (CRx : c <= rt_credit RT Σ) by (unfold OD_DBL_CREDIT in CR; lia).
  apply (aevt_evt RT AF PMc MST).
  apply (HEAD E OK HL (fun ms => aevt Σ K ms) st0 st v344 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 PRE FRM INV).
  -   exact (od_exit_k_of_kc Σ K E mL c R CRx KX).
  -
    unfold od_plus_k. intros st' yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys2 ys9 ys10 ys11 yt3 yt4 yF yfc m' AO F' I'.
    apply evt_done.
    apply (od_plus_cps Σ K E mL c st st' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m' G R HL CRx AO F' I' KX).
    intros st'' v344' zt0 zt1 zt2 za0 za1 za2 za3 za4 za5 za6 za7 zs2 zs9 zs10 zs11 zt3 zt4 zF zfc m2 NX F'' I''.
    exact (HK Σ (o_m0 E) st' st'' v344' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 (od_rt_self RT Σ E mL R) eq_refl eq_refl eq_refl
             ltac:(unfold OD_DBL_CREDIT; lia) (proj1 AO) NX F'' I'').
  -
    intros HH. unfold arm_k. intros yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys11 yt3 yt4 yF yfc m' F' I'. apply evt_done.
    apply (DBL Σ K E mL st _ _ _ _ _ _ _ _ _ _ _ _ _ yfc m' G R HL HH ltac:(unfold OD_DBL_CREDIT in *; lia) F' I').
    unfold od_plus_kc. intros Σ1 m0' st' zt0 zt1 zt2 za0 za1 za2 za3 za4 za5 za6 za7 zs2 zs9 zs10 zs11 zt3 zt4 zF zfc m1' R1 LV1 FRS1 SP1 CR1 AO F1 I1.
    apply (od_plus_cps Σ1 K (oa_rebase E m0') mL c st st' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1' (od_geo_rebase E m0' G) R1 HL
             ltac:(lia) AO F1 I1).
    + apply (od_exit_kc_weaken Σ Σ1 K (oa_rebase E m0') mL c c); [exact KX| exact LV1| exact FRS1| exact SP1| lia].
    + intros st'' v344' wt0 wt1 wt2 wa0 wa1 wa2 wa3 wa4 wa5 wa6 wa7 ws2 ws9 ws10 ws11 wt3 wt4 wF wfc m2 NX F'' I''.
      exact (HK Σ1 m0' st' st'' v344' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 R1 LV1 FRS1 SP1 CR1 (proj1 AO) NX F'' I'').
Qed.

Theorem od_loopA : forall (fuel : nat) (Σ : rts RT) (K : config -> Prop) (E : oaenv) (mL : mem) st0 st v344
    xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs9 xs10 xs11 xt3 xt4 xF xfc m1,
  od_geo E -> od_rt RT Σ E mL -> HLASTP E ->
  o_left (o_idxs E) st <= Z.of_nat fuel -> OD_DBL_CREDIT * (Z.of_nat fuel + 1) <= rt_credit RT Σ ->
  od_head_pre E st0 st -> frm0 xfc -> ODINVh E v344 st m1 ->
  od_exit_kc RT PMc Σ K E mL (rt_credit RT Σ - OD_DBL_CREDIT * (Z.of_nat fuel + 1)) ->
  aevt Σ K (ODST E OD_HEAD xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs9 xs10 xs11 xt3 xt4 xF xfc m1).
Proof using AF MST HEAD HEXIT PLUS DBL.
  induction fuel as [|f IH];
    intros Σ K E mL st0 st v344 xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs9 xs10 xs11 xt3 xt4 xF xfc m1 G R HL HF CR PRE FRM INV KX.
  - apply (od_pass Σ K E mL (rt_credit RT Σ - OD_DBL_CREDIT * (Z.of_nat 0 + 1)) st0 st v344 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 G R HL
             ltac:(unfold OD_DBL_CREDIT in *; lia) ltac:(unfold OD_DBL_CREDIT in *; lia) PRE FRM INV KX).
    intros Σ1 m0' st' st'' v344' yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys2 ys9 ys10 ys11 yt3 yt4 yF yfc m2 R1 LV1 FRS1 SP1 CR1 AP NX F'' I''.
    exfalso. destruct NX as (A1 & A2 & _). unfold o_left in HF. cbn [Z.of_nat] in HF. lia.
  - apply (od_pass Σ K E mL (rt_credit RT Σ - OD_DBL_CREDIT * (Z.of_nat (S f) + 1)) st0 st v344 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 G R HL
             ltac:(unfold OD_DBL_CREDIT in *; lia) ltac:(unfold OD_DBL_CREDIT in *; lia) PRE FRM INV KX).
    intros Σ1 m0' st' st'' v344' yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys2 ys9 ys10 ys11 yt3 yt4 yF yfc m2 R1 LV1 FRS1 SP1 CR1 AP NX F'' I''.
    apply (IH Σ1 K (oa_rebase E m0') mL st' st'' v344'); try assumption.
    + exact (od_geo_rebase E m0' G).
    + destruct NX as (A1 & A2 & _). unfold o_left in *. cbn [oa_rebase od_rebase oa_E o_idxs]. lia.
    + unfold OD_DBL_CREDIT in *. lia.
    + left. exact NX.
    + apply (od_exit_kc_weaken Σ Σ1 K (oa_rebase E m0') mL _ _ KX LV1 FRS1 SP1). unfold OD_DBL_CREDIT in *. lia.
Qed.

End Loop.
