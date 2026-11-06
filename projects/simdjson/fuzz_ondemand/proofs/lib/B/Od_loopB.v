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
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.B Require Import Layout RT_iface D_defs D_kit D_clx Sj_akit Sj_acps Sj_hkit Sj_rtf Sj_num_akit Sj_num_amem Od_defsB Od_cpsB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section Loop.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable PMc : Model -> Prop.
Hypothesis MST : mat_stable PMc.

Hypothesis HEAD : forall E, od_oka E -> od_shb E -> HLASTP E -> od_head_stmt E.
Hypothesis HEXIT : forall E, od_oka E -> od_head_exit_stmt E.
Hypothesis PLUS : forall E, od_oka E -> od_shb E -> HLASTP E -> od_plus_stmt E.
Hypothesis DBL : arm_dbl_cps RT PMc.

Notation aevt := (aevt RT PMc).

Notation ODHST E xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xs5 xs6 xt3 xt4 xt5 xt6 xF xfc m :=
  (ODST E OD_HEAD xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 (Z_to_bv 64 (oa_F E + 200))
        (Z_to_bv 64 1) xs5 xs6 (Z_to_bv 64 (oa_F E + 32)) (Z_to_bv 64 (oa_F E + 192)) xt3 xt4 xt5 xt6 xF xfc m).

Lemma od_exit_kc_rebase : forall Σ0 K E mL c m0, od_exit_kc RT PMc Σ0 K E mL c -> od_exit_kc RT PMc Σ0 K (oa_rebase E m0) mL c.
Proof. intros Σ0 K E mL c m0 H. exact H. Qed.

Lemma od_exit_kc_weaken : forall Σ0 Σ1 K E mL c c', od_exit_kc RT PMc Σ0 K E mL c ->
  rt_live RT Σ1 = rt_live RT Σ0 -> rt_frames RT Σ1 = rt_frames RT Σ0 -> rt_sp0 RT Σ1 = rt_sp0 RT Σ0 -> c <= c' ->
  od_exit_kc RT PMc Σ1 K E mL c'.
Proof.
  intros Σ0 Σ1 K E mL c c' H E1 E2 E3 Hc. unfold od_exit_kc in *. intros Σ' m0' st vs v88 v144 v152 v240 v312 v336 v352
    xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs8 xs9 xs11 xt3 xt4 xt5 xt6 xF xfc m1 R LV FRS SP0 CR FRM INV.
  apply (H Σ' m0' st vs v88 v144 v152 v240 v312 v336 v352); try assumption; try congruence. lia.
Qed.

Lemma od_exit_k_of_kc : forall Σ K E mL c, od_rt RT Σ E mL -> c <= rt_credit RT Σ ->
  od_exit_kc RT PMc Σ K E mL c -> od_exit_k E (fun ms => aevt Σ K ms).
Proof.
  intros Σ K E mL c R CR KX. unfold od_exit_k.
  intros st vs v88 v144 v152 v240 v312 v336 v352 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs8 xs9 xs11 xt3 xt4 xt5 xt6 xF xfc m1 FRM INV.
  apply evt_done.
  exact (KX Σ (o_m0 E) st vs v88 v144 v152 v240 v312 v336 v352 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs8 xs9 xs11 xt3 xt4 xt5 xt6 xF xfc m1
           (od_rt_self RT Σ E mL R) eq_refl eq_refl eq_refl CR FRM INV).
Qed.

Lemma od_plus_cps : forall (Σ : rts RT) (K : config -> Prop) (E : oaenv) (mL : mem) c st st' v352
    xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xs6 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m1,
  od_geo E -> od_rt RT Σ E mL -> HLASTP E -> c <= rt_credit RT Σ ->
  od_arm_out (o_bs E) (o_idxs E) st st' -> frm0 xfc -> ODINVp E v352 st' m1 ->
  od_exit_kc RT PMc Σ K E mL c ->
  (forall st'' v336 w352 yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ys5 ys6 yt3 yt4 yt5 yt6 yF yfc m2,
     od_next_ok (o_bs E) (o_idxs E) 1 st' st'' -> frm0 yfc -> ODINVh E v336 w352 st'' m2 ->
     aevt Σ K (ODHST E yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ys5 ys6 yt3 yt4 yt5 yt6 yF yfc m2)) ->
  aevt Σ K (ODST E OD_PLUS xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xs6 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m1).
Proof using AF MST HEXIT PLUS.
  intros Σ K E mL c st st' v352 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xs6 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m1 G R HL CR AO FRM INV KX HK.
  pose proof (od_oka_of_rt RT AF Σ E mL G R) as OK. pose proof (od_shb_of_rt RT AF Σ E mL G R) as HG.
  apply (aevt_evt RT AF PMc MST).
  eapply (PLUS E OK HG HL (fun ms => aevt Σ K ms) st st' v352); [exact AO| exact FRM| exact INV|].
  unfold od_head_k. intros st'' v336 w352 yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ys5 ys6 yt3 yt4 yt5 yt6 yF yfc m2 PRE'' F'' I''.
  destruct PRE'' as [NX|DEAD].
  - apply evt_done. exact (HK st'' v336 w352 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 NX F'' I'').
  - eapply (HEXIT E OK (fun ms => aevt Σ K ms) st'' v336 w352); [destruct DEAD as (_ & DD & _); lia| exact F''| exact I''|].
    exact (od_exit_k_of_kc Σ K E mL c R CR KX).
Qed.

Lemma od_pass : forall (Σ : rts RT) (K : config -> Prop) (E : oaenv) (mL : mem) c st0 st v336 v352
    xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xs5 xs6 xt3 xt4 xt5 xt6 xF xfc m1,
  od_geo E -> od_rt RT Σ E mL -> HLASTP E -> 0 <= c -> c + OD_DBL_CREDIT <= rt_credit RT Σ ->
  od_head_pre E st0 st -> frm0 xfc -> ODINVh E v336 v352 st m1 ->
  od_exit_kc RT PMc Σ K E mL c ->
  (forall (Σ1 : rts RT) m0' st' st'' w336 w352 yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ys5 ys6 yt3 yt4 yt5 yt6 yF yfc m2,
     od_rt RT Σ1 (oa_rebase E m0') mL ->
     rt_live RT Σ1 = rt_live RT Σ -> rt_frames RT Σ1 = rt_frames RT Σ -> rt_sp0 RT Σ1 = rt_sp0 RT Σ ->
     rt_credit RT Σ - OD_DBL_CREDIT <= rt_credit RT Σ1 ->
     o_pos st <= o_pos st' -> od_next_ok (o_bs E) (o_idxs E) 1 st' st'' -> frm0 yfc -> ODINVh (oa_rebase E m0') w336 w352 st'' m2 ->
     aevt Σ1 K (ODHST (oa_rebase E m0') yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ys5 ys6 yt3 yt4 yt5 yt6 yF yfc m2)) ->
  aevt Σ K (ODHST E xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xs5 xs6 xt3 xt4 xt5 xt6 xF xfc m1).
Proof using AF MST HEAD HEXIT PLUS DBL.
  intros Σ K E mL c st0 st v336 v352 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xs5 xs6 xt3 xt4 xt5 xt6 xF xfc m1 G R HL C0 CR PRE FRM INV KX HK.
  pose proof (od_oka_of_rt RT AF Σ E mL G R) as OK. pose proof (od_shb_of_rt RT AF Σ E mL G R) as HG.
  assert (CRx : c <= rt_credit RT Σ) by (unfold OD_DBL_CREDIT in CR; lia).
  apply (aevt_evt RT AF PMc MST).
  eapply (HEAD E OK HG HL (fun ms => aevt Σ K ms) st0 st v336 v352); [exact PRE| exact FRM| exact INV| | |].
  -   exact (od_exit_k_of_kc Σ K E mL c R CRx KX).
  -
    unfold od_plus_k. intros st' w352 yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys2 ys5 ys6 ys10 ys11 yt3 yt4 yt5 yt6 yF yfc m' AO F' I'.
    apply evt_done.
    eapply (od_plus_cps Σ K E mL c st st' w352); [exact G| exact R| exact HL| exact CRx| exact AO| exact F'| exact I'| exact KX|].
    intros st'' z336 z352 zra zt0 zt1 zt2 za0 za1 za2 za3 za4 za5 za6 zs5 zs6 zt3 zt4 zt5 zt6 zF zfc m2 NX F'' I''.
    exact (HK Σ (o_m0 E) st' st'' z336 z352 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 (od_rt_self RT Σ E mL R) eq_refl eq_refl eq_refl
             ltac:(unfold OD_DBL_CREDIT; lia) (proj1 AO) NX F'' I'').
  -
    intros HH. unfold arm_k. intros yra yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys2 ys5 ys6 ys10 yt3 yt5 yt6 yF yfc m' F' I'. apply evt_done.
    eapply (DBL Σ K E mL st); [exact G| exact R| exact HL| exact HH| unfold OD_DBL_CREDIT in *; lia| exact F'| exact I'|].
    unfold od_plus_kc. intros Σ1 m0' st' z352 zra zt0 zt1 zt2 za0 za1 za2 za3 za4 za5 za6 za7 zs2 zs5 zs6 zs10 zs11 zt3 zt4 zt5 zt6 zF zfc m1' R1 LV1 FRS1 SP1 CR1 AO F1 I1.
    eapply (od_plus_cps Σ1 K (oa_rebase E m0') mL c st st' z352); [exact (od_geo_rebase E m0' G)| exact R1| exact HL| lia| exact AO| exact F1| exact I1| |].
    + apply (od_exit_kc_weaken Σ Σ1 K (oa_rebase E m0') mL c c); [exact KX| exact LV1| exact FRS1| exact SP1| lia].
    + intros st'' w336 w352 wra wt0 wt1 wt2 wa0 wa1 wa2 wa3 wa4 wa5 wa6 ws5 ws6 wt3 wt4 wt5 wt6 wF wfc m2 NX F'' I''.
      exact (HK Σ1 m0' st' st'' w336 w352 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 R1 LV1 FRS1 SP1 CR1 (proj1 AO) NX F'' I'').
Qed.

Theorem od_loopB : forall (fuel : nat) (Σ : rts RT) (K : config -> Prop) (E : oaenv) (mL : mem) st0 st v336 v352
    xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xs5 xs6 xt3 xt4 xt5 xt6 xF xfc m1,
  od_geo E -> od_rt RT Σ E mL -> HLASTP E ->
  o_left (o_idxs E) st <= Z.of_nat fuel -> OD_DBL_CREDIT * (Z.of_nat fuel + 1) <= rt_credit RT Σ ->
  od_head_pre E st0 st -> frm0 xfc -> ODINVh E v336 v352 st m1 ->
  od_exit_kc RT PMc Σ K E mL (rt_credit RT Σ - OD_DBL_CREDIT * (Z.of_nat fuel + 1)) ->
  aevt Σ K (ODHST E xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xs5 xs6 xt3 xt4 xt5 xt6 xF xfc m1).
Proof using AF MST HEAD HEXIT PLUS DBL.
  induction fuel as [|f IH];
    intros Σ K E mL st0 st v336 v352 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xs5 xs6 xt3 xt4 xt5 xt6 xF xfc m1 G R HL HF CR PRE FRM INV KX.
  - eapply (od_pass Σ K E mL (rt_credit RT Σ - OD_DBL_CREDIT * (Z.of_nat 0 + 1)) st0 st v336 v352);
      [exact G| exact R| exact HL| unfold OD_DBL_CREDIT in *; lia| unfold OD_DBL_CREDIT in *; lia| exact PRE| exact FRM| exact INV| exact KX|].
    intros Σ1 m0' st' st'' w336 w352 yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ys5 ys6 yt3 yt4 yt5 yt6 yF yfc m2 R1 LV1 FRS1 SP1 CR1 AP NX F'' I''.
    exfalso. destruct NX as (A1 & A2 & _). unfold o_left in HF. cbn [Z.of_nat] in HF. lia.
  - eapply (od_pass Σ K E mL (rt_credit RT Σ - OD_DBL_CREDIT * (Z.of_nat (S f) + 1)) st0 st v336 v352);
      [exact G| exact R| exact HL| unfold OD_DBL_CREDIT in *; lia| unfold OD_DBL_CREDIT in *; lia| exact PRE| exact FRM| exact INV| exact KX|].
    intros Σ1 m0' st' st'' w336 w352 yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ys5 ys6 yt3 yt4 yt5 yt6 yF yfc m2 R1 LV1 FRS1 SP1 CR1 AP NX F'' I''.
    eapply (IH Σ1 K (oa_rebase E m0') mL st' st'' w336 w352); try eassumption.
    + exact (od_geo_rebase E m0' G).
    + destruct NX as (A1 & A2 & _). unfold o_left in *. cbn [oa_rebase od_rebase oa_E o_idxs]. lia.
    + unfold OD_DBL_CREDIT in *. lia.
    + left. exact NX.
    + apply (od_exit_kc_weaken Σ Σ1 K (oa_rebase E m0') mL _ _ KX LV1 FRS1 SP1). unfold OD_DBL_CREDIT in *. lia.
Qed.

End Loop.
