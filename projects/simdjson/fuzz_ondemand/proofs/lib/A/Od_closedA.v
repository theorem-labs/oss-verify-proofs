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
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Spec Require Import Prelim.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Sj_stage1_kit Atp_h_defs.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.A Require Import Layout Shadow RT_iface RT_iface2 RT_anndefs D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_rtf Sj_akit Sj_acps
  Sj_hkit Sj_hkit2 Sj_new Sj_num_akit Sj_num_amem Od_hbaseA Atp_h_defsA Od_defsA Od_cpsA Od_loopA Od_hkit0A Od_deldtorA Od_beginA Od_topA
  Od_headA Od_plusA Od_arm_rawA Od_arm_contA Od_arm_litA Od_arm_nullA Od_arm_intA Od_arm_strA Od_arm_nestA Od_pstr_defsA Od_pstrA Od_fromchA
  Od_arm_dbl_closedA Od_arm_dbl_exitA Od_arm_dblcA Od_exitA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition od_shb0 (E : oaenv) : Prop :=
  ro_cells asegs (o_m0 E) g_GOT_shadow_offset_cell [C8 (Z_to_bv 64 g_shadow_memory_dynamic_address)] /\
  ro_cells asegs (o_m0 E) g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)].

Section Closed.
Variable RT : rt_sig.
Variable LIB : mem -> Prop.
Hypothesis AF : art_facts RT.
Hypothesis LIB_loc : fp_local LIB_FP LIB.
Hypothesis RTF : rt_contracts_f RT.
Hypothesis DELA : del_cps RT e_delarr.
Hypothesis DTOR : deldtor_cps RT.
Hypothesis VDES : vdestroy_cpsA RT.
Hypothesis AFV : forall Σ m, ART RT Σ m -> vt_dpi m.
Hypothesis AFG : forall Σ m, ART RT Σ m -> ro_cells asegs m OD_GOT_TABS od_got_cells.
Hypothesis HFROMCH : forall PMc, fdfs_only PMc -> mat_stable PMc -> fromcha_stmt RT PMc.
Hypothesis SETUP : forall PMc, fdfs_only PMc -> mat_stable PMc -> od_setup_stmt RT LIB PMc.

Lemma od_shb0_of_rt : forall Σ E mL, od_rt RT Σ E mL -> od_shb0 E.
Proof.
  intros Σ E mL R. pose proof (af_client_consts RT AF Σ (o_m0 E) (ort_art RT Σ E mL R)) as (C1 & C2 & _). split; [exact C1| exact C2].
Qed.

Lemma HEADc : forall E, od_oka E -> od_shb0 E -> HLASTP E -> od_head_stmt E.
Proof.
  intros E OK (G1 & G2) HL.
  exact (od_head E OK HL (od_arm_string_base E OK pstra_spec G1 G2) (od_arm_bool E OK) (od_arm_array E OK) (od_arm_int64 E OK)
           (od_arm_object E OK) (od_arm_uint64 E OK) (od_arm_raw E OK) (od_arm_null E OK) (od_arm_begin E OK) (od_arm_nest E OK)).
Qed.
Definition HEXITc := od_head_exit.
Lemma PLUSc : forall E, od_oka E -> HLASTP E -> od_plus_stmt E.
Proof. exact od_plus_top. Qed.
Lemma EXITPc : forall PMc, fdfs_only PMc -> mat_stable PMc -> od_exitp_stmt RT LIB PMc.
Proof. intros PMc FDO MST. exact (od_exit RT LIB LIB_loc AF PMc FDO MST RTF DELA DTOR VDES AFV). Qed.

Section WithPM.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.
Notation aevt := (aevt RT PMc).

Lemma DBLc : arm_dbl_cps RT PMc.
Proof. exact (od_arm_dbl_cps RT AF PMc MST AFV AFG (HFROMCH PMc FDO MST) arm_dbl_evt_closed dbl_resume). Qed.

Lemma od_plus_cps2 : forall (Σ : rts RT) (K : config -> Prop) (E : oaenv) (mL : mem) c st st'
    xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs9 xs10 xs11 xt3 xt4 xF xfc m1,
  od_geo E -> od_rt RT Σ E mL -> HLASTP E -> c <= rt_credit RT Σ ->
  od_arm_out (o_bs E) (o_idxs E) st st' -> frm0 xfc -> ODINV E st' m1 ->
  od_exit_kc RT PMc Σ K E mL c ->
  (forall st'' v344 yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys2 ys9 ys10 ys11 yt3 yt4 yF yfc m2,
     od_next_ok (o_bs E) (o_idxs E) 1 st' st'' -> frm0 yfc -> ODINVh E v344 st'' m2 ->
     aevt Σ K (ODST E OD_HEAD yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys2 ys9 ys10 ys11 yt3 yt4 yF yfc m2)) ->
  aevt Σ K (ODST E OD_PLUS xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs9 xs10 xs11 xt3 xt4 xF xfc m1).
Proof.
  intros Σ K E mL c st st' xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs9 xs10 xs11 xt3 xt4 xF xfc m1 G R HL CR AO FRM INV KX HK.
  pose proof (od_oka_of_rt RT AF Σ E mL G R) as OK.
  apply (aevt_evt RT AF PMc MST).
  apply (PLUSc E OK HL (fun ms => aevt Σ K ms) st st' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 AO FRM INV).
  unfold od_head_k. intros st'' v344 yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys2 ys9 ys10 ys11 yt3 yt4 yF yfc m2 PRE'' F'' I''.
  destruct PRE'' as [NX|DEAD].
  - apply evt_done. exact (HK st'' v344 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 NX F'' I'').
  - apply (HEXITc E OK (fun ms => aevt Σ K ms) st'' v344); [destruct DEAD as (_ & DD & _); lia| exact F''| exact I''|].
    exact (od_exit_k_of_kc RT PMc Σ K E mL c R CR KX).
Qed.

Lemma od_pass2 : forall (Σ : rts RT) (K : config -> Prop) (E : oaenv) (mL : mem) c st0 st v344
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
Proof.
  intros Σ K E mL c st0 st v344 xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs9 xs10 xs11 xt3 xt4 xF xfc m1 G R HL C0 CR PRE FRM INV KX HK.
  pose proof (od_oka_of_rt RT AF Σ E mL G R) as OK.
  assert (CRx : c <= rt_credit RT Σ) by (unfold OD_DBL_CREDIT in CR; lia).
  apply (aevt_evt RT AF PMc MST).
  apply (HEADc E OK (od_shb0_of_rt Σ E mL R) HL (fun ms => aevt Σ K ms) st0 st v344 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 PRE FRM INV).
  -   exact (od_exit_k_of_kc RT PMc Σ K E mL c R CRx KX).
  -
    unfold od_plus_k. intros st' yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys2 ys9 ys10 ys11 yt3 yt4 yF yfc m' AO F' I'.
    apply evt_done.
    apply (od_plus_cps2 Σ K E mL c st st' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m' G R HL CRx AO F' I' KX).
    intros st'' v344' zt0 zt1 zt2 za0 za1 za2 za3 za4 za5 za6 za7 zs2 zs9 zs10 zs11 zt3 zt4 zF zfc m2 NX F'' I''.
    exact (HK Σ (o_m0 E) st' st'' v344' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 (od_rt_self RT Σ E mL R) eq_refl eq_refl eq_refl
             ltac:(unfold OD_DBL_CREDIT; lia) (proj1 AO) NX F'' I'').
  -
    intros HH. unfold arm_k. intros yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys11 yt3 yt4 yF yfc m' F' I'. apply evt_done.
    apply (DBLc Σ K E mL st _ _ _ _ _ _ _ _ _ _ _ _ _ yfc m' G R HL HH ltac:(unfold OD_DBL_CREDIT in *; lia) F' I').
    unfold od_plus_kc. intros Σ1 m0' st' zt0 zt1 zt2 za0 za1 za2 za3 za4 za5 za6 za7 zs2 zs9 zs10 zs11 zt3 zt4 zF zfc m1' R1 LV1 FRS1 SP1 CR1 AO F1 I1.
    apply (od_plus_cps2 Σ1 K (oa_rebase E m0') mL c st st' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1' (od_geo_rebase E m0' G) R1 HL
             ltac:(lia) AO F1 I1).
    + apply (od_exit_kc_weaken RT PMc Σ Σ1 K (oa_rebase E m0') mL c c); [exact KX| exact LV1| exact FRS1| exact SP1| lia].
    + intros st'' v344' wt0 wt1 wt2 wa0 wa1 wa2 wa3 wa4 wa5 wa6 wa7 ws2 ws9 ws10 ws11 wt3 wt4 wF wfc m2 NX F'' I''.
      exact (HK Σ1 m0' st' st'' v344' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 R1 LV1 FRS1 SP1 CR1 (proj1 AO) NX F'' I'').
Qed.

Theorem od_loop2A : forall (fuel : nat) (Σ : rts RT) (K : config -> Prop) (E : oaenv) (mL : mem) st0 st v344
    xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs9 xs10 xs11 xt3 xt4 xF xfc m1,
  od_geo E -> od_rt RT Σ E mL -> HLASTP E ->
  o_left (o_idxs E) st <= Z.of_nat fuel -> OD_DBL_CREDIT * (Z.of_nat fuel + 1) <= rt_credit RT Σ ->
  od_head_pre E st0 st -> frm0 xfc -> ODINVh E v344 st m1 ->
  od_exit_kc RT PMc Σ K E mL (rt_credit RT Σ - OD_DBL_CREDIT * (Z.of_nat fuel + 1)) ->
  aevt Σ K (ODST E OD_HEAD xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs9 xs10 xs11 xt3 xt4 xF xfc m1).
Proof.
  induction fuel as [|f IH];
    intros Σ K E mL st0 st v344 xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs9 xs10 xs11 xt3 xt4 xF xfc m1 G R HL HF CR PRE FRM INV KX.
  - apply (od_pass2 Σ K E mL (rt_credit RT Σ - OD_DBL_CREDIT * (Z.of_nat 0 + 1)) st0 st v344 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 G R HL
             ltac:(unfold OD_DBL_CREDIT in *; lia) ltac:(unfold OD_DBL_CREDIT in *; lia) PRE FRM INV KX).
    intros Σ1 m0' st' st'' v344' yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys2 ys9 ys10 ys11 yt3 yt4 yF yfc m2 R1 LV1 FRS1 SP1 CR1 AP NX F'' I''.
    exfalso. destruct NX as (A1 & A2 & _). unfold o_left in HF. cbn [Z.of_nat] in HF. lia.
  - apply (od_pass2 Σ K E mL (rt_credit RT Σ - OD_DBL_CREDIT * (Z.of_nat (S f) + 1)) st0 st v344 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 G R HL
             ltac:(unfold OD_DBL_CREDIT in *; lia) ltac:(unfold OD_DBL_CREDIT in *; lia) PRE FRM INV KX).
    intros Σ1 m0' st' st'' v344' yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys2 ys9 ys10 ys11 yt3 yt4 yF yfc m2 R1 LV1 FRS1 SP1 CR1 AP NX F'' I''.
    apply (IH Σ1 K (oa_rebase E m0') mL st' st'' v344'); try assumption.
    + exact (od_geo_rebase E m0' G).
    + destruct NX as (A1 & A2 & _). unfold o_left in *. cbn [oa_rebase od_rebase oa_E o_idxs]. lia.
    + unfold OD_DBL_CREDIT in *. lia.
    + left. exact NX.
    + apply (od_exit_kc_weaken RT PMc Σ Σ1 K (oa_rebase E m0') mL _ _ KX LV1 FRS1 SP1). unfold OD_DBL_CREDIT in *. lia.
Qed.

End WithPM.

Theorem fuzz_one_closed_odA : fuzz_one_cps RT LIB.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m d bs lo
    FDO MST EA0 EA1 ETP D0 BSL BS INLV FRS0 LVPOS LVB CR0 S0C LIB0 IOS ART0 MI0 ST0 LOW LOR SPT SPA SPLE FRM.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
  match goal with |- cps asegs _ ?K0 => set (K := K0) end.

  assert (KFIN : od_fin_k RT LIB PMc K Σ usp lo ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m (rt_credit RT Σ - FUZZ_COST)).
  { unfold od_fin_k. intros Σ' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' FRM' ART' MI' ST' PR' LIB' LV' FRS' SP' CR'.
    apply (aevt_done RT PMc). intros c Hc. subst K. cbv beta. split.
    - exists Σ'. split; [| split; [exact LV'| split; [exact FRS'| split; [exact SP'| exact CR']]]].
      eapply ASTA_conseq; [exact Hc|]. intros ms <-. exists m'. subst tp.
      split; [rewrite ESP; do 16 eexists; reflexivity|]. split; [split; [exact ART'| split; [exact MI'| exact ST']]|].
      split; [rewrite FRS0; exact PR'| exact LIB'].
    - rewrite (asta_eq_fcsr RT Σ' PMc _ c Hc). exact FRM'. }
  eapply cps_conseq; [| intros c [Hc _]; exact Hc| intros c Hc; exact Hc].
  apply (SETUP PMc FDO MST Σ K ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m d bs lo
           FDO MST EA0 EA1 ETP D0 BSL BS INLV FRS0 LVPOS LVB CR0 LIB0 ART0 MI0 ST0 LOW LOR SPT SPA FRM); [| exact KFIN].

  intros Σ1 E A cap size IA OC els xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs8 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m1
    G R PRE EM0 OUT EUSP ELO EGP SP1 CR1 FRM1.
  pose proof (od_oka_of_rt RT AF Σ1 E m1 G R) as OK.
  pose proof (od_n_range E (og_s1 _ G)) as NR.
  assert (KFIN1 : od_fin_k RT LIB PMc K Σ (oa_USP E) (o_lo E) ra (o_gp E) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m (rt_credit RT Σ - FUZZ_COST))
    by (rewrite EUSP, ELO, EGP; exact KFIN).

  assert (KX : forall c, rt_credit RT Σ - FUZZ_COST <= c -> od_exit_kc RT PMc Σ1 K E m1 c).
  { intros c Hc. unfold od_exit_kc.
    intros Σ' m0' st vs6 v224 v248 v304 v312 v328 v344 yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys2 ys5 ys6 ys7 ys8 ys9 ys10 ys11 yt3 yt4 yt5 yt6 yF yfc m2
      R' LV' FRS' SP' CR' FRM' INV'.
    exact (EXITPc PMc FDO MST Σ Σ' K (oa_rebase E m0') m1 m A cap size IA OC els (rt_live RT Σ) ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             (rt_credit RT Σ - FUZZ_COST) st vs6 v224 v248 v304 v312 v328 v344 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ yF yfc m2
             (od_geo_rebase E m0' G) R' (od_outer_rebase RT LIB Σ1 Σ' E m0' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ OUT LV') eq_refl
             ltac:(rewrite SP'; exact SP1) ltac:(lia) FRM' INV' KFIN1). }
  apply (aevt_evt RT AF PMc MST).
  apply (od_iterate E OK (fun ms => aevt RT PMc Σ1 K ms) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ xF xfc m1 PRE FRM1 EM0).
  -
    apply (od_exit_k_of_kc RT PMc Σ1 K E m1 (rt_credit RT Σ - FUZZ_COST) R); [unfold OD_DBL_CREDIT in CR1; lia|].
    apply KX. lia.
  -
    intros HL. unfold od_head_k. intros st v344 yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys2 ys9 ys10 ys11 yt3 yt4 yF yfc m2 PRE2 FRM2 INV2.
    apply evt_done.
    destruct PRE2 as [NX|DEAD].
    + apply (od_loop2A PMc FDO MST (Z.to_nat (o_n E + 1)) Σ1 K E m1 od_init st v344
               _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ yfc m2 G R HL);
        [ destruct NX as ((A1 & A2) & _); unfold o_left, od_init in *; cbn [o_pos] in A1; rewrite Z2Nat.id by lia; lia
        | rewrite Z2Nat.id by lia; unfold OD_DBL_CREDIT in *; lia | left; exact NX | exact FRM2 | exact INV2 | ].
      apply KX. rewrite Z2Nat.id by lia. unfold OD_DBL_CREDIT in *. lia.
    + apply (aevt_evt RT AF PMc MST).
      apply (HEXITc E OK (fun ms => aevt RT PMc Σ1 K ms) st v344 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ yfc m2);
        [destruct DEAD as (_ & DD & _); lia| exact FRM2| exact INV2|].
      apply (od_exit_k_of_kc RT PMc Σ1 K E m1 (rt_credit RT Σ - FUZZ_COST) R); [unfold OD_DBL_CREDIT in CR1; lia|].
      apply KX. lia.
Qed.

End Closed.
