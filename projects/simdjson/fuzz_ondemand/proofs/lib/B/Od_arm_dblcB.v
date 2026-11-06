(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjOd SjNumber.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.B Require Import Layout RT_iface D_defs D_kit D_clx Sj_akit Sj_acps Sj_hkit Sj_rtf Sj_num_akit Sj_num_amem
  Sj_num_iface Sj_num_bdefs Od_defsB Od_cpsB Od_fromchB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Open Scope Z_scope.

Section DblC.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable PMc : Model -> Prop.
Hypothesis MST : mat_stable PMc.

Hypothesis AFV : forall Σ m, ART RT Σ m -> ro_cells bsegs m OD_DPI_VT od_vt_cells.
Hypothesis AFG : forall Σ m, ART RT Σ m -> ro_cells bsegs m OD_GOT_TABS od_got_cells.

Hypothesis HFROMCH : fromchb_stmt RT PMc.

Hypothesis DBLE : forall E, od_oka E -> od_shb E -> arm_dbl_evt E.
Hypothesis DBLR : forall E, od_oka E -> od_shb E -> dbl_resume_stmt E.

Notation aevt := (aevt RT PMc).

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, SHB in *; lia.

Lemma od_client_outside : forall Σ E mL m a, od_geo E -> od_rt RT Σ E mL -> ART RT Σ m ->
  aclient (rt_live RT Σ) (rt_frames RT Σ) (oa_S1 E + 384) a -> outside (od_Wk E) a -> outside (od_W E) a.
Proof using AF.
  intros Σ E mL m a G R HA Ha Ho. unfold od_W. unfold od_Wk in Ho. cbn [outside] in *. split; [| exact Ho].
  destruct (aclient_split_c RT AF Σ m (oa_S1 E + 384) a HA Ha) as [H|H]; [lia|].
  pose proof (ort_lo _ _ _ _ R). lia.
Qed.

Lemma od_rt_after_call : forall Σ Σ' E mL m1 m2, od_geo E -> od_rt RT Σ E mL ->
  munch (od_W E) (o_m0 E) m1 -> wmono bsegs (o_m0 E) m1 ->
  ART RT Σ' m2 -> wmono bsegs m1 m2 -> rt_pres (rt_live RT Σ) (rt_frames RT Σ) (oa_S1 E) m1 m2 ->
  rt_frames RT Σ' = rt_frames RT Σ -> rt_live RT Σ' = rt_live RT Σ -> rt_sp0 RT Σ' = rt_sp0 RT Σ ->
  od_rt RT Σ' (oa_rebase E m2) mL.
Proof using AF.
  intros Σ Σ' E mL m1 m2 G R MU WM ART2 WM2 PR EF EL ES.
  pose proof (od_art_cur RT AF Σ E mL m1 G R MU WM) as ART1.
  pose proof R as [ART0 FRS COPYI SBI IMPLI IDXI LOI SHP SHD KEEP WML].
  assert (INF : In (oa_F E, 3%nat) (rt_frames RT Σ)) by (rewrite FRS; left; reflexivity).
  assert (F8 : oa_F E mod 8 = 0) by (destruct (og_F _ G) as [F64 _]; clear - F64; Z.div_mod_to_equations; lia).
  assert (SHC : forall j k, 0 <= j -> j + k <= 64 -> 0 <= k ->
            forall x, oa_F E / 8 + 2147450880 + j <= x < oa_F E / 8 + 2147450880 + j + k ->
            aclient (rt_live RT Σ) (rt_frames RT Σ) (oa_S1 E) x).
  { intros j k J0 JK K0 x Hx. right; right; right; right. exists (oa_F E), 3%nat. split; [exact INF|].
    unfold shad, SHB, fs_size. change (Z.shiftl 64 (Z.of_nat 3)) with 512.
    clear - F8 Hx J0 JK K0. Z.div_mod_to_equations; lia. }
  constructor; cbn [oa_rebase od_rebase oa_E oa_F oa_S1 oa_USP o_m0 o_COPY o_BUF o_bs o_SB o_CAP o_IMPL o_IDX o_icap o_lo].
  - exact ART2.
  - rewrite EF. exact FRS.
  - rewrite EL. exact COPYI.
  - rewrite EL. exact SBI.
  - rewrite EL. exact IMPLI.
  - rewrite EL. exact IDXI.
  - rewrite ES. exact LOI.
  - pose proof (bytes_at_transport bsegs (od_W E) (o_m0 E) m1 _ _ SHP MU
                  ltac:(rewrite repeat_length; exact (od_W_shadow_apart E 12 7 G ltac:(lia) ltac:(lia) ltac:(lia)))) as B1.
    apply (bytes_at_agree bsegs m1 m2 _ _ B1). apply (agree_of_pres _ _ _ _ _ _ PR).
    intros x Hx. rewrite repeat_length in Hx. exact (SHC 12 7 ltac:(lia) ltac:(lia) ltac:(lia) x Hx).
  - pose proof (bytes_at_transport bsegs (od_W E) (o_m0 E) m1 _ _ SHD MU
                  ltac:(rewrite repeat_length; exact (od_W_shadow_apart E 24 8 G ltac:(lia) ltac:(lia) ltac:(lia)))) as B1.
    apply (bytes_at_agree bsegs m1 m2 _ _ B1). apply (agree_of_pres _ _ _ _ _ _ PR).
    intros x Hx. rewrite repeat_length in Hx. exact (SHC 24 8 ltac:(lia) ltac:(lia) ltac:(lia) x Hx).
  - rewrite EL, EF. fold (od_Wk E).
    apply (pres_fp_trans _ _ _ _ mL (o_m0 E) m2 KEEP).
    apply (pres_fp_trans _ _ _ _ (o_m0 E) m1 m2).
    + apply (pres_fp_of_munch _ _ _ _ (od_W E) _ _ MU). intros a Ha Ho. exact (od_client_outside Σ E mL (o_m0 E) a G R ART0 Ha Ho).
    + intros a Ha _. apply PR. eapply aclient_mono; [exact Ha| auto| auto| lia].
  - exact (wmono_trans bsegs _ _ _ WML (wmono_trans bsegs _ _ _ WM WM2)).
Qed.

Lemma od_inv_after_call : forall Σ Σ' E mL st m1 m2, od_geo E -> od_rt RT Σ E mL ->
  DBLINVs E st m1 ->
  rt_after RT Σ' (oa_S1 E) (o_lo E) m1 m2 -> rt_pres (rt_live RT Σ) (rt_frames RT Σ) (oa_S1 E) m1 m2 ->
  DBLINVs (oa_rebase E m2) st m2.
Proof using AF AFV AFG.
  intros Σ Σ' E mL st m1 m2 G R INV (ART2 & MI2 & WM2 & ST2) PR.
  pose proof R as [ART0 FRS COPYI SBI IMPLI IDXI LOI SHP SHD KEEP WML].
  assert (INF : In (oa_F E, 3%nat) (rt_frames RT Σ)) by (rewrite FRS; left; reflexivity).
  destruct INV as (j96 & j104 & j224 & j232 & j272 & INV).
  od_open_invc INV. og_env G. clear VT GOT MI MU WM ST.
  assert (AG : agree_on (fun x => aclient (rt_live RT Σ) (rt_frames RT Σ) (oa_S1 E) x) m1 m2) by (intros a Ha; exact (PR a Ha)).

  assert (IDXA2 : u32arr bsegs m2 (o_IDX E) ws).
  { apply (u32arr_agree m1 m2 _ _ IDXA); [| exact WM2]. eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in *.
    right; right; left. exists (o_IDX E), (4 * Z.of_nat (o_icap E)). split; [exact IDXI|]. rewrite IDXL in Hx. lia. }
  clear IDXA.
  unfold fs_size in *.
  rt_transport_with m1 m2 AG WM2 ltac:(intros x Hx; cbn [cells_size csize Nat.add length] in Hx; rewrite ?PBL in Hx; cbv beta;
                                       first [ left; unfold USTACK_TOP in *; lia
                                             | right; right; right; left; exists (oa_F E), 3%nat; split; [exact INF|];
                                               unfold fs_size; change (Z.shiftl 64 (Z.of_nat 3)) with 512; lia
                                             | right; right; left; exists (o_IMPL E), 96; split; [exact IMPLI| lia]
                                             | right; right; left; eexists (o_COPY E), _; split; [exact COPYI| lia] ]).
  pose proof (AFV Σ' m2 ART2) as VT. pose proof (AFG Σ' m2 ART2) as GOT.
  pose proof (munch_refl (od_W E) m2) as MU. pose proof (wmono_refl bsegs m2) as WM.
  exists j96, j104, j224, j232, j272.
  unfold ODINVc, fr_k8, fr_k96, fr_k240, iter_cells, od_parser_cells, dpi_cells, wz.
  cbn [oa_rebase od_rebase oa_E oa_F oa_S1 oa_USP o_m0 o_COPY o_BUF o_bs o_SB o_CAP o_IMPL o_IDX o_icap o_lo o_act o_idxs
       o_vptr o_p12 o_nxt o_mid o_docj o_j304 o_w320 o_w328 o_w336 o_w344].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
  split; [ do 2 eexists; eassumption | ].
  split; [eassumption|]. split; [eassumption|].
  split; [ exists ws; split; [exact IDXA2| split; [exact IDXL| exact IDXF]] | ].
  split; [eassumption|]. split; [eassumption|].
  split; [exact VT|]. split; [exact GOT|].
  split; [exact MI2|]. split; [exact MU|]. split; [exact WM| exact ST2].
Qed.

Theorem od_arm_dbl_cps : arm_dbl_cps RT PMc.
Proof using AF MST AFV AFG HFROMCH DBLE DBLR.
  unfold arm_dbl_cps.
  intros Σ K E mL st xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xs6 xs10 xt3 xt5 xt6 xF xfc m1 G R HL HH CR FRM INV KP.
  pose proof (od_oka_of_rt RT AF Σ E mL G R) as OK. pose proof (od_shb_of_rt RT AF Σ E mL G R) as HG.
  apply (aevt_evt RT AF PMc MST).
  apply (DBLE E OK HG (fun ms => aevt Σ K ms) st HL HH); [| | exact FRM| exact INV].
  -
    unfold od_plus_k. intros st' w352 yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys2 ys5 ys6 ys10 ys11 yt3 yt4 yt5 yt6 yF yfc m' AO F' I'.
    apply evt_done.
    eapply (KP Σ (o_m0 E) st' w352); [exact (od_rt_self RT Σ E mL R)| reflexivity| reflexivity| reflexivity
                                     | unfold OD_DBL_CREDIT; lia| exact AO| exact F'| exact I'].
  -
    unfold od_slow_k. intros yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys5 ys6 ys10 ys11 yt3 yt4 yt5 yt6 yF yfc m' F' I'.
    apply evt_done.
    pose proof I' as (j96 & j104 & j224 & j232 & j272 & INV0). od_open_invc INV0. og_env G.
    pose proof R as [ART0 FRS COPYI SBI IMPLI IDXI LOI SHP SHD KEEP WML].
    fold (od_W E) in MU.
    pose proof (od_art_cur RT AF Σ E mL m' G R MU WM) as ART1.
    pose proof HH as (HP & _).
    pose proof (od_tokI_range E S1 (o_pos st) ltac:(lia)) as TR.
    assert (EU : bv_unsigned (Z_to_bv 64 (oa_S1 E)) = oa_S1 E) by (apply unsigned_lit; lia).
    assert (FST : FFB_STACK = 66448) by reflexivity.
    eapply (HFROMCH Σ K) with (A := o_BUF E) (off := tokI (o_bs E) (o_idxs E) (o_pos st)) (stop := o_len E) (lo := o_lo E)
                              (p := o_COPY E) (n := o_BUF E - o_COPY E + o_len E + 64) (txt := padded_bytes (o_bs E)) (b := Z_to_bv 8 0);
      rewrite ?EU, ?PBL;
      [ exact ETP | exact F' | rewrite FRS; unfold FFB_FRAMES, FRAMES_MAX; cbn [length]; lia
      | unfold FFB_CREDIT, OD_DBL_CREDIT in *; lia | exact ART1 | exact MI | exact ST | exact LOI
      | rewrite FST; clear - LOR; lia | unfold USTACK_TOP; lia
      | clear - S32; Z.div_mod_to_equations; lia | exact COPYI | exact CP8 | lia | lia | lia | exact BUFRO | lia | lia
      | rewrite (nth_error_padded (o_bs E) (o_len E)) by lia; rewrite (B_pad (o_bs E) (o_len E)) by lia; reflexivity
      | reflexivity | ].

    intros Σ' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F'' fc'' m'' FRM'' RA PR EF EL ES EC.
    rewrite ?EU in RA, PR.
    pose proof (od_rt_after_call Σ Σ' E mL m' m'' G R MU WM (proj1 RA) (proj1 (proj2 (proj2 RA))) PR EF EL ES) as R2.
    pose proof (od_inv_after_call Σ Σ' E mL st m' m'' G R I' RA PR) as I2.
    pose proof (od_geo_rebase E m'' G) as G2.
    pose proof (od_oka_of_rt RT AF Σ' (oa_rebase E m'') mL G2 R2) as OK2. pose proof (od_shb_of_rt RT AF Σ' (oa_rebase E m'') mL G2 R2) as HG2.
    apply (aevt_evt RT AF PMc MST).
    replace (ret_pc (Z_to_bv 64 0x9b15c)) with (Z_to_bv 64 0x9b15c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    eapply (DBLR (oa_rebase E m'') OK2 HG2 (fun ms => aevt Σ' K ms) st); [exact HL| exact HH| | exact FRM''| exact I2].
    unfold od_plus_k. intros st' w352 zra zt0 zt1 zt2 za0 za1 za2 za3 za4 za5 za6 za7 zs2 zs5 zs6 zs10 zs11 zt3 zt4 zt5 zt6 zF zfc m3 AO F3 I3.
    apply evt_done.
    eapply (KP Σ' m'' st' w352); [exact R2| exact EL| exact EF| exact ES| unfold FFB_CREDIT, OD_DBL_CREDIT in *; lia| exact AO| exact F3| exact I3].
Qed.

End DblC.
