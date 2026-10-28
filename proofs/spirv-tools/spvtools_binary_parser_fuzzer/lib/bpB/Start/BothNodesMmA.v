(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPropExec BCatExec BCatSim BSeqExec BStoreOk BShapeAlg BpinAlg BAgentLib BAgentNodes BNodes BAllocSim BothAcct BothAcctShape BothPlacement BackingBlgebra BMmapSim BRefNodes BoReserve Bcfg BothRefNodes BothCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BxSymExec3 BxSymExec3Sound BxSymRun3 BothPlanCore BothPlan BothPlanSound BothNodesIface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BothNodesLibE.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BothNodesMmLib.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Import AX2. Import AX2S. Import AP. Import APS.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma mmap_flags_core_104022 : mmap_flags_core (Z_to_bv 64 1064994) = 1048610%Z. Proof. vm_compute. reflexivity. Qed.
Lemma mmap_noreserve_b_104022 : mmap_noreserve_b (Z_to_bv 64 1064994) = true.  Proof. vm_compute. reflexivity. Qed.

Section Nodes.
Variable SEGS : list Segment.            Variable A : atable.
Variable nx0 : nat.                      Variable LIMIT : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.     Variable FS0 : Fs.Fs.
Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis RES_len : res_len_ok SEGS A.
Hypothesis RES_hull : Forall (fun iv => img_lo A <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_hi A)
                             (segments_reserved SEGS).

Hypothesis RES_cover : img_lo A < img_hi A /\ forall z, img_lo A <= z < img_hi A ->
  exists iv, In iv (segments_reserved SEGS) /\ bv_unsigned (fst iv) <= z < bv_unsigned (fst iv) + bv_unsigned (snd iv).
Hypothesis HULL_ok : hull_ok A.                  Hypothesis SHADOW_ok : shadow_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Hypothesis argH_sp0 : forall E (a : word), argH E a = true -> bv_unsigned (edenot E e_sp0_early) <= bv_unsigned a.
Hypothesis E_SP0 : AP.expr_vars_lt nx0 e_sp0_early = true.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.

Hypothesis SINV_pg : forall E M, SINV E M -> uE E e_pg_early = pagedown (uE E e_sp0_early).
Context {SC : StepCfg} {AF : AllocForced SC}.

#[local] Notation CSOK := (APS.cs_ok SEGS A LIMIT SINV argH FS0).
#[local] Notation HID := (APS.hid A argH).
#[local] Notation VIS := (APS.vis A).
#[local] Notation MR := (APS.Mr A argH).
#[local] Notation ALLOW := (APS.allowA A).
#[local] Notation cfg := (cfg_of SEGS).

Let HS : nat -> option acs := fun _ => None.
Let XN : nat -> list expr -> acs -> option acs := fun _ _ _ => None.
Let XE : nat -> list expr -> acs -> option (Z * list spiece * acs) := fun _ _ _ => None.
Let XB : nat -> list expr -> acs -> option (acs * acs) := fun _ _ _ => None.
Let RES_len' : length (segments_reserved SEGS) = n_res A := RES_len.
Let HULL_ok' : 0 <= img_lo A /\ img_lo A mod 4096 = 0 /\ img_hi A mod 4096 = 0 /\ img_hi A <= KHI := HULL_ok.
Let SHADOW_ok' : 0 <= shadow_off A <= 2 ^ 47 := SHADOW_ok.
Let RES_hullH : RES_hull_def SEGS A := RES_hull.

Let reg_sound' := APS.reg_sound SEGS A LIMIT SINV argH FS0.
Let reg_lit_sound' := APS.reg_lit_sound SEGS A LIMIT SINV argH FS0.
Let kentry_keep_sem' := APS.kentry_keep_sem SEGS.
Let kentry_apart_b_sem' := APS.kentry_apart_b_sem SEGS.
Let regs_ok_set_n' := APS.regs_ok_set_n.
Let in_ivs_map_den' := APS.in_ivs_map_den.
Let kimg_clip_in_hull' := APS.kimg_clip_in_hull A.
Let cs_ok_agree' := APS.cs_ok_agree SEGS A nx0 LIMIT SINV argH E_SP0 argH_agree SINV_agree FS0.
Let cs_ok_frame' := APS.cs_ok_frame SEGS A LIMIT SINV argH SINV_frame FS0.
Let hid_agree' := APS.hid_agree A nx0 argH argH_agree.
Let vis_add_sound' := APS.vis_add_sound SEGS A LIMIT HS XN XE XB SHADOW_ok SINV argH argH_sp0 FS0 0%nat.
Let A_wf_allowA' := APS.A_wf_allowA A HS XN XE XB 0%nat.
Let know_ok_unhide' := APS.know_ok_unhide SEGS A.
Let hid_hull' := APS.hid_hull A HULL_ok argH argH_high.
Let H_off_segments_cs' := APS.H_off_segments_cs SEGS A SEGS_in_hull HULL_ok argH argH_high.
Let maps_match_exact' := APS.maps_match_exact nx0 HS XN XE XB.

Let budget_slack := BothNodesMmLib.budget_slack SEGS A LIMIT SINV argH FS0 RES_len RES_cover HULL_ok.
Let escale_4096_denot := BothNodesMmLib.escale_4096_denot SEGS A RES_len RES_cover HULL_ok.
Let find_containing_sound := BothNodesMmLib.find_containing_sound SEGS A RES_len.
Let fixed_args_sound := BothNodesMmLib.fixed_args_sound SEGS A LIMIT SINV argH FS0 RES_len RES_cover HULL_ok.
Let fixed_cs1 := BothNodesMmLib.fixed_cs1 A.
Let gap_ok_sound := BothNodesMmLib.gap_ok_sound SEGS A LIMIT SINV argH FS0 RES_len RES_cover HULL_ok SHADOW_ok.
Let gap_weight_eq := BothNodesMmLib.gap_weight_eq SEGS A RES_len.
Let grant_cs1_ok := BothNodesMmLib.grant_cs1_ok SEGS A LIMIT SINV argH FS0 RES_len RES_cover HULL_ok argH_sp0 SINV_frame.
Let grant_eager_le := BothNodesMmLib.grant_eager_le SEGS A RES_len RES_cover HULL_ok.
Let grant_keep_apart := BothNodesMmLib.grant_keep_apart SEGS A RES_len RES_cover HULL_ok.
Let grant_new_facts := BothNodesMmLib.grant_new_facts SEGS A LIMIT SINV argH FS0 RES_len RES_cover HULL_ok argH_sp0.
Let grant_vis_add := BothNodesMmLib.grant_vis_add SEGS A LIMIT SINV argH FS0 SEGS_in_hull RES_len RES_cover HULL_ok SHADOW_ok argH_high argH_sp0.
Let grant_wf := BothNodesMmLib.grant_wf SEGS A RES_len.
Let in_allow_ext := BothNodesMmLib.in_allow_ext A.
Let inside_maps_apart := BothNodesMmLib.inside_maps_apart SEGS A RES_len RES_cover HULL_ok.
Let kimg_in_hull_cons2 := BothNodesMmLib.kimg_in_hull_cons2 SEGS A RES_cover HULL_ok SHADOW_ok.
Let kimg_in_hull_pure := BothNodesMmLib.kimg_in_hull_pure A.
Let kmem_ok := BothNodesMmLib.kmem_ok SEGS A RES_len RES_cover HULL_ok.
Let kn_grant_filter_ok := BothNodesMmLib.kn_grant_filter_ok SEGS A RES_len RES_cover HULL_ok.
Let kn_rezero_clip_ok := BothNodesMmLib.kn_rezero_clip_ok SEGS A RES_len RES_cover HULL_ok.
Let kn_rezero_hull_ok := BothNodesMmLib.kn_rezero_hull_ok SEGS A RES_len RES_cover HULL_ok.
Let kn_rezero_ok_gen := BothNodesMmLib.kn_rezero_ok_gen SEGS A RES_len RES_cover HULL_ok.
Let kn_unfill_clip_ok := BothNodesMmLib.kn_unfill_clip_ok SEGS A RES_len RES_cover HULL_ok.
Let maps_match_disjoint := BothNodesMmLib.maps_match_disjoint SEGS A RES_len.
Let mmap_fixed_grant_cs1 := BothNodesMmLib.mmap_fixed_grant_cs1 SEGS A LIMIT SINV argH FS0 RES_len RES_cover HULL_ok SHADOW_ok argH_sp0 SINV_frame.
Let mmap_fixed_old_facts := BothNodesMmLib.mmap_fixed_old_facts SEGS A nx0 LIMIT SINV argH FS0 RES_len RES_hull RES_cover HULL_ok.
Let mmap_fixed_hole_facts := BothNodesMmLib.mmap_fixed_hole_facts SEGS A LIMIT SINV argH FS0 RES_len RES_cover HULL_ok SHADOW_ok.
Let fixed_pre := BothNodesMmLib.fixed_pre SEGS A LIMIT SINV argH FS0 RES_len RES_cover HULL_ok.
Let mmap_len_sound := BothNodesMmLib.mmap_len_sound SEGS A LIMIT SINV argH FS0 RES_len RES_cover HULL_ok.
Let mmap_null_cs1 := BothNodesMmLib.mmap_null_cs1 SEGS A nx0 LIMIT SINV argH FS0 RES_len RES_cover HULL_ok argH_sp0 E_SP0 argH_agree SINV_frame SINV_agree SINV_pg.
Let null_cs1 := BothNodesMmLib.null_cs1 A.
Let overlap_sum_contained := BothNodesMmLib.overlap_sum_contained SEGS A RES_len RES_cover HULL_ok.
Let page_aligned_sound := BothNodesMmLib.page_aligned_sound SEGS A RES_len.
Let refuse_cont := BothNodesMmLib.refuse_cont SEGS A nx0 LIMIT SINV argH FS0 SINV_frame.
Let refuse_ok := BothNodesMmLib.refuse_ok SEGS A LIMIT SINV argH FS0 SINV_frame.
Let region_free_of_apart := BothNodesMmLib.region_free_of_apart SEGS A nx0 LIMIT SINV argH FS0 RES_len RES_hull RES_cover HULL_ok.
Let regs_ok_regupd_same := BothNodesMmLib.regs_ok_regupd_same SEGS A RES_len.
Let reserved_free_above := BothNodesMmLib.reserved_free_above SEGS A RES_len RES_hull RES_cover HULL_ok.
Let safe_range_apart := BothNodesMmLib.safe_range_apart SEGS A RES_len RES_cover HULL_ok.
Let seps_map_disjoint := BothNodesMmLib.seps_map_disjoint SEGS A RES_len.
Let shadow_facts_new_ok := BothNodesMmLib.shadow_facts_new_ok SEGS A LIMIT SINV argH FS0 RES_len RES_cover HULL_ok SHADOW_ok.
Let slice_args := BothNodesMmLib.slice_args SEGS A LIMIT SINV argH FS0 RES_len RES_hull RES_cover HULL_ok.
Let slice_hyps := BothNodesMmLib.slice_hyps SEGS A LIMIT SINV argH FS0.
Let split_flat_estart := BothNodesMmLib.split_flat_estart SEGS A RES_len HULL_ok.
Let vis_add_inv := BothNodesMmLib.vis_add_inv A LIMIT.
Let vis_add_slice_ok := BothNodesMmLib.vis_add_slice_ok SEGS A LIMIT SINV argH FS0 SEGS_in_hull RES_len RES_cover HULL_ok SHADOW_ok argH_high argH_sp0.
Let vis_grant_out := BothNodesMmLib.vis_grant_out SEGS A RES_len.
Let page_base_aligned := BothNodesMmLib.page_base_aligned SEGS A LIMIT SINV argH FS0 RES_len HULL_ok.
Let sl_MR_out := BothNodesMmLib.sl_MR_out SEGS A LIMIT SINV argH FS0 RES_len RES_cover HULL_ok.
Let sl_bounds := BothNodesMmLib.sl_bounds SEGS A LIMIT SINV argH FS0.
Let sl_eager := BothNodesMmLib.sl_eager SEGS A LIMIT SINV argH FS0 RES_len RES_cover HULL_ok.
Let sl_in_maps := BothNodesMmLib.sl_in_maps SEGS A LIMIT SINV argH FS0 RES_len RES_cover HULL_ok.
Let sl_lazy_in := BothNodesMmLib.sl_lazy_in SEGS A LIMIT SINV argH FS0 RES_len RES_cover HULL_ok.
Let sl_lazy_out := BothNodesMmLib.sl_lazy_out SEGS A LIMIT SINV argH FS0 RES_len RES_cover HULL_ok.
Let sl_lohi := BothNodesMmLib.sl_lohi SEGS A LIMIT SINV argH FS0 RES_len RES_cover HULL_ok.
Let sl_noacc_in := BothNodesMmLib.sl_noacc_in SEGS A LIMIT SINV argH FS0 RES_len.
Let sl_noacc_out := BothNodesMmLib.sl_noacc_out SEGS A LIMIT SINV argH FS0 RES_len.
Let sl_vis_in_E := BothNodesMmLib.sl_vis_in_E SEGS A LIMIT SINV argH FS0 RES_len RES_cover HULL_ok.
Let sl_vis_in_F := BothNodesMmLib.sl_vis_in_F SEGS A LIMIT SINV argH FS0 RES_len RES_cover HULL_ok.
Let sl_vis_in_G := BothNodesMmLib.sl_vis_in_G SEGS A LIMIT SINV argH FS0 RES_len RES_cover HULL_ok.
Let sl_vis_out := BothNodesMmLib.sl_vis_out SEGS A LIMIT SINV argH FS0 RES_len RES_cover HULL_ok.
Let sl_wf' := BothNodesMmLib.sl_wf' SEGS A LIMIT SINV argH FS0 RES_len RES_cover HULL_ok.
Let slice_cs1_ok := BothNodesMmLib.slice_cs1_ok SEGS A LIMIT SINV argH FS0 RES_len RES_cover HULL_ok SHADOW_ok argH_sp0 SINV_frame.
Let null_kfacts := BothNodesMmLib.null_kfacts A.
Let kdisj_shadow_pure := BothNodesMmLib.kdisj_shadow_pure A.
Let kdisj_fixed_pure := BothNodesMmLib.kdisj_fixed_pure A.

Lemma mmap_null_sound1 : forall cs kd (eager visible : bool) cs' E R FULL model TB,
  CSOK E cs R FULL model -> is_ecall_at SEGS cs = true ->
  reg_lit cs 17 = Some 222 -> reg_lit cs 10 = Some 0 ->
  reg_lit cs 12 = Some (if kind_none kd then 0 else 3) ->
  reg_lit cs 13 = Some (if kind_lazy kd then 16418 else 34) ->
  reg_lit cs 14 = Some (two64 - 1) -> reg_lit cs 15 = Some 0 ->
  (kind_none kd || kind_lazy kd = negb eager)%bool -> is_tok_kind kd = false ->
  visible = negb (kind_none kd) ->
  mmap_null A nx0 LIMIT cs kd eager visible = Some cs' ->
  (forall E' R' FULL' model', env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> CSOK E' cs' R' FULL' model' -> m_fs model' = m_fs model ->
      srealizes SEGS (cfg R' (pc cs') FULL' model') TB) ->
  srealizes SEGS (cfg R (pc cs) FULL model) TB.
Proof.
  intros cs kd eager visible cs' E R FULL model TB HC Hec H17 H10 H12 H13 H14 H15 Hkind Hkfog Hvisible Hn HK.
  destruct (is_ecall_at_sound SEGS cs Hec) as (w & Hf & He & Hp0 & Hp4).
  pose proof Hn as Hn0.
  unfold mmap_null in Hn. rewrite kn_grant_filterM_eq in Hn.
  destruct (mmap_len cs) as [[[ne nlo] nhi]|] eqn:HML; [|discriminate].
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
  apply andb_prop in Hcond as [Hcond Hnoh].
  apply andb_prop in Hcond as [Hcond Hbud]. apply andb_prop in Hcond as [Hcond Hgap].
  apply andb_prop in Hcond as [Hfresh Hnev].

  destruct (reg_lit_sound' E cs R FULL model 17 222 HC ltac:(lia) H17) as [R17 _].
  destruct (reg_lit_sound' E cs R FULL model 10 0 HC ltac:(lia) H10) as [R10 _].
  destruct (reg_lit_sound' E cs R FULL model 12 _ HC ltac:(lia) H12) as [R12 _].
  destruct (reg_lit_sound' E cs R FULL model 13 _ HC ltac:(lia) H13) as [R13 _].
  destruct (reg_lit_sound' E cs R FULL model 14 _ HC ltac:(lia) H14) as [R14 _].
  destruct (reg_lit_sound' E cs R FULL model 15 0 HC ltac:(lia) H15) as [R15 _].
  rewrite <- bv5_17 in R17. rewrite <- bv5_10 in R10. rewrite <- bv5_12 in R12. rewrite <- bv5_13 in R13.
  rewrite <- bv5_14 in R14. rewrite <- bv5_15 in R15. rewrite (Z_to_bv64_m1 _ eq_refl) in R14.
  destruct (mmap_len_sound E cs R FULL model ne nlo nhi HC HML) as (R11 & Hlen & Hne & Hnlo & HnZ & HnZal & HneE).
  change (Z_to_bv 5 11) with (Z_to_bv 5 (Z.of_nat 11)) in R11. rewrite <- bv5_11 in R11.
  set (len := bv_unsigned (edenot E (reg cs 11))) in *. set (nZ := page_round_up_Z len) in *.
  set (n := Z_to_bv 64 nZ).
  destruct (gap_ok_sound E cs R FULL model nhi nZ HC Hgap ltac:(lia)) as [a0 Ha0]. rewrite <- R10 in Ha0.
  pose proof (co_halt _ _ _ _ _ _ _ _ _ _ _ HC) as Hhalt.
  pose proof (co_top _ _ _ _ _ _ _ _ _ _ _ HC) as HTOP. unfold TOP, CEIL, CEILMAX in HTOP.
  assert (Hbudget : eager = true -> a_eager cs + a_abytes cs + nhi <= LIMIT).
  { intros ->. cbn in Hbud. unfold budget_ok in Hbud. apply Z.leb_le in Hbud. exact Hbud. }

  assert (CONT : forall (a : word) model' FULL',
            grant_ok_na (getr R 10) model a nZ = true ->
            grant_post kd a n model model' -> grant_mem kd a n FULL FULL' -> m_fs model' = m_fs model ->
            srealizes SEGS (mkCfg (mkst (regupd R 10 a) (v_addi (Z_to_bv 64 (pc cs)) 4) FULL' (seg_rom SEGS)) model') TB).
  { intros a model' FULL' Hg GPo GM Hfs. rewrite R10 in Hg.
    destruct (mmap_null_cs1 cs kd eager ne nlo nhi E R FULL model a model' FULL' HC HML Hfresh Hnev Hbudget Hkind Hkfog Hnoh Hg GPo GM)
      as (HC1 & Hbase & HneE' & Un & Hag0 & NEW).
    fold len nZ n in HC1, HneE', Un, NEW.
    rewrite (v_addi_pc (pc cs) Hp0 Hp4). rewrite bv5_10.
    set (E' := ext1 E (nxt cs) (Z_to_bv 64 (bv_unsigned a / 4096))) in *.
    assert (Hpc : pc cs' = pc cs + 4).
    { destruct visible; [|injection Hn as <-; reflexivity].
      destruct (vis_add_inv _ _ _ _ _ Hn) as (nhi2 & _ & ->). reflexivity. }
    specialize (HK E' (regupd R (Z_to_bv 5 (Z.of_nat 10)) a) FULL' model' (conj Hag0 (ext1_agree'' E (nxt cs) (Z_to_bv 64 (bv_unsigned a / 4096))))).
    unfold cfg_of in HK. rewrite Hpc in HK. apply HK; [|exact Hfs].
    destruct visible.
    -
      assert (Hrw : kind_none kd = false) by (destruct kd; cbn in Hvisible |- *; congruence).
      pose proof (u64_range a) as Ra.
      destruct (grant_ok_na_unpack _ _ _ _ Hg) as (_ & _ & Htop & _).
      eapply (grant_vis_add E' (null_cs1 cs kd eager ne nlo nhi) cs' _ ne _ FULL' model' a n nZ HC1 Hn).
      + unfold null_cs1, BothNodesMmLib.null_cs1, add_entry. cbn [kn a_ss mk_ss s_know]. apply kimg_in_hull_app; [|apply kimg_clip_in_hull'].
        apply kimg_in_hull_pure. unfold BothNodesMmLib.null_kfacts.
        apply Forall_cons; [exact I|]. apply (proj2 (Forall_app _ _ _)); split; [apply null_kend_pure|].
        apply (proj2 (Forall_app _ _ _)); split; [apply kdisj_fixed_pure|].
        apply (proj2 (Forall_app _ _ _)); split; [apply kdisj_shadow_pure | apply kdisj_new_pure].
      + exact Hbase.
      + exact HneE'.
      + exact Un.
      + lia.
      + lia.
      + intros x Hx. destruct (NEW x Hx) as (N1 & N2 & N3 & _). rewrite (gp_noacc _ _ _ _ _ GPo), Hrw. auto.
      + intros x Hx. rewrite (proj2 GM x) by (rewrite Un; exact Hx). rewrite Hrw. reflexivity.
    - injection Hn as <-. exact HC1. }

  unfold cfg_of.
  destruct kd; cbn [kind_none kind_lazy negb orb] in *; [| | | | discriminate Hkfog | discriminate Hkfog].
  -
    destruct eager; [|discriminate].
    assert (Hbk : mmap_noreserve_backed_ok (Z_to_bv 64 34) model nZ = true).
    { unfold mmap_noreserve_backed_ok. rewrite mmap_noreserve_b_22.
      apply Z.leb_le. cbn in Hbud. eapply Z.le_trans; [|eapply (budget_slack E cs R FULL model nhi HC Hbud)]. fold nZ. lia. }
    eapply (srz_mmap_rw1 SEGS R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w len (Z_to_bv 64 34) TB Hf He Hhalt R17 R11 Hlen R12 R13 mmap_flags_core_22 R14 R15).
    + exists a0. split; [exact Ha0 | exact Hbk].
    + intros a Hg _. rewrite (with_mmap_backing_plain _ _ _ _ mmap_noreserve_b_22). apply (CONT a); [exact Hg | | | reflexivity].
      * constructor; reflexivity.
      * split; [intros x Hx; apply zfill_out; exact Hx | intros x Hx; apply zfill_in; exact Hx].
  -
    destruct eager; [discriminate|].
    assert (Hbk : mmap_noreserve_backed_ok (Z_to_bv 64 16418) model nZ = true).
    { unfold mmap_noreserve_backed_ok. rewrite mmap_noreserve_b_4022. reflexivity. }
    eapply (srz_mmap_rw1 SEGS R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w len (Z_to_bv 64 16418) TB Hf He Hhalt R17 R11 Hlen R12 R13 mmap_flags_core_4022 R14 R15).
    + exists a0. split; [exact Ha0 | exact Hbk].
    + intros a Hg _. rewrite (with_mmap_backing_lazy _ _ _ _ mmap_noreserve_b_4022). apply (CONT a); [exact Hg | | | reflexivity].
      * destruct (grant_ok_na_unpack _ _ _ _ Hg) as (Hal & Hpos & Htop & _). unfold page_size in Hal.
        constructor; try reflexivity.
        unfold vm_add_lazy. rewrite m_vm_lazy_with_vm_backing. rewrite lazy_interior_fresh; [reflexivity | exact Hal | | |]; subst n; rewrite u64_lit by lia; [exact HnZal | lia | lia].
      * split; [intros x Hx; apply zfill_out; exact Hx | intros x Hx; apply zfill_in; exact Hx].
  -
    destruct eager; [discriminate|].
    eapply (srz_mmap_none1 SEGS R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w len (Z_to_bv 64 34) TB Hf He Hhalt R17 R11 Hlen R12 R13 mmap_flags_core_22 R14 R15).
    + exists a0. exact Ha0.
    + intros a Hg. rewrite (with_mmap_backing_plain _ _ _ _ mmap_noreserve_b_22). apply (CONT a); [exact Hg | | | reflexivity].
      * constructor; reflexivity.
      * split; [intros x Hx; apply unfill_out; exact Hx | intros x Hx; apply unfill_in; exact Hx].
  -
    destruct eager; [discriminate|].
    eapply (srz_mmap_none1 SEGS R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w len (Z_to_bv 64 16418) TB Hf He Hhalt R17 R11 Hlen R12 R13 mmap_flags_core_4022 R14 R15).
    + exists a0. exact Ha0.
    + intros a Hg. rewrite (with_mmap_backing_lazy _ _ _ _ mmap_noreserve_b_4022). apply (CONT a); [exact Hg | | | reflexivity].
      * destruct (grant_ok_na_unpack _ _ _ _ Hg) as (Hal & Hpos & Htop & _). unfold page_size in Hal.
        constructor; try reflexivity.
        unfold vm_add_lazy. rewrite m_vm_lazy_with_vm_backing. rewrite lazy_interior_fresh; [reflexivity | exact Hal | | |]; subst n; rewrite u64_lit by lia; [exact HnZal | lia | lia].
      * split; [intros x Hx; apply unfill_out; exact Hx | intros x Hx; apply unfill_in; exact Hx].
Qed.

Lemma mmap_fixed_grant_sound1 : forall cs ms0 top b off ne nlo nhi kd (eager visible : bool) f13 cs' E R FULL model TB,
  CSOK E cs R FULL model -> is_ecall_at SEGS cs = true ->
  reg_lit cs 17 = Some 222 ->
  reg_lit cs 12 = Some (if kind_none kd then 0 else 3) ->
  reg_lit cs 13 = Some f13 ->
  (f13 = (if kind_lazy kd then 16434 else 50) \/ (f13 = 1064994 /\ kind_lazy kd = true)) ->
  reg_lit cs 14 = Some (two64 - 1) -> reg_lit cs 15 = Some 0 ->
  (kind_none kd || kind_lazy kd = negb eager)%bool -> is_tok_kind kd = false ->
  visible = eager ->
  fixed_args A cs top false = Some (b, off, ne, nlo, nhi) -> top <= CEIL ->
  (negb eager || budget_ok LIMIT cs nhi)%bool = true ->
  CSOK E (with_maps0 cs ms0) R FULL model ->
  region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) (edenot E (reg cs 10))
              (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (reg cs 11))))) = true ->
  (forall m, In m ms0 -> is_hole m = true ->
     bv_unsigned (edenot E (reg cs 10)) + page_round_up_Z (bv_unsigned (edenot E (reg cs 11))) <= uE E (am_base m)
     \/ uE E (am_base m) + uE E (am_len m) <= bv_unsigned (edenot E (reg cs 10))) ->
  mmap_fixed_grant A LIMIT cs ms0 b off ne nhi kd eager visible = Some cs' ->
  (forall E' R' FULL' model', env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> CSOK E' cs' R' FULL' model' -> m_fs model' = m_fs model ->
      srealizes SEGS (cfg R' (pc cs') FULL' model') TB) ->
  srealizes SEGS (cfg R (pc cs) FULL model) TB.
Proof.
  intros cs ms0 top b off ne nlo nhi kd eager visible f13 cs' E R FULL model TB HC Hec H17 H12 H13 Hf13 H14 H15 Hkind Hkfog Hvisible HFA Htop Hbud HC0 Hrf Hholes Hn HK.
  destruct (is_ecall_at_sound SEGS cs Hec) as (w & Hf & He & Hp0 & Hp4).
  assert (Hbudget : eager = true -> a_eager cs + a_abytes cs + nhi <= LIMIT).
  { intros ->. cbn in Hbud. unfold budget_ok in Hbud. apply Z.leb_le in Hbud. exact Hbud. }
  unfold mmap_fixed_grant in Hn. rewrite kn_grant_filterM_eq in Hn.

  destruct (reg_lit_sound' E cs R FULL model 17 222 HC ltac:(lia) H17) as [R17 _].
  destruct (reg_lit_sound' E cs R FULL model 12 _ HC ltac:(lia) H12) as [R12 _].
  destruct (reg_lit_sound' E cs R FULL model 13 _ HC ltac:(lia) H13) as [R13 _].
  destruct (reg_lit_sound' E cs R FULL model 14 _ HC ltac:(lia) H14) as [R14 _].
  destruct (reg_lit_sound' E cs R FULL model 15 0 HC ltac:(lia) H15) as [R15 _].
  rewrite <- bv5_17 in R17. rewrite <- bv5_12 in R12. rewrite <- bv5_13 in R13.
  rewrite <- bv5_14 in R14. rewrite <- bv5_15 in R15. rewrite (Z_to_bv64_m1 _ eq_refl) in R14.

  assert (Hfl : (mmap_flags_core (Z_to_bv 64 f13) = 50 \/ mmap_flags_core (Z_to_bv 64 f13) = 1048610)
                /\ mmap_noreserve_b (Z_to_bv 64 f13) = kind_lazy kd).
  { destruct Hf13 as [-> | [-> Hlz]].
    - destruct (kind_lazy kd); split; [left; apply mmap_flags_core_4032 | apply mmap_noreserve_b_4032 | left; apply mmap_flags_core_32 | apply mmap_noreserve_b_32].
    - rewrite Hlz. split; [right; apply mmap_flags_core_104022 | apply mmap_noreserve_b_104022]. }
  destruct Hfl as [Hcore Hnrb]. clear Hf13.
  destruct (fixed_args_sound E cs R FULL model top false b off ne nlo nhi HC HFA) as (Hsp & HML & _).
  destruct (mmap_len_sound E cs R FULL model ne nlo nhi HC HML) as (R11 & Hlen & _).
  change (Z_to_bv 5 11) with (Z_to_bv 5 (Z.of_nat 11)) in R11. rewrite <- bv5_11 in R11.
  set (len := bv_unsigned (edenot E (reg cs 11))) in *. set (nZ := page_round_up_Z len) in *.
  set (n := Z_to_bv 64 nZ) in *. set (addr := edenot E (reg cs 10)) in *.
  pose proof (co_halt _ _ _ _ _ _ _ _ _ _ _ HC) as Hhalt.
  pose proof (proj2 (proj2 (proj2 (co_wf _ _ _ _ _ _ _ _ _ _ _ HC)))) as Hisp.

  destruct (fixed_pre cs top b off ne nlo nhi E R FULL model HC HFA (Z.le_trans _ _ _ Htop CEIL_le_CEILMAX))
    as (HneE & Un & Hest & Hal & Hpos & Himg & HtopA & R10 & HnZal & HnZ).
  fold len nZ n addr in HneE, Un, Hest, Hal, Hpos, Himg, HtopA, R10, HnZal, HnZ.
  assert (HaK : bv_unsigned addr + nZ <= CEIL) by lia.
  rewrite <- bv5_10 in R10.
  assert (Hce : bv_unsigned addr + page_round_up_Z len <= alloc_ceiling) by (rewrite CEIL_eq; fold nZ; lia).

  assert (CONT : forall model' FULL',
            grant_post kd addr n model model' -> grant_mem kd addr n FULL FULL' -> m_fs model' = m_fs model ->
            srealizes SEGS (mkCfg (mkst (regupd R 10 addr) (v_addi (Z_to_bv 64 (pc cs)) 4) FULL' (seg_rom SEGS)) model') TB).
  { intros model' FULL' GPo GM Hfs.
    destruct (mmap_fixed_grant_cs1 cs ms0 kd eager top b off ne nlo nhi E R FULL model model' FULL' HC HFA Htop HC0 Hrf Hholes Hbudget Hkind Hkfog GPo GM) as (HC1 & NEW).
    fold len nZ n addr in HC1, NEW.
    rewrite (v_addi_pc (pc cs) Hp0 Hp4). rewrite bv5_10.
    assert (Hpc : pc cs' = pc cs + 4).
    { destruct visible; [|injection Hn as <-; reflexivity].
      destruct (vis_add_inv _ _ _ _ _ Hn) as (nhi2 & _ & ->). reflexivity. }
    specialize (HK E (regupd R (Z_to_bv 5 (Z.of_nat 10)) addr) FULL' model' (conj (env_agree_refl' _ _) (env_agree_refl' _ _))).
    unfold cfg_of in HK. rewrite Hpc in HK. apply HK; [|exact Hfs].
    destruct visible.
    -
      subst eager. assert (Hrw : kind_none kd = false) by (destruct kd; cbn in Hkind |- *; congruence).
      pose proof (u64_range addr) as Ra.
      eapply (vis_add_sound'); [exact Hn | exact HC1 |].
      destruct (vis_add_inv _ _ _ _ _ Hn) as (nhi2 & _ & Ecs2).
      apply Forall_app. split.
      +
        assert (Hfl : flat E (SA b off) (elenZ E ne)) by (unfold flat, elenZ; rewrite Hest, HneE, Un; unfold CEIL in HaK; lia).
        assert (BYTE : forall x : word, bv_unsigned addr <= bv_unsigned x < bv_unsigned addr + nZ ->
                  MR E cs' model' FULL' x = Some (Z_to_bv 8 0)).
        { intros x Hx. destruct (NEW x Hx) as (N1 & N2 & N3).
          unfold Mr, mrestrict, hid. rewrite N3. cbn [orb]. unfold vis. rewrite N1. rewrite (gp_noacc _ _ _ _ _ GPo), Hrw, N2. cbn [negb andb].
          assert (Hallow : in_allow A E cs' (bv_unsigned x) = true).
          { unfold in_allow, in_vis. rewrite Ecs2. cbn [a_vis existsb fst snd with_maps0]. unfold uE. fold addr. rewrite HneE, Un.
            rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity. }
          rewrite Hallow, !orb_true_r. cbn [negb]. rewrite (proj2 GM x) by (rewrite Un; exact Hx). rewrite Hrw. reflexivity. }
        constructor; [|constructor; [|constructor]]; cbn [kentry_ok]; split; try exact Hfl; unfold elenZ; rewrite Hest, HneE, Un.
        * intros d w' Hd Hdw. destruct w' as [|w'']; [reflexivity|].
          apply store_ok_of_all; [rewrite u64_lit by (unfold CEIL in HaK; lia); unfold CEIL in HaK; lia|].
          intros x Hx. rewrite u64_lit in Hx by (unfold CEIL in HaK; lia). unfold wview. rewrite (BYTE x) by lia. discriminate.
        * intros i Hi. apply BYTE. rewrite u64_lit by (unfold CEIL in HaK; lia). lia.
      +
        pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC1) as HK1. unfold Mr in HK1 |- *.
        eapply know_ok_unhide'; [apply H_off_segments_cs' | | | | exact HK1].
        * unfold fixed_cs1, BothNodesMmLib.fixed_cs1, add_entry. cbn [kn a_ss mk_ss s_know with_maps0]. apply kimg_in_hull_app; [|apply kimg_clip_in_hull'].
          destruct kd; cbn [mkind_eqb]; try (apply kimg_in_hull_pure; apply Forall_nil).
          apply kimg_in_hull_pure. apply Forall_flat_map. apply Forall_forall. intros p _. unfold shadow_facts.
          destruct (shadow_of A (kn cs) (fst p) (snd p)) as [[sb sk] sn].
          lazymatch goal with |- Forall _ (if ?c then _ else _) => destruct c end; [|apply Forall_nil].
          apply Forall_cons; [exact I|]. apply Forall_cons; [exact I|]. apply Forall_nil.
        * intros y Hy. rewrite Ecs2 in Hy. eapply hid_cons_sub. exact Hy.
        * intros y Hy. apply hid_hull'. exact Hy.
    - injection Hn as <-. exact HC1. }

  unfold cfg_of.
  destruct kd; cbn [kind_none kind_lazy negb orb] in *; [| | | | discriminate Hkfog | discriminate Hkfog].
  -
    destruct eager; [|discriminate].
    eapply (srz_mmap_fixed_rw_free1 SEGS R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w addr len (Z_to_bv 64 f13) TB
              Hf He Hhalt R17 R10 Hal Hpos R11 ltac:(lia) Hce Hisp R12 R13 Hcore R14 R15 Hrf).
    + unfold mmap_noreserve_backed_ok. rewrite Hnrb. apply Z.leb_le. cbn in Hbud.
      eapply Z.le_trans; [|eapply (budget_slack E cs R FULL model nhi HC Hbud)]. fold nZ. lia.
    + rewrite with_mmap_backing_plain by exact Hnrb.
      apply CONT; [constructor; reflexivity | | reflexivity].
      split; [intros x Hx; apply zfill_out; exact Hx | intros x Hx; apply zfill_in; exact Hx].
  -
    destruct eager; [discriminate|].
    eapply (srz_mmap_fixed_rw_free1 SEGS R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w addr len (Z_to_bv 64 f13) TB
              Hf He Hhalt R17 R10 Hal Hpos R11 ltac:(lia) Hce Hisp R12 R13 Hcore R14 R15 Hrf).
    + unfold mmap_noreserve_backed_ok. rewrite Hnrb. reflexivity.
    + rewrite with_mmap_backing_lazy by exact Hnrb.
      fold nZ. fold n. apply CONT; [| | reflexivity].
      * constructor; try reflexivity.
        unfold vm_add_lazy. rewrite m_vm_lazy_with_vm_backing.
        rewrite lazy_interior_fresh; [reflexivity | exact Hal | rewrite Un; exact HnZal | rewrite Un; lia | rewrite Un; unfold CEIL in HaK; lia].
      * split; [intros x Hx; apply zfill_out; exact Hx | intros x Hx; apply zfill_in; exact Hx].
  -
    destruct eager; [discriminate|].
    eapply (srz_mmap_fixed_none_free1 SEGS R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w addr len (Z_to_bv 64 f13) TB
              Hf He Hhalt R17 R10 Hal Hpos R11 ltac:(lia) Hce Hisp R12 R13 Hcore R14 R15 Hrf).
    rewrite with_mmap_backing_plain by exact Hnrb.
    apply CONT; [constructor; reflexivity | | reflexivity].
    split; [intros x Hx; apply unfill_out; exact Hx | intros x Hx; apply unfill_in; exact Hx].
  -
    destruct eager; [discriminate|].
    eapply (srz_mmap_fixed_none_free1 SEGS R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w addr len (Z_to_bv 64 f13) TB
              Hf He Hhalt R17 R10 Hal Hpos R11 ltac:(lia) Hce Hisp R12 R13 Hcore R14 R15 Hrf).
    rewrite with_mmap_backing_lazy by exact Hnrb.
    fold nZ. fold n. apply CONT; [| | reflexivity].
    * constructor; try reflexivity.
      unfold vm_add_lazy. rewrite m_vm_lazy_with_vm_backing.
      rewrite lazy_interior_fresh; [reflexivity | exact Hal | rewrite Un; exact HnZal | rewrite Un; lia | rewrite Un; unfold CEIL in HaK; lia].
    * split; [intros x Hx; apply unfill_out; exact Hx | intros x Hx; apply unfill_in; exact Hx].
Qed.

Lemma mmap_fixed_free_sound1 : forall cs kd (eager visible : bool) f13 cs' E R FULL model TB,
  CSOK E cs R FULL model -> is_ecall_at SEGS cs = true ->
  reg_lit cs 17 = Some 222 ->
  reg_lit cs 12 = Some (if kind_none kd then 0 else 3) ->
  reg_lit cs 13 = Some f13 ->
  (f13 = (if kind_lazy kd then 16434 else 50) \/ (f13 = 1064994 /\ kind_lazy kd = true)) ->
  reg_lit cs 14 = Some (two64 - 1) -> reg_lit cs 15 = Some 0 ->
  (kind_none kd || kind_lazy kd = negb eager)%bool -> is_tok_kind kd = false ->
  visible = eager ->
  mmap_fixed_free A LIMIT cs kd eager visible = Some cs' ->
  (forall E' R' FULL' model', env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> CSOK E' cs' R' FULL' model' -> m_fs model' = m_fs model ->
      srealizes SEGS (cfg R' (pc cs') FULL' model') TB) ->
  srealizes SEGS (cfg R (pc cs) FULL model) TB.
Proof.
  intros cs kd eager visible f13 cs' E R FULL model TB HC Hec H17 H12 H13 Hf13 H14 H15 Hkind Hkfog Hvisible Hn HK.
  unfold mmap_fixed_free in Hn.
  destruct (fixed_args A cs KHI false) as [[[[[b off] ne] nlo] nhi]|] eqn:HFA.
  -
    match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
    apply andb_prop in Hcond as [Hcond Hav]. apply andb_prop in Hcond as [Hcond Hnev].
    apply andb_prop in Hcond as [Hcond Hbud]. apply andb_prop in Hcond as [Hnf Hall].
    destruct (mmap_fixed_old_facts cs b off ne nlo nhi E R FULL model HC HFA Hnf Hall) as (HC0 & Hrf & Hholes).
    eapply (mmap_fixed_grant_sound1 cs (a_maps cs) KHI b off ne nlo nhi kd eager visible f13 cs' E R FULL model TB
              HC Hec H17 H12 H13 Hf13 H14 H15 Hkind Hkfog Hvisible HFA ltac:(unfold KHI, CEIL; lia) Hbud
              HC0 Hrf Hholes Hn HK).
  -
    destruct (fixed_args A cs CEIL false) as [[[[[b off] ne] nlo] nhi]|] eqn:HFA2; [|discriminate].
    destruct (find_hole (kn cs) (a_maps cs) (reg cs 10) ne) as [h|] eqn:Hfh; [|discriminate].
    match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
    apply andb_prop in Hcond as [Hcond Hav]. apply andb_prop in Hcond as [Hcond Hnev].
    apply andb_prop in Hcond as [Hap Hbud].
    destruct (mmap_fixed_hole_facts cs b off ne nlo nhi h E R FULL model HC HFA2 Hfh Hap) as (HC0 & Hrf & Hholes).
    eapply (mmap_fixed_grant_sound1 cs (unhole (a_maps cs) h) CEIL b off ne nlo nhi kd eager visible f13 cs' E R FULL model TB
              HC Hec H17 H12 H13 Hf13 H14 H15 Hkind Hkfog Hvisible HFA2 ltac:(lia) Hbud
              HC0 Hrf Hholes Hn HK).
Qed.

Lemma node_mprotect_sound1 : forall cs cs' E R FULL model TB,
  CSOK E cs R FULL model -> is_ecall_at SEGS cs = true ->
  node_mprotect A LIMIT cs = Some cs' ->
  (forall E' R' FULL' model', env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> CSOK E' cs' R' FULL' model' -> m_fs model' = m_fs model ->
      srealizes SEGS (cfg R' (pc cs') FULL' model') TB) ->
  srealizes SEGS (cfg R (pc cs) FULL model) TB.
Proof.
  intros cs cs' E R FULL model TB HC Hec Hn HK.
  destruct (is_ecall_at_sound SEGS cs Hec) as (w & Hf & He & Hp0 & Hp4).
  rewrite node_mprotect_eq in Hn.   unfold node_mprotect_ref in Hn.
  destruct (reg_lit cs 17) as [z17|] eqn:H17; [|discriminate].
  destruct (reg_lit cs 12) as [z12|] eqn:H12.
  2: { repeat match type of Hn with context [match ?x with _ => _ end] => destruct x; try discriminate end. }
  destruct (fixed_args A cs CEILMAX true) as [[[[[b off] ne] nlo] nhi]|] eqn:HFA.
  2: { repeat match type of Hn with context [match ?x with _ => _ end] => destruct x; try discriminate end. }
  assert (Hz : z17 = 226 /\ z12 = 3).
  { repeat match type of Hn with context [match ?x with _ => _ end] => destruct x; try discriminate end; auto. }
  destruct Hz as [-> ->].
  destruct (find_containing (kn cs) (a_maps cs) [KNONE; KNONELAZY] b off ne) as [m|] eqn:Hfind; [|discriminate].
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
  apply andb_prop in Hcond as [Hcond _]. apply andb_prop in Hcond as [Hbud _].
  unfold budget_ok in Hbud. apply Z.leb_le in Hbud.
  destruct (reg_lit_sound' E cs R FULL model 17 226 HC ltac:(lia) H17) as [R17 _].
  destruct (reg_lit_sound' E cs R FULL model 12 3 HC ltac:(lia) H12) as [R12 _].
  rewrite <- bv5_17 in R17. rewrite <- bv5_12 in R12.
  destruct (slice_args E cs R FULL model b off ne nlo nhi _ m HC HFA Hfind)
    as (Hm & [Hkind Hnf] & R10 & R11 & Hlen & Hne & Un & HnZpos & HnZ & HnZal & Hal & Hpos & Himg & HaC & Hest & Hin1 & Hin2 & HmC & Hmc & Hrfres & Hov).
  rewrite <- bv5_10 in R10. rewrite <- bv5_11 in R11.
  set (len := bv_unsigned (edenot E (reg cs 11))) in *. set (nZ := page_round_up_Z len) in *.
  set (n := Z_to_bv 64 nZ) in *. set (addr := edenot E (reg cs 10)) in *.
  pose proof (co_halt _ _ _ _ _ _ _ _ _ _ _ HC) as Hhalt. pose proof (co_wf _ _ _ _ _ _ _ _ _ _ _ HC) as Hwf.
  pose proof (u64_range addr) as Ra.
  assert (Hkind' : am_kind m = KNONE \/ am_kind m = KNONELAZY) by (cbn in Hkind; destruct Hkind as [<-|[<-|[]]]; auto).

  assert (Hna : map_contains (vm_noaccess (m_vmmaps model)) addr n = true).
  { pose proof (proj1 (Forall_forall _ _) (co_none _ _ _ _ _ _ _ _ _ _ _ HC) m Hm Hkind') as X.
    eapply map_contains_intro; [exact X | exact Hin1 | rewrite Un; exact Hin2]. }
  unfold cfg_of.
  eapply (srz_mprotect1 SEGS R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w addr len TB Hf He Hhalt R17 R10 Hal R11 ltac:(lia)).
  - unfold two_pow_64. fold nZ. unfold CEILMAX in HaC. lia.
  - exact R12.
  - exact Hna.
  - exact Hmc.
  - apply mprotect_budget_ok_intro_gen; [exact Hwf|]. pose proof (budget_slack E cs R FULL model nhi HC ltac:(unfold budget_ok; apply Z.leb_le; exact Hbud)). fold nZ n. lia.
  - fold nZ. fold n.
    set (model' := mprotect_model addr n model). set (FULL' := zfill addr n FULL).
    assert (SPo : slice_post SlM addr n model model') by (constructor; reflexivity).
    assert (SM : slice_mem SlM addr n FULL FULL').
    { split; [intros x Hx; apply zfill_out; exact Hx | intros x Hx; apply zfill_in; exact Hx]. }
    assert (SH : slice_hyps E cs R FULL model SlM m addr n nZ model' FULL').
    { constructor; try assumption; intros HH; [discriminate HH|]. intros Hk. rewrite Hk in Hkind'. destruct Hkind'; discriminate. }
    rewrite (v_addi_pc (pc cs) Hp0 Hp4).
    destruct (vis_add_inv _ _ _ _ _ Hn) as (nhi2 & _ & Ecs').
    assert (Hpc : pc cs' = pc cs + 4) by (rewrite Ecs'; reflexivity).
    specialize (HK E (regupd R (Z_to_bv 5 (Z.of_nat 10)) (Z_to_bv 64 0)) FULL' model' (conj (env_agree_refl' _ _) (env_agree_refl' _ _))).
    unfold cfg_of in HK. rewrite Hpc, <- bv5_10 in HK. apply HK; [|reflexivity]. clear HK.
    assert (Hregs' : regs_ok E (sr_upd (s_regs (a_ss cs)) 10 (ELit 0)) (regupd R (Z_to_bv 5 (Z.of_nat 10)) (Z_to_bv 64 0))).
    { apply regs_ok_set_n'; [exact (co_regs _ _ _ _ _ _ _ _ _ _ _ HC) | lia | reflexivity]. }
    assert (MROUT := fun x => sl_MR_out E cs R FULL model SlM m addr n nZ model' FULL' SH cs x eq_refl).
    assert (MROUT' : forall x : word, bv_unsigned x < estart E (SA b off) \/ estart E (SA b off) + elenZ E ne <= bv_unsigned x ->
                      MR E cs model' FULL' x = MR E cs model FULL x).
    { intros x Hx. apply MROUT. rewrite Hest in Hx. unfold elenZ in Hx. rewrite Hne, Un in Hx. exact Hx. }
    assert (Hk' : know_ok SEGS E (MR E cs model' FULL') (kimg_clip A (kn_unfill (kn cs) b off ne))).
    { eapply kn_unfill_clip_ok; [exact (co_know _ _ _ _ _ _ _ _ _ _ _ HC) | rewrite Hest; unfold elenZ; rewrite Hne, Un; exact Himg | exact MROUT']. }
    pose proof (slice_cs1_ok E cs R FULL model SlM m addr n nZ model' FULL' SH _ _ _ (pc cs + 4) (s_next (a_ss cs)) nhi (reg cs 10) ne Hregs' Hk' HnZ ltac:(intros _; exact Hbud) eq_refl Hne) as HC1.
    cbn [sl_charge slice_vmop] in HC1.
    eapply (vis_add_slice_ok E _ cs' (reg cs 10) b off ne _ FULL' model' (bv_unsigned addr) nZ HC1).
    + exact Hn.
    + cbn [kn a_ss s_know mk_ss]. apply kimg_clip_in_hull'.
    + reflexivity.
    + exact Hest.
    + unfold elenZ. rewrite Hne. exact Un.
    + lia.
    + lia.
    + lia.
    + intros x Hx. rewrite (sp_maps _ _ _ _ _ SPo).
      split; [exact (sl_in_maps E cs R FULL model SlM m addr n nZ model' FULL' SH x Hx) |].
      split; [exact (sl_noacc_in E cs R FULL model SlM m addr n nZ model' FULL' SH x Hx) |].
      split; [destruct (argH E x) eqn:Ea; [pose proof (argH_sp0 _ _ Ea); pose proof (co_sp0 _ _ _ _ _ _ _ _ _ _ _ HC); unfold TOP in *; lia | reflexivity]|].
      rewrite (proj2 SM x) by (rewrite Un; exact Hx). reflexivity.
Qed.

Lemma mmap_gate_sound : forall cs prot flags isnull,
  mmap_gate cs = Some (prot, flags, isnull) ->
  reg_lit cs 17 = Some 222 /\ reg_lit cs 12 = Some prot /\ reg_lit cs 13 = Some flags
  /\ reg_lit cs 14 = Some (two64 - 1) /\ reg_lit cs 15 = Some 0
  /\ (isnull = true -> reg_lit cs 10 = Some 0).
Proof.
  intros cs prot flags isnull Hg. unfold mmap_gate in Hg.
  destruct (reg_lit cs 17) as [z17|] eqn:H17; [|discriminate].
  destruct (reg_lit cs 12) as [p|] eqn:H12.
  2: { repeat match type of Hg with context [match ?x with _ => _ end] => destruct x; try discriminate end. }
  destruct (reg_lit cs 13) as [f|] eqn:H13.
  2: { repeat match type of Hg with context [match ?x with _ => _ end] => destruct x; try discriminate end. }
  destruct (reg_lit cs 14) as [m1|] eqn:H14.
  2: { repeat match type of Hg with context [match ?x with _ => _ end] => destruct x; try discriminate end. }
  destruct (reg_lit cs 15) as [z15|] eqn:H15.
  2: { repeat match type of Hg with context [match ?x with _ => _ end] => destruct x; try discriminate end. }
  assert (Hz : z17 = 222 /\ z15 = 0).
  { repeat match type of Hg with context [match ?x with _ => _ end] => destruct x; try discriminate end; auto. }
  destruct Hz as [-> ->]. cbn iota in Hg.
  match type of Hg with (if negb ?c then None else _) = _ => destruct c eqn:Hm1; [|discriminate] end. cbn [negb] in Hg.
  apply Z.eqb_eq in Hm1. subst m1. injection Hg as <- <- <-.
  repeat split; try reflexivity.
  destruct (reg_lit cs 10) as [[|p10|p10]|]; intros H; try discriminate H. reflexivity.
Qed.

Theorem node_mmap1_sound : node1_stmt SEGS A nx0 LIMIT SINV argH FS0 (is_ecall_at SEGS) (APS.node_mmap1 A nx0 LIMIT).
Proof.
  intros cs csb E R FULL model TB HC Hec Hn HKB.
  unfold APS.node_mmap1, node_mmap2 in Hn.
  destruct (mmap_gate cs) as [[[prot flags] isnull]|] eqn:Hg; [|discriminate].
  destruct (mmap_gate_sound cs prot flags isnull Hg) as (H17 & H12 & H13 & H14 & H15 & H10).
  match type of Hn with (match match ?g with Some csG => _ | None => None end with _ => _ end) = _ => destruct g as [csG|] eqn:HG; [|discriminate] end.
  injection Hn as <-.
  destruct isnull.
  - specialize (H10 eq_refl).
    assert (ARMS : (prot = 3 /\ flags = 34 /\ mmap_null A nx0 LIMIT cs KRW true true = Some csG)
                   \/ (prot = 3 /\ flags = 16418 /\ mmap_null A nx0 LIMIT cs KRWLAZY false true = Some csG)
                   \/ (prot = 0 /\ flags = 34 /\ mmap_null A nx0 LIMIT cs KNONE false false = Some csG)
                   \/ (prot = 0 /\ flags = 16418 /\ mmap_null A nx0 LIMIT cs KNONELAZY false false = Some csG)).
    { repeat match type of HG with context [match ?x with _ => _ end] => destruct x; try discriminate end; tauto. }
    destruct ARMS as [(-> & -> & Hm)|[(-> & -> & Hm)|[(-> & -> & Hm)|(-> & -> & Hm)]]].
    + eapply (mmap_null_sound1 cs KRW true true); eauto; reflexivity.
    + eapply (mmap_null_sound1 cs KRWLAZY false true); eauto; reflexivity.
    + eapply (mmap_null_sound1 cs KNONE false false); eauto; reflexivity.
    + eapply (mmap_null_sound1 cs KNONELAZY false false); eauto; reflexivity.
  -
    assert (ARMS : (prot = 3 /\ flags = 16434 /\ mmap_fixed_free A LIMIT cs KRWLAZY false false = Some csG)
                   \/ (prot = 3 /\ flags = 50 /\ mmap_fixed_free A LIMIT cs KRW true true = Some csG)
                   \/ (prot = 0 /\ flags = 16434 /\ mmap_fixed_free A LIMIT cs KNONELAZY false false = Some csG)
                   \/ (prot = 0 /\ flags = 50 /\ mmap_fixed_free A LIMIT cs KNONE false false = Some csG)
                   \/ (prot = 3 /\ flags = 1064994 /\ mmap_fixed_free A LIMIT cs KRWLAZY false false = Some csG)
                   \/ (prot = 0 /\ flags = 1064994 /\ mmap_fixed_free A LIMIT cs KNONELAZY false false = Some csG)).
    { repeat match type of HG with context [match ?x with _ => _ end] => destruct x; try discriminate end; tauto. }
    destruct ARMS as [(-> & -> & Hm)|[(-> & -> & Hm)|[(-> & -> & Hm)|[(-> & -> & Hm)|[(-> & -> & Hm)|(-> & -> & Hm)]]]]].
    + eapply (mmap_fixed_free_sound1 cs KRWLAZY false false 16434); eauto; first [left; reflexivity | reflexivity].
    + eapply (mmap_fixed_free_sound1 cs KRW true true 50); eauto; first [left; reflexivity | reflexivity].
    + eapply (mmap_fixed_free_sound1 cs KNONELAZY false false 16434); eauto; first [left; reflexivity | reflexivity].
    + eapply (mmap_fixed_free_sound1 cs KNONE false false 50); eauto; first [left; reflexivity | reflexivity].
    + eapply (mmap_fixed_free_sound1 cs KRWLAZY false false 1064994); eauto; first [right; split; reflexivity | reflexivity].
    + eapply (mmap_fixed_free_sound1 cs KNONELAZY false false 1064994); eauto; first [right; split; reflexivity | reflexivity].
Qed.

Theorem node_mprotect1_sound : node1_stmt SEGS A nx0 LIMIT SINV argH FS0 (is_ecall_at SEGS) (node_mprotect A LIMIT).
Proof.
  intros cs csb E R FULL model TB HC Hec Hn HKB.
  eapply node_mprotect_sound1; eauto.
Qed.

Definition slarm_of (arm : fixed_in_arm) : slarm := match arm with ArmE => SlE | ArmF => SlF | ArmG => SlG end.

Lemma mmap_fixed_in_sound1 : forall cs arm b off ne nlo nhi m csO E R FULL model TB,
  CSOK E cs R FULL model -> is_ecall_at SEGS cs = true ->
  reg_lit cs 17 = Some 222 ->
  reg_lit cs 12 = Some (match arm with ArmG => 0 | _ => 3 end) ->
  reg_lit cs 13 = Some (match arm with ArmF => 16434 | _ => 50 end) ->
  reg_lit cs 14 = Some (two64 - 1) -> reg_lit cs 15 = Some 0 ->
  fixed_in_args A cs arm = Some (b, off, ne, nlo, nhi, m) ->
  mmap_fixed_in A LIMIT cs arm = Some csO ->
  (forall E' R' FULL' model', env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> CSOK E' csO R' FULL' model' -> m_fs model' = m_fs model ->
      srealizes SEGS (cfg R' (pc csO) FULL' model') TB) ->
  srealizes SEGS (cfg R (pc cs) FULL model) TB.
Proof.
  intros cs arm b off ne nlo nhi m csO E R FULL model TB HC Hec H17 H12 H13 H14 H15 HFI Hn HKB.
  destruct (is_ecall_at_sound SEGS cs Hec) as (w & Hf & He & Hp0 & Hp4).

  rewrite fixed_in_args_eq in HFI.   unfold fixed_in_args_ref in HFI.
  destruct (fixed_args A cs CEILMAX true) as [[[[[b0 off0] ne0] nlo0] nhi0]|] eqn:HFA; [|discriminate].
  destruct (find_containing (kn cs) (a_maps cs) _ b0 off0 ne0) as [m0|] eqn:Hfind; [|discriminate].
  match type of HFI with (if ?c then _ else _) = _ => destruct c eqn:Hvars; [|discriminate] end.
  injection HFI as -> -> -> -> -> ->.
  rewrite mmap_fixed_in_eq in Hn.   unfold mmap_fixed_in_ref in Hn. rewrite fixed_in_args_eq in Hn. unfold fixed_in_args_ref in Hn. rewrite HFA, Hfind, Hvars in Hn.
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hbud; [|discriminate] end.
  destruct (reg_lit_sound' E cs R FULL model 17 222 HC ltac:(lia) H17) as [R17 _].
  destruct (reg_lit_sound' E cs R FULL model 12 _ HC ltac:(lia) H12) as [R12 _].
  destruct (reg_lit_sound' E cs R FULL model 13 _ HC ltac:(lia) H13) as [R13 _].
  destruct (reg_lit_sound' E cs R FULL model 14 _ HC ltac:(lia) H14) as [R14 _].
  destruct (reg_lit_sound' E cs R FULL model 15 0 HC ltac:(lia) H15) as [R15 _].
  rewrite <- bv5_17 in R17. rewrite <- bv5_12 in R12. rewrite <- bv5_13 in R13.
  rewrite <- bv5_14 in R14. rewrite <- bv5_15 in R15. rewrite (Z_to_bv64_m1 _ eq_refl) in R14.
  destruct (slice_args E cs R FULL model b off ne nlo nhi _ m HC HFA Hfind)
    as (Hm & [Hkind Hnf] & R10 & R11 & Hlen & Hne & Un & HnZpos & HnZ & HnZal & Hal & Hpos & Himg & HaC & Hest & Hin1 & Hin2 & HmC & Hmc & Hrfres & Hov).
  rewrite <- bv5_10 in R10. rewrite <- bv5_11 in R11.
  set (len := bv_unsigned (edenot E (reg cs 11))) in *. set (nZ := page_round_up_Z len) in *.
  set (n := Z_to_bv 64 nZ) in *. set (addr := edenot E (reg cs 10)) in *.
  pose proof (co_halt _ _ _ _ _ _ _ _ _ _ _ HC) as Hhalt. pose proof (co_wf _ _ _ _ _ _ _ _ _ _ _ HC) as Hwf.
  pose proof (proj2 (proj2 (proj2 Hwf))) as Hisp.
  pose proof (u64_range addr) as Ra.
  assert (Hce : bv_unsigned addr + page_round_up_Z len <= alloc_top (m_vmmaps model)) by (fold nZ; unfold TOP in HmC; lia).
  assert (HF : slarm_of arm = SlF -> am_kind m = KRWLAZY).
  { intros Hs. destruct arm; try discriminate. cbn in Hkind. destruct Hkind as [<-|[]]. reflexivity. }
  assert (HnF : slarm_of arm <> SlF -> am_kind m <> KRWLAZY).
  { intros Hs Hk. destruct arm; [|exact (Hs eq_refl)|]; cbn in Hkind; rewrite Hk in Hkind; destruct Hkind as [|[|[|[]]]]; discriminate. }
  set (prot := match arm with ArmG => 0 | _ => 3 end) in *.
  set (flg := match arm with ArmF => 16434 | _ => 50 end) in *.
  assert (Hprot : prot = 0 \/ prot = 3) by (destruct arm; cbn; lia).
  assert (Hcore : mmap_flags_core (Z_to_bv 64 flg) = 50) by (destruct arm; [apply mmap_flags_core_32 | apply mmap_flags_core_4032 | apply mmap_flags_core_32]).

  assert (CONTB : forall model' FULL',
            slice_post (slarm_of arm) addr n model model' -> slice_mem (slarm_of arm) addr n FULL FULL' -> m_fs model' = m_fs model ->
            srealizes SEGS (mkCfg (mkst (regupd R 10 addr) (v_addi (Z_to_bv 64 (pc cs)) 4) FULL' (seg_rom SEGS)) model') TB).
  { intros model' FULL' SPo SM Hfs.
    assert (SH : slice_hyps E cs R FULL model (slarm_of arm) m addr n nZ model' FULL') by (constructor; assumption).
    rewrite (v_addi_pc (pc cs) Hp0 Hp4). rewrite bv5_10.
    assert (Hpc : pc csO = pc cs + 4).
    { destruct arm; try (injection Hn as <-; reflexivity). destruct (vis_add_inv _ _ _ _ _ Hn) as (nhi2 & _ & ->). reflexivity. }
    specialize (HKB E (regupd R (Z_to_bv 5 (Z.of_nat 10)) addr) FULL' model' (conj (env_agree_refl' _ _) (env_agree_refl' _ _))).
    unfold cfg_of in HKB. rewrite Hpc in HKB. apply HKB; [|exact Hfs]. clear HKB.
    assert (Hregs' : regs_ok E (s_regs (a_ss cs)) (regupd R (Z_to_bv 5 (Z.of_nat 10)) addr)).
    { apply regs_ok_regupd_same; [exact (co_regs _ _ _ _ _ _ _ _ _ _ _ HC) | lia | rewrite <- bv5_10; exact R10]. }
    assert (MROUT := fun x => sl_MR_out E cs R FULL model (slarm_of arm) m addr n nZ model' FULL' SH cs x eq_refl).
    assert (MROUT' : forall x : word, bv_unsigned x < estart E (SA b off) \/ estart E (SA b off) + elenZ E ne <= bv_unsigned x ->
                      MR E cs model' FULL' x = MR E cs model FULL x).
    { intros x Hx. apply MROUT. rewrite Hest in Hx. unfold elenZ in Hx. rewrite Hne, Un in Hx. exact Hx. }
    pose proof (slice_cs1_ok E cs R FULL model (slarm_of arm) m addr n nZ model' FULL' SH (s_regs (a_ss cs)) (regupd R (Z_to_bv 5 (Z.of_nat 10)) addr)) as CS1.
    destruct arm; cbn [slarm_of sl_charge slice_vmop] in *.
    -
      assert (Hk' : know_ok SEGS E (MR E cs model' FULL') (kimg_clip A (kn_unfill (kn cs) b off ne))).
      { eapply kn_unfill_clip_ok; [exact (co_know _ _ _ _ _ _ _ _ _ _ _ HC) | rewrite Hest; unfold elenZ; rewrite Hne, Un; exact Himg | exact MROUT']. }
      unfold budget_ok in Hbud. apply Z.leb_le in Hbud.
      pose proof (CS1 _ (pc cs + 4) (s_next (a_ss cs)) nhi (reg cs 10) ne Hregs' Hk' HnZ ltac:(intros _; exact Hbud) eq_refl Hne) as HC1.
      eapply (vis_add_slice_ok E _ csO (reg cs 10) b off ne _ FULL' model' (bv_unsigned addr) nZ HC1).
      + exact Hn.
      + cbn [kn a_ss s_know mk_ss]. apply kimg_clip_in_hull'.
      + reflexivity.
      + exact Hest.
      + unfold elenZ. rewrite Hne. exact Un.
      + lia.
      + lia.
      + lia.
      + intros x Hx. rewrite (sp_maps _ _ _ _ _ SPo).
        split; [exact (sl_in_maps E cs R FULL model SlE m addr n nZ model' FULL' SH x Hx) |].
        split; [exact (sl_noacc_in E cs R FULL model SlE m addr n nZ model' FULL' SH x Hx) |].
        split; [destruct (argH E x) eqn:Ea; [pose proof (argH_sp0 _ _ Ea); pose proof (co_sp0 _ _ _ _ _ _ _ _ _ _ _ HC); unfold TOP in *; lia | reflexivity]|].
        rewrite (proj2 SM x) by (rewrite Un; exact Hx). reflexivity.
    -
      assert (Hk' : know_ok SEGS E (MR E cs model' FULL') (kimg_clip A (kn_rezero (kn cs) b off ne))).
      { eapply kn_rezero_clip_ok; [exact (co_know _ _ _ _ _ _ _ _ _ _ _ HC) | rewrite Hest; unfold elenZ; rewrite Hne, Un; exact Himg | exact MROUT' |].
        intros x Hx Hdef. rewrite Hest in Hx. unfold elenZ in Hx. rewrite Hne, Un in Hx.
        unfold Mr, mrestrict, hid in Hdef |- *.
        rewrite (sl_vis_in_F E cs R FULL model SlF m addr n nZ model' FULL' SH eq_refl cs x eq_refl Hx).
        destruct (argH E x); [exfalso; apply Hdef; reflexivity|]. cbn [orb] in *.
        destruct (VIS E cs model x); [|exfalso; apply Hdef; reflexivity]. cbn [negb].
        rewrite (proj2 SM x) by (rewrite Un; exact Hx). reflexivity. }
      injection Hn as <-. exact (CS1 _ (pc cs + 4) (s_next (a_ss cs)) nhi (reg cs 10) ne Hregs' Hk' HnZ ltac:(intros HH; discriminate HH) eq_refl Hne).
    -
      assert (Hk' : know_ok SEGS E (MR E cs model' FULL') (kimg_clip A (kn_cutout (kn cs) b off ne))).
      { apply know_ok_filter. eapply (APS.know_ok_cutout SEGS); [exact (co_know _ _ _ _ _ _ _ _ _ _ _ HC) | exact MROUT']. }
      injection Hn as <-. exact (CS1 _ (pc cs + 4) (s_next (a_ss cs)) nhi (reg cs 10) ne Hregs' Hk' HnZ ltac:(intros HH; discriminate HH) eq_refl Hne). }

  unfold cfg_of.
  assert (R12' : getr R 12 = Z_to_bv 64 prot) by (destruct arm; exact R12).
  assert (R13' : getr R 13 = Z_to_bv 64 flg) by (destruct arm; exact R13).
  eapply (srz_mmap_fixedin_lazy SEGS R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w prot (Z_to_bv 64 flg) addr len TB
            Hf He Hhalt R17 Hprot Hcore R10 Hal Hpos R11 ltac:(lia) Hce R12' R13' R14 R15 Hrfres Hmc).
  -   intros Hp3. fold nZ n. destruct arm; cbn in Hp3; try discriminate Hp3; subst flg.
    + apply mmap_fixed_rw_budget_ok_commit_intro; [apply mmap_noreserve_b_32 | exact Hwf |].
      unfold budget_ok in Hbud. pose proof (budget_slack E cs R FULL model nhi HC Hbud). lia.
    + apply mmap_fixed_rw_budget_ok_recommit_intro; [apply mmap_noreserve_b_4032 | exact Hwf | exact Hal | unfold page_size; rewrite Un; exact HnZal | rewrite Un; lia | rewrite Un; unfold CEIL, CEILMAX in *; lia |].
      eapply vm_backing_used_limit; [exact (co_minv _ _ _ _ _ _ _ _ _ _ _ HC) | apply A_wf_allowA'].
  - fold nZ. fold n. destruct arm; subst prot flg; cbn [Z.eqb slarm_of] in CONTB |- *.
    +   unfold fixedin_ok_model, with_mmap_replacement. rewrite with_mmap_backing_plain by apply mmap_noreserve_b_32.
      apply CONTB; [| | reflexivity].
      * constructor; reflexivity.
      * split; [intros x Hx; apply zfill_out; exact Hx | intros x Hx; apply zfill_in; exact Hx].
    +   unfold fixedin_ok_model, with_mmap_replacement. rewrite with_mmap_backing_lazy by apply mmap_noreserve_b_4032.
      apply CONTB; [| | reflexivity].
      * constructor; try reflexivity.
        unfold vm_add_lazy. rewrite m_vm_lazy_with_vm_backing, m_vm_lazy_vm_forget_range.
        rewrite lazy_interior_fresh; [reflexivity | exact Hal | rewrite Un; exact HnZal | rewrite Un; lia | rewrite Un; unfold CEIL, CEILMAX in *; lia].
      * split; [intros x Hx; apply zfill_out; exact Hx | intros x Hx; apply zfill_in; exact Hx].
    +   unfold fixedin_ok_model, with_mmap_replacement. rewrite with_mmap_backing_plain by apply mmap_noreserve_b_32.
      apply CONTB; [| | reflexivity].
      * constructor; reflexivity.
      * split; [intros x Hx; apply unfill_out; exact Hx | intros x Hx; apply unfill_in; exact Hx].
Qed.

Theorem node_mmapin1_sound : node1_stmt SEGS A nx0 LIMIT SINV argH FS0 (is_ecall_at SEGS) (node_mmapin1 A LIMIT).
Proof.
  intros cs csb E R FULL model TB HC Hec Hn HKB.
  unfold node_mmapin1 in Hn.
  destruct (mmap_gate cs) as [[[prot flags] isnull]|] eqn:Hg; [|discriminate].
  destruct (mmap_gate_sound cs prot flags isnull Hg) as (H17 & H12 & H13 & H14 & H15 & _).
  destruct isnull; [discriminate|]. cbv zeta in Hn.
  assert (CASES : forall arm,
     reg_lit cs 12 = Some (match arm with ArmG => 0 | _ => 3 end) ->
     reg_lit cs 13 = Some (match arm with ArmF => 16434 | _ => 50 end) ->
     mmap_fixed_in A LIMIT cs arm = Some csb ->
     srealizes SEGS (cfg R (pc cs) FULL model) TB).
  { intros arm H12' H13' Hn'.
    pose proof Hn' as Hn''. rewrite mmap_fixed_in_eq in Hn''. unfold mmap_fixed_in_ref in Hn''.
    destruct (fixed_in_args A cs arm) as [[[[[[b off] ne] nlo] nhi] m]|] eqn:HFI; [|discriminate].
    eapply (mmap_fixed_in_sound1 cs arm b off ne nlo nhi m csb); eauto. }
  destruct prot as [|p|p]; try discriminate Hn; try (repeat (destruct p as [p|p|]; try discriminate Hn));
  destruct flags as [|q|q]; try discriminate Hn; try (repeat (destruct q as [q|q|]; try discriminate Hn));
  refine (CASES _ _ _ Hn); first [exact H12 | exact H13].
Qed.

Lemma opt_all_In : forall (T U : Type) (f : T -> option U) (l : list T) (ys : list U) (x : T),
  opt_all (map f l) = Some ys -> In x l -> exists y, f x = Some y /\ In y ys.
Proof.
  intros T U f l. induction l as [|a l IH]; intros ys x H Hin; [destruct Hin|].
  cbn [map opt_all] in H. destruct (f a) as [ya|] eqn:Hfa; [|discriminate].
  destruct (opt_all (map f l)) as [r|] eqn:Hr; [|discriminate]. injection H as <-.
  destruct Hin as [<-|Hin].
  - exists ya. split; [exact Hfa | left; reflexivity].
  - destruct (IH r x eq_refl Hin) as (y & Hy & Hiny). exists y. split; [exact Hy | right; exact Hiny].
Qed.

Theorem node_mmapgaps_sound : nodeL_stmt SEGS A nx0 LIMIT SINV argH FS0 (is_ecall_at SEGS) (node_mmapgaps A nx0 LIMIT).
Proof.
  intros cs css E R FULL model TB HC Hec Hn HK.
  destruct (is_ecall_at_sound SEGS cs Hec) as (w & Hf & He & Hp0 & Hp4).
  unfold node_mmapgaps in Hn. rewrite kn_grant_filterM_eq in Hn.
  destruct (mmap_gate cs) as [[[prot flags] isnull]|] eqn:Hg; [|discriminate].
  destruct (mmap_gate_sound cs prot flags isnull Hg) as (H17 & H12 & H13 & H14 & H15 & H10).
  destruct (mmap_len cs) as [[[ne nlo] nhi]|] eqn:HML.
  2: { repeat match type of Hn with context [match ?x with _ => _ end] => destruct x; try discriminate Hn end. }
  assert (Hpf : prot = 3 /\ flags = 34 /\ isnull = true).
  { repeat match type of Hn with context [match ?x with _ => _ end] => destruct x; try discriminate Hn end; auto. }
  destruct Hpf as (-> & -> & ->). specialize (H10 eq_refl). cbn iota in Hn.
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
  apply andb_prop in Hcond as [Hcond Hnoh]. apply andb_prop in Hcond as [Hcond Hbud]. apply andb_prop in Hcond as [Hcond Hgap].
  apply andb_prop in Hcond as [Hfresh Hnev].
  cbv zeta in Hn.
  match type of Hn with (match gaps_of ?c ?v ?sc with _ => _ end) = _ => destruct (gaps_of c v sc) as [gaps|] eqn:Hgaps; [|discriminate] end.

  destruct (reg_lit_sound' E cs R FULL model 17 222 HC ltac:(lia) H17) as [R17 _].
  destruct (reg_lit_sound' E cs R FULL model 10 0 HC ltac:(lia) H10) as [R10 _].
  destruct (reg_lit_sound' E cs R FULL model 12 _ HC ltac:(lia) H12) as [R12 _].
  destruct (reg_lit_sound' E cs R FULL model 13 _ HC ltac:(lia) H13) as [R13 _].
  destruct (reg_lit_sound' E cs R FULL model 14 _ HC ltac:(lia) H14) as [R14 _].
  destruct (reg_lit_sound' E cs R FULL model 15 0 HC ltac:(lia) H15) as [R15 _].
  rewrite <- bv5_17 in R17. rewrite <- bv5_10 in R10. rewrite <- bv5_12 in R12. rewrite <- bv5_13 in R13.
  rewrite <- bv5_14 in R14. rewrite <- bv5_15 in R15. rewrite (Z_to_bv64_m1 _ eq_refl) in R14.
  destruct (mmap_len_sound E cs R FULL model ne nlo nhi HC HML) as (R11 & Hlen & Hne & Hnlo & HnZ & HnZal & HneE).
  change (Z_to_bv 5 11) with (Z_to_bv 5 (Z.of_nat 11)) in R11. rewrite <- bv5_11 in R11.
  set (len := bv_unsigned (edenot E (reg cs 11))) in *. set (nZ := page_round_up_Z len) in *.
  set (n := Z_to_bv 64 nZ).
  destruct (gap_ok_sound E cs R FULL model nhi nZ HC Hgap ltac:(lia)) as [a0 Ha0]. rewrite <- R10 in Ha0.
  pose proof (co_halt _ _ _ _ _ _ _ _ _ _ _ HC) as Hhalt.
  pose proof (co_top _ _ _ _ _ _ _ _ _ _ _ HC) as HTOP. unfold TOP, CEIL, CEILMAX in HTOP.
  assert (Hbudget : true = true -> a_eager cs + a_abytes cs + nhi <= LIMIT).
  { intros _. unfold budget_ok in Hbud. apply Z.leb_le in Hbud. exact Hbud. }

  assert (CONT : forall (a : word) model' FULL',
            grant_ok_na (getr R 10) model a nZ = true ->
            grant_post KRW a n model model' -> grant_mem KRW a n FULL FULL' -> m_fs model' = m_fs model ->
            srealizes SEGS (mkCfg (mkst (regupd R 10 a) (v_addi (Z_to_bv 64 (pc cs)) 4) FULL' (seg_rom SEGS)) model') TB).
  { intros a model' FULL' Hga GPo GM Hfs. rewrite R10 in Hga.
    destruct (mmap_null_cs1 cs KRW true ne nlo nhi E R FULL model a model' FULL' HC HML Hfresh Hnev Hbudget eq_refl eq_refl Hnoh Hga GPo GM)
      as (HC1 & Hbase & HneE' & Un & Hag0 & NEW).
    fold len nZ n in HC1, HneE', Un, NEW.
    rewrite (v_addi_pc (pc cs) Hp0 Hp4). rewrite bv5_10.
    set (E' := ext1 E (nxt cs) (Z_to_bv 64 (bv_unsigned a / 4096))) in *.
    set (cs1 := null_cs1 cs KRW true ne nlo nhi) in *.

    destruct (APS.gaps_of_sound SEGS A LIMIT SINV argH FS0 cs1 (nxt cs) 4096 gaps E' _ FULL' model' HC1 Hgaps) as (g & Hg_in & Hg_z).
    pose proof (APS.gap_child_ok SEGS A LIMIT SINV argH FS0 cs1 (nxt cs) g E' _ FULL' model' HC1 Hg_z) as HCg.
    destruct (opt_all_In _ _ _ gaps css g Hn Hg_in) as (csi & Hvis & Hin_i). cbv beta in Hvis.
    specialize (HK csi Hin_i E' (regupd R (Z_to_bv 5 (Z.of_nat 10)) a) FULL' model' (conj Hag0 (ext1_agree'' E (nxt cs) (Z_to_bv 64 (bv_unsigned a / 4096))))).
    assert (Hpc : pc csi = pc cs + 4).
    { destruct (vis_add_inv _ _ _ _ _ Hvis) as (nhi2 & _ & ->). reflexivity. }
    unfold cfg_of in HK. rewrite Hpc in HK. apply HK; [|exact Hfs].
    pose proof (u64_range a) as Ra.
    destruct (grant_ok_na_unpack _ _ _ _ Hga) as (_ & _ & Htop & _).
    eapply (grant_vis_add E' (gap_child cs1 (nxt cs) g) csi _ ne _ FULL' model' a n nZ HCg Hvis).
    + unfold gap_child. cbn [kn a_ss set_kn with_ss mk_ss s_know]. apply Forall_cons; [exact I|].
      unfold cs1, null_cs1, BothNodesMmLib.null_cs1, add_entry. cbn [kn a_ss mk_ss s_know]. apply kimg_in_hull_app; [|apply kimg_clip_in_hull'].
      apply kimg_in_hull_pure. unfold BothNodesMmLib.null_kfacts.
      apply Forall_cons; [exact I|]. apply (proj2 (Forall_app _ _ _)); split; [apply null_kend_pure|].
      apply (proj2 (Forall_app _ _ _)); split; [apply kdisj_fixed_pure|].
      apply (proj2 (Forall_app _ _ _)); split; [apply kdisj_shadow_pure | apply kdisj_new_pure].
    + exact Hbase.
    + exact HneE'.
    + exact Un.
    + lia.
    + lia.
    + intros x Hx. destruct (NEW x Hx) as (N1 & N2 & N3 & _). rewrite (gp_noacc _ _ _ _ _ GPo). cbn [kind_none]. auto.
    + intros x Hx. rewrite (proj2 GM x) by (rewrite Un; exact Hx). cbn [kind_none]. reflexivity. }

  unfold cfg_of.
  assert (Hbk : mmap_noreserve_backed_ok (Z_to_bv 64 34) model nZ = true).
  { unfold mmap_noreserve_backed_ok. rewrite mmap_noreserve_b_22.
    apply Z.leb_le. eapply Z.le_trans; [|eapply (budget_slack E cs R FULL model nhi HC Hbud)]. fold nZ. lia. }
  eapply (srz_mmap_rw1 SEGS R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w len (Z_to_bv 64 34) TB Hf He Hhalt R17 R11 Hlen R12 R13 mmap_flags_core_22 R14 R15).
  + exists a0. split; [exact Ha0 | exact Hbk].
  + intros a Hga _. rewrite (with_mmap_backing_plain _ _ _ _ mmap_noreserve_b_22). apply (CONT a); [exact Hga | | | reflexivity].
    * constructor; reflexivity.
    * split; [intros x Hx; apply zfill_out; exact Hx | intros x Hx; apply zfill_in; exact Hx].
Qed.

End Nodes.

Section OBL.
Variable SEGS : list Segment.            Variable A : atable.
Variable nx0 : nat.                      Variable LIMIT : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.     Variable FS0 : Fs.Fs.
Context {SC : StepCfg} {AF : AllocForced SC}.
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis RES_len : res_len_ok SEGS A.
Hypothesis RES_hull : Forall (fun iv => img_lo A <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_hi A)
                             (segments_reserved SEGS).
Hypothesis RES_cover : img_lo A < img_hi A /\ forall z, img_lo A <= z < img_hi A ->
  exists iv, In iv (segments_reserved SEGS) /\ bv_unsigned (fst iv) <= z < bv_unsigned (fst iv) + bv_unsigned (snd iv).
Hypothesis HULL_ok : hull_ok A.                  Hypothesis SHADOW_ok : shadow_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Hypothesis argH_sp0 : forall E (a : word), argH E a = true -> bv_unsigned (edenot E e_sp0_early) <= bv_unsigned a.
Hypothesis E_SP0 : AP.expr_vars_lt nx0 e_sp0_early = true.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.

Hypothesis SINV_pg : forall E M, SINV E M -> uE E e_pg_early = pagedown (uE E e_sp0_early).

Theorem node_mmap1_sound_OBL : OBL_mmap1 SEGS A nx0 LIMIT SINV argH FS0.
Proof. unfold OBL_mmap1. eapply node_mmap1_sound; eauto. Qed.
Theorem node_mprotect1_sound_OBL : OBL_mprotect1 SEGS A nx0 LIMIT SINV argH FS0.
Proof. unfold OBL_mprotect1. eapply node_mprotect1_sound; eauto. Qed.
Theorem node_mmapin1_sound_OBL : OBL_mmapin1 SEGS A nx0 LIMIT SINV argH FS0.
Proof. unfold OBL_mmapin1. eapply node_mmapin1_sound; eauto. Qed.
Theorem node_mmapgaps_sound_OBL : OBL_mmapgaps SEGS A nx0 LIMIT SINV argH FS0.
Proof. unfold OBL_mmapgaps. eapply node_mmapgaps_sound; eauto. Qed.
End OBL.
