(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SpinAlg AgentLib AgentNodes Nodes AllocSim
  AsanAcct AsanAcctShape AsanPlacement BackingAlgebra MmapSim RefNodes NoReserve.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanNodesIface.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import AsanNodesLibE.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import AsanNodesMmLib.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import AsanCeil.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import SpinAlgCfg AsanNodesLibCfg AsanPlanSoundCfg.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require AsanNodesMmA.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import AsanNodesNR.
Unset Nia Cache.  (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Import AX2. Import AX2S. Import AP. Import APS.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache.

(* [comment removed for export] *)
Section WithFP1. Context {FP : PropExec.FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

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
Hypothesis HULL_ok : hull_ok A.                  Hypothesis SHADOW_ok : shadow_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
Hypothesis argH_sp : forall E M (a : word), SINV E M -> argH E a = true -> uE E e_sp0 <= bv_unsigned a.
Hypothesis RES_cover : res_cover_ok SEGS A.
Hypothesis NX0_sp : nx0_sp_ok nx0.

#[local] Notation CSOK := (APS.cs_ok SEGS A LIMIT SINV argH FS0).
#[local] Notation HID := (APS.hid A argH).
#[local] Notation VIS := (APS.vis A).
#[local] Notation MR := (APS.Mr A argH).
#[local] Notation ALLOW := (APS.allowA A).
#[local] Notation cfg := (cfg_of SEGS).

(* [comment removed for export] *)
Let HS : nat -> option acs := fun _ => None.
Let XN : nat -> list expr -> acs -> option acs := fun _ _ _ => None.
Let XE : nat -> list expr -> acs -> option (Z * list spiece * acs) := fun _ _ _ => None.
Let XB : nat -> list expr -> acs -> option (acs * acs) := fun _ _ _ => None.
Let RES_len' : length (segments_reserved SEGS) = n_res A := RES_len.
Let HULL_ok' : 0 <= img_lo A /\ img_lo A mod 4096 = 0 /\ img_hi A mod 4096 = 0 /\ img_hi A <= KHI := HULL_ok.
Let SHADOW_ok' : 0 <= shadow_off A <= 2 ^ 47 := SHADOW_ok.
Let RES_hullH : RES_hull_def SEGS A := RES_hull.

(* [comment removed for export] *)
Let reg_sound' := APS.reg_sound SEGS A LIMIT SINV argH FS0.
Let reg_lit_sound' := APS.reg_lit_sound SEGS A LIMIT SINV argH FS0.
Let kentry_keep_sem' := APS.kentry_keep_sem SEGS.
Let kentry_apart_b_sem' := APS.kentry_apart_b_sem SEGS.
Let regs_ok_set_n' := APS.regs_ok_set_n.
Let in_ivs_map_den' := APS.in_ivs_map_den.
Let kimg_clip_in_hull' := APS.kimg_clip_in_hull A.
Let cs_ok_agree' := APS.cs_ok_agree SEGS A nx0 LIMIT SINV argH argH_agree SINV_agree NX0_sp FS0.
Let cs_ok_frame' := APS.cs_ok_frame SEGS A LIMIT SINV argH SINV_frame FS0.
Let hid_agree' := APS.hid_agree A nx0 argH argH_agree.
Let vis_add_sound' := APS.vis_add_sound SEGS A LIMIT HS XN XE XB SHADOW_ok SINV argH argH_sp FS0 0%nat.
Let A_wf_allowA' := APS.A_wf_allowA A HS XN XE XB 0%nat.
Let know_ok_unhide' := APS.know_ok_unhide SEGS A.
Let hid_hull' := APS.hid_hull A HULL_ok argH argH_high.
Let H_off_segments_cs' := APS.H_off_segments_cs SEGS A SEGS_in_hull HULL_ok argH argH_high.
Let maps_match_exact' := APS.maps_match_exact nx0 HS XN XE XB.

(* [comment removed for export] *)
Let budget_slack := AsanNodesMmLib.budget_slack SEGS A LIMIT SINV argH FS0 RES_len HULL_ok.
Let dest_hyps := AsanNodesMmLib.dest_hyps SEGS A LIMIT SINV argH FS0.
Let escale_4096_denot := AsanNodesMmLib.escale_4096_denot SEGS A RES_len HULL_ok.
Let find_containing_sound := AsanNodesMmLib.find_containing_sound SEGS A RES_len.
Let fixed_args_sound := AsanNodesMmLib.fixed_args_sound SEGS A LIMIT SINV argH FS0 RES_len HULL_ok.
Let fixed_cs1 := AsanNodesMmLib.fixed_cs1 A.
Let gap_ok_sound := AsanNodesMmLib.gap_ok_sound SEGS A LIMIT SINV argH FS0 RES_len HULL_ok SHADOW_ok.
Let gap_weight_eq := AsanNodesMmLib.gap_weight_eq SEGS A RES_len.
Let grant_cs1_ok := AsanNodesMmLib.grant_cs1_ok SEGS A LIMIT SINV argH FS0 RES_len HULL_ok SINV_frame argH_sp.
Let grant_eager_le := AsanNodesMmLib.grant_eager_le SEGS A RES_len HULL_ok.
Let grant_keep_apart := AsanNodesMmLib.grant_keep_apart SEGS A RES_len HULL_ok.
Let grant_new_facts := AsanNodesMmLib.grant_new_facts SEGS A LIMIT SINV argH FS0 RES_len HULL_ok argH_sp.
Let grant_vis_add := AsanNodesMmLib.grant_vis_add SEGS A LIMIT SINV argH FS0 SEGS_in_hull RES_len HULL_ok SHADOW_ok argH_high argH_sp.
Let grant_wf := AsanNodesMmLib.grant_wf SEGS A RES_len.
Let in_allow_ext := AsanNodesMmLib.in_allow_ext A.
Let inside_maps_apart := AsanNodesMmLib.inside_maps_apart SEGS A RES_len HULL_ok.
Let kimg_in_hull_cons2 := AsanNodesMmLib.kimg_in_hull_cons2 A HULL_ok SHADOW_ok.
Let kimg_in_hull_pure := AsanNodesMmLib.kimg_in_hull_pure A.
Let kmem_ok := AsanNodesMmLib.kmem_ok SEGS A RES_len HULL_ok.
Let kn_grant_filter_ok := AsanNodesMmLib.kn_grant_filter_ok SEGS A RES_len HULL_ok.
Let kn_rezero_clip_ok := AsanNodesMmLib.kn_rezero_clip_ok SEGS A RES_len HULL_ok.
Let kn_rezero_hull_ok := AsanNodesMmLib.kn_rezero_hull_ok SEGS A RES_len HULL_ok.
Let kn_rezero_ok_gen := AsanNodesMmLib.kn_rezero_ok_gen SEGS A RES_len HULL_ok.
Let kn_unfill_clip_ok := AsanNodesMmLib.kn_unfill_clip_ok SEGS A RES_len HULL_ok.
Let maps_match_disjoint := AsanNodesMmLib.maps_match_disjoint SEGS A RES_len.
Let mmap_fixed_grant_cs1 := AsanNodesMmLib.mmap_fixed_grant_cs1 SEGS A LIMIT SINV argH FS0 RES_len HULL_ok SHADOW_ok SINV_frame argH_sp.   (* [comment removed for export] *)
Let mmap_fixed_old_facts := AsanNodesMmLib.mmap_fixed_old_facts SEGS A nx0 LIMIT SINV argH FS0 RES_len RES_hull HULL_ok.
Let mmap_fixed_hole_facts := AsanNodesMmLib.mmap_fixed_hole_facts SEGS A LIMIT SINV argH FS0 RES_len HULL_ok SHADOW_ok.
Let fixed_pre := AsanNodesMmLib.fixed_pre SEGS A LIMIT SINV argH FS0 RES_len HULL_ok.
Let mmap_len_sound := AsanNodesMmLib.mmap_len_sound SEGS A LIMIT SINV argH FS0 RES_len HULL_ok.
Let mmap_null_cs1 := AsanNodesMmLib.mmap_null_cs1 SEGS A nx0 LIMIT SINV argH FS0 RES_len HULL_ok argH_agree SINV_frame SINV_agree argH_sp RES_cover NX0_sp.
Let null_cs1 := AsanNodesMmLib.null_cs1 A.
Let overlap_sum_contained := AsanNodesMmLib.overlap_sum_contained SEGS A RES_len HULL_ok.
Let page_aligned_sound := AsanNodesMmLib.page_aligned_sound SEGS A RES_len.
Let refuse_cont := AsanNodesMmLib.refuse_cont SEGS A nx0 LIMIT SINV argH FS0 RES_len SINV_frame.
Let refuse_ok := AsanNodesMmLib.refuse_ok SEGS A LIMIT SINV argH FS0 RES_len SINV_frame.
Let region_free_of_apart := AsanNodesMmLib.region_free_of_apart SEGS A nx0 LIMIT SINV argH FS0 RES_len RES_hull HULL_ok.
Let regs_ok_regupd_same := AsanNodesMmLib.regs_ok_regupd_same SEGS A RES_len.
Let reserved_free_above := AsanNodesMmLib.reserved_free_above SEGS A RES_len RES_hull HULL_ok.
Let safe_range_apart := AsanNodesMmLib.safe_range_apart SEGS A RES_len HULL_ok.
Let seps_map_disjoint := AsanNodesMmLib.seps_map_disjoint SEGS A RES_len.
Let shadow_facts_new_ok := AsanNodesMmLib.shadow_facts_new_ok SEGS A LIMIT SINV argH FS0 RES_len HULL_ok SHADOW_ok.
Let slice_args := AsanNodesMmLib.slice_args SEGS A LIMIT SINV argH FS0 RES_len RES_hull HULL_ok.
Let slice_hyps := AsanNodesMmLib.slice_hyps SEGS A LIMIT SINV argH FS0.
Let split_flat_estart := AsanNodesMmLib.split_flat_estart SEGS A RES_len HULL_ok.
Let vis_add_inv := AsanNodesMmLib.vis_add_inv A LIMIT.
Let vis_add_slice_ok := AsanNodesMmLib.vis_add_slice_ok SEGS A LIMIT SINV argH FS0 SEGS_in_hull RES_len HULL_ok SHADOW_ok argH_high argH_sp.
Let vis_grant_out := AsanNodesMmLib.vis_grant_out SEGS A RES_len.
Let d_MR_in := AsanNodesMmLib.d_MR_in SEGS A LIMIT SINV argH FS0 RES_len HULL_ok.
Let d_MR_out := AsanNodesMmLib.d_MR_out SEGS A LIMIT SINV argH FS0 RES_len HULL_ok.
Let d_bounds := AsanNodesMmLib.d_bounds SEGS A LIMIT SINV argH FS0.
Let d_eager := AsanNodesMmLib.d_eager SEGS A LIMIT SINV argH FS0 RES_len HULL_ok.
Let d_in_maps := AsanNodesMmLib.d_in_maps SEGS A LIMIT SINV argH FS0 RES_len HULL_ok.
Let d_lazy_out := AsanNodesMmLib.d_lazy_out SEGS A LIMIT SINV argH FS0 RES_len HULL_ok.
Let d_lohi := AsanNodesMmLib.d_lohi SEGS A LIMIT SINV argH FS0 RES_len HULL_ok.
Let d_maps_in := AsanNodesMmLib.d_maps_in SEGS A LIMIT SINV argH FS0 RES_len.
Let d_maps_out := AsanNodesMmLib.d_maps_out SEGS A LIMIT SINV argH FS0 RES_len.
Let d_noacc_in := AsanNodesMmLib.d_noacc_in SEGS A LIMIT SINV argH FS0 RES_len.
Let d_noacc_out := AsanNodesMmLib.d_noacc_out SEGS A LIMIT SINV argH FS0 RES_len.
Let d_sub_in := AsanNodesMmLib.d_sub_in SEGS A LIMIT SINV argH FS0 RES_len.
Let d_sub_out := AsanNodesMmLib.d_sub_out SEGS A LIMIT SINV argH FS0 RES_len.
Let d_vis_in := AsanNodesMmLib.d_vis_in SEGS A LIMIT SINV argH FS0 RES_len HULL_ok.
Let d_vis_out := AsanNodesMmLib.d_vis_out SEGS A LIMIT SINV argH FS0 RES_len HULL_ok.
Let d_wf' := AsanNodesMmLib.d_wf' SEGS A LIMIT SINV argH FS0 RES_len HULL_ok.
Let dest_cs1_ok := AsanNodesMmLib.dest_cs1_ok SEGS A LIMIT SINV argH FS0 RES_len RES_hull HULL_ok SHADOW_ok SINV_frame argH_sp.
Let page_base_aligned := AsanNodesMmLib.page_base_aligned SEGS A LIMIT SINV argH FS0 RES_len HULL_ok.
Let sl_MR_out := AsanNodesMmLib.sl_MR_out SEGS A LIMIT SINV argH FS0 RES_len HULL_ok.
Let sl_bounds := AsanNodesMmLib.sl_bounds SEGS A LIMIT SINV argH FS0.
Let sl_eager := AsanNodesMmLib.sl_eager SEGS A LIMIT SINV argH FS0 RES_len HULL_ok.
Let sl_in_maps := AsanNodesMmLib.sl_in_maps SEGS A LIMIT SINV argH FS0 RES_len HULL_ok.
Let sl_lazy_in := AsanNodesMmLib.sl_lazy_in SEGS A LIMIT SINV argH FS0 RES_len HULL_ok.
Let sl_lazy_out := AsanNodesMmLib.sl_lazy_out SEGS A LIMIT SINV argH FS0 RES_len HULL_ok.
Let sl_lohi := AsanNodesMmLib.sl_lohi SEGS A LIMIT SINV argH FS0 RES_len HULL_ok.
Let sl_noacc_in := AsanNodesMmLib.sl_noacc_in SEGS A LIMIT SINV argH FS0 RES_len.
Let sl_noacc_out := AsanNodesMmLib.sl_noacc_out SEGS A LIMIT SINV argH FS0 RES_len.
Let sl_vis_in_E := AsanNodesMmLib.sl_vis_in_E SEGS A LIMIT SINV argH FS0 RES_len HULL_ok.
Let sl_vis_in_F := AsanNodesMmLib.sl_vis_in_F SEGS A LIMIT SINV argH FS0 RES_len HULL_ok.
Let sl_vis_in_G := AsanNodesMmLib.sl_vis_in_G SEGS A LIMIT SINV argH FS0 RES_len HULL_ok.
Let sl_vis_out := AsanNodesMmLib.sl_vis_out SEGS A LIMIT SINV argH FS0 RES_len HULL_ok.
Let sl_wf' := AsanNodesMmLib.sl_wf' SEGS A LIMIT SINV argH FS0 RES_len HULL_ok.
Let slice_cs1_ok := AsanNodesMmLib.slice_cs1_ok SEGS A LIMIT SINV argH FS0 RES_len HULL_ok SHADOW_ok SINV_frame argH_sp.

Lemma mmap_nr_grant_sound2 : forall cs ms0 top b off ne nlo nhi kd (fl : Z) (eager visible : bool) cs' E R FULL model TB,
  CSOK E cs R FULL model -> is_ecall_at SEGS cs = true ->
  reg_lit cs 17 = Some 222 ->
  reg_lit cs 12 = Some (if kind_none kd then 0 else 3) ->
  reg_lit cs 13 = Some fl -> nr_core (Z_to_bv 64 fl) -> mmap_noreserve_b (Z_to_bv 64 fl) = kind_lazy kd ->
  reg_lit cs 14 = Some (two64 - 1) -> reg_lit cs 15 = Some 0 ->
  (kind_none kd || kind_lazy kd = negb eager)%bool -> is_tok_kind kd = false ->
  visible = eager ->
  fixed_args A cs top = Some (b, off, ne, nlo, nhi) -> top <= CEIL ->
  (negb eager || budget_ok LIMIT cs nhi)%bool = true ->
  CSOK E (with_maps0 cs ms0) R FULL model ->
  region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) (edenot E (reg cs 10))
              (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (reg cs 11))))) = true ->
  (forall m, In m ms0 -> is_hole m = true ->
     bv_unsigned (edenot E (reg cs 10)) + page_round_up_Z (bv_unsigned (edenot E (reg cs 11))) <= uE E (am_base m)
     \/ uE E (am_base m) + uE E (am_len m) <= bv_unsigned (edenot E (reg cs 10))) ->
  mmap_fixed_grant A LIMIT cs ms0 b off ne nhi kd eager visible = Some cs' ->
  (forall E' R' FULL' model', env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> CSOK E' cs' R' FULL' model' -> m_fs model' = m_fs model ->
      srealizes_cfg SEGS (cfg R' (pc cs') FULL' model') TB) ->
  srealizes_cfg SEGS (cfg R (pc cs) FULL model) TB.
Proof.
  intros cs ms0 top b off ne nlo nhi kd fl eager visible cs' E R FULL model TB HC Hec H17 H12 H13 Hcore Hnrb H14 H15 Hkind Hkfog Hvisible HFA Htop Hbud HC0 Hrf Hholes Hn HK.
  destruct (is_ecall_at_sound SEGS cs Hec) as (w & Hf & He & Hp0 & Hp4).
  assert (Hbudget : eager = true -> a_eager cs + a_abytes cs + nhi <= LIMIT).
  { intros ->. cbn in Hbud. unfold budget_ok in Hbud. apply Z.leb_le in Hbud. exact Hbud. }
  unfold mmap_fixed_grant in Hn. rewrite ?kn_grant_filterB_eqf in Hn.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  destruct (reg_lit_sound' E cs R FULL model 17 222 HC ltac:(lia) H17) as [R17 _].
  destruct (reg_lit_sound' E cs R FULL model 12 _ HC ltac:(lia) H12) as [R12 _].
  destruct (reg_lit_sound' E cs R FULL model 13 _ HC ltac:(lia) H13) as [R13 _].
  destruct (reg_lit_sound' E cs R FULL model 14 _ HC ltac:(lia) H14) as [R14 _].
  destruct (reg_lit_sound' E cs R FULL model 15 0 HC ltac:(lia) H15) as [R15 _].
  rewrite <- bv5_17 in R17. rewrite <- bv5_12 in R12. rewrite <- bv5_13 in R13.
  rewrite <- bv5_14 in R14. rewrite <- bv5_15 in R15. rewrite (Z_to_bv64_m1 _ eq_refl) in R14.
  destruct (fixed_args_sound E cs R FULL model top b off ne nlo nhi HC HFA) as (Hsp & HML & _).
  destruct (mmap_len_sound E cs R FULL model ne nlo nhi HC HML) as (R11 & Hlen & _).
  change (Z_to_bv 5 11) with (Z_to_bv 5 (Z.of_nat 11)) in R11. rewrite <- bv5_11 in R11.
  set (len := bv_unsigned (edenot E (reg cs 11))) in *. set (nZ := page_round_up_Z len) in *.
  set (n := Z_to_bv 64 nZ) in *. set (addr := edenot E (reg cs 10)) in *.
  pose proof (co_halt _ _ _ _ _ _ _ _ _ _ _ HC) as Hhalt.
  pose proof (proj2 (proj2 (proj2 (co_wf _ _ _ _ _ _ _ _ _ _ _ HC)))) as Hisp.  (* [comment removed for export] *)
  (* [comment removed for export] *)
  destruct (fixed_pre cs top b off ne nlo nhi E R FULL model HC HFA Htop)
    as (HneE & Un & Hest & Hal & Hpos & Himg & HtopA & R10 & HnZal & HnZ).
  fold len nZ n addr in HneE, Un, Hest, Hal, Hpos, Himg, HtopA, R10, HnZal, HnZ.
  assert (HaK : bv_unsigned addr + nZ <= CEIL) by lia.   (* [comment removed for export] *)
  rewrite <- bv5_10 in R10.
  assert (Hce : bv_unsigned addr + page_round_up_Z len <= alloc_ceiling) by (rewrite CEIL_eq; fold nZ; lia).
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  assert (CONT : forall model' FULL',
            grant_post kd addr n model model' -> grant_mem kd addr n FULL FULL' -> m_fs model' = m_fs model ->
            srealizes_cfg SEGS (mkCfg (mkst (regupd R 10 addr) (v_addi (Z_to_bv 64 (pc cs)) 4) FULL' (seg_rom SEGS)) model') TB).
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
    - (* [comment removed for export] *)
      subst eager. assert (Hrw : kind_none kd = false) by (destruct kd; cbn in Hkind |- *; congruence).
      pose proof (u64_range addr) as Ra.
      eapply (vis_add_sound'); [exact Hn | exact HC1 |].
      destruct (vis_add_inv _ _ _ _ _ Hn) as (nhi2 & _ & Ecs2).
      apply Forall_app. split.
      + (* [comment removed for export] *)
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
      + (* [comment removed for export] *)
        pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC1) as HK1. unfold Mr in HK1 |- *.
        eapply know_ok_unhide'; [apply H_off_segments_cs' | | | | exact HK1].
        * unfold fixed_cs1, add_entry. cbn [kn a_ss mk_ss s_know with_maps0]. apply kimg_in_hull_app; [|apply kimg_clip_in_hull'].
          destruct kd; cbn [mkind_eqb]; try (apply kimg_in_hull_pure; apply Forall_nil).
          apply kimg_in_hull_pure. apply Forall_flat_map. apply Forall_forall. intros p _. unfold shadow_facts.
          destruct (shadow_of A (kn cs) (fst p) (snd p)) as [[sb sk] sn]. destruct (find_containing _ _ _ _ _ _); [|apply Forall_nil].
          apply Forall_cons; [exact I|]. apply Forall_cons; [exact I|]. apply Forall_nil.
        * intros y Hy. rewrite Ecs2 in Hy. eapply hid_cons_sub. exact Hy.
        * intros y Hy. apply hid_hull'. exact Hy.
    - injection Hn as <-. exact HC1. }
  (* [comment removed for export] *)
  unfold cfg_of.
  destruct kd; cbn [kind_none kind_lazy negb orb] in *; [| | | | discriminate Hkfog | discriminate Hkfog].
  - (* [comment removed for export] *)
    destruct eager; [|discriminate].
    eapply (srz_cfg_mmap_noreplace_rw_free2 SEGS R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w addr len (Z_to_bv 64 fl) TB
              Hf He Hhalt R17 R10 Hal Hpos R11 ltac:(lia) Hce Hisp R12 R13 Hcore R14 R15 Hrf).
    + unfold mmap_noreserve_backed_ok. rewrite Hnrb. apply Z.leb_le. cbn in Hbud.
      eapply Z.le_trans; [|eapply (budget_slack E cs R FULL model nhi HC Hbud)]. fold nZ. lia.
    + rewrite with_mmap_backing_plain by exact Hnrb.
      apply CONT; [constructor; reflexivity | | reflexivity].
      split; [intros x Hx; apply zfill_out; exact Hx | intros x Hx; apply zfill_in; exact Hx].
  - (* [comment removed for export] *)
    destruct eager; [discriminate|].
    eapply (srz_cfg_mmap_noreplace_rw_free2 SEGS R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w addr len (Z_to_bv 64 fl) TB
              Hf He Hhalt R17 R10 Hal Hpos R11 ltac:(lia) Hce Hisp R12 R13 Hcore R14 R15 Hrf).
    + unfold mmap_noreserve_backed_ok. rewrite Hnrb. reflexivity.
    + rewrite with_mmap_backing_lazy by exact Hnrb.
      fold nZ. fold n. apply CONT; [| | reflexivity].
      * constructor; try reflexivity.
        unfold vm_add_lazy. rewrite m_vm_lazy_with_vm_backing.
        rewrite lazy_interior_fresh; [reflexivity | exact Hal | rewrite Un; exact HnZal | rewrite Un; lia | rewrite Un; unfold CEIL in HaK; lia].
      * split; [intros x Hx; apply zfill_out; exact Hx | intros x Hx; apply zfill_in; exact Hx].
  - (* [comment removed for export] *)
    destruct eager; [discriminate|].
    eapply (srz_cfg_mmap_noreplace_none_free2 SEGS R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w addr len (Z_to_bv 64 fl) TB
              Hf He Hhalt R17 R10 Hal Hpos R11 ltac:(lia) Hce Hisp R12 R13 Hcore R14 R15 Hrf).
    + rewrite with_mmap_backing_plain by exact Hnrb.
      apply CONT; [constructor; reflexivity | | reflexivity].
      split; [intros x Hx; apply unfill_out; exact Hx | intros x Hx; apply unfill_in; exact Hx].
  - (* [comment removed for export] *)
    destruct eager; [discriminate|].
    eapply (srz_cfg_mmap_noreplace_none_free2 SEGS R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w addr len (Z_to_bv 64 fl) TB
              Hf He Hhalt R17 R10 Hal Hpos R11 ltac:(lia) Hce Hisp R12 R13 Hcore R14 R15 Hrf).
    + rewrite with_mmap_backing_lazy by exact Hnrb.
      fold nZ. fold n. apply CONT; [| | reflexivity].
      * constructor; try reflexivity.
        unfold vm_add_lazy. rewrite m_vm_lazy_with_vm_backing.
        rewrite lazy_interior_fresh; [reflexivity | exact Hal | rewrite Un; exact HnZal | rewrite Un; lia | rewrite Un; unfold CEIL in HaK; lia].
      * split; [intros x Hx; apply unfill_out; exact Hx | intros x Hx; apply unfill_in; exact Hx].
Qed.

Lemma mmap_nr_free_sound2 : forall cs kd (fl : Z) (eager visible : bool) cs' E R FULL model TB,
  CSOK E cs R FULL model -> is_ecall_at SEGS cs = true ->
  reg_lit cs 17 = Some 222 ->
  reg_lit cs 12 = Some (if kind_none kd then 0 else 3) ->
  reg_lit cs 13 = Some fl -> nr_core (Z_to_bv 64 fl) -> mmap_noreserve_b (Z_to_bv 64 fl) = kind_lazy kd ->
  reg_lit cs 14 = Some (two64 - 1) -> reg_lit cs 15 = Some 0 ->
  (kind_none kd || kind_lazy kd = negb eager)%bool -> is_tok_kind kd = false ->
  visible = eager ->
  mmap_fixed_free A LIMIT cs kd eager visible = Some cs' ->
  (forall E' R' FULL' model', env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> CSOK E' cs' R' FULL' model' -> m_fs model' = m_fs model ->
      srealizes_cfg SEGS (cfg R' (pc cs') FULL' model') TB) ->
  srealizes_cfg SEGS (cfg R (pc cs) FULL model) TB.
Proof.
  intros cs kd fl eager visible cs' E R FULL model TB HC Hec H17 H12 H13 Hcore Hnrb H14 H15 Hkind Hkfog Hvisible Hn HK.
  unfold mmap_fixed_free in Hn. rewrite ?kn_grant_filterB_eqf in Hn.   (* [comment removed for export] *)
  destruct (fixed_args A cs KHI) as [[[[[b off] ne] nlo] nhi]|] eqn:HFA.
  - (* [comment removed for export] *)
    match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
    apply andb_prop in Hcond as [Hcond Hav]. apply andb_prop in Hcond as [Hcond Hnev].
    apply andb_prop in Hcond as [Hcond Hbud]. apply andb_prop in Hcond as [Hnf Hall].
    destruct (mmap_fixed_old_facts cs b off ne nlo nhi E R FULL model HC HFA Hnf Hall) as (HC0 & Hrf & Hholes).
    eapply (mmap_nr_grant_sound2 cs (a_maps cs) KHI b off ne nlo nhi kd fl eager visible cs' E R FULL model TB
              HC Hec H17 H12 H13 Hcore Hnrb H14 H15 Hkind Hkfog Hvisible HFA ltac:(unfold KHI, CEIL; lia) Hbud
              HC0 Hrf Hholes Hn HK).
  - (* [comment removed for export] *)
    destruct (fixed_args A cs CEIL) as [[[[[b off] ne] nlo] nhi]|] eqn:HFA2; [|discriminate].
    destruct (find_hole (kn cs) (a_maps cs) (reg cs 10) ne) as [h|] eqn:Hfh; [|discriminate].
    match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
    apply andb_prop in Hcond as [Hcond Hav]. apply andb_prop in Hcond as [Hcond Hnev].
    apply andb_prop in Hcond as [Hap Hbud].
    destruct (mmap_fixed_hole_facts cs b off ne nlo nhi h E R FULL model HC HFA2 Hfh Hap) as (HC0 & Hrf & Hholes).
    eapply (mmap_nr_grant_sound2 cs (unhole (a_maps cs) h) CEIL b off ne nlo nhi kd fl eager visible cs' E R FULL model TB
              HC Hec H17 H12 H13 Hcore Hnrb H14 H15 Hkind Hkfog Hvisible HFA2 ltac:(lia) Hbud
              HC0 Hrf Hholes Hn HK).
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Theorem node_mmap_nr_sound : APSC.mm2_stmt_fp SEGS A nx0 LIMIT SINV argH FS0 FP (node_mmap_nr A LIMIT).
Proof.
  intros cs csa csb E R FULL model TB HC Hec Hn HKB.
  unfold node_mmap_nr in Hn.
  destruct (mmap_gate cs) as [[[prot flags] isnull]|] eqn:Hg; [|discriminate].
  destruct isnull; [discriminate|].
  destruct (nr_kind prot flags) as [[kd eager]|] eqn:Hk; [|discriminate].
  destruct (mmap_fixed_free A LIMIT cs kd eager eager) as [csG|] eqn:Hm; [|discriminate].
  injection Hn as <- <-.
  destruct (AsanNodesMmA.mmap_gate_sound cs prot flags false Hg) as (H17 & H12 & H13 & H14 & H15 & _).
  destruct (nr_kind_sound prot flags kd eager Hk) as (Hp & Hcore & Hnrb & Hkind & Hkfog).
  subst prot.
  eapply (mmap_nr_free_sound2 cs kd flags eager eager); eauto.
Qed.

End Nodes.
End WithFP1.

(* [comment removed for export] *)
Definition XN_nr (SEGS : list Segment) (A : atable) (LIMIT : Z) (XN0 : nat -> list expr -> acs -> option acs)
    (id : nat) (args : list expr) (cs : acs) : option acs :=
  if Nat.eqb id NR_ID then
    (if is_ecall_at SEGS cs then
       match node_mmap_nr A LIMIT cs with Some (_, csG) => Some csG | None => None end
     else None)
  else XN0 id args cs.

Theorem XN_nr_cfg_OBL : forall SEGS A nx0 LIMIT SINV argH FS0 (FPS : PropExec.FPState -> Prop) XN0,
  wx_segs_nowrap SEGS ->
  (forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None) ->
  res_len_ok SEGS A ->
  Forall (fun iv => img_lo A <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_hi A) (segments_reserved SEGS) ->
  hull_ok A -> shadow_ok A ->
  (forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a) ->
  (forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a) ->
  (forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M') ->
  (forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M) ->
  (forall E M (a : word), SINV E M -> argH E a = true -> uE E e_sp0 <= bv_unsigned a) ->
  res_cover_ok SEGS A -> nx0_sp_ok nx0 ->
  APSC.ext_stmt_cfg SEGS A nx0 LIMIT XN0 SINV argH FS0 FPS ->
  APSC.ext_stmt_cfg SEGS A nx0 LIMIT (XN_nr SEGS A LIMIT XN0) SINV argH FS0 FPS.
Proof.
  intros SEGS A nx0 LIMIT SINV argH FS0 FPS XN0 SEGS_wx SEGS_in_hull RES_len RES_hull HULL_ok SHADOW_ok argH_high argH_agree
    SINV_frame SINV_agree argH_sp RES_cover NX0_sp H0 id args FP HFP cs cs' E R FULL model T HC Hpre Hn Hk.
  unfold XN_nr in Hn. destruct (Nat.eqb id NR_ID).
  - destruct (is_ecall_at SEGS cs) eqn:Hec; [|discriminate].
    destruct (node_mmap_nr A LIMIT cs) as [[csa csG]|] eqn:Hm; [|discriminate]. injection Hn as <-.
    eapply (@node_mmap_nr_sound FP SEGS A nx0 LIMIT SINV argH FS0); try eassumption. exact (Hk FP HFP).
  - exact (H0 id args FP HFP cs cs' E R FULL model T HC Hpre Hn Hk).
Qed.
