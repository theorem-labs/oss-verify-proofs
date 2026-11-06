(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.XQ Require Import StoreOk.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlg ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.XQ Require Import SpinAlg AgentLib AgentNodes Nodes.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import AllocSim.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.XQ Require Import AsanAcct AsanAcctShape AsanPlacement BackingAlgebra.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import MmapSim.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.XQ Require Import RefNodes NoReserve.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.XQ Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanNodesIface.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.XQ Require Import AsanNodesLibE.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.XQ Require Import AsanNodesMmLib AsanNodesMmCs.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.XQ Require Import AsanCeil CfgLift AsanNodesLibCfg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Import ListNotations.
Open Scope Z_scope.

Import AX2. Import AX2S. Import AP. Import APS.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Nodes.
Variable SEGS : list Segment.
Variable SC : SpuriousCfg.     (* [comment removed for export] *)
Hypothesis ALLOC_OFF : family_may_fail SC FamAlloc = false.
Variable A : atable.
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
(* [comment removed for export] *)
Hypothesis argH_sp0 : forall E M (a : word), SINV E M -> argH E a = true -> uE E e_sp0 <= bv_unsigned a.
Hypothesis NX0_S : nx0_sp_ok nx0.
Hypothesis RES_cover : res_cover_def SEGS A.

#[local] Notation CSOK := (APS.cs_ok SEGS A LIMIT SINV argH FS0).
#[local] Notation HID := (APS.hid A argH).
#[local] Notation VIS := (APS.vis A).
#[local] Notation MR := (APS.Mr A argH).
#[local] Notation ALLOW := (APS.allowA A).
#[local] Notation cfg := (cfg_of SEGS).
#[local] Notation RZ := (realizes_cfg SC SEGS).

(* [comment removed for export] *)
Let reg_sound' := APS.reg_sound SEGS A LIMIT SINV argH FS0.
Let reg_lit_sound' := APS.reg_lit_sound SEGS A LIMIT SINV argH FS0.
Let regs_ok_set_n' := APS.regs_ok_set_n.
Let kimg_clip_in_hull' := APS.kimg_clip_in_hull A.
Let vis_add_sound' := APS.vis_add_sound SEGS A LIMIT SHADOW_ok SINV argH argH_sp0 FS0.
Let A_wf_allowA' := APS.A_wf_allowA A.
Let know_ok_unhide' := APS.know_ok_unhide SEGS A.
Let hid_hull' := APS.hid_hull A HULL_ok argH argH_high.
Let H_off_segments_cs' := APS.H_off_segments_cs SEGS A SEGS_in_hull HULL_ok argH argH_high.
Let cs_top := APS.cs_top SEGS A LIMIT SINV argH FS0.
Let cs_argH_top := APS.cs_argH_top SEGS A LIMIT SINV argH argH_sp0 FS0.

(* [comment removed for export] *)
Let mmap_len_sound := AsanNodesMmCs.mmap_len_sound SEGS A LIMIT SINV argH FS0 RES_len HULL_ok.
Let gap_ok_sound := AsanNodesMmCs.gap_ok_sound SEGS A LIMIT SINV argH FS0 RES_len HULL_ok SHADOW_ok.
Let mmap_null_cs1 := AsanNodesMmCs.mmap_null_cs1 SEGS A nx0 LIMIT SINV argH FS0 RES_len HULL_ok SHADOW_ok argH_agree SINV_frame SINV_agree argH_sp0 NX0_S RES_cover.
Let grant_vis_add := AsanNodesMmCs.grant_vis_add SEGS A LIMIT SINV argH FS0 SEGS_in_hull RES_len HULL_ok SHADOW_ok argH_high argH_sp0.
Let slice_cs1_ok := AsanNodesMmCs.slice_cs1_ok SEGS A LIMIT SINV argH FS0 RES_len HULL_ok SHADOW_ok SINV_frame argH_sp0.
Let slice_args := AsanNodesMmCs.slice_args SEGS A LIMIT SINV argH FS0 RES_len RES_hull HULL_ok.
Let budget_slack := AsanNodesMmCs.budget_slack SEGS A LIMIT SINV argH FS0 RES_len HULL_ok.
Let fixed_pre := AsanNodesMmCs.fixed_pre SEGS A LIMIT SINV argH FS0 RES_len HULL_ok.
Let mmap_fixed_grant_cs1 := AsanNodesMmCs.mmap_fixed_grant_cs1 SEGS A LIMIT SINV argH FS0 RES_len HULL_ok SHADOW_ok SINV_frame argH_sp0.
Let mmap_fixed_old_facts := AsanNodesMmCs.mmap_fixed_old_facts SEGS A nx0 LIMIT SINV argH FS0 RES_len RES_hull HULL_ok.
Let fixed_args_sound := AsanNodesMmCs.fixed_args_sound SEGS A LIMIT SINV argH FS0 RES_len HULL_ok.
Let vis_add_inv := AsanNodesMmCs.vis_add_inv A LIMIT.
Let kimg_in_hull_pure := AsanNodesMmCs.kimg_in_hull_pure A.
Let null_kend_pure := AsanNodesMmCs.null_kend_pure A.
Let kn_unfill_clip_ok := AsanNodesMmCs.kn_unfill_clip_ok SEGS A RES_len HULL_ok.
Let kn_rezero_clip_ok := AsanNodesMmCs.kn_rezero_clip_ok SEGS A RES_len HULL_ok.
Let vis_add_slice_ok := AsanNodesMmCs.vis_add_slice_ok SEGS A LIMIT SINV argH FS0 SEGS_in_hull RES_len HULL_ok SHADOW_ok argH_high argH_sp0.
Let sl_MR_out := AsanNodesMmCs.sl_MR_out SEGS A LIMIT SINV argH FS0 RES_len HULL_ok.
Let sl_in_maps := AsanNodesMmCs.sl_in_maps SEGS A LIMIT SINV argH FS0 RES_len HULL_ok.
Let sl_noacc_in := AsanNodesMmCs.sl_noacc_in SEGS A LIMIT SINV argH FS0 RES_len.
Let sl_vis_in_F := AsanNodesMmCs.sl_vis_in_F SEGS A LIMIT SINV argH FS0 RES_len HULL_ok.
Let sl_top := AsanNodesMmCs.sl_top SEGS A LIMIT SINV argH FS0.
Let shadow_facts_new_ok := AsanNodesMmCs.shadow_facts_new_ok SEGS A LIMIT SINV argH FS0 RES_len HULL_ok SHADOW_ok.
Let regs_ok_regupd_same := AsanNodesMmCs.regs_ok_regupd_same SEGS A RES_len.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma kdisj_frame_pure : forall nb ne,
  Forall (fun K => match K with KImg _ _ => False | _ => True end) (kdisj_frame A nb ne).
Proof. intros. unfold kdisj_frame. repeat constructor. Qed.
Lemma kdisj_zone_pure : forall ms nb ne,
  Forall (fun K => match K with KImg _ _ => False | _ => True end) (kdisj_zone A ms nb ne).
Proof. intros. unfold kdisj_zone. destruct (zone_tiled A ms); repeat constructor. Qed.
Lemma ksh_disj_pure : forall k b1 n1 b2 n2,
  Forall (fun K => match K with KImg _ _ => False | _ => True end) (ksh_disj A k b1 n1 b2 n2).
Proof.
  intros. unfold ksh_disj. destruct (shadow_of A k b1 n1) as [[? ?] ?]. destruct (shadow_of A k b2 n2) as [[? ?] ?].
  match goal with |- Forall _ (if ?c then _ else _) => destruct c end; repeat constructor.
Qed.
Lemma kdisj_frame_sh_pure : forall k nb ne,
  Forall (fun K => match K with KImg _ _ => False | _ => True end) (kdisj_frame_sh A k nb ne).
Proof. intros. unfold kdisj_frame_sh. apply Forall_app. split; apply ksh_disj_pure. Qed.
Lemma kdisj_new_sh_pure : forall k ms nb ne,
  Forall (fun K => match K with KImg _ _ => False | _ => True end) (kdisj_new_sh A k ms nb ne).
Proof.
  intros. unfold kdisj_new_sh. apply Forall_flat_map. apply Forall_forall. intros m _.
  destruct (is_fog m); [apply Forall_nil | apply ksh_disj_pure].
Qed.

Lemma grant_pin_facts : forall model a nZ, grant_ok_na_pin model a nZ = true ->
  bv_unsigned a mod 4096 = 0 /\ 0 < bv_unsigned a /\ bv_unsigned a + nZ <= alloc_top (m_vmmaps model)
  /\ region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) a (Z_to_bv 64 nZ) = true.
Proof.
  intros model a nZ Hg. unfold grant_ok_na_pin in Hg.
  apply andb_prop in Hg as [Hg Hrf]. apply andb_prop in Hg as [Hg Htop]. apply andb_prop in Hg as [Hal Hpos].
  apply Z.eqb_eq in Hal. apply Z.ltb_lt in Hpos. apply Z.leb_le in Htop. unfold page_size in Hal. auto.
Qed.

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
      RZ (cfg R' (pc cs') FULL' model') TB) ->
  RZ (cfg R (pc cs) FULL model) TB.
Proof.
  intros cs kd eager visible cs' E R FULL model TB HC Hec H17 H10 H12 H13 H14 H15 Hkind Hkfog Hvisible Hn HK.
  destruct (AsanNodesMmLib.is_ecall_at_sound SEGS cs Hec) as (w & Hf & He & Hp0 & Hp4).
  pose proof Hn as Hn0.
  unfold mmap_null in Hn.
  destruct (mmap_len cs) as [[[ne nlo] nhi]|] eqn:HML; [|discriminate].
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
  apply andb_prop in Hcond as [Hcond Hylo]. apply andb_prop in Hcond as [Hcond Hnof].
  apply andb_prop in Hcond as [Hcond Hbud]. apply andb_prop in Hcond as [Hcond Hgap].
  apply andb_prop in Hcond as [Hfresh Hnev].
  apply Z.leb_le in Hylo.
  (* [comment removed for export] *)
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
  pose proof (gap_ok_sound E cs R FULL model nhi nZ HC Hgap ltac:(lia)) as WIT.
  pose proof (co_halt _ _ _ _ _ _ _ _ _ _ _ HC) as Hhalt.
  pose proof (cs_top _ _ _ _ _ HC) as (T1 & T2 & T3).
  (* [comment removed for export] *)
  assert (CONT : forall (a : word) model' FULL',
            grant_ok_na_pin model a nZ = true ->
            grant_post kd a n model model' -> grant_mem kd a n FULL FULL' -> m_fs model' = m_fs model ->
            RZ (mkCfg (mkst (regupd R 10 a) (v_addi (Z_to_bv 64 (pc cs)) 4) FULL' (seg_rom SEGS)) model') TB).
  { intros a model' FULL' Hg GPo GM Hfs.
    destruct (mmap_null_cs1 cs kd eager ne nlo nhi E R FULL model a model' FULL' HC HML Hfresh Hnev
                ltac:(intros ->; cbn in Hbud; unfold budget_ok in Hbud; apply Z.leb_le in Hbud; exact Hbud)
                Hylo Hkind Hkfog Hnof Hg GPo GM) as (HC1 & Hbase & HneE' & Un & Hag0 & NEW).
    fold len nZ n in HC1, HneE', Un, NEW.
    rewrite (AsanNodesMmLib.v_addi_pc (pc cs) Hp0 Hp4). rewrite bv5_10.
    set (E' := ext1 E (nxt cs) (Z_to_bv 64 (bv_unsigned a / 4096))) in *.
    assert (Hpc : pc cs' = pc cs + 4).
    { destruct visible; [|injection Hn as <-; reflexivity].
      destruct (vis_add_inv _ _ _ _ _ Hn) as (nhi2 & _ & ->). reflexivity. }
    specialize (HK E' (regupd R (Z_to_bv 5 (Z.of_nat 10)) a) FULL' model' (conj Hag0 (ext1_agree'' E (nxt cs) (Z_to_bv 64 (bv_unsigned a / 4096))))).
    unfold cfg_of in HK. rewrite Hpc in HK. apply HK; [|exact Hfs].
    destruct visible.
    - (* [comment removed for export] *)
      assert (Hrw : kind_none kd = false) by (destruct kd; cbn in Hvisible |- *; congruence).
      pose proof (u64_range a) as Ra.
      destruct (grant_pin_facts model a nZ Hg) as (_ & _ & Htop & _).
      eapply (grant_vis_add E' (null_cs1 A cs kd eager ne nlo nhi) cs' _ ne _ FULL' model' a n nZ HC1 Hn).
      + unfold null_cs1, add_entry. cbn [kn a_ss mk_ss s_know]. apply kimg_in_hull_app; [|apply kimg_clip_in_hull'].
        apply kimg_in_hull_pure. apply Forall_cons; [exact I | apply (proj2 (Forall_app _ _ _)); split; [apply null_kend_pure | apply (proj2 (Forall_app _ _ _)); split; [apply kdisj_frame_pure | apply (proj2 (Forall_app _ _ _)); split; [apply kdisj_zone_pure | apply (proj2 (Forall_app _ _ _)); split; [apply kdisj_new_pure | apply (proj2 (Forall_app _ _ _)); split; [apply kdisj_frame_sh_pure | apply kdisj_new_sh_pure]]]]]].
      + exact Hbase.
      + exact HneE'.
      + exact Un.
      + lia.
      + unfold TOPMAX in *. lia.
      + intros x Hx. destruct (NEW x Hx) as (N1 & N2 & N3 & _). rewrite (gp_noacc _ _ _ _ _ GPo), Hrw. auto.
      + intros x Hx. rewrite (proj2 GM x) by (rewrite Un; exact Hx). rewrite Hrw. reflexivity.
    - injection Hn as <-. exact HC1. }
  (* [comment removed for export] *)
  unfold cfg_of.
  destruct kd; cbn [kind_none kind_lazy negb orb] in *; [| | | | discriminate Hkfog | discriminate Hkfog | ].   (* [comment removed for export] *)
  - (* [comment removed for export] *)
    destruct eager; [|discriminate].
    eapply (rz_mmap_rw1_cfg SC SEGS ALLOC_OFF R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w len (Z_to_bv 64 34) TB Hf He Hhalt R17 R11 Hlen R12 R13 mmap_flags_core_22 R14 R15 WIT).
    + unfold mmap_noreserve_backed_ok. rewrite mmap_noreserve_b_22.
      apply Z.leb_le. cbn in Hbud. eapply Z.le_trans; [|eapply (budget_slack E cs R FULL model nhi HC Hbud)]. fold nZ. lia.
    + intros a Hg. rewrite (with_mmap_backing_plain _ _ _ _ mmap_noreserve_b_22). apply (CONT a); [exact Hg | | | reflexivity].
      * constructor; reflexivity.
      * split; [intros x Hx; apply zfill_out; exact Hx | intros x Hx; apply zfill_in; exact Hx].
  - (* [comment removed for export] *)
    destruct eager; [discriminate|].
    eapply (rz_mmap_rw1_cfg SC SEGS ALLOC_OFF R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w len (Z_to_bv 64 16418) TB Hf He Hhalt R17 R11 Hlen R12 R13 mmap_flags_core_4022 R14 R15 WIT).
    + unfold mmap_noreserve_backed_ok. rewrite mmap_noreserve_b_4022. reflexivity.
    + intros a Hg. rewrite (with_mmap_backing_lazy _ _ _ _ mmap_noreserve_b_4022). apply (CONT a); [exact Hg | | | reflexivity].
      * destruct (grant_pin_facts model a nZ Hg) as (Hal & Hpos & Htop & _).
        constructor; try reflexivity.
        unfold vm_add_lazy. rewrite m_vm_lazy_with_vm_backing. rewrite lazy_interior_fresh; [reflexivity | exact Hal | | |]; subst n; rewrite u64_lit by (unfold TOPMAX in T2; lia); [exact HnZal | lia | unfold TOPMAX in T2; lia].
      * split; [intros x Hx; apply zfill_out; exact Hx | intros x Hx; apply zfill_in; exact Hx].
  - (* [comment removed for export] *)
    destruct eager; [discriminate|].
    eapply (rz_mmap_none1_cfg SC SEGS ALLOC_OFF R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w len (Z_to_bv 64 34) TB Hf He Hhalt R17 R11 Hlen R12 R13 mmap_flags_core_22 R14 R15 WIT).
    intros a Hg. rewrite (with_mmap_backing_plain _ _ _ _ mmap_noreserve_b_22). apply (CONT a); [exact Hg | | | reflexivity].
    * constructor; reflexivity.
    * split; [intros x Hx; apply unfill_out; exact Hx | intros x Hx; apply unfill_in; exact Hx].
  - (* [comment removed for export] *)
    destruct eager; [discriminate|].
    eapply (rz_mmap_none1_cfg SC SEGS ALLOC_OFF R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w len (Z_to_bv 64 16418) TB Hf He Hhalt R17 R11 Hlen R12 R13 mmap_flags_core_4022 R14 R15 WIT).
    intros a Hg. rewrite (with_mmap_backing_lazy _ _ _ _ mmap_noreserve_b_4022). apply (CONT a); [exact Hg | | | reflexivity].
    * destruct (grant_pin_facts model a nZ Hg) as (Hal & Hpos & Htop & _).
      constructor; try reflexivity.
      unfold vm_add_lazy. rewrite m_vm_lazy_with_vm_backing. rewrite lazy_interior_fresh; [reflexivity | exact Hal | | |]; subst n; rewrite u64_lit by (unfold TOPMAX in T2; lia); [exact HnZal | lia | unfold TOPMAX in T2; lia].
    * split; [intros x Hx; apply unfill_out; exact Hx | intros x Hx; apply unfill_in; exact Hx].
  - (* [comment removed for export] *)
    destruct eager; [|discriminate].
    eapply (rz_mmap_rw1_cfg SC SEGS ALLOC_OFF R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w len (Z_to_bv 64 34) TB Hf He Hhalt R17 R11 Hlen R12 R13 mmap_flags_core_22 R14 R15 WIT).
    + unfold mmap_noreserve_backed_ok. rewrite mmap_noreserve_b_22.
      apply Z.leb_le. cbn in Hbud. eapply Z.le_trans; [|eapply (budget_slack E cs R FULL model nhi HC Hbud)]. fold nZ. lia.
    + intros a Hg. rewrite (with_mmap_backing_plain _ _ _ _ mmap_noreserve_b_22). apply (CONT a); [exact Hg | | | reflexivity].
      * constructor; reflexivity.
      * split; [intros x Hx; apply zfill_out; exact Hx | intros x Hx; apply zfill_in; exact Hx].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma mmap_fixed_grant_sound1 : forall cs ms0 b off ne nlo nhi kd (flags : Z) (eager visible : bool) cs' E R FULL model TB,
  CSOK E cs R FULL model -> is_ecall_at SEGS cs = true ->
  reg_lit cs 17 = Some 222 ->
  reg_lit cs 12 = Some (if kind_none kd then 0 else 3) ->
  reg_lit cs 13 = Some flags ->
  ((kind_lazy kd = false /\ flags = 50) \/ (kind_lazy kd = true /\ (flags = 16434 \/ flags = 1064994))) ->
  reg_lit cs 14 = Some (two64 - 1) -> reg_lit cs 15 = Some 0 ->
  (kind_none kd || kind_lazy kd = negb eager)%bool -> is_tok_kind kd = false ->
  visible = eager ->
  fixed_args A cs true CEIL = Some (b, off, ne, nlo, nhi) ->
  (negb eager || budget_ok LIMIT cs nhi)%bool = true ->
  CSOK E (with_maps0 cs ms0) R FULL model ->
  region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) (edenot E (reg cs 10))
              (Z_to_bv 64 (page_round_up_Z (bv_unsigned (edenot E (reg cs 11))))) = true ->
  (forall m, In m ms0 -> is_hole m = true ->
     bv_unsigned (edenot E (reg cs 10)) + page_round_up_Z (bv_unsigned (edenot E (reg cs 11))) <= uE E (am_base m)
     \/ uE E (am_base m) + uE E (am_len m) <= bv_unsigned (edenot E (reg cs 10))) ->
  a_ylo cs <= 0 ->
  mmap_fixed_grant A LIMIT cs ms0 b off ne nhi kd eager visible = Some cs' ->
  (forall E' R' FULL' model', env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> CSOK E' cs' R' FULL' model' -> m_fs model' = m_fs model ->
      RZ (cfg R' (pc cs') FULL' model') TB) ->
  RZ (cfg R (pc cs) FULL model) TB.
Proof.
  intros cs ms0 b off ne nlo nhi kd flags eager visible cs' E R FULL model TB HC Hec H17 H12 H13 Hflags H14 H15 Hkind Hkfog Hvisible HFA Hbud HC0 Hrf Hholes Hylo Hn HK.
  destruct (AsanNodesMmLib.is_ecall_at_sound SEGS cs Hec) as (w & Hf & He & Hp0 & Hp4).
  assert (Hbudget : eager = true -> a_eager cs + a_abytes cs + nhi <= LIMIT).
  { intros ->. cbn in Hbud. unfold budget_ok in Hbud. apply Z.leb_le in Hbud. exact Hbud. }
  unfold mmap_fixed_grant in Hn.
  (* [comment removed for export] *)
  destruct (reg_lit_sound' E cs R FULL model 17 222 HC ltac:(lia) H17) as [R17 _].
  destruct (reg_lit_sound' E cs R FULL model 12 _ HC ltac:(lia) H12) as [R12 _].
  destruct (reg_lit_sound' E cs R FULL model 13 _ HC ltac:(lia) H13) as [R13 _].
  destruct (reg_lit_sound' E cs R FULL model 14 _ HC ltac:(lia) H14) as [R14 _].
  destruct (reg_lit_sound' E cs R FULL model 15 0 HC ltac:(lia) H15) as [R15 _].
  rewrite <- bv5_17 in R17. rewrite <- bv5_12 in R12. rewrite <- bv5_13 in R13.
  rewrite <- bv5_14 in R14. rewrite <- bv5_15 in R15. rewrite (Z_to_bv64_m1 _ eq_refl) in R14.
  destruct (fixed_args_sound E cs R FULL model true CEIL b off ne nlo nhi HC HFA) as (Hsp & HML & _).
  destruct (mmap_len_sound E cs R FULL model ne nlo nhi HC HML) as (R11 & Hlen & _).
  change (Z_to_bv 5 11) with (Z_to_bv 5 (Z.of_nat 11)) in R11. rewrite <- bv5_11 in R11.
  set (len := bv_unsigned (edenot E (reg cs 11))) in *. set (nZ := page_round_up_Z len) in *.
  set (n := Z_to_bv 64 nZ) in *. set (addr := edenot E (reg cs 10)) in *.
  pose proof (co_halt _ _ _ _ _ _ _ _ _ _ _ HC) as Hhalt.
  pose proof (proj2 (proj2 (proj2 (co_wf _ _ _ _ _ _ _ _ _ _ _ HC)))) as Hisp.
  (* [comment removed for export] *)
  destruct (fixed_pre cs true CEIL b off ne nlo nhi E R FULL model HC HFA ltac:(unfold CEIL, TOPMAX; lia))
    as (HneE & Un & Hest & Hal & Hpos & Himg & HtopA & R10 & HnZal & HnZ).
  fold len nZ n addr in HneE, Un, Hest, Hal, Hpos, Himg, HtopA, R10, HnZal, HnZ.
  assert (HaK : bv_unsigned addr + nZ <= CEIL) by lia.
  rewrite <- bv5_10 in R10.
  assert (Hce : bv_unsigned addr + page_round_up_Z len <= alloc_ceiling) by (rewrite CEIL_eq; fold nZ; lia).
  (* [comment removed for export] *)
  assert (CONT : forall model' FULL',
            grant_post kd addr n model model' -> grant_mem kd addr n FULL FULL' -> m_fs model' = m_fs model ->
            RZ (mkCfg (mkst (regupd R 10 addr) (v_addi (Z_to_bv 64 (pc cs)) 4) FULL' (seg_rom SEGS)) model') TB).
  { intros model' FULL' GPo GM Hfs.
    destruct (mmap_fixed_grant_cs1 cs ms0 kd eager CEIL b off ne nlo nhi E R FULL model model' FULL' HC HFA ltac:(lia) HC0 Hrf Hholes Hylo Hbudget Hkind Hkfog GPo GM) as (HC1 & NEW).
    fold len nZ n addr in HC1, NEW.
    rewrite (AsanNodesMmLib.v_addi_pc (pc cs) Hp0 Hp4). rewrite bv5_10.
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
  destruct kd; cbn [kind_none kind_lazy negb orb] in *; [| | | | discriminate Hkfog | discriminate Hkfog | ].   (* [comment removed for export] *)
  - (* [comment removed for export] *)
    destruct eager; [|discriminate]. destruct Hflags as [[_ ->]|[X _]]; [|discriminate X].
    eapply (crz_mmap_fixed_rw_free1 SC SEGS ALLOC_OFF R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w addr len (Z_to_bv 64 50) TB
              Hf He Hhalt R17 R10 Hal Hpos R11 ltac:(lia) Hce Hisp R12 R13 mmap_flags_core_32 R14 R15 Hrf).
    + unfold mmap_noreserve_backed_ok. rewrite mmap_noreserve_b_32. apply Z.leb_le. cbn in Hbud.
      eapply Z.le_trans; [|eapply (budget_slack E cs R FULL model nhi HC Hbud)]. fold nZ. lia.
    + rewrite with_mmap_backing_plain by apply mmap_noreserve_b_32.
      apply CONT; [constructor; reflexivity | | reflexivity].
      split; [intros x Hx; apply zfill_out; exact Hx | intros x Hx; apply zfill_in; exact Hx].
  - (* [comment removed for export] *)
    destruct eager; [discriminate|]. destruct Hflags as [[X _]|[_ [-> | ->]]]; [discriminate X| |].
    + eapply (crz_mmap_fixed_rw_free1 SC SEGS ALLOC_OFF R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w addr len (Z_to_bv 64 16434) TB
                Hf He Hhalt R17 R10 Hal Hpos R11 ltac:(lia) Hce Hisp R12 R13 mmap_flags_core_4032 R14 R15 Hrf).
      * unfold mmap_noreserve_backed_ok. rewrite mmap_noreserve_b_4032. reflexivity.
      * rewrite with_mmap_backing_lazy by apply mmap_noreserve_b_4032.
        fold nZ. fold n. apply CONT; [| | reflexivity].
        -- constructor; try reflexivity.
           unfold vm_add_lazy. rewrite m_vm_lazy_with_vm_backing.
           rewrite lazy_interior_fresh; [reflexivity | exact Hal | rewrite Un; exact HnZal | rewrite Un; lia | rewrite Un; unfold CEIL in HaK; lia].
        -- split; [intros x Hx; apply zfill_out; exact Hx | intros x Hx; apply zfill_in; exact Hx].
    + eapply (crz_mmap_noreplace_rw1 SC SEGS ALLOC_OFF R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w addr len (Z_to_bv 64 1064994) TB
                Hf He Hhalt R17 R10 Hal Hpos R11 ltac:(lia) Hce Hisp R12 R13 mmap_flags_core_104022 R14 R15 Hrf).
      * unfold mmap_noreserve_backed_ok. rewrite mmap_noreserve_b_104022. reflexivity.
      * rewrite with_mmap_backing_lazy by apply mmap_noreserve_b_104022.
        fold nZ. fold n. apply CONT; [| | reflexivity].
        -- constructor; try reflexivity.
           unfold vm_add_lazy. rewrite m_vm_lazy_with_vm_backing.
           rewrite lazy_interior_fresh; [reflexivity | exact Hal | rewrite Un; exact HnZal | rewrite Un; lia | rewrite Un; unfold CEIL in HaK; lia].
        -- split; [intros x Hx; apply zfill_out; exact Hx | intros x Hx; apply zfill_in; exact Hx].
  - (* [comment removed for export] *)
    destruct eager; [discriminate|]. destruct Hflags as [[_ ->]|[X _]]; [|discriminate X].
    eapply (crz_mmap_fixed_none_free1 SC SEGS ALLOC_OFF R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w addr len (Z_to_bv 64 50) TB
              Hf He Hhalt R17 R10 Hal Hpos R11 ltac:(lia) Hce Hisp R12 R13 mmap_flags_core_32 R14 R15 Hrf).
    rewrite with_mmap_backing_plain by apply mmap_noreserve_b_32.
    apply CONT; [constructor; reflexivity | | reflexivity].
    split; [intros x Hx; apply unfill_out; exact Hx | intros x Hx; apply unfill_in; exact Hx].
  - (* [comment removed for export] *)
    destruct eager; [discriminate|]. destruct Hflags as [[X _]|[_ [-> | ->]]]; [discriminate X| |].
    + eapply (crz_mmap_fixed_none_free1 SC SEGS ALLOC_OFF R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w addr len (Z_to_bv 64 16434) TB
                Hf He Hhalt R17 R10 Hal Hpos R11 ltac:(lia) Hce Hisp R12 R13 mmap_flags_core_4032 R14 R15 Hrf).
      rewrite with_mmap_backing_lazy by apply mmap_noreserve_b_4032.
      fold nZ. fold n. apply CONT; [| | reflexivity].
      * constructor; try reflexivity.
        unfold vm_add_lazy. rewrite m_vm_lazy_with_vm_backing.
        rewrite lazy_interior_fresh; [reflexivity | exact Hal | rewrite Un; exact HnZal | rewrite Un; lia | rewrite Un; unfold CEIL in HaK; lia].
      * split; [intros x Hx; apply unfill_out; exact Hx | intros x Hx; apply unfill_in; exact Hx].
    + eapply (crz_mmap_noreplace_none1 SC SEGS ALLOC_OFF R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w addr len (Z_to_bv 64 1064994) TB
                Hf He Hhalt R17 R10 Hal Hpos R11 ltac:(lia) Hce Hisp R12 R13 mmap_flags_core_104022 R14 R15 Hrf).
      rewrite with_mmap_backing_lazy by apply mmap_noreserve_b_104022.
      fold nZ. fold n. apply CONT; [| | reflexivity].
      * constructor; try reflexivity.
        unfold vm_add_lazy. rewrite m_vm_lazy_with_vm_backing.
        rewrite lazy_interior_fresh; [reflexivity | exact Hal | rewrite Un; exact HnZal | rewrite Un; lia | rewrite Un; unfold CEIL in HaK; lia].
      * split; [intros x Hx; apply unfill_out; exact Hx | intros x Hx; apply unfill_in; exact Hx].
  - (* [comment removed for export] *)
    destruct eager; [|discriminate]. destruct Hflags as [[_ ->]|[X _]]; [|discriminate X].
    eapply (crz_mmap_fixed_rw_free1 SC SEGS ALLOC_OFF R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w addr len (Z_to_bv 64 50) TB
              Hf He Hhalt R17 R10 Hal Hpos R11 ltac:(lia) Hce Hisp R12 R13 mmap_flags_core_32 R14 R15 Hrf).
    + unfold mmap_noreserve_backed_ok. rewrite mmap_noreserve_b_32. apply Z.leb_le. cbn in Hbud.
      eapply Z.le_trans; [|eapply (budget_slack E cs R FULL model nhi HC Hbud)]. fold nZ. lia.
    + rewrite with_mmap_backing_plain by apply mmap_noreserve_b_32.
      apply CONT; [constructor; reflexivity | | reflexivity].
      split; [intros x Hx; apply zfill_out; exact Hx | intros x Hx; apply zfill_in; exact Hx].
Qed.

Lemma mmap_fixed_free_sound1 : forall cs kd (flags : Z) (eager visible : bool) cs' E R FULL model TB,
  CSOK E cs R FULL model -> is_ecall_at SEGS cs = true ->
  reg_lit cs 17 = Some 222 ->
  reg_lit cs 12 = Some (if kind_none kd then 0 else 3) ->
  reg_lit cs 13 = Some flags ->
  ((kind_lazy kd = false /\ flags = 50) \/ (kind_lazy kd = true /\ (flags = 16434 \/ flags = 1064994))) ->
  reg_lit cs 14 = Some (two64 - 1) -> reg_lit cs 15 = Some 0 ->
  (kind_none kd || kind_lazy kd = negb eager)%bool -> is_tok_kind kd = false ->
  visible = eager ->
  mmap_fixed_free A LIMIT cs kd eager visible = Some cs' ->
  (forall E' R' FULL' model', env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> CSOK E' cs' R' FULL' model' -> m_fs model' = m_fs model ->
      RZ (cfg R' (pc cs') FULL' model') TB) ->
  RZ (cfg R (pc cs) FULL model) TB.
Proof.
  intros cs kd flags eager visible cs' E R FULL model TB HC Hec H17 H12 H13 Hflags H14 H15 Hkind Hkfog Hvisible Hn HK.
  unfold mmap_fixed_free in Hn.
  destruct (fixed_args A cs true CEIL) as [[[[[b off] ne] nlo] nhi]|] eqn:HFA; [|discriminate].
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
  apply andb_prop in Hcond as [Hcond Hylo]. apply andb_prop in Hcond as [Hcond Hav]. apply andb_prop in Hcond as [Hcond Hnev].
  apply andb_prop in Hcond as [Hcond Hbud]. apply andb_prop in Hcond as [Hnf Hall]. apply Z.leb_le in Hylo.
  destruct (mmap_fixed_old_facts cs b off ne nlo nhi E R FULL model HC HFA Hnf Hall) as (HC0 & Hrf & Hholes).
  eapply (mmap_fixed_grant_sound1 cs (a_maps cs) b off ne nlo nhi kd flags eager visible cs' E R FULL model TB
            HC Hec H17 H12 H13 Hflags H14 H15 Hkind Hkfog Hvisible HFA Hbud HC0 Hrf Hholes Hylo Hn HK).
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma node_mprotect_sound1 : forall cs cs' E R FULL model TB,
  CSOK E cs R FULL model -> is_ecall_at SEGS cs = true ->
  node_mprotect A LIMIT cs = Some cs' ->
  (forall E' R' FULL' model', env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> CSOK E' cs' R' FULL' model' -> m_fs model' = m_fs model ->
      RZ (cfg R' (pc cs') FULL' model') TB) ->
  RZ (cfg R (pc cs) FULL model) TB.
Proof.
  intros cs cs' E R FULL model TB HC Hec Hn HK.
  destruct (AsanNodesMmLib.is_ecall_at_sound SEGS cs Hec) as (w & Hf & He & Hp0 & Hp4).
  rewrite node_mprotect_eq in Hn. (* [comment removed for export] *) unfold node_mprotect_ref in Hn.
  destruct (reg_lit cs 17) as [z17|] eqn:H17; [|discriminate].
  destruct (reg_lit cs 12) as [z12|] eqn:H12.
  2: { repeat match type of Hn with context [match ?x with _ => _ end] => destruct x; try discriminate end. }
  destruct (fixed_args A cs false TOPMAX) as [[[[[b off] ne] nlo] nhi]|] eqn:HFA.
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
    as (Hm & [Hkind Hnf] & R10 & R11 & Hlen & Hne & Un & HnZpos & HnZ & HnZal & Hal & Hpos & Himg & Hest & Hin1 & Hin2 & HmC & Hmc & Hrfres & Hov).
  rewrite <- bv5_10 in R10. rewrite <- bv5_11 in R11.
  set (len := bv_unsigned (edenot E (reg cs 11))) in *. set (nZ := page_round_up_Z len) in *.
  set (n := Z_to_bv 64 nZ) in *. set (addr := edenot E (reg cs 10)) in *.
  pose proof (co_halt _ _ _ _ _ _ _ _ _ _ _ HC) as Hhalt. pose proof (co_wf _ _ _ _ _ _ _ _ _ _ _ HC) as Hwf.
  pose proof (cs_top _ _ _ _ _ HC) as (T1 & T2 & T3).
  pose proof (u64_range addr) as Ra.
  assert (Hkind' : am_kind m = KNONE \/ am_kind m = KNONELAZY) by (cbn in Hkind; destruct Hkind as [<-|[<-|[]]]; auto).
  (* [comment removed for export] *)
  assert (Hna : map_contains (vm_noaccess (m_vmmaps model)) addr n = true).
  { pose proof (proj1 (Forall_forall _ _) (co_none _ _ _ _ _ _ _ _ _ _ _ HC) m Hm Hkind') as X.
    eapply map_contains_intro; [exact X | exact Hin1 | rewrite Un; exact Hin2]. }
  unfold cfg_of.
  eapply (crz_mprotect1 SC SEGS ALLOC_OFF R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w addr len TB Hf He Hhalt R17 R10 Hal R11 ltac:(lia)).
  - unfold two_pow_64. fold nZ. unfold TOPMAX in *. lia.
  - exact R12.
  - exact Hna.
  - exact Hmc.
  - apply mprotect_budget_ok_intro_gen; [exact Hwf|]. pose proof (budget_slack E cs R FULL model nhi HC ltac:(unfold budget_ok; apply Z.leb_le; exact Hbud)). fold nZ n. lia.
  - fold nZ. fold n.
    set (model' := mprotect_model addr n model). set (FULL' := zfill addr n FULL).
    assert (SPo : slice_post SlM addr n model model') by (constructor; reflexivity).
    assert (SM : slice_mem SlM addr n FULL FULL').
    { split; [intros x Hx; apply zfill_out; exact Hx | intros x Hx; apply zfill_in; exact Hx]. }
    assert (SH : slice_hyps SEGS A LIMIT SINV argH FS0 E cs R FULL model SlM m addr n nZ model' FULL').
    { constructor; try assumption; intros HH; [discriminate HH|]. intros Hk. rewrite Hk in Hkind'. destruct Hkind'; discriminate. }
    rewrite (AsanNodesMmLib.v_addi_pc (pc cs) Hp0 Hp4).
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
    pose proof (slice_cs1_ok E cs R FULL model SlM m addr n nZ model' FULL' SH _ _ _ (pc cs + 4) (s_next (a_ss cs)) nhi Hregs' Hk' HnZ ltac:(intros _; exact Hbud)) as HC1.
    cbn [sl_charge] in HC1.
    eapply (vis_add_slice_ok E _ cs' (reg cs 10) b off ne _ FULL' model' (bv_unsigned addr) nZ HC1).
    + exact Hn.
    + cbn [kn a_ss s_know mk_ss]. apply kimg_clip_in_hull'.
    + reflexivity.
    + exact Hest.
    + unfold elenZ. rewrite Hne. exact Un.
    + lia.
    + lia.
    + unfold TOPMAX in *. lia.
    + intros x Hx. rewrite (sp_maps _ _ _ _ _ SPo).
      split; [exact (sl_in_maps E cs R FULL model SlM m addr n nZ model' FULL' SH x Hx) |].
      split; [exact (sl_noacc_in E cs R FULL model SlM m addr n nZ model' FULL' SH x Hx) |].
      split; [destruct (argH E x) eqn:Ea; [pose proof (cs_argH_top _ _ _ _ _ x HC Ea); lia | reflexivity]|].
      rewrite (proj2 SM x) by (rewrite Un; exact Hx). reflexivity.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

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

Theorem node_mmapG_sound : mm1_stmt SEGS SC A nx0 LIMIT SINV argH FS0 (node_mmapG A nx0 LIMIT).
Proof.
  intros cs csb E R FULL model TB HC Hec Hn HKB.
  unfold node_mmapG in Hn.
  destruct (mmap_gate cs) as [[[prot flags] isnull]|] eqn:Hg; [|discriminate].
  destruct (mmap_gate_sound cs prot flags isnull Hg) as (H17 & H12 & H13 & H14 & H15 & H10).
  destruct isnull.
  - specialize (H10 eq_refl).
    assert (ARMS : (prot = 3 /\ flags = 34 /\ mmap_null A nx0 LIMIT cs KRW true true = Some csb)
                   \/ (prot = 3 /\ flags = 16418 /\ mmap_null A nx0 LIMIT cs KRWLAZY false true = Some csb)
                   \/ (prot = 0 /\ flags = 34 /\ mmap_null A nx0 LIMIT cs KNONE false false = Some csb)
                   \/ (prot = 0 /\ flags = 16418 /\ mmap_null A nx0 LIMIT cs KNONELAZY false false = Some csb)).
    { repeat match type of Hn with context [match ?x with _ => _ end] => destruct x; try discriminate end; tauto. }
    destruct ARMS as [(-> & -> & Hm)|[(-> & -> & Hm)|[(-> & -> & Hm)|(-> & -> & Hm)]]].
    + eapply (mmap_null_sound1 cs KRW true true); eauto; reflexivity.
    + eapply (mmap_null_sound1 cs KRWLAZY false true); eauto; reflexivity.
    + eapply (mmap_null_sound1 cs KNONE false false); eauto; reflexivity.
    + eapply (mmap_null_sound1 cs KNONELAZY false false); eauto; reflexivity.
  - assert (ARMS : (prot = 3 /\ flags = 16434 /\ mmap_fixed_free A LIMIT cs KRWLAZY false false = Some csb)
                   \/ (prot = 3 /\ flags = 50 /\ mmap_fixed_free A LIMIT cs KRW true true = Some csb)
                   \/ (prot = 0 /\ flags = 16434 /\ mmap_fixed_free A LIMIT cs KNONELAZY false false = Some csb)
                   \/ (prot = 0 /\ flags = 50 /\ mmap_fixed_free A LIMIT cs KNONE false false = Some csb)
                   \/ (prot = 3 /\ flags = 1064994 /\ mmap_fixed_free A LIMIT cs KRWLAZY false false = Some csb)
                   \/ (prot = 0 /\ flags = 1064994 /\ mmap_fixed_free A LIMIT cs KNONELAZY false false = Some csb)).
    { repeat match type of Hn with context [match ?x with _ => _ end] => destruct x; try discriminate end; tauto. }
    destruct ARMS as [(-> & -> & Hm)|[(-> & -> & Hm)|[(-> & -> & Hm)|[(-> & -> & Hm)|[(-> & -> & Hm)|(-> & -> & Hm)]]]]].
    + eapply (mmap_fixed_free_sound1 cs KRWLAZY 16434 false false); eauto; cbn; auto.
    + eapply (mmap_fixed_free_sound1 cs KRW 50 true true); eauto; cbn; auto.
    + eapply (mmap_fixed_free_sound1 cs KNONELAZY 16434 false false); eauto; cbn; auto.
    + eapply (mmap_fixed_free_sound1 cs KNONE 50 false false); eauto; cbn; auto.
    + eapply (mmap_fixed_free_sound1 cs KRWLAZY 1064994 false false); eauto; cbn; auto.
    + eapply (mmap_fixed_free_sound1 cs KNONELAZY 1064994 false false); eauto; cbn; auto.
Qed.

Theorem node_mprotect_sound : mm1_stmt SEGS SC A nx0 LIMIT SINV argH FS0 (node_mprotect A LIMIT).
Proof.
  intros cs csb E R FULL model TB HC Hec Hn HKB. eapply node_mprotect_sound1; eauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

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
      RZ (cfg R' (pc csO) FULL' model') TB) ->
  RZ (cfg R (pc cs) FULL model) TB.
Proof.
  intros cs arm b off ne nlo nhi m csO E R FULL model TB HC Hec H17 H12 H13 H14 H15 HFI Hn HKB.
  destruct (AsanNodesMmLib.is_ecall_at_sound SEGS cs Hec) as (w & Hf & He & Hp0 & Hp4).
  (* [comment removed for export] *)
  rewrite fixed_in_args_eq in HFI. (* [comment removed for export] *) unfold fixed_in_args_ref in HFI.
  destruct (fixed_args A cs false TOPMAX) as [[[[[b0 off0] ne0] nlo0] nhi0]|] eqn:HFA; [|discriminate].
  destruct (find_containing (kn cs) (a_maps cs) _ b0 off0 ne0) as [m0|] eqn:Hfind; [|discriminate].
  match type of HFI with (if ?c then _ else _) = _ => destruct c eqn:Hvars; [|discriminate] end.
  injection HFI as -> -> -> -> -> ->.
  rewrite mmap_fixed_in_eq in Hn. (* [comment removed for export] *) unfold mmap_fixed_in_ref in Hn. rewrite fixed_in_args_eq in Hn. unfold fixed_in_args_ref in Hn. rewrite HFA, Hfind, Hvars in Hn.
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hbud; [|discriminate] end.
  destruct (reg_lit_sound' E cs R FULL model 17 222 HC ltac:(lia) H17) as [R17 _].
  destruct (reg_lit_sound' E cs R FULL model 12 _ HC ltac:(lia) H12) as [R12 _].
  destruct (reg_lit_sound' E cs R FULL model 13 _ HC ltac:(lia) H13) as [R13 _].
  destruct (reg_lit_sound' E cs R FULL model 14 _ HC ltac:(lia) H14) as [R14 _].
  destruct (reg_lit_sound' E cs R FULL model 15 0 HC ltac:(lia) H15) as [R15 _].
  rewrite <- bv5_17 in R17. rewrite <- bv5_12 in R12. rewrite <- bv5_13 in R13.
  rewrite <- bv5_14 in R14. rewrite <- bv5_15 in R15. rewrite (Z_to_bv64_m1 _ eq_refl) in R14.
  destruct (slice_args E cs R FULL model b off ne nlo nhi _ m HC HFA Hfind)
    as (Hm & [Hkind Hnf] & R10 & R11 & Hlen & Hne & Un & HnZpos & HnZ & HnZal & Hal & Hpos & Himg & Hest & Hin1 & Hin2 & HmC & Hmc & Hrfres & Hov).
  rewrite <- bv5_10 in R10. rewrite <- bv5_11 in R11.
  set (len := bv_unsigned (edenot E (reg cs 11))) in *. set (nZ := page_round_up_Z len) in *.
  set (n := Z_to_bv 64 nZ) in *. set (addr := edenot E (reg cs 10)) in *.
  pose proof (co_halt _ _ _ _ _ _ _ _ _ _ _ HC) as Hhalt. pose proof (co_wf _ _ _ _ _ _ _ _ _ _ _ HC) as Hwf.
  pose proof (cs_top _ _ _ _ _ HC) as (T1 & T2 & T3).
  pose proof (u64_range addr) as Ra.
  assert (Htop : bv_unsigned addr + page_round_up_Z len <= alloc_top (m_vmmaps model)) by (fold nZ; lia).
  assert (HF : slarm_of arm = SlF -> am_kind m = KRWLAZY).
  { intros Hs. destruct arm; try discriminate. cbn in Hkind. destruct Hkind as [<-|[]]. reflexivity. }
  assert (HnF : slarm_of arm <> SlF -> am_kind m <> KRWLAZY).
  { intros Hs Hk. destruct arm; [|exact (Hs eq_refl)|]; cbn in Hkind; rewrite Hk in Hkind; destruct Hkind as [|[|[|[|[]]]]]; discriminate. }   (* [comment removed for export] *)
  set (prot := match arm with ArmG => 0 | _ => 3 end) in *.
  set (flg := match arm with ArmF => 16434 | _ => 50 end) in *.
  assert (Hprot : prot = 0 \/ prot = 3) by (destruct arm; cbn; lia).
  assert (Hcore : mmap_flags_core (Z_to_bv 64 flg) = 50) by (destruct arm; [apply mmap_flags_core_32 | apply mmap_flags_core_4032 | apply mmap_flags_core_32]).
  (* [comment removed for export] *)
  assert (CONTB : forall model' FULL',
            slice_post (slarm_of arm) addr n model model' -> slice_mem (slarm_of arm) addr n FULL FULL' -> m_fs model' = m_fs model ->
            RZ (mkCfg (mkst (regupd R 10 addr) (v_addi (Z_to_bv 64 (pc cs)) 4) FULL' (seg_rom SEGS)) model') TB).
  { intros model' FULL' SPo SM Hfs.
    assert (SH : slice_hyps SEGS A LIMIT SINV argH FS0 E cs R FULL model (slarm_of arm) m addr n nZ model' FULL') by (constructor; assumption).
    rewrite (AsanNodesMmLib.v_addi_pc (pc cs) Hp0 Hp4). rewrite bv5_10.
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
    assert (Himg' : estart E (SA b off) + elenZ E ne <= img_lo A \/ img_hi A <= estart E (SA b off)).
    { rewrite Hest. unfold elenZ. rewrite Hne, Un. exact Himg. }
    pose proof (slice_cs1_ok E cs R FULL model (slarm_of arm) m addr n nZ model' FULL' SH (s_regs (a_ss cs)) (regupd R (Z_to_bv 5 (Z.of_nat 10)) addr)) as CS1.
    destruct arm; cbn [slarm_of sl_charge] in *.
    - (* [comment removed for export] *)
      assert (Hk' : know_ok SEGS E (MR E cs model' FULL') (kimg_clip A (kn_unfill (kn cs) b off ne))).
      { eapply kn_unfill_clip_ok; [exact (co_know _ _ _ _ _ _ _ _ _ _ _ HC) | exact Himg' | exact MROUT']. }
      unfold budget_ok in Hbud. apply Z.leb_le in Hbud.
      pose proof (CS1 _ (pc cs + 4) (s_next (a_ss cs)) nhi Hregs' Hk' HnZ ltac:(intros _; exact Hbud)) as HC1.
      eapply (vis_add_slice_ok E _ csO (reg cs 10) b off ne _ FULL' model' (bv_unsigned addr) nZ HC1).
      + exact Hn.
      + cbn [kn a_ss s_know mk_ss]. apply kimg_clip_in_hull'.
      + reflexivity.
      + exact Hest.
      + unfold elenZ. rewrite Hne. exact Un.
      + lia.
      + lia.
      + unfold TOPMAX in *. lia.
      + intros x Hx. rewrite (sp_maps _ _ _ _ _ SPo).
        split; [exact (sl_in_maps E cs R FULL model SlE m addr n nZ model' FULL' SH x Hx) |].
        split; [exact (sl_noacc_in E cs R FULL model SlE m addr n nZ model' FULL' SH x Hx) |].
        split; [destruct (argH E x) eqn:Ea; [pose proof (cs_argH_top _ _ _ _ _ x HC Ea); lia | reflexivity]|].
        rewrite (proj2 SM x) by (rewrite Un; exact Hx). reflexivity.
    - (* [comment removed for export] *)
      assert (Hk' : know_ok SEGS E (MR E cs model' FULL') (kimg_clip A (kn_rezero (kn cs) b off ne))).
      { eapply kn_rezero_clip_ok; [exact (co_know _ _ _ _ _ _ _ _ _ _ _ HC) | exact Himg' | exact MROUT' |].
        intros x Hx Hdef. rewrite Hest in Hx. unfold elenZ in Hx. rewrite Hne, Un in Hx.
        unfold Mr, mrestrict, hid in Hdef |- *.
        rewrite (sl_vis_in_F E cs R FULL model SlF m addr n nZ model' FULL' SH eq_refl cs x eq_refl Hx).
        destruct (argH E x); [exfalso; apply Hdef; reflexivity|]. cbn [orb] in *.
        destruct (VIS E cs model x); [|exfalso; apply Hdef; reflexivity]. cbn [negb].
        rewrite (proj2 SM x) by (rewrite Un; exact Hx). reflexivity. }
      injection Hn as <-. exact (CS1 _ (pc cs + 4) (s_next (a_ss cs)) nhi Hregs' Hk' HnZ ltac:(intros HH; discriminate HH)).
    - (* [comment removed for export] *)
      assert (Hk' : know_ok SEGS E (MR E cs model' FULL') (kimg_clip A (kn_cutout (kn cs) b off ne))).
      { apply know_ok_filter. eapply (APS.know_ok_cutout SEGS); [exact (co_know _ _ _ _ _ _ _ _ _ _ _ HC) | exact MROUT']. }
      injection Hn as <-. exact (CS1 _ (pc cs + 4) (s_next (a_ss cs)) nhi Hregs' Hk' HnZ ltac:(intros HH; discriminate HH)). }
  (* [comment removed for export] *)
  unfold cfg_of.
  assert (R12' : getr R 12 = Z_to_bv 64 prot) by (destruct arm; exact R12).
  assert (R13' : getr R 13 = Z_to_bv 64 flg) by (destruct arm; exact R13).
  eapply (crz_mmap_fixedin1_top SC SEGS ALLOC_OFF R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w prot (Z_to_bv 64 flg) addr len TB
            Hf He Hhalt R17 Hprot Hcore R10 Hal Hpos R11 ltac:(lia) Htop R12' R13' R14 R15 Hrfres Hmc).
  - (* [comment removed for export] *) intros Hp3. fold nZ n. destruct arm; cbn in Hp3; try discriminate Hp3; subst flg.
    + apply mmap_fixed_rw_budget_ok_commit_intro; [apply mmap_noreserve_b_32 | exact Hwf |].
      unfold budget_ok in Hbud. pose proof (budget_slack E cs R FULL model nhi HC Hbud). lia.
    + apply mmap_fixed_rw_budget_ok_recommit_intro; [apply mmap_noreserve_b_4032 | exact Hwf | exact Hal | unfold page_size; rewrite Un; exact HnZal | rewrite Un; lia | rewrite Un; unfold TOPMAX in *; lia |].
      eapply vm_backing_used_limit; [exact (co_minv _ _ _ _ _ _ _ _ _ _ _ HC) | apply A_wf_allowA'].
  - fold nZ. fold n. destruct arm; subst prot flg; cbn [Z.eqb slarm_of] in CONTB |- *.
    + (* [comment removed for export] *) unfold fixedin_ok_model, with_mmap_replacement. rewrite with_mmap_backing_plain by apply mmap_noreserve_b_32.
      apply CONTB; [| | reflexivity].
      * constructor; reflexivity.
      * split; [intros x Hx; apply zfill_out; exact Hx | intros x Hx; apply zfill_in; exact Hx].
    + (* [comment removed for export] *) unfold fixedin_ok_model, with_mmap_replacement. rewrite with_mmap_backing_lazy by apply mmap_noreserve_b_4032.
      apply CONTB; [| | reflexivity].
      * constructor; try reflexivity.
        unfold vm_add_lazy. rewrite m_vm_lazy_with_vm_backing, m_vm_lazy_vm_forget_range.
        rewrite lazy_interior_fresh; [reflexivity | exact Hal | rewrite Un; exact HnZal | rewrite Un; lia | rewrite Un; unfold TOPMAX in *; lia].
      * split; [intros x Hx; apply zfill_out; exact Hx | intros x Hx; apply zfill_in; exact Hx].
    + (* [comment removed for export] *) unfold fixedin_ok_model, with_mmap_replacement. rewrite with_mmap_backing_plain by apply mmap_noreserve_b_32.
      apply CONTB; [| | reflexivity].
      * constructor; reflexivity.
      * split; [intros x Hx; apply unfill_out; exact Hx | intros x Hx; apply unfill_in; exact Hx].
Qed.

Theorem node_mmapin_sound : mm1_stmt SEGS SC A nx0 LIMIT SINV argH FS0 (node_mmapin A LIMIT).
Proof.
  intros cs csb E R FULL model TB HC Hec Hn HKB.
  unfold node_mmapin in Hn.
  destruct (mmap_gate cs) as [[[prot flags] isnull]|] eqn:Hg; [|discriminate].
  destruct (mmap_gate_sound cs prot flags isnull Hg) as (H17 & H12 & H13 & H14 & H15 & _).
  destruct isnull; [discriminate|]. cbv zeta in Hn.
  assert (CASES : forall arm,
     reg_lit cs 12 = Some (match arm with ArmG => 0 | _ => 3 end) ->
     reg_lit cs 13 = Some (match arm with ArmF => 16434 | _ => 50 end) ->
     mmap_fixed_in A LIMIT cs arm = Some csb ->
     RZ (cfg R (pc cs) FULL model) TB).
  { intros arm H12' H13' Hn'.
    destruct (fixed_in_args A cs arm) as [[[[[[b off] ne] nlo] nhi] m]|] eqn:HFI.
    2: { exfalso. revert Hn'. rewrite mmap_fixed_in_eq. unfold mmap_fixed_in_ref. rewrite HFI. discriminate. }
    eapply (mmap_fixed_in_sound1 cs arm b off ne nlo nhi m csb); eauto. }
  destruct prot as [|p|p]; try discriminate Hn; try (repeat (destruct p as [p|p|]; try discriminate Hn));
  destruct flags as [|q|q]; try discriminate Hn; try (repeat (destruct q as [q|q|]; try discriminate Hn));
  refine (CASES _ _ _ Hn); first [exact H12 | exact H13].
Qed.

End Nodes.
