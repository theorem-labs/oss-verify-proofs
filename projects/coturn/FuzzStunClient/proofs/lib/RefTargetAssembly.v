(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.coturn.FuzzStunClient.images Require Import Plain.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec ShapeAlg.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import ItabFast.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Spec TargetSpec TargetKDefs FContract
  RefWorld RefTargetPre RefWorldK RefTargetPreK
  SymExec3 SymExec3Sound SymRun3 SymDrive3 SymPlan SymSlots SymPlanSoundA SymPlanSound SymPlanStmts
  RefATB RefImgHyps SymPlanSoundF
  RefTargetEntry_defs RefTargetEntry RefTargetEntryK_defs RefTargetEntryK TargetShape TargetShapeTop.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFast.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastK.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastM.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import SumWalkFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.gres ::= gres_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.vnorm ::= vnorm_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StepTac.step_simpl ::= step_simpl_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.RefMemcpyLib.not_kept ::= not_kept_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StoreOk.store_ok_peel ::= store_ok_peel_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.SumWalkTac.rdn_peel1 ::= rdn_peel1_fast.
(* [comment removed for export] *)
Unset Lia Cache.
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Import SX2. Import SX2S. Import SP. Import SPSA. Import SPS.
Open Scope Z_scope.

#[local] Abbreviation RSEGS := Plain.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Record ref_tphase_hyps : Prop := RTH {
  rth_cas_or   : cas_or_stmt RSEGS (t_cas_or REF_ATB) (t_cas_or_k REF_ATB);
  rth_cas_and  : cas_and_stmt RSEGS (t_cas_and REF_ATB) (t_cas_and_k REF_ATB);
  rth_cas_lock : cas_lock_stmt RSEGS (t_cas_lock REF_ATB) (t_cas_lock_k REF_ATB);
  rth_memcpy   : memcpy_stmt RSEGS (t_memcpy REF_ATB);
  rth_enframe  : forall nx0, nx0_okP nx0 -> enframe2_sound_stmt RSEGS REF_ATB nx0;
  rth_freepro  : forall nx0, nx0_okP nx0 -> freepro_sound_stmt RSEGS REF_ATB nx0;
  rth_stdio    : forall nx0, nx0_okP nx0 -> stdio_write_sound_stmt RSEGS REF_ATB nx0;
  rth_mainret  : forall nx0, nx0_okP nx0 -> mainret_sound_stmt RSEGS REF_ATB nx0;
  rth_printf   : forall nx0, nx0_okP nx0 -> printf_sound_stmt RSEGS REF_ATB nx0;
  rth_exitcall : exitcall_sound_stmt RSEGS REF_ATB;
  rth_F        : F_contract RSEGS FP_src0
}.

(* [comment removed for export] *)
Lemma npos_class : forall nlo nhi content,
  0 <= nlo -> (nlo = 0 -> nhi = 0) -> nlo <= hdr_paylen content <= nhi ->
  (0 <? nlo) = npos_of content.
Proof.
  intros nlo nhi content H0 Hz Hn. unfold npos_of.
  destruct (Z.ltb_spec 0 nlo); [symmetry; apply Z.ltb_lt; lia|].
  assert (nlo = 0) by lia. specialize (Hz H1). symmetry. apply Z.ltb_ge. lia.
Qed.

(* [comment removed for export] *)
Lemma ITAB_ok : SX2.itab_sound RSEGS ITAB.
Proof. (* [comment removed for export] *)
  apply itab_agrees_sound. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma NX0_ok : nx0_okP NX0.
Proof. unfold nx0_okP, NX0. lia. Qed.
Lemma NX0k_ok : nx0_okP NX0k.
Proof. unfold nx0_okP, NX0k. lia. Qed.

Section WithHyps.
Hypothesis RH : ref_tphase_hyps.

Lemma check_sound_all : forall nx0 fuel bfuel p cs s, nx0_okP nx0 ->
  check RSEGS ITAB REF_ATB nx0 bfuel fuel cs p = COk s ->
  forall E R M model, cs_ok RSEGS E cs R M model ->
  realizes RSEGS (cfg_of RSEGS R (pc cs) M model) (sd E (m_fs model) s).
Proof.
  intros nx0 fuel bfuel p cs s Hnx.
  destruct RH as [Hor Hand Hlock Hmc Hef Hfp Hsw Hmr Hpf Hex HF].
  exact (check_sound RSEGS REF_ATB nx0 ITAB ITAB_ok Hnx H_hull_ref H_res_small_ref H_res_len_ref H_wview_off_ref
           Hor Hand Hlock Hmc (Hef nx0 Hnx) (Hfp nx0 Hnx) (Hsw nx0 Hnx) (call_F_ok nx0 Hnx HF) (Hmr nx0 Hnx) (Hpf nx0 Hnx) Hex
           fuel bfuel p cs s).
Qed.

(* [comment removed for export] *)
Theorem target_class_sound : forall (bfuel fuel : nat) (nlo nhi : Z) (p : plan) (s : shape),
  check RSEGS ITAB REF_ATB NX0 bfuel fuel (cs_T nlo nhi) p = COk s ->
  class_shape_ok (0 <? nlo) s = true ->
  0 <= nlo -> (nlo = 0 -> nhi = 0) ->
  forall (sp0 gm area brkv mas tid : Z) (content : list byte) (R : bvmap 5 word) (M : word -> option byte)
         (VM : VmMaps) (model : Model),
    target_pre sp0 gm area brkv mas tid content R M -> target_vm sp0 gm area VM -> std_model VM model ->
    nlo <= hdr_paylen content <= nhi ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x13cb0) M (seg_rom RSEGS)) model)
             (t_target content (m_fs model)).
Proof.
  intros bfuel fuel nlo nhi p s HC HS H0 Hz sp0 gm area brkv mas tid content R M VM model TP TV [Mf Mv Mh Ml Mm] Hn.
  destruct (target_entry_ok sp0 gm area brkv mas tid content R M VM model nlo nhi TP TV Mf Mv Mh Ml Mm Hn) as (e & c & sv & He & CS).
  eapply rz_conseq.
  - exact (check_sound_all NX0 fuel bfuel p (cs_T nlo nhi) s NX0_ok HC _ R M _ CS).
  - rewrite (npos_class nlo nhi content H0 Hz Hn) in HS.
    apply (class_shape_sound _ (m_fs model) content s); [reflexivity | reflexivity | reflexivity | | exact HS].
    exact (proj1 (tp_len _ _ _ _ _ _ _ _ _ TP)).
Qed.

(* [comment removed for export] *)
Theorem target_class_sound_k : forall (k : Z) (bfuel fuel : nat) (nlo nhi : Z) (p : plan) (s : shape),
  check RSEGS ITAB REF_ATB NX0k bfuel fuel (cs_Tk k nlo nhi) p = COk s ->
  class_shape_ok (0 <? nlo) s = true ->
  0 <= nlo -> (nlo = 0 -> nhi = 0) ->
  forall (sp0 B area brkv mas tid : Z) (content : list byte) (R : bvmap 5 word) (M : word -> option byte)
         (VM : VmMaps) (model : Model),
    target_pre_k k sp0 B area brkv mas tid content R M -> target_vm_k k sp0 B area VM -> std_model VM model ->
    nlo <= hdr_paylen content <= nhi ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x13cb0) M (seg_rom RSEGS)) model)
             (t_target content (m_fs model)).
Proof.
  intros k bfuel fuel nlo nhi p s HC HS H0 Hz sp0 B area brkv mas tid content R M VM model TP TV [Mf Mv Mh Ml Mm] Hn.
  destruct (target_entry_k_ok k sp0 B area brkv mas tid content R M VM model nlo nhi TP TV Mf Mv Mh Ml Mm Hn) as (e & c & sv & He & CS).
  eapply rz_conseq.
  - exact (check_sound_all NX0k fuel bfuel p (cs_Tk k nlo nhi) s NX0k_ok HC _ R M _ CS).
  - rewrite (npos_class nlo nhi content H0 Hz Hn) in HS.
    apply (class_shape_sound _ (m_fs model) content s); [reflexivity | reflexivity | reflexivity | | exact HS].
    exact (tk_len _ _ _ _ _ _ _ _ _ _ TP).
Qed.

(* [comment removed for export] *)
Theorem target_class_sound_top : forall (bfuel fuel : nat) (nlo nhi : Z) (p : plan) (s : shape),
  check RSEGS ITAB REF_ATB NX0 bfuel fuel (cs_T nlo nhi) p = COk s ->
  class_shape_ok0 (0 <? nlo) s = true ->
  65529 <= nlo ->
  forall (sp0 gm area brkv mas tid : Z) (content : list byte) (R : bvmap 5 word) (M : word -> option byte)
         (VM : VmMaps) (model : Model),
    target_pre sp0 gm area brkv mas tid content R M -> target_vm sp0 gm area VM -> std_model VM model ->
    nlo <= hdr_paylen content <= nhi ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x13cb0) M (seg_rom RSEGS)) model)
             (t_target content (m_fs model)).
Proof.
  intros bfuel fuel nlo nhi p s HC HS Htop sp0 gm area brkv mas tid content R M VM model TP TV [Mf Mv Mh Ml Mm] Hn.
  destruct (target_entry_ok sp0 gm area brkv mas tid content R M VM model nlo nhi TP TV Mf Mv Mh Ml Mm Hn) as (e & c & sv & He & CS).
  pose proof (tp_len _ _ _ _ _ _ _ _ _ TP) as HL.
  assert (CR : 0 <= hdr_cfglen content < 32768) by (unfold hdr_cfglen; apply Z.mod_pos_bound; lia).
  assert (C0 : hdr_cfglen content = 0) by (unfold hdr_paylen in Hn; lia).
  eapply rz_conseq.
  - exact (check_sound_all NX0 fuel bfuel p (cs_T nlo nhi) s NX0_ok HC _ R M _ CS).
  - replace (0 <? nlo) with (npos_of content) in HS by (unfold npos_of;
      destruct (Z.ltb_spec 0 nlo); [apply Z.ltb_lt | apply Z.ltb_ge]; lia).
    apply (class_shape_sound0 _ (m_fs model) content s); [reflexivity | reflexivity | reflexivity | exact C0 | lia | exact HS].
Qed.

(* [comment removed for export] *)
Theorem target_class_sound_top_k : forall (k : Z) (bfuel fuel : nat) (nlo nhi : Z) (p : plan) (s : shape),
  check RSEGS ITAB REF_ATB NX0k bfuel fuel (cs_Tk k nlo nhi) p = COk s ->
  class_shape_ok0 (0 <? nlo) s = true ->
  capk k - 7 <= nlo ->
  forall (sp0 B area brkv mas tid : Z) (content : list byte) (R : bvmap 5 word) (M : word -> option byte)
         (VM : VmMaps) (model : Model),
    target_pre_k k sp0 B area brkv mas tid content R M -> target_vm_k k sp0 B area VM -> std_model VM model ->
    nlo <= hdr_paylen content <= nhi ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x13cb0) M (seg_rom RSEGS)) model)
             (t_target content (m_fs model)).
Proof.
  intros k bfuel fuel nlo nhi p s HC HS Htop sp0 B area brkv mas tid content R M VM model TP TV [Mf Mv Mh Ml Mm] Hn.
  destruct (target_entry_k_ok k sp0 B area brkv mas tid content R M VM model nlo nhi TP TV Mf Mv Mh Ml Mm Hn) as (e & c & sv & He & CS).
  pose proof (tk_len _ _ _ _ _ _ _ _ _ _ TP) as HL. pose proof (tk_L _ _ _ _ _ _ _ _ _ _ TP) as HK.
  pose proof (capk_pos (k - 1) ltac:(pose proof (wk_k _ _ _ _ _ _ _ (tk_world _ _ _ _ _ _ _ _ _ _ TP)); lia)) as Hc.
  assert (CR : 0 <= hdr_cfglen content < 32768) by (unfold hdr_cfglen; apply Z.mod_pos_bound; lia).
  assert (C0 : hdr_cfglen content = 0) by (unfold hdr_paylen in Hn; lia).
  eapply rz_conseq.
  - exact (check_sound_all NX0k fuel bfuel p (cs_Tk k nlo nhi) s NX0k_ok HC _ R M _ CS).
  - replace (0 <? nlo) with (npos_of content) in HS by (unfold npos_of;
      destruct (Z.ltb_spec 0 nlo); [apply Z.ltb_lt | apply Z.ltb_ge]; unfold hdr_paylen in *; lia).
    apply (class_shape_sound0 _ (m_fs model) content s); [reflexivity | reflexivity | reflexivity | exact C0 | lia | exact HS].
Qed.

(* [comment removed for export] *)
Theorem target_class_sound_low_k : forall (k : Z) (bfuel fuel : nat) (nlo nhi : Z) (p : plan) (s : shape),
  check RSEGS ITAB REF_ATB NX0k bfuel fuel (cs_Tk k nlo nhi) p = COk s ->
  class_shape_ok1 (0 <? nlo) s = true ->
  nhi + 6 < capk (k - 1) ->
  0 <= nlo -> (nlo = 0 -> nhi = 0) ->
  forall (sp0 B area brkv mas tid : Z) (content : list byte) (R : bvmap 5 word) (M : word -> option byte)
         (VM : VmMaps) (model : Model),
    target_pre_k k sp0 B area brkv mas tid content R M -> target_vm_k k sp0 B area VM -> std_model VM model ->
    nlo <= hdr_paylen content <= nhi ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x13cb0) M (seg_rom RSEGS)) model)
             (t_target content (m_fs model)).
Proof.
  intros k bfuel fuel nlo nhi p s HC HS Hlow H0 Hz sp0 B area brkv mas tid content R M VM model TP TV [Mf Mv Mh Ml Mm] Hn.
  destruct (target_entry_k_ok k sp0 B area brkv mas tid content R M VM model nlo nhi TP TV Mf Mv Mh Ml Mm Hn) as (e & c & sv & He & CS).
  pose proof (tk_len _ _ _ _ _ _ _ _ _ _ TP) as HL. pose proof (tk_L _ _ _ _ _ _ _ _ _ _ TP) as HK.
  assert (C1 : 1 <= hdr_cfglen content) by (unfold hdr_paylen in Hn; lia).
  eapply rz_conseq.
  - exact (check_sound_all NX0k fuel bfuel p (cs_Tk k nlo nhi) s NX0k_ok HC _ R M _ CS).
  - rewrite (npos_class nlo nhi content H0 Hz Hn) in HS.
    apply (class_shape_sound1 _ (m_fs model) content s); [reflexivity | reflexivity | reflexivity | exact C1 | exact HL | exact HS].
Qed.

End WithHyps.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
