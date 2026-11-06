(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgP.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import
  PropExec CatExec ShapeAlg Spec RefWorld RefTargetPre RefWorldK RefTargetPreK
  SymExec3 SymExec3Sound SymRun3 SymDrive3 SymPlan SymSlots SymPlanSoundA SymPlanSound SymPlanSoundH
  SymPlanSoundFP SymPlanSoundEF SymPlanSoundSW SymPlanSoundLib SymPlanSoundMR SymPlanSoundPF SymPlanSoundEX
  RefStdioDefs RefStdioWrite RefMemcpyLib LibIface
  RefTargetEntry_defs RefTargetEntry RefTargetEntryK_defs RefTargetEntryK RefTargetShape.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import SX2. Import SX2S. Import SP. Import SPSA. Import SPS.
Open Scope Z_scope.

#[local] Abbreviation RSEGS := ImgP.M.loaded_segments.
#[local] Existing Instance PropExec.fx0.   (* [comment removed for export] *)

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

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
Lemma ref_stdio_write_ok : ref_stdio_write_stmt.
Proof. exact @ref_stdio_write. Qed.

(* [comment removed for export] *)
Lemma frm_zero_fx0 : LibIface.frm_zero fx0.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma call_inflate_vacuous : forall nx0, inflate_sound_stmt nx0.
Proof. intros nx0 fx cs cs' E R M model T _ Hg. exfalso. cbn in Hg. lia. Qed.
Lemma call_u2tail_vacuous : forall nx0, u2tail_sound_stmt nx0.
Proof. intros nx0 fx cs cs' E R M model T _ Hg. exfalso. cbn in Hg. lia. Qed.

(* [comment removed for export] *)
Lemma ITAB_ok : itab_sound RSEGS ITAB.
Proof.
  unfold ITAB. repeat apply mk_itab_fuel_sound.
  intros pc i. unfold itab_lookup. destruct pc; try discriminate. rewrite pt_get_leaf. discriminate.
Qed.

Section LIB.
Hypothesis HLIB : LibIface.lib_stmt_P.

Lemma check_sound_all : forall nx0 fuel bfuel p cs s,
  check RSEGS ITAB P0 nx0 bfuel fuel cs p = COk s ->
  forall E R M model, cs_ok E cs R M model ->
  realizes RSEGS (cfg_of R (pc cs) M model) (sd E (m_fs model) s).
Proof.
  intros nx0 fuel bfuel p cs s HC E R M model CS.
  exact (check_sound nx0 ITAB ITAB_ok (call_enframe2_ok nx0) (call_freepro_ok nx0) (node_stdio_write_ok nx0 ref_stdio_write_ok)
           (call_lib_ok HLIB nx0) (call_mainret_ok nx0) (call_printf_ok nx0) node_exitcall_ok
           (call_inflate_vacuous nx0) (call_u2tail_vacuous nx0) fuel bfuel p cs s HC fx0 frm_zero_fx0 E R M model CS).
Qed.
End LIB.

(* [comment removed for export] *)
Theorem target_class_sound : forall (bfuel fuel : nat) (nlo nhi : Z) (p : plan) (s : shape),
  check RSEGS ITAB P0 NX0 bfuel fuel (cs_T nlo nhi) p = COk s ->
  class_shape_ok (0 <? nlo) s = true ->
  0 <= nlo -> (nlo = 0 -> nhi = 0) ->
  LibIface.lib_stmt_P ->
  forall (sp0 gm area brkv mas tid sec : Z) (content : list byte) (R : bvmap 5 word) (M : word -> option byte)
         (VM : VmMaps) (model : Model),
    target_pre sp0 gm area brkv mas tid sec content R M -> target_vm sp0 gm area VM -> std_model VM model ->
    nlo <= hdr_paylen content <= nhi ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x32844) M (seg_rom RSEGS)) model)
             (t_target content (m_fs model)).
Proof.
  intros bfuel fuel nlo nhi p s HC HS H0 Hz HLIB sp0 gm area brkv mas tid sec content R M VM model TP TV [Mf Mv Mh Ml Mm] Hn.
  destruct (target_entry_ok sp0 gm area brkv mas tid sec content R M VM model nlo nhi TP TV Mf Mv Mh Ml Mm Hn) as (e & can & He & Hcan & CS).
  eapply rz_conseq.
  - exact (check_sound_all HLIB NX0 fuel bfuel p (cs_T nlo nhi) s HC _ R M _ CS).
  - rewrite (npos_class nlo nhi content H0 Hz Hn) in HS.
    apply (class_shape_sound _ (m_fs model) content s); [reflexivity | reflexivity | reflexivity | | exact HS].
    exact (proj1 (tp_len _ _ _ _ _ _ _ _ _ _ TP)).
Qed.

(* [comment removed for export] *)
Theorem target_class_sound_k : forall (k : Z) (bfuel fuel : nat) (nlo nhi : Z) (p : plan) (s : shape),
  check RSEGS ITAB P0 NX0k bfuel fuel (cs_Tk k nlo nhi) p = COk s ->
  class_shape_ok (0 <? nlo) s = true ->
  0 <= nlo -> (nlo = 0 -> nhi = 0) ->
  LibIface.lib_stmt_P ->
  forall (sp0 B area brkv mas tid sec : Z) (content : list byte) (R : bvmap 5 word) (M : word -> option byte)
         (VM : VmMaps) (model : Model),
    target_pre_k k sp0 B area brkv mas tid sec content R M -> target_vm_k k sp0 B area VM -> std_model VM model ->
    nlo <= hdr_paylen content <= nhi ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x32844) M (seg_rom RSEGS)) model)
             (t_target content (m_fs model)).
Proof.
  intros k bfuel fuel nlo nhi p s HC HS H0 Hz HLIB sp0 B area brkv mas tid sec content R M VM model TP TV [Mf Mv Mh Ml Mm] Hn.
  destruct (target_entry_k_ok k sp0 B area brkv mas tid sec content R M VM model nlo nhi TP TV Mf Mv Mh Ml Mm Hn) as (e & can & He & Hcan & CS).
  eapply rz_conseq.
  - exact (check_sound_all HLIB NX0k fuel bfuel p (cs_Tk k nlo nhi) s HC _ R M _ CS).
  - rewrite (npos_class nlo nhi content H0 Hz Hn) in HS.
    apply (class_shape_sound _ (m_fs model) content s); [reflexivity | reflexivity | reflexivity | | exact HS].
    exact (tk_len _ _ _ _ _ _ _ _ _ _ _ TP).
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
