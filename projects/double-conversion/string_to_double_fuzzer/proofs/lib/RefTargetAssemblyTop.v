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
  SymExec3 SymExec3Sound SymRun3 SymDrive3 SymPlan SymSlots SymPlanSoundA SymPlanSound
  RefTargetEntry_defs RefTargetEntry RefTargetEntryK_defs RefTargetEntryK RefTargetShape RefTargetShapeTop RefTargetAssembly LibIface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import SX2. Import SX2S. Import SP. Import SPSA. Import SPS.
Open Scope Z_scope.

#[local] Abbreviation RSEGS := ImgP.M.loaded_segments.
#[local] Existing Instance PropExec.fx0.   (* [comment removed for export] *)

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Theorem target_class_sound_top : forall (bfuel fuel : nat) (nlo nhi : Z) (p : plan) (s : shape),
  check RSEGS ITAB P0 NX0 bfuel fuel (cs_T nlo nhi) p = COk s ->
  class_shape_ok0 (0 <? nlo) s = true ->
  65529 <= nlo ->
  LibIface.lib_stmt_P ->
  forall (sp0 gm area brkv mas tid sec : Z) (content : list byte) (R : bvmap 5 word) (M : word -> option byte)
         (VM : VmMaps) (model : Model),
    target_pre sp0 gm area brkv mas tid sec content R M -> target_vm sp0 gm area VM -> std_model VM model ->
    nlo <= hdr_paylen content <= nhi ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x32844) M (seg_rom RSEGS)) model)
             (t_target content (m_fs model)).
Proof.
  intros bfuel fuel nlo nhi p s HC HS Htop HLIB sp0 gm area brkv mas tid sec content R M VM model TP TV [Mf Mv Mh Ml Mm] Hn.
  destruct (target_entry_ok sp0 gm area brkv mas tid sec content R M VM model nlo nhi TP TV Mf Mv Mh Ml Mm Hn) as (e & can & He & Hcan & CS).
  pose proof (tp_len _ _ _ _ _ _ _ _ _ _ TP) as HL.
  assert (CR : 0 <= hdr_cfglen content < 32768) by (unfold hdr_cfglen; apply Z.mod_pos_bound; lia).
  assert (C0 : hdr_cfglen content = 0) by (unfold hdr_paylen in Hn; lia).
  eapply rz_conseq.
  - exact (check_sound_all HLIB NX0 fuel bfuel p (cs_T nlo nhi) s HC _ R M _ CS).
  - replace (0 <? nlo) with (npos_of content) in HS by (unfold npos_of;
      destruct (Z.ltb_spec 0 nlo); [apply Z.ltb_lt | apply Z.ltb_ge]; lia).
    apply (class_shape_sound0 _ (m_fs model) content s); [reflexivity | reflexivity | reflexivity | exact C0 | lia | exact HS].
Qed.

(* [comment removed for export] *)
Theorem target_class_sound_top_k : forall (k : Z) (bfuel fuel : nat) (nlo nhi : Z) (p : plan) (s : shape),
  check RSEGS ITAB P0 NX0k bfuel fuel (cs_Tk k nlo nhi) p = COk s ->
  class_shape_ok0 (0 <? nlo) s = true ->
  capk k - 7 <= nlo ->
  LibIface.lib_stmt_P ->
  forall (sp0 B area brkv mas tid sec : Z) (content : list byte) (R : bvmap 5 word) (M : word -> option byte)
         (VM : VmMaps) (model : Model),
    target_pre_k k sp0 B area brkv mas tid sec content R M -> target_vm_k k sp0 B area VM -> std_model VM model ->
    nlo <= hdr_paylen content <= nhi ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x32844) M (seg_rom RSEGS)) model)
             (t_target content (m_fs model)).
Proof.
  intros k bfuel fuel nlo nhi p s HC HS Htop HLIB sp0 B area brkv mas tid sec content R M VM model TP TV [Mf Mv Mh Ml Mm] Hn.
  destruct (target_entry_k_ok k sp0 B area brkv mas tid sec content R M VM model nlo nhi TP TV Mf Mv Mh Ml Mm Hn) as (e & can & He & Hcan & CS).
  pose proof (tk_len _ _ _ _ _ _ _ _ _ _ _ TP) as HL. pose proof (tk_L _ _ _ _ _ _ _ _ _ _ _ TP) as HK.
  pose proof (capk_pos (k - 1) ltac:(pose proof (wk_k _ _ _ _ _ _ _ _ _ (tk_world _ _ _ _ _ _ _ _ _ _ _ TP)); lia)) as Hc.
  assert (CR : 0 <= hdr_cfglen content < 32768) by (unfold hdr_cfglen; apply Z.mod_pos_bound; lia).
  assert (C0 : hdr_cfglen content = 0) by (unfold hdr_paylen in Hn; lia).
  eapply rz_conseq.
  - exact (check_sound_all HLIB NX0k fuel bfuel p (cs_Tk k nlo nhi) s HC _ R M _ CS).
  - replace (0 <? nlo) with (npos_of content) in HS by (unfold npos_of;
      destruct (Z.ltb_spec 0 nlo); [apply Z.ltb_lt | apply Z.ltb_ge]; unfold hdr_paylen in *; lia).
    apply (class_shape_sound0 _ (m_fs model) content s); [reflexivity | reflexivity | reflexivity | exact C0 | lia | exact HS].
Qed.

(* [comment removed for export] *)
Theorem target_class_sound_low_k : forall (k : Z) (bfuel fuel : nat) (nlo nhi : Z) (p : plan) (s : shape),
  check RSEGS ITAB P0 NX0k bfuel fuel (cs_Tk k nlo nhi) p = COk s ->
  class_shape_ok1 (0 <? nlo) s = true ->
  nhi + 6 < capk (k - 1) ->
  0 <= nlo -> (nlo = 0 -> nhi = 0) ->
  LibIface.lib_stmt_P ->
  forall (sp0 B area brkv mas tid sec : Z) (content : list byte) (R : bvmap 5 word) (M : word -> option byte)
         (VM : VmMaps) (model : Model),
    target_pre_k k sp0 B area brkv mas tid sec content R M -> target_vm_k k sp0 B area VM -> std_model VM model ->
    nlo <= hdr_paylen content <= nhi ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x32844) M (seg_rom RSEGS)) model)
             (t_target content (m_fs model)).
Proof.
  intros k bfuel fuel nlo nhi p s HC HS Hlow H0 Hz HLIB sp0 B area brkv mas tid sec content R M VM model TP TV [Mf Mv Mh Ml Mm] Hn.
  destruct (target_entry_k_ok k sp0 B area brkv mas tid sec content R M VM model nlo nhi TP TV Mf Mv Mh Ml Mm Hn) as (e & can & He & Hcan & CS).
  pose proof (tk_len _ _ _ _ _ _ _ _ _ _ _ TP) as HL. pose proof (tk_L _ _ _ _ _ _ _ _ _ _ _ TP) as HK.
  assert (C1 : 1 <= hdr_cfglen content) by (unfold hdr_paylen in Hn; lia).
  eapply rz_conseq.
  - exact (check_sound_all HLIB NX0k fuel bfuel p (cs_Tk k nlo nhi) s HC _ R M _ CS).
  - rewrite (npos_class nlo nhi content H0 Hz Hn) in HS.
    apply (class_shape_sound1 _ (m_fs model) content s); [reflexivity | reflexivity | reflexivity | exact C1 | exact HL | exact HS].
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
