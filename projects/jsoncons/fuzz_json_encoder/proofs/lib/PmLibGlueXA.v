(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceANull HeapIfaceN IcptIfaceA L5Defs FPSteps.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmHeapIfaceA PmIcptIfaceA PmLibIfaceA PmLibIfaceAW PmLibDefs PmLibDefsA PmLibSpecsA PmLibStaticsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmLibSpecs PmEncSpecs PmEncSpecsA PmLibSpecsW PmRef PmRefAllow PmTopSpecsXAW.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import Pm4IcptLayout Pm4L5DefsA Pm4ArtFsInv Pm4ArtIfaceInst Pm4ArtIfaceInstX Pm4ArtIfaceInstN PmLibAssemblyXA PmInfraXA PmIslandInstXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import PmTopSpecsXA AssemblyFullXAWF.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.FloatXA Require SnprintfCpsXA.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module GLXA.
Abbreviation IC := PMLA.C_xasan.

(* [comment removed for export] *)
Lemma clok_CLX : forall txt : list Z, Z.of_nat (length txt) < 2 ^ 26 -> Forall (fun b => 0 <= b <= 255) txt -> PMR.IND txt < 2 ^ 31 -> PMR.IND txt + PMR.ALLOW txt <= ASMXA.CLX.
Proof. intros txt Hn _ HI. pose proof (PMRA.ALLOW_bound txt). unfold ASMXA.CLX. lia. Qed.

(* [comment removed for export] *)
Definition z3eqb (a b : Z * Z * Z) : bool :=
  match a, b with (a1, a2, a3), (b1, b2, b3) => (Z.eqb a1 b1 && Z.eqb a2 b2 && Z.eqb a3 b3)%bool end.
Lemma z3eqb_eq : forall a b, z3eqb a b = true -> a = b.
Proof. intros [[a1 a2] a3] [[b1 b2] b3] H. cbn in H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. apply Z.eqb_eq in H3. subst. reflexivity. Qed.
Lemma incl_of_z3chk : forall l m, forallb (fun c => existsb (z3eqb c) m) l = true -> incl l m.
Proof.
  intros l m H c Hc. rewrite forallb_forall in H. specialize (H c Hc). apply existsb_exists in H as (d & Hd & E). apply z3eqb_eq in E. subst. exact Hd.
Qed.
Lemma SNCELLS : incl SnprintfCpsXA.SNA_CELLS (asc_cells art_C).
Proof. apply incl_of_z3chk. vm_compute. reflexivity. Qed.

Section G.
Variable scfg : SpuriousCfg.
#[local] Instance scfgP : ScfgP := MkScfgP scfg.
Variable IL : icpt_layout.
Variable ILX : icpt_layout_x.
Hypothesis ILok : as0_icpt_layout IL.
Hypothesis ILXok : pm_icpt_layout_x ILX.
Variable PHI : list byte -> Prop.
Hypothesis PHIW : TPSXAW.phiwP PHI.
Theorem libtopw : forall (ar : asan_run) (HI : asan_iface),
  as0_icpt_layout IL -> pm_icpt_layout_x ILX ->
  pm_asan_iface_ok art_L art_LX ar art_C scfg HI ->
  pm_aicpt_ok art_L ar IL ILX scfg HI (aannotate_spec art_L ar scfg HI (iclx_annotate ILX) 4096) ->
  afree_null_spec art_L ar scfg HI ->
  Pm4ArtIfaceInstN.pm_instN art_L ar IL scfg HI ->
  ASMXA.lib_specxAW_exp scfg PHI ar HI ASMXA.LayXA.
Proof.
  intros ar HI _ _ HIok ICok FN INok LPM.
  (* [comment removed for export] *)
  eapply (@ASMFXAWF.lib_ok_xaw_full scfgP art_L ar art_C HI IL).
  all: first
   [ exact LPM
   | reflexivity
   | exact PHIW
   | exact FN
   | exact clok_CLX
   | exact (IFXA.HIok0 scfg ar HI HIok)
   | exact IFXA.LAY | exact IFXA.FPM | exact IFXA.FOOTC | exact IFXA.FOOTC2 | exact IFXA.FOOTXC | exact IFXA.TPV
   | exact (IFXA.ISH scfg ar HI IL ILX ICok)
   | exact (IFXA.ANN scfg ar HI IL ILX ILXok ICok)
   | exact (IFXA.POI_VTT IL ILok) | exact (IFXA.POI_VBO IL ILok) | exact (IFXA.POI_ISS IL ILok) | exact (IFXA.POI_HN IL ILok) | exact (IFXA.POI_EC5 IL ILok)
   | exact (IFXA.POI_MS IL ILok) | exact (IFXA.POI_RO IL ILok)
   | exact IFXA.PATR
   | exact (IFXA.SF5 scfg ar HI HIok)
   | exact (IFXA.SETSH00 scfg ar HI IL ILX ILXok ICok) | exact (IFXA.SETSHF8 scfg ar HI IL ILX ILXok ICok) | exact (IFXA.SETSHF5 scfg ar HI IL ILX ILXok ICok)
   | exact (IFXA.MEMSET_LIBC scfg ar HI IL ILX ILXok ICok) | exact (IFXA.MEMCPY_LIBC scfg ar HI IL ILX ILok ICok) | exact (IFXA.MEMMOVE_LIBC scfg ar HI IL ILX ILok ICok)
   | exact (IFXA.MEMCMP_TU scfg ar HI IL ILX ILXok ICok)
   | exact (IFXA.RTG scfg ar HI IL ILX ICok)
   | exact (IFXA.GLIN IL ILok)
   | exact IFXA.CLOKX | exact IFXA.CL40X | exact (IFXA.POI_TC IL ILok) | exact IFXA.FOOTXC2
   | exact (IFXA.ACC_NULL scfg ar HI IL ILX ILok ICok) | exact (IFXA.ACC_TRUE scfg ar HI IL ILX ILok ICok) | exact (IFXA.ACC_FALSE scfg ar HI IL ILX ILok ICok)
   | exact (IFXA.ACC_COLON scfg ar HI IL ILX ILok ICok) | exact (IFXA.ACC_COMMA scfg ar HI IL ILX ILok ICok) | exact (IFXA.ACC_OBRACE scfg ar HI IL ILX ILok ICok)
   | exact (IFXA.ACC_CBRACE scfg ar HI IL ILX ILok ICok) | exact (IFXA.ACC_OBRACKET scfg ar HI IL ILX ILok ICok) | exact (IFXA.ACC_CBRACKET scfg ar HI IL ILX ILok ICok)
   | exact (IFXA.ACC_JT1 scfg ar HI IL ILX ILok ICok) | exact (IFXA.ACC_JT2 scfg ar HI IL ILX ILok ICok) | exact (IFXA.ACC_OB1 scfg ar HI IL ILX ILok ICok) | exact (IFXA.ACC_OB2 scfg ar HI IL ILX ILok ICok)
   | exact IFXA.SM0 | exact IFXA.SM1 | exact IFXA.SM2 | exact IFXA.SM3 | exact IFXA.SM4 | exact IFXA.SM5
   | exact ICok
   | exact (IFXA.CXA_PC ILX ILXok) | exact (IFXA.CXA_SCR ILX ILXok) | exact (IFXA.CXA_TAB ILX ILXok) | exact (IFXA.CXA_AT ILX ILXok) | exact (IFXA.CXA_NL ILX ILXok)
   | exact (IFXA.POI_VT IL ILok) | exact (IFXA.POI_IOS32 IL ILok) | exact (IFXA.POI_BOM IL ILok) | exact (IFXA.POI_TAB IL ILok)
   | exact IFXA.FLA | exact IFXA.ERRNO_NS | exact (IFXA.GLT IL ILok) | exact (IFXA.GLE IL ILok) | exact (IFXA.RSD scfg ar HI IL ILX ICok) | exact SNCELLS
   | exact (IFXA.ILG_FMT IL ILok) | exact (IFXA.POI_SNP IL ILok)
   | exact (ISAI4.locale_ctor_first_art scfg ar HI IL ILX _ ILok ILXok HIok ICok)
   | exact (IFXA.OPNEWX scfg ar HI IL HIok INok) | exact (IFXA.MEMCPY_X scfg ar HI IL ILok INok) | exact (IFXA.MEMMOVE_X scfg ar HI IL ILok INok)
   | idtac ].
Qed.
End G.
End GLXA.
