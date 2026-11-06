(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceANull HeapIfaceN IcptIfaceA L5Defs FPSteps.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmHeapIfaceA PmIcptIfaceA PmLibIfaceA PmLibIfaceAW PmLibDefs PmLibDefsA PmLibSpecsA PmLibStaticsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmLibSpecs PmEncSpecs PmEncSpecsA PmLibSpecsW PmRef PmRefAllow PmTopSpecsXBW.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import Pm5IcptLayout Pm5L5DefsA Pm5ArtFsInv Pm5ArtIfaceInst Pm5ArtIfaceInstX Pm5ArtIfaceInstN PmLibAssemblyXB PmInfraXB PmIslandInstXB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import PmTopSpecsXB AssemblyFullXBWF.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.FloatXB Require SnprintfCpsXB.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module GLXB.
Abbreviation IC := PMLA.C_xboth.

(* [comment removed for export] *)
Lemma clok_CLX : forall txt : list Z, Z.of_nat (length txt) < 2 ^ 26 -> Forall (fun b => 0 <= b <= 255) txt -> PMR.IND txt < 2 ^ 31 -> PMR.IND txt + PMR.ALLOW txt <= ASMXB.CLX.
Proof. intros txt Hn _ HI. pose proof (PMRA.ALLOW_bound txt). unfold ASMXB.CLX. lia. Qed.

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
Lemma SNCELLS : incl SnprintfCpsXB.SNA_CELLS (asc_cells art_C).
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
  Pm5ArtIfaceInstN.pm_instN art_L ar IL scfg HI ->
  ASMXB.lib_specxAW_exp scfg PHI ar HI ASMXB.LayXA.
Proof.
  intros ar HI _ _ HIok ICok FN INok LPM.
  (* [comment removed for export] *)
  eapply (@ASMFXBWF.lib_ok_xaw_full scfgP art_L ar art_C HI IL).
  all: first
   [ exact LPM
   | reflexivity
   | exact PHIW
   | exact FN
   | exact clok_CLX
   | exact (IFXB.HIok0 scfg ar HI HIok)
   | exact IFXB.LAY | exact IFXB.FPM | exact IFXB.FOOTC | exact IFXB.FOOTC2 | exact IFXB.FOOTXC | exact IFXB.TPV
   | exact (IFXB.ISH scfg ar HI IL ILX ICok)
   | exact (IFXB.ANN scfg ar HI IL ILX ILXok ICok)
   | exact (IFXB.POI_VTT IL ILok) | exact (IFXB.POI_VBO IL ILok) | exact (IFXB.POI_ISS IL ILok) | exact (IFXB.POI_HN IL ILok) | exact (IFXB.POI_EC5 IL ILok)
   | exact (IFXB.POI_MS IL ILok) | exact (IFXB.POI_RO IL ILok)
   | exact IFXB.PATR
   | exact (IFXB.SF5 scfg ar HI HIok)
   | exact (IFXB.SETSH00 scfg ar HI IL ILX ILXok ICok) | exact (IFXB.SETSHF8 scfg ar HI IL ILX ILXok ICok) | exact (IFXB.SETSHF5 scfg ar HI IL ILX ILXok ICok)
   | exact (IFXB.MEMSET_LIBC scfg ar HI IL ILX ILXok ICok) | exact (IFXB.MEMCPY_LIBC scfg ar HI IL ILX ILok ICok) | exact (IFXB.MEMMOVE_LIBC scfg ar HI IL ILX ILok ICok)
   | exact (IFXB.MEMCMP_TU scfg ar HI IL ILX ILXok ICok)
   | exact (IFXB.RTG scfg ar HI IL ILX ICok)
   | exact (IFXB.GLIN IL ILok)
   | exact IFXB.CLOKX | exact IFXB.CL40X | exact (IFXB.POI_TC IL ILok) | exact IFXB.FOOTXC2
   | exact (IFXB.ACC_NULL scfg ar HI IL ILX ILok ICok) | exact (IFXB.ACC_TRUE scfg ar HI IL ILX ILok ICok) | exact (IFXB.ACC_FALSE scfg ar HI IL ILX ILok ICok)
   | exact (IFXB.ACC_COLON scfg ar HI IL ILX ILok ICok) | exact (IFXB.ACC_COMMA scfg ar HI IL ILX ILok ICok) | exact (IFXB.ACC_OBRACE scfg ar HI IL ILX ILok ICok)
   | exact (IFXB.ACC_CBRACE scfg ar HI IL ILX ILok ICok) | exact (IFXB.ACC_OBRACKET scfg ar HI IL ILX ILok ICok) | exact (IFXB.ACC_CBRACKET scfg ar HI IL ILX ILok ICok)
   | exact (IFXB.ACC_JT1 scfg ar HI IL ILX ILok ICok) | exact (IFXB.ACC_JT2 scfg ar HI IL ILX ILok ICok) | exact (IFXB.ACC_OB1 scfg ar HI IL ILX ILok ICok) | exact (IFXB.ACC_OB2 scfg ar HI IL ILX ILok ICok)
   | exact IFXB.SM0 | exact IFXB.SM1 | exact IFXB.SM2 | exact IFXB.SM3 | exact IFXB.SM4 | exact IFXB.SM5
   | exact ICok
   | exact (IFXB.CXA_PC ILX ILXok) | exact (IFXB.CXA_SCR ILX ILXok) | exact (IFXB.CXA_TAB ILX ILXok) | exact (IFXB.CXA_AT ILX ILXok) | exact (IFXB.CXA_NL ILX ILXok)
   | exact (IFXB.POI_VT IL ILok) | exact (IFXB.POI_IOS32 IL ILok) | exact (IFXB.POI_BOM IL ILok) | exact (IFXB.POI_TAB IL ILok)
   | exact IFXB.FLA | exact IFXB.ERRNO_NS | exact (IFXB.GLT IL ILok) | exact (IFXB.GLE IL ILok) | exact (IFXB.RSD scfg ar HI IL ILX ICok) | exact SNCELLS
   | exact (IFXB.ILG_FMT IL ILok) | exact (IFXB.POI_SNP IL ILok)
   | exact (ISAI5.locale_ctor_first_art scfg ar HI IL ILX _ ILok ILXok HIok ICok)
   | exact (IFXB.OPNEWX scfg ar HI IL HIok INok) | exact (IFXB.MEMCPY_X scfg ar HI IL ILok INok) | exact (IFXB.MEMMOVE_X scfg ar HI IL ILok INok)
   | exact (IFXB.POI_CV IL ILok)
   | idtac ].
Qed.
End G.
End GLXB.
