(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From Stdlib Require Permutation.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fb.

(* [comment removed for export] *)
Module Lib_load_obj_hv_pf2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "@Corelib.Init.Datatypes"; "cons"; "pair"; "prod"; "nat"; "list"; "bool"; "true"; "nil"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "PTrue"; "JA"; "frozen"; "nd_below"; "ok_frameKA"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sv"; "ss_facts"; "ss_next"; "sprop"; "sprop_below"; "@stdpp.bitvector.definitions"; "bv"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "assn"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud"; "ndA1"; "RL"; "VLA"; "z0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs"; "NP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_hv0"; "E_hv0"; "@Stdlib.Lists.List"; "In"; "forallb"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.es.Lib_load_obj_hv_pf1"; "pure_ruleL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_hvkit"; "PhisH"; "mH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ez.Lib_load_obj_hvpk"; "xrs_chkRo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue"; "V_B"; "tblB"; "tvL"; "P0_lo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF"; "V_below"; "efmeasA"; "phiK"; "JAF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_hv"; "X_hv"; "T_sd1n"; "T_sd1y"; "T_sd2n"; "T_sd2y"; "T_sd3n"; "T_sd3y"; "T_sd4n"; "T_sd4y"; "T_sd5n"; "T_sd5y"; "T_sd6n"; "T_sd6y"; "T_sd7n"; "T_sd7y"; "T_sd8n"; "T_sd8y"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_hvj"; "K_vr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.Lib_diag_append"; "Posts_da"; "Pre_da"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ez.Lib_load_obj_hv1e"; "cutsH1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f4.Lib_load_obj_hv2"; "L_ms"; "Pre_ms"; "cutsH2"; "E_ms1"; "E_ms2"; "E_ms3"; "T_ms1b"; "T_ms2b"; "T_ms3b"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double"; "Posts_sd"; "Pre_sd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "AE_A"; "JL_pure"; "J_memset_pre"; "alloc_contractsA"; "alloc_contractsA_ex"; "alloc_lawsA"; "@Stdlib.PArith.BinPos.Pos"; "lt"; "le"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eg.Lib_builderH_pf"; "frozen_stableH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_fuzz_iface"; "in_lits"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ff.Lib_load_obj_hv_pf2.Sum"; "fb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CFGA GlueA SummaryA SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV TobjArena ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TobjJVA InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAS TobjJAT TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require ObjEmptyA PinA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require HideA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAM2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAFb OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.TobjJAH OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.ObjZeroA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ObjEmptyA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.PinA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.AddCellsA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.HideA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eg.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_rom_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e8.Lib_scan_double_ex OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eh.Lib_builder_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eg.Lib_builderH_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_rom_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.Lib_diag_append.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ej.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ej.Lib_build_line_index_rom_call.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_defs Lib_load_obj_pro.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ez.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require es.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eo.Lib_load_obj_pro2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_hv0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_hv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_hvj OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_hvkit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ez.Lib_load_obj_hvpk OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f4.Lib_load_obj_hv2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f4.Lib_load_obj_hv1c OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ez.Lib_load_obj_hv1e OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.es.Lib_load_obj_hv_pf1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ScanDoubleAddr DiagAppendAddr LOAddr LOLAddr HVAddr.

Lemma VB_meas : ltac2:(tb__ "0|0|
S13S1bS8S37R1S31A2S9A3S1cS65P1ccR2A2S65P1d3R2A2A2F_;Fn;").
Proof.
  intros n H. split; [apply Pos.ltb_lt; apply (proj1 (forallb_forall _ _) H); cbn; tauto | apply Pos.ltb_lt; apply (proj1 (forallb_forall _ _) H); cbn; tauto].
Qed.

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
S4dS14S7S1aQ40A1A1S67OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
S64SbVAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S12S4eVCST;R1A2S1cS2bZ0R2A2S2cR2S5eA2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S12S4eVXGL;R1A2S1cS2bZ0R2A2S2cR2S5eA2A2F_;Fa;").
Hypothesis HXlits : ltac2:(tb__ "0|0|
S12S69R1A1S4eVXGL;R2A2F_;Fa;").
Hypothesis LFLAG : law_flag_stmt AInv.
Hypothesis LFSH : law_fshadow_stmt AInv.
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S7S5S5S12S12A2S12A2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 7 BX.
Variable rho0 : valuation.
Let P0 : ltac2:(tb__ "0|0|
S14OFr;") := ltac2:(tb__ "0|0|
S34VCST;VFB;VFF;A3").
Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
SeVAInv;VCST;VXGL;S27VKc;Vrho0;VP0;VFB;VFF;VBX;SdVnd;Ac").
Let JAFv (Phi : valuation -> Prop) (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S3aVAInv;VCST;VXGL;S27VKc;Vrho0;VP0;VFB;VFF;VBX;SdVPhi;Vnd;Ad").
Let frozen_stable : ltac2:(tb__ "0|0|
S13S13ScS14S66S27R3A2S1bS8S10R4R3A2S9A3S1eSbR6SfVAInv;VCST;VXGL;S27VKc;Vrho0;VP0;VFB;VFF;VBX;SdR4R3AdA3F_;F_;Frho;Fnd;Fm;Fn;") := ltac2:(tb__ "0|0|
S68VAInv;VCST;VXGL;VALA;S27VKc;VHKc;VFB;VFF;VBX;Vrho0;VP0;Ac").

Lemma CXR_entry : ltac2:(tb__ "0|0|
S1bS8S30VXGL;S16S1S28A1A1S33Z4Z1eS2S28A1A6S9A3"). Proof using . OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma CXR_ms1 : ltac2:(tb__ "0|0|
S1bS8S30VXGL;S16S1S58A1A1S33Z4Z1eS3bA6S9A3"). Proof using . OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma CXR_ms2 : ltac2:(tb__ "0|0|
S1bS8S30VXGL;S16S1S59A1A1S33Z4Z1eS3bA6S9A3"). Proof using . OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma CXR_ms3 : ltac2:(tb__ "0|0|
S1bS8S30VXGL;S16S1S5aA1A1S33Z4Z1eS3bA6S9A3"). Proof using . OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma CVE_ms : ltac2:(tb__ "0|0|
S1cS1bS8S37S17S1S55A1A1S31A2S9A3S1cS1bS8S37S17S1S56A1A1S31A2S9A3S1bS8S37S17S1S57A1A1S31A2S9A3A2A2").
Proof using . OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition fb (T : axst) : bool := ltac2:(tb__ "0|1|
S2aS18S19S17S1VT;A1M0A1A1S16G0A1A3").
Lemma Cfb_sd : ltac2:(tb__ "0|0|
S1bS8S2aS0S6aS3S0S3cS3S0S3dS3S0S3eS3S0S3fS3S0S40S3S0S41S3S0S42S3S0S43S3S0S44S3S0S45S3S0S46S3S0S47S3S0S48S3S0S49S3S0S4aS3S0S4bSaS0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3S9A3").
Proof using . OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma fb_in : ltac2:(tb__ "0|1|
S0S29S0R1S3S0S3cS3S0S3dS3S0S3eS3S0S3fS3S0S40S3S0S41S3S0S42S3S0S43S3S0S44S3S0S45S3S0S46S3S0S47S3S0S48S3S0S49S3S0S4aS3S0S4bSaS0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3S1bS8S2aS18S19S17S1R2A1M0A1A1S16G0A1A3S9A3F_;FT;").
Proof using . intros T H. exact (proj1 (forallb_forall _ _) Cfb_sd T H). Qed.
Ltac inl := cbn [In]; repeat (first [left; reflexivity | right]).

Section Safety.
Variable ok : world -> Prop.
Hypothesis Hok : ltac2:(tb__ "0|0|
S11SbVKc;Vok;A3").
Hypothesis AC : ltac2:(tb__ "0|0|
S62SbS5fVAInv;VCST;VXGL;A5").
Variable FAMQ : list word -> assn.
Hypothesis XKVR : ltac2:(tb__ "0|1|
S14S7S1aQ40A1A1M0G0S20SbVok;S1dSbVJAFv;S32S23A2S4cR3R2A5VFAMQ;R1A1A4Ftp0;Ftp;Frho;").

Lemma PURE_sd_T : ltac2:(tb__ "0|0|
S2dVAInv;VCST;VXGL;VKc;VFB;VFF;VBX;Vrho0;S20SbVok;A2S5cS5bAb").
Proof using ALA HKc Hok.
  intros Cl s R rho1 tp1 nd Q' He Hc Hn Hb Hf Hk.
  apply (pure_callA segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue HKc ALA ok Cl Pre_sd s R Posts_sd rho1 tp1 nd Q'); try assumption.
  intros rho2 tp2. apply scan_double_sum; [apply frozen_ok_frameA; exact Hok | apply (frozen_stable NF (ss_next (ax_S Cl)) nd rho1); [apply Pos.leb_le; exact Hn | exact Hb]].
Qed.
Lemma PURE_da_T : ltac2:(tb__ "0|0|
S2dVAInv;VCST;VXGL;VKc;VFB;VFF;VBX;Vrho0;S20SbVok;A2S50S4fAb").
Proof using ALA HKc Hok.
  intros Cl s R rho1 tp1 nd Q' He Hc Hn Hb Hf Hk.
  apply (pure_callA segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue HKc ALA ok Cl Pre_da s R Posts_da rho1 tp1 nd Q'); try assumption.
  intros rho2 tp2. apply diag_append_sum; [apply frozen_ok_frameA; exact Hok | apply (frozen_stable NF (ss_next (ax_S Cl)) nd rho1); [apply Pos.leb_le; exact Hn | exact Hb]].
Qed.
Lemma CMEMSET_T : ltac2:(tb__ "0|1|
S4dS14S7S1aQ40A1A1S20SbVok;S1dSbS61VAInv;R3VKc;A3S53R2R1A5S36SbS5dR2R1S3S5S0S35A2M0S4S0S35S52S60VAInv;VCST;VXGL;R3VKc;A5A4SaG0A1A3A5A4Ftp1;Frho1;FAi;").
Proof using HKc Hok AC.
  intros Ai rho1 tp1. apply (aca_asan_memset _ _ _ _ _ AC); [exact HKc|]. eapply ok_frameA_of_K; [exact Hok|]. intros r p t m (_ & K & _). exact K.
Qed.

Lemma CUT2_T : ltac2:(tb__ "0|4|
S0ScS6S5S12S15A2M0S14S7S1aQ40A1A1M1G1S29S5S5S5S0ScA2M2S6A2M3G0A2S4G3G0S4G2S6S4S0ScR7R6A4R5A4R4A4S54A3S39S2eR6R4A3S20SbVok;S1dSbVJAv;R8A1R9R5R4A5VFAMQ;R3A1A4F_;F_;Ftp0';Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof using ALA HCST HXGL HXlits LFSH HKc HBX Hok AC XKVR.
  intros T nd k rv rho tp tp0' Hin Hphi.
  apply (triple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisH k) ok nd T rho tp _ Hphi).
  apply (cfg_sound_JAF_h segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc PhisH PhisH_reads H_ecertH2_ok 600%nat cps_v NP cutsH2 exitsH2 ok (FAMQ tp0') Hok
           ecertH2_ok); [| apply in_map_iff; exists (T, nd, k, rv); split; [reflexivity | exact Hin]].
  intros X ndX kX rho1 tp1 HinX. apply in_map_iff in HinX as ([[[X' nd'] k'] rv'] & E & HinX). cbn in E. injection E as <- <- <-.
  destruct CVE_ms as (CV1 & CV2 & CV3).
  assert (MS : forall n E0 Er Ec T0 Tz Tb Tc, ms_chk n E0 Er Ec T0 Tz Tb Tc -> V_below (ss_next (ax_S Ec)) V_B = true ->
               xrs_chkRo XGL (ss_facts (ax_S Tb)) tvL 4 30 X_hv = true -> In (Tc, ndA1, 1%nat) (map efdrop cutsH2) ->
               triple segs ok (SPA segs (JAFv (phiK PhisH 1) ndA1) E0 rho1 tp1) (fun w => SPfamGTA segs (map (nodeIAF AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue PhisH) (map efdrop cutsH2)) w \/ FAMQ tp0' w)).
  { intros n E0 Er Ec T0 Tz Tb Tc Hchk HV HX HinT.
    apply (triple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisH 1)). intros HP1.
    apply (site_ms AInv CST XGL ALA HCST HXGL HXlits LFSH Kc HKc FB FF BX HBX rho0 (triple segs ok) (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok)
             (@triple_ex segs ok) (TRs_pureP segs ok) (call_soundPA3 segs ok) CMEMSET_T n E0 Er Ec T0 Tz Tb Tc rho1 tp1 _ Hchk HV HX HP1).
    intros rho' tp' HP' _.
    exact (reenter_cutJAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue PhisH ok (map efdrop cutsH2) Tc ndA1 1%nat (FAMQ tp0') rho' tp' HinT HP'). }
  cbn [exitsH2 In] in HinX. destruct HinX as [E|[E|[E|[E|[]]]]]; injection E as <- <- <- <-; cbn [efdrop fst snd].
  - exact (MS 0 _ _ _ _ _ _ _ hv2_checks_ms1 CV1 CXR_ms1 ltac:(cbn [map efdrop cutsH2 fst]; inl)).
  - exact (MS 1 _ _ _ _ _ _ _ hv2_checks_ms2 CV2 CXR_ms2 ltac:(cbn [map efdrop cutsH2 fst]; inl)).
  - exact (MS 2 _ _ _ _ _ _ _ hv2_checks_ms3 CV3 CXR_ms3 ltac:(cbn [map efdrop cutsH2 fst]; inl)).
  - eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | exact (XKVR rho1 tp1 tp0')].
Qed.

Lemma CUT1_T : ltac2:(tb__ "0|4|
S0ScS6S5S12S15A2M0S14S7S1aQ40A1A1M1G1S29S5S5S5S0ScA2M2S6A2M3G0A2S4G3G0S4G2S6S4S0ScR7R6A4R5A4R4A4S51A3S39S2eR6R4A3S20SbVok;S1dSbVJAv;R8A1R9R5R4A5VFAMQ;R3A1A4F_;F_;Ftp0';Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof using ALA HCST HXGL HXlits LFSH HKc HBX Hok AC XKVR.
  intros T nd k rv rho tp tp0' Hin Hphi.
  apply (triple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisH k) ok nd T rho tp _ Hphi).
  apply (cfg_sound_JAF_h segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc PhisH PhisH_reads H_ecertH1_ok 600%nat cps_v NP cutsH1 exitsH1 ok (FAMQ tp0') Hok
           ecertH1_ok); [| apply in_map_iff; exists (T, nd, k, rv); split; [reflexivity | exact Hin]].
  intros X ndX kX rho1 tp1 HinX. apply in_map_iff in HinX as ([[[X' nd'] k'] rv'] & E & HinX). cbn in E. injection E as <- <- <-.
  set (QQ := fun w => SPfamGTA segs (map (nodeIAF AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue PhisH) (map efdrop cutsH1)) w \/ FAMQ tp0' w).

  assert (SD : forall Es Tn Ty, sd_chk Es Tn Ty -> fb Tn = true -> fb Ty = true ->
               In (Tn, ndA1, 1%nat) (map efdrop cutsH1) -> In (Ty, ndA1, 1%nat) (map efdrop cutsH1) ->
               tblB rho1 -> triple segs ok (SPA segs (JAv ndA1) Es rho1 tp1) QQ).
  { intros Es Tn Ty Hchk Hbn Hby Hinn Hiny HP1. pose proof Hchk as (_ & _ & _ & _ & _ & _ & _ & _ & CVB & _).
    apply (site_sd AInv CST XGL Kc FB FF BX rho0 (triple segs ok) (TRs_facts segs ok) (TRs_pre segs ok) PURE_sd_T Es Tn Ty rho1 tp1 QQ Hchk Hbn Hby).
    - intros rho' HF Hag. exact (reenter_cutJAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue PhisH ok (map efdrop cutsH1) Tn ndA1 1%nat (FAMQ tp0') rho' tp1 Hinn
                                   (phi_agree V_B tblB tblB_reads _ rho1 rho' CVB Hag HP1)).
    - intros rho' HF Hag. exact (reenter_cutJAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue PhisH ok (map efdrop cutsH1) Ty ndA1 1%nat (FAMQ tp0') rho' tp1 Hiny
                                   (phi_agree V_B tblB tblB_reads _ rho1 rho' CVB Hag HP1)). }

  assert (DA : forall E0 Ec T0 B Td, da_chk E0 Ec T0 B Td -> (exists rv, In (Td, ndA1, 1%nat, rv) cutsH2) ->
               tblB rho1 -> triple segs ok (SPA segs (JAv ndA1) E0 rho1 tp1) QQ).
  { intros E0 Ec T0 B Td Hchk [rvd Hind] HP1. pose proof Hchk as (_ & _ & _ & _ & _ & _ & _ & _ & CVB & _).
    apply (site_da AInv CST XGL Kc FB FF BX rho0 (triple segs ok) (TRs_facts segs ok) (TRs_pre segs ok) PURE_da_T E0 Ec T0 B Td rho1 tp1 QQ Hchk).
    intros rho' HF Hag. eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw |].
    exact (CUT2_T Td ndA1 1%nat rvd rho' tp1 tp0' Hind (phi_agree V_B tblB tblB_reads _ rho1 rho' CVB Hag HP1)). }
  pose proof hv_checks_sd1 as [Cxf1 Csd1].
  assert (Hd1 : exists rv, In (T_da1, ndA1, 1%nat, rv) cutsH2) by (exists (mH 16 3); cbn [cutsH2]; inl).
  assert (Hd2 : exists rv, In (T_da2, ndA1, 1%nat, rv) cutsH2) by (exists (mH 16 3); cbn [cutsH2]; inl).
  assert (Hd3 : exists rv, In (T_da3, ndA1, 1%nat, rv) cutsH2) by (exists (mH 16 3); cbn [cutsH2]; inl).
  cbn [exitsH1 In] in HinX.
  destruct HinX as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]]]]]; injection E as <- <- <- <-; cbn [efdrop fst snd];
    apply (triple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisH 1)); intros HP1.
  - apply (TRs_pre segs ok (SPA segs (JAv ndA1) E_sd1 rho1 tp1)). { intros w Hw. exact (SPA_axforms segs (JAv ndA1) xf_sd1 rho1 E_sd1r E_sd1 tp1 w Cxf1 Hw). }
    exact (SD _ _ _ Csd1 (fb_in T_sd1n ltac:(inl)) (fb_in T_sd1y ltac:(inl)) ltac:(cbn [map efdrop cutsH1 fst]; inl) ltac:(cbn [map efdrop cutsH1 fst]; inl) HP1).
  - exact (SD _ _ _ hv_checks_sd2 (fb_in T_sd2n ltac:(inl)) (fb_in T_sd2y ltac:(inl)) ltac:(cbn [map efdrop cutsH1 fst]; inl) ltac:(cbn [map efdrop cutsH1 fst]; inl) HP1).
  - exact (SD _ _ _ hv_checks_sd3 (fb_in T_sd3n ltac:(inl)) (fb_in T_sd3y ltac:(inl)) ltac:(cbn [map efdrop cutsH1 fst]; inl) ltac:(cbn [map efdrop cutsH1 fst]; inl) HP1).
  - exact (SD _ _ _ hv_checks_sd4 (fb_in T_sd4n ltac:(inl)) (fb_in T_sd4y ltac:(inl)) ltac:(cbn [map efdrop cutsH1 fst]; inl) ltac:(cbn [map efdrop cutsH1 fst]; inl) HP1).
  - exact (SD _ _ _ hv_checks_sd5 (fb_in T_sd5n ltac:(inl)) (fb_in T_sd5y ltac:(inl)) ltac:(cbn [map efdrop cutsH1 fst]; inl) ltac:(cbn [map efdrop cutsH1 fst]; inl) HP1).
  - exact (SD _ _ _ hv_checks_sd6 (fb_in T_sd6n ltac:(inl)) (fb_in T_sd6y ltac:(inl)) ltac:(cbn [map efdrop cutsH1 fst]; inl) ltac:(cbn [map efdrop cutsH1 fst]; inl) HP1).
  - exact (SD _ _ _ hv_checks_sd7 (fb_in T_sd7n ltac:(inl)) (fb_in T_sd7y ltac:(inl)) ltac:(cbn [map efdrop cutsH1 fst]; inl) ltac:(cbn [map efdrop cutsH1 fst]; inl) HP1).
  - exact (SD _ _ _ hv_checks_sd8 (fb_in T_sd8n ltac:(inl)) (fb_in T_sd8y ltac:(inl)) ltac:(cbn [map efdrop cutsH1 fst]; inl) ltac:(cbn [map efdrop cutsH1 fst]; inl) HP1).
  - exact (DA E_da1 E_da1c T_da10 B_da1 T_da1 hv2_checks_da1 Hd1 HP1).
  - exact (DA E_da2 E_da2c T_da20 B_da2 T_da2 hv2_checks_da2 Hd2 HP1).
  - exact (DA E_da3 E_da3c T_da30 B_da3 T_da3 hv2_checks_da3 Hd3 HP1).
  - apply (triple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tblB ok ndA1 K_vr rho1 tp1 _ HP1).
    eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | exact (XKVR rho1 tp1 tp0')].
Qed.

Theorem arm_hv_T : ltac2:(tb__ "0|1|
S14S7S1aQ40A1A1M0G0S20SbVok;S1dSbVJAFv;S32S23A2S28R3R2A5VFAMQ;R1A1A4Ftp0;Ftp;Frho;").
Proof using ALA HCST HXGL HXlits LFSH HKc HBX Hok AC XKVR.
  intros rho tp tp0.
  apply (triple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tblB). intros HPHI.
  pose proof hv_checks_entry as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CVB & _).
  apply (entry_hv AInv CST XGL ALA HCST HXGL HXlits LFSH Kc HKc FB FF BX HBX rho0 (triple segs ok) (TRs_pre segs ok) (@triple_ex segs ok) (TRs_pureP segs ok) rho tp _ CXR_entry).
  intros rho' Hag.
  exact (CUT1_T K_hv0c ndA1 1%nat _ rho' tp tp0 ltac:(cbn [cutsH1]; inl) (phi_agree V_B tblB tblB_reads _ rho rho' CVB Hag HPHI)).
Qed.
End Safety.

Section Existence.
Hypothesis ACX : ltac2:(tb__ "0|0|
S63SbS5fVAInv;VCST;VXGL;A5").
Variable FAM : ltac2:(tb__ "0|0|
S12S7S1aQ40A1A1S21F_;F_;").
Hypothesis FAM_mono : ltac2:(tb__ "0|0|
S12S12S7S1aQ40A1A1S22S2bR4R3A2VFAM;R5R3R2A3VFAM;R5R4R3A3F_;F_;Fw;Ftp0;Fb';Fb;").
Hypothesis XKVR : ltac2:(tb__ "0|2|
S14S7S1aQ40A1A1M0G0S1fSbS1dSbVJAFv;S32S23A2S4cR3R2A5VFAM;S38S4S5S5S0ScA2M1S6A2S5S12S15A2S4G1S6S4S0ScS4cS23A4U1A4S2fZfZ64A2A4R3A2R1A2A3Ftp0;Ftp;Frho;").

Lemma PURE_sd_E : ltac2:(tb__ "0|0|
S2dVAInv;VCST;VXGL;VKc;VFB;VFF;VBX;Vrho0;S1fSbA1S5cS5bAb").
Proof using ALA HKc.
  intros Cl s R rho1 tp1 nd Q' He Hc Hn Hb Hf Hk.
  apply (pure_callA_ex segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue HKc ALA Cl Pre_sd s R Posts_sd rho1 tp1 nd Q'); try assumption.
  intros rho2 tp2. apply scan_double_sum_ex. apply (frozen_stable NF (ss_next (ax_S Cl)) nd rho1); [apply Pos.leb_le; exact Hn | exact Hb].
Qed.
Lemma PURE_da_E : ltac2:(tb__ "0|0|
S2dVAInv;VCST;VXGL;VKc;VFB;VFF;VBX;Vrho0;S1fSbA1S50S4fAb").
Proof using ALA HKc.
  intros Cl s R rho1 tp1 nd Q' He Hc Hn Hb Hf Hk.
  apply (pure_callA_ex segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue HKc ALA Cl Pre_da s R Posts_da rho1 tp1 nd Q'); try assumption.
  intros rho2 tp2. apply diag_append_sum_ex. apply (frozen_stable NF (ss_next (ax_S Cl)) nd rho1); [apply Pos.leb_le; exact Hn | exact Hb].
Qed.
Lemma CMEMSET_E : ltac2:(tb__ "0|1|
S4dS14S7S1aQ40A1A1S1fSbS1dSbS61VAInv;R3VKc;A3S53R2R1A5S36SbS5dR2R1S3S5S0S35A2M0S4S0S35S52S60VAInv;VCST;VXGL;R3VKc;A5A4SaG0A1A3A5A3Ftp1;Frho1;FAi;").
Proof using HKc ACX. intros Ai rho1 tp1. apply (acx_asan_memset _ _ _ _ _ ACX). exact HKc. Qed.

Lemma CUT2_E : ltac2:(tb__ "0|5|
S0ScS6S5S12S15A2M0S14S7S1aQ40A1A1M1S12G1S29S5S5S5S0ScA2M2S6A2M3G0A2S4G3G0S4G2S6S4S0ScR8R7A4R6A4R5A4S54A3S39S2eR7R5A3S1cS2bZ0S38S4G3G0S4G2S6S4S0ScRaR9A4R8A4R7A4R6A2M4A2S2cG4R4A2A2S1fSbS1dSbVJAv;RaA1RbR7R6A5VFAM;R5R4A2A3F_;F_;F_;Ftp0';Fb;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof using ALA HCST HXGL HXlits LFSH HKc HBX ACX FAM_mono XKVR.
  intros T nd k rv rho tp b tp0' Hin Hphi Hm.
  apply (etriple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisH k) nd T rho tp _ Hphi).
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (FAM_mono _ b tp0' w ltac:(apply Z.lt_le_incl; exact (proj2 Hm)) Hw) |].
  apply (cfg_complete_JAF_bh segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc PhisH PhisH_reads H_ecertH2_ok 600%nat cps_v NP cutsH2 exitsH2 (fun b w => FAM b tp0' w)
           (fun b b' w Hb Hw => FAM_mono b b' tp0' w Hb Hw) ecertH2_ok); [|exact Hin].
  intros X ndX kX rvX rho1 tp1 HinX.
  destruct CVE_ms as (CV1 & CV2 & CV3).
  assert (MS : forall n E0 Er Ec T0 Tz Tb Tc, ms_chk n E0 Er Ec T0 Tz Tb Tc -> V_below (ss_next (ax_S Ec)) V_B = true ->
               xrs_chkRo XGL (ss_facts (ax_S Tb)) tvL 4 30 X_hv = true -> In (Tc, ndA1, 1%nat, mH 16 1) cutsH2 ->
               etriple segs (SPA segs (JAFv (phiK PhisH 1) ndA1) E0 rho1 tp1)
                 (fun w => SPfamETA segs (map (enodeIAF AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue PhisH) cutsH2) (efmeasA (E0, ndA1, 1%nat, mH 16 2) rho1) w
                           \/ FAM (efmeasA (E0, ndA1, 1%nat, mH 16 2) rho1) tp0' w)).
  { intros n E0 Er Ec T0 Tz Tb Tc Hchk HV HX HinT.
    apply (etriple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisH 1)). intros HP1.
    apply (TRe_facts segs). intros HF0.
    pose proof Hchk as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CL1 & CL2 & CL3).
    destruct (loopF_vals rho1 _ HF0 (conj CL1 (conj CL2 CL3))) as [HiC Hc26].
    apply (site_ms AInv CST XGL ALA HCST HXGL HXlits LFSH Kc HKc FB FF BX HBX rho0 (etriple segs) (TRe_facts segs) (TRe_ex segs) (TRe_pre segs)
             (@etriple_ex segs) (TRe_pureP segs) (call_completePA3 segs) CMEMSET_E n E0 Er Ec T0 Tz Tb Tc rho1 tp1 _ Hchk HV HX HP1).
    intros rho' tp' HP' HVB.
    apply (ereenter_cutJAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue PhisH cutsH2 Tc ndA1 1%nat (mH 16 1) _ _ rho' tp' HinT HP').
    apply (VLA_lt2 rho1 rho' 16 16 2 1 E0 Tc ndA1 ndA1 1%nat 1%nat); [apply HVB; cbn; tauto | apply HVB; cbn; tauto | exact HiC | exact Hc26 | lia | lia | lia | lia | right; lia]. }
  cbn [exitsH2 In] in HinX. destruct HinX as [E|[E|[E|[E|[]]]]]; injection E as <- <- <- <-.
  - exact (MS 0 _ _ _ _ _ _ _ hv2_checks_ms1 CV1 CXR_ms1 ltac:(cbn [cutsH2]; inl)).
  - exact (MS 1 _ _ _ _ _ _ _ hv2_checks_ms2 CV2 CXR_ms2 ltac:(cbn [cutsH2]; inl)).
  - exact (MS 2 _ _ _ _ _ _ _ hv2_checks_ms3 CV3 CXR_ms3 ltac:(cbn [cutsH2]; inl)).
  - eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | exact (XKVR rho1 tp1 tp0')].
Qed.

Lemma CUT1_E : ltac2:(tb__ "0|5|
S0ScS6S5S12S15A2M0S14S7S1aQ40A1A1M1S12G1S29S5S5S5S0ScA2M2S6A2M3G0A2S4G3G0S4G2S6S4S0ScR8R7A4R6A4R5A4S51A3S39S2eR7R5A3S1cS2bZ0S38S4G3G0S4G2S6S4S0ScRaR9A4R8A4R7A4R6A2M4A2S2cG4R4A2A2S1fSbS1dSbVJAv;RaA1RbR7R6A5VFAM;R5R4A2A3F_;F_;F_;Ftp0';Fb;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof using ALA HCST HXGL HXlits LFSH HKc HBX ACX FAM_mono XKVR.
  intros T nd k rv rho tp b tp0' Hin Hphi Hm.
  apply (etriple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisH k) nd T rho tp _ Hphi).
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (FAM_mono _ b tp0' w ltac:(apply Z.lt_le_incl; exact (proj2 Hm)) Hw) |].
  apply (cfg_complete_JAF_bh segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc PhisH PhisH_reads H_ecertH1_ok 600%nat cps_v NP cutsH1 exitsH1 (fun b w => FAM b tp0' w)
           (fun b b' w Hb Hw => FAM_mono b b' tp0' w Hb Hw) ecertH1_ok); [|exact Hin].
  intros X ndX kX rvX rho1 tp1 HinX.
  set (FQ := fun (bb : Z) (w : world) => SPfamETA segs (map (enodeIAF AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue PhisH) cutsH1) bb w \/ FAM bb tp0' w).

  assert (SD : forall Es E0 Tn Ty aE aT, sd_chk Es Tn Ty -> fb Tn = true -> fb Ty = true -> 0 <= aT < aE -> aE < 2 ^ 27 ->
               In (Tn, ndA1, 1%nat, mH 16 aT) cutsH1 -> In (Ty, ndA1, 1%nat, mH 16 aT) cutsH1 ->
               tblB rho1 -> etriple segs (SPA segs (JAv ndA1) Es rho1 tp1) (FQ (efmeasA (E0, ndA1, 1%nat, mH 16 aE) rho1))).
  { intros Es E0 Tn Ty aE aT Hchk Hbn Hby Ha HaE Hinn Hiny HP1. pose proof Hchk as (_ & _ & _ & _ & _ & _ & _ & _ & CVB & CL1 & CL2 & CL3).
    destruct (VB_meas _ CVB) as [L460 L467].
    apply (TRe_facts segs). intros HF0. destruct (loopF_vals rho1 _ HF0 (conj CL1 (conj CL2 CL3))) as [HiC Hc26].
    apply (site_sd AInv CST XGL Kc FB FF BX rho0 (etriple segs) (TRe_facts segs) (TRe_pre segs) PURE_sd_E Es Tn Ty rho1 tp1 _ Hchk Hbn Hby).
    - intros rho' HF Hag.
      apply (ereenter_cutJAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue PhisH cutsH1 Tn ndA1 1%nat (mH 16 aT) _ _ rho' tp1 Hinn (phi_agree V_B tblB tblB_reads _ rho1 rho' CVB Hag HP1)).
      apply (VLA_lt2 rho1 rho' 16 16 aE aT E0 Tn ndA1 ndA1 1%nat 1%nat); [symmetry; apply (proj1 Hag); exact L460 | symmetry; apply (proj1 Hag); exact L467 | exact HiC | exact Hc26 | lia | lia | lia | lia | right; lia].
    - intros rho' HF Hag.
      apply (ereenter_cutJAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue PhisH cutsH1 Ty ndA1 1%nat (mH 16 aT) _ _ rho' tp1 Hiny (phi_agree V_B tblB tblB_reads _ rho1 rho' CVB Hag HP1)).
      apply (VLA_lt2 rho1 rho' 16 16 aE aT E0 Ty ndA1 ndA1 1%nat 1%nat); [symmetry; apply (proj1 Hag); exact L460 | symmetry; apply (proj1 Hag); exact L467 | exact HiC | exact Hc26 | lia | lia | lia | lia | right; lia]. }

  assert (DA : forall E0 Ec T0 B Td, da_chk E0 Ec T0 B Td -> In (Td, ndA1, 1%nat, mH 16 3) cutsH2 ->
               tblB rho1 -> etriple segs (SPA segs (JAv ndA1) E0 rho1 tp1) (FQ (efmeasA (E0, ndA1, 1%nat, mH 16 4) rho1))).
  { intros E0 Ec T0 B Td Hchk Hind HP1. pose proof Hchk as (_ & _ & _ & _ & _ & _ & _ & _ & CVB & CL1 & CL2 & CL3).
    destruct (VB_meas _ CVB) as [L460 L467].
    apply (site_da AInv CST XGL Kc FB FF BX rho0 (etriple segs) (TRe_facts segs) (TRe_pre segs) PURE_da_E E0 Ec T0 B Td rho1 tp1 _ Hchk).
    intros rho' HF Hag. destruct (loopF_vals rho1 _ HF (conj CL1 (conj CL2 CL3))) as [HiC Hc26].
    eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw |].
    apply (CUT2_E Td ndA1 1%nat (mH 16 3) rho' tp1 _ tp0' Hind (phi_agree V_B tblB tblB_reads _ rho1 rho' CVB Hag HP1)).
    apply (VLA_lt2 rho1 rho' 16 16 4 3 E0 Td ndA1 ndA1 1%nat 1%nat); [symmetry; apply (proj1 Hag); exact L460 | symmetry; apply (proj1 Hag); exact L467 | exact HiC | exact Hc26 | lia | lia | lia | lia | right; lia]. }
  pose proof hv_checks_sd1 as [Cxf1 Csd1].
  cbn [exitsH1 In] in HinX.
  destruct HinX as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]]]]]; injection E as <- <- <- <-;
    apply (etriple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisH 1)); intros HP1.
  - apply (TRe_pre segs (SPA segs (JAv ndA1) E_sd1 rho1 tp1)). { intros w Hw. exact (SPA_axforms segs (JAv ndA1) xf_sd1 rho1 E_sd1r E_sd1 tp1 w Cxf1 Hw). }
    exact (SD E_sd1 E_sd1r T_sd1n T_sd1y 38 36 Csd1 (fb_in T_sd1n ltac:(inl)) (fb_in T_sd1y ltac:(inl)) ltac:(lia) ltac:(lia) ltac:(cbn [cutsH1]; inl) ltac:(cbn [cutsH1]; inl) HP1).
  - exact (SD E_sd2 E_sd2 T_sd2n T_sd2y 34 32 hv_checks_sd2 (fb_in T_sd2n ltac:(inl)) (fb_in T_sd2y ltac:(inl)) ltac:(lia) ltac:(lia) ltac:(cbn [cutsH1]; inl) ltac:(cbn [cutsH1]; inl) HP1).
  - exact (SD E_sd3 E_sd3 T_sd3n T_sd3y 30 28 hv_checks_sd3 (fb_in T_sd3n ltac:(inl)) (fb_in T_sd3y ltac:(inl)) ltac:(lia) ltac:(lia) ltac:(cbn [cutsH1]; inl) ltac:(cbn [cutsH1]; inl) HP1).
  - exact (SD E_sd4 E_sd4 T_sd4n T_sd4y 26 24 hv_checks_sd4 (fb_in T_sd4n ltac:(inl)) (fb_in T_sd4y ltac:(inl)) ltac:(lia) ltac:(lia) ltac:(cbn [cutsH1]; inl) ltac:(cbn [cutsH1]; inl) HP1).
  - exact (SD E_sd5 E_sd5 T_sd5n T_sd5y 22 20 hv_checks_sd5 (fb_in T_sd5n ltac:(inl)) (fb_in T_sd5y ltac:(inl)) ltac:(lia) ltac:(lia) ltac:(cbn [cutsH1]; inl) ltac:(cbn [cutsH1]; inl) HP1).
  - exact (SD E_sd6 E_sd6 T_sd6n T_sd6y 18 16 hv_checks_sd6 (fb_in T_sd6n ltac:(inl)) (fb_in T_sd6y ltac:(inl)) ltac:(lia) ltac:(lia) ltac:(cbn [cutsH1]; inl) ltac:(cbn [cutsH1]; inl) HP1).
  - exact (SD E_sd7 E_sd7 T_sd7n T_sd7y 14 12 hv_checks_sd7 (fb_in T_sd7n ltac:(inl)) (fb_in T_sd7y ltac:(inl)) ltac:(lia) ltac:(lia) ltac:(cbn [cutsH1]; inl) ltac:(cbn [cutsH1]; inl) HP1).
  - exact (SD E_sd8 E_sd8 T_sd8n T_sd8y 10 8 hv_checks_sd8 (fb_in T_sd8n ltac:(inl)) (fb_in T_sd8y ltac:(inl)) ltac:(lia) ltac:(lia) ltac:(cbn [cutsH1]; inl) ltac:(cbn [cutsH1]; inl) HP1).
  - exact (DA E_da1 E_da1c T_da10 B_da1 T_da1 hv2_checks_da1 ltac:(cbn [cutsH2]; inl) HP1).
  - exact (DA E_da2 E_da2c T_da20 B_da2 T_da2 hv2_checks_da2 ltac:(cbn [cutsH2]; inl) HP1).
  - exact (DA E_da3 E_da3c T_da30 B_da3 T_da3 hv2_checks_da3 ltac:(cbn [cutsH2]; inl) HP1).
  - apply (etriple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tblB ndA1 K_vr rho1 tp1 _ HP1).
    eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | exact (XKVR rho1 tp1 tp0')].
Qed.

Theorem arm_hv_E : ltac2:(tb__ "0|2|
S14S7S1aQ40A1A1M0G0S1fSbS1dSbVJAFv;S32S23A2S28R3R2A5VFAM;S38S4S5S5S0ScA2M1S6A2S5S12S15A2S4G1S6S4S0ScS28S23A4U1A4S4S12S15S24S25Z11S26A2A4A4R3A2R1A2A3Ftp0;Ftp;Frho;").
Proof using ALA HCST HXGL HXlits LFSH HKc HBX ACX FAM_mono XKVR.
  intros rho tp tp0.
  apply (etriple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tblB). intros HPHI.
  pose proof hv_checks_entry as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CVB & CL1 & CL2 & CL3).
  destruct (VB_meas _ CVB) as [L460 L467].
  apply (TRe_facts segs). intros HF0. destruct (loopF_vals rho _ HF0 (conj CL1 (conj CL2 CL3))) as [HiC Hc26].
  apply (entry_hv AInv CST XGL ALA HCST HXGL HXlits LFSH Kc HKc FB FF BX HBX rho0 (etriple segs) (TRe_pre segs) (@etriple_ex segs) (TRe_pureP segs) rho tp _ CXR_entry).
  intros rho' Hag.
  apply (CUT1_E K_hv0c ndA1 1%nat (mH 16 40) rho' tp _ tp0 ltac:(cbn [cutsH1]; inl) (phi_agree V_B tblB tblB_reads _ rho rho' CVB Hag HPHI)).
  apply (VLA_lt2 rho rho' 17 16 0 40 E_hv0 K_hv0c ndA1 ndA1 1%nat 1%nat); [symmetry; apply (proj1 Hag); exact L460 | symmetry; apply (proj1 Hag); exact L467 | exact HiC | exact Hc26 | lia | lia | lia | lia | left; lia].
Qed.
End Existence.
End Sum.
End Lib_load_obj_hv_pf2.

(* [comment removed for export] *)
Module Lib_load_obj_hv_pf5.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "valuation"; "rw"; "ss_facts"; "sprop"; "holds"; "sobj"; "ss_next"; "SLit"; "@Corelib.Init.Datatypes"; "list"; "prod"; "pair"; "true"; "bool"; "app"; "Some"; "cons"; "nil"; "option"; "snd"; "fst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "@Corelib.Init.Logic"; "eq"; "and"; "True"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "smatchA"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue"; "frL"; "tblB"; "V_B"; "P0_lo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs"; "kb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop"; "xLD"; "xLK"; "pH"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "rho_sub"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "call_checkPA"; "entails_frA"; "J_ofPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fc.Lib_load_obj_hv4"; "kept_o1"; "R_o1"; "X_1"; "nd_op1"; "tv_op0"; "tv_op1"; "E_o1c"; "PDk_o1"; "T_op0"; "T_op0r"; "T_op1"; "T_op1r"; "Xk_o1"; "nd_op0"; "passed_o1"; "s_o1c"; "tv_o1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ew.Lib_load_obj_hv4p"; "kept_o3"; "E_o3c"; "R_o3"; "X_3"; "payX_o3"; "tv_p0"; "tv_p1"; "PDk_o3"; "T_p0"; "T_p0r"; "T_p1"; "T_p1r"; "Xk_o3"; "nd_p0"; "nd_p1"; "passed_o3"; "payY_o3"; "s_o3c"; "tv_o3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ff.Lib_load_obj_hv_pf5.OP1P"; "P0_op"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ff.Lib_load_obj_hv_pf5.OP3P"; "P0_op"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "PTrue"; "ndesc"; "ANone"; "JA_pre"; "NDA"; "TPA"; "amode"; "fbinA"; "ffinA"; "frinA"; "nd_am"; "tvinA"; "AHead"; "JA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ez.Lib_load_obj_hvpk"; "xrs_chkRo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bitem"; "BXok_d"; "bd_nn"; "bd_wpos"; "bxt"; "pay_sem"; "pay_okF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_geom"; "topG"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs"; "NP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fd.Lib_load_obj_hv4w"; "PreR"; "LR"; "E_o3"; "R_w"; "s_w"; "w_chk"; "w_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "call_linkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_hv3"; "h0"; "nd_keep"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "FBx";
"T_ok"; "tvd"; "tvz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "FFx"; "robjs_okF"; "xrs_okF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG"; "bd_permb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.TobjJAH"; "ndh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK"; "PostsCk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_fuzz_iface"; "in_lits"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f7.Lib_load_obj_hv3m"; "E_o1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fc.Lib_load_obj_hv4.OP1"; "PD_op"; "Pre_op"; "nd0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ew.Lib_load_obj_hv4p.OP3"; "PD_op"; "Pre_op"; "nd0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3"; "import_okPA3"; "import_postA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "JL_pure"; "J_pure_pre"; "alloc_lawsA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia Permutation.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CFGA GlueA SummaryA SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV TobjArena ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TobjJVA InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAS TobjJAT TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require ObjEmptyA PinA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAM2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAFb OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.TobjJAH OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.ObjZeroA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ObjEmptyA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.PinA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.AddCellsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eg.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_rom_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e8.Lib_scan_double_ex OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eh.Lib_builder_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eg.Lib_builderH_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_rom_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.Lib_diag_append.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ej.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eb.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ej.Lib_build_line_index_rom_call OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eb.Lib_vec_reserve_pf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_opt_push1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ei.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_opt_push3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.Asan_memcpyR_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_defs Lib_load_obj_pro.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ez.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require es.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require et.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ew.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fd.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eo.Lib_load_obj_pro2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_hv0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_hv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_hvj OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_hvkit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ez.Lib_load_obj_hvpk OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f4.Lib_load_obj_hv2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.es.Lib_load_obj_hv_pf1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_hv3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f7.Lib_load_obj_hv3m OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fa.Lib_load_obj_hv3e OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_loopE OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.et.Lib_load_obj_hv3f OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fa.Lib_load_obj_hv_pf3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ew.Lib_load_obj_hv_pf4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fc.Lib_load_obj_hv4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fd.Lib_load_obj_hv4w OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ew.Lib_load_obj_hv4p.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ScanDoubleAddr DiagAppendAddr LOAddr LOLAddr HVAddr.

Module OP1P. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ei.Lib_opt_push1_pf. End OP1P.
Lemma HamC_o1 : nd_am OP1.nd0 = ANone. Proof. reflexivity. Qed.
Lemma HamPD_o1 : ltac2:(tb__ "0|1|
S2dSaS16S62A2M0G0S19S67S6bS13S16S62R1A3A1S63A3Ld;S99A3"). Proof. repeat constructor. Qed.
Lemma P0_op_mono : ltac2:(tb__ "0|2|
S9SaS1cS1cA2M0A1M1G1S9SaG0S1cA2A1S1G0S1eG0R1R5A3S1eG0R2R5A3F_;Fbn;S5fR5R3R2A3S5fR5R4R3A3F_;F_;Fr;FFFc;FF';FF;").
Proof. intros F F' FFc r _ H. exact H. Qed.
Lemma lines_in_kept_o1 : ltac2:(tb__ "0|0|
S1eSaS0S0A2SbS0S0S2aS29Z10S2bA2A4S3bA3").
Proof. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 hv4_checks_o1_nd)))))))))))). Qed.
Lemma lines_in_tv_o1 : ltac2:(tb__ "0|0|
S1eSaS0S0A2SbS0S0S2aS29Z10S2bA2A4S4bA3").
Proof. unfold tv_o1. apply in_or_app. left. exact lines_in_kept_o1. Qed.
Lemma lines_in_tv_op1 : ltac2:(tb__ "0|0|
S1eSaS0S0A2SbS0S0S2aS29Z10S2bA2A4S40A3").
Proof. cbn. repeat (first [left; reflexivity | right]). Qed.
Lemma lines_in_tv_op0 : ltac2:(tb__ "0|0|
S1eSaS0S0A2SbS0S0S2aS29Z10S2bA2A4S3fA3").
Proof. cbn. repeat (first [left; reflexivity | right]). Qed.

Module OP3P. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ei.Lib_opt_push3_pf. End OP3P.
Lemma HamC_o3 : nd_am OP3.nd0 = ANone. Proof. reflexivity. Qed.
Lemma HamPD_o3 : ltac2:(tb__ "0|1|
S2dSaS16S62A2M0G0S19S67S6bS13S16S62R1A3A1S63A3Ld;S9cA3"). Proof. repeat constructor. Qed.
Lemma P0_op3_mono : ltac2:(tb__ "0|2|
S9SaS1cS1cA2M0A1M1G1S9SaG0S1cA2A1S1G0S1eG0R1R5A3S1eG0R2R5A3F_;Fbn;S60R5R3R2A3S60R5R4R3A3F_;F_;Fr;FFFc;FF';FF;").
Proof. intros F F' FFc r _ H. exact H. Qed.
Lemma lines_in_kept_o3 : ltac2:(tb__ "0|0|
S1eSaS0S0A2SbS0S0S2aS29Z10S2bA2A4S4cA3").
Proof. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 hv4_checks_o3_nd)))))))))))). Qed.
Lemma lines_in_tv_o3 : ltac2:(tb__ "0|0|
S1eSaS0S0A2SbS0S0S2aS29Z10S2bA2A4S5eA3").
Proof. unfold tv_o3. apply in_or_app. left. exact lines_in_kept_o3. Qed.
Lemma lines_in_tv_p1 : ltac2:(tb__ "0|0|
S1eSaS0S0A2SbS0S0S2aS29Z10S2bA2A4S52A3").
Proof. cbn. repeat (first [left; reflexivity | right]). Qed.
Lemma lines_in_tv_p0 : ltac2:(tb__ "0|0|
S1eSaS0S0A2SbS0S0S2aS29Z10S2bA2A4S51A3").
Proof. cbn. repeat (first [left; reflexivity | right]). Qed.

Lemma pay_okF_split_sem : ltac2:(tb__ "0|1|
S1OF_;S9S4A1S0S1cS9S70A1M0G0G0G0G0S19SdS93R5SeS70R3R2A3A2ScA3S19SdS93SeS70R4R2A3R5A2ScA3S19SdS73R5A1ScA3S19SdS73R4A1ScA3S88Z0RaA2S1S2dS4S5R1A1ReA3S72R9R2A2S75R3RfReRaR9A5F_;F_;Frho;S76RfReRdRcRbRaA6F_;F_;F_;F_;F_;F_;FY;FX;Fcommon;Fbto;Fbfrom;FcostK;FcostV;Ffacts;Fpre;").
Proof.
  intros pre facts costV costK bfrom bto common X Y HP1 HP2 Hwc Hwy Hk Hsem.
  pose proof (bd_permb_sound _ _ HP1) as P1. pose proof (bd_permb_sound _ _ HP2) as P2.
  split; [|split; [exact Hk|]].
  - unfold bd_wpos in *. apply forallb_forall. intros it Hit.
    assert (Hin : In it (common ++ Y)) by (eapply Permutation_in; [apply Permutation_sym; exact P2 | exact Hit]).
    apply in_app_or in Hin as [Hin|Hin]; [exact (proj1 (forallb_forall _ _) Hwc it Hin) | exact (proj1 (forallb_forall _ _) Hwy it Hin)].
  - intros rho HF Hpre Hwf Hnf.
    assert (Hn2 : bd_nn (common ++ X) rho).
    { unfold bd_nn in *. apply Forall_forall. intros it Hit. apply (proj1 (Forall_forall _ _) Hnf). eapply Permutation_in; [apply Permutation_sym; exact P1 | exact Hit]. }
    unfold bd_nn in Hn2. apply Forall_app in Hn2 as [Hnc Hnx].
    destruct (Hsem rho HF Hnx) as (Q1 & Q2 & Q6).
    unfold pay_sem. rewrite (bsumV_perm bfrom (common ++ X) rho P1), (bsumK_perm bfrom (common ++ X) rho P1).
    rewrite <- (bsumV_perm (common ++ Y) bto rho P2), <- (bsumK_perm (common ++ Y) bto rho P2).
    rewrite !bsumV_app, !bsumK_app. split; [lia|]. split; [lia|].
    unfold bd_nn. apply Forall_forall. intros it Hit.
    assert (Hin : In it (common ++ Y)) by (eapply Permutation_in; [apply Permutation_sym; exact P2 | exact Hit]).
    apply in_app_or in Hin as [Hin|Hin]; [exact (proj1 (Forall_forall _ _) Hnc it Hin) | exact (proj1 (Forall_forall _ _) Q6 it Hin)].
Qed.

Lemma pay_o3 : ltac2:(tb__ "0|1|
S1S2dS4S5R1A1S3S17S4dA1A1A3S72S50R2A2S75R3S8Z0M0A1G0S50S5cA5F_;F_;Fr;").
Proof.
  intros r HF Hnn.
  pose proof hv4_checks_o3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CNV & _).
  pose proof (holds_mem _ _ _ HF CNV) as FN. rewrite h_ule, uval_lit in FN by lia.
  pose proof (uval_range r c_av) as RC. pose proof (uval_range r k_acol) as RK.
  assert (E3 : uval r (SMd M_MUL (SLit 3) c_av) = 3 * uval r c_av) by (apply uval_mul_lit; lia).
  assert (E2 : uval r (SAlu ALU_ADD (SMd M_MUL (SLit 3) c_av) (SLit 2)) = 3 * uval r c_av + 2).
  { rewrite uval_add_small by (rewrite E3, uval_lit by lia; lia). rewrite E3, uval_lit by lia. reflexivity. }
  assert (E5 : uval r (SAlu ALU_ADD (SMd M_MUL (SLit 3) c_av) (SLit 5)) = 3 * uval r c_av + 5).
  { rewrite uval_add_small by (rewrite E3, uval_lit by lia; lia). rewrite E3, uval_lit by lia. reflexivity. }
  assert (A2 : uval r (SMd M_MUL (SLit 4) (SAlu ALU_ADD (SMd M_MUL (SLit 3) c_av) (SLit 2))) = 4 * (3 * uval r c_av + 2)).
  { rewrite uval_mul_lit by (rewrite ?E2; lia). rewrite E2. reflexivity. }
  assert (A5 : uval r (SMd M_MUL (SLit 4) (SAlu ALU_ADD (SMd M_MUL (SLit 3) c_av) (SLit 5))) = 4 * (3 * uval r c_av + 5)).
  { rewrite uval_mul_lit by (rewrite ?E5; lia). rewrite E5. reflexivity. }
  pose proof (uval_range r vLEN) as RL0. pose proof (uval_range r pNX) as RN0.
  unfold bd_nn, payX_o3 in Hnn. apply Forall_cons_iff in Hnn as [N1 N2]. apply Forall_cons_iff in N2 as [N2 _].
  unfold phi_old, LA, A1 in N1, N2. cbv beta iota delta [bival lfval aval bi_v bi_k bi_f bi_c] in N1, N2. rewrite A2 in N1.
  unfold pay_sem, payX_o3, payY_o3, phi_old, phi_new, LA, A1, bd_nn.
  cbv beta iota delta [bsumV bsumK bival lfval aval bi_v bi_k bi_f bi_c]. rewrite A2, A5. rewrite (uval_lit r 0) by lia.
  split; [lia|]. split; [lia|].
  constructor; [|constructor; [|constructor]]; cbv beta iota delta [bival lfval aval bi_v bi_k bi_f bi_c]; rewrite ?A5; lia.
Qed.

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
S77S1S9S22Q40A1A1S2fOF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
Sa3S15VAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S1cS87VCST;R1A2S1aS88Z0R2A2S89R2S96A2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S1cS87VXGL;R1A2S1aS88Z0R2A2S89R2S96A2A2F_;Fa;").
Hypothesis HXlits : ltac2:(tb__ "0|0|
S1cS97R1A1S87VXGL;R2A2F_;Fa;").
Hypothesis LFLAG : law_flag_stmt AInv.
Hypothesis LFSH : law_fshadow_stmt AInv.
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S9SaSaS1cS1cA2S1cA2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 7 BX.
Variable rho0 : valuation.
Let HNP : NP_okA NP := NP_okA_intro NP eq_refl.
Let HTOP : InitState.segs_top segs <= IMG_HI := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eb.Lib_arena_alloc.HTOP_ok.
Let P0 : ltac2:(tb__ "0|0|
S1OFr;") := ltac2:(tb__ "0|0|
S26VCST;VFB;VFF;A3").
Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S6eVAInv;VCST;VXGL;S7cVKc;Vrho0;VP0;VFB;VFF;VBX;S61Vnd;Ac").

Lemma HIN_o1 : ltac2:(tb__ "0|1|
S1S3aS77S1S9S22Q40A1A1S2fS2dS4S5R6A1S3S17S41A1A1A3VP0;Vrho0;A1S84S7cVrho0;R8A3VAInv;R7R6R5R4A4S66Vrho0;R8A2S8dRbS79S78R9A1A1A2S68VFB;RaA2S69VFF;RbA2S6cVFB;RcReSeSaS0S0A2S3bS49A3M0A4S8eRfG0A2S8fR10G0A2S6aVFF;RfR11S23A4S1aS91VCST;Vrho0;VFB;VFF;R12S3bS23S3cA8S1aS92VCST;VXGL;Vrho0;VFB;VFF;R12S3bS23S47A9S5fS8cVFB;R12S3bA3S90VFF;R12S23A3S32S31R12S3cR11A3S4aA2A3A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FAi;Fms;Frho;").
Proof using ALA HCST HXlits.
  intros rho ms Ai rho1 tp1 md1 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR.
  pose proof hv4_checks_o1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CR & CX & CLN & _ & W12 & W36 & W33 & W34).
  assert (HNk : tvinA FB Ai rho kept_o1) by (apply (tvinA_sublist FB Ai rho (kept_o1 ++ passed_o1)); [intros t Ht; apply in_or_app; left; exact Ht | exact HN]).
  assert (HDk : tvd rho kept_o1) by (exact (tvd_app_l rho kept_o1 passed_o1 HD)).
  assert (HZk : tvz rho kept_o1) by (apply (tvz_sublist rho (kept_o1 ++ passed_o1)); [intros t Ht; apply in_or_app; left; exact Ht | exact HZ]).
  split; [|split].
  - exact (lo_robjsF AInv CST ALA HCST FB FF rho0 Ai rho _ kept_o1 R_o1 rho1 tp1 md1 HM HF HP0 Hav HT HTK HNk HDk HZk HFR CLN lines_in_kept_o1 CR).
  - exact (lo_xrsF AInv CST XGL ALA HXlits FB FF rho0 Ai rho _ kept_o1 Xk_o1 rho1 tp1 md1 HM HF HP0 Hav HT HTK HNk HDk HZk HFR CX).
  - unfold OP1P.P0_op. rewrite !rw_call'. rewrite W12, W36, W33, W34.
    repeat change (bv_unsigned (eval rho ?e)) with (uval rho e).
    fact HF (SPUle vF (SLit 140737479964672)) HvF. rewrite h_ule, uval_lit in HvF by lia.
    assert (HinF : In (uval rho vF, fs_frame_size 5, uval rho vFL) (FFx FF rho frL)).
    { apply In_FFx. right. exists (vF, 5, vFL). split; [left; reflexivity | reflexivity]. }
    change (fs_frame_size 5) with 2048 in HinF.
    assert (EA : forall k, 0 <= k <= 2048 -> uval rho (SAlu ALU_ADD vF (SLit k)) = uval rho vF + k).
    { intros k Hk. rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia. reflexivity. }
    unfold alA. rewrite !EA by lia. unfold OP1.CM.
    repeat split; exists (uval rho vF), 2048, (uval rho vFL); (split; [exact HinF | lia]).
Qed.

Lemma HIN_o3 : ltac2:(tb__ "0|1|
S1S3aS77S1S9S22Q40A1A1S2fS2dS4S5R6A1S3S17S4dA1A1A3VP0;Vrho0;A1S84S7cVrho0;R8A3VAInv;R7R6R5R4A4S66Vrho0;R8A2S8dRbS79S78R9A1A1A2S68VFB;RaA2S69VFF;RbA2S6cVFB;RcReSeSaS0S0A2S4cS5bA3M0A4S8eRfG0A2S8fR10G0A2S6aVFF;RfR11S23A4S1aS91VCST;Vrho0;VFB;VFF;R12S4cS23S4eA8S1aS92VCST;VXGL;Vrho0;VFB;VFF;R12S4cS23S58A9S60S8cVFB;R12S4cA3S90VFF;R12S23A3S32S31R12S4eR11A3S5dA2A3A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FAi;Fms;Frho;").
Proof using ALA HCST HXlits.
  intros rho ms Ai rho1 tp1 md1 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR.
  pose proof hv4_checks_o3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CR & CX & CLN & _ & W12 & W36 & W33 & W34 & _).
  assert (HNk : tvinA FB Ai rho kept_o3) by (apply (tvinA_sublist FB Ai rho (kept_o3 ++ passed_o3)); [intros t Ht; apply in_or_app; left; exact Ht | exact HN]).
  assert (HDk : tvd rho kept_o3) by (exact (tvd_app_l rho kept_o3 passed_o3 HD)).
  assert (HZk : tvz rho kept_o3) by (apply (tvz_sublist rho (kept_o3 ++ passed_o3)); [intros t Ht; apply in_or_app; left; exact Ht | exact HZ]).
  split; [|split].
  - exact (lo_robjsF AInv CST ALA HCST FB FF rho0 Ai rho _ kept_o3 R_o3 rho1 tp1 md1 HM HF HP0 Hav HT HTK HNk HDk HZk HFR CLN lines_in_kept_o3 CR).
  - exact (lo_xrsF AInv CST XGL ALA HXlits FB FF rho0 Ai rho _ kept_o3 Xk_o3 rho1 tp1 md1 HM HF HP0 Hav HT HTK HNk HDk HZk HFR CX).
  - unfold OP3P.P0_op. rewrite !rw_call'. rewrite W12, W36, W33, W34.
    repeat change (bv_unsigned (eval rho ?e)) with (uval rho e).
    fact HF (SPUle vF (SLit 140737479964672)) HvF. rewrite h_ule, uval_lit in HvF by lia.
    assert (HinF : In (uval rho vF, fs_frame_size 5, uval rho vFL) (FFx FF rho frL)).
    { apply In_FFx. right. exists (vF, 5, vFL). split; [left; reflexivity | reflexivity]. }
    change (fs_frame_size 5) with 2048 in HinF.
    assert (EA : forall k, 0 <= k <= 2048 -> uval rho (SAlu ALU_ADD vF (SLit k)) = uval rho vF + k).
    { intros k Hk. rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia. reflexivity. }
    unfold alA. rewrite !EA by lia. unfold OP3.CM.
    repeat split; exists (uval rho vF), 2048, (uval rho vFL); (split; [exact HinF | lia]).
Qed.

Section X.
Variable TR : assn -> assn -> Prop.
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S20S16S1S9S22Q40A1A1S27S2dS4S5R3A1S3S17R4A1A1A3VTR;S1fS15R6R5R4R3A5R2A2M0F_;G0F_;FQ;Ftp;Frho;FS;FJ;").
Hypothesis TR_ex : forall (T : Type) (J : T -> jpredA) S rho tp (Q : assn),
  (forall x, TR (SPA segs (J x) S rho tp) Q) -> TR (SPA segs (fun r p t m => exists x, J x r p t m) S rho tp) Q.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S27S27S27S28R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_exw : forall (T : Type) (P : T -> assn) (Q : assn), (forall a, TR (P a) Q) -> TR (fun w => exists a, P a w) Q.
Hypothesis TR_pureP : ltac2:(tb__ "0|1|
S27OS27S28R4R1A1R4F_;Fw;R3VTR;R5R3A2M0F_;G0F_;F_;FQ;FX;FP;").
Hypothesis TR_callP : ltac2:(tb__ "0|5|
S20S20S16S16S33S9S6A1M0S9SaS16S34A2M1A1S9SaS0S0A2M2A1S27S1S9S22Q40A1A1M3G2S1eG2R1R5A3S1eG2R2S18RbA1A3F_;Fr;S19S12G0A1S37RaR9R8A3SfG0R7A2A3S19SdS36RbRaR9R8S2eG1S16S14S16S34A2R7A4A5ScA3S1G3VTR;S1fS15RfRdR2R1A5S35S15S7S17RdA1A1R2R1RaA5A2Ftp1;Frho1;S9S30A1M4S3aS2fS21S15R9R8R10SbG4S7aR3S7bR2R1A2A4A5R13RaR9R4R2A4R13S32S31RbRfS39R3RaR4A3A3R10A2RaR5R3A4F_;F_;Fmd;Fms;Ftr;S16S34G4S3aS2fS1G3G4S3aS2fS1eG1SbS16S34RaR9A4R14A3S21S15R12R11R19SbG4S7aR9S7bR8R7A2A4A5R1cR13R12RaR8A4S84S7S17R1aA1A1S32S31R14R18S39R9R13RaA3A3R19A2R8A3S21S15R9R8ReSbG4S7aR7S7bR6R5A2A4A5ReS32S31R16R1aS39RbR15RcA3A3R1bA2R15RaR9R8R6A6S1aS9fR17S39RcR16RdA3R1bR1cR1dR10R1eR19RbA9S1S85R18S39RdR17ReA3R1cR1dS17R1eA1S17R1fA1S17R11A1R1RcA9VTR;S1fS15S38R11S32S31R19R1dS39ReR18RfA3A3R1eA2R18RdRcA5Sa0R1eR1fR12R20R1dR1bA6R2RcA5R1aA2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S1fS15R11RfR8R7A5R9A2F_;F_;F_;F_;F_;F_;Ftp;Frho;FQ;FXk;FPosts;FR;Fs;FPre;FC;FJp;FJ;").
Hypothesis CHOP1 : ltac2:(tb__ "0|1|
S9SaS1cS1cA2M0A1S9SaG0S1cA2A1S74S1S9S22Q40A1A1S71Z4R3A2VTR;S1fS15S64VAInv;VCST;VXGL;VKc;S5fR6R5A2R6R5R4S61S94S8aScS9bA3AaS9aR3R2A5S35S15S86R3R2S95VAInv;VCST;VXGL;VKc;S5fS61S42R6R5R4AaA5A2F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").

Lemma site_o1 : ltac2:(tb__ "0|7|
S1S9S22Q40A1M0A1M1S27S19SdS6fVXGL;S3S17S46A1A1S40Z4M2Z1eM3S3dA6ScA3S19SdS6fVXGL;S3S17S44A1A1S3fG2G3S3dA6ScA3S24R5A1S1G1S24R2A1M4S1dS1eS1dR1S25A3M5S19G0S2R5R2A2M6S2RbR2A2A3F_;Fv;VTR;S1fS15VJAv;S3eA1S45R4R3A5R8A2F_;F_;Ftp';Frho';S1G1G4S1dG5S19G0G6S2RcR2A2A3F_;Fv;VTR;S1fS15VJAv;S48A1S43R4R3A5R9A2F_;F_;Ftp';Frho';VTR;S1fS15VJAv;S8bA1S98R8R7A5R6A2F_;F_;F_;F_;F_;FQ;Ftp;Frho;").
Proof using ALA HCST HXGL HXlits LFSH HKc HBX TR_facts TR_ex TR_pre TR_exw TR_pureP TR_callP CHOP1.
  intros rho tp Q CXR1 CXR0 HPHI K1 K0.
  pose proof hv4_checks_o1 as (Cxf & Cent & Cchk & Cta & Cdom & Ctvs & Cam & Cpd & Cptv & Cpbd & Cxk & Chand & PP1 & PP2 & PWc & PPay & Cnb & Cbr & Cnp & _ & _ & CLN & CVB & _).

  assert (CREL : rel_chkG tv_keep bd_keep [(160, 4); (176, 4)] E_o1 E_o1r).
  { pose proof hv4_checks_rel as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & _). exact (conj R1 (conj R2 (conj R3 (conj R4 (conj R5 (conj R6 (conj R7 R8))))))). }
  unfold nd_keep.
  apply (site_relG AInv CST XGL ALA HCST HXGL LFSH Kc HKc FB FF BX HBX rho0 TR TR_facts TR_pre TR_exw TR_pureP
           tv_keep bd_keep [(160, 4); (176, 4)] E_o1 E_o1r rho tp Q CREL lines_in_tv_keep HPHI). intros rho1 HPHI1 HV1.

  set (ndv := NDA tv_o1 frL bd_o1 (AHead pH true)).
  apply (TR_pre (SPA segs (JAv ndv) E_o1c rho1 tp)).
  { intros w Hw. apply (SPA_axforms segs (JAv ndv) (xf_o1 E_o1r) rho1 E_o1r E_o1c tp w Cxf).
    unfold ndv. apply (SPA_bd_permb segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue _ frL bd_keep bd_o1 _ E_o1r rho1 tp w Cpbd).
    apply (SPA_tv_permb segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tv_keep _ frL bd_keep _ E_o1r rho1 tp w Cptv). exact Hw. }
  apply TR_facts. intros HF.
  apply (TR_pureP _ (uval rho1 xLD <> 0 /\ uval rho1 pI < uval rho1 xLC /\ uval rho1 xLC <= uval rho1 xLK /\ 16 * uval rho1 xLK <= 4294967295
                     /\ uval rho1 xLD + 16 * uval rho1 xLK <= 2 ^ 47)).
  { intros [tr [ms md]] [_ (Ai & kc & Hav & _ & _ & HT & _ & _ & (_ & _ & HZ) & _)]. cbn [nd_tv ndv] in HZ.
    pose proof (T_of_TPA NP rho0 rho1 Ai Hav ltac:(reflexivity) HT) as HTK. pose proof (topG_range (aa_geom Ai)) as TG.
    destruct (lines_blk rho1 _ (topG (aa_geom Ai)) HF CLN HTK) as (_ & HiC & HcK & Hk32 & _ & HdT).
    split; [|repeat split; lia].
    exact (lines_nz rho1 _ (topG (aa_geom Ai)) tv_o1 HF CLN HTK HZ lines_in_tv_o1). }
  intros (Hdnz & HiC & HcK & Hk32 & HdT).
  unfold ndv, tv_o1.
  apply (client_callT_k segs AInv CST XGL ALA HCST HXGL NP Kc rho0 P0 FB FF BX PTrue HKc HBX OP1P.P0_op PTrue (fun _ H => H) (fun _ _ _ H => H)
           OP1.Pre_op (ndh h0 true OP1.nd0) PDk_o1 NF eq_refl eq_refl eq_refl TR TR_facts TR_ex TR_pre TR_callP CHOP1 eq_refl
           E_o1c s_o1c R_o1 Xk_o1 rho1 tp kept_o1 passed_o1 frL bd_o1 brest_o1 (AHead pH true) Q
           Cxk Cent Cchk Cta Cdom Cnp Cnb Cbr Ctvs Cam).
  - rewrite Chand. unfold payA. apply (pay_okF_split _ _ _ _ bd_o1 _ payC_o1 payX_o1 payY_o1 PP1 PP2 PWc PPay).
  - exact Cpd.
  - intros Ai ms HF' HP0 Hav HBf HFF HN HD HZ HFR (rho2 & tp2 & md2 & HM) HT HTK.
    exact (HIN_o1 rho1 ms Ai rho2 tp2 md2 HF' HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR).
  -
    intros [[Ld ndL] PsiL] rho' tp' Hd Hag HK _.
    assert (HV' : forall v, In v V_B -> rw rho' v = rw rho v).
    { intros v Hv. rewrite (V_B_agree_n _ rho1 rho' CVB Hag v Hv). exact (HV1 v Hv). }
    assert (HPHI' : tblB rho').
    { apply (tblB_kept rho1 rho' (V_B_agree_n _ rho1 rho' CVB Hag)); [| exact HiC | exact HcK | exact HPHI1].
      apply (keptK_lines CST FB FF rho0 rho1 kept_o1 frL rho' HK lines_in_kept_o1 Hdnz); [exact HdT | unfold B32, Lib_vec_reserve.B32; lia]. }
    pose proof hv4_checks_o1_nd as (N1 & N0 & T10 & T00 & B1 & B0 & Ti1 & Ti0 & REO1 & REO0 & _).
    cbn [PDk_o1 liftPD PDh OP1.PD_op map In fst snd] in Hd. destruct Hd as [Hd|[Hd|[]]]; injection Hd as <- <- <-; cbn [fst snd].
    +
      rewrite T10, N1.
      apply (TR_pre (SPA segs (JAv nd_op1) T_op1 rho' tp')); [|exact (K1 rho' tp' HPHI' HV')].
      intros w Hw.
      apply (SPA_reopen_lo AInv CST XGL ALA HCST HXGL HXlits LFSH Kc HKc FB FF BX HBX rho0 tv_op1 bd_op1 X_1 T_op1r T_op1 rho' tp' w REO1 lines_in_tv_op1 CXR1).
      rewrite <- Ti1. apply SPA_tidy. exact (SPA_axforms segs (JAv nd_op1) (xfb_o1 T_op1_0) rho' T_op1_0 B_op1 tp' w B1 Hw).
    +
      rewrite T00, N0.
      apply (TR_pre (SPA segs (JAv nd_op0) T_op0 rho' tp')); [|exact (K0 rho' tp' HPHI' HV')].
      intros w Hw.
      apply (SPA_reopen_lo AInv CST XGL ALA HCST HXGL HXlits LFSH Kc HKc FB FF BX HBX rho0 tv_op0 brest_o1 X_1 T_op0r T_op0 rho' tp' w REO0 lines_in_tv_op0 CXR0).
      rewrite <- Ti0. apply SPA_tidy. exact (SPA_axforms segs (JAv nd_op0) (xfb_o1 T_op0_0) rho' T_op0_0 B_op0 tp' w B0 Hw).
Qed.

Hypothesis CMEMCPYR : ltac2:(tb__ "0|2|
S77S1S9S22Q40A1A1M0VTR;S1fS15S1G0S9S30A1S2fS1aSa2VAInv;R7VKc;R4R3R2R1A7S1bA2Lm;Lt;Lp;Lr;S7dR2R1A5S35S15S86R2R1S10SaS16S34A2M1SbS16S34S7eSa1VAInv;VCST;VXGL;R3VKc;A5A4S11G1A1A3A5A2Ftp1;Frho1;FAi;").
Lemma w_ok_ent : ltac2:(tb__ "0|3|
S16S19SdS83R1A1ScA3S1aS19S12S9S6A1M0A1S37R2S7dS81R2A1M1A3SfG0S80R2A1M2A2A3S19SdS36R2S7dG1G2S10S16S7eS11S16A1A3A5ScA3A2F_;FE;").
Proof using . intros E H. unfold w_ok, R_w in *. destruct (entails_frA E PreR (s_w E)) as [R|]; [split; [reflexivity | exact H] | discriminate]. Qed.
Lemma site_w : ltac2:(tb__ "0|4|
S9SaS0S0A2M0A1S9S70A1S16S16S16S16S16S16S1S9S22Q40A1M1A1M2S27S82RbRaR9R8R7R6R5R4A8S1eG0SbS0S0S2aS29Z10S2bA2A4RcA3S24R5A1S1G2S24R2A1S1dS1eS1dR1S25A3S19G1S2R5R2A2S2RbR2A2A3F_;Fv;VTR;S1fS15VJAv;S65R12S23R11S6dS2cScA2M3A4A1RbR4R3A5R8A2F_;F_;Ftp';Frho';VTR;S1fS15VJAv;S65RfS23ReG3A4A1RdR7R6A5R5A2F_;F_;F_;F_;FQ;Ftp;Frho;FT;FTb;FT0;FE;FEr;FL;Fbd;Ftv;").
Proof using ALA HCST HXGL HXlits LFSH HKc HBX TR_facts TR_ex TR_pre TR_exw TR_pureP TR_callP CMEMCPYR.
  intros tv bd L Er E T0 Tb T rho tp Q
    (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & Cxf & Cok & Cta & Cnp & Cnb & Cbb & Cwp & Cpp & CR & CX & CLN & CVE & CT0 & CTb & CT & _) Hlin HPHI HK.
  destruct (w_ok_ent E Cok) as [Cent Cchk].
  set (nd := NDA tv frL bd (AHead pH true)).
  assert (CREL : rel_chkG tv bd [(192, 12); (224, 12)] L Er) by (exact (conj R1 (conj R2 (conj R3 (conj R4 (conj R5 (conj R6 (conj R7 R8)))))))).
  apply (site_relG AInv CST XGL ALA HCST HXGL LFSH Kc HKc FB FF BX HBX rho0 TR TR_facts TR_pre TR_exw TR_pureP
           tv bd [(192, 12); (224, 12)] L Er rho tp Q CREL Hlin HPHI). intros rho1 HPHI1 HV1.
  apply (TR_pre (SPA segs (JAv nd) E rho1 tp)). { intros w Hw. exact (SPA_axforms segs (JAv nd) (xf_w Er) rho1 Er E tp w Cxf Hw). }
  apply TR_facts. intros HF1.
  apply (TR_pureP _ (uval rho1 xLD <> 0 /\ uval rho1 pI < uval rho1 xLC /\ uval rho1 xLC <= uval rho1 xLK /\ uval rho1 (kb 16 xLK) = 16 * uval rho1 xLK)).
  { intros [tr [ms md]] [_ (Ai & kc & Hav & _ & _ & HT & _ & _ & (_ & _ & HZ) & _)]. cbn [nd_tv nd] in HZ.
    pose proof (T_of_TPA NP rho0 rho1 Ai Hav ltac:(reflexivity) HT) as HTK.
    destruct (lines_blk rho1 _ (topG (aa_geom Ai)) HF1 CLN HTK) as (_ & HiC & HcK & _ & EK & _).
    split; [exact (lines_nz rho1 _ (topG (aa_geom Ai)) tv HF1 CLN HTK HZ Hlin) | split; [exact HiC | split; [exact HcK | exact EK]]]. }
  intros (Hdnz & HiC & HcK & EK).
  apply (purec_callT_k_xp segs AInv CST XGL ALA HCST HXGL NP Kc rho0 P0 FB FF BX PTrue HKc TR TR_facts TR_ex TR_pre TR_callP
           (fun _ _ => True) PreR [LR] E (s_w E) (R_w E) rho1 tp nd bd Q).
  - intros Ai rho2 tp2. cbn [map]. exact (CMEMCPYR Ai rho2 tp2).
  - reflexivity.
  - reflexivity.
  - exact Cent.
  - exact Cchk.
  - exact Cta.
  - exact Cnp.
  - exact Cnb.
  - exact Cbb.
  - cbn [nd_bd nd]. apply payA_same. exact Cwp.
  - exact Cpp.
  - exact (site_rt_lo AInv CST XGL ALA HCST HXlits FB FF rho0 E (s_w E) (R_w E) rho1 tv bd (AHead pH true) CR CX CLN Hlin).
  - intros Ai tr ms md _ _ _. exact I.
  - intros L' rho2 tp2 HL Hag HKR. destruct HL as [<-|[]]. cbn [nd_tv nd_fr nd_am nd].
    change (T_afterA PreR E (s_w E) (R_w E) LR) with (T_wc E). rewrite CT0.
    assert (HV2 : forall v, In v V_B -> rw rho2 v = rw rho v).
    { intros v Hv. rewrite (V_B_agree_n _ rho1 rho2 CVE Hag v Hv). exact (HV1 v Hv). }
    apply (TR_pre (SPA segs (JAv nd) T rho2 tp2)).
    { intros w Hw. rewrite <- CT. apply SPA_tidy. exact (SPA_axforms segs (JAv nd) (xfb_w T0) rho2 T0 Tb tp2 w CTb Hw). }
    apply (HK rho2 tp2); [|exact HV2].
    apply (tblB_kept rho1 rho2 (V_B_agree_n _ rho1 rho2 CVE Hag)); [| exact HiC | exact HcK | exact HPHI1].
    intros z Hz. apply (HKR (xLD, kb 16 xLK) z Hlin); [unfold tnz; cbn [fst]; exact Hdnz|].
    unfold tvv. cbn [fst snd]. change (bv_unsigned (eval rho1 xLD)) with (uval rho1 xLD). change (bv_unsigned (eval rho1 (kb 16 xLK))) with (uval rho1 (kb 16 xLK)).
    rewrite EK. exact Hz.
Qed.

Hypothesis CHOP3 : ltac2:(tb__ "0|1|
S9SaS1cS1cA2M0A1S9SaG0S1cA2A1S74S1S9S22Q40A1A1S71Z4R3A2VTR;S1fS15S64VAInv;VCST;VXGL;VKc;S60R6R5A2R6R5R4S61S94S8aScS9eA3AaS9dR3R2A5S35S15S86R3R2S95VAInv;VCST;VXGL;VKc;S60S61S53R6R5R4AaA5A2F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Lemma site_o3 : ltac2:(tb__ "0|7|
S1S9S22Q40A1M0A1M1S27S19SdS6fVXGL;S3S17S57A1A1S52Z4M2Z1eM3S4fA6ScA3S19SdS6fVXGL;S3S17S55A1A1S51G2G3S4fA6ScA3S24R5A1S1G1S24R2A1M4S1dS1eS1dR1S25A3M5S19G0S2R5R2A2M6S2RbR2A2A3F_;Fv;VTR;S1fS15VJAv;S5aA1S56R4R3A5R8A2F_;F_;Ftp';Frho';S1G1G4S1dG5S19G0G6S2RcR2A2A3F_;Fv;VTR;S1fS15VJAv;S59A1S54R4R3A5R9A2F_;F_;Ftp';Frho';VTR;S1fS15VJAv;S3eA1S7fR8R7A5R6A2F_;F_;F_;F_;F_;FQ;Ftp;Frho;").
Proof using ALA HCST HXGL HXlits LFSH HKc HBX TR_facts TR_ex TR_pre TR_pureP TR_callP CHOP3.
  intros rho tp Q CXR1 CXR0 HPHI K1 K0.
  pose proof hv4_checks_o3 as (Cxf & Cent & Cchk & Cta & Cdom & Ctvs & Cam & Cpd & Cptv & Cpbd & Cxk & Chand & PP1 & PP2 & PWc & PWy & _ & Cnb & Cbr & Cnp & _ & _ & CLN & CVB & _).
  set (ndv := NDA tv_o3 frL bd_o3 (AHead pH true)).
  apply (TR_pre (SPA segs (JAv ndv) E_o3c rho tp)).
  { intros w Hw. apply (SPA_axforms segs (JAv ndv) (xf_o3 E_o3) rho E_o3 E_o3c tp w Cxf).
    unfold ndv. apply (SPA_bd_permb segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue _ frL bd_op1 bd_o3 _ E_o3 rho tp w Cpbd).
    apply (SPA_tv_permb segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tv_op1 _ frL bd_op1 _ E_o3 rho tp w Cptv). exact Hw. }
  apply TR_facts. intros HF.
  apply (TR_pureP _ (uval rho xLD <> 0 /\ uval rho pI < uval rho xLC /\ uval rho xLC <= uval rho xLK /\ 16 * uval rho xLK <= 4294967295
                     /\ uval rho xLD + 16 * uval rho xLK <= 2 ^ 47)).
  { intros [tr [ms md]] [_ (Ai & kc & Hav & _ & _ & HT & _ & _ & (_ & _ & HZ) & _)]. cbn [nd_tv ndv] in HZ.
    pose proof (T_of_TPA NP rho0 rho Ai Hav ltac:(reflexivity) HT) as HTK. pose proof (topG_range (aa_geom Ai)) as TG.
    destruct (lines_blk rho _ (topG (aa_geom Ai)) HF CLN HTK) as (_ & HiC & HcK & Hk32 & _ & HdT).
    split; [|repeat split; lia].
    exact (lines_nz rho _ (topG (aa_geom Ai)) tv_o3 HF CLN HTK HZ lines_in_tv_o3). }
  intros (Hdnz & HiC & HcK & Hk32 & HdT).
  unfold ndv, tv_o3.
  apply (client_callT_k segs AInv CST XGL ALA HCST HXGL NP Kc rho0 P0 FB FF BX PTrue HKc HBX OP3P.P0_op PTrue (fun _ H => H) (fun _ _ _ H => H)
           OP3.Pre_op (ndh h0 true OP3.nd0) PDk_o3 NF eq_refl eq_refl eq_refl TR TR_facts TR_ex TR_pre TR_callP CHOP3 eq_refl
           E_o3c s_o3c R_o3 Xk_o3 rho tp kept_o3 passed_o3 frL bd_o3 brest_o3 (AHead pH true) Q
           Cxk Cent Cchk Cta Cdom Cnp Cnb Cbr Ctvs Cam).
  - rewrite Chand. unfold payA.
    apply (pay_okF_split_sem _ _ (SLit 0) 0 bd_o3 _ payC_o3 payX_o3 payY_o3 PP1 PP2 PWc PWy (Z.le_refl 0)). intros r HFr Hnn. exact (pay_o3 r HFr Hnn).
  - exact Cpd.
  - intros Ai ms HF' HP0 Hav HBf HFF HN HD HZ HFR (rho2 & tp2 & md2 & HM) HT HTK.
    exact (HIN_o3 rho ms Ai rho2 tp2 md2 HF' HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR).
  - intros [[Ld ndL] PsiL] rho' tp' Hd Hag HK _.
    assert (HV' : forall v, In v V_B -> rw rho' v = rw rho v) by (exact (V_B_agree_n _ rho rho' CVB Hag)).
    assert (HPHI' : tblB rho').
    { apply (tblB_kept rho rho' (V_B_agree_n _ rho rho' CVB Hag)); [| exact HiC | exact HcK | exact HPHI].
      apply (keptK_lines CST FB FF rho0 rho kept_o3 frL rho' HK lines_in_kept_o3 Hdnz); [exact HdT | unfold B32, Lib_vec_reserve.B32; lia]. }
    pose proof hv4_checks_o3_nd as (N1 & N0 & T10 & T00 & B1 & B0 & Ti1 & Ti0 & REO1 & REO0 & _).
    cbn [PDk_o3 liftPD PDh OP3.PD_op map In fst snd] in Hd. destruct Hd as [Hd|[Hd|[]]]; injection Hd as <- <- <-; cbn [fst snd].
    + rewrite T10, N1.
      apply (TR_pre (SPA segs (JAv nd_p1) T_p1 rho' tp')); [|exact (K1 rho' tp' HPHI' HV')].
      intros w Hw.
      apply (SPA_reopen_lo AInv CST XGL ALA HCST HXGL HXlits LFSH Kc HKc FB FF BX HBX rho0 tv_p1 bd_p1 X_3 T_p1r T_p1 rho' tp' w REO1 lines_in_tv_p1 CXR1).
      rewrite <- Ti1. apply SPA_tidy. exact (SPA_axforms segs (JAv nd_p1) (xfb_o3 T_p1_0) rho' T_p1_0 B_p1 tp' w B1 Hw).
    + rewrite T00, N0.
      apply (TR_pre (SPA segs (JAv nd_p0) T_p0 rho' tp')); [|exact (K0 rho' tp' HPHI' HV')].
      intros w Hw.
      apply (SPA_reopen_lo AInv CST XGL ALA HCST HXGL HXlits LFSH Kc HKc FB FF BX HBX rho0 tv_p0 brest_o3 X_3 T_p0r T_p0 rho' tp' w REO0 lines_in_tv_p0 CXR0).
      rewrite <- Ti0. apply SPA_tidy. exact (SPA_axforms segs (JAv nd_p0) (xfb_o3 T_p0_0) rho' T_p0_0 B_p0 tp' w B0 Hw).
Qed.
End X.
End Sum.
End Lib_load_obj_hv_pf5.

(* [comment removed for export] *)
Module Lib_load_obj_hv4f.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "and"; "eq"; "@Corelib.Init.Datatypes"; "bool"; "true"; "cons"; "nil"; "prod"; "app"; "option"; "pair"; "fst"; "length"; "list"; "Some"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "SPUle"; "sprop_eqb"; "SLit"; "SAlu"; "cell"; "sobj"; "ss_facts"; "ss_next"; "sv_eqb"; "SMd"; "c_off"; "c_val"; "c_width"; "mkCell"; "mkObj"; "ob_base"; "ob_cells"; "ob_dflt"; "ob_hi"; "ob_lo"; "sprop_below"; "ss_objs"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bitem"; "@Stdlib.Lists.List"; "existsb"; "find"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_setS"; "axst"; "@Corelib.Lists.ListDef"; "map"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "M_MUL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.et.Lib_load_obj_hv3f"; "lx_chk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ff.Lib_load_obj_hv4f"; "X_lokR"; "Xs_v"; "Ys_v"; "lr_chk"; "X_l1R"; "X_l3R"; "bdX_v"; "comm_v"; "X_l1S"; "X_l1b"; "X_l1r"; "X_l3S"; "X_l3b"; "X_l3r"; "X_lokS"; "X_lokb"; "X_lokr"; "av_cell_new"; "av_cell_old"; "nv1"; "rate_nv1"; "s_l1"; "s_l3"; "s_lok"; "tvj_l1"; "tvj_l3"; "tvj_lok"; "upd_cellv"; "upd_objv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop"; "pPOS"; "pLNL"; "pNX"; "X_latch"; "pE0"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud"; "LAX"; "LAXK"; "bdX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs"; "vLEN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_hv3"; "c_av"; "objs_nl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_loopE"; "X_latchE2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG"; "bd_permb"; "@Stdlib.Arith.PeanoNat.Nat"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fc.Lib_load_obj_hv4"; "brest_o1"; "tv_op0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fb.Lib_load_obj_hv4e"; "X_l1"; "X_l3"; "X_lok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ew.Lib_load_obj_hv4p"; "bd_p1"; "brest_o3"; "tv_p0"; "tv_p1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue"; "tvL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "sv_subst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF"; "bud_pay2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS"; "shadow_release_stateA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CFGA GlueA SummaryA SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAS TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require ObjEmptyA PinA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.TobjJAH OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.ObjZeroA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ObjEmptyA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.PinA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.AddCellsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_opt_push1 Lib_opt_push3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.Asan_memcpyR_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_defs Lib_load_obj_pro.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require et.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ew.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fb.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eo.Lib_load_obj_pro2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_hv0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_hv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_hvj OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_hvkit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_hv3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f7.Lib_load_obj_hv3m OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fa.Lib_load_obj_hv3e OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_loopE OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.et.Lib_load_obj_hv3f OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fc.Lib_load_obj_hv4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fd.Lib_load_obj_hv4w OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ew.Lib_load_obj_hv4p OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fb.Lib_load_obj_hv4e.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr HVAddr.

Definition av_cell_old : sv := ltac2:(tb__ "0|1|
S13S2fS19S30S5aS12Z3A1M0A3G0A3").
Definition nv1 : sv := SAlu ALU_ADD c_av (SLit 1).
Definition av_cell_new : sv := SMd M_MUL nv1 (SLit 3).
Definition upd_cellv (old new : sv) (c : cell) : cell := ltac2:(tb__ "0|0|
S2S14L_;S18S1bVc;A1Vold;A2S1dS1aVc;A1S1cVc;A1Vnew;A3Vc;X2x2").
Definition upd_objv (old new : sv) (o : sobj) : sobj := ltac2:(tb__ "0|0|
S1eS1fVo;A1S23Vo;A1S22Vo;A1S2eS14S14S4dVold;Vnew;A2S20Vo;A1A4S21Vo;A1A5").
Definition restate_cells (old new : sv) (A : axst) : axst := ltac2:(tb__ "0|1|
S2cVA;S6bS2bVA;A1M0S2eS15S15S4eVold;Vnew;A2S25G0A1A4A2A2").
Definition rate_nv1 : sprop := ltac2:(tb__ "0|0|
S10S45S13S2fS53S12Z1A1A3A2").

Definition lr_chk (L R LR : axst) : Prop := ltac2:(tb__ "0|b|
S0S1S2S26S2bVR;A1M0A1S3A3S0S1S8S6ScS6SeSeA2M1A1M2ScSfA1M3A2M4A1S69S2bVL;A1M5G0A2SdG4S9G2G3S4G1S9SeSeS44S43A4S5G1A1A3S5SfA1M6A4A2A3S0S1S55S17G0A1M7S17G5A1A3S0S1S2dS2cVL;G0A2VR;A3S0S1S2dS6cVR;S7SfS4SfS46G6A3S16G0A1M8A3M9A2VLR;A3S0S1S2S2aSfS24G7A1G9A3S3A3S0S1S2S28SfS11S10S5aS51A2A1G8A3S3A3S0S1S2S28SfS11S10S51S4fA2A1G8A3S3A3S0S1S2S28SfS11S10S13S2fS4fS50A3S59A2A1G8A3S3A3S0S1S2S28SfS11S10S59S12Z4000000A1MaA2A1G8A3S3A3S0S1S2S28SfS11S10S4fGaA2A1G8A3S3A3S1S2S28SfS11S10S50GaA2A1G8A3S3A3A2A2A2A2A2A2A2A2A2A2A2").
Definition relr (L : axst) : axst := ltac2:(tb__ "0|0|
S6eVL;S5bVL;A1P6eS5S6S54S54A2A1A4").
Definition tvj_of (s : wsub) (tv : list (sv * sv)) : list (sv * sv) := ltac2:(tb__ "0|2|
S2eS6SeSeA2M0G0G0S8G0A1G0Lx;S29G0G0S18S6aVs;SaSeSeR1A3A2SaSeSeR2A3A2Ltj;S68A3G0R1Lx;S9SeSeS12Z0A1M1G1A4X8x2Lt;Vtv;A4").

Definition X_l1S : axst := Eval vm_compute in restate_cells av_cell_old av_cell_new X_l1.
Definition X_l1R : axst := Eval vm_compute in ax_add_facts [rate_nv1] X_l1S.
Definition X_l1r : axst := Eval vm_compute in relr X_l1R.
Definition X_l1b : axst := Eval vm_compute in optL' (apply_axforms X_l1r (xf_tail X_l1r)).
Definition s_l1 : wsub := Eval vm_compute in infer_sub NP (ax_S X_l1b) (ax_S X_latchE2).
Definition tvj_l1 : list (sv * sv) := Eval vm_compute in tvj_of s_l1 tv_op0.
Lemma hv4_checks_l1 : ltac2:(tb__ "0|1|
S0S35S61S3aS36A3S31S60S5fS4aS4S27S56Z0M0A1S4S27S57G0A1S5S27A1A3A3S5cS36S3cS3bS47A9A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition X_l3S : axst := Eval vm_compute in restate_cells av_cell_old av_cell_new X_l3.
Definition X_l3R : axst := Eval vm_compute in ax_add_facts [rate_nv1] X_l3S.
Definition X_l3r : axst := Eval vm_compute in relr X_l3R.
Definition X_l3b : axst := Eval vm_compute in optL' (apply_axforms X_l3r (xf_tail X_l3r)).
Definition s_l3 : wsub := Eval vm_compute in infer_sub NP (ax_S X_l3b) (ax_S X_latchE2).
Definition tvj_l3 : list (sv * sv) := Eval vm_compute in tvj_of s_l3 tv_p0.
Lemma hv4_checks_l3 : ltac2:(tb__ "0|1|
S0S35S62S3dS37A3S31S66S65S4bS4S27S56Z0M0A1S4S27S57G0A1S5S27A1A3A3S5cS37S3fS3eS48A9A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition X_lokS : axst := Eval vm_compute in restate_cells av_cell_old av_cell_new X_lok.
Definition X_lokR : axst := Eval vm_compute in ax_add_facts [rate_nv1] X_lokS.
Definition X_lokr : axst := Eval vm_compute in relr X_lokR.
Definition X_lokb : axst := Eval vm_compute in optL' (apply_axforms X_lokr (xf_tail X_lokr)).
Definition s_lok : wsub := Eval vm_compute in infer_sub NP (ax_S X_lokb) (ax_S X_latch).
Definition tvj_lok : list (sv * sv) := Eval vm_compute in tvj_of s_lok tv_p1.
Definition bdX_v : list bitem := Eval vm_compute in bd_subst s_lok (bdX 0).
Definition comm_v : list bitem := Eval vm_compute in bd_common bd_p1 bdX_v.
Definition Xs_v : list bitem := Eval vm_compute in bd_minus bd_p1 bdX_v.
Definition Ys_v : list bitem := Eval vm_compute in bd_minus bdX_v bd_p1.
Lemma hv4_checks_lok : ltac2:(tb__ "0|2|
S0S35S63S40S32A3S0S1S2S5dS64S7S27S39S33A3A2S3A3S0S1S2S5dS7S27S39S34A3S38A2S3A3S0S1S2S6dS16S2bS32A1A1S12Z0M0A1G0S33S34A5S3A3S0S1S2S5eSbS27S33A2U8M1A2S3A3S0S1S2S5eSbS27S34A2G1A2S3A3S31S67S38S4cS58G0A1S52S32S42S41S49A9A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
End Lib_load_obj_hv4f.

(* [comment removed for export] *)
Module Lib_load_obj_hv_pf6.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@Corelib.Init.Datatypes"; "list"; "prod"; "pair"; "nat"; "true"; "bool"; "cons"; "nil"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sv"; "sprop"; "SPUle"; "sprop_eqb"; "ss_facts"; "eval"; "holds"; "SAlu"; "SLit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "PTrue"; "JA_pre"; "NDA"; "AHead"; "JA"; "ok_frameKA"; "@Corelib.Init.Logic"; "eq"; "and"; "True"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue"; "tblB"; "frL"; "P0_lo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "assn"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@Stdlib.Lists.List"; "existsb"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF"; "efmeasA"; "phiK"; "JAF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_hv3"; "h0"; "nd_keep"; "c_av"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ff.Lib_load_obj_hv_pf5.OP1P"; "P0_op"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ff.Lib_load_obj_hv_pf5.OP3P"; "P0_op"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ez.Lib_load_obj_hvpk"; "xrs_chkRo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "BXok_d"; "bxt"; "bitem"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.TobjJAH"; "ndh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK"; "PostsCk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "AE_A"; "JL_pure"; "J_pure_pre"; "alloc_contractsA"; "alloc_contractsA_ex"; "alloc_lawsA"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud"; "RL"; "VLA"; "ndA1"; "ndX0"; "ndXE"; "z0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_hv0"; "E_hv0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f7.Lib_load_obj_hv3m"; "E_o1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop"; "X_latch"; "pPOS"; "pLNL"; "pNX"; "pH"; "xLD"; "xLK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_loopE"; "X_latchE2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.Asan_memcpyR_iface"; "white_hv"; "memcpyR_contractA"; "memcpyR_contractA_ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs"; "NP"; "vLEN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fc.Lib_load_obj_hv4.OP1"; "Pre_op"; "nd0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fc.Lib_load_obj_hv4"; "PDk_o1"; "X_1"; "T_op0r"; "T_op1r"; "tv_op0"; "tv_op1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fb.Lib_load_obj_hv4e"; "cutsH4"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ew.Lib_load_obj_hv4p.OP3"; "Pre_op"; "nd0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ew.Lib_load_obj_hv4p"; "PDk_o3"; "X_3"; "tv_p1"; "T_p0r"; "T_p1r"; "tv_p0";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fd.Lib_load_obj_hv4w"; "LR"; "PreR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_hvkit"; "PhisH"; "mH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "@Corelib.Lists.ListDef"; "Forall"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs"; "kb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_fuzz_iface"; "in_lits"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ff.Lib_load_obj_hv4f"; "av_cell_new"; "av_cell_old"; "lr_chk"; "rate_nv1"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia Permutation.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CFGA GlueA SummaryA SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV TobjArena ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TobjJVA InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAS TobjJAT TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require ObjEmptyA PinA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAM2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAFb OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.TobjJAH OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.ObjZeroA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ObjEmptyA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.PinA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.AddCellsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eg.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_rom_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e8.Lib_scan_double_ex OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eh.Lib_builder_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eg.Lib_builderH_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_rom_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.Lib_diag_append.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ej.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eb.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ej.Lib_build_line_index_rom_call OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eb.Lib_vec_reserve_pf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_opt_push1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ei.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_opt_push3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e2.Asan_memcpyR_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_defs Lib_load_obj_pro.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ez.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require es.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require et.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ew.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fb.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eo.Lib_load_obj_pro2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_hv0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_hv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_hvj OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_hvkit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ez.Lib_load_obj_hvpk OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f4.Lib_load_obj_hv2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.es.Lib_load_obj_hv_pf1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_hv3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f7.Lib_load_obj_hv3m OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fa.Lib_load_obj_hv3e OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_loopE OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.et.Lib_load_obj_hv3f OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fa.Lib_load_obj_hv_pf3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ew.Lib_load_obj_hv_pf4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fc.Lib_load_obj_hv4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fd.Lib_load_obj_hv4w OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ew.Lib_load_obj_hv4p OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fb.Lib_load_obj_hv4e OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ff.Lib_load_obj_hv4f OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ff.Lib_load_obj_hv_pf5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f4.Lib_load_obj_hv1c OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ez.Lib_load_obj_hv1e OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ff.Lib_load_obj_hv_pf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ScanDoubleAddr DiagAppendAddr LOAddr LOLAddr HVAddr.

Ltac inl := cbn [In]; repeat (first [left; reflexivity | right]).
Lemma av_cell_eq : ltac2:(tb__ "0|0|
SaS1fS16Q40A1S10R1S78A2S10R1S77A2A3Frho;").
Proof.
  intros rho. unfold av_cell_old, av_cell_new, nv1. apply bv_eq. rewrite U_add, !U_mul, U_add, !U_lit.
  change (3 mod M64v) with 3. change (1 mod M64v) with 1.
  rewrite Zplus_mod_idemp_l. rewrite Zmult_mod_idemp_l. f_equal. lia.
Qed.
Lemma rate_nv1_holds : ltac2:(tb__ "0|1|
SaS1ScA1S1fS6S2cScSeSdS33S51A2A1R1A3S5A3S1fS6S2cScSeSdS51S4fA2A1R2A3S5A3S1fS6S2cScSeSdS12S74S4fS50A3S5cA2A1R3A3S5A3S1fS6S2cScSeSdS5cS13Z4000000A1M0A2A1R4A3S5A3S1fS6S2cScSeSdS4fG0A2A1R5A3S5A3S1fS6S2cScSeSdS50G0A2A1R6A3S5A3S73ScS11R8A1R7A3S11R9S7aA2F_;F_;F_;F_;F_;F_;F_;FF;Frho;").
Proof.
  intros rho F M1 M2 M3 M4 M5 M6 HF.
  pose proof (holds_mem _ _ _ HF M1) as F1. pose proof (holds_mem _ _ _ HF M2) as F2. pose proof (holds_mem _ _ _ HF M3) as F3. pose proof (holds_mem _ _ _ HF M4) as F4.
  pose proof (holds_mem _ _ _ HF M5) as F5. pose proof (holds_mem _ _ _ HF M6) as F6.
  rewrite h_ule in F1, F2, F3, F4, F5, F6. rewrite uval_lit in F4, F5, F6 by lia.
  pose proof (uval_range rho pPOS) as RP. pose proof (uval_range rho pLNL) as RL. pose proof (uval_range rho c_av) as RC. pose proof (uval_range rho pNX) as RN.
  unfold rate_nv1, nv1, pE0. apply (proj2 (h_ule _ _ _)).
  rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia.
  rewrite uval_add_small by (rewrite uval_add_small, uval_lit by lia; lia). rewrite uval_add_small by lia. rewrite uval_lit by lia. lia.
Qed.
Lemma lines_in_tv_p1' : ltac2:(tb__ "0|0|
S2dS2SbSbA2S3SbSbS53S75Z10S54A2A4S6aA3"). Proof. exact lines_in_tv_p1. Qed.

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
S56SaS1S16Q40A1A1S44OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
S41S0VAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S9S57VCST;R1A2S20S42Z0R2A2S43R2S72A2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S9S57VXGL;R1A2S20S42Z0R2A2S43R2S72A2A2F_;Fa;").
Hypothesis HXlits : ltac2:(tb__ "0|0|
S9S76R1A1S57VXGL;R2A2F_;Fa;").
Hypothesis LFLAG : law_flag_stmt AInv.
Hypothesis LFSH : law_fshadow_stmt AInv.
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S1S2S2S9S9A2S9A2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 7 BX.
Variable rho0 : valuation.
Let P0 : ltac2:(tb__ "0|0|
SaOFr;") := ltac2:(tb__ "0|0|
S24VCST;VFB;VFF;A3").
Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S1dVAInv;VCST;VXGL;S5bVKc;Vrho0;VP0;VFB;VFF;VBX;S19Vnd;Ac").
Let JAFv (Phi : valuation -> Prop) (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S30VAInv;VCST;VXGL;S5bVKc;Vrho0;VP0;VFB;VFF;VBX;S19VPhi;Vnd;Ad").

Lemma CXR_op1 : ltac2:(tb__ "0|0|
S1fS6S36VXGL;SfS15S62A1A1S64Z4Z1eS60A6S5A3"). Proof using . OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma CXR_op0 : ltac2:(tb__ "0|0|
S1fS6S36VXGL;SfS15S61A1A1S63Z4Z1eS60A6S5A3"). Proof using . OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma CXR_p1 : ltac2:(tb__ "0|0|
S1fS6S36VXGL;SfS15S6cA1A1S6aZ4Z1eS69A6S5A3"). Proof using . OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma CXR_p0 : ltac2:(tb__ "0|0|
S1fS6S36VXGL;SfS15S6bA1A1S6dZ4Z1eS69A6S5A3"). Proof using . OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Section X.
Variable TR : assn -> assn -> Prop.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S27S27S27S28R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").

Lemma site_lr : ltac2:(tb__ "0|1|
S1S2SbSbA2A1S1S39A1S14S14S14SaS1S16Q40A1A1S27S79R6R5R4A3VTR;S17S0VJAv;S1bR9S23R8S1cS52S5A2M0A4A1R5R4R3A5R2A2VTR;S17S0VJAv;S1bRaS23R9G0A4A1R8R5R4A5R3A2F_;F_;FQ;Ftp;Frho;FLR;FR;FL;Fbd;Ftv;").
Proof using TR_pre.
  intros tv bd L R LR rho tp Q (Rwf & Rsd & Rnx & RR & RLR & Rfb & M1 & M2 & M3 & M4 & M5 & M6) HK.
  apply (TR_pre (SPA segs (JAv (NDA tv frL bd (AHead pH true))) LR rho tp)); [|exact HK]. intros w Hw.
  rewrite <- RLR. apply (SPA_refacts_JA segs); [| exact Rfb |].
  - rewrite <- RR. apply (SPA_restate segs _ rho L (ax_S R) tp w _ _ Rwf Rsd Rnx); [| constructor | exact Hw].
    constructor; [|constructor]. cbn [fst snd]. apply av_cell_eq.
  - intros tr md _ HF1. apply Forall_app. split; [|exact HF1]. constructor; [|constructor]. exact (rate_nv1_holds rho _ M1 M2 M3 M4 M5 M6 HF1).
Qed.
End X.

Section Safety.
Variable ok : world -> Prop.
Hypothesis Hok : ltac2:(tb__ "0|0|
S1eS0VKc;Vok;A3").
Hypothesis AC : ltac2:(tb__ "0|0|
S3fS0S3cVAInv;VCST;VXGL;A5").
Hypothesis MCROM : ltac2:(tb__ "0|0|
S59S0S3cVAInv;VCST;VXGL;S58ZcA7").
Variable FAMQ : list word -> assn.
Hypothesis XLATCH : ltac2:(tb__ "0|1|
SaS1S16Q40A1A1M0G0S26S0Vok;S17S0VJAFv;S22S49A2S4eR3R2A5VFAMQ;R1A1A4Ftp0;Ftp;Frho;").
Hypothesis XLATCHE2 : ltac2:(tb__ "0|1|
SaS1S16Q40A1A1M0G0S26S0Vok;S17S0VJAFv;S22S4aA2S55R3R2A5VFAMQ;R1A1A4Ftp0;Ftp;Frho;").

Lemma CHOP1_T : ltac2:(tb__ "0|1|
S1S2S9S9A2M0A1S1S2G0S9A2A1S38SaS1S16Q40A1A1S37Z4R3A2S26S0Vok;S17S0S1aVAInv;VCST;VXGL;VKc;S34R6R5A2R6R5R4S19S3aS31S5S5eA3AaS5dR3R2A5S29S0S2bR3R2S3bVAInv;VCST;VXGL;VKc;S34S19S5fR6R5R4AaA5A4F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Proof using ALA HCST HXGL HKc Hok AC.
  intros FBc FFc BXc rho1 tp1 HB. unfold PDk_o1.
  eapply (sum_PostsC_k segs AInv CST XGL Kc OP1P.P0_op PTrue OP1.Pre_op (ndh h0 true OP1.nd0) (PDh OP1.PD_op h0 true) NF); [|exact Hok|exact HB].
  intros ok' FBc' FFc' BXc' rho2 tp2 Hok' HB'.
  eapply (JA_frame_sum segs AInv CST XGL ALA Kc OP1P.P0_op PTrue OP1.Pre_op OP1.nd0 OP1.PD_op NF h0 true h0_ltNF HamC_o1 HamPD_o1 P0_op_mono ok'); [|exact HB'].
  intros FBc'' FFc'' BXc'' rho3 tp3 HB''. exact (OP1P.opt_push1_sum AInv CST XGL ALA HCST HXGL Kc HKc FBc'' FFc'' BXc'' HB'' rho3 ok' Hok' AC tp3).
Qed.
Lemma CHOP3_T : ltac2:(tb__ "0|1|
S1S2S9S9A2M0A1S1S2G0S9A2A1S38SaS1S16Q40A1A1S37Z4R3A2S26S0Vok;S17S0S1aVAInv;VCST;VXGL;VKc;S35R6R5A2R6R5R4S19S3aS31S5S67A3AaS66R3R2A5S29S0S2bR3R2S3bVAInv;VCST;VXGL;VKc;S35S19S68R6R5R4AaA5A4F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Proof using ALA HCST HXGL HKc Hok AC.
  intros FBc FFc BXc rho1 tp1 HB. unfold PDk_o3.
  eapply (sum_PostsC_k segs AInv CST XGL Kc OP3P.P0_op PTrue OP3.Pre_op (ndh h0 true OP3.nd0) (PDh OP3.PD_op h0 true) NF); [|exact Hok|exact HB].
  intros ok' FBc' FFc' BXc' rho2 tp2 Hok' HB'.
  eapply (JA_frame_sum segs AInv CST XGL ALA Kc OP3P.P0_op PTrue OP3.Pre_op OP3.nd0 OP3.PD_op NF h0 true h0_ltNF HamC_o3 HamPD_o3 P0_op3_mono ok'); [|exact HB'].
  intros FBc'' FFc'' BXc'' rho3 tp3 HB''. exact (OP3P.opt_push3_sum AInv CST XGL ALA HCST HXGL Kc HKc FBc'' FFc'' BXc'' HB'' rho3 ok' Hok' AC tp3).
Qed.
Lemma CMEMCPYR_T : ltac2:(tb__ "0|2|
S56SaS1S16Q40A1A1M0S26S0Vok;S17S0SaG0S1S45A1S44S20S3eVAInv;R7VKc;R4R3R2R1A7S21A2Lm;Lt;Lp;Lr;S6fR2R1A5S29S0S2bR2R1S7S2S14S2aA2M1S3S14S2aS6eS3dVAInv;VCST;VXGL;R3VKc;A5A4S8G1A1A3A5A4Ftp1;Frho1;FAi;").
Proof using HKc Hok MCROM.
  intros Ai rho1 tp1. eapply triple_conseq; [| intros w Hw; exact Hw |].
  2: { apply (MCROM ok Ai Kc rho1 tp1 HKc). eapply ok_frameA_of_K; [exact Hok|]. intros r p t m (_ & K & _). exact K. }
  intros [tr [ms md]] [Hsm [HJ _]]. split; [exact Hsm | exact HJ].
Qed.

Lemma CUT4_T : ltac2:(tb__ "0|4|
S14S18S4S2S9SbA2M0SaS1S16Q40A1A1M1G1S2dS2S2S2S14S18A2M2S4A2M3G0A2S3G3G0S3G2S4S3S14S18R7R6A4R5A4R4A4S65A3S2fS70R6R4A3S26S0Vok;S17S0VJAv;R8A1R9R5R4A5VFAMQ;R3A1A4F_;F_;Ftp0';Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof using ALA HCST HXGL HXlits LFSH HKc HBX Hok AC MCROM XLATCH XLATCHE2.
  intros T nd k rv rho tp tp0' Hin Hphi.
  apply (triple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisH k) ok nd T rho tp _ Hphi).
  apply (cfg_sound_JAF segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc PhisH PhisH_reads 600%nat cps_v NP (map efdrop cutsH4) (map efdrop exitsH4) ok (FAMQ tp0') Hok
           (ejcertAF_jcertAF segs NP PhisH _ _ _ _ _ ecertH4_ok)); [| apply in_map_iff; exists (T, nd, k, rv); split; [reflexivity | exact Hin]].
  intros X ndX kX rho1 tp1 HinX. apply in_map_iff in HinX as ([[[X' nd'] k'] rv'] & E & HinX). cbn in E. injection E as <- <- <-.
  set (QQ := fun w => SPfamGTA segs (map (nodeIAF AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue PhisH) (map efdrop cutsH4)) w \/ FAMQ tp0' w).
  assert (RE : forall Tc ndc rho' tp', In (Tc, ndc, 1%nat) (map efdrop cutsH4) -> tblB rho' -> triple segs ok (SPA segs (JAv ndc) Tc rho' tp') QQ).
  { intros Tc ndc rho' tp' Hi HP'. exact (reenter_cutJAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue PhisH ok (map efdrop cutsH4) Tc ndc 1%nat (FAMQ tp0') rho' tp' Hi HP'). }
  assert (WS : forall L Er Ec T0 Tb Tc, w_chk tv_op1 bd_op1 L Er Ec T0 Tb Tc -> In (Tc, nd_op1, 1%nat) (map efdrop cutsH4) -> tblB rho1 ->
               triple segs ok (SPA segs (JAv nd_op1) L rho1 tp1) QQ).
  { intros L Er Ec T0 Tb Tc Hchk Hi HP1. unfold nd_op1.
    apply (site_w AInv CST XGL ALA HCST HXGL HXlits LFSH Kc HKc FB FF BX HBX rho0 (triple segs ok) (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok)
             (@triple_ex segs ok) (TRs_pureP segs ok) (call_soundPA3 segs ok) CMEMCPYR_T tv_op1 bd_op1 L Er Ec T0 Tb Tc rho1 tp1 QQ Hchk lines_in_tv_op1 HP1).
    intros rho' tp' HP' _. exact (RE Tc nd_op1 rho' tp' Hi HP'). }
  assert (LE : forall tv bd tvj (L R LRs Lr Lb : axst) s, lr_chk L R LRs -> lx_chk tv bd tvj [LAX 0; LAXK 0] X_latchE2 LRs Lr Lb s -> In (xLD, kb 16 xLK) tv -> tblB rho1 ->
               triple segs ok (SPA segs (JAv (NDA tv frL bd (AHead pH true))) L rho1 tp1) QQ).
  { intros tv bd tvj L R LRs Lr Lb s Hlr Hlx Hlin HP1.
    apply (site_lr (triple segs ok) (TRs_pre segs ok) tv bd L R LRs rho1 tp1 QQ Hlr).
    apply (latch_rel AInv CST XGL ALA HCST HXGL LFSH Kc HKc FB FF BX HBX rho0 (triple segs ok) (TRs_facts segs ok) (TRs_pre segs ok) (@triple_ex segs ok) (TRs_pureP segs ok)
             tv bd tvj [LAX 0; LAXK 0] X_latchE2 LRs Lr Lb s rho1 tp1 QQ Hlx Hlin HP1).
    intros rho2 _ HP2.
    apply (triple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tblB ok (NDA tvL frL [LAX 0; LAXK 0] (AHead pH true)) X_latchE2 (rho_sub rho2 s) tp1 _ HP2).
    eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | exact (XLATCHE2 (rho_sub rho2 s) tp1 tp0')]. }
  cbn [exitsH4 In] in HinX. destruct HinX as [E|[E|[E|[E|[E|[E|[]]]]]]]; injection E as <- <- <- <-; cbn [efdrop fst snd];
    apply (triple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisH 1)); intros HP1.
  - exact (WS _ _ _ _ _ _ hv4_checks_w0 ltac:(cbn [map efdrop cutsH4 fst]; inl) HP1).
  - exact (WS _ _ _ _ _ _ hv4_checks_w1 ltac:(cbn [map efdrop cutsH4 fst]; inl) HP1).
  -
    apply (site_o3 AInv CST XGL ALA HCST HXGL HXlits LFSH Kc HKc FB FF BX HBX rho0 (triple segs ok) (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok)
             (TRs_pureP segs ok) (call_soundPA3 segs ok) CHOP3_T rho1 tp1 QQ CXR_p1 CXR_p0 HP1).
    + intros rho' tp' HP' _. exact (RE T_p1 nd_p1 rho' tp' ltac:(cbn [map efdrop cutsH4 fst]; inl) HP').
    + intros rho' tp' HP' _. exact (RE T_p0 nd_p0 rho' tp' ltac:(cbn [map efdrop cutsH4 fst]; inl) HP').
  - destruct hv4_checks_l1 as [Hlr Hlx]. exact (LE tv_op0 brest_o1 tvj_l1 _ _ _ _ _ _ Hlr Hlx lines_in_tv_op0 HP1).
  - destruct hv4_checks_l3 as [Hlr Hlx]. exact (LE tv_p0 brest_o3 tvj_l3 _ _ _ _ _ _ Hlr Hlx lines_in_tv_p0 HP1).
  -
    destruct hv4_checks_lok as (Hlr & PP1 & PP2 & PPay & _ & _ & Hlx). unfold nd_p1.
    apply (site_lr (triple segs ok) (TRs_pre segs ok) tv_p1 bd_p1 X_lok X_lokS X_lokR rho1 tp1 QQ Hlr).
    apply (TRs_facts segs ok). intros HFo.
    apply (TRs_pre segs ok (SPA segs (JAv (NDA tv_p1 frL bdX_v (AHead pH true))) X_lokR rho1 tp1)).
    { intros w Hw. exact (SPA_bd_repay AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tv_p1 frL (AHead pH true) bd_p1 comm_v Xs_v Ys_v bdX_v _ X_lokR rho1 tp1 w PP1 PP2 HFo PPay Hw). }
    apply (latch_rel AInv CST XGL ALA HCST HXGL LFSH Kc HKc FB FF BX HBX rho0 (triple segs ok) (TRs_facts segs ok) (TRs_pre segs ok) (@triple_ex segs ok) (TRs_pureP segs ok)
             tv_p1 bdX_v tvj_lok (bdX 0) X_latch X_lokR X_lokr X_lokb s_lok rho1 tp1 QQ Hlx lines_in_tv_p1 HP1).
    intros rho2 _ HP2.
    apply (triple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tblB ok (NDA tvL frL (bdX 0) (AHead pH true)) X_latch (rho_sub rho2 s_lok) tp1 _ HP2).
    eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | exact (XLATCH (rho_sub rho2 s_lok) tp1 tp0')].
Qed.

Theorem xko1_T : ltac2:(tb__ "0|1|
SaS1S16Q40A1A1M0G0S26S0Vok;S17S0VJAFv;S22S32A2S4dR3R2A5VFAMQ;R1A1A4Ftp0;Ftp;Frho;").
Proof using ALA HCST HXGL HXlits LFSH HKc HBX Hok AC MCROM XLATCH XLATCHE2.
  intros rho tp tp0.
  apply (triple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tblB). intros HPHI.
  apply (site_o1 AInv CST XGL ALA HCST HXGL HXlits LFSH Kc HKc FB FF BX HBX rho0 (triple segs ok) (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok)
           (@triple_ex segs ok) (TRs_pureP segs ok) (call_soundPA3 segs ok) CHOP1_T rho tp _ CXR_op1 CXR_op0 HPHI).
  - intros rho' tp' HP' _. exact (CUT4_T T_op1 nd_op1 1%nat _ rho' tp' tp0 ltac:(cbn [cutsH4]; inl) HP').
  - intros rho' tp' HP' _. exact (CUT4_T T_op0 nd_op0 1%nat _ rho' tp' tp0 ltac:(cbn [cutsH4]; inl) HP').
Qed.

Theorem arm_v_T : ltac2:(tb__ "0|1|
SaS1S16Q40A1A1M0G0S26S0Vok;S17S0VJAFv;S22S48A2S4cR3R2A5VFAMQ;R1A1A4Ftp0;Ftp;Frho;").
Proof using ALA HCST HXGL HXlits LFSH HKc HBX Hok AC MCROM XLATCH XLATCHE2.
  exact (arm_hv_T AInv CST XGL ALA HCST HXGL HXlits LFSH Kc HKc FB FF BX HBX rho0 ok Hok AC FAMQ
           (kvr_T AInv CST XGL ALA HCST HXGL HXlits LFSH Kc HKc FB FF BX HBX rho0 ok Hok AC FAMQ xko1_T XLATCHE2)).
Qed.
End Safety.

Section Existence.
Hypothesis ACX : ltac2:(tb__ "0|0|
S40S0S3cVAInv;VCST;VXGL;A5").
Hypothesis MCROMX : ltac2:(tb__ "0|0|
S5aS0S3cVAInv;VCST;VXGL;S58ZcA7").
Variable FAM : ltac2:(tb__ "0|0|
S9S1S16Q40A1A1S27F_;F_;").
Hypothesis FAM_mono : ltac2:(tb__ "0|0|
S9S9S1S16Q40A1A1S28S42R4R3A2VFAM;R5R3R2A3VFAM;R5R4R3A3F_;F_;Fw;Ftp0;Fb';Fb;").
Hypothesis XLATCH : ltac2:(tb__ "0|2|
SaS1S16Q40A1A1M0G0S25S0S17S0VJAFv;S22S49A2S4eR3R2A5VFAM;S2eS3S2S2S14S18A2M1S4A2S2S9SbA2S3G1S4S3S14S18S4eS49A4U1A4S3S9SbS46S47Z1S4bA2A4A4R3A2R1A2A3Ftp0;Ftp;Frho;").
Hypothesis XLATCHE2 : ltac2:(tb__ "0|2|
SaS1S16Q40A1A1M0G0S25S0S17S0VJAFv;S22S4aA2S55R3R2A5VFAM;S2eS3S2S2S14S18A2M1S4A2S2S9SbA2S3G1S4S3S14S18S55S4aA4U1A4S3S9SbS46S47Z1S4bA2A4A4R3A2R1A2A3Ftp0;Ftp;Frho;").

Lemma CHOP1_E : ltac2:(tb__ "0|1|
S1S2S9S9A2M0A1S1S2G0S9A2A1S38SaS1S16Q40A1A1S37Z4R3A2S25S0S17S0S1aVAInv;VCST;VXGL;VKc;S34R6R5A2R6R5R4S19S3aS31S5S5eA3AaS5dR3R2A5S29S0S2bR3R2S3bVAInv;VCST;VXGL;VKc;S34S19S5fR6R5R4AaA5A3F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Proof using ALA HCST HXGL HKc ACX.
  intros FBc FFc BXc rho1 tp1 HB. unfold PDk_o1.
  eapply (sum_PostsC_k_ex segs AInv CST XGL Kc OP1P.P0_op PTrue OP1.Pre_op (ndh h0 true OP1.nd0) (PDh OP1.PD_op h0 true) NF); [|exact HB].
  intros FBc' FFc' BXc' rho2 tp2 HB'.
  eapply (JA_frame_sum_ex segs AInv CST XGL ALA Kc OP1P.P0_op PTrue OP1.Pre_op OP1.nd0 OP1.PD_op NF h0 true h0_ltNF HamC_o1 HamPD_o1 P0_op_mono); [|exact HB'].
  intros FBc'' FFc'' BXc'' rho3 tp3 HB''. exact (OP1P.opt_push1_sum_ex AInv CST XGL ALA HCST HXGL Kc HKc FBc'' FFc'' BXc'' HB'' rho3 ACX tp3).
Qed.
Lemma CHOP3_E : ltac2:(tb__ "0|1|
S1S2S9S9A2M0A1S1S2G0S9A2A1S38SaS1S16Q40A1A1S37Z4R3A2S25S0S17S0S1aVAInv;VCST;VXGL;VKc;S35R6R5A2R6R5R4S19S3aS31S5S67A3AaS66R3R2A5S29S0S2bR3R2S3bVAInv;VCST;VXGL;VKc;S35S19S68R6R5R4AaA5A3F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Proof using ALA HCST HXGL HKc ACX.
  intros FBc FFc BXc rho1 tp1 HB. unfold PDk_o3.
  eapply (sum_PostsC_k_ex segs AInv CST XGL Kc OP3P.P0_op PTrue OP3.Pre_op (ndh h0 true OP3.nd0) (PDh OP3.PD_op h0 true) NF); [|exact HB].
  intros FBc' FFc' BXc' rho2 tp2 HB'.
  eapply (JA_frame_sum_ex segs AInv CST XGL ALA Kc OP3P.P0_op PTrue OP3.Pre_op OP3.nd0 OP3.PD_op NF h0 true h0_ltNF HamC_o3 HamPD_o3 P0_op3_mono); [|exact HB'].
  intros FBc'' FFc'' BXc'' rho3 tp3 HB''. exact (OP3P.opt_push3_sum_ex AInv CST XGL ALA HCST HXGL Kc HKc FBc'' FFc'' BXc'' HB'' rho3 ACX tp3).
Qed.
Lemma CMEMCPYR_E : ltac2:(tb__ "0|2|
S56SaS1S16Q40A1A1M0S25S0S17S0SaG0S1S45A1S44S20S3eVAInv;R7VKc;R4R3R2R1A7S21A2Lm;Lt;Lp;Lr;S6fR2R1A5S29S0S2bR2R1S7S2S14S2aA2M1S3S14S2aS6eS3dVAInv;VCST;VXGL;R3VKc;A5A4S8G1A1A3A5A3Ftp1;Frho1;FAi;").
Proof using HKc MCROMX.
  intros Ai rho1 tp1. eapply etriple_conseq; [| intros w Hw; exact Hw | exact (MCROMX Ai Kc rho1 tp1 HKc)].
  intros [tr [ms md]] [Hsm [HJ _]]. split; [exact Hsm | exact HJ].
Qed.

Lemma CUT4_E : ltac2:(tb__ "0|5|
S14S18S4S2S9SbA2M0SaS1S16Q40A1A1M1S9G1S2dS2S2S2S14S18A2M2S4A2M3G0A2S3G3G0S3G2S4S3S14S18R8R7A4R6A4R5A4S65A3S2fS70R7R5A3S20S42Z0S2eS3G3G0S3G2S4S3S14S18RaR9A4R8A4R7A4R6A2M4A2S43G4R4A2A2S25S0S17S0VJAv;RaA1RbR7R6A5VFAM;R5R4A2A3F_;F_;F_;Ftp0';Fb;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof using ALA HCST HXGL HXlits LFSH HKc HBX ACX MCROMX FAM_mono XLATCH XLATCHE2.
  intros T nd k rv rho tp b tp0' Hin Hphi Hm.
  apply (etriple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisH k) nd T rho tp _ Hphi).
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (FAM_mono _ b tp0' w ltac:(apply Z.lt_le_incl; exact (proj2 Hm)) Hw) |].
  apply (cfg_complete_JAF_b segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc PhisH PhisH_reads 600%nat cps_v NP cutsH4 exitsH4 (fun b w => FAM b tp0' w)
           (fun b b' w Hb Hw => FAM_mono b b' tp0' w Hb Hw) ecertH4_ok); [|exact Hin].
  intros X ndX kX rvX rho1 tp1 HinX.
  destruct VB_460 as [I460 I467].
  set (EN := map (enodeIAF AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue PhisH) cutsH4).
  assert (WS : forall L Er Ec T0 Tb Tc, w_chk tv_op1 bd_op1 L Er Ec T0 Tb Tc -> In (Tc, nd_op1, 1%nat, mH 15 40) cutsH4 ->
               etriple segs (SPA segs (JAFv (phiK PhisH 1) nd_op1) L rho1 tp1)
                 (fun w => SPfamETA segs EN (efmeasA (L, nd_op1, 1%nat, mH 15 45) rho1) w \/ FAM (efmeasA (L, nd_op1, 1%nat, mH 15 45) rho1) tp0' w)).
  { intros L Er Ec T0 Tb Tc Hchk Hi.
    apply (etriple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisH 1)). intros HP1.
    apply (TRe_facts segs). intros HF0.
    pose proof Hchk as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CL1 & CL2 & CL3).
    destruct (loopF_vals rho1 _ HF0 (conj CL1 (conj CL2 CL3))) as [HiC Hc26]. unfold nd_op1.
    apply (site_w AInv CST XGL ALA HCST HXGL HXlits LFSH Kc HKc FB FF BX HBX rho0 (etriple segs) (TRe_facts segs) (TRe_ex segs) (TRe_pre segs)
             (@etriple_ex segs) (TRe_pureP segs) (call_completePA3 segs) CMEMCPYR_E tv_op1 bd_op1 L Er Ec T0 Tb Tc rho1 tp1 _ Hchk lines_in_tv_op1 HP1).
    intros rho' tp' HP' HVB.
    apply (ereenter_cutJAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue PhisH cutsH4 Tc nd_op1 1%nat (mH 15 40) _ _ rho' tp' Hi HP').
    apply (VLA_lt2 rho1 rho' 15 15 45 40 L Tc nd_op1 nd_op1 1%nat 1%nat); [exact (HVB _ I460) | exact (HVB _ I467) | exact HiC | exact Hc26 | lia | lia | lia | lia | right; lia]. }
  assert (LE : forall tv bd tvj (L R LRs Lr Lb : axst) s, lr_chk L R LRs -> lx_chk tv bd tvj [LAX 0; LAXK 0] X_latchE2 LRs Lr Lb s -> In (xLD, kb 16 xLK) tv ->
               etriple segs (SPA segs (JAFv (phiK PhisH 1) (NDA tv frL bd (AHead pH true))) L rho1 tp1)
                 (fun w => SPfamETA segs EN (efmeasA (L, NDA tv frL bd (AHead pH true), 1%nat, (RL, VLA 1 z0)) rho1) w
                           \/ FAM (efmeasA (L, NDA tv frL bd (AHead pH true), 1%nat, (RL, VLA 1 z0)) rho1) tp0' w)).
  { intros tv bd tvj L R LRs Lr Lb s Hlr Hlx Hlin.
    apply (etriple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisH 1)). intros HP1.
    pose proof Hlx as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & W460 & W467 & _).
    apply (site_lr (etriple segs) (TRe_pre segs) tv bd L R LRs rho1 tp1 _ Hlr).
    apply (latch_rel AInv CST XGL ALA HCST HXGL LFSH Kc HKc FB FF BX HBX rho0 (etriple segs) (TRe_facts segs) (TRe_pre segs) (@etriple_ex segs) (TRe_pureP segs)
             tv bd tvj [LAX 0; LAXK 0] X_latchE2 LRs Lr Lb s rho1 tp1 _ Hlx Hlin HP1).
    intros rho2 HV2 HP2.
    apply (etriple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tblB (NDA tvL frL [LAX 0; LAXK 0] (AHead pH true)) X_latchE2 (rho_sub rho2 s) tp1 _ HP2).
    eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw |].
    rewrite <- (efmeasA_VLA_agree X_latchE2 L ndXE (NDA tv frL bd (AHead pH true)) 1%nat 1%nat RL 1 rho1 rho2 (HV2 _ I460) (HV2 _ I467)).
    rewrite <- (efmeasA_VLA_sub X_latchE2 X_latchE2 ndXE ndXE 1%nat 1%nat RL 1 s rho2 W460 W467).
    exact (XLATCHE2 (rho_sub rho2 s) tp1 tp0'). }
  cbn [exitsH4 In] in HinX. destruct HinX as [E|[E|[E|[E|[E|[E|[]]]]]]]; injection E as <- <- <- <-.
  - exact (WS _ _ _ _ _ _ hv4_checks_w0 ltac:(cbn [cutsH4]; inl)).
  - exact (WS _ _ _ _ _ _ hv4_checks_w1 ltac:(cbn [cutsH4]; inl)).
  -
    apply (etriple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisH 1)). intros HP1.
    apply (TRe_facts segs). intros HF0.
    pose proof hv4_checks_o3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CL1 & CL2 & CL3).
    destruct (loopF_vals rho1 _ HF0 (conj CL1 (conj CL2 CL3))) as [HiC Hc26].
    assert (MM : forall rho' (Tc : axst) ndc, (forall v, In v V_B -> rw rho' v = rw rho1 v) ->
              0 <= efmeasA (Tc, ndc, 1%nat, mH 15 30) rho' < efmeasA (E_o3, nd_op1, 1%nat, mH 15 35) rho1).
    { intros rho' Tc ndc HV. apply (VLA_lt2 rho1 rho' 15 15 35 30 E_o3 Tc nd_op1 ndc 1%nat 1%nat); [exact (HV _ I460) | exact (HV _ I467) | exact HiC | exact Hc26 | lia | lia | lia | lia | right; lia]. }
    apply (site_o3 AInv CST XGL ALA HCST HXGL HXlits LFSH Kc HKc FB FF BX HBX rho0 (etriple segs) (TRe_facts segs) (TRe_ex segs) (TRe_pre segs)
             (TRe_pureP segs) (call_completePA3 segs) CHOP3_E rho1 tp1 _ CXR_p1 CXR_p0 HP1).
    + intros rho' tp' HP' HV. exact (ereenter_cutJAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue PhisH cutsH4 T_p1 nd_p1 1%nat (mH 15 30) _ _ rho' tp' ltac:(cbn [cutsH4]; inl) HP' (MM rho' T_p1 nd_p1 HV)).
    + intros rho' tp' HP' HV. exact (ereenter_cutJAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue PhisH cutsH4 T_p0 nd_p0 1%nat (mH 15 30) _ _ rho' tp' ltac:(cbn [cutsH4]; inl) HP' (MM rho' T_p0 nd_p0 HV)).
  - destruct hv4_checks_l1 as [Hlr Hlx]. exact (LE tv_op0 brest_o1 tvj_l1 _ _ _ _ _ _ Hlr Hlx lines_in_tv_op0).
  - destruct hv4_checks_l3 as [Hlr Hlx]. exact (LE tv_p0 brest_o3 tvj_l3 _ _ _ _ _ _ Hlr Hlx lines_in_tv_p0).
  -
    apply (etriple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisH 1)). intros HP1.
    destruct hv4_checks_lok as (Hlr & PP1 & PP2 & PPay & _ & _ & Hlx).
    pose proof Hlx as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & W460 & W467 & _). unfold nd_p1.
    apply (site_lr (etriple segs) (TRe_pre segs) tv_p1 bd_p1 X_lok X_lokS X_lokR rho1 tp1 _ Hlr).
    apply (TRe_facts segs). intros HFo.
    apply (TRe_pre segs (SPA segs (JAv (NDA tv_p1 frL bdX_v (AHead pH true))) X_lokR rho1 tp1)).
    { intros w Hw. exact (SPA_bd_repay AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tv_p1 frL (AHead pH true) bd_p1 comm_v Xs_v Ys_v bdX_v _ X_lokR rho1 tp1 w PP1 PP2 HFo PPay Hw). }
    apply (latch_rel AInv CST XGL ALA HCST HXGL LFSH Kc HKc FB FF BX HBX rho0 (etriple segs) (TRe_facts segs) (TRe_pre segs) (@etriple_ex segs) (TRe_pureP segs)
             tv_p1 bdX_v tvj_lok (bdX 0) X_latch X_lokR X_lokr X_lokb s_lok rho1 tp1 _ Hlx lines_in_tv_p1 HP1).
    intros rho2 HV2 HP2.
    apply (etriple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tblB (NDA tvL frL (bdX 0) (AHead pH true)) X_latch (rho_sub rho2 s_lok) tp1 _ HP2).
    eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw |].
    rewrite <- (efmeasA_VLA_agree X_latch X_lok ndX0 (NDA tv_p1 frL bd_p1 (AHead pH true)) 1%nat 1%nat RL 1 rho1 rho2 (HV2 _ I460) (HV2 _ I467)).
    rewrite <- (efmeasA_VLA_sub X_latch X_latch ndX0 ndX0 1%nat 1%nat RL 1 s_lok rho2 W460 W467).
    exact (XLATCH (rho_sub rho2 s_lok) tp1 tp0').
Qed.

Theorem xko1_E : ltac2:(tb__ "0|2|
SaS1S16Q40A1A1M0G0S25S0S17S0VJAFv;S22S32A2S4dR3R2A5VFAM;S2eS3S2S2S14S18A2M1S4A2S2S9SbA2S3G1S4S3S14S18S4dS32A4U1A4S71ZfZ3cA2A4R3A2R1A2A3Ftp0;Ftp;Frho;").
Proof using ALA HCST HXGL HXlits LFSH HKc HBX ACX MCROMX FAM_mono XLATCH XLATCHE2.
  intros rho tp tp0.
  apply (etriple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tblB). intros HPHI.
  pose proof hv4_checks_rel as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CL1 & CL2 & CL3).
  apply (TRe_facts segs). intros HF0. destruct (loopF_vals rho _ HF0 (conj CL1 (conj CL2 CL3))) as [HiC Hc26].
  destruct VB_460 as [I460 I467].
  assert (MM : forall rho' (Tc : axst) ndc, (forall v, In v V_B -> rw rho' v = rw rho v) ->
            0 <= efmeasA (Tc, ndc, 1%nat, mH 15 50) rho' < efmeasA (E_o1, nd_keep, 1%nat, mH 15 60) rho).
  { intros rho' Tc ndc HV. apply (VLA_lt2 rho rho' 15 15 60 50 E_o1 Tc nd_keep ndc 1%nat 1%nat); [exact (HV _ I460) | exact (HV _ I467) | exact HiC | exact Hc26 | lia | lia | lia | lia | right; lia]. }
  apply (site_o1 AInv CST XGL ALA HCST HXGL HXlits LFSH Kc HKc FB FF BX HBX rho0 (etriple segs) (TRe_facts segs) (TRe_ex segs) (TRe_pre segs)
           (@etriple_ex segs) (TRe_pureP segs) (call_completePA3 segs) CHOP1_E rho tp _ CXR_op1 CXR_op0 HPHI).
  - intros rho' tp' HP' HV. exact (CUT4_E T_op1 nd_op1 1%nat (mH 15 50) rho' tp' _ tp0 ltac:(cbn [cutsH4]; inl) HP' (MM rho' T_op1 nd_op1 HV)).
  - intros rho' tp' HP' HV. exact (CUT4_E T_op0 nd_op0 1%nat (mH 15 50) rho' tp' _ tp0 ltac:(cbn [cutsH4]; inl) HP' (MM rho' T_op0 nd_op0 HV)).
Qed.

Theorem arm_v_E : ltac2:(tb__ "0|2|
SaS1S16Q40A1A1M0G0S25S0S17S0VJAFv;S22S48A2S4cR3R2A5VFAM;S2eS3S2S2S14S18A2M1S4A2S2S9SbA2S3G1S4S3S14S18S4cS48A4U1A4S3S9SbS46S47Z11S4bA2A4A4R3A2R1A2A3Ftp0;Ftp;Frho;").
Proof using ALA HCST HXGL HXlits LFSH HKc HBX ACX MCROMX FAM_mono XLATCH XLATCHE2.
  exact (arm_hv_E AInv CST XGL ALA HCST HXGL HXlits LFSH Kc HKc FB FF BX HBX rho0 ACX FAM FAM_mono
           (kvr_E AInv CST XGL ALA HCST HXGL HXlits LFSH Kc HKc FB FF BX HBX rho0 ACX FAM FAM_mono xko1_E XLATCHE2)).
Qed.
End Existence.
End Sum.
End Lib_load_obj_hv_pf6.

