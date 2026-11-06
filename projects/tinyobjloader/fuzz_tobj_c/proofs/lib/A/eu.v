(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Ox.F128_038.   (* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require et.

(* [comment removed for export] *)
Module Lib_handle_f_g1b.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "bool"; "true"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "ss_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_defs"; "E_co0"; "T_cok"; "pA"; "pKco"; "pQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.et.Lib_handle_f_gdefs"; "E_co1"; "coF"; "liveF"; "vrF"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV ObjXform ObjUnbase TobjJVAz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAT ResidualA AxArrA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAM2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ResidualA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxArrA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double Lib_parse_corner2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Asan_set_shadow_iface.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_parse_corner2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.Lib_diag_append OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Asan_set_shadow_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eg.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_defs Lib_handle_f_s1 Lib_handle_f_s2 Lib_handle_f_s3 Lib_handle_f_s4 Lib_handle_f_s5 Lib_handle_f_s6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_s9 Lib_handle_f_s9b.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require es.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require en.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_nodes.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eh.Lib_builder_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eg.Lib_builderH_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_handle_f_s7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_handle_f_s8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s9b OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.es.Lib_handle_f_s10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.en.Lib_handle_f_epi OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_nodes.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_tess_polygon_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_arith.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Import ScanDoubleAddr VRAddr RA.ReallocAddr ParseCornerAddr DiagAppendAddr HFAddr.
Close Scope bv_scope.
Open Scope Z_scope.
Module PGC. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_tess_polygon_cstates. End PGC.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require et.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.et.Lib_handle_f_gdefs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import MemoFast.
Ltac vmr := vmc.
Lemma co_coF : ltac2:(tb__ "0|0|
S2S0SbS3S4SaA1A1A1S1A3"). Proof. vmr. Qed.
Lemma cok_live : ltac2:(tb__ "0|0|
S2S0ScS7Z1S8S3S4S6A1A1A4S1A3"). Proof. vmr. Qed.
Lemma co_vrF : ltac2:(tb__ "0|0|
S2S0SdS9S3S4S5A1A1A2S1A3"). Proof. vmr. Qed.
End Lib_handle_f_g1b.

(* [comment removed for export] *)
Module Lib_handle_f_g1.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "sv_eqb"; "SVar"; "SLit"; "ss_next"; "ss_objs"; "sprop"; "ss_facts"; "DZero"; "cell"; "sv_below"; "SPAlign"; "SPUle"; "mkCell"; "sprop_eqb"; "swf"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Init.Datatypes"; "andb"; "nil"; "cons"; "prod"; "bool"; "list"; "true"; "app"; "pair"; "Some"; "nat"; "None"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_defs"; "pQ"; "pDco"; "E_co"; "pKco"; "s_co"; "pK2"; "E_sm0"; "T_sm1"; "s_sm"; "tv0"; "tv_body"; "bd_loop"; "pD2"; "JR_co"; "L_sm"; "Pre_sm"; "R_sm"; "X_hf0"; "X_pro"; "co_need"; "nd0"; "objs_pro"; "objs_sm1"; "C_pro0"; "E_co0"; "JF_co"; "R_co"; "T_cof"; "T_cog"; "T_cok"; "T_coks"; "Xkeep"; "cVF"; "fr_hf"; "xf_vr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bitem"; "bd_subst"; "bd_wpos"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs"; "kb"; "tE"; "NPH"; "PROG"; "hF"; "hFL"; "hG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_X"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_subA"; "call_checkPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_defs.VN"; "Pre_vr"; "P_grown"; "P_keep"; "tv0"; "P_fail"; "bdP"; "nd0"; "tvP"; "vKn"; "vN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.et.Lib_handle_f_gdefs"; "brest_co"; "kept_co"; "s_cog"; "s_cok"; "E_co1"; "land_chk"; "bF"; "bd2_cog"; "bd2_cok"; "bdG_co"; "bdK_co"; "cells_pro"; "s_cof"; "xff_chk"; "release_chk"; "tv2_cof"; "tv2_cog"; "tv2_cok"; "vr_chk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "sv_subst"; "wsub_get"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "ltb"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "import_tv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "nd_bd"; "nd_below"; "@Corelib.Lists.ListDef"; "firstn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eg.Lib_builderH_pf"; "extraXH"; "extraOH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_nodes"; "ndP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS"; "xrs_checkL"; "frame_open_stateA"; "shobj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG"; "tv_permb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "call_checkTA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAT"; "robjs_checkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "V_FLAG"; "V_RES"; "flagbyte_obj"; "@Stdlib.Lists.List"; "existsb"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV ObjXform ObjUnbase TobjJVAz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAT ResidualA AxArrA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAM2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ResidualA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxArrA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double Lib_parse_corner2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Asan_set_shadow_iface.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_parse_corner2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.Lib_diag_append OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Asan_set_shadow_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eg.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_defs Lib_handle_f_s1 Lib_handle_f_s2 Lib_handle_f_s3 Lib_handle_f_s4 Lib_handle_f_s5 Lib_handle_f_s6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_s9 Lib_handle_f_s9b.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require es.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require en.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_nodes.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eh.Lib_builder_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eg.Lib_builderH_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_handle_f_s7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_handle_f_s8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s9b OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.es.Lib_handle_f_s10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.en.Lib_handle_f_epi OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_nodes.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_tess_polygon_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_arith.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Import ScanDoubleAddr VRAddr RA.ReallocAddr ParseCornerAddr DiagAppendAddr HFAddr.
Close Scope bv_scope.
Open Scope Z_scope.
Module PGC. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_tess_polygon_cstates. End PGC.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require et.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.et.Lib_handle_f_gdefs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import MemoFast.
Ltac vmr := vmc.

Section G.
Variable XGL : list (Z * Z).

Lemma sm_chk : ltac2:(tb__ "0|8|
S11S16S12S12S12S12S12S12S12S12S12S12S12S12S50S25S2eS27S2fS14S4dS2dS13S4dA1A3A5S80S47S27A2A2S70S47S5S4cS25A1M0A1M1A2A2S75G1S33A2A2S44S74S33A1A1A2S2S6fS4fS27S2eS2dS25A4M2S84A2S3Pa0M3A1A2A2S70G1G3A2A2S2S6fG2S83A2S3PaaM4A1A2A2S70G1G4A2A2S61S8G0A1M5A1A2S81G5S28S13S15S15S0S72A2S0A2A1M6S1dS1cA1M7S78S2fA6A2S7aVXGL;G5S28G6G7S6G0A1S77S4eS25A1A8A2S2S6fS27PcA2S4Z140A1A2A2S18A3").
Proof. vmr. Qed.

Lemma T_sm1_objs : ltac2:(tb__ "0|1|
S11S17S1A1S6S4cS26A1A1S19S1S35S14S1S85S4aS14SaSeS4Z0A1Z1M0S4G0A1A3S13SaA1A3A2S13S1A1A3A3A3"). Proof. vmr. Qed.
Lemma T_sm1_X : ltac2:(tb__ "0|1|
S11S17S15S0S0A2M0A1S4eS26A1S19G0S30S14G0S1aS0S0S49S4Z200A1A4S13G0A1A3A3A3"). Proof. vmr. Qed.
Lemma sm1_chk : ltac2:(tb__ "0|7|
S11S16S12S12S12S12S12S12S10S4cS7bS26S35S19S15S0S0A2M0S30S13G0A1A3M1Pa0M2Z200A5A1A1S70S47S5S4cS26A1M3A1M4A2A2S75G4S79A2A2S61S8G3A1M5A1A2S7aVXGL;G5S28S40S1bS1cU0A2S6G3A1S77G1A8A2S86S7SfScG2Z5A2A1S8S4cS36A1M6A1A3A2S71G2S5G6A1A2A2S18A3").
Proof. vmr. Qed.

Lemma X_pro_objs : ltac2:(tb__ "0|0|
S11S17S1A1S6S4cS31A1A1S19S1S34S14S1S7cS4bZ0Z40S66S9A5S13S1A1A3A3A3"). Proof. vmr. Qed.
Lemma pro_chk : ltac2:(tb__ "0|0|
S11S16S69S31S34Z0Z40S66S9S13S15S72S72A2A1S28S74S79A1A9S18A3"). Proof. vmr. Qed.

Lemma E_co1_eq : ltac2:(tb__ "0|0|
S11S1eS4dA1S7eS37S41U13Z2d0A2A2S1bS4dS5fA2A3"). Proof. vmr. Qed.
Lemma E_co_eq2 : ltac2:(tb__ "0|0|
S11S4dS7dS32S1fA1S5fA2S21A3"). Proof. vmr. Qed.
Lemma co_xff : ltac2:(tb__ "0|0|
S11S16S68S5fS32S1fA1A2S18A3"). Proof. vmr. Qed.
Lemma co_tvp : ltac2:(tb__ "0|1|
S11S16S7fS29S20S22A2S19S15S0S0A2M0S5cS14G0S1aS0S0S20S45ZcS22A2A4S13G0A1A3A3A2S18A3"). Proof. vmr. Qed.
Lemma co_chk : ltac2:(tb__ "0|0|
S11S16S6dVXGL;S21S5cS20S22ZcZ2d0S2aS1fS22A2S5bS23S39S3eS20A1AcS18A3"). Proof. vmr. Qed.
Lemma co_iK : ltac2:(tb__ "0|1|
S11S17S15S0S0A2M0A1S73S4fS23S51S53S21A4S54A2S14G0S1aS0S0S20S45ZcS22A2A4S13G0A1A3A3"). Proof. vmr. Qed.
Lemma co_iF : ltac2:(tb__ "0|1|
S11S17S15S0S0A2M0A1S73S4fS23S51S55S21A4S54A2S14G0S1aS0S0S20S45ZcS22A2A4S13G0A1A3A3"). Proof. vmr. Qed.
Lemma co_iG : ltac2:(tb__ "0|1|
S11S17S15S0S0A2M0A1S73S4fS23S51S52S21A4S58A2S14G0S1aS0S0S3P208A1S45ZcS3P209A1A2A4S13G0A1A3A3"). Proof. vmr. Qed.
Lemma co_bK : ltac2:(tb__ "0|0|
S11S17S42A1S43S4fS23S51S53S21A4S74S57A1A2S65A3"). Proof. vmr. Qed.
Lemma co_bG : ltac2:(tb__ "0|0|
S11S17S42A1S43S4fS23S51S52S21A4S56S5aS59A2A2S64A3"). Proof. vmr. Qed.

Lemma cok_xff : ltac2:(tb__ "0|0|
S11S16S68S3cS14S7SdS4S82A1S20A2S13S7A1A3A2S18A3"). Proof. vmr. Qed.
Lemma cok_land : ltac2:(tb__ "0|1|
S11S16S60S3dS2cS5eS19S15S0S0A2M0S5cS14G0S1aS0S0S20S45ZcS22A2A4S13G0A1A3A3S6cS19S42S65S5bA3S63S29S2bS24A2A8S18A3"). Proof. vmr. Qed.
Lemma cok_bd : ltac2:(tb__ "0|0|
S11S17S42A1S43S5eS2aS1fS24A2A2S63A3"). Proof. vmr. Qed.
Lemma cog_land : ltac2:(tb__ "0|1|
S11S16S60S3bS2cS5dS19S15S0S0A2M0S5cS14G0S1aS0S0S3P208A1S45ZcS3P209A1A2A4S13G0A1A3A3S6bS19S42S64S5bA3S62S29S2bS24A2A8S18A3"). Proof. vmr. Qed.
Lemma cog_bd : ltac2:(tb__ "0|0|
S11S17S42A1S43S5dS2aS1fS24A2A2S62A3"). Proof. vmr. Qed.
Lemma cof_land : ltac2:(tb__ "0|2|
S11S16S60S3aS38S67S19S15S0S0A2M0S5cS14G0S1aS0S0S20S45ZcS22A2A4S13G0A1A3A3S6aS76S42U1S5bA3M1G1S29S2bS24A2A8S18A3"). Proof. vmr. Qed.
Lemma cof_bd : ltac2:(tb__ "0|0|
S11S17S42A1S43S67S14S42S48S3fS1fA2S13S42A1A3A2S76S42U1S5bA3A3"). Proof. vmr. Qed.
Lemma cof_wp : bd_wpos brest_co = true. Proof. vmr. Qed.

Lemma co_meas : ltac2:(tb__ "0|1|
S11S16S12S12S12S12S12S2S6eS5eS46A2S46A2S2S6eS5eS1fA2S1fA2A2S2S6eS5dS46A2S46A2A2S2S6eS5dS1fA2S1fA2A2SbS5S4cS21A1A1M0S46A2A2SbG0S1fA2A2S18A3"). Proof. vmr. Qed.
End G.
End Lib_handle_f_g1.

(* [comment removed for export] *)
Module Lib_handle_f_g2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "@Corelib.Init.Datatypes"; "bool"; "true"; "nil"; "cons"; "Some"; "option"; "andb"; "prod"; "pair"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_defs"; "pD2"; "pA"; "pQ"; "pK2"; "X_body"; "E_ms1"; "T_ms0"; "E_ms"; "ndR"; "pDco"; "pKco"; "pT0"; "E_ms0"; "L_ms"; "Pre_ms"; "R_ms"; "bd_loop"; "reshapeA"; "s_ms"; "slot_obj"; "tv_body"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_X"; "xr_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs"; "kb"; "tE"; "tL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "sobj"; "ss_facts"; "SAlu"; "cell"; "mkObj"; "ss_next"; "sv"; "DUnknown"; "sv_below"; "obj_wf"; "ss_objs"; "SPUle"; "sprop"; "sprop_eqb"; "DZero"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXMerge"; "AXSelect"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.et.Lib_handle_f_gdefs"; "E_pc2"; "rsF"; "T_da2"; "T_dg2"; "T_pc2"; "pure_chk"; "vrF"; "purec_chk"; "slotF"; "xff_chk"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_setX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s1"; "E_pc1"; "E_pc"; "T_pc0"; "xslot"; "E_da"; "pc_need"; "sel_da"; "E_da0"; "E_pc0"; "R_da"; "R_pc"; "T_da"; "T_da0"; "T_pc"; "T_pc1"; "s_da"; "s_pc"; "sel_pc"; "@Stdlib.Lists.List"; "nth_error"; "existsb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "xrs_inclb"; "xr_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.Lib_diag_append"; "P_da"; "Pre_da"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s2"; "E_dg"; "R_dg"; "T_dg"; "T_dg0"; "ndXA"; "s_dg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_parse_corner2"; "P_ret"; "Pre_pc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV ObjXform ObjUnbase TobjJVAz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAT ResidualA AxArrA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAM2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ResidualA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxArrA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double Lib_parse_corner2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Asan_set_shadow_iface.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_parse_corner2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.Lib_diag_append OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Asan_set_shadow_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eg.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_defs Lib_handle_f_s1 Lib_handle_f_s2 Lib_handle_f_s3 Lib_handle_f_s4 Lib_handle_f_s5 Lib_handle_f_s6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_s9 Lib_handle_f_s9b.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require es.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require en.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_nodes.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eh.Lib_builder_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eg.Lib_builderH_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_handle_f_s7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_handle_f_s8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s9b OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.es.Lib_handle_f_s10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.en.Lib_handle_f_epi OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_nodes.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_tess_polygon_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_arith.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Import ScanDoubleAddr VRAddr RA.ReallocAddr ParseCornerAddr DiagAppendAddr HFAddr.
Close Scope bv_scope.
Open Scope Z_scope.
Module PGC. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_tess_polygon_cstates. End PGC.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require et.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.et.Lib_handle_f_gdefs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import MemoFast.
Ltac vmr := vmc.

Section G.
Variable XGL : list (Z * Z).

Lemma ms_o33 : ltac2:(tb__ "0|2|
S0S6S27A1S58S27S31S1fSfA1A1U21A3S5S27S2bSaS23ZcM0SbA2M1S29S44G1S26G0A1A3S3S2aA1S2eA5A2A3"). Proof. vmr. Qed.
Lemma ms_wf : ltac2:(tb__ "0|1|
S0S1S30S2cS1fSfA1A1S2bS29S44SaS23ZcM0SbA2A3S26Z0A1S26G0A1S3S2aA1S2eA5A2S2A3"). Proof. vmr. Qed.
Lemma ms_rs : ltac2:(tb__ "0|0|
S0S1S3bSaS23ZcSbA2S28S1fSfA1A1A3S2A3"). Proof. vmr. Qed.
Lemma ms_chk : ltac2:(tb__ "0|0|
S0S1S41VXGL;S18S4S20S17S3S20A1A3S11S1eSaSdA2S1aScSdA2S1cS19A8S2A3"). Proof. vmr. Qed.
Lemma tms_o1 : ltac2:(tb__ "0|1|
S0S6S27A1S58S27S31S1fS10A1A1U1A3S5S27S2bS29S44SaS23ZcM0SbA2A3S26Z0A1S26G0A1S3S2aA1S35A5A2A3"). Proof. vmr. Qed.
Lemma tms_wf : ltac2:(tb__ "0|2|
S0S1S30S2cS1fS10A1A1S2bSaS23ZcM0SbA2M1S29S44G1S26G0A1A3S3S2aA1S2eA5A2S2A3"). Proof. vmr. Qed.
Lemma tms_rs : ltac2:(tb__ "0|0|
S0S1S3bSaS23ZcSbA2S28S1fS10A1A1A3S2A3"). Proof. vmr. Qed.
Lemma ms_vrF : ltac2:(tb__ "0|0|
S0S1S40ScS28S1fS16A1A1A2S2A3"). Proof. vmr. Qed.
Lemma ms_meas : ltac2:(tb__ "0|1|
S0S1S7S2fS2cS1fS11A1A1M0S24A2S2fG0ScA2A2S2A3"). Proof. vmr. Qed.

Lemma E_pc2_eq : ltac2:(tb__ "0|0|
S0S20S1bS46U22S1dSaSbA2A3S3aA3"). Proof. vmr. Qed.
Lemma E_pc_eq3 : ltac2:(tb__ "0|0|
S0S20S66S4bS15ScA2S45S3aS4S8S2dS2dA2S49SaSbA2S21S3aA1A3A2A2S47A3"). Proof. vmr. Qed.
Lemma pc_o34 : ltac2:(tb__ "0|2|
S0S6S27A1S58S27S31S1fS46A1A1U22A3S5S27S2bSaS23ZcM0SbA2M1S29S44G1S26G0A1A3S3S2aA1S2eA5A2A3"). Proof. vmr. Qed.
Lemma pc_wf : ltac2:(tb__ "0|1|
S0S1S30S2cS1fS46A1A1S2bS29S44SaS23ZcM0SbA2A3S26Z0A1S26G0A1S3S2aA1S2eA5A2S2A3"). Proof. vmr. Qed.
Lemma pc_rs : ltac2:(tb__ "0|0|
S0S1S3bSaS23ZcSbA2S28S1fS46A1A1A3S2A3"). Proof. vmr. Qed.
Lemma pc_xin : ltac2:(tb__ "0|0|
S0S1S59S8S2dS2dA2S5bS9S2dS2dSaS23ZcSdA2A4A1S21S3aA1A3S2A3"). Proof. vmr. Qed.
Lemma pc_xb : ltac2:(tb__ "0|0|
S0S1S22S2cS1fS3aA1A1S49SaSbA2A2S2A3"). Proof. vmr. Qed.
Lemma pc_slotF : ltac2:(tb__ "0|0|
S0S1S42SbSdS28S1fS3aA1A1A3S2A3"). Proof. vmr. Qed.
Lemma pc_xff : ltac2:(tb__ "0|0|
S0S1S43S45S3aS4S8S2dS2dA2S49SaSbA2S21S3aA1A3A2S4bS15ScA2A2S2A3"). Proof. vmr. Qed.
Lemma pc_pcF : ltac2:(tb__ "0|1|
S0S1S7S59S33S34S32ScS24A2A1S28S1fS3aA1A1M0A3S59S33S34S32S24S25A2A1G0A3A2S2A3"). Proof. vmr. Qed.
Lemma pc_chk : ltac2:(tb__ "0|0|
S0S1S3fS65S64S47S12S56S50A6S2A3"). Proof. vmr. Qed.
Lemma T_pc2_eq : ltac2:(tb__ "0|1|
S0S6S20A1S39S54S4S36S38S57A1S4S36S37U0A1S4S36S37U20A1M0S4S36G0S3S36A1A3A3A3A3A2S5S20S3eA2A3"). Proof. vmr. Qed.
Lemma T_pc_eq2 : ltac2:(tb__ "0|0|
S0S20S45S3eSeSaSdA2A2S53A3"). Proof. vmr. Qed.
Lemma tpc_o2 : ltac2:(tb__ "0|1|
S0S6S27A1S58S27S31S1fS48A1A1U2A3S5S27S2bS29S44SaS23ZcM0SbA2A3S26Z0A1S26G0A1S3S2aA1S2eA5A2A3"). Proof. vmr. Qed.
Lemma tpc_wf : ltac2:(tb__ "0|2|
S0S1S30S2cS1fS48A1A1S2bSaS23ZcM0SbA2M1S29S44G1S26G0A1A3S3S2aA1S2eA5A2S2A3"). Proof. vmr. Qed.
Lemma tpc_rs : ltac2:(tb__ "0|0|
S0S1S3bSaS23ZcSbA2S28S1fS48A1A1A3S2A3"). Proof. vmr. Qed.
Lemma pc_xsub : ltac2:(tb__ "0|0|
S0S1S5aSeSaSdA2S21S3eA1A2S2A3"). Proof. vmr. Qed.
Lemma pc_vrF : ltac2:(tb__ "0|0|
S0S1S40ScS28S1fS4eA1A1A2S2A3"). Proof. vmr. Qed.
Lemma pc_meas : ltac2:(tb__ "0|1|
S0S1S7S2fS2cS1fS47A1A1M0S24A2S2fG0ScA2A2S2A3"). Proof. vmr. Qed.

Lemma da_chk : ltac2:(tb__ "0|0|
S0S1S3fS5dS5cS4aS12S55S4fA6S2A3"). Proof. vmr. Qed.
Lemma T_da2_eq : ltac2:(tb__ "0|0|
S0S6S20A1S39S52S4S36S38S4cA1S4S36S37U0A1S3S36A1A3A3A2S5S20S3cA2A3"). Proof. vmr. Qed.
Lemma T_da_eq2 : ltac2:(tb__ "0|0|
S0S20S45S3cSeSaSdA2A2S51A3"). Proof. vmr. Qed.
Lemma da_xsub : ltac2:(tb__ "0|0|
S0S1S5aSeSaSdA2S21S3cA1A2S2A3"). Proof. vmr. Qed.
Lemma da_vrF : ltac2:(tb__ "0|0|
S0S1S40ScS28S1fS4dA1A1A2S2A3"). Proof. vmr. Qed.
Lemma da_meas : ltac2:(tb__ "0|1|
S0S1S7S2fS2cS1fS4aA1A1M0S24A2S2fG0ScA2A2S2A3"). Proof. vmr. Qed.
Lemma dg_chk : ltac2:(tb__ "0|0|
S0S1S3fS5dS5cS5eS62S63S5fA6S2A3"). Proof. vmr. Qed.
Lemma T_dg2_eq : ltac2:(tb__ "0|0|
S0S6S20A1S39S61S4S36S38S4cA1S4S36S37U0A1S3S36A1A3A3A2S5S20S3dA2A3"). Proof. vmr. Qed.
Lemma T_dg_eq2 : ltac2:(tb__ "0|0|
S0S20S45S3dSeS13S14A2A2S60A3"). Proof. vmr. Qed.
Lemma dg_xsub : ltac2:(tb__ "0|0|
S0S1S5aSeS13S14A2S21S3dA1A2S2A3"). Proof. vmr. Qed.
End G.
End Lib_handle_f_g2.

(* [comment removed for export] *)
Module Lib_handle_f_gdefs3.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "ss_facts"; "SLit"; "dflt_writable"; "ob_base"; "ob_hi"; "ob_lo"; "ss_objs"; "sv_eqb"; "swf"; "@Corelib.Init.Datatypes"; "andb"; "false"; "bool"; "prod"; "nat"; "negb"; "None"; "Some"; "orb"; "@Stdlib.ZArith.BinInt.Z"; "leb"; "add"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@LinuxProcessSemantics.Riscv.Instr"; "aluop"; "mulop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "SHADOW_OFF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_X"; "ax_base"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs"; "hG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_defs"; "fr_hf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.et.Lib_handle_f_gdefs"; "feF"; "bF"; "fF"; "@Stdlib.Lists.List"; "filter"; "@Stdlib.PArith.BinPos.Pos"; "eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eg.Lib_builderH_pf"; "extraOH"; "extraXH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eu.Lib_handle_f_gdefs3"; "is_shx"; "xloc_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "xrs_inclb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS"; "robjs_checkF"; "shadow_reopen_stateA"; "wclear"; "xrs_checkL"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV ObjXform ObjUnbase TobjJVAz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAT ResidualA AxArrA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAM2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ResidualA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxArrA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double Lib_parse_corner2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Asan_set_shadow_iface.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_parse_corner2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.Lib_diag_append OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Asan_set_shadow_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eg.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_defs Lib_handle_f_s1 Lib_handle_f_s2 Lib_handle_f_s3 Lib_handle_f_s4 Lib_handle_f_s5 Lib_handle_f_s6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_s9 Lib_handle_f_s9b.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require es.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require en.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_nodes.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eh.Lib_builder_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eg.Lib_builderH_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_handle_f_s7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_handle_f_s8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s9b OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.es.Lib_handle_f_s10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.en.Lib_handle_f_epi OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_nodes.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_tess_polygon_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_arith.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Import ScanDoubleAddr VRAddr RA.ReallocAddr ParseCornerAddr DiagAppendAddr HFAddr.
Close Scope bv_scope.
Open Scope Z_scope.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require et.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.et.Lib_handle_f_gdefs.

Definition release0_chk (A : axst) (k1 k2 : Z) (d : odefault) : bool := ltac2:(tb__ "0|0|
SbSbSbSbS14Z0Vk1;A2S14Vk1;Vk2;A2A2S14Vk2;Z40A2A2S4Vd;A1A2S21S2S1cVA;A1A1A1A2").

Definition is_shx (k1 k2 : Z) (o : sobj) : bool := ltac2:(tb__ "0|7|
S0SdLx;M0S5Vo;A1S16ScLz;S17G0S7Vo;A1S16G0S6Vo;A1S16SbSbSbSbS25R3S1fA2S14S1bR2A2A2S14R2R1A2A2S14R1S15S1bZ40A2A2A2S13S14R1S15S1bVk1;A2A2S14S15S1bVk2;A2R2A2A2A2Lhi;S17ScLi;M1S19S0S0ScLb;La;M2Lop;M3G3S1aG2Lop;M4G4SdS18S0ScLa;Lw;Lsgn;M5S17S0S16ScLk;Li;Ll;M6X0x8Llo;G1G3G3G4G4G5G6X0x8Lg;G3G3G4G4G5G6X0x8").

Definition xloc_ok (k1 k2 : Z) (r : sv * sv) : bool := ltac2:(tb__ "0|9|
SeS0S0A2SdLr;Vr;S0S0S0SdLs;R2S16ScLz;M0S17ScLi;M1S19S0S0S19SdLop;R3S0SdLa;R2G0S17S0SdLb;R2S16S0SdLs0;R6S16SbSbSbSbS25R3Pa0A2S14Z0R2A2A2S14Z1R1A2A2S14S15R2R1A2Z200A2A2S2dVk1;Vk2;R2R1A4A2Llen;G1S19S0S0ScLb0;La0;M2Lop0;M3G3S1aG2Lop0;M4G4SdS18S0ScLa0;Lw;Lsgn;M5S17S0S16ScLk;Li;Ll;M6X0x8Loff;G1G3G3G4G4G5G6X0x8Lp;G3G3G4G4G5G6X0x8ScScScScScScScScScX19xaLb;La;Lop;S19S0S0ScLb;La;M7Lop;S1aG7Lop;M8G8SdS18S0ScLa;Lw;Lsgn;G6X0x8Ls0;Ls;Xex1").

Definition reopenS_chk (XGL : list (Z * Z)) (A : axst) (X' : list (sv * sv)) (tv : list (sv * sv)) (k1 k2 : Z) : bool := ltac2:(tb__ "0|4|
SbSbSbSbSbSbSbSbSbSbS9S1eVA;A1S3S1bA1A2S14Z0Vk1;A2A2S14Vk1;Vk2;A2A2S14Vk2;Z40A2A2S21S2S1cVA;A1M0A1M1A1A2S2aVX';S1dVA;A1A2A2SaS1cS2cVA;VX';S1fVk1;Vk2;A5A1A1A2S22G1A1A2S23G1A1A2S2bG1Vtv;S20S11SfA1S26S24S1S1S10S28Vk1;Vk2;R1A3A1Lo;S8G0A1M2A3A6A2S2eVXGL;G1Vtv;S20S12SfU0A2G2S27S24SeS0S0A2M3G3S10S29Vk1;Vk2;R1A3A1Lr;VX';A3A8A2").
End Lib_handle_f_gdefs3.

(* [comment removed for export] *)
Module Lib_handle_f_g4.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "SVar"; "SLit"; "SPUle"; "ss_facts"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "@Corelib.Init.Datatypes"; "nil"; "cons"; "bool"; "list"; "true"; "pair"; "prod"; "app"; "Some"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bitem"; "bd_subst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_defs.VN"; "Pre_vr"; "P_grown"; "P_keep"; "P_fail"; "tv0"; "bdP"; "nd0"; "tvP"; "vKn"; "vN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs"; "kb"; "hG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_defs"; "tr_d"; "ts_d"; "tr_k"; "rp_d"; "ts_k"; "X_body"; "pDco"; "pKco"; "rp_k"; "xf_vr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_subA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "nd_bd"; "nd_tv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s2"; "XkeepF"; "xf_backV"; "ndXA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.et.Lib_handle_f_gdefs"; "land_chk"; "kept_ts"; "brest_rp"; "brest_trb"; "brest_trg"; "brest_ts"; "kept_rp"; "kept_trb"; "kept_trg"; "xff_chk"; "E_ts1x"; "T_rpk1"; "T_trbk1"; "T_trgk1"; "T_tsk1"; "vr_chk"; "E_rp1x"; "E_trb1x"; "E_trg1x"; "T_rpf0"; "T_rpg0"; "T_rpk0"; "T_trbf0"; "T_trbg0"; "T_trbk0"; "T_trgf0"; "T_trgg0"; "T_trgk0"; "T_tsf0"; "T_tsg0"; "T_tsk0"; "bd2_rpg"; "bd2_rpk"; "bd2_trbg"; "bd2_trbk"; "bd2_trgg"; "bd2_trgk"; "bd2_tsg"; "bd2_tsk"; "bdG_rp"; "bdG_trb"; "bdG_trg"; "bdG_ts"; "bdK_rp"; "bdK_trb"; "bdK_trg"; "bdK_ts"; "liveTri"; "reopen_chk"; "s_rpf"; "s_rpg"; "s_rpk"; "s_trbf"; "s_trbg"; "s_trbk"; "s_trgf"; "s_trgg"; "s_trgk"; "s_tsf"; "s_tsg"; "s_tsk"; "liveRp"; "liveTs"; "triAF"; "tv2_rpf"; "tv2_rpg"; "tv2_rpk"; "tv2_trbf"; "tv2_trbg"; "tv2_trbk"; "tv2_trgf"; "tv2_trgg"; "tv2_trgk"; "tv2_tsf"; "tv2_tsg"; "tv2_tsk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "import_tv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "T_afterA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_nodes"; "ndTR"; "ndRP"; "ndTRf"; "ndTS"; "ndRPf"; "ndTSf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s4"; "E_trb"; "E_trg"; "s_trb"; "s_trg"; "R_trb"; "R_trg"; "XTR"; "pDtr"; "pKtr"; "JR_trb"; "JR_trg"; "T_trbf"; "T_trbg"; "T_trbk"; "T_trgf"; "T_trgg"; "T_trgk"; "E_trb0"; "E_trg0"; "JF_trb"; "JF_trg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s5"; "E_rp"; "E_ts"; "s_rp"; "s_ts"; "T_tsg"; "T_tsk"; "R_rp"; "R_ts"; "XRT"; "pDrp"; "pKrp"; "JR_rp"; "JR_ts"; "T_rpf"; "T_rpg"; "T_rpk"; "T_tsf"; "need_facts"; "E_rp0"; "E_ts0"; "JF_rp"; "JF_ts"; "@Corelib.Lists.ListDef"; "firstn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG"; "tv_permb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS"; "shadow_reopen_stateA"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV ObjXform ObjUnbase TobjJVAz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAT ResidualA AxArrA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAM2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ResidualA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxArrA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double Lib_parse_corner2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Asan_set_shadow_iface.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_parse_corner2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.Lib_diag_append OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Asan_set_shadow_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eg.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_defs Lib_handle_f_s1 Lib_handle_f_s2 Lib_handle_f_s3 Lib_handle_f_s4 Lib_handle_f_s5 Lib_handle_f_s6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_s9 Lib_handle_f_s9b.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require es.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require en.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_nodes.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eh.Lib_builder_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eg.Lib_builderH_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_handle_f_s7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_handle_f_s8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s9b OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.es.Lib_handle_f_s10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.en.Lib_handle_f_epi OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_nodes.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_tess_polygon_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_arith.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Import ScanDoubleAddr VRAddr RA.ReallocAddr ParseCornerAddr DiagAppendAddr HFAddr.
Close Scope bv_scope.
Open Scope Z_scope.
Module PGC. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_tess_polygon_cstates. End PGC.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require et.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.et.Lib_handle_f_gdefs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import MemoFast.
Ltac vmr := vmc.

Section G.
Variable XGL : list (Z * Z).

Lemma E_trg1x_eq : ltac2:(tb__ "0|0|
S6S13S7A1S32S99S2bU15Z310A2A2S12S7S45A2A3"). Proof. vmr. Qed.
Lemma E_trg_eq2 : ltac2:(tb__ "0|0|
S6S7Sb3SaS1A1S45A2S88A3"). Proof. vmr. Qed.
Lemma trg_tvp : ltac2:(tb__ "0|1|
S6ScSb5S2eS31A1S11S10S0S0A2M0S3bSbG0SfS0S0S22S20Z4S24A2A4SaG0A1A3A3A2SeA3"). Proof. vmr. Qed.
Lemma trg_chk : ltac2:(tb__ "0|0|
S6ScS42VXGL;S88S3bS22S24Z4Z310S2dS31A1S37S8aS8cS2fS22S27S28S29A2A2AcSeA3"). Proof. vmr. Qed.
Lemma trg_iK : ltac2:(tb__ "0|1|
S6SdS10S0S0A2M0A1S7fS2cS8aS16S18S88A4S1aA2SbG0SfS0S0S22S20Z4S24A2A4SaG0A1A3A3"). Proof. vmr. Qed.
Lemma trg_iF : ltac2:(tb__ "0|1|
S6SdS10S0S0A2M0A1S7fS2cS8aS16S19S88A4S1aA2SbG0SfS0S0S22S20Z4S24A2A4SaG0A1A3A3"). Proof. vmr. Qed.
Lemma trg_iG : ltac2:(tb__ "0|1|
S6SdS10S0S0A2M0A1S7fS2cS8aS16S17S88A4S1dA2SbG0SfS0S0S2P208A1S20Z4S2P209A1A2A4SaG0A1A3A3"). Proof. vmr. Qed.
Lemma trg_bK : ltac2:(tb__ "0|0|
S6SdS14A1S15S2cS8aS16S18S88A4S2dS1cA1A2S60A3"). Proof. vmr. Qed.
Lemma trg_bG : ltac2:(tb__ "0|0|
S6SdS14A1S15S2cS8aS16S17S88A4S1bS1fS1eA2A2S5cA3"). Proof. vmr. Qed.
Lemma T_trgk0_ta : ltac2:(tb__ "0|0|
S6S7S80S16S88S8aS8cS18S2fS22S27S28S29A2A2A6S4eA3"). Proof. vmr. Qed.
Lemma T_trgk1_ap : ltac2:(tb__ "0|0|
S6S13S7A1S32S4eS30U14U22Z310A3A2S12S7S40A2A3"). Proof. vmr. Qed.
Lemma T_trgk_eq2 : ltac2:(tb__ "0|0|
S6S7Sb3SbS1S4S3Sb4A1S22A2SaS1A1A3S40A2S97A3"). Proof. vmr. Qed.
Lemma trgk_xff : ltac2:(tb__ "0|0|
S6ScS3cS40SbS1S4S3Sb4A1S22A2SaS1A1A3A2SeA3"). Proof. vmr. Qed.
Lemma trgk_land : ltac2:(tb__ "0|1|
S6ScS33S97S91S6cS11S10S0S0A2M0S3bSbG0SfS0S0S22S20Z4S24A2A4SaG0A1A3A3S7bS11S14S60S37A3S57S2eS81A1A8SeA3"). Proof. vmr. Qed.
Lemma trgk_bd : ltac2:(tb__ "0|0|
S6SdS14A1S15S6cS2dS81A1A2S57A3"). Proof. vmr. Qed.
Lemma trgk_live : ltac2:(tb__ "0|0|
S6ScS62S24S5S8S40A1A1A2SeA3"). Proof. vmr. Qed.
Lemma T_trgf0_ta : ltac2:(tb__ "0|0|
S6S7S80S16S88S8aS8cS19S2fS22S27S28S29A2A2A6S4cA3"). Proof. vmr. Qed.
Lemma T_trgf_ap : ltac2:(tb__ "0|0|
S6S13S7A1S32S4cS30U14U22Z310A3A2S12S7S95A2A3"). Proof. vmr. Qed.
Lemma trgf_land : ltac2:(tb__ "0|2|
S6ScS33S95S9bS6aS11S10S0S0A2M0S3bSbG0SfS0S0S22S20Z4S24A2A4SaG0A1A3A3S79Sb2S14U1S37A3M1G1S2eS83A1A8SeA3"). Proof. vmr. Qed.
Lemma trgf_bd : ltac2:(tb__ "0|0|
S6SdS14A1S15S6aS2dS83A1A2Sb2S14U1S37A3A3"). Proof. vmr. Qed.
Lemma T_trgg0_ta : ltac2:(tb__ "0|0|
S6S7S80S16S88S8aS8cS17S2fS22S27S28S29A2A2A6S4dA3"). Proof. vmr. Qed.
Lemma T_trgg_ap : ltac2:(tb__ "0|0|
S6S13S7A1S32S4dS30U14U22Z310A3A2S12S7S96A2A3"). Proof. vmr. Qed.
Lemma trgg_land : ltac2:(tb__ "0|1|
S6ScS33S96S91S6bS11S10S0S0A2M0S3bSbG0SfS0S0S2P208A1S20Z4S2P209A1A2A4SaG0A1A3A3S7aS11S14S5cS37A3S56S2eS81A1A8SeA3"). Proof. vmr. Qed.
Lemma trgg_bd : ltac2:(tb__ "0|0|
S6SdS14A1S15S6bS2dS81A1A2S56A3"). Proof. vmr. Qed.
Lemma trgf_wp : bd_wpos brest_trg = true. Proof. vmr. Qed.

Lemma E_trb1x_eq : ltac2:(tb__ "0|0|
S6S13S7A1S32S98S2bU15Z310A2A2S12S7S44A2A3"). Proof. vmr. Qed.
Lemma E_trb_eq2 : ltac2:(tb__ "0|0|
S6S7Sb3SaS1A1S44A2S87A3"). Proof. vmr. Qed.
Lemma trb_tvp : ltac2:(tb__ "0|1|
S6ScSb5S2eS31A1S11S10S0S0A2M0S3aSbG0SfS0S0S22S20Z4S24A2A4SaG0A1A3A3A2SeA3"). Proof. vmr. Qed.
Lemma trb_chk : ltac2:(tb__ "0|0|
S6ScS42VXGL;S87S3aS22S24Z4Z310S2dS31A1S36S89S8bS2fS22S27S28S29A2A2AcSeA3"). Proof. vmr. Qed.
Lemma trb_iK : ltac2:(tb__ "0|1|
S6SdS10S0S0A2M0A1S7fS2cS89S16S18S87A4S1aA2SbG0SfS0S0S22S20Z4S24A2A4SaG0A1A3A3"). Proof. vmr. Qed.
Lemma trb_iF : ltac2:(tb__ "0|1|
S6SdS10S0S0A2M0A1S7fS2cS89S16S19S87A4S1aA2SbG0SfS0S0S22S20Z4S24A2A4SaG0A1A3A3"). Proof. vmr. Qed.
Lemma trb_iG : ltac2:(tb__ "0|1|
S6SdS10S0S0A2M0A1S7fS2cS89S16S17S87A4S1dA2SbG0SfS0S0S2P208A1S20Z4S2P209A1A2A4SaG0A1A3A3"). Proof. vmr. Qed.
Lemma trb_bK : ltac2:(tb__ "0|0|
S6SdS14A1S15S2cS89S16S18S87A4S2dS1cA1A2S5fA3"). Proof. vmr. Qed.
Lemma trb_bG : ltac2:(tb__ "0|0|
S6SdS14A1S15S2cS89S16S17S87A4S1bS1fS1eA2A2S5bA3"). Proof. vmr. Qed.
Lemma T_trbk0_ta : ltac2:(tb__ "0|0|
S6S7S80S16S87S89S8bS18S2fS22S27S28S29A2A2A6S4bA3"). Proof. vmr. Qed.
Lemma T_trbk1_ap : ltac2:(tb__ "0|0|
S6S13S7A1S32S4bS30U14U22Z310A3A2S12S7S3fA2A3"). Proof. vmr. Qed.
Lemma T_trbk_eq2 : ltac2:(tb__ "0|0|
S6S7Sb3SbS1S4S3Sb4A1S22A2SaS1A1A3S3fA2S94A3"). Proof. vmr. Qed.
Lemma trbk_xff : ltac2:(tb__ "0|0|
S6ScS3cS3fSbS1S4S3Sb4A1S22A2SaS1A1A3A2SeA3"). Proof. vmr. Qed.
Lemma trbk_land : ltac2:(tb__ "0|1|
S6ScS33S94S90S69S11S10S0S0A2M0S3aSbG0SfS0S0S22S20Z4S24A2A4SaG0A1A3A3S78S11S14S5fS36A3S55S2eS81A1A8SeA3"). Proof. vmr. Qed.
Lemma trbk_bd : ltac2:(tb__ "0|0|
S6SdS14A1S15S69S2dS81A1A2S55A3"). Proof. vmr. Qed.
Lemma trbk_live : ltac2:(tb__ "0|0|
S6ScS62S24S5S8S3fA1A1A2SeA3"). Proof. vmr. Qed.
Lemma T_trbf0_ta : ltac2:(tb__ "0|0|
S6S7S80S16S87S89S8bS19S2fS22S27S28S29A2A2A6S49A3"). Proof. vmr. Qed.
Lemma T_trbf_ap : ltac2:(tb__ "0|0|
S6S13S7A1S32S49S30U14U22Z310A3A2S12S7S92A2A3"). Proof. vmr. Qed.
Lemma trbf_land : ltac2:(tb__ "0|2|
S6ScS33S92S9aS67S11S10S0S0A2M0S3aSbG0SfS0S0S22S20Z4S24A2A4SaG0A1A3A3S76Sb2S14U1S36A3M1G1S2eS83A1A8SeA3"). Proof. vmr. Qed.
Lemma trbf_bd : ltac2:(tb__ "0|0|
S6SdS14A1S15S67S2dS83A1A2Sb2S14U1S36A3A3"). Proof. vmr. Qed.
Lemma T_trbg0_ta : ltac2:(tb__ "0|0|
S6S7S80S16S87S89S8bS17S2fS22S27S28S29A2A2A6S4aA3"). Proof. vmr. Qed.
Lemma T_trbg_ap : ltac2:(tb__ "0|0|
S6S13S7A1S32S4aS30U14U22Z310A3A2S12S7S93A2A3"). Proof. vmr. Qed.
Lemma trbg_land : ltac2:(tb__ "0|1|
S6ScS33S93S90S68S11S10S0S0A2M0S3aSbG0SfS0S0S2P208A1S20Z4S2P209A1A2A4SaG0A1A3A3S77S11S14S5bS36A3S54S2eS81A1A8SeA3"). Proof. vmr. Qed.
Lemma trbg_bd : ltac2:(tb__ "0|0|
S6SdS14A1S15S68S2dS81A1A2S54A3"). Proof. vmr. Qed.
Lemma trbf_wp : bd_wpos brest_trb = true. Proof. vmr. Qed.

Lemma E_rp1x_eq : ltac2:(tb__ "0|0|
S6S13S7A1S32SaeS2bU14Z2f0A2A2S12S7S43A2A3"). Proof. vmr. Qed.
Lemma E_rp_eq2 : ltac2:(tb__ "0|0|
S6S7Sb3SaS1A1S43A2S9cA3"). Proof. vmr. Qed.
Lemma rp_tvp : ltac2:(tb__ "0|1|
S6ScSb5S2eS81A1S11S10S0S0A2M0S39SbG0SfS0S0S25S20Z4S2aA2A4SaG0A1A3A3A2SeA3"). Proof. vmr. Qed.
Lemma rp_chk : ltac2:(tb__ "0|0|
S6ScS42VXGL;S9cS39S25S2aZ4Z2f0S2dS81A1S35S9eSa2S2fS25S8dS8eS8fA2A2AcSeA3"). Proof. vmr. Qed.
Lemma rp_iK : ltac2:(tb__ "0|1|
S6SdS10S0S0A2M0A1S7fS2cS9eS16S18S9cA4S1aA2SbG0SfS0S0S25S20Z4S2aA2A4SaG0A1A3A3"). Proof. vmr. Qed.
Lemma rp_iF : ltac2:(tb__ "0|1|
S6SdS10S0S0A2M0A1S7fS2cS9eS16S19S9cA4S1aA2SbG0SfS0S0S25S20Z4S2aA2A4SaG0A1A3A3"). Proof. vmr. Qed.
Lemma rp_iG : ltac2:(tb__ "0|1|
S6SdS10S0S0A2M0A1S7fS2cS9eS16S17S9cA4S1dA2SbG0SfS0S0S2P208A1S20Z4S2P209A1A2A4SaG0A1A3A3"). Proof. vmr. Qed.
Lemma rp_bK : ltac2:(tb__ "0|0|
S6SdS14A1S15S2cS9eS16S18S9cA4S2dS1cA1A2S5eA3"). Proof. vmr. Qed.
Lemma rp_bG : ltac2:(tb__ "0|0|
S6SdS14A1S15S2cS9eS16S17S9cA4S1bS1fS1eA2A2S5aA3"). Proof. vmr. Qed.
Lemma T_rpk0_ta : ltac2:(tb__ "0|0|
S6S7S80S16S9cS9eSa2S18S2fS25S8dS8eS8fA2A2A6S48A3"). Proof. vmr. Qed.
Lemma T_rpk1_ap : ltac2:(tb__ "0|0|
S6S13S7A1S32S48S30U13U21Z2f0A3A2S12S7S3eA2A3"). Proof. vmr. Qed.
Lemma T_rpk_eq2 : ltac2:(tb__ "0|0|
S6S7Sb3SbS1S4S3Sb4A1S25A2SaS1A1A3S3eA2SabA3"). Proof. vmr. Qed.
Lemma rpk_xff : ltac2:(tb__ "0|0|
S6ScS3cS3eSbS1S4S3Sb4A1S25A2SaS1A1A3A2SeA3"). Proof. vmr. Qed.
Lemma rpk_land : ltac2:(tb__ "0|1|
S6ScS33SabSa7S66S11S10S0S0A2M0S39SbG0SfS0S0S25S20Z4S2aA2A4SaG0A1A3A3S75S11S14S5eS35A3S53S2eS82A1A8SeA3"). Proof. vmr. Qed.
Lemma rpk_bd : ltac2:(tb__ "0|0|
S6SdS14A1S15S66S2dS82A1A2S53A3"). Proof. vmr. Qed.
Lemma rpk_live : ltac2:(tb__ "0|0|
S6ScS70S2aS5S8S3eA1A1A2SeA3"). Proof. vmr. Qed.
Lemma T_rpf0_ta : ltac2:(tb__ "0|0|
S6S7S80S16S9cS9eSa2S19S2fS25S8dS8eS8fA2A2A6S46A3"). Proof. vmr. Qed.
Lemma T_rpf_ap : ltac2:(tb__ "0|0|
S6S13S7A1S32S46S30U13U21Z2f0A3A2S12S7Sa9A2A3"). Proof. vmr. Qed.
Lemma rpf_land : ltac2:(tb__ "0|2|
S6ScS33Sa9Sb0S64S11S10S0S0A2M0S39SbG0SfS0S0S25S20Z4S2aA2A4SaG0A1A3A3S73Sb2S14U1S35A3M1G1S2eS85A1A8SeA3"). Proof. vmr. Qed.
Lemma rpf_bd : ltac2:(tb__ "0|0|
S6SdS14A1S15S64S2dS85A1A2Sb2S14U1S35A3A3"). Proof. vmr. Qed.
Lemma T_rpg0_ta : ltac2:(tb__ "0|0|
S6S7S80S16S9cS9eSa2S17S2fS25S8dS8eS8fA2A2A6S47A3"). Proof. vmr. Qed.
Lemma T_rpg_ap : ltac2:(tb__ "0|0|
S6S13S7A1S32S47S30U13U21Z2f0A3A2S12S7SaaA2A3"). Proof. vmr. Qed.
Lemma rpg_land : ltac2:(tb__ "0|1|
S6ScS33SaaSa7S65S11S10S0S0A2M0S39SbG0SfS0S0S2P208A1S20Z4S2P209A1A2A4SaG0A1A3A3S74S11S14S5aS35A3S52S2eS82A1A8SeA3"). Proof. vmr. Qed.
Lemma rpg_bd : ltac2:(tb__ "0|0|
S6SdS14A1S15S65S2dS82A1A2S52A3"). Proof. vmr. Qed.
Lemma rpf_wp : bd_wpos brest_rp = true. Proof. vmr. Qed.

Lemma E_ts1x_eq : ltac2:(tb__ "0|0|
S6S13S7A1S32SafS2bU16Z330A2A2S12S7S3dA2A3"). Proof. vmr. Qed.
Lemma E_ts_eq2 : ltac2:(tb__ "0|0|
S6S7Sb3SadS3dA2S9dA3"). Proof. vmr. Qed.
Lemma ts_xff : ltac2:(tb__ "0|0|
S6ScS3cS3dSadA2SeA3"). Proof. vmr. Qed.
Lemma ts_needF : ltac2:(tb__ "0|0|
S6ScS72S5S8S3dA1A1A1SeA3"). Proof. vmr. Qed.
Lemma ts_tvp : ltac2:(tb__ "0|1|
S6ScSb5S2eS82A1S11S10S0S0A2M0S34SbG0SfS0S0S23S20Z1S26A2A4SaG0A1A3A3A2SeA3"). Proof. vmr. Qed.
Lemma ts_chk : ltac2:(tb__ "0|0|
S6ScS42VXGL;S9dS34S23S26Z1Z330S2dS82A1S38S9fSa3S2fS23Sa4Sa5Sa6S23S26A4A2AcSeA3"). Proof. vmr. Qed.
Lemma ts_iK : ltac2:(tb__ "0|1|
S6SdS10S0S0A2M0A1S7fS2cS9fS16S18S9dA4S1aA2SbG0SfS0S0S23S20Z1S26A2A4SaG0A1A3A3"). Proof. vmr. Qed.
Lemma ts_iF : ltac2:(tb__ "0|1|
S6SdS10S0S0A2M0A1S7fS2cS9fS16S19S9dA4S1aA2SbG0SfS0S0S23S20Z1S26A2A4SaG0A1A3A3"). Proof. vmr. Qed.
Lemma ts_iG : ltac2:(tb__ "0|1|
S6SdS10S0S0A2M0A1S7fS2cS9fS16S17S9dA4S1dA2SbG0SfS0S0S2P208A1S20Z1S2P209A1A2A4SaG0A1A3A3"). Proof. vmr. Qed.
Lemma ts_bK : ltac2:(tb__ "0|0|
S6SdS14A1S15S2cS9fS16S18S9dA4S2dS1cA1A2S61A3"). Proof. vmr. Qed.
Lemma ts_bG : ltac2:(tb__ "0|0|
S6SdS14A1S15S2cS9fS16S17S9dA4S1bS1fS1eA2A2S5dA3"). Proof. vmr. Qed.
Lemma T_tsk0_ta : ltac2:(tb__ "0|0|
S6S7S80S16S9dS9fSa3S18S2fS23Sa4Sa5Sa6S23S26A4A2A6S51A3"). Proof. vmr. Qed.
Lemma T_tsk1_ap : ltac2:(tb__ "0|0|
S6S13S7A1S32S51S30U15U23Z330A3A2S12S7S41A2A3"). Proof. vmr. Qed.
Lemma T_tsk_eq2 : ltac2:(tb__ "0|0|
S6S7Sb3SbS1S4S3Sb4A1S23A2SaS1A1A3S41A2Sa1A3"). Proof. vmr. Qed.
Lemma tsk_xff : ltac2:(tb__ "0|0|
S6ScS3cS41SbS1S4S3Sb4A1S23A2SaS1A1A3A2SeA3"). Proof. vmr. Qed.
Lemma tsk_ro0 : ltac2:(tb__ "0|1|
S6ScS63VXGL;Sa1S9Sa1A1S11S10S0S0A2M0S34SbG0SfS0S0S23S20Z1S26A2A4SaG0A1A3A3Z6ZfA6SeA3"). Proof. vmr. Qed.
Lemma tsk_land : ltac2:(tb__ "0|1|
S6ScS33Sb6Sa1S9Sa1A1S21Z6ZfA5Sa8S6fS11S10S0S0A2M0S34SbG0SfS0S0S23S20Z1S26A2A4SaG0A1A3A3S7eS11S14S61S38A3S59S2eS84A1A8SeA3"). Proof. vmr. Qed.
Lemma tsk_bd : ltac2:(tb__ "0|0|
S6SdS14A1S15S6fS2dS84A1A2S59A3"). Proof. vmr. Qed.
Lemma tsk_live : ltac2:(tb__ "0|0|
S6ScS71S26S5S8S41A1A1A2SeA3"). Proof. vmr. Qed.
Lemma T_tsf0_ta : ltac2:(tb__ "0|0|
S6S7S80S16S9dS9fSa3S19S2fS23Sa4Sa5Sa6S23S26A4A2A6S4fA3"). Proof. vmr. Qed.
Lemma T_tsf_ap : ltac2:(tb__ "0|0|
S6S13S7A1S32S4fS30U15U23Z330A3A2S12S7SacA2A3"). Proof. vmr. Qed.
Lemma tsf_land : ltac2:(tb__ "0|2|
S6ScS33SacSb1S6dS11S10S0S0A2M0S34SbG0SfS0S0S23S20Z1S26A2A4SaG0A1A3A3S7cSb2S14U1S38A3M1G1S2eS86A1A8SeA3"). Proof. vmr. Qed.
Lemma tsf_bd : ltac2:(tb__ "0|0|
S6SdS14A1S15S6dS2dS86A1A2Sb2S14U1S38A3A3"). Proof. vmr. Qed.
Lemma T_tsg0_ta : ltac2:(tb__ "0|0|
S6S7S80S16S9dS9fSa3S17S2fS23Sa4Sa5Sa6S23S26A4A2A6S50A3"). Proof. vmr. Qed.
Lemma T_tsg_ap : ltac2:(tb__ "0|0|
S6S13S7A1S32S50S30U15U23Z330A3A2S12S7Sa0A2A3"). Proof. vmr. Qed.
Lemma tsg_ro0 : ltac2:(tb__ "0|1|
S6ScS63VXGL;Sa0S9Sa0A1S11S10S0S0A2M0S34SbG0SfS0S0S2P208A1S20Z1S2P209A1A2A4SaG0A1A3A3Z6ZfA6SeA3"). Proof. vmr. Qed.
Lemma tsg_land : ltac2:(tb__ "0|1|
S6ScS33Sb6Sa0S9Sa0A1S21Z6ZfA5Sa8S6eS11S10S0S0A2M0S34SbG0SfS0S0S2P208A1S20Z1S2P209A1A2A4SaG0A1A3A3S7dS11S14S5dS38A3S58S2eS84A1A8SeA3"). Proof. vmr. Qed.
Lemma tsg_bd : ltac2:(tb__ "0|0|
S6SdS14A1S15S6eS2dS84A1A2S58A3"). Proof. vmr. Qed.
Lemma tsf_wp : bd_wpos brest_ts = true. Proof. vmr. Qed.
End G.
End Lib_handle_f_g4.

(* [comment removed for export] *)
Module Lib_handle_f_g3.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "SVar"; "SLit"; "ss_facts"; "SAlu"; "SPUle"; "sobj"; "DUnknown"; "ss_objs"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "@Corelib.Init.Datatypes"; "cons"; "bool"; "nil"; "true"; "pair"; "prod"; "list"; "app"; "Some"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bitem"; "bd_subst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs"; "kb"; "hG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_defs.VN"; "Pre_vr"; "P_grown"; "P_keep"; "P_fail"; "tv0"; "bdP"; "nd0"; "tvP"; "vKn"; "vN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "nd_bd"; "nd_tv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_subA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_defs"; "mm_d"; "sg_d"; "fv_d"; "mi_d"; "mm_k"; "pA"; "sg_k"; "fv_k"; "pKco"; "mi_k"; "pDco"; "X_body"; "fv_c"; "mi_c"; "mm_c"; "sg_c"; "xf_vr"; "rp_d"; "rp_k"; "tr_d"; "tr_k"; "ts_d"; "ts_k"; "fv_n"; "mi_n"; "mm_n"; "sg_n"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s2"; "XkeepF"; "xf_backV"; "E_fv"; "E_mi"; "E_mm"; "s_fv"; "s_mi"; "s_mm"; "vr_need"; "co_live"; "T_migs"; "T_mik"; "T_miks"; "R_fv"; "R_mi"; "R_mm"; "T_fvk"; "T_mif"; "T_mig"; "T_mmk"; "XF1"; "XFV"; "pDfv"; "pKfv"; "T_fvf"; "T_mmf"; "E_fv0"; "JR_fv"; "JR_mi"; "NFV"; "NMI"; "NMM"; "NSG"; "T_fvf0"; "T_fvg"; "T_fvg0"; "T_fvk0"; "T_fvks"; "T_mif0"; "T_mifs"; "T_mig0"; "T_mik0"; "T_mmf0"; "T_mmg"; "T_mmg0"; "T_mmk0"; "X_face"; "ndXA"; "objs_fv0"; "pDmi"; "pKmi"; "E_fv1"; "E_mi0"; "E_mm0"; "JF_fv"; "JF_mi"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.et.Lib_handle_f_gdefs"; "land_chk"; "xff_chk"; "kept_sg"; "kept_mi"; "reopen_chk"; "kept_fv"; "kept_mm"; "brest_fv"; "brest_mi"; "brest_mm"; "brest_sg"; "E_fv1x"; "E_mi1x"; "E_mm1x"; "E_sg1x"; "liveF"; "vr3F"; "vr_chk"; "live3F"; "bd2_fvg"; "bd2_fvk"; "bd2_mig"; "bd2_mik"; "bd2_mmg"; "bd2_mmk"; "bd2_sgg"; "bd2_sgk"; "bdG_fv"; "bdG_mi"; "bdG_mm"; "bdG_sg"; "bdK_fv"; "bdK_mi"; "bdK_mm"; "bdK_sg"; "cells_fv"; "s_fvf"; "s_fvg"; "s_fvk"; "s_mif"; "s_mig"; "s_mik"; "s_mmf"; "s_mmg"; "s_mmk"; "s_sgf"; "s_sgg"; "s_sgk"; "release_chk"; "tv2_fvf"; "tv2_fvg"; "tv2_fvk"; "tv2_mif"; "tv2_mig"; "tv2_mik"; "tv2_mmf"; "tv2_mmg"; "tv2_mmk"; "tv2_sgf"; "tv2_sgg"; "tv2_sgk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "import_tv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "T_afterA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s3"; "E_sg"; "s_sg"; "XMM"; "XnoL"; "T_sgf"; "T_sgg"; "T_sgks"; "R_sg"; "T_sgk"; "pDmm"; "pKmm"; "JR_mm"; "JR_sg"; "T_mmks"; "T_sgf0"; "T_sgg0"; "T_sgk0"; "E_sg0"; "JF_mm"; "JF_sg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@Corelib.Lists.ListDef"; "firstn"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_nodes"; "ndMI"; "ndFV"; "ndMM"; "ndSG"; "ndFVf"; "ndMIf"; "ndMMf";
"ndSGf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS"; "shadow_reopen_stateA"; "shobj"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG"; "tv_permb"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV ObjXform ObjUnbase TobjJVAz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAT ResidualA AxArrA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAM2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ResidualA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxArrA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double Lib_parse_corner2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Asan_set_shadow_iface.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_parse_corner2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.Lib_diag_append OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Asan_set_shadow_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eg.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_defs Lib_handle_f_s1 Lib_handle_f_s2 Lib_handle_f_s3 Lib_handle_f_s4 Lib_handle_f_s5 Lib_handle_f_s6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_s9 Lib_handle_f_s9b.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require es.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require en.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_nodes.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eh.Lib_builder_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eg.Lib_builderH_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_handle_f_s7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_handle_f_s8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s9b OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.es.Lib_handle_f_s10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.en.Lib_handle_f_epi OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_nodes.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_tess_polygon_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_arith.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Import ScanDoubleAddr VRAddr RA.ReallocAddr ParseCornerAddr DiagAppendAddr HFAddr.
Close Scope bv_scope.
Open Scope Z_scope.
Module PGC. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_tess_polygon_cstates. End PGC.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require et.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.et.Lib_handle_f_gdefs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import MemoFast.
Ltac vmr := vmc.

Section G.
Variable XGL : list (Z * Z).

Lemma E_mi1x_eq : ltac2:(tb__ "0|0|
SaS17SbA1S7cS78S39UfZ1f0A2A2S16SbS89A2A3"). Proof. vmr. Qed.
Lemma E_mi_eq2 : ltac2:(tb__ "0|0|
SaSbSd0S4cZcS5Sd2S36S3Z3A1A3S62S2eA1A3S89A2S47A3"). Proof. vmr. Qed.
Lemma mi_xff : ltac2:(tb__ "0|0|
SaSfS7eS89S4cZcS5Sd2S36S3Z3A1A3S62S2eA1A3A2S11A3"). Proof. vmr. Qed.
Lemma mi_needF : ltac2:(tb__ "0|0|
SaSfS8dZcZ3Z24S36S41S4ScS89A1A1A6S11A3"). Proof. vmr. Qed.
Lemma mi_tvp : ltac2:(tb__ "0|1|
SaSfSdfS27S73A1S15S13S0S0A2M0S80SeG0S12S0S0S2cS1aZcS32A2A4S10G0A1A3A3A2S11A3"). Proof. vmr. Qed.
Lemma mi_chk : ltac2:(tb__ "0|0|
SaSfS8eVXGL;S47S80S2cS32ZcZ1f0S26S73A1S85S4aS52S44S2cS34S33S31A2A2AcS11A3"). Proof. vmr. Qed.
Lemma mi_iK : ltac2:(tb__ "0|1|
SaS14S13S0S0A2M0A1SbaS28S4aS1cS1eS47A4S20A2SeG0S12S0S0S2cS1aZcS32A2A4S10G0A1A3A3"). Proof. vmr. Qed.
Lemma mi_iF : ltac2:(tb__ "0|1|
SaS14S13S0S0A2M0A1SbaS28S4aS1cS1fS47A4S20A2SeG0S12S0S0S2cS1aZcS32A2A4S10G0A1A3A3"). Proof. vmr. Qed.
Lemma mi_iG : ltac2:(tb__ "0|1|
SaS14S13S0S0A2M0A1SbaS28S4aS1cS1dS47A4S23A2SeG0S12S0S0S2P208A1S1aZcS2P209A1A2A4S10G0A1A3A3"). Proof. vmr. Qed.
Lemma mi_bK : ltac2:(tb__ "0|0|
SaS14S18A1S19S28S4aS1cS1eS47A4S26S22A1A2S9dA3"). Proof. vmr. Qed.
Lemma mi_bG : ltac2:(tb__ "0|0|
SaS14S18A1S19S28S4aS1cS1dS47A4S21S25S24A2A2S99A3"). Proof. vmr. Qed.
Lemma T_mik0_ta : ltac2:(tb__ "0|0|
SaSbSbbS1cS47S4aS52S1eS44S2cS34S33S31A2A2A6S6dA3"). Proof. vmr. Qed.
Lemma T_mik_ap : ltac2:(tb__ "0|0|
SaS17SbA1S7cS6dS45UeU1cZ1f0A3A2S16SbS4fA2A3"). Proof. vmr. Qed.
Lemma T_miks_eq2 : ltac2:(tb__ "0|0|
SaSbSd0SeS1S6S3SdbA1S2cA2SeS1S4dS10S1A1A3A3S4fA2S50A3"). Proof. reflexivity. Qed.
Lemma mik_xff : ltac2:(tb__ "0|0|
SaSfS7eS4fSeS1S6S3SdbA1S2cA2SeS1S4dS10S1A1A3A3A2S11A3"). Proof. vmr. Qed.
Lemma mik_ro0 : ltac2:(tb__ "0|1|
SaSfS81VXGL;S50SdS50A1S15S13S0S0A2M0S80SeG0S12S0S0S2cS1aZcS32A2A4S10G0A1A3A3Z4Z5A6S11A3"). Proof. vmr. Qed.
Lemma mik_land : ltac2:(tb__ "0|1|
SaSfS7dSdcS50SdS50A1S1bZ4Z5A5S60Sa6S15S13S0S0A2M0S80SeG0S12S0S0S2cS1aZcS32A2A4S10G0A1A3A3Sb3S15S18S9dS85A3S93S27Sd3A1A8S11A3"). Proof. vmr. Qed.
Lemma mik_bd : ltac2:(tb__ "0|0|
SaS14S18A1S19Sa6S26Sd3A1A2S93A3"). Proof. vmr. Qed.
Lemma mik_live : ltac2:(tb__ "0|0|
SaSfS8cS36Z3S32S4ScS4fA1A1A4S11A3"). Proof. vmr. Qed.
Lemma mik_colive : ltac2:(tb__ "0|0|
SaSfS8fS2eS31S4ScS4fA1A1A3S11A3"). Proof. vmr. Qed.
Lemma T_mif0_ta : ltac2:(tb__ "0|0|
SaSbSbbS1cS47S4aS52S1fS44S2cS34S33S31A2A2A6S6aA3"). Proof. vmr. Qed.
Lemma T_mif_ap : ltac2:(tb__ "0|0|
SaS17SbA1S7cS6aS45UeU1cZ1f0A3A2S16SbS55A2A3"). Proof. vmr. Qed.
Lemma T_mifs_eq2 : ltac2:(tb__ "0|0|
SaSbSd0SeS1S4dS10S1A1A3S55A2S6bA3"). Proof. reflexivity. Qed.
Lemma mif_xff : ltac2:(tb__ "0|0|
SaSfS7eS55SeS1S4dS10S1A1A3A2S11A3"). Proof. vmr. Qed.
Lemma mif_land : ltac2:(tb__ "0|2|
SaSfS7dS6bS7bSa4S15S13S0S0A2M0S80SeG0S12S0S0S2cS1aZcS32A2A4S10G0A1A3A3Sb1Sd1S18U1S85A3M1G1S27Sd8A1A8S11A3"). Proof. vmr. Qed.
Lemma mif_bd : ltac2:(tb__ "0|0|
SaS14S18A1S19Sa4S26Sd8A1A2Sd1S18U1S85A3A3"). Proof. vmr. Qed.
Lemma mif_colive : ltac2:(tb__ "0|0|
SaSfS8fS2eS31S4ScS55A1A1A3S11A3"). Proof. vmr. Qed.
Lemma T_mig0_ta : ltac2:(tb__ "0|0|
SaSbSbbS1cS47S4aS52S1dS44S2cS34S33S31A2A2A6S6cA3"). Proof. vmr. Qed.
Lemma T_mig_ap : ltac2:(tb__ "0|0|
SaS17SbA1S7cS6cS45UeU1cZ1f0A3A2S16SbS56A2A3"). Proof. vmr. Qed.
Lemma T_migs_eq2 : ltac2:(tb__ "0|0|
SaSbSd0SeS1S4dS10S1A1A3S56A2S4eA3"). Proof. reflexivity. Qed.
Lemma mig_xff : ltac2:(tb__ "0|0|
SaSfS7eS56SeS1S4dS10S1A1A3A2S11A3"). Proof. vmr. Qed.
Lemma mig_ro0 : ltac2:(tb__ "0|1|
SaSfS81VXGL;S4eSdS4eA1S15S13S0S0A2M0S80SeG0S12S0S0S2P208A1S1aZcS2P209A1A2A4S10G0A1A3A3Z4Z5A6S11A3"). Proof. vmr. Qed.
Lemma mig_land : ltac2:(tb__ "0|1|
SaSfS7dSdcS4eSdS4eA1S1bZ4Z5A5S60Sa5S15S13S0S0A2M0S80SeG0S12S0S0S2P208A1S1aZcS2P209A1A2A4S10G0A1A3A3Sb2S15S18S99S85A3S92S27Sd3A1A8S11A3"). Proof. vmr. Qed.
Lemma mig_bd : ltac2:(tb__ "0|0|
SaS14S18A1S19Sa5S26Sd3A1A2S92A3"). Proof. vmr. Qed.
Lemma mig_colive : ltac2:(tb__ "0|0|
SaSfS8fS2eS31S4ScS56A1A1A3S11A3"). Proof. vmr. Qed.
Lemma mif_wp : bd_wpos brest_mi = true. Proof. vmr. Qed.

Lemma fv_robjs : ltac2:(tb__ "0|0|
SaS14S7A1S9ScS5eA1A1S15S7S74SeS7SddS1bZ4Z5Sa0S8A5S10S7A1A3A3A3"). Proof. vmr. Qed.
Lemma fv_rel : ltac2:(tb__ "0|2|
SaSfSadS5eS74Z4M0Z5Sa0S8SeS13SdeSdeA2M1S12SdeSdeZ20G0A4S10G1A1A3S27Sd3A1S26Sd3A1A9S11A3"). Proof. vmr. Qed.
Lemma E_fv1x_eq : ltac2:(tb__ "0|0|
SaS17SbA1S7cS77S39U10Z210A2A2S16SbS88A2A3"). Proof. vmr. Qed.
Lemma E_fv_eq2 : ltac2:(tb__ "0|0|
SaSbSd0S4cZ4S5Sd2S35S3Z1A1A3S61S2eA1A3S88A2S46A3"). Proof. vmr. Qed.
Lemma fv_xff : ltac2:(tb__ "0|0|
SaSfS7eS88S4cZ4S5Sd2S35S3Z1A1A3S61S2eA1A3A2S11A3"). Proof. vmr. Qed.
Lemma fv_needF : ltac2:(tb__ "0|0|
SaSfS8dZ4Z1Z8S35S40S4ScS88A1A1A6S11A3"). Proof. vmr. Qed.
Lemma fv_tvp : ltac2:(tb__ "0|1|
SaSfSdfS27Sd3A1S15S13S0S0A2M0S82SeG0S12S0S0S2bS1aZ4S30A2A4S10G0A1A3A3A2S11A3"). Proof. vmr. Qed.
Lemma fv_chk : ltac2:(tb__ "0|0|
SaSfS8eVXGL;S46S82S2bS30Z4Z210S26Sd3A1S84S49S51S44S2bS58A2AcS11A3"). Proof. vmr. Qed.
Lemma fv_iK : ltac2:(tb__ "0|1|
SaS14S13S0S0A2M0A1SbaS28S49S1cS1eS46A4S20A2SeG0S12S0S0S2bS1aZ4S30A2A4S10G0A1A3A3"). Proof. vmr. Qed.
Lemma fv_iF : ltac2:(tb__ "0|1|
SaS14S13S0S0A2M0A1SbaS28S49S1cS1fS46A4S20A2SeG0S12S0S0S2bS1aZ4S30A2A4S10G0A1A3A3"). Proof. vmr. Qed.
Lemma fv_iG : ltac2:(tb__ "0|1|
SaS14S13S0S0A2M0A1SbaS28S49S1cS1dS46A4S23A2SeG0S12S0S0S2P208A1S1aZ4S2P209A1A2A4S10G0A1A3A3"). Proof. vmr. Qed.
Lemma fv_bK : ltac2:(tb__ "0|0|
SaS14S18A1S19S28S49S1cS1eS46A4S26S22A1A2S9cA3"). Proof. vmr. Qed.
Lemma fv_bG : ltac2:(tb__ "0|0|
SaS14S18A1S19S28S49S1cS1dS46A4S21S25S24A2A2S98A3"). Proof. vmr. Qed.
Lemma T_fvk0_ta : ltac2:(tb__ "0|0|
SaSbSbbS1cS46S49S51S1eS44S2bS58A2A6S68A3"). Proof. vmr. Qed.
Lemma T_fvk_ap : ltac2:(tb__ "0|0|
SaS17SbA1S7cS68S45UfU1dZ210A3A2S16SbS54A2A3"). Proof. vmr. Qed.
Lemma T_fvks_eq2 : ltac2:(tb__ "0|0|
SaSbSd0SeS1S6S3SdbA1S2bA2S10S1A1A3S54A2S69A3"). Proof. reflexivity. Qed.
Lemma fvk_xff : ltac2:(tb__ "0|0|
SaSfS7eS54SeS1S6S3SdbA1S2bA2S10S1A1A3A2S11A3"). Proof. vmr. Qed.
Lemma fvk_land : ltac2:(tb__ "0|1|
SaSfS7dS69S5fSa3S15S13S0S0A2M0S82SeG0S12S0S0S2bS1aZ4S30A2A4S10G0A1A3A3Sb0S15S18S9cS84A3S91S27Sd4A1A8S11A3"). Proof. vmr. Qed.
Lemma fvk_bd : ltac2:(tb__ "0|0|
SaS14S18A1S19Sa3S26Sd4A1A2S91A3"). Proof. vmr. Qed.
Lemma fvk_live : ltac2:(tb__ "0|0|
SaSfS8cS35Z1S30S4ScS54A1A1A4S11A3"). Proof. vmr. Qed.
Lemma T_fvf0_ta : ltac2:(tb__ "0|0|
SaSbSbbS1cS46S49S51S1fS44S2bS58A2A6S65A3"). Proof. vmr. Qed.
Lemma T_fvf_ap : ltac2:(tb__ "0|0|
SaS17SbA1S7cS65S45UfU1dZ210A3A2S16SbS5cA2A3"). Proof. vmr. Qed.
Lemma fvf_ro0 : ltac2:(tb__ "0|2|
SaSfS81VXGL;S5cS72S75S2bS29S2aS33S3aS3cS3eS76S30S2dS2fS31S3bS3dS3fA10S15S13S0S0A2M0S82SeG0S12S0S0S2bS1aZ4M1S30A2A4S10G0A1A3A3G1Z5A6S11A3"). Proof. vmr. Qed.
Lemma fvf_land : ltac2:(tb__ "0|3|
SaSfS7dSdcS5cS72S75S2bS29S2aS33S3aS3cS3eS76S30S2dS2fS31S3bS3dS3fA10S1bZ4M0Z5A5S7aSa1S15S13S0S0A2M1S82SeG1S12S0S0S2bS1aG0S30A2A4S10G1A1A3A3SaeSd1S18U1S84A3M2G2S27Sd7A1A8S11A3"). Proof. vmr. Qed.
Lemma fvf_bd : ltac2:(tb__ "0|0|
SaS14S18A1S19Sa1S26Sd7A1A2Sd1S18U1S84A3A3"). Proof. vmr. Qed.
Lemma T_fvg0_ta : ltac2:(tb__ "0|0|
SaSbSbbS1cS46S49S51S1dS44S2bS58A2A6S67A3"). Proof. vmr. Qed.
Lemma T_fvg_ap : ltac2:(tb__ "0|0|
SaS17SbA1S7cS67S45UfU1dZ210A3A2S16SbS66A2A3"). Proof. vmr. Qed.
Lemma fvg_land : ltac2:(tb__ "0|1|
SaSfS7dS66S5fSa2S15S13S0S0A2M0S82SeG0S12S0S0S2P208A1S1aZ4S2P209A1A2A4S10G0A1A3A3SafS15S18S98S84A3S90S27Sd4A1A8S11A3"). Proof. vmr. Qed.
Lemma fvg_bd : ltac2:(tb__ "0|0|
SaS14S18A1S19Sa2S26Sd4A1A2S90A3"). Proof. vmr. Qed.
Lemma fvf_wp : bd_wpos brest_fv = true. Proof. vmr. Qed.

Lemma E_mm1x_eq : ltac2:(tb__ "0|0|
SaS17SbA1S7cS79S39U11Z230A2A2S16SbS8aA2A3"). Proof. vmr. Qed.
Lemma E_mm_eq2 : ltac2:(tb__ "0|0|
SaSbSd0S4cZ4S5Sd2S37S3Z1A1A3S63S2eA1A3S8aA2S48A3"). Proof. vmr. Qed.
Lemma mm_xff : ltac2:(tb__ "0|0|
SaSfS7eS8aS4cZ4S5Sd2S37S3Z1A1A3S63S2eA1A3A2S11A3"). Proof. vmr. Qed.
Lemma mm_needF : ltac2:(tb__ "0|0|
SaSfS8dZ4Z1Z8S37S42S4ScS8aA1A1A6S11A3"). Proof. vmr. Qed.
Lemma mm_tvp : ltac2:(tb__ "0|1|
SaSfSdfS27Sd4A1S15S13S0S0A2M0S83SeG0S12S0S0S29S1aZ4S2dA2A4S10G0A1A3A3A2S11A3"). Proof. vmr. Qed.
Lemma mm_chk : ltac2:(tb__ "0|0|
SaSfS8eVXGL;S48S83S29S2dZ4Z230S26Sd4A1S86S4bS53S44S29S59S5aS5bA2A2AcS11A3"). Proof. vmr. Qed.
Lemma mm_iK : ltac2:(tb__ "0|1|
SaS14S13S0S0A2M0A1SbaS28S4bS1cS1eS48A4S20A2SeG0S12S0S0S29S1aZ4S2dA2A4S10G0A1A3A3"). Proof. vmr. Qed.
Lemma mm_iF : ltac2:(tb__ "0|1|
SaS14S13S0S0A2M0A1SbaS28S4bS1cS1fS48A4S20A2SeG0S12S0S0S29S1aZ4S2dA2A4S10G0A1A3A3"). Proof. vmr. Qed.
Lemma mm_iG : ltac2:(tb__ "0|1|
SaS14S13S0S0A2M0A1SbaS28S4bS1cS1dS48A4S23A2SeG0S12S0S0S2P230A1S1aZ4S2P231A1A2A4S10G0A1A3A3"). Proof. vmr. Qed.
Lemma mm_bK : ltac2:(tb__ "0|0|
SaS14S18A1S19S28S4bS1cS1eS48A4S26S22A1A2S9eA3"). Proof. vmr. Qed.
Lemma mm_bG : ltac2:(tb__ "0|0|
SaS14S18A1S19S28S4bS1cS1dS48A4S21S25S24A2A2S9aA3"). Proof. vmr. Qed.
Lemma T_mmk0_ta : ltac2:(tb__ "0|0|
SaSbSbbS1cS48S4bS53S1eS44S29S59S5aS5bA2A2A6S71A3"). Proof. vmr. Qed.
Lemma T_mmk_ap : ltac2:(tb__ "0|0|
SaS17SbA1S7cS71S45U10U1eZ230A3A2S16SbS57A2A3"). Proof. vmr. Qed.
Lemma T_mmks_eq2 : ltac2:(tb__ "0|0|
SaSbSd0SeS1S6S3SdbA1S29A2S10S1A1A3S57A2Sc9A3"). Proof. reflexivity. Qed.
Lemma mmk_xff : ltac2:(tb__ "0|0|
SaSfS7eS57SeS1S6S3SdbA1S29A2S10S1A1A3A2S11A3"). Proof. vmr. Qed.
Lemma mmk_land : ltac2:(tb__ "0|1|
SaSfS7dSc9Sc7Sa9S15S13S0S0A2M0S83SeG0S12S0S0S29S1aZ4S2dA2A4S10G0A1A3A3Sb6S15S18S9eS86A3S95S27Sd5A1A8S11A3"). Proof. vmr. Qed.
Lemma mmk_bd : ltac2:(tb__ "0|0|
SaS14S18A1S19Sa9S26Sd5A1A2S95A3"). Proof. vmr. Qed.
Lemma mmk_live : ltac2:(tb__ "0|0|
SaSfS8cS37Z1S2dS4ScS57A1A1A4S11A3"). Proof. vmr. Qed.
Lemma T_mmf0_ta : ltac2:(tb__ "0|0|
SaSbSbbS1cS48S4bS53S1fS44S29S59S5aS5bA2A2A6S6eA3"). Proof. vmr. Qed.
Lemma T_mmf_ap : ltac2:(tb__ "0|0|
SaS17SbA1S7cS6eS45U10U1eZ230A3A2S16SbS5dA2A3"). Proof. vmr. Qed.
Lemma mmf_ro0 : ltac2:(tb__ "0|2|
SaSfS81VXGL;S5dSbeS29S2dA2S15S13S0S0A2M0S83SeG0S12S0S0S29S1aZ4M1S2dA2A4S10G0A1A3A3G1Z5A6S11A3"). Proof. vmr. Qed.
Lemma mmf_land : ltac2:(tb__ "0|3|
SaSfS7dSdcS5dSbeS29S2dA2S1bZ4M0Z5A5SceSa7S15S13S0S0A2M1S83SeG1S12S0S0S29S1aG0S2dA2A4S10G1A1A3A3Sb4Sd1S18U1S86A3M2G2S27Sd9A1A8S11A3"). Proof. vmr. Qed.
Lemma mmf_bd : ltac2:(tb__ "0|0|
SaS14S18A1S19Sa7S26Sd9A1A2Sd1S18U1S86A3A3"). Proof. vmr. Qed.
Lemma T_mmg0_ta : ltac2:(tb__ "0|0|
SaSbSbbS1cS48S4bS53S1dS44S29S59S5aS5bA2A2A6S70A3"). Proof. vmr. Qed.
Lemma T_mmg_ap : ltac2:(tb__ "0|0|
SaS17SbA1S7cS70S45U10U1eZ230A3A2S16SbS6fA2A3"). Proof. vmr. Qed.
Lemma mmg_land : ltac2:(tb__ "0|1|
SaSfS7dS6fSc7Sa8S15S13S0S0A2M0S83SeG0S12S0S0S2P230A1S1aZ4S2P231A1A2A4S10G0A1A3A3Sb5S15S18S9aS86A3S94S27Sd5A1A8S11A3"). Proof. vmr. Qed.
Lemma mmg_bd : ltac2:(tb__ "0|0|
SaS14S18A1S19Sa8S26Sd5A1A2S94A3"). Proof. vmr. Qed.
Lemma mmf_wp : bd_wpos brest_mm = true. Proof. vmr. Qed.

Lemma E_sg1x_eq : ltac2:(tb__ "0|0|
SaS17SbA1S7cScdS39U12Z250A2A2S16SbS8bA2A3"). Proof. vmr. Qed.
Lemma E_sg_eq2 : ltac2:(tb__ "0|0|
SaSbSd0S4cZ4S5Sd2S38S3Z1A1A3S64S2eA1A3S8bA2SbcA3"). Proof. vmr. Qed.
Lemma sg_xff : ltac2:(tb__ "0|0|
SaSfS7eS8bS4cZ4S5Sd2S38S3Z1A1A3S64S2eA1A3A2S11A3"). Proof. vmr. Qed.
Lemma sg_needF : ltac2:(tb__ "0|0|
SaSfS8dZ4Z1Z8S38S43S4ScS8bA1A1A6S11A3"). Proof. vmr. Qed.
Lemma sg_tvp : ltac2:(tb__ "0|1|
SaSfSdfS27Sd5A1S15S13S0S0A2M0S7fSeG0S12S0S0S2aS1aZ4S2fA2A4S10G0A1A3A3A2S11A3"). Proof. vmr. Qed.
Lemma sg_chk : ltac2:(tb__ "0|0|
SaSfS8eVXGL;SbcS7fS2aS2fZ4Z250S26Sd5A1S87SbdSc3S44S2aSbeSc5Sc6A2A2AcS11A3"). Proof. vmr. Qed.
Lemma sg_iK : ltac2:(tb__ "0|1|
SaS14S13S0S0A2M0A1SbaS28SbdS1cS1eSbcA4S20A2SeG0S12S0S0S2aS1aZ4S2fA2A4S10G0A1A3A3"). Proof. vmr. Qed.
Lemma sg_iF : ltac2:(tb__ "0|1|
SaS14S13S0S0A2M0A1SbaS28SbdS1cS1fSbcA4S20A2SeG0S12S0S0S2aS1aZ4S2fA2A4S10G0A1A3A3"). Proof. vmr. Qed.
Lemma sg_iG : ltac2:(tb__ "0|1|
SaS14S13S0S0A2M0A1SbaS28SbdS1cS1dSbcA4S23A2SeG0S12S0S0S2P290A1S1aZ4S2P291A1A2A4S10G0A1A3A3"). Proof. vmr. Qed.
Lemma sg_bK : ltac2:(tb__ "0|0|
SaS14S18A1S19S28SbdS1cS1eSbcA4S26S22A1A2S9fA3"). Proof. vmr. Qed.
Lemma sg_bG : ltac2:(tb__ "0|0|
SaS14S18A1S19S28SbdS1cS1dSbcA4S21S25S24A2A2S9bA3"). Proof. vmr. Qed.
Lemma T_sgk0_ta : ltac2:(tb__ "0|0|
SaSbSbbS1cSbcSbdSc3S1eS44S2aSbeSc5Sc6A2A2A6SccA3"). Proof. vmr. Qed.
Lemma T_sgk_ap : ltac2:(tb__ "0|0|
SaS17SbA1S7cSccS45U11U1fZ250A3A2S16SbSc4A2A3"). Proof. vmr. Qed.
Lemma T_sgks_eq2 : ltac2:(tb__ "0|0|
SaSbSd0SeS1S6S3SdbA1S2aA2S10S1A1A3Sc4A2Sc2A3"). Proof. reflexivity. Qed.
Lemma sgk_xff : ltac2:(tb__ "0|0|
SaSfS7eSc4SeS1S6S3SdbA1S2aA2S10S1A1A3A2S11A3"). Proof. vmr. Qed.
Lemma sgk_ro0 : ltac2:(tb__ "0|2|
SaSfS81VXGL;Sc2SbfSc2A1S15S13S0S0A2M0S7fSeG0S12S0S0S2aS1aZ4M1S2fA2A4S10G0A1A3A3G1Z5A6S11A3"). Proof. vmr. Qed.
Lemma sgk_land : ltac2:(tb__ "0|2|
SaSfS7dSdcSc2SbfSc2A1S1bZ4M0Z5A5Sc8SacS15S13S0S0A2M1S7fSeG1S12S0S0S2aS1aG0S2fA2A4S10G1A1A3A3Sb9S15S18S9fS87A3S97S27Sd6A1A8S11A3"). Proof. vmr. Qed.
Lemma sgk_bd : ltac2:(tb__ "0|0|
SaS14S18A1S19SacS26Sd6A1A2S97A3"). Proof. vmr. Qed.
Lemma sgk_live : ltac2:(tb__ "0|0|
SaSfS8cS38Z1S2fS4ScSc4A1A1A4S11A3"). Proof. vmr. Qed.
Lemma T_sgf0_ta : ltac2:(tb__ "0|0|
SaSbSbbS1cSbcSbdSc3S1fS44S2aSbeSc5Sc6A2A2A6ScaA3"). Proof. vmr. Qed.
Lemma T_sgf_ap : ltac2:(tb__ "0|0|
SaS17SbA1S7cScaS45U11U1fZ250A3A2S16SbSc0A2A3"). Proof. vmr. Qed.
Lemma sgf_ro0 : ltac2:(tb__ "0|2|
SaSfS81VXGL;Sc0SbfSc0A1S15S13S0S0A2M0S7fSeG0S12S0S0S2aS1aZ4M1S2fA2A4S10G0A1A3A3G1Z5A6S11A3"). Proof. vmr. Qed.
Lemma sgf_land : ltac2:(tb__ "0|3|
SaSfS7dSdcSc0SbfSc0A1S1bZ4M0Z5A5ScfSaaS15S13S0S0A2M1S7fSeG1S12S0S0S2aS1aG0S2fA2A4S10G1A1A3A3Sb7Sd1S18U1S87A3M2G2S27SdaA1A8S11A3"). Proof. vmr. Qed.
Lemma sgf_bd : ltac2:(tb__ "0|0|
SaS14S18A1S19SaaS26SdaA1A2Sd1S18U1S87A3A3"). Proof. vmr. Qed.
Lemma T_sgg0_ta : ltac2:(tb__ "0|0|
SaSbSbbS1cSbcSbdSc3S1dS44S2aSbeSc5Sc6A2A2A6ScbA3"). Proof. vmr. Qed.
Lemma T_sgg_ap : ltac2:(tb__ "0|0|
SaS17SbA1S7cScbS45U11U1fZ250A3A2S16SbSc1A2A3"). Proof. vmr. Qed.
Lemma sgg_ro0 : ltac2:(tb__ "0|2|
SaSfS81VXGL;Sc1SbfSc1A1S15S13S0S0A2M0S7fSeG0S12S0S0S2P290A1S1aZ4M1S2P291A1A2A4S10G0A1A3A3G1Z5A6S11A3"). Proof. vmr. Qed.
Lemma sgg_land : ltac2:(tb__ "0|2|
SaSfS7dSdcSc1SbfSc1A1S1bZ4M0Z5A5Sc8SabS15S13S0S0A2M1S7fSeG1S12S0S0S2P290A1S1aG0S2P291A1A2A4S10G1A1A3A3Sb8S15S18S9bS87A3S96S27Sd6A1A8S11A3"). Proof. vmr. Qed.
Lemma sgg_bd : ltac2:(tb__ "0|0|
SaS14S18A1S19SabS26Sd6A1A2S96A3"). Proof. vmr. Qed.
Lemma sgf_wp : bd_wpos brest_sg = true. Proof. vmr. Qed.
End G.
End Lib_handle_f_g3.

