(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Ox.F128_037.   (* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require et Lib_opt_push3 fd.

(* [comment removed for export] *)
Module Lib_handle_f_gdefs2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "andb"; "cons"; "nil"; "nat"; "None"; "app"; "pair"; "prod"; "Some"; "fst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "sprop"; "sprop_eqb"; "SPUle"; "cell"; "sv_eqb"; "DUnknown"; "mkObj"; "SAlu"; "mkCell"; "ss_facts"; "ss_objs"; "sv"; "SPBranch"; "ss_next"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXSplit"; "@Stdlib.Lists.List"; "existsb"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s6"; "s_pg"; "E_pg"; "R_pg"; "Xk_pg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs"; "kb"; "NPH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s5"; "pDts"; "pKrp"; "needA"; "pDrp"; "pKts"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_LTU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_defs"; "fr_hf"; "pA"; "am2"; "xfo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "ax_base"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "ANone"; "NDA"; "nd_bd"; "nd_below"; "nd_tv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s4"; "pKtr"; "pDtr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eg.Lib_builderH_pf"; "extraOH"; "extraXH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_defs.PG"; "Pre_pg"; "P_inv"; "P_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.et.Lib_handle_f_gdefs.PGC"; "nd0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.et.Lib_handle_f_gdefs"; "bF"; "fF"; "triAF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ew.Lib_handle_f_gdefs2"; "off_c4"; "off_g1"; "off_g2"; "off_g3"; "off_m4"; "pg0F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_nodes"; "ndTS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s6.AR"; "o4A"; "o16A"; "oNXTe"; "oPRV"; "oPRVe"; "oRFX"; "oRFXe"; "orfx"; "pNXT'"; "pPRV'"; "pRFX'"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve"; "B32"; "two47"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bitem"; "bd_below"; "bd_subst"; "bd_wpos"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS"; "xrs_checkL"; "flag_carve_stateA"; "robjs_checkF"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s2"; "co_live"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_handle_f_s8"; "XLJ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "wsub_dom_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "pd_okA"; "pdescA"; "xrs_inclb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "call_checkTA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAT"; "robjs_checkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "SHADOW_OFF"; "@Stdlib.PArith.BinPos.Pos"; "leb"].
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

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.ObjZeroA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require et.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.et.Lib_handle_f_gdefs.

Definition E_mdx : axst := Eval vm_compute in optAp (apply_axforms E_md1 xf_md).
Definition cells_md : list cell := Eval vm_compute in ob_cells (sh_last E_md0).
Definition cs_md : list cell := ltac2:(tb__ "0|2|
S1SeS13SaZ70A1Z8M0SaZ0A1M1A3S1SeS13SaZ48A1Z4G1A3S1SeS13SaZ40A1G0G1A3S2SeA1A3A3A3").

Definition cells_g1a : list cell := Eval vm_compute in ob_cells (sh_last E_g1_1).
Definition cells_g1b : list cell := Eval vm_compute in ob_cells (sh_last E_g1_2).
Definition off_g1 : sv := Eval vm_compute in off_of E_g1_3.
Definition xf_g1 : list axform := ltac2:(tb__ "0|0|
S1S1aS1bU1SaZe0A1A2S1S1aS1bU2SaZecA1A2S1S1aS1bU22S46A2S1S1aS1bU23S12S2aS46SaZcA1A3A2S2S1aA1A3A3A3A3").
Definition E_g1a : axst := Eval vm_compute in optAp (apply_axforms E_g1_3 xf_g1).
Definition E_g1b : axst := Eval vm_compute in reshapeA E_g1a 2 (mkObj (xfo 224) (SLit 0) (SLit 12) [] DUnknown).
Definition E_g1c : axst := Eval vm_compute in reshapeA E_g1b 35 (mkObj (SAlu ALU_ADD pDco off_g1) (SLit 0) (SLit 12) [] DUnknown).
Definition T_g1t : axst := Eval vm_compute in T_afterA Pre_mc E_g1 (s_g E_g1) R_g1 L_mc1.
Definition T_g1u : axst := Eval vm_compute in reshapeA T_g1t 1 (mkObj hF (SLit 224) (SLit 236) [] DUnknown).
Definition T_g1v : axst := Eval vm_compute in reshapeA T_g1u 2 (mkObj pDco off_g1 (SAlu ALU_ADD off_g1 (SLit 12)) [] DUnknown).

Definition off_g2 : sv := Eval vm_compute in off_of E_g2_0.
Definition xf_g2 : list axform := ltac2:(tb__ "0|0|
S1S1aS1bU1SaZecA1A2S1S1aS1bU2SaZf8A1A2S1S1aS1bU22S47A2S1S1aS1bU23S12S2aS47SaZcA1A3A2S2S1aA1A3A3A3A3").
Definition E_g2a : axst := Eval vm_compute in optAp (apply_axforms E_g2_0 xf_g2).
Definition E_g2b : axst := Eval vm_compute in reshapeA E_g2a 2 (mkObj (xfo 236) (SLit 0) (SLit 12) [] DUnknown).
Definition E_g2c : axst := Eval vm_compute in reshapeA E_g2b 35 (mkObj (SAlu ALU_ADD pDco off_g2) (SLit 0) (SLit 12) [] DUnknown).
Definition T_g2t : axst := Eval vm_compute in T_afterA Pre_mc E_g2 (s_g E_g2) R_g2 L_mc1.
Definition T_g2u : axst := Eval vm_compute in reshapeA T_g2t 1 (mkObj hF (SLit 236) (SLit 248) [] DUnknown).
Definition T_g2v : axst := Eval vm_compute in reshapeA T_g2u 2 (mkObj pDco off_g2 (SAlu ALU_ADD off_g2 (SLit 12)) [] DUnknown).

Definition off_g3 : sv := Eval vm_compute in off_of E_g3_0.
Definition xf_g3 : list axform := ltac2:(tb__ "0|0|
S1S1aS1bU1SaZf8A1A2S1S1aS1bU2SaZ104A1A2S1S1aS1bU22S48A2S1S1aS1bU23S12S2aS48SaZcA1A3A2S2S1aA1A3A3A3A3").
Definition E_g3a : axst := Eval vm_compute in optAp (apply_axforms E_g3_0 xf_g3).
Definition E_g3b : axst := Eval vm_compute in reshapeA E_g3a 2 (mkObj (xfo 248) (SLit 0) (SLit 12) [] DUnknown).
Definition E_g3c : axst := Eval vm_compute in reshapeA E_g3b 35 (mkObj (SAlu ALU_ADD pDco off_g3) (SLit 0) (SLit 12) [] DUnknown).
Definition T_g3t : axst := Eval vm_compute in T_afterA Pre_mc E_g3 (s_g E_g3) R_g3 L_mc1.
Definition T_g3u : axst := Eval vm_compute in reshapeA T_g3t 1 (mkObj hF (SLit 248) (SLit 260) [] DUnknown).
Definition T_g3v : axst := Eval vm_compute in reshapeA T_g3u 2 (mkObj pDco off_g3 (SAlu ALU_ADD off_g3 (SLit 12)) [] DUnknown).
Definition T_g3w : axst := Eval vm_compute in optAp (apply_axforms T_g3v [AXSelect sel_g; AXMerge 1; AXMerge 1; AXMerge 32; AXMerge 32]).

Definition off_c4 : sv := Eval vm_compute in offd_of E_c4_0.
Definition xf_c4 : list axform := ltac2:(tb__ "0|0|
S1S1aS1bU1SaZe0A1A2S1S1aS1bU2SaZ104A1A2S1S1aS1bU1eS45A2S1S1aS1bU1fS12S2aS45SaZ24A1A3A2S2S1aA1A3A3A3A3").
Definition E_c4a : axst := Eval vm_compute in optAp (apply_axforms E_c4_0 xf_c4).
Definition E_c4b : axst := Eval vm_compute in reshapeA E_c4a 2 (mkObj (xfo 224) (SLit 0) (SLit 36) [] DUnknown).
Definition E_c4c : axst := Eval vm_compute in reshapeA E_c4b 31 (mkObj (SAlu ALU_ADD pDm4 off_c4) (SLit 0) (SLit 36) [] DUnknown).
Definition T_c4t : axst := Eval vm_compute in T_afterA Pre_mc E_c4 s_c4 R_c4 L_mc1.
Definition T_c4u : axst := Eval vm_compute in reshapeA T_c4t 1 (mkObj pDm4 off_c4 (SAlu ALU_ADD off_c4 (SLit 36)) [] DUnknown).
Definition T_c4v : axst := Eval vm_compute in reshapeA T_c4u 2 (mkObj hF (SLit 224) (SLit 260) [] DUnknown).

Definition off_m4 : sv := Eval vm_compute in offd_of E_m4_0.
Definition xf_m4 : list axform := ltac2:(tb__ "0|0|
S1S1aS1bU1SaZ130A1A2S1S1aS1bU2SaZ134A1A2S1S1aS1bU1fS49A2S1S1aS1bU20S12S2aS49SaZ4A1A3A2S2S1aA1A3A3A3A3").
Definition E_m4a : axst := Eval vm_compute in optAp (apply_axforms E_m4_0 xf_m4).
Definition E_m4b : axst := Eval vm_compute in reshapeA E_m4a 2 (mkObj (xfo 304) (SLit 0) (SLit 4) [] DUnknown).
Definition E_m4c : axst := Eval vm_compute in reshapeA E_m4b 32 (mkObj (SAlu ALU_ADD pDf4 off_m4) (SLit 0) (SLit 4) [] DUnknown).
Definition T_m4t : axst := Eval vm_compute in T_afterA Pre_mc E_m4 s_m4 R_m4 L_mc1.
Definition T_m4u : axst := Eval vm_compute in reshapeA T_m4t 1 (mkObj pDf4 off_m4 (SAlu ALU_ADD off_m4 (SLit 4)) [] DUnknown).
Definition T_m4v : axst := Eval vm_compute in reshapeA T_m4u 2 (mkObj hF (SLit 304) (SLit 308) [] DUnknown).

Definition T_tdg2 : axst := Eval vm_compute in optAp (apply_axforms T_tdg0 [AXSelect sel_da; AXMerge 0]).
Definition T_wdg2 : axst := Eval vm_compute in optAp (apply_axforms T_wdg0 [AXSelect sel_wdg; AXMerge 0]).

Definition objs_XJ : list sobj := Eval vm_compute in removelast (ss_objs (ax_S XJ)).
Definition objs_J : list sobj := Eval vm_compute in removelast objs_XJ.
Definition XJ1 : axst := Eval vm_compute in shadow_release_stateA XJ objs_XJ 160 [].
Definition XLJf : axst := ltac2:(tb__ "0|0|
S65S1SbS62S2SbA1A3S63A2").
Definition XLJ1 : axst := Eval vm_compute in shadow_reopen_stateA XLJf (ax_X XLJf) hG 28 33.

Definition objs_E (A : axst) : list sobj := removelast (ss_objs (ax_S A)).
Definition objs_Ef42 : list sobj := Eval vm_compute in objs_E XEf42.
Definition objs_Eo42 : list sobj := Eval vm_compute in objs_E XEo42.
Definition objs_Ef6a : list sobj := Eval vm_compute in objs_E XEf6a.
Definition XEf6a1 : axst := Eval vm_compute in shadow_release_stateA XEf6a objs_Ef6a 160 [].
Definition objs_Ef6a1 : list sobj := Eval vm_compute in objs_E XEf6a1.
Definition objs_Ef6b : list sobj := Eval vm_compute in objs_E XEf6b.
Definition XEf6b1 : axst := Eval vm_compute in shadow_release_stateA XEf6b objs_Ef6b 160 [].
Definition objs_Ef6b1 : list sobj := Eval vm_compute in objs_E XEf6b1.
Definition objs_Eo6 : list sobj := Eval vm_compute in objs_E XEo6.
Definition XEo61 : axst := Eval vm_compute in shadow_release_stateA XEo6 objs_Eo6 160 [].
Definition objs_Eo61 : list sobj := Eval vm_compute in objs_E XEo61.

Definition E_f5o1 : axst := Eval vm_compute in shadow_reopen_stateA E_f5o0 (XR E_f5o0) hG 0 64.
Definition E_f5f1 : axst := Eval vm_compute in shadow_reopen_stateA E_f5f0 (XR E_f5f0) hG 0 64.
Definition T_f5o1 : axst := Eval vm_compute in optAp (apply_axforms T_f5o0 (xf_shback T_f5o0)).
Definition T_f5f1 : axst := Eval vm_compute in optAp (apply_axforms T_f5f0 (xf_shback T_f5f0)).
Definition objs_f5o1 : list sobj := Eval vm_compute in removelast (ss_objs (ax_S T_f5o1)).
Definition objs_f5f1 : list sobj := Eval vm_compute in removelast (ss_objs (ax_S T_f5f1)).
Definition sh_f5o1 : sobj := Eval vm_compute in sh_last T_f5o1.
Definition sh_f5f1 : sobj := Eval vm_compute in sh_last T_f5f1.
Definition X_rlo1 : axst := Eval vm_compute in optAp (apply_axforms X_rlo [AXSelect sel_rel]).
Definition X_rlf1 : axst := Eval vm_compute in optAp (apply_axforms X_rlf [AXSelect sel_rel]).

Definition liveLF (k : sv) (F : list sprop) : bool := ltac2:(tb__ "0|0|
S0S0S1cSbScSdS2dVk;A2A1VF;A3S1cSbScS17S2bSaZ2A1S2dA3A1VF;A3A2S1cSbScSdVk;SaS57A1A2A1VF;A3A2").

Definition carve_chk (XGL : list (Z * Z)) (A : axst) (objs : list sobj) (tv : list (sv * sv)) : bool := ltac2:(tb__ "0|2|
S0S0S0S0S0SfS33VA;A1SaS6dA1A2S19S31S5fVA;PaaA2A1A1A2S42S14S31VA;A1M0A1M1A1A2S43G1A1A2S60G1Vtv;S2cS4S3A1S3cVobjs;A6A2S5eVXGL;G1Vtv;S2cS8S3U0A2S15G0A1S3dS32VA;A1A8A2").

Definition cells_pg : list cell := Eval vm_compute in ob_cells (sh_last E_pg0).
Definition E_pg0r : axst := Eval vm_compute in shadow_release_stateA E_pg0 (objs_butlast E_pg0) 160 [(160, 24)].
Definition E_pg3a : axst := Eval vm_compute in reshapeA E_pg3 43 O_nxt'.
Definition E_pg3b : axst := Eval vm_compute in reshapeA E_pg3a 45 O_prv'.
Definition O_nxt : sobj := ltac2:(tb__ "0|0|
S11S25S4dS4eS2SeA1S10A5").
Definition O_prv : sobj := ltac2:(tb__ "0|0|
S11S25S4fS50S2SeA1S10A5").
Definition O_rfx : sobj := ltac2:(tb__ "0|0|
S11S25S51S52S2SeA1S10A5").
Definition O_nxt1 : sobj := ltac2:(tb__ "0|0|
S11S54SaZ0A1S4cS2SeA1S10A5").
Definition O_prv1 : sobj := ltac2:(tb__ "0|0|
S11S55SaZ0A1S4cS2SeA1S10A5").
Definition O_rfx1 : sobj := ltac2:(tb__ "0|0|
S11S56SaZ0A1S53S2SeA1S10A5").
Definition pgF (F : list sprop) : bool := ltac2:(tb__ "0|2|
S0S0S0S0S0S0S44VF;A1S1cSbScSdS25SaS58A1A2A1VF;A3A2S1cSbScSdS22Z3M0S2dA2S26A2A1VF;A3A2S1cSbScSdS26SaS57A1M1A2A1VF;A3A2S1cSbScSdS22G0S2eA2S3aA2A1VF;A3A2S1cSbScSdS3aG1A2A1VF;A3A2S1cSbScSdS27S29A2A1VF;A3A2").
Definition pg0F (F : list sprop) : bool := ltac2:(tb__ "0|2|
S0S0S0S0S0S43VF;A1S1cSbScSdSaS6cA1M0S28A2A1VF;A3A2S1cSbScSdG0S3bA2A1VF;A3A2S1cSbScSdG0S25A2A1VF;A3A2S1cSbScSdS22ZcS2dA2S22Z4M1S26A2A2A1VF;A3A2S1cSbScSdS22G1S22Z3S2eA2A2S22G1S3aA2A2A1VF;A3A2").

Definition pg_call_chk (XGL : list (Z * Z)) : bool := ltac2:(tb__ "0|9|
S0S0S0S0S0S0S0S0S0S0S0S0S0S0S0S0S0S0S0S69S21S32S1fA1A2S66S1fS3eS1eS20S61S7S30S34A2M0S30S9S30S34A2S1G0S6S30S34S3fS41A4S1G0S6S30S34S40S41A4S2G0A1A3A3M1A4A5A2S6aS23S1eA2A2S64S1eS59A2A2S6eS23S18S31S1fA1M2A1M3A2A2S38G3S36S5S7S16S16A2M4S39S4bA1M5S2G4A1A3S2cS5S5aS5cS1eS2S5aA1A2S37S4bA1M6A3S35A4A2A2S5bG3G6A2A2S5dG6A1A2S1dS68S67S3eS59S1eG3A4G1A3A2S42S14G2A1M7A1A2S6bG7G5S2cS4S3A1M8S3cS20A6A2S5eVXGL;G7G5S2cG8S15G2A1S3dS21A8A2SfS24S1ePcA2S2fZ30A1A2A2SfS24S1ePdA2S2fZa0A1A2A2SfS24S1ePeA2S2dA2A2SfS24S1ePfA2S28A2A2SfS24S1eP10A2S3bA2A2SfS24S1eP11A2S25A2A2SfS24S1eP12A2S27A2A2S4aG7A1A2").

Definition T_pgoa : axst := Eval vm_compute in reshapeA T_pgo0 8 O_nxt0.
Definition T_pgob : axst := Eval vm_compute in reshapeA T_pgoa 9 O_prv0.
Definition T_pgo2 : axst := Eval vm_compute in optAp (apply_axforms T_pgo1 xf_pgb1).
Definition T_pgo3 : axst := Eval vm_compute in pg_back1 T_pgo1.
Definition T_pgo4 : axst := Eval vm_compute in optAp (apply_axforms T_pgo3 xf_pgb2).
Definition T_pgoR1 : axst := Eval vm_compute in shadow_reopen_stateA T_pgo XT hG 6 15.
Definition T_pgia : axst := Eval vm_compute in reshapeA T_pgi0 8 O_nxt0.
Definition T_pgib : axst := Eval vm_compute in reshapeA T_pgia 9 O_prv0.
Definition T_pgic : axst := Eval vm_compute in pg_back0 T_pgi0.
Definition cs_pgi : list cell := ltac2:(tb__ "0|0|
S1SeS13SaZ8A1Z4SaZ0A1A3S2SeA1A3").
Definition T_pgi2 : axst := Eval vm_compute in optAp (apply_axforms T_pgi1 xf_pgb1).
Definition T_pgi3 : axst := Eval vm_compute in pg_back1 T_pgi1.
Definition T_pgi4 : axst := Eval vm_compute in optAp (apply_axforms T_pgi3 xf_pgb2).
Definition T_pgiR1 : axst := Eval vm_compute in shadow_reopen_stateA T_pgi XT hG 6 15.
End Lib_handle_f_gdefs2.

(* [comment removed for export] *)
Module Lib_handle_f_chk0.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs"; "NPH"; "@Corelib.Init.Datatypes"; "bool"; "true"; "app"; "nat"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_defs"; "FUEL_hf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_nodes"; "cutpcs_hfF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.et.Lib_handle_f_nodes2"; "cutsF2"; "exitsF2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.JcertCutA"; "cut_okE"; "etargets"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e5.Lib_handle_f_fastcert"; "eecheckJA'"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "edescA"; "eecheckJA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG SymSummary SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SummaryA EntailA CFGA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA TobjJA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.JcertCutA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs Lib_handle_f_defs Lib_handle_f_s1 Lib_handle_f_s2 Lib_handle_f_s3 Lib_handle_f_s4 Lib_handle_f_s5 Lib_handle_f_s6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_s9 Lib_handle_f_s9b.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require es.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require en.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_nodes.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ez.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require et.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_handle_f_s7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_handle_f_s8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s9b OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.es.Lib_handle_f_s10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.en.Lib_handle_f_epi OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_nodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ez.Lib_handle_f_s8w OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.et.Lib_handle_f_nodes2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e5.Lib_handle_f_fastcert.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import HFAddr.

Abbreviation TG := (etargets cutsF2 exitsF2).
Abbreviation PE := (eecheckJA NPH (cutsF2 ++ exitsF2)).
Abbreviation PE' := (eecheckJA' NPH (cutsF2 ++ exitsF2)).
Abbreviation CC i T := (cut_okE segs FUEL_hf cutpcs_hfF NPH PE i T TG).
Abbreviation CC' i T := (cut_okE segs FUEL_hf cutpcs_hfF NPH PE' i T TG).
Lemma CC_fast : ltac2:(tb__ "0|2|
S4SeS5S1SbS6S7S8S0SdS0S3SfS9SaA3M0A2R2R1ScS9SaA2M1A8S2A3S5S1SbS6S7S8S0S10S0G0A2R3R2G1A8S2A3F_;FT;Fi;").
Proof. intros i T H. rewrite (cut_okE_ext segs FUEL_hf cutpcs_hfF NPH PE PE' i T TG (fun e => eq_sym (eecheckJA'_eq NPH (cutsF2 ++ exitsF2) e))). exact H. Qed.
End Lib_handle_f_chk0.

(* [comment removed for export] *)
Module Lib_load_obj_certE.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "bool"; "true"; "pair"; "prod"; "nat"; "cons"; "nil"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "nd_am"; "nd_bd"; "nd_fr"; "nd_tv"; "am_eqb"; "am_subst"; "fr_sub_eqb"; "nd_below"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "ss_facts"; "ss_next"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs"; "NP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ew.Lib_load_obj_certE"; "ndE0d"; "s_l7"; "cutsE2g"; "cutsE3"; "exitsE2g"; "exitsE3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud"; "z0"; "ndX0"; "ndXE"; "RL"; "VLA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ez.Lib_load_obj_loopEf"; "ndE0f"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF"; "wsub_id_on"; "bud_le2"; "ejcertAF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_epiD1"; "s_dispA"; "s_dispX"; "La_errx"; "cps_epi"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.et.Lib_load_obj_epiD_eqs"; "nd_d0"; "V_ld"; "PhisD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop"; "X_latch7"; "cps_loop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_loopE"; "s_E"; "K_afterE2"; "X_errxE2"; "X_latchE2"; "K_loopE2"; "X_bodyE2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "tv_sub_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bd_subst"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue"; "V_B"; "V_L"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CFGA GlueA SummaryA SummaryA2 MemoFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV TobjArena ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAS TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require ObjEmptyA PinA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.ObjZeroA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ObjEmptyA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.PinA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs Lib_rom_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_rom_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_defs Lib_load_obj_pro.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ez.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eo.Lib_load_obj_pro2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_hv0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_exits OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_loopE OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ez.Lib_load_obj_loopEf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require et.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_epiD1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.et.Lib_load_obj_epiD_eqs.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr HVAddr.

Definition cutsE2g : list efnode := ltac2:(tb__ "0|5|
S7S5S5S5S16S9A2M0S6A2M1S5S12S13A2M2A2M3S4G1G2S4G0S6S4S16S9S36S25A4U0M4A4S4S12S13S23S24Z1aS20A2A4A4S7G3S4G1G2S4G0S6S4S16S9S37S25A4G4A4S4S12S13S23S24Z19S20A2A4A4S8G3A1A3A3").
Definition exitsE2g : list efnode := ltac2:(tb__ "0|5|
S7S5S5S5S16S9A2M0S6A2M1S5S12S13A2M2A2M3S4G1G2S4G0S6S4S16S9S33S25A4U0M4A4S4S12S13Z190S20A4A4S7G3S4G1G2S4G0S6S4S16S9S34S25A4G4A4S4S12S13Z18bS20A4A4S8G3A1A3A3").
Lemma ecertE2g_ok : ltac2:(tb__ "0|0|
S0S2S28S3bS19S2fU96S31S19S1cS1eA8S3A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Definition cutsE3 : list efnode := ltac2:(tb__ "0|4|
S7S5S5S5S16S9A2M0S6A2M1S5S12S13A2M2A2M3S4G1G2S4G0S6S4S16S9S33S25A4U0A4S4S12S13Z190S20A4A4S8G3A1A3").
Definition exitsE3 : list efnode := ltac2:(tb__ "0|4|
S7S5S5S5S16S9A2M0S6A2M1S5S12S13A2M2A2M3S4G1G2S4G0S6S4S16S9S2bS25A4U0A4S4S12S13Z18bS20A4A4S8G3A1A3").
Lemma ecertE3_ok : ltac2:(tb__ "0|0|
S0S2S28S3bS19S2fU12cS2cS19S1dS1fA8S3A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Definition ndE0d : ndesc := ndEp tvL bd_disp.
Definition s_l7 : wsub := ltac2:(tb__ "0|0|
S3eS19S17S30A1S17S35A1A3").

Lemma certE_checks_disp : ltac2:(tb__ "0|c|
S1S0S9S2dS1aA3S1S0S2S3aS19S15S17S2bA1M0A1M1A2S3A3S1S0S2S11G1S1aA2S3A3S1S0S2S38S29SdS1aA1M2SdS2dA1M3A3S3A3S1S0S2S10S29ScS1aA1M4ScS2dA1M5A3S3A3S1S0S2S27S14G0A1S39S29SbS2dA1M6A2SbS1aA1M7A3S3A3S1S0S2SeSfS29SaS2dA1M8A2SaS1aA1M9A2S3A3S1S0S2S26S2eS29A2S3A3S1S0S2S3aS19S15S17S34A1MaA1MbA2S3A3S1S0S2S11GbS1aA2S3A3S1S0S2S38S2aG2G3A3S3A3S1S0S2S10S2aG4G5A3S3A3S1S0S2S27S14GaA1S39S2aG6A2G7A3S3A3S1S0S2SeSfS2aG8A2G9A2S3A3S0S2S26S2eS2aA2S3A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Lemma certE_checks_l7 : ltac2:(tb__ "0|2|
S1S0S2S18S30S35S1bA3S3A3S1S0S2S3fS1bS19A2S3A3S1S0S2S3aS19S15S17S30A1M0A1M1A2S3A3S1S0S2S11G1S21A2S3A3S1S0S2S38S1bSdS21A1SdS22A1A3S3A3S1S0S2S10S1bScS21A1ScS22A1A3S3A3S1S0S2S27S14G0A1S39S1bSbS22A1A2SbS21A1A3S3A3S1S0S2SeSfS1bSaS22A1A2SaS21A1A2S3A3S0S2S26S3cS1bA2S3A3A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Lemma certE_checks_sE : ltac2:(tb__ "0|0|
S1S0S2S26S3cS32A2S3A3S1S0S2S26S2eS32A2S3A3S0S2S26S3dS32A2S3A3A2A2").
Proof. conj_vmc. Qed.
End Lib_load_obj_certE.

(* [comment removed for export] *)
Module Lib_load_obj_epiD_chk.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "bool"; "true"; "nil"; "cons"; "prod"; "false"; "list"; "app"; "andb"; "pair"; "Some"; "nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "sprop_eqb"; "SLit"; "SPUle"; "SVar"; "sobj"; "ss_objs"; "swf"; "SAlu"; "SPBranch"; "SPEq"; "SPNot"; "dflt_writable"; "ob_cells"; "ob_dflt"; "ss_facts"; "ss_next"; "sv_below"; "sv_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue"; "frL"; "extraLO"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "ax_base"; "has_facts"; "entailsA"; "g8"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ew.Lib_load_obj_epiD_chk"; "Fx"; "nx"; "ent_chk"; "g5_facts"; "Te_sf0"; "shape_ok"; "she"; "two52"; "ndA1p"; "nd_d1n"; "@Stdlib.Lists.List"; "existsb"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs"; "NP"; "g5"; "objs_butlast"; "L_ms"; "Pre_ms"; "vF"; "L_f8"; "Pre_f8"; "vFL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.et.Lib_load_obj_epiD_eqs"; "tvA"; "KU1"; "nd_e"; "nd_fa"; "nd_d1"; "nd_d2"; "gp"; "nd_CL"; "V_ld"; "nd_A2"; "nd_B2"; "ndT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "nd_below"; "nd_am"; "nd_bd"; "nd_fr"; "nd_tv"; "ndesc"; "AHeadN"; "NDA"; "am_eqb"; "am_subst"; "fr_sub_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f9.Lib_load_obj_epiD3"; "Ee_sfA"; "Ee_sf"; "Ee_sfD"; "Te_s81"; "Te_s82"; "Ee_s8"; "Ee_sfB"; "Re_sf"; "Ee_s8a"; "L_sf"; "Pre_sf"; "Re_s8"; "Te_s8r"; "Te_sf"; "X_sx"; "s_s8"; "s_sf"; "sx_sfB"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_hvkit"; "robjs_chkR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bitem"; "KU"; "bud_pay"; "BIc"; "bd_below"; "bd_subst"; "bud_le"; "bd_wpos"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit2"; "robjs_chkC"; "xextraLO"; "xrs_chkC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_epiD1"; "E_fl"; "kept_bd"; "E_flF"; "E_flG"; "L_fr"; "Pre_fr"; "dropX"; "E_bd"; "E_flC"; "K_j1"; "R_fl"; "L_fl0"; "L_fl1"; "L_j1s"; "Lb_j1"; "R_bd"; "T_fl0"; "Xk_bd"; "bd_disp"; "brest_bd"; "dnz"; "fact_sz"; "s_fl"; "s_j1b"; "s_j1s"; "szL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f7.Lib_load_obj_epiD2"; "E_fa"; "E_fd"; "E_s80"; "vG"; "E_ms0"; "X_A1"; "X_B"; "C_L"; "K_fa"; "L_L3"; "R_fa"; "R_fd"; "R_ms"; "s_L3"; "s_ms"; "vNd"; "vNx"; "E_fa0"; "E_fd1"; "L_L1"; "T_fa0"; "T_fd0"; "T_ms0"; "X_A"; "X_fa0"; "X_fa1"; "gA"; "nB"; "s_L1"; "s_fa"; "s_fa0"; "s_fa1"; "s_fd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop"; "xLD"; "xLK"; "pH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "T_afterA"; "call_checkTA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF"; "xrs47_chk"; "V_below"; "carve_site_chk"; "wsub_id_on"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs"; "kb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro"; "vARn"; "ax_tidy"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub_id_below"; "sv_subst"; "wsub";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "remove_nth"; "tv_sub_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR"; "e32"; "carve_stateA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS"; "flag_carve_stateA"; "shadow_release_stateA"; "shadow_reopen_stateA"; "shobj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "SHADOW_OFF"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_EQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "new_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "xs_framed"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "T_afterA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAT"; "robjs_checkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "V_FL"; "@Stdlib.ZArith.BinInt.Z"; "pow"; "sub"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG SymSummary SymObj SymFrame.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA SummaryA2 MemoFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv ObjXform ObjUnbase TobjJV.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAS TobjJAT TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAD.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require ObjEmptyA PinA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.TobjJAH OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.ObjZeroA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ObjEmptyA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.PinA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_defs Lib_load_obj_pro.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ez.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eo.Lib_load_obj_pro2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_hv0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_exits OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_loopE OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_avn OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_hvkit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ez.Lib_load_obj_hvpk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builder_dispose.
Import ListNotations. Close Scope bv_scope. Open Scope Z_scope. Import ScanDoubleAddr LOAddr LOLAddr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require et.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_epiD1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f7.Lib_load_obj_epiD2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f9.Lib_load_obj_epiD3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.et.Lib_load_obj_epiD_eqs.

Definition Fx (A : axst) : list sprop := ss_facts (ax_S A).
Definition nx (A : axst) : positive := ss_next (ax_S A).

Definition ent_chk (L T : axst) (s : wsub) (ndi ndj : ndesc) : bool := ltac2:(tb__ "0|2|
S2S2L_;M0S29VL;VT;Vs;A3G0Sc1Vs;S37A2G0S69S37S2cVL;A1M1A2G0S4cG1Vndi;A2G0Sc5Vs;S50Vndi;A1S50Vndj;A1A3G0S56Vs;S4fVndi;A1S4fVndj;A1A3G0S72S2bVL;A1S71Vs;S4eVndj;A1A2S4eVndi;A1A3S54S55Vs;S4dVndj;A1A2S4dVndi;A1A2S7X2x2S7X2x2S7X2x2S7X2x2S7X2x2S7X2x2S7X2x2").
Lemma ent_chk_unf : ltac2:(tb__ "0|2|
S24S24Sc3S51S51S0S2S2dR5R4R3R2R1A5S3A3S1S0S2S29R6R5R4A3S3A3S1S0S2Sc1R4S37A2S3A3S1S0S2S69S37S1fS25R6A1M0A1M1A2S3A3S1S0S2S4cG1R3A2S3A3S1S0S2Sc5R4S50R3A1S50R2A1A3S3A3S1S0S2S56R4S4fR3A1S4fR2A1A3S3A3S1S0S2S72S1eG0A1S71R4S4eR2A1A2S4eR3A1A3S3A3S0S2S54S55R4S4dR2A1A2S4dR3A1A2S3A3A2A2A2A2A2A2A2F_;Fndj;Fndi;Fs;FT;FL;").
Proof.
  intros L T s ndi ndj H. unfold ent_chk in H.
  apply lazy_andb_prop in H as [H1 H]. apply lazy_andb_prop in H as [H2 H]. apply lazy_andb_prop in H as [H3 H]. apply lazy_andb_prop in H as [H4 H].
  apply lazy_andb_prop in H as [H5 H]. apply lazy_andb_prop in H as [H6 H]. apply lazy_andb_prop in H as [H7 H8]. repeat split; assumption.
Qed.

Definition nd_d1n : ndesc := ndEp tvA brest_bd.

Lemma epiD_chk_bd : ltac2:(tb__ "0|4|
S1S0S2S74S2bS7eA1M0S78S22S23S86A5S3A3S1S0S2S76G0S78S22S75S88A5S3A3S1S0S2S73S89A1S3A3S1S0S2S35SfS10S12SbdZ10Sb3A2M1S11ZffffffffA1M2A2A1G0A3S3A3S1S0S2S35SfS10S12Sb3G2A2A1G0A3S3A3S1S0S2S35SfS10S12Sb2S11Z800000000000A1A2A1G0A3S3A3S1S0S2S35SfS10S12S17ScdSb2G1A3S13P1eA1M3A2A1G0A3S3A3S1S0S2S35SfS10S12S3cS11Z7fffff7ff800A1A2A1G0A3S3A3S1S0S2S35SfS10S12G3S11Z7fffff800000A1A2A1G0A3S3A3S0S2Sb8S2cS7eA1S48A2S3A3A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Lemma epiD_chk_fl : ltac2:(tb__ "0|6|
S1S0S2S2dS82S7aS4S6SbcSeA2A1M0S44S44A5S3A3S1S0S2S2dS83S7aG0S44S44A5S3A3S1S0S2SbaS48G0A2S3A3S1S0S2S35SfS10S12SbdZ10Sb3A2S11ZffffffffA1M1A2A1S2bS7aA1M2A3S3A3S1S0S2S35SfS10S12Sb3G1A2A1G2A3S3A3S1S0S2Sb9S79S78S22U0M3S23A5S3A3S1S0S24Sc7S79Sb2S90A3S7fA3S1S0S24S7dSb2S7fA2S77A3S1S0S2S35SfS10S8cA1S2bS79A1A3S3A3S1S0S2S74S2bS77A1M4S40S22S23S81A5S3A3S1S0S2S76G4S40S22S75S26S77A1A5S3A3S1S0S2S35SfS10S8bA1G4A3S3A3S1S0S2S6eG4S11Z0A1S6dS8aS41A5S3A3S1S0S2S70S2cS77A1S41A2S3A3S1S0S24Sb5S7cS77S8dS81S7bA5S87A3S0S8S6SeSeA2M5A1Sc4G5G3S78A3S40A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Lemma epiD_chk_j1 : ltac2:(tb__ "0|1|
S1S0S2S2dS84S80S8fS34S45A5S3A3S1S0S2S2dS85S80S8eS45S45A5S3A3S0S8S6SeSeA2M0A1Sc4G0U0S78A3S40A3A2A2").
Proof. conj_vmc. Qed.

Definition ndA1p : ndesc := ltac2:(tb__ "0|0|
S53S40S22S41S52Sb4SabA2A4").
Definition two52 : Z := TobjJAD.two52.
Lemma epiD_chk_loop : ltac2:(tb__ "0|e|
S1S0S2S2dSa9S99SafS43S43A5S3A3S1S0S2S2dSaaS99Sb0S43S43A5S3A3S1S0S2S2dSa4S98SadS49S47A5S3A3S1S0S2S2dS9aS98S9eS4aS47A5S3A3S1S0S2S69S37S2cSa8A1M0A2S3A3S1S0S2S4cG0S45A2S3A3S1S0S2S69S37S2cS96A1M1A2S3A3S1S0S2S4cG1S33A2S3A3S1S0S2S6bS2bS96A1M2S40S22S23S15S25S96A1A1A5S3A3S1S0S2Sb7G2S40S26S96A1A3S3A3S1S0S51S53S5S6SeSeA2M3SbSeSeSb4Sc6S13S6aG1P1M4A2A1A1A4S40A3S22S9S6cS41S5S6cS6fZ0Z1S6dA3S4S6cA1A3A3M5S52S13G1A1S13S6aG1P3M6A2A1A2A4S49A3S1S0S2S69S37S2cS97A1M7A2S3A3S1S0S2S4cG7S4bSa1S94A2A2S3A3S1S0S2S6bS2bS97A1M8S40S22S23S15S25S97A1A1A5S3A3S1S0S2Sb7G8S40S26S97A1A3S3A3S1S0S51S53S5G3SbSeSeSa1Sc6S13S6aG7G4A2A1A1A4S40A3S22G5S52S13G7A1S13S6aG7G6A2M9A1A2A4S4aA3S1S0SbcG9S6aSacG6A2MaA3S1S0S2S35SfS10S12S94S11S32A1MbA2A1G8A3S3A3S1S0S2S35SfS10S12S13GaA1McGbA2A1S2bS9aA1A3S3A3S0SeSc2S9eS46S94Z8MdA2A2S46GcGdA2A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Lemma epiD_chk_fd : ltac2:(tb__ "0|4|
S1S0S24S7dSa0Sa3A2S92A3S1S0S2S74S2bS92A1M0S40S22S23S9cA5S3A3S1S0S2S76G0S40S22S75S26S92A1A5S3A3S1S0S2S35SfS10S1aS18SceSa0S11Z0M1A1M2A3A1A1G0A3S3A3S1S0S2S6eG0G2S6dS9S6cS41S5S6cS6fG1Z1S6dA3S4S6cA1A3A3S41A5S3A3S1S0S2S70S2cS92A1M3S41A2S3A3S1S0S2S4cG3S47A2S3A3S1S0S24Sb5S7cS92Sb1S9cS7bA5Sa6A3S1S0S2S35SfS10S12S94S11S32A1A2A1G0A3S3A3S0S2S20G3S46S94Z6A2A2S3A3A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Definition shape_ok (Pre : axst) (Ls : list axst) : bool := ltac2:(tb__ "0|1|
S36S24S24SaSaS8S14A1M0S2Lx;ScfS25VPre;A1S25R1A1A2S3S14G0S7Ll;Ls;X8x2Sd0VPre;R1A2A2S21S27R1A1S27VPre;A1A2A2LL;VLs;A3").
Definition g5_facts : list sprop := ltac2:(tb__ "0|0|
S5SfS19S2aS38A1S13P6eA1A2S5SfS12S13S38A1S11Sd5Sd4Z2Z3dA2Z1A2A1A2S4SfA1A3A3").
Lemma epiD_chk_fa : ltac2:(tb__ "0|2|
S1S0S24S7dSbeSa2A2S91A3S1S0S2S74S2bS91A1M0S4S6SeSeA2A1M1S22S23S9bA5S3A3S1S0S2S76G0G1S22S75S26S91A1A5S3A3S1S0S2S35SfS10S12S11Z1000A1SbeA2A1G0A3S3A3S1S0S2S6eG0S11Z0A1S6dS41S4S6cA1A5S3A3S1S0S2S4cS2cS91A1S43A2S3A3S0S24Sb5S7cS91SaeS9bS7bA5Sa5A3A2A2A2A2A2A2").
Proof. conj_vmc. Qed.
Lemma epiD_chk_ms : ltac2:(tb__ "0|3|
S1S0S2Sb6S37S9fA2S3A3S1S0S2S69S37S2cS95A1M0A2S3A3S1S0S2S4cG0S42A2S3A3S1S0S2S30S3bS5S24S3aS4S24A1A3A2S3A3S1S0S2S74S2bS95A1M1S4S6SeSeA2A1M2S22S23S9dA5S3A3S1S0S2S76G1G2S22S75S26S95A1A5S3A3S0S24Sb5S3bS95S9fS9dS3aA5Sa7A3A2A2A2A2A2A2").
Proof. conj_vmc. Qed.
Lemma epiD_chk_s8 : ltac2:(tb__ "0|7|
S1S0SeS27S93A1S11SccA1M0A3S1S0S2S28S2eS2bS93A1M1A2S3A3S1S0S2S6bG1S4S6SeSeA2A1M2S22S23S15S25S93A1A1A5S3A3S1S0S2Sb6S37S66S5cA1A2S3A3S1S0S2S69S37S2cS5cA1M3A2S3A3S1S0S2S4cG3S42A2S3A3S1S0S2S30S3eS5S24S3dS4S24A1A3A2S3A3S1S0S2S74S2bS5cA1M4G2S22S23S62A5S3A3S1S0S2S76G4G2S22S75S26S5cA1A5S3A3S1S0SeS27S5aA1G0A3S1S0S2S28S2eS2bS5aA1M5A2S3A3S1S0S2S4cS2cS5aA1S42A2S3A3S1S0S2S6bG5G2S22S23S39S5aA1A5S3A3S1S0SeS27S5bA1G0A3S1S0S2S28S2eS2bS5bA1M6A2S3A3S0S2S6bG6G2S22S23S15S25S5bA1A1A5S3A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.
Definition she : sobj := Eval vm_compute in last (ss_objs (ax_S Ee_sfA)) dflt_obj.
Definition Te_sf0 : axst := Eval vm_compute in T_afterA3 Pre_sf Ee_sf (s_sf Ee_sf) Re_sf L_sf (ax_X Ee_sf).
Lemma epiD_chk_sf : ltac2:(tb__ "0|8|
S1S0SeS27S57A1S11SccA1M0A3S1S0S8S14A1S15S25S57A1A1S9S14S39S57A1M1S5S14ScbS38Z20Z40S1cS31A1S1dS31A1M2A5S4S14A1A3A3A3S1S0S2S1bG2A1S3A3S1S0S2S28S2eS2bS57A1M3A2S3A3S1S0S2S4cS2cS57A1S42A2S3A3S1S0S2S6bG3S4S6SeSeA2A1M4S22S23G1A5S3A3S1S0S24S68S57A1S5dA3S1S0SeS27S59A1G0A3S1S0S24Sc8S59P78A2S58A3S1S0S2S16S25S58A1A1S3A3S1S0S2S6bS2bS59A1M5G4S22S23S15S25S59A1A1A5S3A3S1S0S2Sb7G5G4S26S59A1A3S3A3S1S0S2Sb6S37S67S58A1M6A2S3A3S1S0S2S69S37S2cS58A1M7A2S3A3S1S0S2S4cG7S42A2S3A3S1S0SeSc0G6PcA2S3cA3S1S0SeSc0G6Sd3A2S3fA3S1S0S2Sd2S2bS58A1G4S22ScSdU0A2S23S5eA6S3A3S1S0S24Sd1S61S58G6S5eS60S26S58A1A6S2fA3S0S24SbfS2fA1S64A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Lemma epiD_chk_sx : ltac2:(tb__ "0|4|
S1S0S24ScaS93S65S93A1S38Z44Ze7A5M0S5fA3S1S0S2S16S25G0A1A1S3A3S1S0S24Sc9S5aS39S5aA1P6eM1S4S6SbbSbbA2A1M2A4S5bA3S1S0S24ScaS5bS26S5bA1S38Z20Z40A5M3S63A3S1S0S2S16S25G3A1A1S3A3S1S0S24Sc9S57S39S57A1G1G2A4S5dA3S0S2S16S25Sc8S59P78A2A1A1S3A3A2A2A2A2A2A2").
Proof. conj_vmc. Qed.
End Lib_load_obj_epiD_chk.

(* [comment removed for export] *)
Module Lib_load_obj_hv_pf4.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@Corelib.Init.Datatypes"; "prod"; "pair"; "list"; "nat"; "true"; "bool"; "cons"; "nil"; "app"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_base"; "g8"; "has_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "valuation"; "rw"; "ss_facts"; "sobj"; "sprop"; "DUnknown"; "SLit"; "SPEq"; "SPUle"; "SVar"; "holds"; "ob_cells"; "ss_next"; "ss_objs"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "PTrue"; "NDA"; "AHead"; "JA_pre"; "JA"; "nd_below"; "ok_frameKA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue"; "tblB"; "frL"; "V_B"; "P0_lo"; "tvL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "etriple"; "triple"; "world"; "@Stdlib.Lists.List"; "In"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF"; "efmeasA"; "phiK"; "JAF"; "V_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eb.Lib_vec_reserve_pf"; "P0_vr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "pow"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs"; "kb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud"; "ndA1"; "ndXE"; "VLA"; "z0"; "RL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs"; "g5"; "NP"; "vF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_hv3"; "nd_keep"; "PDk_vr"; "h0"; "tv_keep"; "T_failr"; "objs_nl"; "sh_of"; "tv_fail"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f7.Lib_load_obj_hv3m"; "E_o1"; "L_mc1"; "Pre_mc"; "E_mk0"; "T_mkb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_hvj"; "K_vr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop"; "pH"; "xLD"; "xLK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_loopE"; "X_latchE2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_hv"; "X_hv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_hv3.VR"; "Pre_vr"; "nd0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fa.Lib_load_obj_hv3e"; "cutsH3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_hvkit"; "PhisH"; "mH"; "extra_hv"; "robjs_chkR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ez.Lib_load_obj_hvpk"; "xrs_chkRo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_sub"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "BXok_d"; "bitem"; "bxt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.TobjJAH"; "ndh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK"; "PostsCk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "SHADOW_OFF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "AE_A"; "JL_pure"; "J_memcpy_pre"; "alloc_contractsA"; "alloc_contractsA_ex"; "alloc_lawsA";
"@Stdlib.PArith.BinPos.Pos"; "lt"; "@Corelib.Lists.ListDef"; "Forall"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_fuzz_iface"; "in_lits"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit2"; "lines_chk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.et.Lib_load_obj_hv3f"; "lx_chk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.es.Lib_load_obj_hv_pf1"; "loopF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ew.Lib_load_obj_hv_pf4.Sum.X"; "rel_chkG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS"; "local_ok"; "shadow_release_stateA"; "shobj"].
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
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eo.Lib_load_obj_pro2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_hv0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_hv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_hvj OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_hvkit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ez.Lib_load_obj_hvpk OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f4.Lib_load_obj_hv2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.es.Lib_load_obj_hv_pf1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_hv3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f7.Lib_load_obj_hv3m OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fa.Lib_load_obj_hv3e OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_loopE OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.et.Lib_load_obj_hv3f OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fa.Lib_load_obj_hv_pf3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ScanDoubleAddr DiagAppendAddr LOAddr LOLAddr HVAddr.

Ltac inl := cbn [In]; repeat (first [left; reflexivity | right]).
Lemma lines_in_tv_keep : ltac2:(tb__ "0|0|
S36S1S11S11A2S2S11S11S5cS44Z10S5dA2A4S50A3").
Proof. cbn. repeat (first [left; reflexivity | right]). Qed.
Lemma VB_meas4 : ltac2:(tb__ "0|0|
SbS2bS6S3bR1S2fA2S5A3S2cS79P1ccR2A2S79P1d3R2A2A2F_;Fn;").
Proof.
  intros n H. split; [apply Pos.ltb_lt; apply (proj1 (forallb_forall _ _) H); cbn; tauto | apply Pos.ltb_lt; apply (proj1 (forallb_forall _ _) H); cbn; tauto].
Qed.
Lemma VB_460 : In 460%positive V_B /\ In 467%positive V_B. Proof. split; cbn; tauto. Qed.

Lemma efmeasA_VLA_agree : ltac2:(tb__ "0|7|
ScScS21S21S4S4SaSaS12S12S2bS20Q40A1M0S13R1P1ccM1A2S13R2G1A2A3S2bG0S13R2P1d3M2A2S13R3G2A2A3S2bSaS38S2S1S1ScS21A2M3S4A2M4S1SaS11A2M5S2G3S4S2ScS21RcRaA4R8A4S2SaS11R6S47R5S48A2A4M6A4R3A2S38S2G4G5S2G3S4S2ScS21RbR9A4R7A4G6A4R4A2A3F_;F_;Frho';Frho;Fph;Fr;Fk';Fk;Fnd';Fnd;FX';FX;").
Proof.
  intros X X' nd nd' k k' r ph rho rho' H460 H467. unfold efmeasA. cbn [ef_rank ef_var fst snd]. f_equal. f_equal.
  unfold VLA, z0, xLC, pI. cbn [eval]. rewrite H460, H467. reflexivity.
Qed.
Lemma hv3_facts_loop : ltac2:(tb__ "0|0|
S7fS14SdS58A1A1A1").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
S5fS12S3S20Q40A1A1S7bOF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
S78S0VAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
SaS60VCST;R1A2S2cS40Z0R2A2S41R2S71A2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
SaS60VXGL;R1A2S2cS40Z0R2A2S41R2S71A2A2F_;Fa;").
Hypothesis HXlits : ltac2:(tb__ "0|0|
SaS7cR1A1S60VXGL;R2A2F_;Fa;").
Hypothesis LFLAG : law_flag_stmt AInv.
Hypothesis LFSH : law_fshadow_stmt AInv.
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S3S1S1SaSaA2SaA2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 7 BX.
Variable rho0 : valuation.
Let HNP : NP_okA NP := NP_okA_intro NP eq_refl.
Let HTOP : InitState.segs_top segs <= IMG_HI := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eb.Lib_arena_alloc.HTOP_ok.
Let P0 : ltac2:(tb__ "0|0|
S12OFr;") := ltac2:(tb__ "0|0|
S30VCST;VFB;VFF;A3").
Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S26VAInv;VCST;VXGL;S4bVKc;Vrho0;VP0;VFB;VFF;VBX;S22Vnd;Ac").
Let JAFv (Phi : valuation -> Prop) (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S3aVAInv;VCST;VXGL;S4bVKc;Vrho0;VP0;VFB;VFF;VBX;S22VPhi;Vnd;Ad").

Lemma CXR_mk : ltac2:(tb__ "0|0|
S2bS6S69VXGL;S14SdS59A1A1S50Z4Z1eS61A6S5A3"). Proof using . OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma CXR_fail : ltac2:(tb__ "0|0|
S2bS6S69VXGL;S14SdS51A1A1S54Z4Z1eS61A6S5A3"). Proof using . OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Section X.
Variable TR : assn -> assn -> Prop.
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S2aScS12S3S20Q40A1A1S32S7aS16S1cR3A1S14SdR4A1A1A3VTR;S29S0R6R5R4R3A5R2A2M0F_;G0F_;FQ;Ftp;Frho;FS;FJ;").
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S32S32S32S35R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_exw : forall (T : Type) (P : T -> assn) (Q : assn), (forall a, TR (P a) Q) -> TR (fun w => exists a, P a w) Q.
Hypothesis TR_pureP : ltac2:(tb__ "0|1|
S32OS32S35R4R1A1R4F_;Fw;R3VTR;R5R3A2M0F_;G0F_;F_;FQ;FX;FP;").

Definition rel_chkG (tv : list (sv * sv)) (bd : list bitem) (L : list (Z * Z)) (E0 Er : axst) : Prop := ltac2:(tb__ "0|6|
S2cS2bS3S15A1S1fSdVE0;A1M0A1S9S15S52VE0;A1M1S7S15S83S4aZ4M2Z1eM3S1dS53VE0;A1A1M4S17A5S8S15A1A3A3A3S2cS2bS11SeVE0;A1S18S72A1A3S2cS2bS6S10S7S16S19SfS4aA1S4cA2S7S16S1aS1bS4aA1S18S43S42Z2Z3dA2Z1A2A1A2S8S16A1A3A3S14G0A1M5A2S5A3S2cS2bS6S37S1SaSaA2S81G4S17G2G3A4VL;A3S5A3S2cS2bS6S27S1eG0A1S23Vtv;S2eVbd;S24S5bS5A2A4A2S5A3S2cS2bS6S68G5Vtv;S2eS67G1A5S5A3S2cS2bS6S7dG5A1S5A3S2bScS82VE0;G1P6eVL;A4VEr;A3A2A2A2A2A2A2A2").
Lemma site_relG : ltac2:(tb__ "0|3|
S3S1S11S11A2M0A1S3S6dA1S3S1SaSaA2A1ScScS12S3S20Q40A1M1A1S32S80R8R7R6R5R4A5S36G0S2S11S11S5cS44Z10S5dA2A4R9A3S2dR5A1S12S2dR1A1SbS36SbR1S2fA3S2bG1S13R4R2A2S13RaR2A2A3F_;Fv;VTR;S29S0VJAv;S23ReS2eRdS24S5bS5A2M2A4A1RaR3R8A5R7A2F_;F_;Frho1;VTR;S29S0VJAv;S23RcS2eRbG2A4A1R9R7R6A5R5A2F_;F_;F_;F_;FQ;Ftp;Frho;FEr;FE0;FL;Fbd;Ftv;").
Proof using ALA HCST HXGL LFSH HKc HBX TR_facts TR_pre TR_exw TR_pureP.
  intros tv bd L E0 Er rho tp Q (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8) Hlin HPHI HK.
  set (nd := NDA tv frL bd (AHead pH true)).
  apply TR_facts. intros HF0.
  apply (TR_pre (fun w => exists rho1, (tblB rho1 /\ forall v, In v V_B -> rw rho1 v = rw rho v) /\ SPA segs (JAv nd) Er rho1 tp w)).
  { intros [tr [ms md]] Hw. exists (rho_absorb rho [shobj g5 4 30 (ob_cells (sh_of E0)) DUnknown] (vms md tp ms)). split.
    - split; [|intros v _; reflexivity].
      destruct Hw as [Hsm (Ai & kc & HJ)]. pose proof HJ as (Hav & _ & HM & HT & _ & _ & (_ & _ & HZ) & _). cbn [nd_tv nd] in HZ.
      pose proof (T_of_TPA NP rho0 rho Ai Hav ltac:(reflexivity) HT) as HTK.
      destruct (lines_blk rho _ (topG (aa_geom Ai)) HF0 R7 HTK) as (_ & HiC & HcK & _ & _ & Htop).
      pose proof (lines_nz rho _ (topG (aa_geom Ai)) tv HF0 R7 HTK HZ Hlin) as Hnz.
      pose proof (has_facts_sound rho _ _ HF0 R3) as HG. apply Forall_cons_iff in HG as [HG1 HG2]. apply Forall_cons_iff in HG2 as [HG2 _].
      pose proof (topG_range (aa_geom Ai)) as TG.
      apply (tblB_absorb_sh AInv CST XGL ALA HCST Kc FB FF BX rho0 nd Ai kc rho tp tr md 0%nat 110%positive 5 120%positive g5 4 30 _ DUnknown _ HJ frL_0);
        [lia | lia | change (fs_frame_size 5) with 2048; lia | exact HG1 | exact HG2 | exact Hlin | exact Hnz | lia | exact HiC | exact HcK | exact HPHI].
    - rewrite <- R8.
      apply (JA_shadow_release segs HTOP AInv CST XGL ALA HCST HXGL LFSH NP Kc rho0 P0 FB FF BX PTrue HKc HBX HNP
               tv frL bd (AHead pH true) 0%nat 110%positive 5 120%positive g5 4 30 (ob_cells (sh_of E0)) DUnknown E0 (objs_nl E0) L rho tp tr ms md
               frL_0 ltac:(lia) R2 R1 ltac:(lia) ltac:(change (fs_frame_size 5) with 2048; lia) eq_refl R3 R4 R5); [|exact Hw].
      intros Ai rho1 tp1 md1 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR.
      exact (lo_robjsR AInv CST ALA HCST FB FF rho0 Ai rho _ tv (objs_nl E0) rho1 tp1 md1 HM HF HP0 Hav HT HTK HN HD HZ HFR R7 Hlin R6). }
  apply TR_exw. intros rho1.
  apply (TR_pureP _ (tblB rho1 /\ forall v, In v V_B -> rw rho1 v = rw rho v)); [intros w [H _]; exact H|]. intros [HPHI1 HV1].
  apply (TR_pre (SPA segs (JAv nd) Er rho1 tp)); [intros w [_ Hw]; exact Hw|]. exact (HK rho1 HPHI1 HV1).
Qed.

Lemma latch_rel : ltac2:(tb__ "0|5|
S3S1S11S11A2M0A1M1S3S6dA1M2G1G2ScScScScS6bS12S3S20Q40A1M3A1S32S7eRcRbRaR9R8R7R6R5R4A9S36G0S2S11S11S5cS44Z10S5dA2A4RdA3S2dR5A1S12SbS36SbR1S2fA3S2bG3S13R3R2A2S13R9R2A2A3F_;Fv;S2dS6aR2R9A2A1VTR;S29S0VJAv;S23S31S2eRfS24S5bS5A2M4A4A1ReS6aR3RaA2R8A5R7A2F_;F_;Frho1;VTR;S29S0VJAv;S23R10S2eRfG4A4A1RbR7R6A5R5A2F_;F_;F_;F_;FQ;Ftp;Frho;Fs;FLb;FLr;FL;FX;Fbdj;Ftvj;Fbd;Ftv;").
Proof using ALA HCST HXGL LFSH HKc HBX TR_facts TR_pre TR_exw TR_pureP.
  intros tv bd tvj bdj X L Lr Lb s rho tp Q
    (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & Cent & Cid & Cnp & Cnb & Ctv & Cfr & Cbd & Cam & CV & _ & _ & Cperm & _) Hlin HPHI HK.
  assert (CREL : rel_chkG tv bd [] L Lr) by (exact (conj C1 (conj C2 (conj C3 (conj eq_refl (conj C4 (conj C5 (conj C6 C7)))))))).
  apply (site_relG tv bd [] L Lr rho tp Q CREL Hlin HPHI). intros rho1 HPHI1 HV1.
  apply (TR_pre (SPA segs (JAv (NDA tvL frL bdj (AHead pH true))) X (rho_sub rho1 s) tp));
    [|exact (HK rho1 HV1 (phi_sub V_B tblB tblB_reads s rho1 CV HPHI1))].
  intros w Hw.
  pose proof (SPA_axforms segs (JAv (NDA tv frL bd (AHead pH true))) (xf_tail Lr) rho1 Lr Lb tp w C8 Hw) as Hw1.
  destruct (latch_exit AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc Lb X s (NDA tv frL bd (AHead pH true)) tvj bdj (AHead pH true) tblB V_B rho1 tp w
              tblB_reads Cent Cid Cnp Cnb Ctv Cfr Cbd Cam CV HPHI1 Hw1) as [_ Hw2].
  exact (SPA_tv_permb segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tvj tvL frL bdj (AHead pH true) X (rho_sub rho1 s) tp w Cperm Hw2).
Qed.
End X.

Section Safety.
Variable ok : world -> Prop.
Hypothesis Hok : ltac2:(tb__ "0|0|
S28S0VKc;Vok;A3").
Hypothesis AC : ltac2:(tb__ "0|0|
S76S0S73VAInv;VCST;VXGL;A5").
Variable FAMQ : list word -> assn.
Hypothesis XKO1 : ltac2:(tb__ "0|1|
S12S3S20Q40A1A1M0G0S34S0Vok;S29S0VJAFv;S2dS4dA2S55R3R2A5VFAMQ;R1A1A4Ftp0;Ftp;Frho;").
Hypothesis XLATCHE2 : ltac2:(tb__ "0|1|
S12S3S20Q40A1A1M0G0S34S0Vok;S29S0VJAFv;S2dS46A2S5eR3R2A5VFAMQ;R1A1A4Ftp0;Ftp;Frho;").

Lemma CHVR_T : ltac2:(tb__ "0|1|
S3S1SaSaA2M0A1S3S1G0SaA2A1S6eS12S3S20Q40A1A1S6cZ3R3A2S34S0Vok;S29S0S25VAInv;VCST;VXGL;VKc;S3cR6R5A2R6R5R4S22S6fS4fS5S63A3AaS62R3R2A5S3dS0S3fR3R2S70VAInv;VCST;VXGL;VKc;S3cS22S4eR6R5R4AaA5A4F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Proof using ALA HCST HXGL HKc Hok AC.
  intros FBc FFc BXc rho1 tp1 HB. unfold PDk_vr.
  eapply (sum_PostsC_k segs AInv CST XGL Kc P0_vr PTrue VR.Pre_vr (ndh h0 true VR.nd0) (PDh PD_vr h0 true) NF); [|exact Hok|exact HB].
  intros ok' FBc' FFc' BXc' rho2 tp2 Hok' HB'.
  eapply (JA_frame_sum segs AInv CST XGL ALA Kc P0_vr PTrue VR.Pre_vr VR.nd0 PD_vr NF h0 true h0_ltNF HamC_vr HamPD_vr P0_vr_mono ok'); [|exact HB'].
  intros FBc'' FFc'' BXc'' rho3 tp3 HB''. exact (vec_reserve_sum AInv CST XGL ALA HCST HXGL Kc HKc FBc'' FFc'' BXc'' HB'' rho3 ok' Hok' AC tp3).
Qed.
Lemma CMEMCPY_T : ltac2:(tb__ "0|2|
S5fS12S3S20Q40A1A1S34S0Vok;S29S0S75VAInv;R3VKc;A3S57R2R1A5S3dS0S3fR2R1S7S1ScS3eA2M0S2ScS3eS56S74VAInv;VCST;VXGL;R3VKc;A5A4M1S7G0G1S8G0A1A3A3A5A4Ftp1;Frho1;FAi;").
Proof using HKc Hok AC.
  intros Ai rho1 tp1. apply (aca_asan_memcpy _ _ _ _ _ AC); [exact HKc|]. eapply ok_frameA_of_K; [exact Hok|]. intros r p t m (_ & K & _). exact K.
Qed.

Lemma CUT3_T : ltac2:(tb__ "0|4|
ScS21S4S1SaS11A2M0S12S3S20Q40A1A1M1G1S36S1S1S1ScS21A2M2S4A2M3G0A2S2G3G0S2G2S4S2ScS21R7R6A4R5A4R4A4S64A3S39S65R6R4A3S34S0Vok;S29S0VJAv;R8A1R9R5R4A5VFAMQ;R3A1A4F_;F_;Ftp0';Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof using ALA HCST HXGL HXlits LFSH HKc HBX Hok AC XKO1 XLATCHE2.
  intros T nd k rv rho tp tp0' Hin Hphi.
  apply (triple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisH k) ok nd T rho tp _ Hphi).
  apply (cfg_sound_JAF segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc PhisH PhisH_reads 600%nat cps_v NP (map efdrop cutsH3) (map efdrop exitsH3) ok (FAMQ tp0') Hok
           (ejcertAF_jcertAF segs NP PhisH _ _ _ _ _ ecertH3_ok)); [| apply in_map_iff; exists (T, nd, k, rv); split; [reflexivity | exact Hin]].
  intros X ndX kX rho1 tp1 HinX. apply in_map_iff in HinX as ([[[X' nd'] k'] rv'] & E & HinX). cbn in E. injection E as <- <- <-.
  cbn [exitsH3 In] in HinX. destruct HinX as [E|[E|[E|[]]]]; injection E as <- <- <- <-; cbn [efdrop fst snd].
  -
    apply (triple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisH 1)). intros HP1.
    pose proof hv3_facts_mc as (CS1 & CS0 & _ & _).
    apply (site_mc AInv CST XGL ALA HCST HXGL HXlits LFSH Kc HKc FB FF BX HBX rho0 (triple segs ok) (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok)
             (@triple_ex segs ok) (TRs_pureP segs ok) (call_soundPA3 segs ok) CMEMCPY_T d_av k_av tv_keep bd_keep X_hv E_mk0 E_mk1 E_mk T_mk0 T_mkr T_mkb T_mck rho1 tp1 _
             hv3_checks_mk CS1 CS0 lines_in_tv_keep CXR_mk HP1).
    intros rho' tp' HP' _.
    exact (reenter_cutJAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue PhisH ok (map efdrop cutsH3) T_mck nd_keep 1%nat (FAMQ tp0') rho' tp'
             ltac:(cbn [map efdrop cutsH3 fst]; inl) HP').
  -
    eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | exact (XKO1 rho1 tp1 tp0')].
  -
    apply (triple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisH 1)). intros HP1.
    apply (latch_rel (triple segs ok) (TRs_facts segs ok) (TRs_pre segs ok) (@triple_ex segs ok) (TRs_pureP segs ok)
             tv_fail brest_vr tv_vr [LAX 0; LAXK 0] X_latchE2 X_rlF X_rlFr X_rlFb s_rlF rho1 tp1 _ hv3_checks_rlF lines_in_tv_fail HP1).
    intros rho2 _ HP2.
    apply (triple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tblB ok (NDA tvL frL [LAX 0; LAXK 0] (AHead pH true)) X_latchE2 (rho_sub rho2 s_rlF) tp1 _ HP2).
    eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | exact (XLATCHE2 (rho_sub rho2 s_rlF) tp1 tp0')].
Qed.

Theorem kvr_T : ltac2:(tb__ "0|1|
S12S3S20Q40A1A1M0G0S34S0Vok;S29S0VJAFv;S2dS45A2S5aR3R2A5VFAMQ;R1A1A4Ftp0;Ftp;Frho;").
Proof using ALA HCST HXGL HXlits LFSH HKc HBX Hok AC XKO1 XLATCHE2.
  intros rho tp tp0.
  apply (triple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tblB). intros HPHI.
  apply (site_vr AInv CST XGL ALA HCST HXGL HXlits LFSH Kc HKc FB FF BX HBX rho0 (triple segs ok) (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok)
           (@triple_ex segs ok) (TRs_pureP segs ok) (call_soundPA3 segs ok) CHVR_T rho tp _ CXR_fail HPHI).
  - intros rho' tp' HP' _. exact (CUT3_T T_keepS nd_keep 1%nat _ rho' tp' tp0 ltac:(cbn [cutsH3]; inl) HP').
  - intros rho' tp' HP' _. exact (CUT3_T T_grownS nd_grown 1%nat _ rho' tp' tp0 ltac:(cbn [cutsH3]; inl) HP').
  - intros rho' tp' HP' _. exact (CUT3_T T_fail nd_fail 1%nat _ rho' tp' tp0 ltac:(cbn [cutsH3]; inl) HP').
Qed.
End Safety.

Section Existence.
Hypothesis ACX : ltac2:(tb__ "0|0|
S77S0S73VAInv;VCST;VXGL;A5").
Variable FAM : ltac2:(tb__ "0|0|
SaS3S20Q40A1A1S32F_;F_;").
Hypothesis FAM_mono : ltac2:(tb__ "0|0|
SaSaS3S20Q40A1A1S35S40R4R3A2VFAM;R5R3R2A3VFAM;R5R4R3A3F_;F_;Fw;Ftp0;Fb';Fb;").
Hypothesis XKO1 : ltac2:(tb__ "0|2|
S12S3S20Q40A1A1M0G0S33S0S29S0VJAFv;S2dS4dA2S55R3R2A5VFAM;S38S2S1S1ScS21A2M1S4A2S1SaS11A2S2G1S4S2ScS21S55S4dA4U1A4S66ZfZ3cA2A4R3A2R1A2A3Ftp0;Ftp;Frho;").
Hypothesis XLATCHE2 : ltac2:(tb__ "0|2|
S12S3S20Q40A1A1M0G0S33S0S29S0VJAFv;S2dS46A2S5eR3R2A5VFAM;S38S2S1S1ScS21A2M1S4A2S1SaS11A2S2G1S4S2ScS21S5eS46A4U1A4S2SaS11S49S47Z1S48A2A4A4R3A2R1A2A3Ftp0;Ftp;Frho;").

Lemma CHVR_E : ltac2:(tb__ "0|1|
S3S1SaSaA2M0A1S3S1G0SaA2A1S6eS12S3S20Q40A1A1S6cZ3R3A2S33S0S29S0S25VAInv;VCST;VXGL;VKc;S3cR6R5A2R6R5R4S22S6fS4fS5S63A3AaS62R3R2A5S3dS0S3fR3R2S70VAInv;VCST;VXGL;VKc;S3cS22S4eR6R5R4AaA5A3F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Proof using ALA HCST HXGL HKc ACX.
  intros FBc FFc BXc rho1 tp1 HB. unfold PDk_vr.
  eapply (sum_PostsC_k_ex segs AInv CST XGL Kc P0_vr PTrue VR.Pre_vr (ndh h0 true VR.nd0) (PDh PD_vr h0 true) NF); [|exact HB].
  intros FBc' FFc' BXc' rho2 tp2 HB'.
  eapply (JA_frame_sum_ex segs AInv CST XGL ALA Kc P0_vr PTrue VR.Pre_vr VR.nd0 PD_vr NF h0 true h0_ltNF HamC_vr HamPD_vr P0_vr_mono); [|exact HB'].
  intros FBc'' FFc'' BXc'' rho3 tp3 HB''. exact (vec_reserve_sum_ex AInv CST XGL ALA HCST HXGL Kc HKc FBc'' FFc'' BXc'' HB'' rho3 ACX tp3).
Qed.
Lemma CMEMCPY_E : ltac2:(tb__ "0|2|
S5fS12S3S20Q40A1A1S33S0S29S0S75VAInv;R3VKc;A3S57R2R1A5S3dS0S3fR2R1S7S1ScS3eA2M0S2ScS3eS56S74VAInv;VCST;VXGL;R3VKc;A5A4M1S7G0G1S8G0A1A3A3A5A3Ftp1;Frho1;FAi;").
Proof using HKc ACX. intros Ai rho1 tp1. apply (acx_asan_memcpy _ _ _ _ _ ACX). exact HKc. Qed.

Lemma CUT3_E : ltac2:(tb__ "0|5|
ScS21S4S1SaS11A2M0S12S3S20Q40A1A1M1SaG1S36S1S1S1ScS21A2M2S4A2M3G0A2S2G3G0S2G2S4S2ScS21R8R7A4R6A4R5A4S64A3S39S65R7R5A3S2cS40Z0S38S2G3G0S2G2S4S2ScS21RaR9A4R8A4R7A4R6A2M4A2S41G4R4A2A2S33S0S29S0VJAv;RaA1RbR7R6A5VFAM;R5R4A2A3F_;F_;F_;Ftp0';Fb;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof using ALA HCST HXGL HXlits LFSH HKc HBX ACX FAM_mono XKO1 XLATCHE2.
  intros T nd k rv rho tp b tp0' Hin Hphi Hm.
  apply (etriple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisH k) nd T rho tp _ Hphi).
  eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; exact (FAM_mono _ b tp0' w ltac:(apply Z.lt_le_incl; exact (proj2 Hm)) Hw) |].
  apply (cfg_complete_JAF_b segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc PhisH PhisH_reads 600%nat cps_v NP cutsH3 exitsH3 (fun b w => FAM b tp0' w)
           (fun b b' w Hb Hw => FAM_mono b b' tp0' w Hb Hw) ecertH3_ok); [|exact Hin].
  intros X ndX kX rvX rho1 tp1 HinX.
  cbn [exitsH3 In] in HinX. destruct HinX as [E|[E|[E|[]]]]; injection E as <- <- <- <-.
  -
    apply (etriple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisH 1)). intros HP1.
    apply (TRe_facts segs). intros HF0. destruct (loopF_vals rho1 _ HF0 hv3_facts_loop) as [HiC Hc26].
    pose proof hv3_facts_mc as (CS1 & CS0 & _ & _).
    apply (site_mc AInv CST XGL ALA HCST HXGL HXlits LFSH Kc HKc FB FF BX HBX rho0 (etriple segs) (TRe_facts segs) (TRe_ex segs) (TRe_pre segs)
             (@etriple_ex segs) (TRe_pureP segs) (call_completePA3 segs) CMEMCPY_E d_av k_av tv_keep bd_keep X_hv E_mk0 E_mk1 E_mk T_mk0 T_mkr T_mkb T_mck rho1 tp1 _
             hv3_checks_mk CS1 CS0 lines_in_tv_keep CXR_mk HP1).
    intros rho' tp' HP' HVB. destruct VB_460 as [I460 I467].
    apply (ereenter_cutJAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue PhisH cutsH3 T_mck nd_keep 1%nat (mH 15 70) _ _ rho' tp' ltac:(cbn [cutsH3]; inl) HP').
    apply (VLA_lt2 rho1 rho' 15 15 80 70 E_mk0 T_mck nd_keep nd_keep 1%nat 1%nat); [exact (HVB _ I460) | exact (HVB _ I467) | exact HiC | exact Hc26 | lia | lia | lia | lia | right; lia].
  -
    eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | exact (XKO1 rho1 tp1 tp0')].
  -
    apply (etriple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue (phiK PhisH 1)). intros HP1.
    pose proof hv3_checks_rlF as CK. pose proof CK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & W460 & W467 & _).
    destruct VB_460 as [I460 I467].
    apply (latch_rel (etriple segs) (TRe_facts segs) (TRe_pre segs) (@etriple_ex segs) (TRe_pureP segs)
             tv_fail brest_vr tv_vr [LAX 0; LAXK 0] X_latchE2 X_rlF X_rlFr X_rlFb s_rlF rho1 tp1 _ CK lines_in_tv_fail HP1).
    intros rho2 HV2 HP2.
    apply (etriple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tblB (NDA tvL frL [LAX 0; LAXK 0] (AHead pH true)) X_latchE2 (rho_sub rho2 s_rlF) tp1 _ HP2).
    eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw |].
    rewrite <- (efmeasA_VLA_agree X_latchE2 X_rlF ndXE nd_fail 1%nat 1%nat RL 1 rho1 rho2 (HV2 _ I460) (HV2 _ I467)).
    rewrite <- (efmeasA_VLA_sub X_latchE2 X_latchE2 ndXE ndXE 1%nat 1%nat RL 1 s_rlF rho2 W460 W467).
    exact (XLATCHE2 (rho_sub rho2 s_rlF) tp1 tp0').
Qed.

Theorem kvr_E : ltac2:(tb__ "0|2|
S12S3S20Q40A1A1M0G0S33S0S29S0VJAFv;S2dS45A2S5aR3R2A5VFAM;S38S2S1S1ScS21A2M1S4A2S1SaS11A2S2G1S4S2ScS21S5aS45A4U1A4S66ZfZ64A2A4R3A2R1A2A3Ftp0;Ftp;Frho;").
Proof using ALA HCST HXGL HXlits LFSH HKc HBX ACX FAM_mono XKO1 XLATCHE2.
  intros rho tp tp0.
  apply (etriple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BX PTrue tblB). intros HPHI.
  pose proof hv3_checks_rel as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CL1 & CL2 & CL3).
  apply (TRe_facts segs). intros HF0. destruct (loopF_vals rho _ HF0 (conj CL1 (conj CL2 CL3))) as [HiC Hc26].
  destruct VB_460 as [I460 I467].
  assert (MM : forall rho' (T : axst) nd, (forall v, In v V_B -> rw rho' v = rw rho v) ->
            0 <= efmeasA (T, nd, 1%nat, mH 15 90) rho' < efmeasA (K_vr, ndA1, 1%nat, mH 15 100) rho).
  { intros rho' T nd HV. apply (VLA_lt2 rho rho' 15 15 100 90 K_vr T ndA1 nd 1%nat 1%nat); [exact (HV _ I460) | exact (HV _ I467) | exact HiC | exact Hc26 | lia | lia | lia | lia | right; lia]. }
  apply (site_vr AInv CST XGL ALA HCST HXGL HXlits LFSH Kc HKc FB FF BX HBX rho0 (etriple segs) (TRe_facts segs) (TRe_ex segs) (TRe_pre segs)
           (@etriple_ex segs) (TRe_pureP segs) (call_completePA3 segs) CHVR_E rho tp _ CXR_fail HPHI).
  - intros rho' tp' HP' HV. exact (CUT3_E T_keepS nd_keep 1%nat (mH 15 90) rho' tp' _ tp0 ltac:(cbn [cutsH3]; inl) HP' (MM rho' T_keepS nd_keep HV)).
  - intros rho' tp' HP' HV. exact (CUT3_E T_grownS nd_grown 1%nat (mH 15 90) rho' tp' _ tp0 ltac:(cbn [cutsH3]; inl) HP' (MM rho' T_grownS nd_grown HV)).
  - intros rho' tp' HP' HV. exact (CUT3_E T_fail nd_fail 1%nat (mH 15 90) rho' tp' _ tp0 ltac:(cbn [cutsH3]; inl) HP' (MM rho' T_fail nd_fail HV)).
Qed.
End Existence.
End Sum.
End Lib_load_obj_hv_pf4.

(* [comment removed for export] *)
Module Lib_load_obj_hv4p.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "and"; "eq"; "@Corelib.Init.Datatypes"; "cons"; "true"; "bool"; "app"; "pair"; "nat"; "prod"; "nil"; "Some"; "fst"; "list"; "S"; "option"; "length"; "negb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "sv"; "SAlu"; "SMd"; "sprop"; "sprop_eqb"; "SPUle"; "sobj"; "ss_facts"; "ss_next"; "valuation"; "SPUlt"; "ss_objs"; "sv_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "apply_axforms"; "AXUnbase"; "AXSplit"; "AXRebase"; "AXMerge"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ew.Lib_load_obj_hv4p"; "s_o3c"; "E_o3c"; "R_o3"; "brest_o3"; "kept_o3"; "Xk_o3"; "T_p0_0"; "T_p1_0"; "bd_o3"; "k_acol"; "payC_o3"; "B_p0"; "B_p1"; "PDk_o3"; "T_p0"; "T_p0r"; "T_p1"; "T_p1r"; "X_3"; "d_acol"; "hand_o3"; "payY_o3"; "tv_o3"; "tv_p0"; "tv_p1"; "xfb_o3"; "acol_base"; "bd_p1"; "nd_p0"; "nd_p1"; "passed_o3"; "payX_o3"; "phi_new"; "phi_old"; "rest_o3"; "vD3"; "vK3"; "xf_o3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "axwf"; "ax_X"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_hvkit"; "oidx"; "s1A"; "sel_front"; "extra_hv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bitem"; "batom"; "ASv"; "bd_subst"; "BI"; "bd_wpos"; "bd_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs"; "vF"; "vDp"; "NP"; "vLEN"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "M_MUL"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ew.Lib_load_obj_hv4p.OP3"; "Pre_op"; "P_op0"; "P_op1"; "PD_op"; "nd0"; "nd0'"; "nd1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue"; "frL"; "A1"; "LA"; "V_B"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_hv3"; "h0"; "c_av"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "NDA"; "ndesc"; "AHead"; "am_subst"; "nd_am"; "nd_bd"; "nd_tv"; "nd_below"; "am_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_hv"; "optL'"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop"; "pH"; "xLC"; "alA"; "bA"; "pI"; "xLD"; "xLK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "@Stdlib.Lists.List"; "existsb"; "In"; "filter"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs"; "kb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fd.Lib_load_obj_hv4w"; "E_o3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG"; "bd_permb"; "tv_permb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.TobjJAH"; "ndh"; "PDh"; "@Stdlib.ZArith.BinInt.Z"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fc.Lib_load_obj_hv4"; "reo_chk4"; "X_1"; "bd_op1"; "nd_op1"; "s128"; "tv_op1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro"; "ax_tidy"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_subA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "import_tv"; "tv_sub_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "T_afterA3"; "pdescA"; "pd_okA"; "xrs_inclb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF"; "V_below"; "@Corelib.Lists.ListDef";
"map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit2"; "lines_chk"; "robjs_chkC"; "xextraLO"; "xrs_chkC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud"; "AK1"; "LAK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "wsub_dom_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK"; "liftPD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "call_checkTA"; "@Stdlib.PArith.BinPos.Pos"; "leb"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fd.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eo.Lib_load_obj_pro2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_hv0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_hv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_hvj OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_hvkit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_hv3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f7.Lib_load_obj_hv3m OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fc.Lib_load_obj_hv4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fd.Lib_load_obj_hv4w.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr HVAddr.

Module OP3. Include Lib_opt_push3. End OP3.
Definition acol_t : T3 := v_acol vsP.
Definition d_acol : sv := t_d acol_t. Definition c_acol : sv := t_c acol_t. Definition k_acol : sv := t_k acol_t.

Definition xf_o3 (T : axst) : list axform := ltac2:(tb__ "0|a|
S2S1fS22S4fS50S5bVT;A3M0S11N80M1A1A2S2S1fS21G0G1A2S9S1fA1M2A3A3ScS1fA1M3S78S20VT;R1A2A1S4bS2S1fS21S4fS7cS11Z118M4A1R1A3G4A2G2A3G3S78S20R2R1A2A1S4bS4fS5aS11Z20A1R1A3S7S5S1fR5S5S1fR3S2S1fS22R1S11Zc0M5A1A2S2S1fS22SdR1A1M6S11ZccA1A2S2S1fS22SdG6A1M7S11Ze0M8A1A2S2S1fS22SdG7A1M9S11ZecA1A2S2S1fS21G6G5A2S2S1fS21G9G8A2G2A3A3A3A3A3A3A3A3Tj;TT2;Tpre2;TT1;Tpre1;").
Definition E_o3c : axst := Eval vm_compute in optL' (apply_axforms E_o3 (xf_o3 E_o3)).
Definition s_o3c : wsub := ltac2:(tb__ "0|1|
S2S8S61S12A2M0S6S61S12S6dS79A4S2G0S6S61S12P13S13S5eS5bS11Z80A1A3A4Sa5PaS4cS26A1S4cS62A1A3A3A3").
Definition R_o3 : list sobj := Eval vm_compute in optR (entails_frA E_o3c OP3.Pre_op s_o3c).
Definition PDk_o3 : list pdescK := ltac2:(tb__ "0|0|
Sa7S8aS65S6dS3A3A1").

Definition passed_o3 : list (sv * sv) := ltac2:(tb__ "0|1|
S2S8S12S12A2M0S6S12S12S38S85Z4S2eA2A4S9G0A1A3").
Definition kept_o3 : list (sv * sv) := Eval vm_compute in firstn 3 tv_op1 ++ skipn 4 tv_op1.
Definition tv_o3 : list (sv * sv) := kept_o3 ++ passed_o3.
Definition hand_o3 : list bitem := Eval vm_compute in bd_subst s_o3c (nd_bd (ndh h0 true OP3.nd0)).
Definition rest_o3 : list bitem := Eval vm_compute in firstn 2 bd_op1 ++ firstn 8 bdrest_o1 ++ skipn 10 bdrest_o1.
Definition bd_o3 : list bitem := Eval vm_compute in (firstn 2 (skipn 8 bdrest_o1) ++ LA (A1 - 96) :: LAK AK1 :: rest_o3).
Definition brest_o3 : list bitem := ltac2:(tb__ "0|0|
S2S53S6bS8bS6aZa8A2A1S2S53Sa4Sa3A1S47A3A3").
Definition phi_old (c k : sv) : bitem := ltac2:(tb__ "0|3|
S57Z1Z0M0S2S8S60S54A2M1S6S60S54Z6S55S14S5fS11Z4A1M2S13S5eS14S5fS11Z3A1Vc;A3S11Z2A1A3A3A1A4S2G1S6S60S54N4S55S14S5fG2Vk;A3A1A4S2G1S6S60S54Z20S55G2A1A4S9G1A1A3A3A3G0A4").
Definition phi_new (c k : sv) : bitem := ltac2:(tb__ "0|3|
S57Z1Z0M0S2S8S60S54A2M1S6S60S54Z6S55S14S5fS11Z4A1M2S13S5eS14S5fS11Z3A1Vc;A3S11Z5A1A3A3A1A4S2G1S6S60S54N4S55S14S5fG2Vk;A3A1A4S2G1S6S60S54Z20S55G2A1A4S9G1A1A3A3A3G0A4").
Definition payX_o3 : list bitem := ltac2:(tb__ "0|0|
S2S53S46S6eS2eA2S2S53S6bS8bS6aZ60A2A1S9S53A1A3A3").
Definition payY_o3 : list bitem := ltac2:(tb__ "0|0|
S2S53S45S6eS2eA2S2S53S6bS8bS6aZa8A2A1S9S53A1A3A3").
Definition payC_o3 : list bitem := Eval vm_compute in (nth 9 bdrest_o1 (LA 0) :: LAK AK1 :: rest_o3).
Definition Xk_o3 : list (sv * sv) := Eval vm_compute in List.filter (fun r => negb (sv_eqb (fst r) d_acol)) (ax_X E_o3c).

Lemma hv4_checks_o3 : ltac2:(tb__ "0|d|
S0S1SeS4bA1S20S86S4aS86A1A2SaS4bS26A2A3S0S1SeScS18A1M0A1S95S26S62S25A3SaG0S27A2A3S0S1S4S94S26S62S25S27S9eS8S8S4bS70A2M1S1bS1bOF_;F_;M2A2M3S4bG3SbS4bS70SbG1G2R1A3A3Ld;S32A4A5S3A3S0S1S4Sa8S5cS25A2S3A3S0S1S4Sa6S25S96A2S3A3S0S1S4S98S25S43S75S89S6dS3S66A3M4A1A3S3A3S0S1S4S77S72S25S73G4A1A2S71S79S3A2M5A2S3A3S0S1S4S84S8S9aG2A2M6G6S9bS62S96S25S1aS4cS26A1M7A1M8SbS9aG2R1A3A5Ld;S32A3S3A3S0S1S4S88S91S3bA2S3A3S0S1S4S87S8eS2dA2S3A3S0S1S4S9cS2aS4eS26A1A2S3A3S0S1ScS53A1S56S25S74G4A1A2S39A3S0S1S4S87S2dS5S53S2fS44A3A2S3A3S0S1S4S87S5S53S2fS3aA3S5S53S39S28A3A2S3A3S0S1S4S58S2fA1S3A3S0S1S4S58S3aA1S3A3S0S1S4S81S15S16S17S6eS11Z8000000A1A2A1S19G7A1M9A3S3A3S0S1S4S76G8S6fS3bS69S2dG5A4A2S3A3S0S1S4S59G8S28A2S3A3S0S1S4Sa9S5cG8A2S3A3S0S1S4Sa0G9S29S69S52S27A5S3A3S0S1S4Sa2G9S29S69Sa1S2aA5S3A3S0S1S4S9fG9A1S3A3S0S1S4S9dG8S6cA2S3A3S0S1S12S80S25PcA2S13S5eS5aS11Z338A1A3A3S0S1S12S80S25P24A2S7bA3S0S1S12S80S25P21A2S13S5eS5aS11Zc0A1A3A3S0S1S12S80S25P22A2S13S5eS5aS11Ze0A1A3A3S0S1S4S76S1aS4cS86A1MaA1MbS8fA2S3A3S0S1S4S9dGbS6cA2S3A3S0S1S4S81S15S16S1cS7dS7aA2A1S19GaA1McA3S3A3S0S1S4S81S15S16S17S7aS5dA2A1GcA3S3A3S1S4S81S15S16S17S5dS11Z4000000A1A2A1GcA3S3A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition T_p1_0 : axst := Eval vm_compute in T_afterA3 OP3.Pre_op E_o3c s_o3c R_o3 OP3.P_op1 Xk_o3.
Definition T_p0_0 : axst := Eval vm_compute in T_afterA3 OP3.Pre_op E_o3c s_o3c R_o3 OP3.P_op0 Xk_o3.
Definition isub_p1 : wsub := Eval vm_compute in import_subA s_o3c OP3.Pre_op OP3.P_op1 E_o3c.
Definition isub_p0 : wsub := Eval vm_compute in import_subA s_o3c OP3.Pre_op OP3.P_op0 E_o3c.
Definition vD3 : sv := Eval vm_compute in sv_subst isub_p1 (SVar 140).
Definition vC3 : sv := Eval vm_compute in sv_subst isub_p1 (SVar 141).
Definition vK3 : sv := Eval vm_compute in sv_subst isub_p1 (SVar 142).
Definition tv_p1 : list (sv * sv) := Eval vm_compute in (kept_o3 ++ import_tv isub_p1 (nd_tv (ndh h0 true OP3.nd1))).
Definition bd_p1 : list bitem := Eval vm_compute in (bd_subst isub_p1 (nd_bd (ndh h0 true OP3.nd1)) ++ brest_o3).
Definition tv_p0 : list (sv * sv) := Eval vm_compute in (kept_o3 ++ import_tv isub_p0 (nd_tv (ndh h0 true OP3.nd0'))).
Definition nd_p1 : ndesc := ltac2:(tb__ "0|0|
S6fS3dS69S40S71S79S3A2A4").
Definition nd_p0 : ndesc := ltac2:(tb__ "0|0|
S6fS3cS69S28S71S79S3A2A4").
Definition acol_base : sv := SAlu ALU_ADD vF (SLit 824).
Definition xfb_o3 (T : axst) : list axform := ltac2:(tb__ "0|a|
S2S1fS21S4fS90S13S5eS5bS11Z80M0A1A3VT;A3G0A2S2S1fS21S4fS3fS11Z0A1M1VT;A3N118A2S2S1fS23S4fS13S5eS5aS11Zc0A1M2A3G1VT;A3A1S2S1fS23S4fS13S5eS5aS11Ze0A1M3A3G1VT;A3A1S9S1fA1M4A3A3A3A3ScS1fA1M5S78S20VT;R1A2A1S4bS2S1fS51S2S7S4fS50S5bR1A3S2S7S4fS50S11N80A1R1A3S9S7A1M6A3A3SfS18S1dS4cR1A1A1A2M7A2S2S1fS24U0A1M8G4A3M9A3G5S78S20R2R1A2A1S4bS5S1fR4S5S1fR2S2S1fS51S2S7S4fS5aS11Z20A1R1A3S2S7S4fS5aG2R1A3S2S7S4fS5aS11ZccA1R1A3S2S7S4fS5aG3R1A3S2S7S4fS5aS11ZecA1R1A3G6A3A3A3A3A3G7A2S2S1fG8S2S1fG8S2S1fG8G9A3A3A3A3A3A3TT2;Tg1;TT1;Tpre;").
Definition B_p1 : axst := Eval vm_compute in optL' (apply_axforms T_p1_0 (xfb_o3 T_p1_0)).
Definition B_p0 : axst := Eval vm_compute in optL' (apply_axforms T_p0_0 (xfb_o3 T_p0_0)).
Definition T_p1r : axst := Eval vm_compute in ax_tidy B_p1.
Definition T_p0r : axst := Eval vm_compute in ax_tidy B_p0.
Definition X_3 : list (sv * sv) := ltac2:(tb__ "0|1|
S2S8S12S12A2M0S6S12S12S48S85Z4S49A2A4S83G0G0S10S1eSbS12S12R1A3S38A2A1Lr;S8dA3A3").
Definition T_p1 : axst := Eval vm_compute in shadow_reopen_stateA T_p1r X_3 g5 4 30.
Definition T_p0 : axst := Eval vm_compute in shadow_reopen_stateA T_p0r X_3 g5 4 30.

Lemma hv4_checks_o3_nd : ltac2:(tb__ "0|6|
S0S1S70S6fS5S8S12S12A2M0S29S97S93S25S62S64S26A4M1S75S89S6dS3S68A3M2A1A2A3S69S5S53S56G1S74G2A1A2S28A3S72G1S73G2A1A2A4S42A3S0S1S70S6fS5G0S29S97S93S25S62S63S26A4M3S75S89S6dS3S67A3M4A1A2A3S69S5S53S56G3S74G4A1A2S28A3S72G3S73G4A1A2A4S41A3S0S1S4bS99S62S26S25S27S64S2aA6S2cA3S0S1S4bS99S62S26S25S27S63S2aA6S2bA3S0S1SeS4bA1M5S20S2cS3eS2cA1A2SaS4bS31A2A3S0S1G5S20S2bS3eS2bA1A2SaS4bS30A2A3S0S1S4bS92S31A1S36A3S0S1S4bS92S30A1S34A3S0S8cS3dS37S36S35A4S0S8cS3cS37S34S33A4S0S1S4S4dS35A1S3A3S0S1S4S4dS33A1S3A3S82G0S6S12S12S7eS85Z10S7fA2A4S29A3A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. vm_compute. repeat split; try reflexivity. repeat (first [left; reflexivity | right]). Qed.
End Lib_load_obj_hv4p.

