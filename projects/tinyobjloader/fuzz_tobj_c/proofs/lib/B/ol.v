(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oj.

(* [comment removed for export] *)
Module Lib_handle_f_gdefs4.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "andb"; "cons"; "nil"; "prod"; "app"; "fst"; "pair"; "None"; "nat"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "SPUle"; "sprop_eqb"; "sv_eqb"; "SLit"; "sv"; "SAlu"; "SVar"; "ss_facts"; "ss_next"; "ss_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s6"; "s_pg"; "Xk_pg"; "@Stdlib.Lists.List"; "existsb"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "ANone"; "NDA"; "nd_bd"; "nd_below"; "nd_tv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs"; "kb"; "NPH"; "hF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_defs"; "fr_hf"; "xfo"; "pA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ol.Lib_handle_f_gdefs4"; "E_pgF"; "PD_pgF"; "Pre_pgF"; "R_pgF"; "P_invF"; "P_okF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s4"; "pDtr"; "pKtr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s5"; "pDrp"; "pDts"; "pKts"; "needA"; "pKrp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oj.Lib_handle_f_gdefs2.PGC"; "nd0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_nodes"; "ndTS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bitem"; "bd_below"; "bd_subst"; "bd_wpos"; "@Stdlib.ZArith.BinInt.Z"; "pow"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o1.Lib_builderH_pf"; "extraOH"; "extraXH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oh.Lib_handle_f_gdefs"; "bF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oj.Lib_handle_f_gdefs2"; "pg0F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve"; "B32"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "wsub_dom_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "pd_okA"; "pdescA"; "xrs_inclb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "call_checkTA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS"; "xrs_checkL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAT"; "robjs_checkP"; "@Stdlib.PArith.BinPos.Pos"; "leb"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAM2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR TobjJAS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAT.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAT.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import ResidualA AxArrA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Lib_scan_double Lib_parse_corner2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Asan_set_shadow_iface.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_parse_corner2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Lib_diag_append OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Asan_set_shadow_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ny.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_handle_f_defs Lib_handle_f_s1 Lib_handle_f_s2 Lib_handle_f_s3 Lib_handle_f_s4 Lib_handle_f_s5 Lib_handle_f_s6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require od.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_handle_f_s9 Lib_handle_f_s9b Lib_handle_f_s10.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_handle_f_nodes.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ny.Lib_builder_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o1.Lib_builderH_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Lib_handle_f_s7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.od.Lib_handle_f_s8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s9b OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Lib_handle_f_epi OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_nodes.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_tess_polygon_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_arith.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Import ScanDoubleAddr VRAddr RA.ReallocAddr ParseCornerAddr DiagAppendAddr HFAddr.
Close Scope bv_scope.
Open Scope Z_scope.
Module PGC. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_tess_polygon_cstates. End PGC.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.ObjZeroA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oj.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oh.Lib_handle_f_gdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oj.Lib_handle_f_gdefs2.

Definition Pre_pgS : axst := Eval vm_compute in optAp (apply_axforms PG.Pre_pg [AXSplit 3 (SLit 16)]).
Definition xF (r : sv * sv) : list sprop := ltac2:(tb__ "0|4|
S1SaSbS10S1dS5SfSfVr;A3M0S9SfSfVr;A3M1A3SeS3eZ2M2Z2fA2A1M3A2S1SaSbG1SeS3eG2Z28A2A1A2S1SaSbG0G3A2S2SaA1A3A3A3").

Definition X_pgF : list (sv * sv) := Eval vm_compute in List.filter (fun r => negb (xr_post_ok PG.P_ok [] r)) (ax_X PG.P_ok).
Definition F_pg : list sprop := Eval vm_compute in flat_map xF X_pgF.
Definition Pre_pgF : axst := Eval vm_compute in ax_add_facts F_pg Pre_pgS.
Definition P_okF : axst := Eval vm_compute in ax_add_facts F_pg PG.P_ok.
Definition P_invF : axst := Eval vm_compute in ax_add_facts F_pg PG.P_inv.
Definition PD_pgF : list (axst * ndesc) := ltac2:(tb__ "0|1|
S1S3S1aS1eA2M0S6S1aS1eS2eS37A4S1G0S6S1aS1eS2fS37A4S2G0A1A3A3").

Definition E_pgS : axst := Eval vm_compute in optAp (apply_axforms E_pg [AXSplit 5 (SLit 16)]).
Definition F_pgC : list sprop := Eval vm_compute in subst_facts s_pg F_pg.
Definition E_pgF : axst := Eval vm_compute in ax_add_facts F_pgC E_pgS.
Definition R_pgF : list sobj := Eval vm_compute in optR (entails_frA E_pgF Pre_pgF s_pg).
Definition T_pgo0F : axst := Eval vm_compute in T_afterA3 Pre_pgF E_pgF s_pg R_pgF P_okF Xk_pg.
Definition T_pgi0F : axst := Eval vm_compute in T_afterA3 Pre_pgF E_pgF s_pg R_pgF P_invF Xk_pg.

Definition facts_sub (F G : list sprop) : bool := ltac2:(tb__ "0|0|
S18SaSaS17SaScR1A1VG;A3Lp;VF;A3").

Definition pg_call_chkF (XGL : list (Z * Z)) : bool := ltac2:(tb__ "0|7|
S0S0S0S0S0S0S0S0S0S0S0S0S0S0S0S0S0S0S0S49S16S1cS2aA1A2S46S2aS2cS15S2dS3fS3S1aS1eA2S1aS5S1aS1eA2S2bA4A5A2S4aS25S15A2A2S45S15S39A2A2S4dS25S13S1bS2aA1M0A1M1A2A2S22G1S20S4S3SfSfA2M2S23S38A1M3S2G2A1A3S27S4S3aS3cS15S2S3aA1A2S21S38A1M4A3S1fA4A2A2S3bG1G4A2A2S3dG4A1A2S18S48S47S2cS39S15G1A4S2bA3A2S42S12G0A1M5A1A2S4cG5G3S27S7S8A1M6S40S2dA6A2S4bVXGL;G5G3S27G6S14G0A1S41S16A8A2SdS19S15PcA2S28Z30A1A2A2SdS19S15PdA2S28Za0A1A2A2SdS19S15PeA2S29A2A2SdS19S15PfA2S32A2A2SdS19S15P10A2S30A2A2SdS19S15P11A2S33A2A2SdS19S15P12A2S35A2A2S43G5A1A2").

Definition pgEF (F : list sprop) : bool := ltac2:(tb__ "0|3|
S0S0S0S0S0S0S0S0S17SaScSbS10S1dS32S24Z4M0S36A2A3S11P1eA1M1A2A1VF;A3S17SaScSbS10S1dS30S24G0S31A2A3G1A2A1VF;A3A2S17SaScSbS10S1dS33S24Z1S34A2A3G1A2A1VF;A3A2S17SaScSbS10S1dS26SeZ200A1A3G1A2A1VF;A3A2S17SaScSbG1SeZ7fffff800000A1A2A1VF;A3A2S17SaScSbS32SeZ800000000000A1M2A2A1VF;A3A2S17SaScSbS30G2A2A1VF;A3A2S17SaScSbS26G2A2A1VF;A3A2S17SaScSbS34SeS44A1A2A1VF;A3A2").
End Lib_handle_f_gdefs4.

(* [comment removed for export] *)
Module Lib_handle_f_g6.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "sobj"; "DUnknown"; "SAlu"; "cell"; "mkObj"; "sprop"; "ss_facts"; "sprop_eqb"; "ss_next"; "ss_objs"; "SPUle"; "obj_wf"; "SVar"; "SPUlt"; "sv_below"; "SMd"; "SExt"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Init.Datatypes"; "nil"; "bool"; "true"; "cons"; "Some"; "option"; "andb"; "list"; "prod"; "app"; "pair"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "M_MUL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_defs"; "pDco"; "reshapeA"; "pA"; "pKco"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs"; "hF"; "hG"; "kb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXMerge"; "apply_axforms"; "AXSelect"; "@Stdlib.Lists.List"; "existsb"; "nth_error"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oj.Lib_handle_f_gdefs2"; "off_g1"; "off_g2"; "off_g3"; "E_g1b"; "E_g2b"; "E_g3b"; "T_g1u"; "T_g2u"; "T_g3u"; "E_g1a"; "E_g1c"; "E_g2a"; "E_g2c"; "E_g3a"; "E_g3c"; "T_g1t"; "T_g2t"; "T_g3t"; "T_g3w"; "T_g1v"; "T_g2v"; "T_g3v"; "cells_g1a"; "cells_g1b"; "xf_g1"; "xf_g2"; "xf_g3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s2"; "L_mc1"; "Pre_mc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.od.Lib_handle_f_s8"; "g_need"; "s_g"; "E_g1"; "E_g2"; "E_g3"; "E_g1_0"; "E_g1_3"; "E_g2_0"; "E_g3_0"; "R_g1"; "R_g2"; "R_g3"; "pL"; "sel_g"; "T_g1"; "T_g2"; "T_g3"; "@Stdlib.ZArith.BinInt.Z"; "sub"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_nodes"; "ndLL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ol.Lib_handle_f_g6.G"; "E_g1_1x"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oh.Lib_handle_f_gdefs"; "fF"; "gF"; "purec_chk"; "vlF"; "xff_chk"; "release_chk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve"; "two47"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s6"; "objs_butlast"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "nd_bd"; "nd_tv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Lib_handle_f_s7"; "pNT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "T_afterA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS"; "shadow_release_stateA"; "shobj"; "shadow_reopen_stateA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oj.Lib_handle_f_gdefs3"; "release0_chk"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAM2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR TobjJAS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAT.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAT.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import ResidualA AxArrA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Lib_scan_double Lib_parse_corner2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Asan_set_shadow_iface.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_parse_corner2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Lib_diag_append OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Asan_set_shadow_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ny.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_handle_f_defs Lib_handle_f_s1 Lib_handle_f_s2 Lib_handle_f_s3 Lib_handle_f_s4 Lib_handle_f_s5 Lib_handle_f_s6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require od.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_handle_f_s9 Lib_handle_f_s9b Lib_handle_f_s10.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_handle_f_nodes.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ny.Lib_builder_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o1.Lib_builderH_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Lib_handle_f_s7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.od.Lib_handle_f_s8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s9b OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Lib_handle_f_epi OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_nodes.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_tess_polygon_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_arith.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Import ScanDoubleAddr VRAddr RA.ReallocAddr ParseCornerAddr DiagAppendAddr HFAddr.
Close Scope bv_scope.
Open Scope Z_scope.
Module PGC. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_tess_polygon_cstates. End PGC.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.ObjZeroA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oj.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oh.Lib_handle_f_gdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oj.Lib_handle_f_gdefs2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oj.Lib_handle_f_gdefs3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import MemoFast.
Ltac vmr := vmc.

Section G.
Variable XGL : list (Z * Z).

Definition E_g1_1x : axst := Eval vm_compute in shadow_release_stateA E_g1_0 (objs_butlast E_g1_0) 160 [].
Lemma g1_robjs1 : ltac2:(tb__ "0|0|
S12S1aS1A1SaS20S54A1A1S1cS1S6bS54A1S16S1S73S29Z26Z27S49S2A5S13S1A1A3A3A3"). Proof. vmr. Qed.
Lemma g1_rel1 : ltac2:(tb__ "0|0|
S12S14S75S54Z26Z27S2A4S15A3"). Proof. vmr. Qed.
Lemma E_g1_1x_eq : ltac2:(tb__ "0|0|
S12S1fS72S54S6bS54A1Pa0S13S1bS31S31A2A1A4S63A3"). Proof. vmr. Qed.
Lemma g1_robjs2 : ltac2:(tb__ "0|0|
S12S1aS1A1SaS20S63A1A1S1cS1S6bS63A1S16S1S73S29Z1cZ21S48S2A5S13S1A1A3A3A3"). Proof. vmr. Qed.
Lemma g1_rel2 : ltac2:(tb__ "0|1|
S12S14S69S63S6bS63A1Z1cZ21S48S2S16S1bS31S31A2M0S1dS31S31Ze0Z24A4S13G0A1A3S6dS62A1S6cS62A1A9S15A3"). Proof. vmr. Qed.
Lemma E_g1_3x_eq : ltac2:(tb__ "0|1|
S12S1fS72S63S6bS63A1Pa0S16S1bS31S31A2M0S1dS31S31Ze0Z24A4S13G0A1A3A4S55A3"). Proof. vmr. Qed.
Lemma E_g1a_eq : ltac2:(tb__ "0|0|
S12S18S1fA1S2dS55S4aA2S17S1fS3bA2A3"). Proof. vmr. Qed.
Lemma g1_o2 : ltac2:(tb__ "0|0|
S12S18S1A1S30S1SaS20S3bA1A1U2A3S17S1S5S28S0Ze0A1S0ZecA1S13S4A1S2A5A2A3"). Proof. vmr. Qed.
Lemma g1_wf2 : ltac2:(tb__ "0|2|
S12S14S19ScS9S20S3bA1M0A1S5S3S22S28S0Ze0M1A1A3S0Z0A1S0S60ZecG1A2A1S13S4A1S2A5A2S64S7G0A1A1A2S15A3"). Proof. vmr. Qed.
Lemma E_g1b_eq : ltac2:(tb__ "0|1|
S12S1fS25S3bU2S5S3S22S28S0Ze0M0A1A3S0Z0A1S0S60ZecG0A2A1S13S4A1S2A5A3S35A3"). Proof. vmr. Qed.
Lemma g1_oi : ltac2:(tb__ "0|0|
S12S18S1A1S30S1SaS20S35A1A1U23A3S17S1S5S24S32S3S22S32S0ZcA1A3S13S4A1S2A5A2A3"). Proof. vmr. Qed.
Lemma g1_wfi : ltac2:(tb__ "0|0|
S12S14ScS9S20S35A1A1S5S3S22S24S32A3S0Z0A1S0ZcA1S13S4A1S2A5A2S15A3"). Proof. vmr. Qed.
Lemma E_g1c_eq : ltac2:(tb__ "0|0|
S12S1fS25S35U23S5S3S22S24S32A3S0Z0A1S0ZcA1S13S4A1S2A5A3S3cA3"). Proof. vmr. Qed.
Lemma g1_bnd : ltac2:(tb__ "0|0|
S12S14S2fS6S8SbS24S0S6aA1A2A1S7S20S35A1A1A3S15A3"). Proof. vmr. Qed.
Lemma E_g1_eq3 : ltac2:(tb__ "0|0|
S12S1fS6fS4fS55A1S3cA2S51A3"). Proof. vmr. Qed.
Lemma g1_gneed : ltac2:(tb__ "0|2|
S12S1aS6A1S4fS55A1S16S6SbS3S22S3S22S24S10S23S11S1eQ20SdP1e1A1A3S0ZcM0A1M1A3A3G1A3S3S22S24S2aG0S27A2A3A2S13S6A1A3A3"). Proof. vmr. Qed.
Lemma g1_xff : ltac2:(tb__ "0|0|
S12S14S68S3cS4fS55A1A2S15A3"). Proof. vmr. Qed.
Lemma g1_gF : ltac2:(tb__ "0|1|
S12S14S19S65S7S20S3cA1A1M0A1S2fS6S8SeSdP1e1A1S26A2A1G0A3A2S15A3"). Proof. vmr. Qed.
Lemma g1_chk : ltac2:(tb__ "0|0|
S12S14S66VXGL;S4eS16S1fS4dS16S1fS4dS13S1fA1A3A3S51S6dS62A1S6cS62A1S50S51A1S58A8S15A3"). Proof. vmr. Qed.
Lemma R_g1_eq2 : ltac2:(tb__ "0|1|
S12S18S1aS1A1M0A1S70S51S4eS50S51A1A3S17G0S58A2A3"). Proof. vmr. Qed.
Lemma T_g1t_eq : ltac2:(tb__ "0|0|
S12S1fS71S4eS51S50S51A1S58S4dA5S41A3"). Proof. vmr. Qed.
Lemma g1_to1 : ltac2:(tb__ "0|1|
S12S18S1A1S30S1SaS20S41A1A1U1A3S17S1S5S3S22S28S0Ze0M0A1A3S0Z0A1S0S60ZecG0A2A1S13S4A1S2A5A2A3"). Proof. vmr. Qed.
Lemma g1_twf1 : ltac2:(tb__ "0|1|
S12S14S19ScS9S20S41A1M0A1S5S28S0Ze0A1S0ZecA1S13S4A1S2A5A2S64S7G0A1A1A2S15A3"). Proof. vmr. Qed.
Lemma T_g1u_eq : ltac2:(tb__ "0|0|
S12S1fS25S41U1S5S28S0Ze0A1S0ZecA1S13S4A1S2A5A3S38A3"). Proof. vmr. Qed.
Lemma g1_to2 : ltac2:(tb__ "0|0|
S12S18S1A1S30S1SaS20S38A1A1U2A3S17S1S5S3S22S24S32A3S0Z0A1S0ZcA1S13S4A1S2A5A2A3"). Proof. vmr. Qed.
Lemma g1_twf2 : ltac2:(tb__ "0|0|
S12S14ScS9S20S38A1A1S5S24S32S3S22S32S0ZcA1A3S13S4A1S2A5A2S15A3"). Proof. vmr. Qed.
Lemma T_g1v_eq : ltac2:(tb__ "0|0|
S12S1fS25S38U2S5S24S32S3S22S32S0ZcA1A3S13S4A1S2A5A3S45A3"). Proof. vmr. Qed.
Lemma g1_tbnd : ltac2:(tb__ "0|0|
S12S14S2fS6S8SbS24S0S6aA1A2A1S7S20S38A1A1A3S15A3"). Proof. vmr. Qed.
Lemma T_g1_eq2 : ltac2:(tb__ "0|2|
S12S18S1fA1S2dS45S16S2bS2eS5cA1S16S2bS2cU1A1M0S16S2bG0S16S2bS2cU20A1M1S16S2bG1S13S2bA1A3A3A3A3A3A2S17S1fS5dA2A3"). Proof. vmr. Qed.
Lemma g1_vlF : ltac2:(tb__ "0|0|
S12S14S67S7S20S54A1A1A1S15A3"). Proof. vmr. Qed.
Lemma g1_meas : ltac2:(tb__ "0|1|
S12S14S19SfS9S20S51A1A1M0S6eA2SfG0S5bA2A2S15A3"). Proof. vmr. Qed.

Lemma E_g2a_eq : ltac2:(tb__ "0|0|
S12S18S1fA1S2dS56S4bA2S17S1fS3dA2A3"). Proof. vmr. Qed.
Lemma g2_o2 : ltac2:(tb__ "0|0|
S12S18S1A1S30S1SaS20S3dA1A1U2A3S17S1S5S28S0ZecA1S0Zf8A1S13S4A1S2A5A2A3"). Proof. vmr. Qed.
Lemma g2_wf2 : ltac2:(tb__ "0|2|
S12S14S19ScS9S20S3dA1M0A1S5S3S22S28S0ZecM1A1A3S0Z0A1S0S60Zf8G1A2A1S13S4A1S2A5A2S64S7G0A1A1A2S15A3"). Proof. vmr. Qed.
Lemma E_g2b_eq : ltac2:(tb__ "0|1|
S12S1fS25S3dU2S5S3S22S28S0ZecM0A1A3S0Z0A1S0S60Zf8G0A2A1S13S4A1S2A5A3S36A3"). Proof. vmr. Qed.
Lemma g2_oi : ltac2:(tb__ "0|0|
S12S18S1A1S30S1SaS20S36A1A1U23A3S17S1S5S24S33S3S22S33S0ZcA1A3S13S4A1S2A5A2A3"). Proof. vmr. Qed.
Lemma g2_wfi : ltac2:(tb__ "0|0|
S12S14ScS9S20S36A1A1S5S3S22S24S33A3S0Z0A1S0ZcA1S13S4A1S2A5A2S15A3"). Proof. vmr. Qed.
Lemma E_g2c_eq : ltac2:(tb__ "0|0|
S12S1fS25S36U23S5S3S22S24S33A3S0Z0A1S0ZcA1S13S4A1S2A5A3S3eA3"). Proof. vmr. Qed.
Lemma g2_bnd : ltac2:(tb__ "0|1|
S12S14S19S19S2fS6S8SbS24S0S6aA1A2A1S7S20S36A1A1M0A3S2fS6S8SeSdP1e2A1S26A2A1G0A3A2S2fS6S8SbS26S0S61Z2Z14A2A1A2A1G0A3A2S15A3"). Proof. vmr. Qed.
Lemma E_g2_eq3 : ltac2:(tb__ "0|0|
S12S1fS6fS4fS56A1S3eA2S52A3"). Proof. vmr. Qed.
Lemma g2_gneed : ltac2:(tb__ "0|2|
S12S1aS6A1S4fS56A1S16S6SbS3S22S3S22S24S10S23SdP1e2A1S0ZcM0A1M1A3A3G1A3S3S22S24S2aG0S27A2A3A2S13S6A1A3A3"). Proof. vmr. Qed.
Lemma g2_xff : ltac2:(tb__ "0|0|
S12S14S68S3eS4fS56A1A2S15A3"). Proof. vmr. Qed.
Lemma g2_gF : ltac2:(tb__ "0|1|
S12S14S19S65S7S20S3eA1A1M0A1S2fS6S8SeSdP1e2A1S26A2A1G0A3A2S15A3"). Proof. vmr. Qed.
Lemma g2_chk : ltac2:(tb__ "0|0|
S12S14S66VXGL;S4eS16S1fS4dS16S1fS4dS13S1fA1A3A3S52S6dS62A1S6cS62A1S50S52A1S59A8S15A3"). Proof. vmr. Qed.
Lemma R_g2_eq2 : ltac2:(tb__ "0|1|
S12S18S1aS1A1M0A1S70S52S4eS50S52A1A3S17G0S59A2A3"). Proof. vmr. Qed.
Lemma T_g2t_eq : ltac2:(tb__ "0|0|
S12S1fS71S4eS52S50S52A1S59S4dA5S42A3"). Proof. vmr. Qed.
Lemma g2_to1 : ltac2:(tb__ "0|1|
S12S18S1A1S30S1SaS20S42A1A1U1A3S17S1S5S3S22S28S0ZecM0A1A3S0Z0A1S0S60Zf8G0A2A1S13S4A1S2A5A2A3"). Proof. vmr. Qed.
Lemma g2_twf1 : ltac2:(tb__ "0|1|
S12S14S19ScS9S20S42A1M0A1S5S28S0ZecA1S0Zf8A1S13S4A1S2A5A2S64S7G0A1A1A2S15A3"). Proof. vmr. Qed.
Lemma T_g2u_eq : ltac2:(tb__ "0|0|
S12S1fS25S42U1S5S28S0ZecA1S0Zf8A1S13S4A1S2A5A3S39A3"). Proof. vmr. Qed.
Lemma g2_to2 : ltac2:(tb__ "0|0|
S12S18S1A1S30S1SaS20S39A1A1U2A3S17S1S5S3S22S24S33A3S0Z0A1S0ZcA1S13S4A1S2A5A2A3"). Proof. vmr. Qed.
Lemma g2_twf2 : ltac2:(tb__ "0|0|
S12S14ScS9S20S39A1A1S5S24S33S3S22S33S0ZcA1A3S13S4A1S2A5A2S15A3"). Proof. vmr. Qed.
Lemma T_g2v_eq : ltac2:(tb__ "0|0|
S12S1fS25S39U2S5S24S33S3S22S33S0ZcA1A3S13S4A1S2A5A3S46A3"). Proof. vmr. Qed.
Lemma g2_tbnd : ltac2:(tb__ "0|1|
S12S14S19S19S2fS6S8SbS24S0S6aA1A2A1S7S20S39A1A1M0A3S2fS6S8SeSdP1e2A1S26A2A1G0A3A2S2fS6S8SbS26S0S61Z2Z14A2A1A2A1G0A3A2S15A3"). Proof. vmr. Qed.
Lemma T_g2_eq2 : ltac2:(tb__ "0|2|
S12S18S1fA1S2dS46S16S2bS2eS5cA1S16S2bS2cU1A1M0S16S2bG0S16S2bS2cU20A1M1S16S2bG1S13S2bA1A3A3A3A3A3A2S17S1fS5eA2A3"). Proof. vmr. Qed.
Lemma g2_vlF : ltac2:(tb__ "0|0|
S12S14S67S7S20S56A1A1A1S15A3"). Proof. vmr. Qed.
Lemma g2_meas : ltac2:(tb__ "0|1|
S12S14S19SfS9S20S52A1A1M0S6eA2SfG0S5bA2A2S15A3"). Proof. vmr. Qed.

Lemma E_g3a_eq : ltac2:(tb__ "0|0|
S12S18S1fA1S2dS57S4cA2S17S1fS3fA2A3"). Proof. vmr. Qed.
Lemma g3_o2 : ltac2:(tb__ "0|0|
S12S18S1A1S30S1SaS20S3fA1A1U2A3S17S1S5S28S0Zf8A1S0Z104A1S13S4A1S2A5A2A3"). Proof. vmr. Qed.
Lemma g3_wf2 : ltac2:(tb__ "0|2|
S12S14S19ScS9S20S3fA1M0A1S5S3S22S28S0Zf8M1A1A3S0Z0A1S0S60Z104G1A2A1S13S4A1S2A5A2S64S7G0A1A1A2S15A3"). Proof. vmr. Qed.
Lemma E_g3b_eq : ltac2:(tb__ "0|1|
S12S1fS25S3fU2S5S3S22S28S0Zf8M0A1A3S0Z0A1S0S60Z104G0A2A1S13S4A1S2A5A3S37A3"). Proof. vmr. Qed.
Lemma g3_oi : ltac2:(tb__ "0|0|
S12S18S1A1S30S1SaS20S37A1A1U23A3S17S1S5S24S34S3S22S34S0ZcA1A3S13S4A1S2A5A2A3"). Proof. vmr. Qed.
Lemma g3_wfi : ltac2:(tb__ "0|0|
S12S14ScS9S20S37A1A1S5S3S22S24S34A3S0Z0A1S0ZcA1S13S4A1S2A5A2S15A3"). Proof. vmr. Qed.
Lemma E_g3c_eq : ltac2:(tb__ "0|0|
S12S1fS25S37U23S5S3S22S24S34A3S0Z0A1S0ZcA1S13S4A1S2A5A3S40A3"). Proof. vmr. Qed.
Lemma g3_bnd : ltac2:(tb__ "0|1|
S12S14S19S19S2fS6S8SbS24S0S6aA1A2A1S7S20S37A1A1M0A3S2fS6S8SeSdP1e3A1S26A2A1G0A3A2S2fS6S8SbS26S0S61Z2Z14A2A1A2A1G0A3A2S15A3"). Proof. vmr. Qed.
Lemma E_g3_eq3 : ltac2:(tb__ "0|0|
S12S1fS6fS4fS57A1S40A2S53A3"). Proof. vmr. Qed.
Lemma g3_gneed : ltac2:(tb__ "0|2|
S12S1aS6A1S4fS57A1S16S6SbS3S22S3S22S24S10S23SdP1e3A1S0ZcM0A1M1A3A3G1A3S3S22S24S2aG0S27A2A3A2S13S6A1A3A3"). Proof. vmr. Qed.
Lemma g3_xff : ltac2:(tb__ "0|0|
S12S14S68S40S4fS57A1A2S15A3"). Proof. vmr. Qed.
Lemma g3_gF : ltac2:(tb__ "0|1|
S12S14S19S65S7S20S40A1A1M0A1S2fS6S8SeSdP1e3A1S26A2A1G0A3A2S15A3"). Proof. vmr. Qed.
Lemma g3_chk : ltac2:(tb__ "0|0|
S12S14S66VXGL;S4eS16S1fS4dS16S1fS4dS13S1fA1A3A3S53S6dS62A1S6cS62A1S50S53A1S5aA8S15A3"). Proof. vmr. Qed.
Lemma R_g3_eq2 : ltac2:(tb__ "0|1|
S12S18S1aS1A1M0A1S70S53S4eS50S53A1A3S17G0S5aA2A3"). Proof. vmr. Qed.
Lemma T_g3t_eq : ltac2:(tb__ "0|0|
S12S1fS71S4eS53S50S53A1S5aS4dA5S43A3"). Proof. vmr. Qed.
Lemma g3_to1 : ltac2:(tb__ "0|1|
S12S18S1A1S30S1SaS20S43A1A1U1A3S17S1S5S3S22S28S0Zf8M0A1A3S0Z0A1S0S60Z104G0A2A1S13S4A1S2A5A2A3"). Proof. vmr. Qed.
Lemma g3_twf1 : ltac2:(tb__ "0|1|
S12S14S19ScS9S20S43A1M0A1S5S28S0Zf8A1S0Z104A1S13S4A1S2A5A2S64S7G0A1A1A2S15A3"). Proof. vmr. Qed.
Lemma T_g3u_eq : ltac2:(tb__ "0|0|
S12S1fS25S43U1S5S28S0Zf8A1S0Z104A1S13S4A1S2A5A3S3aA3"). Proof. vmr. Qed.
Lemma g3_to2 : ltac2:(tb__ "0|0|
S12S18S1A1S30S1SaS20S3aA1A1U2A3S17S1S5S3S22S24S34A3S0Z0A1S0ZcA1S13S4A1S2A5A2A3"). Proof. vmr. Qed.
Lemma g3_twf2 : ltac2:(tb__ "0|0|
S12S14ScS9S20S3aA1A1S5S24S34S3S22S34S0ZcA1A3S13S4A1S2A5A2S15A3"). Proof. vmr. Qed.
Lemma T_g3v_eq : ltac2:(tb__ "0|0|
S12S1fS25S3aU2S5S24S34S3S22S34S0ZcA1A3S13S4A1S2A5A3S47A3"). Proof. vmr. Qed.
Lemma g3_tbnd : ltac2:(tb__ "0|1|
S12S14S19S19S2fS6S8SbS24S0S6aA1A2A1S7S20S3aA1A1M0A3S2fS6S8SeSdP1e3A1S26A2A1G0A3A2S2fS6S8SbS26S0S61Z2Z14A2A1A2A1G0A3A2S15A3"). Proof. vmr. Qed.
Lemma T_g3w_eq : ltac2:(tb__ "0|2|
S12S18S1fA1S2dS47S16S2bS2eS5cA1S16S2bS2cU1A1M0S16S2bG0S16S2bS2cU20A1M1S16S2bG1S13S2bA1A3A3A3A3A3A2S17S1fS44A2A3"). Proof. vmr. Qed.

Lemma T_g3_eq2 : ltac2:(tb__ "0|0|
S12S1fS74S44S21S44A1S29Z26Z27A5S5fA3"). Proof. vmr. Qed.
Lemma g3_vlF : ltac2:(tb__ "0|0|
S12S14S67S7S20S57A1A1A1S15A3"). Proof. vmr. Qed.
Lemma g3_meas : ltac2:(tb__ "0|1|
S12S14S19SfS9S20S53A1A1M0S6eA2SfG0S5bA2A2S15A3"). Proof. vmr. Qed.

End G.
End Lib_handle_f_g6.

(* [comment removed for export] *)
Module Lib_handle_f_chk2.

From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG SymSummary SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SummaryA EntailA CFGA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require BudA TobjJA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.JcertCutA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs Lib_handle_f_defs Lib_handle_f_s1 Lib_handle_f_s2 Lib_handle_f_s3 Lib_handle_f_s4 Lib_handle_f_s5 Lib_handle_f_s6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require od.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_handle_f_s9 Lib_handle_f_s9b Lib_handle_f_s10.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_handle_f_nodes Lib_handle_f_s8w.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oj.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Lib_handle_f_s7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.od.Lib_handle_f_s8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s9b OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Lib_handle_f_epi OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_nodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s8w OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oh.Lib_handle_f_nodes2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Lib_handle_f_fastcert OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oj.Lib_handle_f_chk0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import HFAddr.
Lemma cc_1 : CC 1 C_pro = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_8 : CC 8 JF_co = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_15 : CC 15 JR_mi = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_22 : CC 22 JR_mm = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_29 : CC 29 JR_trg = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_36 : CC 36 JF_rp = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_43 : CC 43 T_md = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_50 : CC 50 T_g2 = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_57 : CC 57 T_m4 = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_64 : CC 64 T_f5f = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End Lib_handle_f_chk2.

(* [comment removed for export] *)
Module Lib_handle_f_chk1.

From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG SymSummary SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SummaryA EntailA CFGA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require BudA TobjJA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.JcertCutA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs Lib_handle_f_defs Lib_handle_f_s1 Lib_handle_f_s2 Lib_handle_f_s3 Lib_handle_f_s4 Lib_handle_f_s5 Lib_handle_f_s6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require od.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_handle_f_s9 Lib_handle_f_s9b Lib_handle_f_s10.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_handle_f_nodes Lib_handle_f_s8w.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oj.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Lib_handle_f_s7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.od.Lib_handle_f_s8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s9b OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Lib_handle_f_epi OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_nodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s8w OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oh.Lib_handle_f_nodes2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Lib_handle_f_fastcert OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oj.Lib_handle_f_chk0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import HFAddr.
Lemma cc_0 : CC 0 Pre_hf = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_7 : CC 7 JR_co = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_14 : CC 14 RW = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_21 : CC 21 T_mcq = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_28 : CC 28 K1Xb = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_35 : CC 35 JR_rp = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_42 : CC 42 JF_ts = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_49 : CC 49 T_g1 = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_56 : CC 56 JF_fv4 = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_63 : CC 63 C_Eo2 = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End Lib_handle_f_chk1.

(* [comment removed for export] *)
Module Lib_handle_f_g5b.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "SVar"; "sprop"; "sv_eqb"; "ss_facts"; "SAlu"; "SPUle"; "sv_below"; "ss_next"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.od.Lib_handle_f_s8"; "lDfv"; "lKfv"; "pL"; "cFV"; "@Corelib.Init.Datatypes"; "bool"; "true"; "cons"; "nil"; "pair"; "prod"; "app"; "list"; "andb"; "Some"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s9"; "E_fv4"; "s_fv4"; "T_fv4f"; "E_fv4_0"; "R_fv4"; "XnoLoc"; "JR_fv4"; "T_fv4g"; "T_fv4k"; "JF_fv4"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs"; "kb"; "hG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bitem"; "bd_subst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_defs.VN"; "Pre_vr"; "P_grown"; "P_keep"; "P_fail"; "tv0"; "bdP"; "nd0"; "tvP"; "vKn"; "vN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oh.Lib_handle_f_gdefs"; "kept_fv4"; "brest_fv4"; "E_fv41x"; "T_fv4k1"; "s_fv4g"; "s_fv4k"; "land_chk"; "T_fv4f0"; "T_fv4g0"; "T_fv4k0"; "bd2_fv4g"; "bd2_fv4k"; "bdG_fv4"; "bdK_fv4"; "s_fv4f"; "xff_chk"; "liveF"; "reopen_chk"; "tv2_fv4f"; "tv2_fv4g"; "tv2_fv4k"; "vlF"; "vrLF"; "vr_chk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Lib_handle_f_s7"; "pNT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_subA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "nd_bd"; "nd_tv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_nodes"; "ndL4b"; "ndL4a"; "ndL4bf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s2"; "XkeepF"; "xf_backV"; "NFV"; "vr_need"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "sv_subst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "import_tv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "T_afterA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS"; "shadow_reopen_stateA"; "@Corelib.Lists.ListDef"; "firstn"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_defs"; "pA"; "fv_c"; "fv_n"; "xf_vr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oj.Lib_handle_f_gdefs3"; "reopenS_chk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAG"; "tv_permb"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAM2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR TobjJAS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAT.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAT.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import ResidualA AxArrA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Lib_scan_double Lib_parse_corner2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Asan_set_shadow_iface.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_parse_corner2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Lib_diag_append OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Asan_set_shadow_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ny.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_handle_f_defs Lib_handle_f_s1 Lib_handle_f_s2 Lib_handle_f_s3 Lib_handle_f_s4 Lib_handle_f_s5 Lib_handle_f_s6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require od.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_handle_f_s9 Lib_handle_f_s9b Lib_handle_f_s10.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_handle_f_nodes.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ny.Lib_builder_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o1.Lib_builderH_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Lib_handle_f_s7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.od.Lib_handle_f_s8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s9b OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Lib_handle_f_epi OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_nodes.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_tess_polygon_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_arith.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Import ScanDoubleAddr VRAddr RA.ReallocAddr ParseCornerAddr DiagAppendAddr HFAddr.
Close Scope bv_scope.
Open Scope Z_scope.
Module PGC. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_tess_polygon_cstates. End PGC.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oj.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oh.Lib_handle_f_gdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oj.Lib_handle_f_gdefs3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import MemoFast.
Ltac vmr := vmc.

Section G.
Variable XGL : list (Z * Z).

Lemma E_fv41x_eq : ltac2:(tb__ "0|0|
SaS19S1aA1S59S20S62U10Z210A2A2S18S1aS37A2A3"). Proof. vmr. Qed.
Lemma E_fv4_eq2 : ltac2:(tb__ "0|0|
SaS1aS63S57Z4S6S5eSeSdA1S1Z1A1A3S56S5fA1A3S37A2S1dA3"). Proof. vmr. Qed.
Lemma fv4_xff : ltac2:(tb__ "0|0|
SaSfS44S37S57Z4S6S5eSeSdA1S1Z1A1A3S56S5fA1A3A2S10A3"). Proof. vmr. Qed.
Lemma fv4_needF : ltac2:(tb__ "0|0|
SaSfS4bZ4Z1Z8S60S61S5S1bS37A1A1A6S10A3"). Proof. vmr. Qed.
Lemma fv4_tvp : ltac2:(tb__ "0|1|
SaSfS66S50S52A1S15S14S0S0A2M0S35S11G0S13S0S0SbS27Z4ScA2A4S12G0A1A3A3A2S10A3"). Proof. vmr. Qed.
Lemma fv4_chk : ltac2:(tb__ "0|0|
SaSfS4cVXGL;S1dS35SbScZ4Z210S4fS52A1S36S1eS21S54SbS1cS20A1A2AcS10A3"). Proof. vmr. Qed.
Lemma fv4_iK : ltac2:(tb__ "0|1|
SaS16S14S0S0A2M0A1S5aS4eS1eS2bS2dS1dA4S2fA2S11G0S13S0S0SbS27Z4ScA2A4S12G0A1A3A3"). Proof. vmr. Qed.
Lemma fv4_iF : ltac2:(tb__ "0|1|
SaS16S14S0S0A2M0A1S5aS4eS1eS2bS2eS1dA4S2fA2S11G0S13S0S0SbS27Z4ScA2A4S12G0A1A3A3"). Proof. vmr. Qed.
Lemma fv4_iG : ltac2:(tb__ "0|1|
SaS16S14S0S0A2M0A1S5aS4eS1eS2bS2cS1dA4S32A2S11G0S13S0S0S2P234A1S27Z4S2P235A1A2A4S12G0A1A3A3"). Proof. vmr. Qed.
Lemma fv4_bK : ltac2:(tb__ "0|0|
SaS16S29A1S2aS4eS1eS2bS2dS1dA4S4fS31A1A2S42A3"). Proof. vmr. Qed.
Lemma fv4_bG : ltac2:(tb__ "0|0|
SaS16S29A1S2aS4eS1eS2bS2cS1dA4S30S34S33A2A2S41A3"). Proof. vmr. Qed.
Lemma T_fv4k0_ta : ltac2:(tb__ "0|0|
SaS1aS5bS2bS1dS1eS21S2dS54SbS1cS20A1A2A6S3eA3"). Proof. vmr. Qed.
Lemma T_fv4k1_ap : ltac2:(tb__ "0|0|
SaS19S1aA1S59S3eS55UfU1dZ210A3A2S18S1aS38A2A3"). Proof. vmr. Qed.
Lemma T_fv4k_eq2 : ltac2:(tb__ "0|0|
SaS1aS63S11S3S7S1S64A1SbA2S12S3A1A3S38A2S25A3"). Proof. vmr. Qed.
Lemma fv4k_xff : ltac2:(tb__ "0|0|
SaSfS44S38S11S3S7S1S64A1SbA2S12S3A1A3A2S10A3"). Proof. vmr. Qed.
Lemma fv4k_land : ltac2:(tb__ "0|1|
SaSfS3bS25S23S3aS15S14S0S0A2M0S35S11G0S13S0S0SbS27Z4ScA2A4S12G0A1A3A3S49S15S29S42S36A3S40S50S51A1A8S10A3"). Proof. vmr. Qed.
Lemma fv4k_bd : ltac2:(tb__ "0|0|
SaS16S29A1S2aS3aS4fS51A1A2S40A3"). Proof. vmr. Qed.
Lemma fv4k_live : ltac2:(tb__ "0|0|
SaSfS45SeSdA1Z1ScS5S1bS38A1A1A4S10A3"). Proof. vmr. Qed.
Lemma T_fv4f0_ta : ltac2:(tb__ "0|0|
SaS1aS5bS2bS1dS1eS21S2eS54SbS1cS20A1A2A6S3cA3"). Proof. vmr. Qed.
Lemma T_fv4f_ap : ltac2:(tb__ "0|0|
SaS19S1aA1S59S3cS55UfU1dZ210A3A2S18S1aS1fA2A3"). Proof. vmr. Qed.
Lemma fv4f_ro0 : ltac2:(tb__ "0|1|
SaSfS46VXGL;S1fS22S1fA1S15S14S0S0A2M0S35S11G0S13S0S0SbS27Z4ScA2A4S12G0A1A3A3Z26Z27A6S10A3"). Proof. vmr. Qed.
Lemma fv4f_ro1 : ltac2:(tb__ "0|2|
SaSfS65VXGL;S5cS1fS22S1fA1M0S28Z26Z27A5G0S15S14S0S0A2M1S35S11G1S13S0S0SbS27Z4ScA2A4S12G1A1A3A3Z1cZ21A6S10A3"). Proof. vmr. Qed.
Lemma fv4f_land : ltac2:(tb__ "0|3|
SaSfS3bS5cS5cS1fS22S1fA1M0S28Z26Z27A5G0S28Z1cZ21A5S26S43S15S14S0S0A2M1S35S11G1S13S0S0SbS27Z4ScA2A4S12G1A1A3A3S47S5dS29U1S36A3M2G2S50S53A1A8S10A3"). Proof. vmr. Qed.
Lemma fv4f_bd : ltac2:(tb__ "0|0|
SaS16S29A1S2aS43S4fS53A1A2S5dS29U1S36A3A3"). Proof. vmr. Qed.
Lemma T_fv4g0_ta : ltac2:(tb__ "0|0|
SaS1aS5bS2bS1dS1eS21S2cS54SbS1cS20A1A2A6S3dA3"). Proof. vmr. Qed.
Lemma T_fv4g_ap : ltac2:(tb__ "0|0|
SaS19S1aA1S59S3dS55UfU1dZ210A3A2S18S1aS24A2A3"). Proof. vmr. Qed.
Lemma fv4g_land : ltac2:(tb__ "0|1|
SaSfS3bS24S23S39S15S14S0S0A2M0S35S11G0S13S0S0S2P234A1S27Z4S2P235A1A2A4S12G0A1A3A3S48S15S29S41S36A3S3fS50S51A1A8S10A3"). Proof. vmr. Qed.
Lemma fv4g_bd : ltac2:(tb__ "0|0|
SaS16S29A1S2aS39S4fS51A1A2S3fA3"). Proof. vmr. Qed.
Lemma fv4f_wp : bd_wpos brest_fv4 = true. Proof. vmr. Qed.
Lemma fv4_vlF : ltac2:(tb__ "0|0|
SaSfS4aS5S1bS20A1A1A1S10A3"). Proof. vmr. Qed.
Lemma fv4_meas : ltac2:(tb__ "0|1|
SaSfS17S17S17S17S17S4S58S3aS4dA2S4dA2S4S58S3aSdA2SdA2A2S4S58S39S4dA2S4dA2A2S4S58S39SdA2SdA2A2S8S9S1bS1dA1A1M0S4dA2A2S8G0SdA2A2S10A3"). Proof. vmr. Qed.
End G.
End Lib_handle_f_g5b.

