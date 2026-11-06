(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAT.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n9 Lib_handle_vn no nt nv.

(* [comment removed for export] *)
Module Lib_handle_vn_pf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "or"; "not"; "True"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "ax_setS"; "leafA"; "g8"; "la_state"; "has_facts"; "ax_base"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "valuation"; "SLit"; "sobj"; "ss_facts"; "SPUle"; "ss_next"; "SAlu"; "ss_objs"; "holds"; "sprop_eqb"; "SVar"; "cell"; "DUnknown"; "mkObj"; "rw"; "obj_range"; "obj_wf"; "soff"; "SPEq"; "sv_eqb"; "DZero"; "ob_base"; "ob_hi"; "ob_lo"; "sprop_below"; "swf"; "agree_below"; "mkCell"; "@Corelib.Init.Datatypes"; "cons"; "list"; "prod"; "bool"; "true"; "pair"; "nat"; "nil"; "Some"; "option"; "fst"; "None"; "snd"; "app"; "andb"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "apply_axforms"; "AXSelect"; "AXMerge"; "AXUnbase"; "AXSplit"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@Stdlib.ZArith.BinInt.Z"; "le"; "pow"; "lt"; "mul"; "add"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "smatchA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "ANone"; "NDA"; "PTrue"; "nd_below"; "TPA"; "frinA"; "tvinA"; "JA_pre"; "fbinA"; "ffinA"; "ND"; "emeasA"; "JA"; "JLA"; "ejcertA"; "frozen"; "nodeIA"; "ok_frameKA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "uval"; "bitem"; "bd_subst"; "bd_wpos"; "BXok_d"; "bd_below"; "bxt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_vn"; "fr_hvn"; "vF"; "E_vr"; "gF"; "s_v"; "ndp"; "E_B"; "E_C"; "cutsH"; "epi_state"; "E_A"; "R_v"; "optAh"; "sel_rel"; "L_mc1"; "Pre_mc"; "T_sm1"; "Xk_v"; "ndf"; "C_pro0"; "P_fail"; "P_ok"; "T_grown0"; "T_keep0"; "X_epi"; "nd0"; "nd_fail"; "nd_ok"; "slot_facts"; "vKg"; "C_ms1"; "E_A0"; "E_sm0"; "E_vr0"; "L_ms"; "Pre_hvn"; "Pre_ms"; "R_A"; "R_B"; "R_C"; "T_ms0"; "T_sm"; "X_epf0"; "X_epf1"; "X_epg"; "X_epk"; "X_hvn"; "X_rel"; "X_rlf0"; "X_rlf1"; "X_rlg"; "X_rlk"; "Y_epf0"; "Y_epf1"; "Y_epg"; "Y_epk"; "bd_hvn"; "dst_obj"; "exitsH"; "ndg"; "ndk"; "objs_sm1"; "s_A"; "s_B"; "s_C"; "src_obj"; "tv_hvn"; "xf_mc"; "C_body"; "C_epf0"; "C_epf1"; "C_epg"; "C_epk"; "C_ms"; "C_pro"; "E_ms"; "FUEL_hvn"; "L_sm"; "Pre_sm"; "R_ms"; "R_sm"; "T_A0"; "T_A1"; "T_B0"; "T_B1"; "T_C0"; "T_C1"; "T_fail0"; "T_grown"; "T_keep"; "T_ms1"; "cutpcs_hvn"; "objs_rel"; "s_ms"; "s_sm"; "sel_ms"; "sel_sm"; "tvG"; "vDg"; "xf_sd"; "xf_vr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nz.Lib_handle_vn_pf"; "P0_hvn"; "baseF"; "extraO"; "frameF"; "extraX"; "basez"; "xf_cf"; "E_mc2"; "cm1"; "in_callers"; "cm_dst"; "cm_src"; "vb184"; "E_mc3"; "PD_vr"; "base_facts"; "cells_rel"; "cm2"; "extra_tab"; "frame_facts"; "framez"; "xf_cm"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "import_postA"; "LQPA"; "import_subA"; "entails_frA"; "call_checkA"; "call_checkPA"; "J_ofPA"; "@Stdlib.Lists.List"; "existsb"; "In";
"nth_error"; "forallb"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "firstn"; "skipn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double"; "Pre_sd"; "vB"; "vL"; "P_none"; "P_num"; "Posts_sd"; "two26"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs"; "vNK"; "vND"; "vb"; "vNC"; "vAL"; "cb4"; "kb4"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "topG"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve"; "Pre_vr"; "z0"; "B32"; "P_grown"; "P_keep"; "P_fail"; "bdP"; "tv0"; "vW"; "nd0"; "tvP"; "vKn"; "two47"; "vK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "call_linkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "jnodeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "fs_frame_size"; "SHADOW_OFF"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double.ScanDoubleAddr"; "pow10_tab"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "rho_sub"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "T_ok"; "FBx"; "tvd"; "tvz"; "import_tv"; "remove_nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "pclMA"; "FFx"; "T_afterA3"; "PostsC"; "robjs_okF"; "xrs_inclb"; "xrs_okF"; "xrs_okL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nz.Lib_handle_vn_pf.Sum"; "Posts_hvn"; "JLh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase"; "reshape_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA"; "infrFF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS"; "xrs_checkL"; "robjs_checkF"; "shobj"; "frame_open_stateA"; "release_objs_ok"; "shadow_reopen_stateA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "AE_A"; "JL_pure"; "JL_stack_malloc"; "J_memcpy_pre"; "J_memset_pre"; "J_stack_malloc_pre"; "L_stack_malloc"; "Pre_stack_malloc"; "alloc_contractsA"; "alloc_contractsA_ex"; "alloc_lawsA"; "flagbyte_obj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nn.Lib_vec_reserve_pf"; "P0_vr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "T_afterA"; "ccount"; "is_shadowZ"; "call_checkTA"; "payA"; "robjs_okA"; "site_okA"; "xrs_okA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAT"; "robjs_checkP"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "ax_setX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_vn.HVNAddr"; "DW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3"; "import_okPA3"; "import_postA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR"; "robjs_okF"; "xrs_ok47"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR TobjJAS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAT.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAT.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Lib_scan_double.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n9.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n9.Lib_scan_double_ex.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_handle_vn.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nn.Lib_vec_reserve_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_vn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Import ScanDoubleAddr VRAddr RA.ReallocAddr HVNAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Definition P0_hvn (CST : list (Z * Z)) (FB : list (Z * Z)) (FF : list (Z * Z * Z)) (r : valuation) : Prop := ltac2:(tb__ "0|4|
S1S3bS1S46S45Q40M0S1eVr;PfA2A2M1R1A2S48R1S4aG1S45G0S1eVr;P12A2A2A2A2A2S12fVCST;Vr;VFB;VFF;R2A5F_;Fa;S1S13aVFF;S45G0S1eVr;PcA2A2Z518A3S1S13aVFF;S45G0S1eVr;P3aA2A2Z30A3S1S3S0S3bS45G0S1eVr;P38A2A2Z0M2A3A1S3S0S3bS45G0S1eVr;P36A2A2G2A3A1F_;S0S32S152G2Sf4S2eS2eS3bS3bA2M3S3bA2G3S36G3S3bA2VFF;A4A2U0A3A2A2A2A2").

Definition cm_dst (d : sv) : sobj := ltac2:(tb__ "0|1|
S1dVd;S103S101A1M0S16Se6G0S11ZcA1A3S33S1bA1S1cA5").
Definition cm_src : sobj := ltac2:(tb__ "0|0|
S1dS6cS11Z20A1S11Z2cA1S33S1bA1S1cA5").
Definition cm1 (A : axst) (d : sv) : axst := ltac2:(tb__ "0|0|
S8VA;S139S6VA;A1U1SdaVd;A1A3A2").
Definition cm2 (A : axst) : axst := ltac2:(tb__ "0|0|
S8VA;S139S6VA;A1U2SdbA3A2").
Definition xf_cm : list axform := ltac2:(tb__ "0|7|
S2cS3eS42UbM0Z68A2S2cS3eS42U5M1Nb8A2S2cS3eS40S2cS32U0S2cS32UcS2cS32U2S2cS32UdM2S2cS32UeS2cS32U3S2cS32U4S2cS32UfS2cS32G0S2cS32U10S2cS32U11S2cS32U12S2cS32G1S2cS32U6S2cS32U9S2cS32U13S2cS32UaS2cS32U7S2cS32U1M3S2cS32U8S33S32A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A1S2cS3eS41G3A1M4S2cS3eG4S2cS3eS41G1A1M5S2cS3eG5S2cS3eS41G2A1M6S2cS3eG6S33S3eA1A3A3A3A3A3A3A3A3A3").
Definition xf_cf : list axform := ltac2:(tb__ "0|6|
S2cS3eS42U1M0Z40A2S2cS3eS42U9M1Z68A2S2cS3eS42U2M2Nb8A2S2cS3eS40S2cS32G0S2cS32U0M3S2cS32UaS2cS32UbS2cS32U5M4S2cS32U6S2cS32UcS2cS32G1S2cS32UdS2cS32UeS2cS32UfS2cS32G2S2cS32U3S2cS32U7S2cS32U10S2cS32U8S2cS32U4S33S32A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A1S2cS3eS41G3A1S2cS3eS41G4A1M5S2cS3eG5S33S3eA1A3A3A3A3A3A3A3").
Lemma Y_epk_eq : ltac2:(tb__ "0|0|
S0S35S5A1S3fS98Sd6A2S34S5Sa2A2A3").     Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Y_epg_eq : ltac2:(tb__ "0|0|
S0S35S5A1S3fS97Sd6A2S34S5Sa1A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Y_epf0_eq : ltac2:(tb__ "0|0|
S0S35S5A1S3fS95Sd6A2S34S5S9fA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Y_epf1_eq : ltac2:(tb__ "0|0|
S0S35S5A1S3fS96Sd6A2S34S5Sa0A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma C_epk_eq : ltac2:(tb__ "0|0|
S0S5S74Sa2SffSfeA3Sb3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma C_epg_eq : ltac2:(tb__ "0|0|
S0S5S74Sa1ScdS88A3Sb2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma C_epf0_eq : ltac2:(tb__ "0|0|
S0S5S74S9fSffSfeA3Sb0A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma C_epf1_eq : ltac2:(tb__ "0|0|
S0S5S74Sa0SffSfeA3Sb1A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_A_eq : ltac2:(tb__ "0|0|
S0S35S5A1S3fS8aSceA2S34S5S75A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_B_eq : ltac2:(tb__ "0|0|
S0S35S5A1S3fS71S33S3eA1A2S34S5S71A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_C_eq : ltac2:(tb__ "0|0|
S0S35S5A1S3fS72S33S3eA1A2S34S5S72A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_A0_eq : ltac2:(tb__ "0|0|
S0S5S11aS13S6S75A1A1Se8Sa9Sf7SfaS75S90A5A2SbcA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_A1_eq : ltac2:(tb__ "0|0|
S0S5S11aS13S6S75A1A1Se8Sa9Sf7SfbS75S90A5A2SbdA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_B0_eq : ltac2:(tb__ "0|0|
S0S5S11aS13S6S71A1A1Se8SaaSf7SfaS71S91A5A2SbeA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_B1_eq : ltac2:(tb__ "0|0|
S0S5S11aS13S6S71A1A1Se8SaaSf7SfbS71S91A5A2SbfA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_C0_eq : ltac2:(tb__ "0|0|
S0S5S11aS13S6S72A1A1Se8SabSf7SfaS72S92A5A2Sc0A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_C1_eq : ltac2:(tb__ "0|0|
S0S5S11aS13S6S72A1A1Se8SabSf7SfbS72S92A5A2Sc1A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition E_mc1 (E0 : axst) : axst := ltac2:(tb__ "0|0|
S77S3fVE0;SaeA2A1").
Definition E_mc2 (E1 : axst) (d : sv) : axst := ltac2:(tb__ "0|0|
S8VE1;S139S6VE1;A1U4Sa4Vd;A1A3A2").
Definition E_mc3 (E2 : axst) : axst := ltac2:(tb__ "0|0|
S8VE2;S139S6VE2;A1UcSacA3A2").

Definition cells_rel : list cell := Eval vm_compute in ob_cells sh_rel.
Lemma X_rel_objs : ltac2:(tb__ "0|0|
S0S2dS12A1S17S6S9aA1A1S39S12Sc7S2cS12S13dS6eZ0Z8Se0S24A5S33S12A1A3A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma C_ms1_eq : ltac2:(tb__ "0|0|
S0S35S5A1S3fSb4S2cS3eS43U1S11Z20A1A2S2cS3eS43U2S11Z2cA1A2S33S3eA1A3A3A2S34S5S89A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma C_ms1_o2 : ltac2:(tb__ "0|0|
S0S35S12A1Sf1S12S17S6S89A1A1U2A3S34S12S1dS6cS11Z20A1S11Z2cA1S33S1bA1S1cA5A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_ms0_eq : ltac2:(tb__ "0|0|
S0S5S151S8fSb6Sc8SbaS8dA5S93A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_ms0_o1 : ltac2:(tb__ "0|0|
S0S35S12A1Sf1S12S17S6S93A1A1U1A3S34S12S1dS16Se6S6cS11Z20A1A3S11Z0A1S11ZcA1S33S1bA1S24A5A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma C_body_eq : ltac2:(tb__ "0|1|
S0S35S5A1S3fSc5S2cS3eS40ScaA1S2cS3eS41U1A1M0S2cS3eG0S33S3eA1A3A3A3A2S34S5SafA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_sm_eq : ltac2:(tb__ "0|1|
S0S5S151S148S141Z0M0A2S8bSc9SbbS147S141G0A2A5S94A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_sm1_eq : ltac2:(tb__ "0|0|
S0S35S5A1S3fS94S2cS3eS40ScbA1S33S3eA1A3A2S34S5S7bA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_sm1_objs : ltac2:(tb__ "0|1|
S0S2dS12A1S17S6S7bA1A1S39S12Sa8S2cS12S14cS1aP78A1S2cS1bS2bS11Z0A1Z1M0S11G0A1A3S33S1bA1A3A2S33S12A1A3A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_sm1_X : ltac2:(tb__ "0|1|
S0S2dS2eSeSeA2M0A1S7S7bA1S39G0S99SffSfeA2S2cG0S31SeSeS1aP6eA1S11S122Z0A1A1A4S33G0A1A3A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma C_pro0_eq : ltac2:(tb__ "0|0|
S0S5S13eS7bSa8S99SffSfeA2P6eS122Z0A1A5S7eA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma C_pro_eq : ltac2:(tb__ "0|0|
S0S5S15dS7eS2cS2eSeSeA2S31SeSeS1aP6eA1S11Z0A1A4S7S7eA1A3A2Sb5A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_vr_eq : ltac2:(tb__ "0|0|
S0S35S5A1S3fS8cScfA2S34S5S6dA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition PD_vr : list (axst * ndesc) := ltac2:(tb__ "0|2|
S2cS2eS5S50A2M0S31S5S50S10eS113A4S2cG0S31S5S50S10fS5bS111S33S2eS2eSeS3bA2SeA2A1M1S33S65A1A3A4S2cG0S31S5S50S10dS5bS114G1S110S112S115A2A3A4S33G0A1A3A3A3").
Lemma T_keep0_eq : ltac2:(tb__ "0|0|
S0S5S131S10aS6dS6fS76S10eS7cA6S82A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_fail0_eq : ltac2:(tb__ "0|0|
S0S5S131S10aS6dS6fS76S10fS7cA6Sc2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_grown0_eq : ltac2:(tb__ "0|0|
S0S5S131S10aS6dS6fS76S10dS7cA6S81A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_keep_eq : ltac2:(tb__ "0|0|
S0S5S15cS82S39SfS39SfS87SfeA1S2cSfS14S11S121A1SffA2S33SfA1A3A3S13S6S82A1A1A3A2Sc4A3"). Proof. reflexivity. Qed.
Lemma T_grown_eq : ltac2:(tb__ "0|0|
S0S5S15cS81S39SfS87S88A1S13S6S81A1A1A3A2Sc3A3"). Proof. reflexivity. Qed.
Lemma imp_keep_tv : ltac2:(tb__ "0|0|
S0S2dS2eSeSeA2A1S12dSeaS6fS10aS10eS6dA4S111A2SadSffSfeA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_keep_bd : ltac2:(tb__ "0|0|
S0S2dS65A1S66SeaS6fS10aS10eS6dA4S110S112S117A2A2Sa3S101SfeA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_fail_tv : ltac2:(tb__ "0|0|
S0S2dS2eSeSeA2A1S12dSeaS6fS10aS10fS6dA4S111A2SadSffSfeA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_grown_tv : ltac2:(tb__ "0|0|
S0S2dS2eSeSeA2A1S12dSeaS6fS10aS10dS6dA4S114A2SccA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_grown_bd : ltac2:(tb__ "0|0|
S0S2dS65A1S66SeaS6fS10aS10dS6dA4S110S112S115A2A2Sa3S101S88A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma X_rlk_eq : ltac2:(tb__ "0|1|
S0S35S5A1S3fS9eS2cS3eS40S78A1S33S3eA1A3A2M0S34S5S77G0A1A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma X_rlg_eq : ltac2:(tb__ "0|1|
S0S35S5A1S3fS9dS2cS3eS40S78A1S33S3eA1A3A2M0S34S5S77G0A1A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma X_rlf0_eq : ltac2:(tb__ "0|1|
S0S35S5A1S3fS9bS2cS3eS40S78A1S33S3eA1A3A2M0S34S5S77G0A1A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma X_rlf1_eq : ltac2:(tb__ "0|1|
S0S35S5A1S3fS9cS2cS3eS40S78A1S33S3eA1A3A2M0S34S5S77G0A1A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition base_facts : list sprop := ltac2:(tb__ "0|4|
S2cSfS14S1aPaA1M0S11S116A1M1A2S2cSfS14S16Se6S1aP1eA1M2S11S15eA1A3G0A2S2cSfS14S11S121A1M3S100A2S2cSfS14S16Se6S100S11Z518A1A3G2A2S2cSfS14S100G1A2S2cSfS14G3S102A2S2cSfS14S16Se6S102S11Z30A1A3G2A2S2cSfS14S102G1A2S2cSfS14Sf9S11SfdA1A2S2cSfS14Sf8G1A2S2cSfS14S11Z7fff7f800000A1G2A2S2cSfS14G2S11Z7fffff800000A1A2S33SfA1A3A3A3A3A3A3A3A3A3A3A3A3").
Definition baseF (F : list sprop) : bool := ltac2:(tb__ "0|0|
Sf2SfSfSefSfS19R1A1VF;A3Lp;SdfA3").

Definition frame_facts : list sprop := ltac2:(tb__ "0|2|
S2cSfS22SaS6eA1S6cA2S2cSfS14S1aS6eA1S11S4bS47Z2M0Z3dA2Z1A2A1A2S2cSfS14S11S121A1S6cA2S2cSfS14S16Se6S6cS11Z40A1A3S1aP1eA1M1A2S2cSfS14S6cS11S47G0Z2fA2A1A2S2cSfS14G1S11Z7fffff800000A1A2S33SfA1A3A3A3A3A3A3").
Definition frameF (F : list sprop) : bool := ltac2:(tb__ "0|0|
Sf2SfSfSefSfS19R1A1VF;A3Lp;Se3A3").

Record basez (rho : valuation) : Prop := BZ {
  bz_sp : aceil + DW <= uval rho (SVar 10) <= 2 ^ 47;
  bz_b : IMG_HI <= uval rho vb /\ uval rho vb + 1304 <= bv_unsigned (rw rho V_TOP);
  bz_al : IMG_HI <= uval rho vAL /\ uval rho vAL + 48 <= bv_unsigned (rw rho V_TOP);
  bz_L : uval rho vL <= 2 ^ 26;
  bz_B : uval rho vB <= 2 ^ 47;
  bz_top : bv_unsigned (rw rho V_TOP) + DW <= uval rho (SVar 10) /\ 140735332483072 <= bv_unsigned (rw rho V_TOP) <= 140737479966720 }.
Record framez (rho : valuation) : Prop := FZ {
  fz_g : uval rho (SVar gF) = uval rho vF / 8;
  fz_g8 : uval rho vF mod 8 = 0;
  fz_f : IMG_HI <= uval rho vF /\ uval rho vF + 64 <= bv_unsigned (rw rho V_TOP) /\ bv_unsigned (rw rho V_TOP) <= 140737479966720 }.

Lemma uval_add_litZ : ltac2:(tb__ "0|0|
S10SeS3bS46Z0R1A2S48S4aS64R4R3A2R2A2S47Z2Z40A2A2S0S3bS64R5S16Se6R4S11R3A1A3A2S4aS64R5R4A2R3A2A3F_;F_;Fk;Fa;Frho;").
Proof. intros rho a k Hk H. pose proof (uval_range rho a). rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia. reflexivity. Qed.

Lemma basez_of : ltac2:(tb__ "0|0|
S10S2dSfA1Sf3SfS18R2A1R1A3S0S2fSd1R2A1S30A3Sd5R4A1F_;F_;FF;Frho;").
Proof.
  intros rho F HF HB. unfold baseF in HB.
  assert (G : forall p, In p base_facts -> holds rho p).
  { intros p Hp. apply (holds_mem rho F p HF). exact (proj1 (forallb_forall _ _) HB p Hp). }
  cbn [base_facts] in G.
  pose proof (G _ ltac:(left; reflexivity)) as F1. pose proof (G _ ltac:(do 1 right; left; reflexivity)) as F2.
  pose proof (G _ ltac:(do 2 right; left; reflexivity)) as F3. pose proof (G _ ltac:(do 3 right; left; reflexivity)) as F4.
  pose proof (G _ ltac:(do 4 right; left; reflexivity)) as F5. pose proof (G _ ltac:(do 5 right; left; reflexivity)) as F6.
  pose proof (G _ ltac:(do 6 right; left; reflexivity)) as F7. pose proof (G _ ltac:(do 7 right; left; reflexivity)) as F8.
  pose proof (G _ ltac:(do 8 right; left; reflexivity)) as F9. pose proof (G _ ltac:(do 9 right; left; reflexivity)) as F10.
  pose proof (G _ ltac:(do 10 right; left; reflexivity)) as F11. pose proof (G _ ltac:(do 11 right; left; reflexivity)) as F12.
  rewrite h_ule in F1, F2, F3, F4, F5, F6, F7, F8, F9, F10, F11, F12.
  unfold two47, two26, RA.two47 in *. unfold DW, IMG_HI in *.
  rewrite !uval_lit in * by lia. pose proof (uval_range rho (SVar 30)) as R30. rewrite uval_add_litZ in F2 by lia.
  change (uval rho (SVar 30)) with (bv_unsigned (rw rho V_TOP)) in *.
  pose proof (uval_range rho vb) as Rb. pose proof (uval_range rho vAL) as Ral.
  rewrite uval_add_litZ in F4 by lia. rewrite uval_add_litZ in F7 by lia.
  constructor; rewrite ?aceil_val; unfold DW, IMG_HI in *; lia.
Qed.

Lemma framez_of : ltac2:(tb__ "0|0|
S10S2dSfA1Sf3SfS18R2A1R1A3S0S2fSd3R2A1S30A3Se4R4A1F_;F_;FF;Frho;").
Proof.
  intros rho F HF HB. unfold frameF in HB.
  assert (G : forall p, In p frame_facts -> holds rho p).
  { intros p Hp. apply (holds_mem rho F p HF). exact (proj1 (forallb_forall _ _) HB p Hp). }
  cbn [frame_facts] in G.
  pose proof (G _ ltac:(left; reflexivity)) as F1. pose proof (G _ ltac:(do 1 right; left; reflexivity)) as F2.
  pose proof (G _ ltac:(do 2 right; left; reflexivity)) as F3. pose proof (G _ ltac:(do 3 right; left; reflexivity)) as F4.
  pose proof (G _ ltac:(do 4 right; left; reflexivity)) as F5. pose proof (G _ ltac:(do 5 right; left; reflexivity)) as F6.
  rewrite h_ule in F2, F3, F4, F5, F6. cbn [holds] in F1. change (uval rho (SVar 30)) with (bv_unsigned (rw rho V_TOP)) in *. unfold IMG_HI in *.
  rewrite !uval_lit in * by lia. pose proof (uval_range rho vF) as Rf. pose proof (uval_range rho (SVar gF)) as Rg.
  rewrite uval_add_litZ in F4 by lia.
  assert (E8 : uval rho (g8 gF) = (uval rho (SVar gF) * 8) mod 2 ^ 64).
  { unfold uval, g8. rewrite U_sll_lit. change (2 ^ (3 mod 64)) with 8. reflexivity. }
  apply (f_equal bv_unsigned) in F1. change (uval rho (g8 gF) = uval rho vF) in F1. rewrite E8 in F1.
  rewrite Z.mod_small in F1 by lia.
  constructor; [rewrite <- F1; rewrite Z.div_mul by lia; reflexivity | rewrite <- F1; apply Z_mod_mult | unfold IMG_HI; lia].
Qed.

Definition vb184 : sv := SAlu ALU_ADD vb (SLit 184).
Definition extra_tab : list (sv * sv * sv) := ltac2:(tb__ "0|3|
S2cS2eS2eSeSeA2M0SeA2M1S31G0SeS31SeSeS100S11Z0A1M2A4S11Z8A1A4S2cG1S31G0SeS31SeSeS100S11Z60A1A4S11Z78A1A4S2cG1S31G0SeS31SeSeS100S11Zb8A1A4S11Zd8A1A4S2cG1S31G0SeS31SeSeSdcG2A4S11Z20A1A4S2cG1S31G0SeS31SeSeS102G2A4S11Z30A1A4S2cG1S31G0SeS31SeSeSf8G2A4Sf9A4S33G1A1A3A3A3A3A3A3").
Definition extraO (o : sobj) : bool := ltac2:(tb__ "0|3|
SefS2eS2eSeSeA2M0SeA2M1G1S3aS3aS23S25Vo;A1S36SeSeS36G0SeR1A3M2A3A2S23S27Vo;A1S38SeSeG2A3A2A2S23S26Vo;A1S38G0SeR1A3A2A2Lt;Se2A3").
Definition extraX_tab : list (sv * sv) := ltac2:(tb__ "0|1|
S2cS2eSeSeA2M0S31SeSeS100S11Z518A1A4S2cG0S31SeSeS102S11Z30A1A4S2cG0S31SeSeSf8Sf9A4S2cG0S31SeSeSdcS11Z20A1A4S2cG0S31SeSeS11S125A1S11Zb8A1A4S33G0A1A3A3A3A3A3").
Definition extraX (r : sv * sv) : bool := existsb (xr_eqb r) extraX_tab.
Definition in_callers (rho : valuation) (a : Z) : Prop := ltac2:(tb__ "0|3|
S2S1S46S64Vrho;S100A2M0Va;A2S48Va;S4aG0Z518A2A2A2S2S1S46S64Vrho;S102A2M1Va;A2S48Va;S4aG1Z30A2A2A2S2S1S46S64Vrho;Sf8A2M2Va;A2S48Va;S4aG2S64Vrho;Sf9A2A2A2A2S1S46S125Va;A2S48Va;S4aS125Zb8A2A2A2A2A2A2").

Lemma obj_rangeZ : ltac2:(tb__ "0|2|
S10S12S3bS3bS3bS1S46S36S3bS3bS1fR5R4A2M0A3R3A2S48R3S38S3bS3bG0A3A2A2S0S3bS21R6S27R5A1A2R3A3S0S3bS21R7S26R6A1A2R3A3S1S46S4aS64R8S25R7A1A2M1R5A2R6A2S48R6S4aG1R4A2A2A2F_;F_;F_;Fhi;Flo;Fa;Fo;Frho;").
Proof. intros rho o a lo hi Hr <- <-. unfold obj_range, obj_lo_of, obj_hi_of in Hr. unfold uval. exact Hr. Qed.

Lemma extraO_sound : ltac2:(tb__ "0|1|
S10S12S3bSd5R3A1S0S2fSd2R3A1S30A3S1S46S36S3bS3bS1fR5R4A2M0A3R3A2S48R3S38S3bS3bG0A3A2A2Sd9R6R4A2F_;F_;F_;Fa;Fo;Frho;").
Proof.
  intros rho o a [Bsp Bb Bal BL BB Btop] HE Hr. rewrite aceil_val in *. unfold IMG_HI in *.
  assert (E184 : uval rho vb184 = uval rho vb + 184) by (unfold vb184; apply uval_add_litZ; lia).
  unfold extraO in HE. apply existsb_exists in HE as (t & Hin & Heq).
  apply andb_prop in Heq as [Heq Hh]. apply andb_prop in Heq as [Hb Hl]. apply sv_eqb_sound in Hb. apply sv_eqb_sound in Hl. apply sv_eqb_sound in Hh.
  unfold in_callers. cbn [extra_tab In] in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn [fst snd] in Hb, Hl, Hh;
    (eapply obj_rangeZ in Hr; [| rewrite Hl; first [apply soff_lit_small; lia | apply soff_smallu; lia] | rewrite Hh; first [apply soff_lit_small; lia | apply soff_smallu; lia]]);
    rewrite Hb in Hr; rewrite ?E184 in Hr; lia.
Qed.

Lemma extraX_sound : ltac2:(tb__ "0|1|
S10S2eSeSeA2S3bSd5R3A1S0S2fSd4R3A1S30A3S1S46S64R5S36SeSeR4A3A2M0R3A2S48R3S4aG0S64R5S38SeSeR4A3A2A2A2A2Sd9R6R4A2F_;F_;F_;Fa;Fr;Frho;").
Proof.
  intros rho r a [Bsp Bb Bal BL BB Btop] HE Hr. rewrite aceil_val in *. unfold IMG_HI in *.
  assert (E184 : uval rho vb184 = uval rho vb + 184) by (unfold vb184; apply uval_add_litZ; lia).
  unfold extraX in HE. apply existsb_exists in HE as (t & Hin & Heq). apply xr_eqb_sound in Heq. subst t.
  unfold in_callers. cbn [extraX_tab In] in Hin. unfold pow10_tab in *.
  destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; destruct r as [b l]; injection E as <- <-; cbn [fst snd] in Hr;
    rewrite ?uval_lit in Hr by lia; rewrite ?E184 in Hr; lia.
Qed.

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
S105S10S2dS44Q40A1A1S108OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
S14bS3dVAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S3bS14dVCST;R1A2S1S46Z0R2A2S48R2S121A2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S3bS14dVXGL;R1A2S1S46Z0R2A2S48R2S121A2A2F_;Fa;").

Hypothesis HXpow : ltac2:(tb__ "0|0|
S3bS1S46S125R1A2S48R1S4aS125Zb8A2A2A2S14dVXGL;R2A2F_;Fa;").
Hypothesis LFLAG : law_flag_stmt AInv.
Hypothesis LFSH : law_fshadow_stmt AInv.
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S2dS2eS2eS3bS3bA2S3bA2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 5 BX.
Let HNP : NP_okA NF := NP_okA_intro NF eq_refl.
Variable rho0 : valuation.
Let HTOP : InitState.segs_top segs <= IMG_HI := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nn.Lib_arena_alloc.HTOP_ok.

Definition JLh (nd : ndesc) : jpostA := ltac2:(tb__ "0|0|
S5eVAInv;VCST;VXGL;VKc;Sd0VCST;VFB;VFF;A3VFB;VFF;VBX;S53Vnd;Aa").
Definition Posts_hvn : list (axst * jpostA) := ltac2:(tb__ "0|1|
S2cS2eS5Se7A2M0S31S5Se7S80S138S86A1A4S2cG0S31S5Se7S7fS138S85A1A4S33G0A1A3A3").

Definition PD_hvn : list (axst * ndesc) := ltac2:(tb__ "0|1|
S2cS2eS5S50A2M0S31S5S50S80S86A4S2cG0S31S5S50S7fS85A4S33G0A1A3A3").

Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S5dVAInv;VCST;VXGL;S63VKc;Vrho0;Sd0VCST;VFB;VFF;A3VFB;VFF;VBX;S53Vnd;Ac").
Let nI : ltac2:(tb__ "0|0|
S2eS5S50A2S11bFn;") := ltac2:(tb__ "0|0|
S61VAInv;VCST;VXGL;S63VKc;Vrho0;Sd0VCST;VFB;VFF;A3VFB;VFF;VBX;S53Ab").
Let Q (tp0 : list word) : assn := ltac2:(tb__ "0|0|
Se9S3dS63Vrho0;Vtp0;S137A5").

Lemma P0_now : ltac2:(tb__ "0|3|
S10S118S63Vrho0;R1A3Sd0VCST;VFB;VFF;Vrho0;A4S1S3bS1S46S64R4Sf8A2M0R1A2S48R1S4aG0S64R4Sf9A2A2A2A2S12fVCST;Vrho0;VFB;VFF;R2A5F_;Fa;S1S13aVFF;S64R3S100A2Z518A3S1S13aVFF;S64R3S102A2Z30A3S1S3S0S3bS64R3SfeA2Z0M1A3A1S3S0S3bS64R4SffA2G1A3A1F_;S0S32S152G1Sf4S2eS2eS3bS3bA2M2S3bA2G2S36G2S3bA2VFF;A4A2U0A3A2A2A2A2F_;F_;Frho;").
Proof.
  intros rho Hav (A & B & C & D & E). unfold uval, vL, vB, vb, vAL, vNK, vND. cbn [eval].
  rewrite <- (proj1 Hav 12%positive eq_refl), <- (proj1 Hav 15%positive eq_refl), <- (proj1 Hav 18%positive eq_refl),
          <- (proj1 Hav 58%positive eq_refl), <- (proj1 Hav 54%positive eq_refl), <- (proj1 Hav 56%positive eq_refl).
  repeat (split; [assumption|]). assumption.
Qed.

Lemma in_callers_ok : ltac2:(tb__ "0|0|
S10S3bS2dS2eSeSeA2A1S2dS2eS2eSeS3bA2SeA2A1S118S63Vrho0;R4A3Sd0VCST;VFB;VFF;Vrho0;A4Sd9R6R5A2S2S12fVCST;Vrho0;S12aVFB;R7R5A3S130VFF;R7R4A3R6A5S14dVXGL;R6A2A2F_;F_;F_;Ffrs;Fkept;Fa;Frho;").
Proof.
  intros rho a kept frs Hav HP0 H. destruct (P0_now rho Hav HP0) as (HT & Hb & Hal & _ & _).
  destruct H as [H|[H|[H|H]]].
  - destruct Hb as (f & sz & fl & Hin & H1 & H2). left. right; right; right. exists f, sz, fl. split; [apply In_FFx; left; exact Hin | lia].
  - destruct Hal as (f & sz & fl & Hin & H1 & H2). left. right; right; right. exists f, sz, fl. split; [apply In_FFx; left; exact Hin | lia].
  - left. destruct (HT a H) as [P|[P|[(b0 & n0 & Hin & Hr)|(f & s0 & fl & Hin & Hr)]]]; [left; exact P | right; left; exact P | |].
    + right; right; left. exists b0, n0. split; [apply In_FBx; left; exact Hin | exact Hr].
    + right; right; right. exists f, s0, fl. split; [apply In_FFx; left; exact Hin | exact Hr].
  - right. exact (HXpow a H).
Qed.

Lemma extraO_client : ltac2:(tb__ "0|1|
S10S12S3bS2dS2eSeSeA2A1S2dS2eS2eSeS3bA2SeA2A1Sd5R5A1S118S63Vrho0;R6A3Sd0VCST;VFB;VFF;Vrho0;A4S0S2fSd2R7A1S30A3S1S46S36S3bS3bS1fR9R8A2M0A3R7A2S48R7S38S3bS3bG0A3A2A2S12fVCST;Vrho0;S12aVFB;RaR7A3S130VFF;RaR6A3R8A5F_;F_;F_;F_;F_;Ffrs;Fkept;Fa;Fo;Frho;").
Proof.
  intros rho o a kept frs BZ Hav HP0 HE Hr. destruct (P0_now rho Hav HP0) as (HT & Hb & Hal & _ & _).
  pose proof BZ as [Bsp Bb Bal BL BB Btop]. rewrite aceil_val in *. unfold IMG_HI in *.
  assert (E184 : uval rho vb184 = uval rho vb + 184) by (unfold vb184; apply uval_add_litZ; lia).
  unfold extraO in HE. apply existsb_exists in HE as (t & Hin & Heq).
  apply andb_prop in Heq as [Heq Hh]. apply andb_prop in Heq as [Hb0 Hl]. apply sv_eqb_sound in Hb0. apply sv_eqb_sound in Hl. apply sv_eqb_sound in Hh.
  cbn [extra_tab In] in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn [fst snd] in Hb0, Hl, Hh;
    (eapply obj_rangeZ in Hr; [| rewrite Hl; first [apply soff_lit_small; lia | apply soff_smallu; lia] | rewrite Hh; first [apply soff_lit_small; lia | apply soff_smallu; lia]]);
    rewrite Hb0 in Hr; rewrite ?E184 in Hr.
  1-4: destruct Hb as (f & sz & fl & Hin & H1 & H2); right; right; right; exists f, sz, fl; split; [apply In_FFx; left; exact Hin | lia].
  - destruct Hal as (f & sz & fl & Hin & H1 & H2). right; right; right. exists f, sz, fl. split; [apply In_FFx; left; exact Hin | lia].
  - destruct (HT a ltac:(lia)) as [P|[P|[(b0 & n0 & Hin & Hr')|(f & s0 & fl & Hin & Hr')]]]; [left; exact P | right; left; exact P | |].
    + right; right; left. exists b0, n0. split; [apply In_FBx; left; exact Hin | exact Hr'].
    + right; right; right. exists f, s0, fl. split; [apply In_FFx; left; exact Hin | exact Hr'].
Qed.

Lemma siteP : ltac2:(tb__ "0|0|
S105S10S2dSfA1S2dS2eSeSeA2A1S2dS2eS2eSeS3bA2SeA2A1S35S32A1S2dS12A1S10S2dS44Q40A1A1S108VAInv;RaR3R2R1A4Sf3SfS18RaA1R9A3S0S2fSd1RaA1S30A3S118S63Vrho0;RcA3Sd0VCST;VFB;VFF;Vrho0;A4S55Vrho0;RfA2S129RfS107S106R10A1A1A2S59VFB;R11A2S5aVFF;R12A2S57VFB;R13R12R10A4S12bR13R11A2S12cR14R12A2S56VFF;R16R15R12A4S0S2fS159R15R14R13R12Sd2R11A6S30A3S156VCST;R18S37S3bA1R17R12A5F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FR;Fskip;Ffr;Ftv;Ffacts;Frho;FAi;").
Proof.
  intros Ai rho facts tv fr skip R rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HBf HFF HN HD HZ HFR Hchk.
  eapply (robjsP_okA segs AInv CST ALA rho0 FB FF Ai rho facts tv fr skip extraO R rho1 tp1 md1 HM HF HT HTK HBf HFF HN HD HZ HFR Hchk).
  intros o a Ho HE Hr. exact (extraO_client rho o a _ _ (basez_of rho facts HF HB) Hav HP0 HE Hr).
Qed.
Lemma siteF : ltac2:(tb__ "0|0|
S105S10S2dSfA1S2dS2eSeSeA2A1S2dS2eS2eSeS3bA2SeA2A1S2dS12A1S10S2dS44Q40A1A1S108VAInv;R9R3R2R1A4Sf3SfS18R9A1R8A3S0S2fSd1R9A1S30A3S118S63Vrho0;RbA3Sd0VCST;VFB;VFF;Vrho0;A4S55Vrho0;ReA2S129ReS107S106RfA1A1A2S57VFB;R10RfRdA4S12bR10ReA2S12cR11RfA2S56VFF;R13R12RfA4S0S2fS13cR12R11R10S37S32A1Sd2RfA6S30A3S162VCST;Vrho0;VFB;VFF;R14R12R11R10A8F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FR;Ffr;Ftv;Ffacts;Frho;FAi;").
Proof.
  intros Ai rho facts tv fr R rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HN HD HZ HFR Hchk.
  eapply (robjsP_okF segs AInv CST ALA rho0 FB FF Ai rho facts tv fr extraO R rho1 tp1 md1 HM HF HT HTK HN HD HZ HFR Hchk).
  intros o a Ho HE Hr. exact (extraO_client rho o a _ _ (basez_of rho facts HF HB) Hav HP0 HE Hr).
Qed.
Lemma siteH : ltac2:(tb__ "0|1|
S105S10S2dSfA1S2dS2eSeSeA2A1S2dS2eS2eSeS3bA2SeA2A1S2dS12A1S10S2dS44Q40A1A1S108VAInv;R9R3R2R1A4Sf3SfS18R9A1R8A3S0S2fSd1R9A1S30A3S118S63Vrho0;RbA3Sd0VCST;VFB;VFF;Vrho0;A4S55Vrho0;ReA2S129ReS107S106RfA1A1A2S57VFB;R10RfRdA4S12bR10ReA2S12cR11RfA2S56VFF;R13R12RfA4S0S2fS13cR12R11R10S37S32A1Sd2RfA6S30A3S12S3bSf0S12R2R12A3S1S46S36S3bS3bS1fR17R3A2M0A3R2A2S48R2S38S3bS3bG0A3A2A2S2S12fVCST;Vrho0;S12aVFB;R18R16A3S130VFF;R18R15A3R3A5S2S1S46Z0R3A2S48R3S121A2A2S153R3A1A2A2F_;F_;Fa;Fo;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FR;Ffr;Ftv;Ffacts;Frho;FAi;").
Proof.
  intros Ai rho facts tv fr R rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HN HD HZ HFR Hchk.
  eapply (robjsP_hse segs AInv CST ALA rho0 FB FF Ai rho facts tv fr extraO R rho1 tp1 md1 HM HF HT HTK HN HD HZ HFR Hchk).
  intros o a Ho HE Hr. exact (extraO_client rho o a _ _ (basez_of rho facts HF HB) Hav HP0 HE Hr).
Qed.
Lemma siteX : ltac2:(tb__ "0|4|
S105S10S2dSfA1S2dS2eSeSeA2A1M0S2dS2eS2eSeS3bA2SeA2M1A1M2S35S32A1M3S2dS12A1G0S10S2dS44Q40A1A1S108VAInv;RbR3R2R1A4Sf3SfS18RbA1RaA3S0S2fSd1RbA1S30A3S118S63Vrho0;RdA3Sd0VCST;VFB;VFF;Vrho0;A4S55Vrho0;R10A2S129R10S107S106R11A1A1A2S59VFB;R12A2S5aVFF;R13A2S57VFB;R14R13R11A4S12bR14R12A2S12cR15R13A2S56VFF;R17R16R13A4S0S2fS13bVXGL;R16R15R14R13R12Sd4R11A8S30A3S1S136VCST;VXGL;Vrho0;VFB;VFF;R18R16G3G2Lskip;R14S32S12eG1R1R16A3Li;R15X35x2R12A9S1S158VCST;VXGL;R19S37S3bA1R18R12A6S163R18R12A2A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FX;Fobjs;Fskip;Ffr;Ftv;Ffacts;Frho;FAi;").
Proof.
  intros Ai rho facts tv fr skip objs X rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HBf HFF HN HD HZ HFR Hchk.
  assert (HEX : forall r a, In r X -> extraX r = true -> uval rho (fst r) <= a < uval rho (fst r) + uval rho (snd r) ->
            pclMA CST rho0 (FBx FB rho tv) (FFx FF rho (match skip with Some i => remove_nth i fr | None => fr end)) a \/ RtCells.in_rangesZ XGL a).
  { intros r a Hr HE Ha. apply (in_callers_ok rho a _ _ Hav HP0). exact (extraX_sound rho r a (basez_of rho facts HF HB) HE Ha). }
  split; [exact (xrs_checkL_sound segs AInv CST XGL ALA rho0 FB FF Ai rho facts tv fr skip objs extraX X rho1 tp1 md1 HM HF (T_ok_T0 rho0 _ Ai HT HTK) HN HD HZ HFR Hchk HEX)|].
  exact (xrs_checkL_okA segs AInv CST XGL ALA HCST HXGL rho0 FB FF Ai rho facts tv fr skip objs extraX X rho1 tp1 md1 HM HF HT HTK HBf HFF HN HD HZ HFR Hchk HEX).
Qed.

Lemma slot_holds : ltac2:(tb__ "0|1|
S10S2dSfA1SeSf3SfS18R3A1R2A3S0S2fSefSfS19S14S16Se6S101S11Z3A1A3R2A2A1R3A3S30A3S0S2fSefSfS19S14R3S11S10cA1M0A2A1R4A3S30A3S0S2fSefSfS19S14S101SfeA2A1R5A3S30A3S0S2fSefSfS19S14SfeG0A2A1R6A3S30A3S0S2fSefSfS19S14S104R6A1G0A2A1R7A3S30A3Sf3SfS18R9A1S87R7A1A3F_;F_;F_;F_;F_;F_;Fk;FF;Frho;").
Proof.
  intros rho F k HF H1 H2 H3 H4 H5.
  pose proof (holds_mem _ _ _ HF H1) as F1. pose proof (holds_mem _ _ _ HF H2) as F2. pose proof (holds_mem _ _ _ HF H3) as F3.
  pose proof (holds_mem _ _ _ HF H4) as F4. pose proof (holds_mem _ _ _ HF H5) as F5.
  rewrite h_ule in F1, F2, F3, F4, F5. unfold B32 in *. rewrite uval_lit in F2 by lia. rewrite uval_lit in F4 by lia. rewrite uval_lit in F5 by lia.
  pose proof (uval_range rho vNC) as RC. pose proof (uval_range rho k) as Rk. pose proof (uval_range rho vNK) as RK.
  rewrite uval_add_litZ in F1 by lia.
  assert (E4k : uval rho (kb4 k) = 4 * uval rho k) by (unfold kb4; apply uval_mul_lit; lia). rewrite E4k in F5.
  assert (E4c : uval rho (cb4 vNC) = 4 * uval rho vNC) by (unfold cb4; rewrite uval_mul_comm; apply uval_mul_lit; lia).
  unfold slot_facts. change (SMd M_MUL vNC (SLit 4)) with (cb4 vNC).
  constructor; [|constructor; [|constructor; [|constructor]]]; rewrite h_ule.
  - rewrite uval_add_litZ by (rewrite ?E4c; lia). rewrite E4c, E4k. lia.
  - rewrite E4c, E4k. lia.
  - unfold B32. rewrite E4c, uval_lit by lia. lia.
Qed.

Lemma payA_same : ltac2:(tb__ "0|1|
S2dSfA1S2dS65A1S0S2fS67R1A1S30A3S155S63Vrho0;Sd0VCST;VFB;VFF;A3R3S11Z0M0A1G0R2R2A8F_;Fbd;Ffacts;").
Proof.
  intros facts bd Hw. split; [exact Hw|]. split; [lia|]. intros rho HF _ _ Hn. unfold pay_sem. rewrite uval_lit by lia.
  split; [lia|]. split; [lia | exact Hn].
Qed.

Lemma frozen_stableA' : ltac2:(tb__ "0|0|
S3cS3cS50S10S15bS63R3A2S0S2fS54R4R3A2S30A3S4fS3dR6S60VAInv;VCST;VXGL;S63VKc;Vrho0;Sd0VCST;VFB;VFF;A3VFB;VFF;VBX;S53R4R3AdA3F_;F_;Frho;Fnd;Fm;Fn;").
Proof.
  intros n m nd rho Hm Hb r r' tp tr md md' _ Hme (Ai & kc & HJ). exists Ai, kc.
  eapply (JAi_stable segs AInv CST XGL NF Kc rho0 (P0_hvn CST FB FF) FB FF BX PTrue HKc ALA m nd Ai kc rho rho tp tr md md'); [exact Hm | exact Hb | apply agree_below_refl | exact Hme | exact HJ].
Qed.

Section X.
Variable TR : assn -> assn -> Prop.
Variable FAM : ltac2:(tb__ "0|0|
S3bS2dS44Q40A1A1S11cF_;F_;").
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S4dS5S10S2dS44Q40A1A1S11cSf3SfS18R3A1S13S6R4A1A1A3VTR;S4cS3dR6R5R4R3A5R2A2M0F_;G0F_;FQ;Ftp;Frho;FS;FJ;").
Hypothesis TR_ex : forall (T : Type) (J : T -> jpredA) S rho tp (Q : assn),
  (forall x, TR (SPA segs (J x) S rho tp) Q) -> TR (SPA segs (fun r p t m => exists x, J x r p t m) S rho tp) Q.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S11cS11cS11cS11dR3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_exw : forall (T : Type) (P : T -> assn) (Q : assn), (forall a, TR (P a) Q) -> TR (fun w => exists a, P a w) Q.
Hypothesis TR_callP : ltac2:(tb__ "0|5|
S4dS4dS5S5S128S2dS12A1M0S2dS2eS5Se7A2M1A1S2dS2eSeSeA2M2A1S11cS10S2dS44Q40A1A1M3G2Sf0G2R1R5A3Sf0G2R2S7RbA1A3F_;Fr;S0S35G0A1SebRaR9R8A3S34G0R7A2A3S0S2fSedRbRaR9R8Sf4G1S5S36S5Se7A2R7A4A5S30A3S10G3VTR;S4cS3dRfRdR2R1A5Se9S3dS15S6RdA1A1R2R1RaA5A2Ftp1;Frho1;S2dS109A1M4S124S108S4eS3dR9R8R10S31G4S14eR3S14fR2R1A2A4A5R13RaR9R4R2A4R13S127S126RbRfS120R3RaR4A3A3R10A2RaR5R3A4F_;F_;Fmd;Fms;Ftr;S5Se7G4S124S108S10G3G4S124S108Sf0G1S31S5Se7RaR9A4R14A3S4eS3dR12R11R19S31G4S14eR9S14fR8R7A2A4A5R1cR13R12RaR8A4S118S15S6R1aA1A1S127S126R14R18S120R9R13RaA3A3R19A2R8A3S4eS3dR9R8ReS31G4S14eR7S14fR6R5A2A4A5ReS127S126R16R1aS120RbR15RcA3A3R1bA2R15RaR9R8R6A6S1S160R17S120RcR16RdA3R1bR1cR1dR10R1eR19RbA9S10S119R18S120RdR17ReA3R1cR1dS6R1eA1S6R1fA1S6R11A1R1RcA9VTR;S4cS3dSeeR11S127S126R19R1dS120ReR18RfA3A3R1eA2R18RdRcA5S161R1eR1fR12R20R1dR1bA6R2RcA5R1aA2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S4cS3dR11RfR8R7A5R9A2F_;F_;F_;F_;F_;F_;Ftp;Frho;FQ;FXk;FPosts;FR;Fs;FPre;FC;FJp;FJ;").
Hypothesis CVRES : ltac2:(tb__ "0|1|
S2dS2eS3bS3bA2M0A1S2dS2eG0S3bA2A1S6aS10S2dS44Q40A1A1S68Z3R3A2VTR;S4cS3dS58VAInv;VCST;VXGL;VKc;S150R6R5A2R6R5R4S53S113AaS10aR3R2A5Se9S3dS63R3R2S132VAInv;VCST;VXGL;VKc;S150S53SdeR6R5R4AaA5A2F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Hypothesis CSM : ltac2:(tb__ "0|2|
S105S10S2dS44Q40A1A1VTR;S4cS3dS146VAInv;Z0M0R3VKc;A4Sb9R2R1A5Se9S3dS63R2R1S2cS2eS5Se7A2M1S31S5Se7Sb8S143VAInv;VCST;VXGL;G0R3VKc;A6A4S33G1A1A3A5A2Ftp1;Frho1;FAi;").

Hypothesis CMEMSET : ltac2:(tb__ "0|1|
S105S10S2dS44Q40A1A1VTR;S4cS3dS145VAInv;R3VKc;A3S8fR2R1A5Se9S3dS63R2R1S2cS2eS5Se7A2M0S31S5Se7S8dS142VAInv;VCST;VXGL;R3VKc;A5A4S33G0A1A3A5A2Ftp1;Frho1;FAi;").
Hypothesis CMEMCPY : ltac2:(tb__ "0|2|
S105S10S2dS44Q40A1A1VTR;S4cS3dS144VAInv;R3VKc;A3S7aR2R1A5Se9S3dS63R2R1S2cS2eS5Se7A2M0S31S5Se7S79S142VAInv;VCST;VXGL;R3VKc;A5A4M1S2cG0G1S33G0A1A3A3A5A2Ftp1;Frho1;FAi;").

Hypothesis CALL_sd : ltac2:(tb__ "0|2|
S5S128S2dS12A1M0S10S2dS44Q40A1A1S50S11cS0S35G0A1SebR7Sf7R6A3S34G0R5A2A3S0S2fSecR8Sf7R7R6Sf4S9S5SbSfcA4A5S30A3S0S2fS15aS63S15S6R9A1A1A2S30A3S0S2fS54S15S6RaA1A1R5A2S30A3S0S2fSf2SfS28S15S6RbA1M1A1A1S13G1A1A3S30A3S9S10Sf0S9R2SfcA3S2aS15S6RfA1A1RcR2A3VTR;S4cS3dVJAv;RbA1S11aS13S6R10A1A1Se8RfSf7SbR4A1R10ReA5A2R3RcA5RaA2F_;F_;Frho';FL;VTR;S4cS3dVJAv;R8A1RdRaR9A5R7A2F_;F_;F_;F_;F_;F_;FQ;Fnd;Ftp;Frho;FR;Fs;FCl;").
Hypothesis REENTER : ltac2:(tb__ "0|4|
S5S50S2eS3bSeA2M0S10S2dS44Q40A1A1M1S3bG1Sf0S2eS2eS5S50A2M2G0A2S31G2G0S31S5S50R7R6A4R5A4S73A3S1S46Z0S5cS31G2G0S31S5S50R8R7A4R6A4R5A2M3A2S48G3R3A2A2VTR;S4cS3dVJAv;R8A1R9R6R5A5VFAM;R4R3A2A2F_;F_;Ftp0;Fb;Ftp;Frho;Frv;Fnd;FT;").
Hypothesis POST : ltac2:(tb__ "0|1|
S5S50S10S2dS44Q40A1A1M0S3bG0Sf0S2eS5Se7A2S31S5Se7R6S138R5A1A4S137A3VTR;S4cS3dVJAv;R6A1R7R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;Fnd;FP;").

Ltac meas := unfold emeasA; cbn [eda_rank eda_var fst snd z0 eval]; rewrite lit_unsigned; cbn; lia.

Ltac vmr := first [ lazymatch goal with |- @eq ?T ?t ?v => tryif first [ has_evar t | has_evar v ] then fail else vm_cast_no_check (@eq_refl T v) end
                  | vm_compute; reflexivity ].
Tactic Notation "innth" integer(n) := cbn [In cutsH exitsH Posts_hvn PD_hvn PD_vr]; do n right; left; reflexivity.

Lemma shobj_range_hse : ltac2:(tb__ "0|1|
S10S2dSfA1S3bSf3SfS18R3A1R2A3S0S2fSd3R3A1S30A3S1S46S36S3bS3bS1fR5S13dS6eZ0Z8S33S1bA1S1cA5A2M0A3R3A2S48R3S38S3bS3bG0A3A2A2S153R4A1F_;F_;F_;Fa;FF;Frho;").
Proof.
  intros rho F a HF HFR Hr. pose proof (framez_of rho F HF HFR) as [G1 G2 G3]. unfold is_shadowZ, IMG_HI in *.
  unfold shobj, obj_range, obj_lo_of, obj_hi_of in Hr. cbn [ob_base ob_lo ob_hi fst snd] in Hr.
  unfold SHADOW_OFF, HIGH_SHADOW_END in *. rewrite !soff_lit_small in Hr by lia.
  change (bv_unsigned (eval rho (SVar gF))) with (uval rho (SVar gF)) in Hr. rewrite G1 in Hr.
  pose proof (uval_range rho vF). lia.
Qed.

Lemma X_Y_ep : ltac2:(tb__ "0|6|
S5S5S2dS2eSeSeA2A1S2dS65A1SeSeS10S2dS44Q40A1A1M0S3bG0S0SeSdRaA1S11S123A1A3S0S2fScS2cSfS22SaS6eA1S6cA2S2cSfS14S1aS6eA1S11S4bS47Z2M1Z3dA2Z1A2A1A2S33SfA1A3A3S13S6RbA1A1A2S30A3S0S2fS134S83R8R7A2S7RcA1A2S30A3S0S2fS29S6S140RdS83R9R8A2S6eZ0Z8A5A1A1S30A3S0S2fS29S6S74ReRaR9A3A1A1S30A3S0S2fS54S15S6RfA1A1S52RdS6bRcS51A4A2S30A3S0S2fSd1S13S6R10A1A1A1S30A3S0S2fSd3S13S6R11A1A1A1S30A3S0S2fS13cS13S6R12A1M2A1R10S6bS37S32A1Sd2S17G2A1A6S30A3S0S2fS13bVXGL;S13S6R13A1M3A1R11S6bS34S32U0A2S17G3A1Sd4S83RfReA2A8S30A3S0S5S74R14R10RfA3R13A3Sf0S2eS2eS5S50A2M4S2eS3bSeA2M5A2S31G4G5S31S5S50R14S52R13S6bR12S51A4A4S31S3bSeZ32S10bA4A4S73A3S46S49Z37S47G1Z40A2A2ReA2VTR;S4cS3dVJAv;S52R15S6bR14S51A4A1R17R11R10A5VFAM;RfReA2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Ftp0;Fb;Ftp;Frho;Fk;Fd;Fbd;Ftv;FC;FY;").
Proof.
  intros Y C tv bd d k rho tp b tp0 Hbase Hfe HXi Hwf1 Hwf2 Hnb HB HFRF HRO HXL HC HinC Hb.
  eapply TR_pre; [|apply (REENTER C (NDA tv fr_hvn bd ANone) (50, z0)); [exact HinC | meas]].
  intros w Hw. rewrite <- HC. unfold epi_state.
  apply (JA_flag_carve segs HTOP AInv CST XGL ALA HCST HXGL LFLAG NF Kc rho0 (P0_hvn CST FB FF) FB FF BX PTrue HKc HBX HNP
           tv fr_hvn bd ANone 0%nat 110%positive 0 120%positive (shadow_reopen_stateA Y (X_epi d k) gF 0 8) rho tp w eq_refl ltac:(lia)).
  - exact Hbase.
  - exact Hwf2.
  - intros Ai rho1 tp1 md1 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR. cbn [shadow_reopen_stateA ax_S ss_facts ss_objs ax_X] in HF |- *. split.
    + intros o a Ho Hr. apply in_app_or in Ho as [Ho|[<-|[]]].
      * exact (siteH Ai rho _ tv fr_hvn _ rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HN HD HZ HFR HRO o a Ho Hr).
      * right. right. exact (shobj_range_hse rho _ a HF HFRF Hr).
    + exact (proj2 (proj2 (siteX Ai rho _ tv fr_hvn (Some 0%nat) _ _ rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HBf HFF HN HD HZ HFR HXL))).
  - apply (JA_shadow_reopen segs HTOP AInv CST XGL ALA HCST HXGL LFSH NF Kc rho0 (P0_hvn CST FB FF) FB FF BX PTrue HKc HBX HNP
             tv fr_hvn bd ANone 0%nat 110%positive 0 120%positive gF 0 8 Y (X_epi d k) rho tp w eq_refl ltac:(lia) Hbase ltac:(lia)
             ltac:(vm_compute; split; [discriminate|discriminate]) Hfe (xrs_inclb_sound _ _ HXi) Hwf1); [|exact Hw].
    intros Ai rho1 tp1 md1 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR. split.
    + exact (siteF Ai rho _ tv fr_hvn _ rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HN HD HZ HFR HRO).
    + intros r y Hr Hy. left. exact (proj1 (siteX Ai rho _ tv fr_hvn (Some 0%nat) _ _ rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HBf HFF HN HD HZ HFR HXL) r y Hr Hy).
Qed.

Lemma XH_X_epf0 : ltac2:(tb__ "0|1|
S10S2dS44Q40A1A1M0S3bG0S46S49Z37S47Z2Z40A2A2R2A2VTR;S4cS3dVJAv;S7dA1S95R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. eapply TR_pre; [intros w Hw; exact (SPA_axforms segs _ xf_cf rho X_epf0 Y_epf0 tp w Y_epf0_eq Hw)|].
  apply (X_Y_ep Y_epf0 C_epf0 _ _ vND vNK rho tp b tp0); [vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr| exact C_epf0_eq | innth 18 | exact Hb].
Qed.
Lemma XH_X_epf1 : ltac2:(tb__ "0|1|
S10S2dS44Q40A1A1M0S3bG0S46S49Z37S47Z2Z40A2A2R2A2VTR;S4cS3dVJAv;S7dA1S96R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. eapply TR_pre; [intros w Hw; exact (SPA_axforms segs _ xf_cf rho X_epf1 Y_epf1 tp w Y_epf1_eq Hw)|].
  apply (X_Y_ep Y_epf1 C_epf1 _ _ vND vNK rho tp b tp0); [vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr| exact C_epf1_eq | innth 19 | exact Hb].
Qed.

Lemma cm_rng : ltac2:(tb__ "0|4|
S10S2dSfA1SeSf3SfS18R3A1R2A3S0S2fSd3R3A1S30A3S0S2fSefSfS19S14R3S1aP1eA1A2A1R4A3S30A3S0S2fSefSfS19S14S103S101A1M0S11S10cA1A2A1R5A3S30A3S1S0S3bS64R7S16Se6R5G0A3A2S4aS64R7R5A2S64R7G0A2M1A2A3S1S0S3bS21R7G0A2G1A3S1S0S3bS21R7S16Se6G0S11ZcM2A1A3A2S4aG1G2A2A3S0S3bS64R7S16Se6S6cS11Z20M3A1A3A2S4aS64R7S6cA2G3A2A3A2A2A2F_;F_;F_;F_;Fd;FF;Fr;").
Proof.
  intros r F d HF HFR Hd Hs. pose proof (framez_of r F HF HFR) as [_ _ G3]. unfold IMG_HI in G3.
  pose proof (holds_mem _ _ _ HF Hd) as F1. pose proof (holds_mem _ _ _ HF Hs) as F2.
  rewrite h_ule in F1, F2. change (uval r (SVar 30)) with (bv_unsigned (rw r V_TOP)) in F1. unfold B32 in F2. rewrite uval_lit in F2 by lia.
  pose proof (uval_range r (cb4 vNC)) as Rc. pose proof (uval_range r d) as Rd. pose proof (uval_range r vF) as Rf.
  assert (A12 : uval r (SAlu ALU_ADD (cb4 vNC) (SLit 12)) = uval r (cb4 vNC) + 12) by (apply uval_add_litZ; lia).
  split; [apply uval_add_small; lia|]. split; [apply soff_smallu; lia|]. split; [rewrite <- A12; apply soff_smallu; rewrite A12; lia|].
  apply uval_add_litZ; lia.
Qed.

Lemma X_E_sd : ltac2:(tb__ "0|7|
S5S5S5S5S2dS3eA1S128S2dS12A1M0S10S2dS44Q40A1A1M1S3bG1S3bS0S35S5A1S3fRcR8A2S34S5RbA2A3S0S35G0A1SebRcSf7R8A3S34G0R7A2A3S0S2fSecRdSf7R9R8Sf4S9S5SbSfcA4A5S30A3S0S2fS15aS63S15S6ReA1A1A2S30A3S0S2fS54S15S6RfA1A1S70A2S30A3S0S2fSf2SfS28S15S6R10A1M2A1A1S13G2A1A3S30A3S0S5S11aS13S6R11A1A1Se8RdSf7SfaR11RcA5A2R10A3S0S5S11aS13S6R12A1A1Se8ReSf7SfbR12RdA5A2R10A3Sf0S2eS2eS5S50A2M3S2eS3bSeA2M4A2M5S31G3G4S31S5S50R12S70A4M6S31S3bSeR9S10bA4A4S73A3Sf0G5S31G3G4G6S31S3bSeRaS10bA4A4S73A3S46Z0RbA2S46S49S4aRcZ1A2S47Z2Z40A2A2ReA2VTR;S4cS3dVJAv;S70A1R18R11R10A5VFAM;RfReA2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Frk;Ftp0;Fb;Ftp;Frho;FR;Fs;Fxf;FT1;FT0;FE;FE0;").
Proof.
  intros E0 E T0 T1 xf s R rho tp b tp0 rk HE He Hchk Hnf Hnb Hfb HT0 HT1 Hin0 Hin1 Hrk Hb.
  eapply TR_pre; [intros w Hw; exact (SPA_axforms segs _ xf rho E0 E tp w HE Hw)|].
  apply (CALL_sd E s R rho tp ndp (FAM b tp0) He Hchk Hnf Hnb Hfb).
  intros L rho' HL Hag. cbn [Posts_sd In] in HL. destruct HL as [<-|[<-|[]]]; cbn [la_state].
  - rewrite HT0. apply (REENTER T0 ndp (rk, z0)); [exact Hin0|]. unfold emeasA. cbn [eda_rank eda_var fst snd z0 eval]. rewrite lit_unsigned by lia. lia.
  - rewrite HT1. apply (REENTER T1 ndp (rk, z0)); [exact Hin1|]. unfold emeasA. cbn [eda_rank eda_var fst snd z0 eval]. rewrite lit_unsigned by lia. lia.
Qed.
Lemma XH_E_A : ltac2:(tb__ "0|1|
S10S2dS44Q40A1A1M0S3bG0S46S49Z5aS47Z2Z40A2A2R2A2VTR;S4cS3dVJAv;S70A1S8aR5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply (X_E_sd E_A0 E_A T_A0 T_A1 xf_sd s_A R_A rho tp b tp0 88 E_A_eq);
    [vmr|vmr|vmr|vmr|vmr| exact T_A0_eq | exact T_A1_eq | innth 3 | innth 4 | lia | lia].
Qed.
Lemma XH_E_B : ltac2:(tb__ "0|1|
S10S2dS44Q40A1A1M0S3bG0S46S49Z56S47Z2Z40A2A2R2A2VTR;S4cS3dVJAv;S70A1S71R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply (X_E_sd E_B E_B T_B0 T_B1 [] s_B R_B rho tp b tp0 84 E_B_eq);
    [vmr|vmr|vmr|vmr|vmr| exact T_B0_eq | exact T_B1_eq | innth 5 | innth 6 | lia | lia].
Qed.
Lemma XH_E_C : ltac2:(tb__ "0|1|
S10S2dS44Q40A1A1M0S3bG0S46S49Z52S47Z2Z40A2A2R2A2VTR;S4cS3dVJAv;S70A1S72R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply (X_E_sd E_C E_C T_C0 T_C1 [] s_C R_C rho tp b tp0 80 E_C_eq);
    [vmr|vmr|vmr|vmr|vmr| exact T_C0_eq | exact T_C1_eq | innth 7 | innth 8 | lia | lia].
Qed.

Lemma HIN_v : ltac2:(tb__ "0|1|
S10S124S105S10S2dS44Q40A1A1S108Sf3SfS18R6A1S13S6S6dA1A1A3Sd0VCST;VFB;VFF;Vrho0;A4S118S63Vrho0;R8A3VAInv;R7R6R5R4A4S55Vrho0;R8A2S129RbS107S106R9A1A1A2S59VFB;RaA2S5aVFF;RbA2S56VFF;RcReS6bA4S1S133VCST;Vrho0;VFB;VFF;RfS33S2eSeSeA2A1M0S6bS76A8S1S135VCST;VXGL;Vrho0;VFB;VFF;RfG0S6bS7cA9S150S12aVFB;RfG0A3S130VFF;RfS6bA3S127S126RfS76ReA3S6fA2A3A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FAi;Fms;Frho;").
Proof.
  intros rho ms Ai rho1 tp1 md1 HF HP0 Hav HM HTP HTK HBf HFF HFR. destruct (P0_now rho Hav HP0) as (HT & Hb & Hal & HKD & _).
  assert (HB : baseF (ss_facts (ax_S E_vr)) = true) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
  pose proof (basez_of rho _ HF HB) as BZ. pose proof BZ as [Bsp Bb Bal BL BB Btop]. rewrite aceil_val in *.
  assert (HN0 : tvinA FB Ai rho []) by constructor. assert (HZ0 : tvz rho []) by constructor.
  split; [|split].
  - intros o a Ho Hr. eapply (robjs_checkP_sound segs AInv CST ALA rho0 FB FF Ai rho _ [] fr_hvn None extraO R_v rho1 tp1 md1 HM HF (T_ok_T0 rho0 _ Ai HTP HTK) HN0 I HZ0 HFR ltac:(vmr));
      [intros o' a' Ho' HE Hr'; exact (extraO_client rho o' a' _ _ BZ Hav HP0 HE Hr') | exact Ho | exact Hr].
  - exact (proj1 (siteX Ai rho _ [] fr_hvn None (ss_objs (ax_S E_vr)) Xk_v rho1 tp1 md1 HM HF HB Hav HP0 HTP HTK HBf HFF HN0 I HZ0 HFR ltac:(vmr))).
  - unfold P0_vr. rewrite !rw_call'.
    change (wsub_get s_v 17) with vNK. change (wsub_get s_v 15) with vND. change (wsub_get s_v 14) with vAL. change (wsub_get s_v 12) with vb184.
    split; [exact HKD|]. split.
    + destruct Hb as (f & sz & fl & Hin & H1 & H2). exists f, sz, fl. split; [apply In_FFx; left; exact Hin|].
      assert (E184 : uval rho vb184 = uval rho vb + 184) by (unfold vb184; apply uval_add_litZ; unfold IMG_HI in *; lia).
      unfold uval in E184, H1, H2. rewrite E184. lia.
    + destruct Hal as (f & sz & fl & Hin & H1 & H2). exists f, sz, fl. split; [apply In_FFx; left; exact Hin|]. unfold uval in H1, H2. lia.
Qed.

Lemma XH_E_vr : ltac2:(tb__ "0|1|
S10S2dS44Q40A1A1M0S3bG0S46S49Z4aS47Z2Z40A2A2R2A2VTR;S4cS3dVJAv;S70A1S8cR5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  eapply TR_pre with (P := SPA segs (JAv ndp) E_vr rho tp).
  { intros w Hw. exact (SPA_axforms segs _ xf_vr rho E_vr0 E_vr tp w E_vr_eq Hw). }
  apply TR_facts. intros HF. unfold ndp, ndF. change (tv_hvn vND vNK) with ([] ++ tv_hvn vND vNK).
  apply (client_callT segs AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_hvn CST FB FF) FB FF BX PTrue HKc HBX P0_vr PTrue (fun _ H => H) (fun _ _ _ H => H)
           Pre_vr Lib_vec_reserve.nd0 PD_vr NF eq_refl eq_refl eq_refl TR TR_facts TR_ex TR_pre TR_callP CVRES eq_refl
           E_vr s_v R_v Xk_v rho tp [] (tv_hvn vND vNK) fr_hvn (bd_hvn vNC vNK) [] ANone (FAM b tp0)).
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - apply payA_of_bud_pay. vmr.
  - vmr.
  - intros Ai ms HF' HP0 Hav HBf HFF HN HD HZ HFR (rho1 & tp1 & md1 & HM) HT HTK. exact (HIN_v rho ms Ai rho1 tp1 md1 HF' HP0 Hav HM HT HTK HBf HFF HFR).
  - intros [Ld ndL] rho' tp' Hd Hag. cbn [PD_vr In] in Hd. destruct Hd as [Hd|[Hd|[Hd|[]]]]; injection Hd as <- <-;
      cbn [fst snd nd_tv nd_bd nd_am Lib_vec_reserve.nd0 ND am_subst app].
    +
      rewrite T_keep0_eq, imp_keep_tv, imp_keep_bd. rewrite app_nil_r.
      eapply TR_pre; [|apply (REENTER T_keep ndk (70, z0)); [innth 10 | meas]].
      intros w Hw. rewrite <- T_keep_eq. apply (SPA_refacts_JA segs); [exact Hw | vmr |].
      intros tr md HJ HF2. apply Forall_app. split; [|exact HF2]. apply Forall_app. split.
      * apply (slot_holds rho' _ vNK HF2); vmr.
      * assert (TNZ : tnz rho' (vND, kb4 vNK)).
        { destruct HJ as (Ai & kc & Hav' & _ & _ & _ & _ & _ & _ & _ & _ & HP0' & _). destruct (P0_now rho' Hav' HP0') as (_ & _ & _ & HKD & _).
          pose proof (holds_mem _ _ (SPUle (SAlu ALU_ADD vNC (SLit 3)) vNK) HF2 ltac:(vmr)) as F1.
          pose proof (holds_mem _ _ (SPUle vNC vNK) HF2 ltac:(vmr)) as F3. pose proof (holds_mem _ _ (SPUle vNK (SLit B32)) HF2 ltac:(vmr)) as F4.
          rewrite h_ule in F1, F3, F4. unfold B32 in F4. rewrite uval_lit in F4 by lia. pose proof (uval_range rho' vNC).
          rewrite uval_add_litZ in F1 by lia. unfold tnz. cbn [fst]. apply HKD. lia. }
        pose proof (JA_tv_facts segs AInv CST XGL NF Kc rho0 (P0_hvn CST FB FF) FB FF BX PTrue ALA _ _ _ _ _ (vND, kb4 vNK) eq_refl HJ (or_introl eq_refl) TNZ) as TF.
        constructor; [|constructor]. apply (proj1 (Forall_forall _ _) TF). unfold tv_factsA. cbn [fst snd]. do 5 right. left. reflexivity.
    +
      rewrite T_fail0_eq, imp_fail_tv. change (bd_subst _ []) with (@nil bitem). cbn [app].
      apply (REENTER T_fail0 ndf (70, z0)); [innth 12 | meas].
    +
      rewrite T_grown0_eq, imp_grown_tv, imp_grown_bd. rewrite app_nil_r.
      eapply TR_pre; [|apply (REENTER T_grown ndg (70, z0)); [innth 11 | meas]].
      intros w Hw. rewrite <- T_grown_eq. apply (SPA_refacts_JA segs); [exact Hw | vmr |].
      intros tr md _ HF2. apply Forall_app. split; [|exact HF2]. apply (slot_holds rho' _ vKg HF2); vmr.
Qed.

Lemma site_pure : ltac2:(tb__ "0|2|
S5S128S2dS12A1S10S2dS2eSeSeA2A1S2dS65A1S0S2fSd1S13S6R6A1A1A1S30A3S0S2fS159S13S6R7A1A1R3S6bS37S32A1M0Sd2R5A6S30A3S0S2fS13bVXGL;S13S6R8A1M1A1R4S6bG0S17G1A1Sd4S7R8A1A8S30A3S157VAInv;VCST;VXGL;S63Vrho0;Sd0VCST;VFB;VFF;A3VFB;VFF;R9R8R7R6S52R5S6bR4S51A4S37S3bA1S105S124S4L_;L_;AfF_;F_;F_;Fbd;Ftv;Frho;FR;Fs;FE;").
Proof.
  intros E s R rho tv bd HB HR HX Ai ms HF HP0 Hav HBf HFF HN HD HZ HFR (rho1 & tp1 & md1 & HM) HT HTK. cbn [nd_tv nd_fr] in HN, HD, HZ, HFR.
  split; [exact (siteP Ai rho _ tv fr_hvn None R rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HBf HFF HN HD HZ HFR HR)|].
  split; [exact (proj1 (proj2 (siteX Ai rho _ tv fr_hvn None _ _ rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HBf HFF HN HD HZ HFR HX))) | exact I].
Qed.

Lemma X_E_mc : ltac2:(tb__ "0|9|
S5S5S5S5SeSeS2dS2eSeSeA2A1S2dS65A1S128S2dS12A1M0S10S2dS44Q40A1A1M1S3bG1S0S35S5A1S3fReSaeA2S34S5RdA2A3S0S35S12A1M2Sf1S12S17S6ReA1A1U4A3S34S12S1dRbS103S101A1M3S16Se6G3S11ZcA1A3S33S1bA1M4S1cA5A2A3S0S2fS20S15S6RfA1A1Sa4RcA1A2S30A3S0G2Sf1S12S17S6Sd7R10RdA2A1A1UcA3S34S12S1dS6cS11Z20A1S11Z2cA1G4S1cA5A2A3S0S2fS20S15S6Sd7R11ReA2A1A1SacA2S30A3S0S2fSd3S13S6R12A1A1A1S30A3S0S2fSefSfS19S14R10S1aP1eA1A2A1S13S6R13A1A1A3S30A3S0S2fSefSfS19S14G3S11S10cA1A2A1S13S6R14A1A1A3S30A3S0S5SddSd7R15R12A2A1R14A3S0S35G0A1SebR15S7aRfA3S34G0ReA2A3S0S2fSedR16S7aR10RfS2cS5S79S2cS5S79S33S5A1A3A3A5S30A3S0S2fS154S63R11A2S30A3S0S2fS15aS63S15S6R18A1A1A2S30A3S0S2fS54S15S6R19A1A1S52R15S6bR14S51A4A2S30A3S0S2fS69S15S6R1aA1A1R15A2S30A3S0S2fS67R16A1S30A3S0S2fSd1S13S6R1cA1A1A1S30A3S0S2fS159S13S6R1dA1A1R19S6bS37S32A1M5Sd2R16A6S30A3S0S2fS13bVXGL;S13S6R1eA1M6A1R1aS6bG5S17G6A1Sd4S7R1eA1A8S30A3S0S5S151S7aR1fR19R18S79A5R1eA3Sf0S2eS2eS5S50A2M7S2eS3bSeA2M8A2S31G7G8S31S5S50R1fS52R1cS6bR1bS51A4A4S31S3bSeZ3aS10bA4A4S73A3S46S49Z3cS47Z2Z40A2A2R17A2VTR;S4cS3dVJAv;S52R1eS6bR1dS51A4A1R24R1aR19A5VFAM;R18R17A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Ftp0;Fb;Ftp;Frho;FR;Fs;Fbd;Ftv;Fk;Fd;FT;FE;FE1;FE0;").
Proof.
  intros E0 E1 E T d k tv bd s R rho tp b tp0 HE1 H4 Hwf4 H12 Hwf12 HFR Hd Hs HE He Hchk Htp Hnf Hnb Hbb Hwp HB HR HX HT HinT Hb.
  eapply TR_pre with (P := SPA segs (JAv (NDA tv fr_hvn bd ANone)) E rho tp).
  { intros w Hw. pose proof (SPA_axforms segs _ xf_mc rho E0 E1 tp w HE1 Hw) as Hw1. rewrite <- HE.
    assert (Hw2 : SPA segs (JAv (NDA tv fr_hvn bd ANone)) (E_mc2 E1 d) rho tp w).
    { unfold E_mc2. apply (SPA_reshape segs _ rho E1 4 _ _ tp w H4); [reflexivity | reflexivity | reflexivity | exact Hwf4 | | exact Hw1].
      intros HF. destruct (cm_rng rho _ d HF HFR Hd Hs) as (A1 & A2 & A3 & A4).
      unfold dst_obj, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite !soff_lit_small by lia. rewrite A2, A3.
      change (bv_unsigned (eval rho (SAlu ALU_ADD d (cb4 vNC)))) with (uval rho (SAlu ALU_ADD d (cb4 vNC))). rewrite A1. unfold uval. lia. }
    unfold E_mc3. apply (SPA_reshape segs _ rho (E_mc2 E1 d) 12 _ _ tp w H12); [reflexivity | reflexivity | reflexivity | exact Hwf12 | | exact Hw2].
    intros HF. assert (HF' : Forall (holds rho) (ss_facts (ax_S E1))) by exact HF.
    destruct (cm_rng rho _ d HF' HFR Hd Hs) as (A1 & A2 & A3 & A4).
    unfold src_obj, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite !soff_lit_small by lia.
    change (bv_unsigned (eval rho (SAlu ALU_ADD vF (SLit 32)))) with (uval rho (SAlu ALU_ADD vF (SLit 32))). rewrite A4. unfold uval. lia. }
  apply (purec_callT_xp segs AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_hvn CST FB FF) FB FF BX PTrue HKc TR TR_facts TR_ex TR_pre TR_callP
           XP_memcpy Pre_mc [L_mc1; L_mc1] E s R rho tp (NDA tv fr_hvn bd ANone) bd (FAM b tp0)).
  - intros Ai rho1 tp1. cbn [map]. exact (CMEMCPY Ai rho1 tp1).
  - reflexivity.
  - reflexivity.
  - exact He.
  - exact Hchk.
  - exact Htp.
  - exact Hnf.
  - exact Hnb.
  - exact Hbb.
  - cbn [nd_bd]. apply payA_same. exact Hwp.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - exact (site_pure E s R rho tv bd HB HR HX).
  - intros Ai tr ms md Hsm HM HX'. exact (XP_memcpy_site segs AInv CST XGL ALA HCST HXGL Ai E memcpy_pc s R rho tp tr ms md Hsm HM HX' He).
  - intros L rho' tp' HL. cbn [In] in HL. assert (HL' : L = L_mc1) by (destruct HL as [<-|[<-|[]]]; reflexivity). subst L. cbn [nd_tv nd_fr nd_am]. rewrite HT.
    apply (REENTER T (NDA tv fr_hvn bd ANone) (58, z0)); [exact HinT | meas].
Qed.

Lemma XH_E_sm : ltac2:(tb__ "0|1|
S10S2dS44Q40A1A1M0S3bG0S46S49Z62S47Z2Z40A2A2R2A2VTR;S4cS3dVJAv;S84A1S8bR5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply TR_facts. intros HF.
  apply (smalloc_callT segs AE_A AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_hvn CST FB FF) FB FF BX PTrue HKc TR TR_facts TR_ex TR_pre TR_callP
           0 E_sm0 s_sm R_sm rho tp nd0 110 120 (FAM b tp0) CSM).
  - lia.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - intros A A' _; exact I.
  -
    intros Ai ms HF' HP0 Hav HBf HFF HN HD HZ HFR (rho1 & tp1 & md1 & HM) HT HTK. destruct (P0_now rho Hav HP0) as (_ & _ & _ & _ & HC0).
    cbn [nd_tv nd_fr nd0 ND] in HN, HD, HZ, HFR |- *.
    split; [|split].
    + exact (siteP Ai rho _ (tv_hvn vND vNK) [] None R_sm rho1 tp1 md1 HM HF' ltac:(vmr) Hav HP0 HT HTK HBf HFF HN HD HZ HFR ltac:(vmr)).
    + exact (proj1 (proj2 (siteX Ai rho _ (tv_hvn vND vNK) [] None (ss_objs (ax_S E_sm0)) (ax_X E_sm0) rho1 tp1 md1 HM HF' ltac:(vmr) Hav HP0 HT HTK HBf HFF HN HD HZ HFR ltac:(vmr)))).
    + split; [change (wsub_get s_sm 12) with (SLit 64); rewrite uval_lit by lia; change (fs_frame_size 0) with 64; lia|].
      unfold ffpairs. change (map (fun y : Z * Z * Z => fst y) FF) with (map fst FF). rewrite HC0. cbn. lia.
  -
    intros rho' tp'. rewrite T_sm_eq.
    eapply TR_pre with (P := SPA segs (JAv ndp) T_sm1 rho' tp').
    { intros w Hw. exact (SPA_axforms segs _ [AXSelect sel_sm] rho' T_sm T_sm1 tp' w T_sm1_eq Hw). }
    apply (TR_pre (fun w => exists rho2, SPA segs (JAv ndp) C_pro rho2 tp' w)).
    { intros w Hw.
      destruct (JA_frame_open segs HTOP AInv CST XGL ALA HCST HXGL LFLAG NF Kc rho0 (P0_hvn CST FB FF) FB FF BX PTrue HKc HBX HNP
                  (tv_hvn vND vNK) fr_hvn (bd_hvn vNC vNK) ANone 0%nat 110 0 120
                  T_sm1 objs_sm1 (X_hvn vND vNK) [] rho' tp' w eq_refl ltac:(lia) eq_refl T_sm1_objs T_sm1_X
                  ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) eq_refl ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc)) as (rho2 & _ & Hw2); [| exact Hw |].
      - intros Ai rho1 tp1 md1 HF2 HP0 Hav HM HT HTK HBf HFF HN HDt HZt HFR. rewrite app_nil_r.
        exact (proj1 (siteX Ai rho' _ (tv_hvn vND vNK) fr_hvn (Some 0%nat) (ss_objs (ax_S T_sm1)) (X_hvn vND vNK) rho1 tp1 md1 HM HF2 ltac:(vmr) Hav HP0 HT HTK HBf HFF HN HDt HZt HFR ltac:(vmr))).
      - exists rho2. rewrite app_nil_r in Hw2. rewrite C_pro0_eq in Hw2. rewrite <- C_pro_eq.
        apply (SPA_x_len0 segs (JAv ndp) C_pro0 110 5 rho2 tp' w); [vmr | lia | vmr | exact Hw2]. }
    apply TR_exw. intros rho2. apply (REENTER C_pro ndp (96, z0)); [innth 1 | meas].
Qed.

Lemma f32_rng : ltac2:(tb__ "0|1|
S10S2dSfA1Sf3SfS18R2A1R1A3S0S2fSd3R2A1S30A3S0S3bS64R4S16Se6S6cS11Z20M0A1A3A2S4aS64R4S6cA2G0A2A3F_;F_;FF;Fr;").
Proof.
  intros r F HF HFR. pose proof (framez_of r F HF HFR) as [_ _ G3]. unfold IMG_HI in G3.
  pose proof (uval_range r vF). apply uval_add_litZ; lia.
Qed.

Lemma XH_X_rel : ltac2:(tb__ "0|1|
S10S2dS44Q40A1A1M0S3bG0S46S49Z5eS47Z2Z40A2A2R2A2VTR;S4cS3dVJAv;S70A1S9aR5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.

  apply (TR_pre (fun w => exists rho', SPA segs (JAv ndp) C_ms rho' tp w)).
  { intros [tr [ms md]] Hw. exists (rho_absorb rho [shobj gF 0 8 cells_rel DZero] (vms md tp ms)).
    change C_ms with (shadow_release_stateA X_rel objs_rel 110 [(32, 12)]).
    apply (JA_shadow_release segs HTOP AInv CST XGL ALA HCST HXGL LFSH NF Kc rho0 (P0_hvn CST FB FF) FB FF BX PTrue HKc HBX HNP
             (tv_hvn vND vNK) fr_hvn (bd_hvn vNC vNK) ANone 0%nat 110%positive 0 120%positive gF 0 8 cells_rel DZero X_rel objs_rel [(32, 12)] rho tp tr ms md
             eq_refl ltac:(lia) eq_refl X_rel_objs ltac:(lia) ltac:(vm_compute; split; discriminate) eq_refl ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc)
             ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc)); [|exact Hw].
    intros Ai rho1 tp1 md1 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR.
    exact (siteF Ai rho _ (tv_hvn vND vNK) fr_hvn objs_rel rho1 tp1 md1 HM HF ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) Hav HP0 HT HTK HN HD HZ HFR ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc)). }
  apply TR_exw. intros rho'.

  eapply TR_pre with (P := SPA segs (JAv ndp) E_ms rho' tp).
  { intros w Hw. pose proof (SPA_axforms segs _ _ rho' C_ms C_ms1 tp w C_ms1_eq Hw) as Hw1. unfold E_ms.
    apply (SPA_reshape segs _ rho' C_ms1 2 _ _ tp w C_ms1_o2); [reflexivity | reflexivity | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | | exact Hw1].
    intros HF. unfold xyz_obj, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite !soff_lit_small by lia.
    change (bv_unsigned (eval rho' (SAlu ALU_ADD vF (SLit 32)))) with (uval rho' (SAlu ALU_ADD vF (SLit 32))).
    rewrite (f32_rng rho' _ HF ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc)). unfold uval. lia. }

  apply (purec_callT_xp segs AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_hvn CST FB FF) FB FF BX PTrue HKc TR TR_facts TR_ex TR_pre TR_callP
           XP_memset Pre_ms [L_ms] E_ms s_ms R_ms rho' tp ndp (bd_hvn vNC vNK) (FAM b tp0)).
  - intros Ai rho1 tp1. cbn [map]. exact (CMEMSET Ai rho1 tp1).
  - reflexivity.
  - reflexivity.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - cbn [nd_bd ndp ndF]. apply payA_same. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - unfold ndp, ndF. apply (site_pure E_ms s_ms R_ms rho' (tv_hvn vND vNK) (bd_hvn vNC vNK)); OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - intros Ai tr ms md Hsm HM HX'. exact (XP_memset_site segs AInv CST XGL ALA HCST HXGL Ai E_ms memset_pc s_ms R_ms rho' tp tr ms md Hsm HM HX' ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc)).
  -
    intros L rho2 tp2 [<-|[]]. cbn [nd_tv nd_fr nd_am ndp ndF]. rewrite T_ms0_eq.
    eapply TR_pre; [|apply (REENTER C_body ndp (92, z0)); [innth 2 | meas]].
    intros w Hw. apply (SPA_axforms segs _ _ rho2 T_ms1 C_body tp2 w C_body_eq). unfold T_ms1.
    apply (SPA_reshape segs _ rho2 T_ms0 1 _ _ tp2 w T_ms0_o1); [reflexivity | reflexivity | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | | exact Hw].
    intros HF. unfold mid_xyz, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite !soff_lit_small by lia.
    change (bv_unsigned (eval rho2 (SAlu ALU_ADD vF (SLit 32)))) with (uval rho2 (SAlu ALU_ADD vF (SLit 32))).
    rewrite (f32_rng rho2 _ HF ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc)). unfold uval. lia.
Qed.

Lemma X_cm_Y : ltac2:(tb__ "0|5|
S5S5SeSeS50S10S2dS44Q40A1A1S11dS0S35S12A1M0Sf1S12S17S6R8A1A1U1A3S34S12S1dS16Se6R6S103S101A1M1A3S11Z0A1M2S11ZcA1M3S33S1bA1M4S1cA5A2A3S0G0Sf1S12S17S6Sd8R9R7A2A1A1U2A3S34S12S1dS16Se6S6cS11Z20A1A3G2G3G4S1cA5A2A3S0S2fS20S15S6RaA1A1SdaR8A1A2S30A3S0S2fS20S15S6Sd8RbR9A2A1A1SdbA2S30A3S0S2fSd3S13S6RcA1A1A1S30A3S0S2fSefSfS19S14RbS1aP1eA1A2A1S13S6RdA1A1A3S30A3S0S2fSefSfS19S14G1S11S10cA1A2A1S13S6ReA1A1A3S30A3S0S35S5A1S3fSe1Sd8RfRdA2A1Se5A2S34S5ReA2A3S4cS3dVJAv;RcA1R10RbRaR9A6S4cS3dVJAv;RdA1R10RcRbRaA6F_;F_;F_;F_;F_;F_;F_;F_;F_;Fw;Ftp;Frho;Fnd;Fk;Fd;FY;FX;").
Proof.
  intros X Y d k nd rho tp w H1 H2 Hwf1 Hwf2 HFR Hd Hs HY Hw.
  apply (SPA_axforms segs _ xf_cm rho (cm2 (cm1 X d)) Y tp w HY).
  assert (Hw1 : SPA segs (JAv nd) (cm1 X d) rho tp w).
  { unfold cm1. apply (SPA_reshape segs _ rho X 1 _ _ tp w H1); [reflexivity | reflexivity | reflexivity | exact Hwf1 | | exact Hw].
    intros HF. destruct (cm_rng rho _ d HF HFR Hd Hs) as (A1 & A2 & A3 & A4).
    unfold cm_dst, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite !soff_lit_small by lia. rewrite A2, A3.
    change (bv_unsigned (eval rho (SAlu ALU_ADD d (cb4 vNC)))) with (uval rho (SAlu ALU_ADD d (cb4 vNC))). rewrite A1. unfold uval. lia. }
  unfold cm2. apply (SPA_reshape segs _ rho (cm1 X d) 2 _ _ tp w H2); [reflexivity | reflexivity | reflexivity | exact Hwf2 | | exact Hw1].
  intros HF. assert (HF' : Forall (holds rho) (ss_facts (ax_S X))) by exact HF.
  destruct (cm_rng rho _ d HF' HFR Hd Hs) as (A1 & A2 & A3 & A4).
  unfold cm_src, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite !soff_lit_small by lia.
  change (bv_unsigned (eval rho (SAlu ALU_ADD vF (SLit 32)))) with (uval rho (SAlu ALU_ADD vF (SLit 32))). rewrite A4. unfold uval. lia.
Qed.

Lemma XH_X_epk : ltac2:(tb__ "0|1|
S10S2dS44Q40A1A1M0S3bG0S46S49Z37S47Z2Z40A2A2R2A2VTR;S4cS3dVJAv;Sa7A1S98R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. eapply TR_pre; [intros w Hw; exact (SPA_axforms segs _ xf_cf rho X_epk Y_epk tp w Y_epk_eq Hw)|].
  apply (X_Y_ep Y_epk C_epk _ _ vND vNK rho tp b tp0); [vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr| exact C_epk_eq | innth 16 | exact Hb].
Qed.
Lemma XH_X_epg : ltac2:(tb__ "0|1|
S10S2dS44Q40A1A1M0S3bG0S46S49Z37S47Z2Z40A2A2R2A2VTR;S4cS3dVJAv;Sa6A1S97R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. eapply TR_pre; [intros w Hw; exact (SPA_axforms segs _ xf_cf rho X_epg Y_epg tp w Y_epg_eq Hw)|].
  apply (X_Y_ep Y_epg C_epg _ _ vDg vKg rho tp b tp0); [vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr| exact C_epg_eq | innth 17 | exact Hb].
Qed.

Lemma X_X_rl : ltac2:(tb__ "0|6|
S5S5S5S2dS2eSeSeA2A1S2dS65A1S10S2dS44Q40A1A1M0S3bG0S0S35S5A1S3fR9S2cS3eS40S78A1S33S3eA1A3A2S34S5R8A2A3S0S5S8R9S15fS6R9A1M1Sf5S12UcM2S17G1A1A3A2A2R8A3S0S2fS13fP6eP78S6eZ0Sf6S12G2S17S6RaA1A1A3A5S30A3S0S2fScS2cSfS22SaS6eA1S6cA2S2cSfS14S1aS6eA1S11S4bS47Z2M3Z3dA2Z1A2A1A2S33SfA1A3A3S13S6RbA1A1A2S30A3S0S2fS54S15S6RcA1A1S52RaS6bR9S51A4A2S30A3Sf0S2eS2eS5S50A2M4S2eS3bSeA2M5A2S31G4G5S31S5S50RcS52RbS33S2eS2eSeS3bA2SeA2A1RaS51A4A4S31S3bSeZ28S10bA4A4S73A3S46S49Z2dS47G3Z40A2A2R8A2VTR;S4cS3dVJAv;S52RdS6bRcS51A4A1R10RbRaA5VFAM;R9R8A2A2F_;F_;F_;F_;F_;F_;F_;Ftp0;Fb;Ftp;Frho;Fbd;Ftv;FC;FX1;FX;").
Proof.
  intros X X1 C tv bd rho tp b tp0 HX1 HC HR Hfe Hnb HinC Hb.
  apply (TR_pre (fun w => exists rho', SPA segs (JAv (NDA tv [] bd ANone)) C rho' tp w)).
  { intros [tr [ms md]] Hw. pose proof (SPA_axforms segs _ [AXSelect sel_rel] rho X X1 tp _ HX1 Hw) as Hw1.
    exists (rho_absorb rho (skipn 12 (ss_objs (ax_S X1))) (vms md tp ms)). rewrite <- HC.
    change (ax_setS X1 (set_objs (ax_S X1) (firstn 12 (ss_objs (ax_S X1))))) with (drop_lastA X1 (firstn 12 (ss_objs (ax_S X1)))).
    change (@nil (sv * Z * sv)) with (remove_nth 0 fr_hvn).
    apply (JA_release_inline segs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nn.Lib_arena_alloc.HTOP_ok AInv CST XGL ALA HCST HXGL LFLAG LFSH NF Kc rho0 (P0_hvn CST FB FF) FB FF BX PTrue HKc HBX HNP
             tv fr_hvn bd ANone 0%nat 110%positive 0 120%positive gF X1 (firstn 12 (ss_objs (ax_S X1))) (skipn 12 (ss_objs (ax_S X1))) rho tp tr ms md);
      [reflexivity | lia | symmetry; apply firstn_skipn | exact HR | exact Hfe | exact Hnb | intros A1 A2 _; exact I | exact Hw1]. }
  apply TR_exw. intros rho'. apply (REENTER C (NDA tv [] bd ANone) (40, z0)); [exact HinC | meas].
Qed.
Lemma XH_X_rlk : ltac2:(tb__ "0|1|
S10S2dS44Q40A1A1M0S3bG0S46S49Z2dS47Z2Z40A2A2R2A2VTR;S4cS3dVJAv;Sa7A1S9eR5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply (X_X_rl X_rlk _ C_rlk _ _ rho tp b tp0 X_rlk_eq); [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | innth 20 | exact Hb].
Qed.
Lemma XH_X_rlg : ltac2:(tb__ "0|1|
S10S2dS44Q40A1A1M0S3bG0S46S49Z2dS47Z2Z40A2A2R2A2VTR;S4cS3dVJAv;Sa6A1S9dR5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply (X_X_rl X_rlg _ C_rlg _ _ rho tp b tp0 X_rlg_eq); [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | innth 21 | exact Hb].
Qed.
Lemma XH_X_rlf0 : ltac2:(tb__ "0|1|
S10S2dS44Q40A1A1M0S3bG0S46S49Z2dS47Z2Z40A2A2R2A2VTR;S4cS3dVJAv;S7dA1S9bR5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply (X_X_rl X_rlf0 _ C_rlf0 _ _ rho tp b tp0 X_rlf0_eq); [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | innth 22 | exact Hb].
Qed.
Lemma XH_X_rlf1 : ltac2:(tb__ "0|1|
S10S2dS44Q40A1A1M0S3bG0S46S49Z2dS47Z2Z40A2A2R2A2VTR;S4cS3dVJAv;S7dA1S9cR5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply (X_X_rl X_rlf1 _ C_rlf1 _ _ rho tp b tp0 X_rlf1_eq); [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | innth 23 | exact Hb].
Qed.

Lemma X_P_ok : ltac2:(tb__ "0|1|
S10S2dS44Q40A1A1M0S3bG0VTR;S4cS3dVJAv;S86A1S80R4R3A5VFAM;R2R1A2A2Ftp0;Fb;Ftp;Frho;").
Proof. intros. apply POST. innth 0. Qed.
Lemma X_P_fail : ltac2:(tb__ "0|1|
S10S2dS44Q40A1A1M0S3bG0VTR;S4cS3dVJAv;S85A1S7fR4R3A5VFAM;R2R1A2A2Ftp0;Fb;Ftp;Frho;").
Proof. intros. apply POST. innth 1. Qed.

Lemma exits_okT : ltac2:(tb__ "0|3|
S5S50S2eS3bSeA2M0S10S2dS44Q40A1A1M1G1Sf0S2eS2eS5S50A2M2G0A2S31G2G0S31S5S50R6R5A4R4A4Sa5A3VTR;S4cS3dVJAv;R6A1R7R4R3A5VFAM;S5cS31G2G0S31S5S50R7R6A4R5A4R4A2R2A2A2F_;Ftp0;Ftp;Frho;FrvX;FndX;FX;").
Proof.
  intros X ndX rvX rho tp tp0 Hin. cbn [In exitsH] in Hin.
  destruct Hin as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[]]]]]]]]]]]]]]]]]; injection H as <- <- <-.
  - apply XH_E_sm. meas. - apply XH_X_rel. meas. - apply XH_E_A. meas. - apply XH_E_B. meas. - apply XH_E_C. meas.
  - apply XH_E_vr. meas.
  - apply XH_X_epk. meas. - apply XH_X_epg. meas. - apply XH_X_epf0. meas. - apply XH_X_epf1. meas.
  - apply XH_X_rlk. meas. - apply XH_X_rlg. meas. - apply XH_X_rlf0. meas. - apply XH_X_rlf1. meas.
  - apply X_P_ok. - apply X_P_fail.
Qed.
End X.

Lemma ejcertH_ok : ltac2:(tb__ "0|0|
S0S2fS5fS3dS63Sb7Sc6P64S73Sa5A7S30A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Section Safety.
Variable ok : world -> Prop.
Hypothesis Hok : ltac2:(tb__ "0|0|
S62S3dVKc;Vok;A3").
Hypothesis AC : ltac2:(tb__ "0|0|
S149S3dS141VAInv;VCST;VXGL;A5").

Theorem handle_vn_sum : ltac2:(tb__ "0|0|
S2dS44Q40A1A1S11fS3dVok;S4cS3dS58VAInv;VCST;VXGL;VKc;Sd0VCST;VFB;VFF;A3VFB;VFF;VBX;S53S84AaS8eVrho0;R1A5Se9S3dS63Vrho0;R1S137A5A4Ftp0;").
Proof.
  intros tp0.
  eapply triple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_sound_JA segs AInv CST XGL NF Kc rho0 (P0_hvn CST FB FF) FB FF BX PTrue HKc ALA FUEL_hvn cutpcs_hvn 100
                (map edropA cutsH) (map edropA exitsH) ok (Q tp0) Hok (ejcertA_jcertA segs NF _ _ _ _ _ ejcertH_ok))
         with (ndT := nd0); [|left; reflexivity].
       intros X ndX rho tp Hin. apply in_map_iff in Hin as ([[X' nd'] rv] & E0 & Hin). cbn in E0. injection E0 as <- <-.
       apply (exits_okT (triple segs ok) (fun _ _ w => SPfamGTA segs (map nI (map edropA cutsH)) w \/ Q tp0 w)
                (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok) (@triple_ex segs ok) (call_soundPA3 segs ok)) with (rvX := rv) (tp0 := tp0).
       - intros FBc FFc BXc rho1 tp1 HB0. apply (vec_reserve_sum AInv CST XGL ALA HCST HXGL Kc HKc FBc FFc BXc HB0 rho1 ok Hok AC tp1).
       - intros Ai rho1 tp1. apply (aca_stack_malloc _ _ _ _ _ AC 0 ltac:(cbn; tauto)); [exact HKc|]. eapply ok_frameA_of_K; [exact Hok|]. intros r p t m (_ & K & _). exact K.
       - intros Ai rho1 tp1. apply (aca_asan_memset _ _ _ _ _ AC); [exact HKc|]. eapply ok_frameA_of_K; [exact Hok|]. intros r p t m (_ & K & _). exact K.
       - intros Cl s R rho1 tp1 nd Q' He Hc Hn Hb Hf Hk.
         apply (pure_callA segs AInv CST XGL NF Kc rho0 (P0_hvn CST FB FF) FB FF BX PTrue HKc ALA ok Cl Pre_sd s R Posts_sd rho1 tp1 nd Q'); try assumption.
         intros rho2 tp2. apply scan_double_sum; [apply frozen_ok_frameA; exact Hok | apply (frozen_stableA' NF (ss_next (ax_S Cl)) nd rho1); [apply Pos.leb_le; exact Hn | exact Hb]].
       - intros T nd rv' rho1 tp1 b tp2 HinT _. apply (reenter_cutJA segs AInv CST XGL NF Kc rho0 (P0_hvn CST FB FF) FB FF BX PTrue ok (map edropA cutsH) T nd).
         apply in_map_iff. exists (T, nd, rv'). auto.
       - intros P nd rho1 tp1 b tp2 HinP. apply (exit_postGA segs AInv CST XGL NF Kc (P0_hvn CST FB FF) FB FF BX PTrue ok rho0 tp0 nd Posts_hvn P). exact HinP.
       - exact Hin. }
  intros w Hw. apply JA_pre_intro. exact Hw.
Qed.
End Safety.

Section Existence.
Hypothesis ACX : ltac2:(tb__ "0|0|
S14aS3dS141VAInv;VCST;VXGL;A5").

Theorem handle_vn_sum_ex : ltac2:(tb__ "0|0|
S2dS44Q40A1A1S11eS3dS4cS3dS58VAInv;VCST;VXGL;VKc;Sd0VCST;VFB;VFF;A3VFB;VFF;VBX;S53S84AaS8eVrho0;R1A5Se9S3dS63Vrho0;R1S137A5A3Ftp0;").
Proof.
  intros tp0.
  eapply etriple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_complete_JA segs AInv CST XGL NF Kc rho0 (P0_hvn CST FB FF) FB FF BX PTrue HKc ALA FUEL_hvn cutpcs_hvn 100 cutsH exitsH (Q tp0) ejcertH_ok)
         with (ndT := nd0) (rv := (100, z0)); [|left; reflexivity].
       intros X ndX rv rho tp Hin.
       apply (exits_okT (etriple segs) (fun b _ w => SPfamETA segs (map (enodeIA AInv CST XGL NF Kc rho0 (P0_hvn CST FB FF) FB FF BX PTrue) cutsH) b w \/ Q tp0 w)
                (TRe_facts segs) (TRe_ex segs) (TRe_pre segs) (@etriple_ex segs) (call_completePA3 segs)) with (tp0 := tp0).
       - intros FBc FFc BXc rho1 tp1 HB0. apply (vec_reserve_sum_ex AInv CST XGL ALA HCST HXGL Kc HKc FBc FFc BXc HB0 rho1 ACX tp1).
       - intros Ai rho1 tp1. apply (acx_stack_malloc _ _ _ _ _ ACX 0 ltac:(cbn; tauto)). exact HKc.
       - intros Ai rho1 tp1. apply (acx_asan_memset _ _ _ _ _ ACX). exact HKc.
       - intros Cl s R rho1 tp1 nd Q' He Hc Hn Hb Hf Hk.
         apply (pure_callA_ex segs AInv CST XGL NF Kc rho0 (P0_hvn CST FB FF) FB FF BX PTrue HKc ALA Cl Pre_sd s R Posts_sd rho1 tp1 nd Q'); try assumption.
         intros rho2 tp2. apply scan_double_sum_ex. apply (frozen_stableA' NF (ss_next (ax_S Cl)) nd rho1); [apply Pos.leb_le; exact Hn | exact Hb].
       - intros T nd rv' rho1 tp1 b tp2 HinT Hm. apply (ereenter_cutJA segs AInv CST XGL NF Kc rho0 (P0_hvn CST FB FF) FB FF BX PTrue cutsH T nd rv'); [exact HinT | exact Hm].
       - intros P nd rho1 tp1 b tp2 HinP. apply (eexit_postGA segs AInv CST XGL NF Kc (P0_hvn CST FB FF) FB FF BX PTrue rho0 tp0 nd Posts_hvn P). exact HinP.
       - exact Hin. }
  intros w Hw. apply JA_pre_intro. exact Hw.
Qed.
End Existence.
End Sum.
End Lib_handle_vn_pf.

(* [comment removed for export] *)
Module Lib_intern_rest_eqs.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "ss_objs"; "sprop"; "ss_facts"; "SLit"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Init.Datatypes"; "cons"; "app"; "nil"; "list"; "Some"; "length"; "nat"; "option"; "bool"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXSelect"; "AXSplit"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.no.Lib_intern_rest"; "X_sretc2"; "X_sretn2"; "vN"; "X_fitc"; "X_fitn"; "X_ret2"; "X_sretc1"; "X_sretn1"; "E_m"; "Pre_m"; "R_m"; "X_nofit1"; "X_ret"; "fit_facts"; "new_facts"; "p_fit"; "p_new"; "s_m"; "C_open"; "FUEL_ir"; "T_mnull"; "T_mok0"; "X_fitc3"; "X_fitn3"; "X_nofit2"; "X_open"; "X_ret3"; "X_sretc"; "X_sretc3"; "X_sretn"; "X_sretn3"; "cutpcs_ir"; "cutsI"; "exitsI"; "nofit_fact"; "vHDi"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nz.Lib_intern_rest_eqs"; "objsR"; "objsNc"; "objsNn"; "ohNc"; "ohNn"; "ohR"; "sel_c"; "sel_n"; "ohFc"; "ohFn"; "osR"; "otNc"; "otNn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR"; "carve_stateA"; "drop_lastA"; "open_stateA"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "T_afterA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "AE_A"; "UStopLe"; "ulink"; "L_malloc_null"; "L_malloc_ok"; "@Stdlib.Lists.List"; "removelast"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ejcertA"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TobjJVA InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxCellA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_scan_double.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require no.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.no.Lib_intern_rest.
Module AAP. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_arena_alloc_pf. End AAP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import IRAddr RA.ReallocAddr.
Local Open Scope lazy_bool_scope.

Definition ohFc : sobj := Eval vm_compute in last (ss_objs (ax_S X_fitc)) O_Wi.
Definition ohFn : sobj := Eval vm_compute in last (ss_objs (ax_S X_fitn)) O_Wi.

Definition iNc : nat := Eval vm_compute in find_idxb (fun o => sv_eqb (ob_base o) (SVar pN)) (ss_objs (ax_S X_sretc)) 0%nat.
Definition sel_c : list nat := Eval vm_compute in (List.filter (fun j => negb (Nat.eqb j iNc)) (seq 0 (length (ss_objs (ax_S X_sretc))))) ++ [iNc].
Definition iNn : nat := Eval vm_compute in find_idxb (fun o => sv_eqb (ob_base o) (SVar pN)) (ss_objs (ax_S X_sretn)) 0%nat.
Definition sel_n : list nat := Eval vm_compute in (List.filter (fun j => negb (Nat.eqb j iNn)) (seq 0 (length (ss_objs (ax_S X_sretn))))) ++ [iNn].
Definition objsNc : list sobj := Eval vm_compute in removelast (removelast (ss_objs (ax_S X_sretc1))).
Definition ohNc : sobj := Eval vm_compute in nth (length objsNc) (ss_objs (ax_S X_sretc1)) O_Wi.
Definition otNc : sobj := Eval vm_compute in nth (S (length objsNc)) (ss_objs (ax_S X_sretc1)) O_Wi.
Definition objsNn : list sobj := Eval vm_compute in removelast (removelast (ss_objs (ax_S X_sretn1))).
Definition ohNn : sobj := Eval vm_compute in nth (length objsNn) (ss_objs (ax_S X_sretn1)) O_Wi.
Definition otNn : sobj := Eval vm_compute in nth (S (length objsNn)) (ss_objs (ax_S X_sretn1)) O_Wi.

Definition objsR : list sobj := Eval vm_compute in removelast (removelast (ss_objs (ax_S X_ret))).
Definition ohR : sobj := Eval vm_compute in nth (length objsR) (ss_objs (ax_S X_ret)) O_Wi.
Definition osR : sobj := Eval vm_compute in nth (S (length objsR)) (ss_objs (ax_S X_ret)) O_Wi.

Lemma C_open_eq : ltac2:(tb__ "0|0|
S5S10S4aS30S3aA2S29A3"). Proof. vm_compute. reflexivity. Qed.
Lemma T_mnull_eq : ltac2:(tb__ "0|0|
S5S10S4cS20S1fS28S21S50S4dS8S4fA1S4eA3A5S2bA3"). Proof. vm_compute. reflexivity. Qed.
Lemma T_mok0_eq : ltac2:(tb__ "0|0|
S5S10S4cS20S1fS28S21S51S4dS8S4fA1S4eA3A5S2cA3"). Proof. vm_compute. reflexivity. Qed.
Lemma X_nofit2_eq : ltac2:(tb__ "0|0|
S5S10S16S22S6S2S39S3S11S22A1A1A3A2S2fA3"). Proof. vm_compute. reflexivity. Qed.
Lemma objsFc_eq : ltac2:(tb__ "0|1|
S5S9S0A1S1S11S1aA1A1M0S7S0S52S0G0A2S6S0S43S8S0A1A3A3A3"). Proof. vm_compute. reflexivity. Qed.
Lemma objsFn_eq : ltac2:(tb__ "0|1|
S5S9S0A1S1S11S1bA1A1M0S7S0S52S0G0A2S6S0S44S8S0A1A3A3A3"). Proof. vm_compute. reflexivity. Qed.
Lemma X_fitc3_eq : ltac2:(tb__ "0|0|
S5S10S16S48S1aS26S19A3S7S2S24S3S11S1aA1A1A3A2S2dA3"). Proof. vm_compute. reflexivity. Qed.
Lemma X_fitn3_eq : ltac2:(tb__ "0|0|
S5S10S16S48S1bS26S19A3S7S2S24S3S11S1bA1A1A3A2S2eA3"). Proof. vm_compute. reflexivity. Qed.
Lemma X_sretc1_eq : ltac2:(tb__ "0|0|
S5SdS10A1S15S32S6S12S13S41A1S6S12S14S4bSbScS41A2U1A2S4Z18A1A2S8S12A1A3A3A2SaS10S1dA2A3"). Proof. vm_compute. reflexivity. Qed.
Lemma X_sretn1_eq : ltac2:(tb__ "0|0|
S5SdS10A1S15S34S6S12S13S42A1S6S12S14S4bSbScS42A2U1A2S4Z18A1A2S8S12A1A3A3A2SaS10S1eA2A3"). Proof. vm_compute. reflexivity. Qed.
Lemma objsNc_eq : ltac2:(tb__ "0|1|
S5S9S0A1S1S11S1dA1A1S7S0S7S0S3cS6S0S3eS8S0A1M0A3A3S6S0S46G0A3A3A3"). Proof. vm_compute. reflexivity. Qed.
Lemma objsNn_eq : ltac2:(tb__ "0|1|
S5S9S0A1S1S11S1eA1A1S7S0S7S0S3dS6S0S3fS8S0A1M0A3A3S6S0S47G0A3A3A3"). Proof. vm_compute. reflexivity. Qed.
Lemma X_sretc2_eq : ltac2:(tb__ "0|0|
S5S10S49S1dS7S0S3cS6S0S3eS8S0A1A3A3A2S17A3"). Proof. vm_compute. reflexivity. Qed.
Lemma X_sretn2_eq : ltac2:(tb__ "0|0|
S5S10S49S1eS7S0S3dS6S0S3fS8S0A1A3A3A2S18A3"). Proof. vm_compute. reflexivity. Qed.
Lemma objsNc2_eq : ltac2:(tb__ "0|0|
S5S9S0A1S1S11S17A1A1S7S0S3cS6S0S3eS8S0A1A3A3A3"). Proof. vm_compute. reflexivity. Qed.
Lemma objsNn2_eq : ltac2:(tb__ "0|0|
S5S9S0A1S1S11S18A1A1S7S0S3dS6S0S3fS8S0A1A3A3A3"). Proof. vm_compute. reflexivity. Qed.
Lemma X_sretc3_eq : ltac2:(tb__ "0|0|
S5S10S16S48S17S27S19A3S7S2S25S3S11S17A1A1A3A2S33A3"). Proof. vm_compute. reflexivity. Qed.
Lemma X_sretn3_eq : ltac2:(tb__ "0|0|
S5S10S16S48S18S27S19A3S7S2S25S3S11S18A1A1A3A2S35A3"). Proof. vm_compute. reflexivity. Qed.
Lemma objsR_eq : ltac2:(tb__ "0|1|
S5S9S0A1S1S11S23A1A1S7S0S7S0S3bS6S0S40S8S0A1M0A3A3S6S0S45G0A3A3A3"). Proof. vm_compute. reflexivity. Qed.
Lemma X_ret2_eq : ltac2:(tb__ "0|0|
S5S10S49S23S7S0S3bS6S0S40S8S0A1A3A3A2S1cA3"). Proof. vm_compute. reflexivity. Qed.
Lemma objsR2_eq : ltac2:(tb__ "0|0|
S5S9S0A1S1S11S1cA1A1S7S0S3bS6S0S40S8S0A1A3A3A3"). Proof. vm_compute. reflexivity. Qed.
Lemma X_ret3_eq : ltac2:(tb__ "0|0|
S5S10S49S1cS3bA2S31A3"). Proof. vm_compute. reflexivity. Qed.
Lemma ejcertI_ok : ltac2:(tb__ "0|0|
S5SeS55S53S54S2aS36P64S37S38A7SfA3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End Lib_intern_rest_eqs.

(* [comment removed for export] *)
Module Lib_intern_rest_pf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "or"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "bool"; "true"; "cons"; "list"; "prod"; "pair"; "nil"; "app"; "false"; "fst"; "snd"; "Some"; "nat"; "option"; "None"; "length"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sv"; "valuation"; "SLit"; "SPUle"; "sobj"; "ss_facts"; "SAlu"; "ss_next"; "sprop_eqb"; "SVar"; "sv_eqb"; "holds"; "SPBranch"; "ob_base"; "ob_hi"; "ob_lo"; "ss_objs"; "sv_below"; "obj_range"; "cell"; "ob_dflt"; "sprop_below"; "swf"; "DUnknown"; "SPNot"; "dflt_writable"; "odefault"; "rw"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "pow"; "mul"; "lt"; "sub"; "opp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_X"; "entailsA"; "ax_base"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "uval"; "bitem"; "BI"; "batom"; "ASv"; "KU"; "bd_subst"; "bud_le"; "bd_wpos"; "bsumK"; "bsumV"; "bd_nn"; "bud_pay"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "O_got"; "O_rtc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.no.Lib_intern_rest"; "vN"; "vHDi"; "vCAP"; "tv_ir"; "vBld"; "vK"; "p_fit"; "vU"; "p_new"; "bd_slow"; "nd0"; "ndO"; "vARi"; "vCu"; "P_fail"; "P_ok"; "X_ir"; "am_np"; "bd_m2"; "cutsI"; "ndF"; "ndK"; "ndL"; "ndMok"; "ndS"; "s_m"; "vC1"; "vC2"; "vDp"; "vUg"; "E_m"; "O_cu"; "P_b8"; "Pre_ir"; "R_m"; "am_loop"; "bd_loop"; "bd_open"; "fit_facts"; "ndKc"; "new_facts"; "spm"; "two40"; "vLEN"; "CHi"; "CHn"; "C_K"; "O_Wi"; "X_K1"; "X_K2"; "X_fitc"; "X_fitn"; "X_nofit"; "X_nohead"; "X_open"; "X_ret"; "X_sretc"; "X_sretn"; "bd_K"; "bd_m"; "exitsI"; "pN"; "vNX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "smatchA"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_GE"; "BC_EQ"; "BC_GEU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "PTrue"; "potK"; "potV"; "NDA"; "am_eqb"; "am_subst"; "nd_below"; "AOpen"; "JA_pre"; "emeasA"; "JA"; "JLA"; "nodeIA"; "ok_frameKA"; "@Stdlib.Lists.List"; "existsb"; "In"; "forallb"; "removelast"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nz.Lib_intern_rest_pf"; "P0_ir"; "baseFI"; "basezI"; "ccF"; "objclass"; "openF"; "base_factsI"; "cc_facts"; "open_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double"; "vB"; "vL"; "vE"; "vI"; "O_txt"; "two26"; "two47"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "J_ofPA"; "call_checkPA"; "entails_frA"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR"; "carve_stateA"; "e32"; "POT"; "xrs_ok47"; "drop_lastA"; "robjs_okF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "rho_sub"; "wsub"; "wsub_id_below"; "wsub_get"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "pclMA"; "xr_eqb"; "FFx";
"@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nz.Lib_intern_rest_pf.Sum"; "Posts_ir"; "JL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "AE_A"; "UStopLe"; "ulink"; "J_alloc_pre"; "Posts_malloc"; "Pre_malloc"; "V_TOP"; "alloc_contractsA"; "alloc_contractsA_ex"; "alloc_lawsA"; "unwind_stopJ"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "uleq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "tv_sub_eqb"; "FBx"; "T0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXSelect"; "AXSplit"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA"; "infrFF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "payA"; "site_okA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "SHADOW_OFF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "call_linkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "jnodeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVA"; "hdr_shape"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3"; "import_okPA3"; "import_postA3"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TobjJVA InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxCellA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Code Lib_scan_double.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require no.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.no.Lib_intern_rest OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nz.Lib_intern_rest_eqs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import IRAddr ScanDoubleAddr RA.ReallocAddr.
Local Open Scope lazy_bool_scope.

Definition P0_ir (CST : list (Z * Z)) (FB : list (Z * Z)) (FF : list (Z * Z * Z)) (r : valuation) : Prop := ltac2:(tb__ "0|1|
S1S3S1S31S3dVr;Sb2A2M0R1A2S35R1S32G0S3dVr;Sb3A2A2A2A2Sd0VCST;Vr;VFB;VFF;R2A5F_;Fa;SedVFF;S3dVr;S51A2Z518A3A2").

Definition is_xo (o : sobj) : bool := ltac2:(tb__ "0|4|
S4S4L_;M0G0S1fS22Vo;A1M1S51A2G0S1fS24Vo;A1M2S17Z8A1A2S1fS23Vo;A1M3S17Z10A1A2ScX4x2ScX4x2S5G0S1fG1Sb2A2G0S1fG2S17Z0A1A2S1fG3Sb3A2ScX4x2ScX4x2X4x2").
Definition is_xX (r : sv * sv) : bool := ltac2:(tb__ "0|0|
S4S4L_;Sd1Vr;S9S15S15S51S17Z518A1A4A2S5Sd1Vr;S9S15S15Sb2Sb3A4A2X4x2").

Definition base_factsI : list sprop := ltac2:(tb__ "0|5|
S6S14S18S1ePaA1M0S17Sb8A1M1A2S6S14S18S1eP1eA1M2S1bS91S76Z70A1M3S69A3A2S6S14S18G2G3A2S6S14S18G2G0A2S6S14S21S92S17N1000A1S69A3S6S14S21S92S69S17S37S77A1A1A3S6S14S18S17Sf0A1S51A2S6S14S18S1bS91S51S17Z518A1A3G2A2S6S14S18S17Z1000A1S59A2S6S14S18S1bS91S59S17Z40A1A3G2A2S6S14S18Sb5Sb4A2S6S14S18Sb4Sb3A2S6S14S18Sb3S17Sb7A1A2S6S14S18S17Z1A1Sb2A2S6S14S18S1bS91Sb2Sb3A3S17Z7fffff800000A1M4A2S6S14S18S51G1A2S6S14S18S59G1A2S6S14S18Sb2G1A2S6S14S18S17Z7fff7f800000A1G2A2S6S14S18G2G4A2S6S14S18G2S5aA2S6S14S18S1bS91S5aS17Z10A1A3G1A2S6S14S18S5aG1A2SaS14A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition baseFI (F : list sprop) : bool := ltac2:(tb__ "0|0|
Sa7S14S14Sa5S14S1dR1A1VF;A3Lp;SafA3").
Record basezI (rho : valuation) : Prop := BZI {
  bz_sp : aceil + 112 <= uval rho (SVar 10) <= 2 ^ 47;
  bz_win : forall a, fst (obj_range rho O_Wi) <= a < snd (obj_range rho O_Wi) -> bv_unsigned (rw rho V_TOP) <= a < uval rho (SVar 10) - 112;
  bz_b : IMG_HI <= uval rho vBld /\ uval rho vBld + 1304 <= bv_unsigned (rw rho V_TOP);
  bz_ar : 4096 <= uval rho vARi /\ uval rho vARi + 64 <= bv_unsigned (rw rho V_TOP);
  bz_txt : uval rho vI <= uval rho vE /\ uval rho vE <= uval rho vL /\ uval rho vL <= 2 ^ 26;
  bz_B : 1 <= uval rho vB /\ uval rho vB + uval rho vL <= 140737479966720;

  bz_top : bv_unsigned (rw rho V_TOP) + 112 <= uval rho (SVar 10) /\ 140735332483072 <= bv_unsigned (rw rho V_TOP) <= 140737479966720;
  bz_cu : bv_unsigned (rw rho V_TOP) <= uval rho vCu /\ uval rho vCu + 16 <= 2 ^ 47 }.
Lemma uval_spm80 : ltac2:(tb__ "0|2|
S16S31Z70M0S3dR1S1ePaA1M1A2A2S0S3S3dR2S76G0A1A2S36S3dR2G1A2G0A2A3F_;Frho;").
Proof.
  intros rho Hk. unfold spm, RA.spm, uval in *. rewrite U_add, U_lit. pose proof (U_range (eval rho (SVar 10))) as R. unfold M64v in *.
  set (x := bv_unsigned (eval rho (SVar 10))) in *.
  rewrite Zplus_mod_idemp_r. replace (x + - 112) with (x - 112) by lia. apply Z.mod_small. lia.
Qed.
Lemma basezI_of : ltac2:(tb__ "0|0|
S16S7S14A1SbeS14S20R2A1R1A3S0S4SaaR2A1S5A3SabR4A1F_;F_;FF;Frho;").
Proof.
  intros rho F HF HB. unfold baseFI in HB.
  assert (G : forall p, In p base_factsI -> holds rho p).
  { intros p Hp. apply (holds_mem rho F p HF). exact (proj1 (forallb_forall _ _) HB p Hp). }
  cbn [base_factsI] in G.
  pose proof (G _ ltac:(left; reflexivity)) as F1. pose proof (G _ ltac:(do 1 right; left; reflexivity)) as F2.
  pose proof (G _ ltac:(do 2 right; left; reflexivity)) as F3. pose proof (G _ ltac:(do 3 right; left; reflexivity)) as F4.
  pose proof (G _ ltac:(do 4 right; left; reflexivity)) as F5. pose proof (G _ ltac:(do 5 right; left; reflexivity)) as F6.
  pose proof (G _ ltac:(do 6 right; left; reflexivity)) as F7. pose proof (G _ ltac:(do 7 right; left; reflexivity)) as F8.
  pose proof (G _ ltac:(do 8 right; left; reflexivity)) as F9. pose proof (G _ ltac:(do 9 right; left; reflexivity)) as F10.
  pose proof (G _ ltac:(do 10 right; left; reflexivity)) as F11. pose proof (G _ ltac:(do 11 right; left; reflexivity)) as F12.
  pose proof (G _ ltac:(do 12 right; left; reflexivity)) as F13. pose proof (G _ ltac:(do 13 right; left; reflexivity)) as F14.
  pose proof (G _ ltac:(do 14 right; left; reflexivity)) as F15. pose proof (G _ ltac:(do 15 right; left; reflexivity)) as F16.
  pose proof (G _ ltac:(do 16 right; left; reflexivity)) as F17. pose proof (G _ ltac:(do 17 right; left; reflexivity)) as F18.
  pose proof (G _ ltac:(do 18 right; left; reflexivity)) as F19. pose proof (G _ ltac:(do 19 right; left; reflexivity)) as F20.
  pose proof (G _ ltac:(do 20 right; left; reflexivity)) as F21. pose proof (G _ ltac:(do 21 right; left; reflexivity)) as F22. pose proof (G _ ltac:(do 22 right; left; reflexivity)) as F23.
  rewrite h_ule in F1, F2, F3, F4, F7, F8, F9, F10, F11, F12, F13, F14, F15, F16, F17, F18, F19, F20, F21, F22, F23.
  apply (proj1 (holds_bge _ _ _)) in F5. apply (proj1 (holds_bge _ _ _)) in F6.
  repeat change (bv_unsigned (eval ?r ?e)) with (uval r e) in *.
  change (uval rho (SVar 30)) with (bv_unsigned (rw rho V_TOP)) in *.
  unfold two47, two26, two40, RA.two40 in *. unfold IMG_HI in *.
  rewrite !uval_lit in F1, F7, F9, F13, F14, F16, F17, F18, F19, F20 by lia. rewrite uval_lit in F15 by lia.
  change (uval rho (SLit (-4096))) with (bv_unsigned (eval rho (SLit (-4096)))) in F5. rewrite U_lit in F5. change ((-4096) mod M64v) with 18446744073709547520 in F5.
  change (uval rho (SLit (- 2 ^ 40))) with (bv_unsigned (eval rho (SLit (- 2 ^ 40)))) in F6. rewrite U_lit in F6.
  change ((- 2 ^ 40) mod M64v) with 18446742974197923840 in F6.
  pose proof (uval_range rho vBld) as Rb. pose proof (uval_range rho vARi) as Rar. pose proof (uval_range rho vB) as RB. pose proof (uval_range rho vL) as RL.
  rewrite uval_add_small in F8 by (rewrite uval_lit by lia; lia). rewrite uval_lit in F8 by lia.
  rewrite uval_lit in F23 by lia. rewrite uval_add_small in F22 by (rewrite uval_lit by lia; lia). rewrite !uval_lit in F22 by lia.
  rewrite uval_add_small in F10 by (rewrite uval_lit by lia; lia). rewrite uval_lit in F10 by lia.
  rewrite uval_add_small in F15 by lia.
  rewrite uval_spm80 in F3 by lia.
  pose proof (uval_range rho vDp) as RD.
  destruct (Zsigned_spec (uval rho vDp)) as [[L1 E1]|[L1 E1]]; rewrite E1 in F5, F6;
    [destruct (Zsigned_spec 18446744073709547520) as [[? E2]|[? E2]]; rewrite E2 in F5; lia|].
  destruct (Zsigned_spec 18446744073709547520) as [[? E2]|[? E2]]; rewrite E2 in F5; [lia|].
  destruct (Zsigned_spec 18446742974197923840) as [[? E3]|[? E3]]; rewrite E3 in F6; [lia|].
  assert (EA : uval rho (SAlu ALU_ADD (spm 112) vDp) = uval rho (SVar 10) - 112 + (uval rho vDp - 2 ^ 64)).
  { unfold uval at 1. rewrite U_add. change (bv_unsigned (eval rho (spm 112))) with (uval rho (spm 112)). change (bv_unsigned (eval rho vDp)) with (uval rho vDp).
    rewrite uval_spm80 by lia. unfold M64v.
    replace (uval rho (SVar 10) - 112 + uval rho vDp) with ((uval rho (SVar 10) - 112 + (uval rho vDp - 2 ^ 64)) + 1 * 2 ^ 64) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
  rewrite EA in F2.
  constructor; unfold aceil, IMG_HI; try lia.
  intros a Hr. unfold obj_range, obj_lo_of, obj_hi_of, O_Wi in Hr. cbn [ob_base ob_lo ob_hi fst snd] in Hr.
  rewrite soff_lit_small in Hr by lia. change (bv_unsigned (eval rho (spm 112))) with (uval rho (spm 112)) in Hr. rewrite uval_spm80 in Hr by lia.
  unfold soff in Hr. rewrite bv_signed_U in Hr. change (bv_unsigned (eval rho vDp)) with (uval rho vDp) in Hr. rewrite E1 in Hr. lia.
Qed.
Ltac basez_tac HF := exact (basezI_of _ _ HF ltac:(vm_compute; reflexivity)).

Lemma P0_now : ltac2:(tb__ "0|3|
S7S8S3S3A2M0A1M1G1S7S8G0S3A2A1S16S16Sa9R5R4R3R2A4Sf4S95R3R2A3S1S3S1S31S3dR4Sb2A2M2R1A2S35R1S32G2S3dR4Sb3A2A2A2A2Sd0R9R6R8R7R2A5F_;Fa;SedR5S3dR3S51A2Z518A3A2F_;F_;Frho;Frho0;FFF;FFB;FCST;").
Proof.
  intros CST FB FF rho0 rho [HT Hb] [Hav _]. unfold uval in *. cbn [eval vB vL vBld] in *.
  rewrite <- (Hav 15%positive) by reflexivity. rewrite <- (Hav 18%positive) by reflexivity. rewrite <- (Hav 12%positive) by reflexivity.
  split; [exact HT | exact Hb].
Qed.
Lemma pclMA_x : ltac2:(tb__ "0|2|
S7S8S3S3A2M0A1M1S16G1S7S8G0S3A2A1S16S7S8S15S15A2A1S7S8S8S15S3A2S15A2A1S3Sd0R8R7R6R5R1A5Sd0R9R8Se7R7R5R4A3Sd2R6R5R3A3R2A5F_;Fa;Ffr;Ftv;Frho;FFF;FFB;Frho0;FCST;").
Proof.
  intros CST rho0 FB FF rho tv fr a [H|[H|[(b & n & Hin & Hr)|(f & s & fl & Hin & Hr)]]]; [left; exact H | right; left; exact H | |].
  - right; right; left. exists b, n. split; [apply In_FBx; left; exact Hin | exact Hr].
  - right; right; right. exists f, s, fl. split; [apply In_FFx; left; exact Hin | exact Hr].
Qed.
Lemma txt_range : ltac2:(tb__ "0|2|
S16S3SabR2A1S1S31SdS3S3S27R3Sb6SaS28A1A1A2M0A3R2A2S35R2SeS3S3G0A3A2A2S1S31S3dR4Sb2A2M1R3A2S35R3S32G1S3dR4Sb3A2A2A2A2F_;F_;Fa;Frho;").
Proof.
  intros rho a BZ Hr. destruct BZ as [_ _ _ _ T1 T2 TT _]. unfold obj_range, obj_lo_of, obj_hi_of, O_txt in Hr. cbn [ob_base ob_lo ob_hi fst snd] in Hr.
  rewrite soff_lit_small in Hr by lia. rewrite (soff_smallu rho vL) in Hr by lia. unfold uval in *. lia.
Qed.
Lemma b8_range : ltac2:(tb__ "0|2|
S16S3SabR2A1S1S31SdS3S3S27R3S6dA2M0A3R2A2S35R2SeS3S3G0A3A2A2S1S31S3dR4S51A2M1R3A2S35R3S32G1Z518A2A2A2F_;F_;Fa;Frho;").
Proof. intros rho a BZ Hr. unfold P_b8 in Hr. apply range_lit' in Hr; lia. Qed.
Lemma cu_range : ltac2:(tb__ "0|2|
S16S3SabR2A1S1S31SdS3S3S27R3S6cA2M0A3R2A2S35R2SeS3S3G0A3A2A2S1S31S3dR4S5aA2M1R3A2S35R3S32G1Z10A2A2A2F_;F_;Fa;Frho;").
Proof. intros rho a BZ Hr. unfold O_cu in Hr. apply range_lit' in Hr; lia. Qed.

Definition objclass (o : sobj) : Prop := ltac2:(tb__ "0|5|
S2S1S0S15S22Vo;A1M0S1ePaA1A3S1S0S15S24Vo;A1M1S17N70A1A3S1S0S15S23Vo;A1M2S17Z0A1M3A3S0S2fS29Vo;A1S2cA3M4A2A2A2S2S0S19Vo;S7cA3S2S0S19Vo;S6dA3S2S1S0S15G0S59A3S1S0S15G1G3A3S1S0S15G2S17Z40A1A3G4A2A2A2S2S2S0S19Vo;S4bA3S0S19Vo;S4cA3A2S2S0S19Vo;Sb6SaS28A1A1A3S0S19Vo;S6cA3A2A2A2A2A2A2").
Lemma objs_ok_ir : ltac2:(tb__ "0|3|
S7S8S3S3A2M0A1M1S16G1S7S8G0S3A2A1S16S7S19A1SabR2A1S3S1S31S3dR4Sb2A2M2R1A2S35R1S32G2S3dR4Sb3A2A2A2A2Sd0R9R8R7R6R2A5F_;Fa;SedR5S3dR4S51A2Z518A3S19Sa6S19R1R5A3SadR2A1F_;Fo;S0S3Se8R9A1S90Q40S30R6SdeA2A2A3ScaRbRaR9R8R7S50SaS8S8S15S3A2S15A2A1R6A8F_;F_;F_;F_;F_;Fobjs;Frho;FFF;FFB;Frho0;FCST;").
Proof.
  intros CST rho0 FB FF rho objs BZ HT Hb Hcls ET o a Ho Hr. pose proof BZ as [Bsp Bwin Bb Bar Btxt BB Btop Bcu].
  destruct (Hcls o Ho) as [(H1 & H2 & H3 & H4)|[->|[->|[(H1 & H2 & H3 & H4)|[[->| ->]|[->| ->]]]]]].
  - left. left. destruct o as [ob olo ohi oc od]. cbn [ob_base ob_lo ob_hi ob_dflt] in H1, H2, H3, H4. subst.
    apply range_lit' in Hr; [|lia|lia]. lia.
  - left. left. pose proof (Bwin a Hr). lia.
  - left. apply pclMA_x. eapply (infrFF_pclMA CST rho0 FF FB rho) in Hb; [| exact (b8_range rho a BZ Hr)].
    unfold FFx in Hb. cbn [map] in Hb. rewrite app_nil_r in Hb. exact Hb.
  - left. right; right; left. exists (uval rho vARi), 64. split.
    + apply In_FBx. right. exists (vARi, SLit 64). split; [left; reflexivity|]. split; [unfold tnz; cbn [fst]; unfold uval in Bar; lia|].
      unfold tvv. cbn [fst snd]. unfold uval. rewrite U_lit. reflexivity.
    + destruct o as [ob olo ohi oc od]. cbn [ob_base ob_lo ob_hi ob_dflt] in H1, H2, H3, H4. subst. apply range_lit' in Hr; [|lia|lia]. lia.
  - right. unfold obj_range, obj_lo_of, obj_hi_of, O_got in Hr. cbn [ob_base ob_lo ob_hi fst snd eval] in Hr. unfold GOT_LO, GOT_HI in Hr.
    rewrite lit_unsigned, !soff_lit_small in Hr by lia. unfold IMG_HI. change (0 mod 2 ^ 64) with 0 in Hr. lia.
  - right. unfold obj_range, obj_lo_of, obj_hi_of, O_rtc in Hr. cbn [ob_base ob_lo ob_hi fst snd eval] in Hr. unfold RTC_LO, RTC_HI in Hr.
    rewrite lit_unsigned, !soff_lit_small in Hr by lia. unfold IMG_HI. change (0 mod 2 ^ 64) with 0 in Hr. lia.
  - left. apply pclMA_x. apply HT. exact (txt_range rho a BZ Hr).
  - left. left. pose proof (cu_range rho a BZ Hr) as Hcr. lia.
Qed.

Definition cc_facts : list sprop := ltac2:(tb__ "0|0|
S6S14S18Sb5S67A2S6S14S18S67S68A2S6S14S18S68Sb4A2SaS14A1A3A3A3").
Definition ccF (F : list sprop) : bool := ltac2:(tb__ "0|0|
Sa7S14S14Sa5S14S1dR1A1VF;A3Lp;Sb0A3").
Lemma nval : ltac2:(tb__ "0|8|
S16S7S14A1SbeS14S20R2A1R1A3S0S4SaaR2A1S5A3S0S4SacR3A1S5A3S1S31S3dR5Sb5A2M0S3dR5S67A2M1A2S1S31G1S3dR5S68A2M2A2S1S31G2S3dR5Sb4A2M3A2S1S0S3S3dR5S78A2S36G2G1A2M4A3S1S0S3S3dR5S4dA2M5S32G4Z1M6A2A3S1S1S31G6G5A2S31G5S32S36G3G0A2G6A2A2A2S1S31G5S33Z2M7Z1bA2A2S31G3S33G7Z1aA2A2A2A2A2A2A2A2A2F_;F_;F_;FF;Frho;").
Proof.
  intros rho F HF HB HC. pose proof (uval_range rho vI). pose proof (basezI_of rho F HF HB) as [_ _ _ _ [T1 [T2 T3]] _ _].
  unfold ccF in HC.
  assert (G : forall p, In p cc_facts -> holds rho p).
  { intros p Hp. apply (holds_mem rho F p HF). exact (proj1 (forallb_forall _ _) HC p Hp). }
  cbn [cc_facts] in G.
  pose proof (G _ ltac:(left; reflexivity)) as F1. pose proof (G _ ltac:(do 1 right; left; reflexivity)) as F2.
  pose proof (G _ ltac:(do 2 right; left; reflexivity)) as F3.
  rewrite h_ule in F1, F2, F3.
  pose proof (uval_range rho vC1) as R1. pose proof (uval_range rho vC2) as R2.
  assert (EL : uval rho vLEN = uval rho vC2 - uval rho vC1).
  { unfold vLEN, uval. rewrite U_sub. change (bv_unsigned (eval rho vC2)) with (uval rho vC2). change (bv_unsigned (eval rho vC1)) with (uval rho vC1).
    unfold M64v. apply Z.mod_small. lia. }
  assert (EN : uval rho vN = uval rho vC2 - uval rho vC1 + 1).
  { unfold vN. fold vLEN. rewrite uval_add_small by (rewrite EL, uval_lit by lia; lia). rewrite EL, uval_lit by lia. lia. }
  repeat split; lia.
Qed.

Lemma xrs47_ir : ltac2:(tb__ "0|0|
S16SabR1A1Sc8R2S5dA2F_;Frho;").
Proof.
  intros rho [_ _ [B1 B2] [A1 A2] _ [T1 T2] [BT1 BT2] [C1 C2]] r a Hr Ha. unfold IMG_HI in *.
  assert (HX : In r [(vBld, SLit 1304); (vARi, SLit 64); (vB, vL); (vCu, SLit 16)]) by exact Hr. clear Hr.
  destruct HX as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Ha; rewrite ?uval_lit in Ha by lia; lia.
Qed.
Lemma xrs47_cons : ltac2:(tb__ "0|1|
S16S15S15S7S8S15S15A2M0A1S31S32S3dR4R3A2S32S3dR4R2A2Z20A2A2Z7fffff800000A2Sc8R5R2A2Sc8R6S6G0S9S15S15R5Sc6R4A1A4R3A3A2F_;F_;FX;Fc;Fh;Frho;").
Proof.
  intros rho h c X Hh HX r a [<-|Hr] Ha; [|exact (HX r a Hr Ha)]. cbn [fst snd] in Ha.
  pose proof (uval_range rho c). pose proof (uval_range rho h). unfold e32 in Ha.
  rewrite uval_add_small in Ha by (rewrite uval_lit by lia; lia). rewrite uval_lit in Ha by lia. lia.
Qed.

Definition open_facts : list sprop := ltac2:(tb__ "0|1|
S6S14S18S4eS1eP1eA1M0A2S6S14S18S54S4fA2S6S14S18S4fS17S36S33Z2Z28A2Z21A2A1A2S6S14S18S17Z10000A1S4fA2S6S14S18S1bS91S4eSc6S4fA1A3G0A2S6S14S18S17Z1000A1S4eA2S6S14S18G0S17Z7fffff800000A1A2SaS14A1A3A3A3A3A3A3A3").
Definition openF (F : list sprop) : bool := ltac2:(tb__ "0|0|
Sa7S14S14Sa5S14S1dR1A1VF;A3Lp;Sb1A3").
Lemma openz : ltac2:(tb__ "0|7|
S16S7S14A1SbeS14S20R2A1R1A3S0S4SaeR2A1S5A3S1S31S3dR4S4eA2M0Z7fffff800000M1A2S1S31S3dR4S54A2S3dR4S4fA2M2A2S1S31G2S36S33Z2Z28A2Z21A2A2S1S31Z10000G2A2S1S31S32G0S32G2Z20A2M3A2M4S3dR4S1eP1eA1A2M5A2S1S1S31Z1000G0A2S31G5G1A2A2S1S0S3S3dR4Sc6S4fA1M6A2G3A3S0S3S3dR4S1bS91S4eG6A3A2G4A3A2A2A2A2A2A2A2F_;F_;FF;Frho;").
Proof.
  intros rho F HF HB. unfold openF in HB.
  assert (G : forall p, In p open_facts -> holds rho p).
  { intros p Hp. apply (holds_mem rho F p HF). exact (proj1 (forallb_forall _ _) HB p Hp). }
  cbn [open_facts] in G.
  pose proof (G _ ltac:(left; reflexivity)) as F1. pose proof (G _ ltac:(do 1 right; left; reflexivity)) as F2.
  pose proof (G _ ltac:(do 2 right; left; reflexivity)) as F3. pose proof (G _ ltac:(do 3 right; left; reflexivity)) as F4.
  pose proof (G _ ltac:(do 4 right; left; reflexivity)) as F5. pose proof (G _ ltac:(do 5 right; left; reflexivity)) as F6.
  pose proof (G _ ltac:(do 6 right; left; reflexivity)) as F7.
  rewrite h_ule in F1, F2, F3, F4, F5, F6, F7. rewrite !uval_lit in F3, F4, F6, F7 by lia.
  pose proof (uval_range rho vHDi) as R1. pose proof (uval_range rho vCAP) as R3.
  assert (EK : uval rho (e32 vCAP) = uval rho vCAP + 32) by (unfold e32; rewrite uval_add_small by (rewrite uval_lit by lia; lia); rewrite uval_lit by lia; lia).
  assert (EH : uval rho (SAlu ALU_ADD vHDi (e32 vCAP)) = uval rho vHDi + (uval rho vCAP + 32)) by (rewrite uval_add_small by (rewrite EK; lia); rewrite EK; lia).
  rewrite EH in F5. repeat split; lia.
Qed.
Ltac openz_tac HF := exact (openz _ _ HF ltac:(vm_compute; reflexivity)).

Lemma uval_add_comm : ltac2:(tb__ "0|0|
S16S15S15S0S3S3dR3S1bS91R2R1A3A2S3dR3S1bS91R1R2A3A2A3Fb;Fa;Frho;").
Proof. intros rho a b. unfold uval. rewrite !U_add. f_equal. lia. Qed.
Lemma fit_arith : ltac2:(tb__ "0|7|
S16S31S3dR1S4eA2Z7fffff800000A2S31S3dR2S54A2S3dR2S4fA2A2S31S3dR3S4fA2S36S33Z2M0Z28A2Z21A2A2S1S31Z1S3dR4S4dA2M1A2S31G1S33G0Z1bA2A2A2S1S0S3S3dR5S53A2M2S32S32S3dR5S4eA2M3S3dR5S54A2M4A2Z20M5A2A3S1S0S3S3dR5S1bS91S53S4dA3A2S32G2S3dR5S4dA2M6A2A3S1S0S3S3dR5S1bS91S54S4dA3A2S32G4G6A2A3S0S3S3dR5S1bS91S4eS17G5A1A3A2S32G3G5A2A3A2A2A2F_;F_;F_;F_;Frho;").
Proof.
  intros rho Hh Hu Hc Hn.
  pose proof (uval_range rho vHDi) as R1. pose proof (uval_range rho vU) as R2. pose proof (uval_range rho vCAP) as R3. pose proof (uval_range rho vN) as R4.
  assert (EP : uval rho p_fit = uval rho vHDi + uval rho vU + 32).
  { unfold p_fit. rewrite uval_add_small by (rewrite uval_add_small by (rewrite uval_lit by lia; lia); rewrite uval_lit by lia; lia).
    rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia. lia. }
  split; [exact EP|]. split; [rewrite uval_add_small by lia; lia|]. split; [rewrite uval_add_small by lia; lia|].
  rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia. lia.
Qed.

Lemma sums_slow : ltac2:(tb__ "0|2|
S16S1S0S3S47S56R1A2S32S99S3dR1S6aA2M0A1S32S34Z2S3dR1S4dA2M1A2Z60A2A2A3S0S3S46S56R1A2S32S98G0A1S32S34Z4G1A2Z40A2A2A3A2Fr;").
Proof.
  intros r. unfold bd_slow. rewrite bsumV_app, bsumK_app. destruct (POT_vals r vUg) as (-> & -> & _).
  unfold CHn. cbn [bsumV bsumK bi_v bi_k]. unfold bival. cbn [lfval aval bi_f bi_c]. lia.
Qed.
Lemma sums_K : ltac2:(tb__ "0|7|
S16S15S1S0S3S47SbS3eS6S3eS3fZ1M0Z0M1S6S8S3S40A2M2S9S3S40G0S41R1A1A4SaG2A1M3A3G1A4S6S3eS3fG1G0G3S34Z2S42A2M4A4SaS3eA1A3A3Sc7S4dA1A3M5R2A2S32S3dR2R1A2S99S3dR2S4dA2M6A1A2A3S1S0S3S46G5R2A2S32G4S98G6A1A2A3S1S48G5R2A2S0S4S45G5A1S5A3A2A2A2Fk;Fr;").
Proof.
  intros r k. rewrite bsumV_app, bsumK_app. destruct (POT_vals r vN) as (-> & -> & NN & WP).
  cbn [bsumV bsumK bi_v bi_k]. unfold bival. cbn [lfval aval bi_f bi_c]. pose proof (uval_range r k). unfold KU.
  split; [lia|]. split; [lia|]. split; [|reflexivity].
  apply bd_nn_app. split; [|exact NN]. repeat constructor; unfold bival; cbn [lfval aval bi_f bi_c]; lia.
Qed.
Lemma pay_K_arith : ltac2:(tb__ "0|4|
S3S3S3S31Z0R3A2S1S31Z1M0R3A2S31R3S33Z2M1Z1bA2A2A2S31Z10001S32R5R4A2A2S2S1S0S3R4Z10000M2A3S35S32R5G0A2M3G2A2A2S1S0S3R4G3A3S31G2G3A2A2A2S1S31S32S32R5Z20A2S99R6A1A2S32S99R7A1S32S34G1R6A2Z60A2A2A2S31S32S34G1S42A2S98R6A1A2S32S98R7A1S32S34Z4R6A2Z40A2A2A2A2F_;F_;F_;F_;Fk;Fn;Fug;").
Proof. intros ug n k Hu Hn Hs Hk. unfold potV, potK, AV0, AK0, KU. destruct Hk as [[-> Hc]|[-> Hc]]; split; lia. Qed.

Lemma len2_val : ltac2:(tb__ "0|0|
S16S7S14A1SbeS14S20R2A1R1A3S0S4SaaR2A1S5A3S0S4SacR3A1S5A3S0S3S3dR5S1bS91S78S17Z2A1A3A2S32S3dR5S4dA2Z1A2A3F_;F_;F_;FF;Fr;").
Proof.
  intros r F HF HB HC. pose proof (nval r _ HF HB HC) as (N1 & N2 & N3 & EL & EN & N4 & N4b & N5).
  pose proof (uval_range r vC1). pose proof (uval_range r vI).
  rewrite uval_add_small by (rewrite EL, uval_lit by lia; lia). rewrite EL, uval_lit by lia. lia.
Qed.

Section Sum.
Let HTOP : InitState.segs_top segs <= IMG_HI := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nn.Lib_arena_alloc.HTOP_ok.
Variable AInv : ltac2:(tb__ "0|0|
Sf2S16S7S8fQ40A1A1Sd4OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
Se1S4aVAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S3Sf7VCST;R1A2S1S31Z0R2A2S35R2Sf0A2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S3Sf7VXGL;R1A2S1S31Z0R2A2S35R2Sf0A2A2F_;Fa;").
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S7S8S8S3S3A2S3A2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 5 BX.
Let HNP : NP_okA NF := NP_okA_intro NF eq_refl.
Variable rho0 : valuation.

Definition JL (nd : ndesc) : jpostA := ltac2:(tb__ "0|0|
Sa2VAInv;VCST;VXGL;VKc;Sa9VCST;VFB;VFF;A3VFB;VFF;VBX;S97Vnd;Aa").
Definition Posts_ir : list (axst * jpostA) := ltac2:(tb__ "0|1|
S6S8S39Sb9A2M0S9S39Sb9S5bSd7S61A1A4S6G0S9S39Sb9S5cSd7S62A1A4SaG0A1A3A3").

Definition PD_ir : list (axst * ndesc) := ltac2:(tb__ "0|1|
S6S8S39S96A2M0S9S39S96S5bS61A4S6G0S9S39S96S5cS62A4SaG0A1A3A3").

Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
Sa1VAInv;VCST;VXGL;S95VKc;Vrho0;Sa9VCST;VFB;VFF;A3VFB;VFF;VBX;S97Vnd;Ac").
Let nI : ltac2:(tb__ "0|0|
S8S39S96A2Sf9Fn;") := ltac2:(tb__ "0|0|
Sa3VAInv;VCST;VXGL;S95VKc;Vrho0;Sa9VCST;VFB;VFF;A3VFB;VFF;VBX;S97Ab").
Let Q (tp0 : list word) : assn := ltac2:(tb__ "0|0|
SbaS4aS95Vrho0;Vtp0;Sd6A5").

Section X.
Variable TR : assn -> assn -> Prop.
Variable FAM : ltac2:(tb__ "0|0|
S3S7S8fQ40A1A1Sc0F_;F_;").
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S8dS39S16S7S8fQ40A1A1Sc0SbeS14S20R3A1S1aS38R4A1A1A3VTR;S8cS4aR6R5R4R3A5R2A2M0F_;G0F_;FQ;Ftp;Frho;FS;FJ;").
Hypothesis TR_ex : forall (T : Type) (J : T -> jpredA) S rho tp (Q : assn),
  (forall x, TR (SPA segs (J x) S rho tp) Q) -> TR (SPA segs (fun r p t m => exists x, J x r p t m) S rho tp) Q.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
Sc0Sc0Sc0Sc3R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_exw : forall (T : Type) (P : T -> assn) (Q : assn), (forall a, TR (P a) Q) -> TR (fun w => exists a, P a w) Q.
Hypothesis TR_callP : ltac2:(tb__ "0|5|
S8dS8dS39S39ScdS7S19A1M0S7S8S39Sb9A2M1A1S7S8S15S15A2M2A1Sc0S16S7S8fQ40A1A1M3G2Sa6G2R1R5A3Sa6G2R2S3aRbA1A3F_;Fr;S0S11G0A1SbdRaR9R8A3SfG0R7A2A3S0S4SbcRbRaR9R8SbfG1S39SdS39Sb9A2R7A4A5S5A3S16G3VTR;S8cS4aRfRdR2R1A5SbaS4aS1cS38RdA1A1R2R1RaA5A2Ftp1;Frho1;S7Sd5A1M4Sd3Sd4S8eS4aR9R8R10S9G4Se3R3Se4R2R1A2A4A5R13RaR9R4R2A4R13SccScbRbRfSc4R3RaR4A3A3R10A2RaR5R3A4F_;F_;Fmd;Fms;Ftr;S39Sb9G4Sd3Sd4S16G3G4Sd3Sd4Sa6G1S9S39Sb9RaR9A4R14A3S8eS4aR12R11R19S9G4Se3R9Se4R8R7A2A4A5R1cR13R12RaR8A4Sf4S1cS38R1aA1A1SccScbR14R18Sc4R9R13RaA3A3R19A2R8A3S8eS4aR9R8ReS9G4Se3R7Se4R6R5A2A4A5ReSccScbR16R1aSc4RbR15RcA3A3R1bA2R15RaR9R8R6A6S1SfbR17Sc4RcR16RdA3R1bR1cR1dR10R1eR19RbA9S16Sf5R18Sc4RdR17ReA3R1cR1dS38R1eA1S38R1fA1S38R11A1R1RcA9VTR;S8cS4aSbbR11SccScbR19R1dSc4ReR18RfA3A3R1eA2R18RdRcA5SfcR1eR1fR12R20R1dR1bA6R2RcA5R1aA2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S8cS4aR11RfR8R7A5R9A2F_;F_;F_;F_;F_;F_;Ftp;Frho;FQ;FXk;FPosts;FR;Fs;FPre;FC;FJp;FJ;").
Hypothesis CMALLOC : ltac2:(tb__ "0|1|
Sf2S16S7S8fQ40A1A1VTR;S8cS4aSdbVAInv;SaSdaA1M0Sd9R3VKc;S1ePcA1A6SddSd8G0Sd9A3R2R1A5SbaS4aS95R2R1SdcSd8VAInv;VCST;VXGL;G0Sd9R3VKc;A8A5A2Ftp1;Frho1;FAi;").

Hypothesis REENTER : ltac2:(tb__ "0|4|
S39S96S8S3S15A2M0S16S7S8fQ40A1A1M1S3G1Sa6S8S8S39S96A2M2G0A2S9G2G0S9S39S96R7R6A4R5A4S60A3S1S31Z0Sa0S9G2G0S9S39S96R8R7A4R6A4R5A2M3A2S35G3R3A2A2VTR;S8cS4aVJAv;R8A1R9R6R5A5VFAM;R4R3A2A2F_;F_;Ftp0;Fb;Ftp;Frho;Frv;Fnd;FT;").
Hypothesis POST : ltac2:(tb__ "0|1|
S39S96S16S7S8fQ40A1A1M0S3G0Sa6S8S39Sb9A2S9S39Sb9R6Sd7R5A1A4Sd6A3VTR;S8cS4aVJAv;R6A1R7R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;Fnd;FP;").

Ltac meas := unfold emeasA; cbn [eda_rank eda_var fst snd];
  match goal with |- context [bv_unsigned (eval ?r ?e)] => pose proof (U_range (eval r e)) end; unfold M64v in *; lia.
Tactic Notation "innth" integer(k) := do k right; left; reflexivity.

Lemma pay_CHn : ltac2:(tb__ "0|1|
S39S7S3eA1S0S4SaaS1aS38R2A1A1A1S5A3S0S4SacS1aS38R3A1A1A1S5A3S0S4S45R3A1S5A3SeeS95Vrho0;Sa9VCST;VFB;VFF;A3S1aS38R5A1A1S17Z0M0A1G0SbS3eS79R4A3SbS3eS7aR4A3A8F_;F_;F_;Frest;FX;").
Proof.
  intros X rest HB HC HW. split; [unfold bd_wpos in *; rewrite forallb_app, HW; reflexivity|]. split; [lia|]. intros r HF _ _ HNN. unfold pay_sem.
  destruct (nval r _ HF HB HC) as (N1 & N2 & N3 & EL & EN & N4 & N4b & N5).
  rewrite uval_lit by lia. rewrite !bsumV_app, !bsumK_app.
  unfold CHi, CHn. cbn [bsumV bsumK bi_v bi_k]. unfold bival. cbn [lfval aval bi_f bi_c]. rewrite EN.
  split; [lia|]. split; [lia|].
  apply bd_nn_app. split.
  - repeat constructor; unfold bival; cbn [lfval aval bi_f bi_c]; rewrite ?EN; lia.
  - unfold bd_nn in HNN |- *. apply Forall_app in HNN as [_ HNN]. exact HNN.
Qed.

Lemma X_P_fail : ltac2:(tb__ "0|1|
S16S7S8fQ40A1A1M0S3G0VTR;S8cS4aVJAv;S61A1S5bR4R3A5VFAM;R2R1A2A2Ftp0;Fb;Ftp;Frho;").
Proof. intros. apply POST. left. reflexivity. Qed.
Lemma X_P_ok : ltac2:(tb__ "0|1|
S16S7S8fQ40A1A1M0S3G0VTR;S8cS4aVJAv;S62A1S5cR4R3A5VFAM;R2R1A2A2Ftp0;Fb;Ftp;Frho;").
Proof. intros. apply POST. right. left. reflexivity. Qed.

Lemma X_X_open : ltac2:(tb__ "0|1|
S16S7S8fQ40A1A1M0S3G0S31S34Z5bS33Z2Z40A2A2R2A2VTR;S8cS4aVJAv;S57A1S83R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  apply (TR_pre (fun w => exists rho', SPA segs (JAv ndO) C_open rho' tp w)).
  { intros w Hw0.
    pose proof (JA_repay segs AInv CST XGL NF Kc rho0 (P0_ir CST FB FF) FB FF BX PTrue tv_ir [] (CHi ++ []) (CHn ++ []) am_ir X_open rho tp w
                  (pay_CHn X_open [] ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl) Hw0) as Hw.
    rewrite app_nil_r in Hw.
    destruct (JA_open segs AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_ir CST FB FF) FB FF BX PTrue HKc HBX HNP tv_ir [] CHn vHDi true X_open rho tp w) as (rho' & _ & Hw');
      [vm_compute; reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | | exact Hw |].
    - intros Ai rho1 tp1 md1 HF HP0 Hav _ HTS HTKS. pose proof (T0_agreeA rho0 NF rho Hav eq_refl) as ET. destruct (P0_now CST FB FF rho0 rho HP0 Hav) as [HT Hbb]. split.
      + apply (objs_ok_ir CST rho0 FB FF); [basez_tac HF | exact HT | exact Hbb | | exact ET].
        intros o Ho. cbn in Ho. unfold objclass. destruct Ho as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]; cbn; auto 12.
      + apply xrs47_ir. basez_tac HF.
    - exists rho'. rewrite <- C_open_eq. exact Hw'. }
  apply TR_exw. intros rho'. apply (REENTER C_open ndO (90, z0)); [innth 5 | meas].
Qed.

Lemma X_X_nohead : ltac2:(tb__ "0|1|
S16S7S8fQ40A1A1M0S3G0S31S34Z51S33Z2Z40A2A2R2A2VTR;S8cS4aVJAv;S57A1S82R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  eapply TR_pre; [|apply (REENTER C_slow ndS (80, z0) (rho_sub rho s_nohead)); [innth 6 | meas]].
  intros w Hw0.
  pose proof (JA_repay segs AInv CST XGL NF Kc rho0 (P0_ir CST FB FF) FB FF BX PTrue tv_ir [] (CHi ++ []) (CHn ++ []) am_ir X_nohead rho tp w
                (pay_CHn X_nohead [] ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl) Hw0) as Hw.
  rewrite app_nil_r in Hw.
  apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 (P0_ir CST FB FF) FB FF BX PTrue HKc X_nohead C_slow s_nohead (NDA tv_ir [] (CHn ++ [BIc 1 0 AV0; BIc 0 1 AK0]) (AHead vHDi false)) ndS);
    [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity |].
  apply (JA_pot_out0 segs AInv CST XGL NF Kc rho0 (P0_ir CST FB FF) FB FF BX PTrue HBX); [vm_compute; reflexivity | exact Hw].
Qed.

Lemma X_X_nofit : ltac2:(tb__ "0|1|
S16S7S8fQ40A1A1M0S3G0S31S34Z51S33Z2Z40A2A2R2A2VTR;S8cS4aVJAv;S58A1S81R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply TR_facts. intros HF.
  assert (BZ : basezI rho) by basez_tac HF.
  pose proof (nval rho _ HF ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as (N1 & N2 & N3 & EL & EN & N4 & N4b & N5).
  assert (OZ : uval rho vHDi <= 140737479966720 /\ uval rho vU <= uval rho vCAP /\ uval rho vCAP <= 2 ^ 40 - 33 /\ 65536 <= uval rho vCAP
               /\ uval rho vHDi + (uval rho vCAP + 32) <= uval rho (SVar 30) /\ (4096 <= uval rho vHDi /\ uval rho (SVar 30) <= 140737479966720)
               /\ uval rho (e32 vCAP) = uval rho vCAP + 32 /\ uval rho (SAlu ALU_ADD vHDi (e32 vCAP)) = uval rho vHDi + (uval rho vCAP + 32)) by openz_tac HF.
  destruct OZ as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & EK & EH).
  destruct (fit_arith rho Z1 Z2 Z3 ltac:(lia)) as (EP & EPN & EUN & EH32).
  factz HF (SPNot (SPBranch BC_GEU vCAP (SAlu ALU_ADD vN vU))) H0. rewrite (uval_add_comm rho vN vU), EUN in H0.
  apply (TR_pre (fun w => exists rho', SPA segs (JAv ndS) C_slow rho' tp w)).
  { intros [tr [ms md]] Hw.
    pose proof (JA_close_np segs HTOP AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_ir CST FB FF) FB FF BX PTrue HKc HBX HNP tv_ir [] bd_open vHDi vNX vCAP vU X_nofit
                  (removelast (ss_objs (ax_S X_nofit))) (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nn.Lib_arena_alloc.O_hdr vHDi vNX vCAP vU) rho tp tr ms md) as CL.
    specialize (CL ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; left; reflexivity) eq_refl Hw).
    set (rho1 := rho_absorb rho [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nn.Lib_arena_alloc.O_hdr vHDi vNX vCAP vU] (vms md tp ms)) in CL.
    assert (CL2 : SPA segs (JAv (NDA tv_ir [] bd_open am_np)) X_nofit2 rho1 tp (tr, mkCfg ms md)).
    { rewrite <- X_nofit2_eq. change (drop_lastA X_nofit (removelast (ss_objs (ax_S X_nofit)))) with X_nofit1 in CL.
      apply (SPA_refacts_JA segs _ rho1 X_nofit1 (nofit_fact :: ss_facts (ax_S X_nofit1))); [exact CL | vm_compute; reflexivity |].
      intros tr' md' _ HF1. constructor; [|exact HF1].
      apply (proj2 (holds_ule _ _ _)). rewrite U_lit. change (65537 mod M64v) with 65537.
      assert (EU : forall e, eval rho1 e = eval rho e) by (intros e; unfold rho1; apply eval_absorb).
      rewrite EU. change (bv_unsigned (eval rho (SAlu ALU_ADD vU vN))) with (uval rho (SAlu ALU_ADD vU vN)). rewrite EUN. lia. }
    exists (rho_sub rho1 s_nofit).
    apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 (P0_ir CST FB FF) FB FF BX PTrue HKc X_nofit2 C_slow s_nofit (NDA tv_ir [] bd_open am_np) ndS);
      [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | exact CL2]. }
  apply TR_exw. intros rho'. apply (REENTER C_slow ndS (80, z0)); [innth 6 | meas].
Qed.

Lemma X_X_fitG : ltac2:(tb__ "0|7|
S39S39S39S19ScdS3S15S16S7S8fQ40A1A1M0S3G0S0S7S19A1S25S38RbA1A1M1SbS19Sa8S19G1A2S6S19R8SaS19A1A3A3A3S1S0S15S22R9A1S4eA3S1S0S15S24R9A1S17Z0M2A1A3S0S15S23R9A1S17Z18A1A3A2A2S19Sa6S19R1Sa8S19S25S38ReA1A1A2A3SadR2A1F_;Fo;S0S7S8S15S15A2M3A1S3aReA1S6G3S9S15S15S4eSc6S4fA1A4S5dA3A3S0S4SaaS1aS38RfA1A1A1S5A3S0S4SacS1aS38R10A1A1A1S5A3S0S4SaeS1aS38R11A1A1A1S5A3S0S4Sa5S14S1dS21S94S4fS1bS91S4dS54A3A3A1S1aS38R12A1A1A3S5A3S0S4S2bS38Sc5R13S53S4dA3A1A1S5A3S0S15S3cR14A1S17Sf1A1A3S0S4S26S1cS38R15A1A1S53A2S5A3S0S4S26S1cS38R16A1A1S4dA2S5A3S0S39Sf6Sc5R17S53S4dA3SbS14S73S1aS38R17A1A1A3A2R16A3S0S4Sa7S14S2aS1cS38Sc5R18S53S4dA3A1A1A1SbS14S73S1aS38R18A1A1A3A3S5A3Sa6S8S8S39S96A2M4S8S3S15A2M5A2S9G4G5S9S39S96R17S63A4S9S3S15R14R13A4A4S60A3S1S31G2R15A2S31R15Z32A2A2S0S4S3bR1aR19R17A3S5A3S0S4SceR18S95A2S5A3S0S4Sf3S95S1cS38R1cA1A1A2S5A3S0S4S9dS1cS38R1dA1A1S9aS50SaS8S8S15S3A2S15A2A1S72S9eS4eS8bS4fS6G3S9S15S15S53S4dA4SaG3A1A3A4M6A4A2S5A3S0S4Se6R1bS50S50A3S5A3S0S4S44S1aS38R1fA1A1S43R1cS71A2S72A3S5A3S0S4S9bS9cR1dS70A2G6A2S5A3S31S34Z33S33Z2Z40A2A2R19A2VTR;S8cS4aVJAv;S58A1R23R1cR1bA5VFAM;R1aR19A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Ftp0;Fb;Ftp;Frho;Frvar;Frk;Fs;Foh;FT;FXf3;FXf;").
Proof.
  intros Xf Xf3 T oh s rk rvar rho tp b tp0 Hobjs (Ohb & Ohl & Ohh) Hcls HX HB HC HO Hge Hwf Hbase Hb1 Hb2 HX3 Hfb HinT Hrk He Hid Hnf Hnb Htv Hle Ham Hb.
  apply TR_facts. intros HF.
  assert (BZ : basezI rho) by exact (basezI_of _ _ HF HB).
  pose proof (nval rho _ HF HB HC) as (N1 & N2 & N3 & EL & EN & N4 & N4b & N5).
  destruct (openz rho _ HF HO) as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & EK & EH).
  destruct (fit_arith rho Z1 Z2 Z3 ltac:(lia)) as (EP & EPN & EUN & EH32).
  pose proof (holds_mem _ _ _ HF Hge) as H0. zf H0. repeat change (bv_unsigned (eval ?r ?e)) with (uval r e) in H0. rewrite (uval_add_comm rho vN vU), EUN in H0.
  eapply TR_pre; [|apply (REENTER T ndL (rk, rvar) (rho_sub rho s)); [exact HinT | unfold emeasA; cbn [eda_rank eda_var fst snd]; pose proof (U_range (eval (rho_sub rho s) rvar)); unfold M64v in *; nia]].
  intros w Hw.
  apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 (P0_ir CST FB FF) FB FF BX PTrue HKc Xf3 T s (NDA tv_ir [] bd_open (AOpen vHDi vNX vCAP [(p_fit, vN)])) ndL);
    [exact He | exact Hid | exact Hnf | exact Hnb | exact Htv | reflexivity | exact Hle | exact Ham |].
  rewrite <- HX3. apply (SPA_refacts_JA segs _ rho (carve_stateA Xf p_fit vN) (fit_facts ++ ss_facts (ax_S Xf))); [| exact Hfb |].
  - apply (JA_carve segs AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_ir CST FB FF) FB FF BX PTrue HNP tv_ir [] bd_open vHDi vNX vCAP p_fit vN Xf rho tp w);
      [exact Hwf | exact Hbase | exact Hb1 | exact Hb2 | | | exact Hw].
    + intros r HFr.
      pose proof (nval r _ HFr HB HC) as (_ & _ & _ & _ & _ & M4 & M4b & M5).
      destruct (openz r _ HFr HO) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & _).
      destruct (fit_arith r Y1 Y2 Y3 ltac:(lia)) as (EP' & _ & EUN' & _).
      pose proof (holds_mem _ _ _ HFr Hge) as H1. zf H1. repeat change (bv_unsigned (eval ?rr ?e)) with (uval rr e) in H1. rewrite (uval_add_comm r vN vU), EUN' in H1.
      pose proof (uval_range r vU). lia.
    + intros Ai rho1 tp1 md1 HF' HP0 Hav _ HTS HTKS. pose proof (T0_agreeA rho0 NF rho Hav eq_refl) as ET. destruct (P0_now CST FB FF rho0 rho HP0 Hav) as [HT Hbb]. split.
      * intros o a Ho Hr. rewrite Hobjs in Ho. apply in_app_or in Ho. destruct Ho as [Ho'|[<-|[]]].
        -- destruct (objs_ok_ir CST rho0 FB FF rho (removelast (ss_objs (ax_S Xf))) BZ HT Hbb Hcls ET o a Ho' Hr) as [P|P]; [left; exact P | right; left; exact P].
        -- right; right. unfold obj_range, obj_lo_of, obj_hi_of in Hr. rewrite Ohb, Ohl, Ohh in Hr. cbn [fst snd] in Hr.
           rewrite !soff_lit_small in Hr by lia. unfold uval. lia.
      * rewrite HX. apply xrs47_cons; [lia | apply xrs47_ir; exact BZ].
  - intros tr md _ HF2. apply Forall_app. split; [|exact HF2].
    unfold fit_facts. pose proof (uval_range rho vU).
    repeat apply Forall_cons; try apply Forall_nil; cbn [holds]; repeat change (bv_unsigned (eval ?r ?e)) with (uval r e);
      rewrite ?EPN, ?EH, ?EH32, ?EP; rewrite ?uval_lit by lia; lia.
Qed.
Lemma X_X_fitc : ltac2:(tb__ "0|1|
S16S7S8fQ40A1A1M0S3G0S31S34Z33S33Z2Z40A2A2R2A2VTR;S8cS4aVJAv;S58A1S7fR5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  apply (X_X_fitG X_fitc X_fitc3 C_loop ohFc s_fitc 50 (SAlu ALU_SUB vLn vJ) rho tp b tp0 objsFc_eq);
    [cbn; repeat split; reflexivity | | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
    | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | exact X_fitc3_eq | vm_compute; reflexivity
    | innth 10 | lia | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
    | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | exact Hb].
  intros o Ho. cbn in Ho. unfold objclass. destruct Ho as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]; cbn; auto 12.
Qed.
Lemma X_X_fitn : ltac2:(tb__ "0|1|
S16S7S8fQ40A1A1M0S3G0S31S34Z33S33Z2Z40A2A2R2A2VTR;S8cS4aVJAv;S58A1S80R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  apply (X_X_fitG X_fitn X_fitn3 C_nul ohFn s_fitn 45 z0 rho tp b tp0 objsFn_eq);
    [cbn; repeat split; reflexivity | | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
    | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | exact X_fitn3_eq | vm_compute; reflexivity
    | innth 11 | lia | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
    | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | exact Hb].
  intros o Ho. cbn in Ho. unfold objclass. destruct Ho as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]; cbn; auto 12.
Qed.

Lemma pay_K : ltac2:(tb__ "0|9|
S39S15S0S4SaaS1aS38R2A1A1A1S5A3S0S4SacS1aS38R3A1A1A1S5A3S0S4Sa5S14S1dS18S17Z10001A1S1bS91S6aS4dA3A2A1S1aS38R4A1A1A3S5A3S0S4Sa5S14S1dS18S6aS17S77A1A2A1S1aS38R5A1A1A3S5A3S16SbeS14S20R1A1S1aS38R7A1A1M0A3S2S1S0S3S3dR2R7A2M1Z10020A3S35S32S3dR2S4dA2M2Z1M3A2M4Z10000M5A2A2S1S0S3G1S32G2Z21A2A3S31G5G4A2A2A2F_;Fr;SeeS95Vrho0;Sa9VCST;VFB;VFF;A3G0S17Z0M6A1G6S56SbS3eS6S3eS3fG3G6S6S8S3S40A2M7S9S3S40G3S41R6A1A4SaG7A1M8A3G6A4S6S3eS3fG6G3G8S34Z2S42A2A4SaS3eA1A3A3Sc7S4dA1A3A8F_;F_;F_;F_;F_;Fk;FX;").
Proof.
  intros X k HB HC Hug1 Hug2 HK. destruct (sums_K rho0 k) as (_ & _ & _ & WP). split; [exact WP|]. split; [lia|]. intros r HF _ _ _. unfold pay_sem.
  pose proof (nval r _ HF HB HC) as (N1 & N2 & N3 & EL & EN & N4 & N4b & N5).
  destruct (sums_K r k) as (-> & -> & NN & _). destruct (sums_slow r) as [-> ->]. rewrite uval_lit by lia.
  pose proof (holds_mem _ _ _ HF Hug1) as H1. pose proof (holds_mem _ _ _ HF Hug2) as H2. zf H1. zf H2.
  repeat change (bv_unsigned (eval ?rr ?e)) with (uval rr e) in H1. repeat change (bv_unsigned (eval ?rr ?e)) with (uval rr e) in H2.
  unfold two40, RA.two40 in H2. rewrite !uval_lit in H1, H2 by lia. pose proof (uval_range r vUg).
  rewrite uval_add_small in H1 by lia.
  pose proof (HK r HF) as HKr.
  destruct (pay_K_arith (uval r vUg) (uval r vN) (uval r k - 32) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [A B].
  split; [lia|]. split; [lia | exact NN].
Qed.

Lemma X_X_K : ltac2:(tb__ "0|8|
S39ScdS15S16S7S8fQ40A1A1M0S3G0SeeS95Vrho0;Sa9VCST;VFB;VFF;A3S1aS38R7A1A1S17Z0M1A1G1S56SbS3eS6S3eS3fZ1M2G1S6S8S3S40A2M3S9S3S40G2S41R5A1A4SaG3A1M4A3G1A4S6S3eS3fG1G2G4S34Z2M5S42A2A4SaS3eA1A3M6A3Sc7S4dA1M7A3A8S0S4S3bR8S7bR7A3S5A3S0S4SceR8S95A2S5A3S0S4Sf3S95S1cS38RaA1A1A2S5A3S0S4S9dS1cS38RbA1A1S9aS50SaS8S8S15S3A2S15A2A1SbS3eS6S3eS3fG2G1S6G3S9S3S40G2S41R9A1A4G4A3G1A4G6A3G7A3S5eA4A2S5A3S0S4S44S1aS38RcA1A1S43RbS87A2SbS3eS6S3eS3fG2G1S6G3S9S3S40G2S41RaA1A4G4A3G1A4G6A3G7A3A3S5A3S0S4S9bS9cRcS5eA2S5eA2S5A3S0S4Se6RdS50S50A3S5A3S31S34Z4cS33G5Z40A2A2RaA2VTR;S8cS4aVJAv;S65A1R10RdRcA5VFAM;RbRaA2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;Ftp0;Fb;Ftp;Frho;Fk;Fs;FX;").
Proof.
  intros X s k rho tp b tp0 HPAY He Hid Hnf Hnb Hle Ham Htv Hb.
  eapply TR_pre; [|apply (REENTER C_K ndKc (75, z0) (rho_sub rho s)); [innth 7 | meas]].
  intros w Hw. apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 (P0_ir CST FB FF) FB FF BX PTrue HKc X C_K s (NDA tv_ir [] ([BI 1 0 [(1, ASv k)] 0; BI 0 1 [] (2 * KU)] ++ POT vN) am_np) ndKc);
    [exact He | exact Hid | exact Hnf | exact Hnb | exact Htv | reflexivity | exact Hle | exact Ham |].
  apply (JA_repay segs AInv CST XGL NF Kc rho0 (P0_ir CST FB FF) FB FF BX PTrue tv_ir [] bd_slow _ am_np X rho tp w HPAY Hw).
Qed.
Lemma X_X_K1 : ltac2:(tb__ "0|1|
S16S7S8fQ40A1A1M0S3G0S31S34Z4cS33Z2Z40A2A2R2A2VTR;S8cS4aVJAv;S65A1S7dR5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply (X_X_K X_K1 s_K1 (SLit 65568));
    [| vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | exact Hb].
  apply pay_K; [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity |].
  intros r HF. left. factz HF (SPBranch BC_LTU (SAlu ALU_ADD vLEN (SLit 2)) (SLit 65536)) H1.
  rewrite (len2_val r _ HF ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) in H1.
  rewrite !uval_lit in * by lia. lia.
Qed.
Lemma X_X_K2 : ltac2:(tb__ "0|1|
S16S7S8fQ40A1A1M0S3G0S31S34Z4cS33Z2Z40A2A2R2A2VTR;S8cS4aVJAv;S65A1S7eR5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply (X_X_K X_K2 s_K2 (SAlu ALU_ADD vN (SLit 33)));
    [| vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | exact Hb].
  apply pay_K; [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity |].
  intros r HF. right. factz HF (SPNot (SPBranch BC_LTU (SAlu ALU_ADD vLEN (SLit 2)) (SLit 65536))) H1.
  rewrite (len2_val r _ HF ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) in H1.
  pose proof (nval r _ HF ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as (_ & _ & _ & _ & _ & N4 & N4b & N5).
  rewrite !uval_lit in * by lia. rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia. lia.
Qed.

Lemma site_m : ltac2:(tb__ "0|1|
S16SefVAInv;VCST;VXGL;S95Vrho0;Sa9VCST;VFB;VFF;A3VFB;VFF;S6bS66S6fR1S74S12S3A1Sf2Sd3S1S1S31Z1S3dR3ScfS66PcA2A2M0A2S35G0S33Z2Z27A2A2A2Se2SaSdaA1Sd9SccScbR3S6fR1A3S66A2A3A2Lms;LAi;AfFrho;").
Proof.
  intros rho Ai ms HF HP0 Hav HB HFF HN HD HZ HFR (r1 & t1 & m1 & HM) HTP HTK. cbn [nd_tv nd_fr nd_bd ndKc] in HN, HD, HZ, HFR.
  assert (BZ : basezI rho) by basez_tac HF. destruct (P0_now CST FB FF rho0 rho HP0 Hav) as [HT Hbb].
  assert (XO : forall o a, is_xo o = true -> fst (obj_range rho o) <= a < snd (obj_range rho o) -> cmaddrA CST Ai None a).
  { intros o a Hx Hr. unfold is_xo in Hx. apply lazy_orb_prop in Hx as [Hx|Hx];
      apply lazy_andb_prop in Hx as [H1 Hx]; apply lazy_andb_prop in Hx as [H2 H3];
      apply sv_eqb_sound in H1; apply sv_eqb_sound in H2; apply sv_eqb_sound in H3;
      destruct o as [ob olo ohi oc od]; cbn [ob_base ob_lo ob_hi] in H1, H2, H3; subst.
    - apply (infrFF_cmaddrA CST FF Ai (uval rho vBld) 1304 None a HFF Hbb).
      unfold obj_range, obj_lo_of, obj_hi_of in Hr. cbn [ob_base ob_lo ob_hi fst snd] in Hr. rewrite !soff_lit_small in Hr by lia. unfold uval. lia.
    - apply (pclMA_cmaddrA CST rho0 FB FF Ai a HB HFF HTP). apply HT.
      destruct BZ as [_ _ _ _ [T1 [T2 T3]] _ _].
      unfold obj_range, obj_lo_of, obj_hi_of in Hr. cbn [ob_base ob_lo ob_hi fst snd] in Hr. rewrite soff_lit_small in Hr by lia.
      rewrite (soff_smallu rho vL) in Hr by lia. unfold uval in *. lia. }
  assert (XX : forall r a, is_xX r = true -> uval rho (fst r) <= a < uval rho (fst r) + uval rho (snd r) -> cmaddrA CST Ai None a).
  { intros r a Hx Ha. unfold is_xX in Hx. apply lazy_orb_prop in Hx as [Hx|Hx]; apply xr_eqb_sound in Hx; subst r; cbn [fst snd] in Ha.
    - apply (infrFF_cmaddrA CST FF Ai (uval rho vBld) 1304 None a HFF Hbb). rewrite uval_lit in Ha by lia. exact Ha.
    - apply (pclMA_cmaddrA CST rho0 FB FF Ai a HB HFF HTP). apply HT. exact Ha. }
  split; [|split; [|split; [|exact I]]].
  - eapply (robjs_checkA_sound segs AInv CST ALA FB Ai rho (ss_facts (ax_S E_m)) tv_ir None is_xo R_m None r1 t1 m1 HM HF HN HD HZ HTK).
    + vm_compute. reflexivity.
    + intros o a Ho Hb Hr. exact (XO o a Hb Hr).
    + exact I.
  - eapply (xrs_checkA_sound segs AInv CST XGL ALA FB Ai rho (ss_facts (ax_S E_m)) tv_ir None (ss_objs (ax_S E_m)) is_xX (ax_X E_m) None r1 t1 m1 HM HF HN HD HZ HTK).
    + vm_compute. reflexivity.
    + intros r a Hr Hb Ha. left. exact (XX r a Hb Ha).
    + exact I.
  - change (wsub_get s_m 12) with (e32 vK). factz HF (SPUle (SLit 65536) vK) H1. factz HF (SPUle vK (SLit (2 ^ 27))) H2.
    rewrite !uval_lit in H1, H2 by lia. unfold e32. rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia. lia.
Qed.

Lemma X_E_m : ltac2:(tb__ "0|1|
S16S7S8fQ40A1A1M0S3G0S31S34Z42S33Z2Z40A2A2R2A2VTR;S8cS4aVJAv;S74A1S6bR5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  apply (malloc_callT segs AE_A AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_ir CST FB FF) FB FF BX PTrue HKc HBX TR TR_facts TR_ex TR_pre TR_callP
           [] UStopLe E_m s_m R_m rho tp ndKc bd_m (FAM b tp0) CMALLOC).
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - reflexivity.
  - vm_compute. reflexivity.
  - reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - apply payA_of_bud_pay. vm_compute. reflexivity.
  - intros A A_ _ _; exact I.
  - exact (site_m rho).
  - intros rho' tp'. cbn [nd_tv nd_fr nd_am ndKc]. fold Pre_m. rewrite T_mnull_eq. apply (REENTER T_mnull ndM (65, z0)); [innth 8 | meas].
  - intros rho' tp'. cbn [nd_tv nd_fr nd_am ndKc]. fold Pre_m. rewrite T_mok0_eq.
    eapply TR_pre; [|apply (REENTER T_mok ndMok (65, z0)); [innth 9 | meas]].
    intros w Hw. unfold T_mok. apply (SPA_refacts_JA segs); [exact Hw | reflexivity |].
    intros tr md HJ HF. apply Forall_app. split; [|exact HF].
    eapply JA_tv_facts; [exact ALA | | exact HJ | left; reflexivity |]; [reflexivity|].
    apply tnz_of_fact. apply (holds_mem _ _ _ HF). vm_compute. reflexivity.
Qed.

Lemma X_X_sretG : ltac2:(tb__ "0|11|
S39S39S39S39S39S7S10A1S7S19A1M0S19S19ScdS3S15S16S7S8fQ40A1A1M1S3G1S0S11S39A1SecR10S6Se9SeaRbA1S6Se9SebSf8S13S10RbA2U1A2S17Z18A1M2A2SaSe9A1A3A3A2SfS39RfA2A3S0G0S25S38R10A1A1SbS19SbS19RbS6S19RaSaS19A1M3A3A3S6S19R9G3A3A3A3S0S4SfaRbS1eS8aA1M4S4eS52S4dA5S5A3S0S4S4S4L_;M5S1fS22RbA1G4A2G5S1fS24RbA1G2A2G5S1fS23RbA1Sc6S52A1M6A2S2eS29RbA1A1ScX4x2ScX4x2ScX4x2S5A3S0S4Se5S1aS38R13A1A1G6Z0M7G6A4S5A3S0S4Se5S1aS38R14A1A1S17Z10000A1M8G7S52A4S5A3S0S4Se5S1aS38R15A1A1S52G7S17S36S33Z2M9Z28A2Z21A2A1A4S5A3S0S4Sa5S14S1dS2dS21S93G4S17G7A1MaA3A1A1S1aS38R16A1A1A3S5A3S0S4S49S1aS38R17A1A1GaS42S88S5fA5S5A3S0S39Sc9R18SbS19R13S6S19R12G3A3A3A2R17A3S0G0S25S38R18A1A1SbS19R14S6S19R13G3A3A3A3S19Sa6S19R1R16A3SadR2A1F_;Fo;S0S7S8S15S15A2MbA1S3aR1aA1SbGbS5dS6GbS9S15S15G4G6A4SaGbA1McA3A3A3S0S4SaaS1aS38R1bA1A1A1S5A3S0S4SacS1aS38R1cA1A1A1S5A3S0S4Sa5S14S1dS18S1bS91G4G6A3S1eP1eA1MdA2A1S1aS38R1dA1A1A3S5A3S0S4Sa5S14S1dS18G4GdA2A1S1aS38R1eA1A1A3S5A3S0S4Sa5S14S1dS18G8S52A2A1S1aS38R1fA1A1A3S5A3S0S4Sa5S14S1dS18S52S17S33G9Z1bA2A1A2A1S1aS38R20A1A1A3S5A3S0S4Sa5S14S1dS18S1bS91S4dS17Z1A1A3S52A2A1S1aS38R21A1A1A3S5A3S0S4S2bS38Sc5R22S55S4dA3A1A1S5A3S0S15S3cR23A1S17Sf1A1A3S0S4S26S1cS38R24A1A1S55A2S5A3S0S4S26S1cS38R25A1A1S4dA2S5A3S0S39Sf6Sc5R26S55S4dA3SbS14S75S1aS38R26A1A1A3A2R25A3S0S4Sa7S14S2aS1cS38Sc5R27S55S4dA3A1A1A1SbS14S75S1aS38R27A1A1A3A3S5A3Sa6S8S8S39S96A2MeS8S3S15A2MfA2S9GeGfS9S39S96R26S63A4S9S3S15R20R1fA4A4S60A3S1S31G7R21A2S31R21Z32A2A2S0S4S3bR29R28R23A3S5A3S0S4SceR24S95A2S5A3S0S4Sf3S95S1cS38R2bA1A1A2S5A3S0S4S9dS1cS38R2cA1A1S9aS50SaS8S8S15S3A2S15A2A1S5fS9eG4S4eS52S6GbS9S15S15S55S4dA4GcA3A4M10A4A2S5A3S0S4Se6R27S50S50A3S5A3S0S4S44S1aS38R2eA1A1S43R28S71A2S5fA3S5A3S0S4S9bS9cR29S70A2G10A2S5A3S31S34Z33S33G9Z40A2A2R25A2VTR;S8cS4aVJAv;S64A1R34R28R27A5VFAM;R26R25A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Ftp0;Fb;Ftp;Frho;Frvar;Frk;Fs;FotN;FohN;FobjsN;Fsel;FT;FXs3;FXs2;FXs1;FXs;").
Proof.
  intros Xs Xs1 Xs2 Xs3 T sel objsN ohN otN s rk rvar rho tp b tp0 Hax Hobjs1 Hsh Hot Hu1 Hu2 Hu3 Hnz Hpay HX2 Hobjs2 Hcls HX HB HC He1 He2 Hk1 Hk2 Hk3
         Hwf Hbase Hb1 Hb2 HX3 Hfb HinT Hrk He Hid Hnf Hnb Htv Hle Ham Hb.
  apply (TR_pre (fun w => exists rho', SPA segs (JAv ndL) T rho' tp w)).
  { intros [tr [ms md]] Hw.
    pose proof (SPA_axforms segs _ _ rho Xs Xs1 tp _ Hax Hw) as H1.
    pose proof (JA_push_open segs HTOP AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_ir CST FB FF) FB FF BX PTrue HKc HBX HNP tv_m [] bd_m bd_m2 0 blkN vHDi vK vN
                  Xs1 objsN ohN otN rho tp tr ms md Hobjs1 eq_refl Hsh Hot Hu1 Hu1 Hu2 Hu3 Hnz Hpay H1) as H2.
    rewrite HX2 in H2. cbn [remove_nth fst blkN tv_m] in H2.
    set (rho1 := rho_absorb rho [otN] (vms md tp ms)) in H2.
    assert (HF1 : Forall (holds rho1) (ss_facts (ax_S Xs2))) by exact (smatchA_facts segs _ _ _ _ (proj1 H2)).
    assert (BZ1 : basezI rho1) by exact (basezI_of _ _ HF1 HB).
    pose proof (nval rho1 _ HF1 HB HC) as (N1 & N2 & N3 & EL & EN & N4 & N4b & N5).
    pose proof (holds_mem _ _ _ HF1 He1) as HE1. pose proof (holds_mem _ _ _ HF1 He2) as HE2.
    pose proof (holds_mem _ _ _ HF1 Hk1) as HK1. pose proof (holds_mem _ _ _ HF1 Hk2) as HK2. pose proof (holds_mem _ _ _ HF1 Hk3) as HK3.
    rewrite h_ule in HE1, HE2, HK1, HK2, HK3.
    change (uval rho1 (SVar 30)) with (bv_unsigned (rw rho1 V_TOP)) in HE1, HE2. pose proof BZ1 as [_ _ _ _ _ _ [BT0 [BT1 BT2]] _].
    rewrite !uval_lit in HK1, HK2 by lia.
    pose proof (uval_range rho1 (SVar pN)) as RP. pose proof (uval_range rho1 vK) as RK.
    assert (EK : uval rho1 (e32 vK) = uval rho1 vK + 32) by (unfold e32; rewrite uval_add_small by (rewrite uval_lit by lia; lia); rewrite uval_lit by lia; lia).
    rewrite uval_add_small in HE1 by (rewrite EK; lia). rewrite EK in HE1.
    rewrite uval_add_small in HK3 by (rewrite uval_lit by lia; lia). rewrite uval_lit in HK3 by lia.
    assert (EPn : uval rho1 p_new = uval rho1 (SVar pN) + 32) by (unfold p_new; rewrite uval_add_small by (rewrite uval_lit by lia; lia); rewrite uval_lit by lia; lia).
    assert (H3 : SPA segs (JAv (NDA tv_ir [] bd_m2 (AOpen (SVar pN) vHDi vK [(p_new, vN)]))) Xs3 rho1 tp (tr, mkCfg ms md)).
    { rewrite <- HX3.
      apply (SPA_refacts_JA segs _ rho1 (carve_stateA Xs2 p_new vN) (new_facts ++ ss_facts (ax_S Xs2))); [| exact Hfb |].
      - apply (JA_carve segs AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_ir CST FB FF) FB FF BX PTrue HNP tv_ir [] bd_m2 (SVar pN) vHDi vK p_new vN Xs2 rho1 tp _);
          [exact Hwf | exact Hbase | exact Hb1 | exact Hb2 | | | exact H2].
        + intros r HFr.
          pose proof (nval r _ HFr HB HC) as (_ & _ & _ & _ & _ & M4 & M4b & M5).
          pose proof (holds_mem _ _ _ HFr Hk3) as HK3'. pose proof (holds_mem _ _ _ HFr Hk2) as HK2'. pose proof (holds_mem _ _ _ HFr He2) as HE2'.
          rewrite h_ule in HK3', HK2', HE2'. rewrite uval_lit in HK2' by lia. change (uval r (SVar 30)) with (bv_unsigned (rw r V_TOP)) in HE2'.
          pose proof (basezI_of _ _ HFr HB) as [_ _ _ _ _ _ [_ [_ BT2']]].
          rewrite uval_add_small in HK3' by (rewrite uval_lit by lia; lia). rewrite uval_lit in HK3' by lia.
          pose proof (uval_range r (SVar pN)). unfold p_new.
          rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia. lia.
        + intros Ai rho2 tp2 md2 HF' HP0 Hav _ HTS HTKS. pose proof (T0_agreeA rho0 NF rho1 Hav eq_refl) as ET. destruct (P0_now CST FB FF rho0 rho1 HP0 Hav) as [HT Hbb]. split.
          * intros o a Ho Hr. rewrite Hobjs2 in Ho. apply in_app_or in Ho. destruct Ho as [Ho'|[<-|[]]].
            -- destruct (objs_ok_ir CST rho0 FB FF rho1 objsN BZ1 HT Hbb Hcls ET o a Ho' Hr) as [P|P]; [left; exact P | right; left; exact P].
            -- right; right. unfold TobjJVA.hdr_shape in Hsh.
               apply lazy_andb_prop in Hsh as [Q1 Hsh']. apply lazy_andb_prop in Hsh' as [Q2 Hsh'']. apply lazy_andb_prop in Hsh'' as [Q3 _].
               apply sv_eqb_sound in Q1. apply sv_eqb_sound in Q2. apply sv_eqb_sound in Q3.
               unfold obj_range, obj_lo_of, obj_hi_of in Hr. rewrite Q1, Q2, Q3 in Hr. cbn [fst snd] in Hr.
               rewrite !soff_lit_small in Hr by lia. unfold uval. lia.
          * rewrite HX. intros r a Hr Ha. apply in_app_or in Hr. destruct Hr as [Hr|[<-|[]]]; [exact (xrs47_ir rho1 BZ1 r a Hr Ha)|].
            cbn [fst snd] in Ha. rewrite EK in Ha. lia.
      - intros tr' md' _ HF2. apply Forall_app. split; [|exact HF2].
        unfold new_facts. change (bv_unsigned (rw rho1 V_TOP)) with (uval rho1 (SVar 30)) in *.
        assert (EPS : uval rho1 (SAlu ALU_ADD p_new vN) = uval rho1 p_new + uval rho1 vN) by (rewrite uval_add_small by lia; lia).
        assert (EHC : uval rho1 (SAlu ALU_ADD (SVar pN) (e32 vK)) = uval rho1 (SVar pN) + (uval rho1 vK + 32)) by (rewrite uval_add_small by (rewrite EK; lia); rewrite EK; lia).
        repeat apply Forall_cons; try apply Forall_nil; cbn [holds]; repeat change (bv_unsigned (eval ?r ?e)) with (uval r e);
          rewrite ?EPS, ?EHC, ?EPn; rewrite ?uval_lit by lia; lia. }
    exists (rho_sub rho1 s).
    apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 (P0_ir CST FB FF) FB FF BX PTrue HKc Xs3 T s (NDA tv_ir [] bd_m2 (AOpen (SVar pN) vHDi vK [(p_new, vN)])) ndL);
      [exact He | exact Hid | exact Hnf | exact Hnb | exact Htv | reflexivity | exact Hle | exact Ham | exact H3]. }
  apply TR_exw. intros rho'. apply (REENTER T ndL (rk, rvar)); [exact HinT | unfold emeasA; cbn [eda_rank eda_var fst snd]; pose proof (U_range (eval rho' rvar)); unfold M64v in *; nia].
Qed.
Lemma X_X_sretc : ltac2:(tb__ "0|1|
S16S7S8fQ40A1A1M0S3G0S31S34Z33S33Z2Z40A2A2R2A2VTR;S8cS4aVJAv;S64A1S85R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  apply (X_X_sretG X_sretc X_sretc1 X_sretc2 X_sretc3 C_loop sel_c objsNc ohNc otNc s_sretc 50 (SAlu ALU_SUB vLn vJ) rho tp b tp0 X_sretc1_eq objsNc_eq);
    [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
    | vm_compute; reflexivity | vm_compute; reflexivity | exact X_sretc2_eq | exact objsNc2_eq | | vm_compute; reflexivity
    | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
    | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
    | exact X_sretc3_eq | vm_compute; reflexivity | innth 10 | lia | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
    | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | exact Hb].
  intros o Ho. cbn in Ho. unfold objclass. destruct Ho as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]; cbn; auto 12.
Qed.
Lemma X_X_sretn : ltac2:(tb__ "0|1|
S16S7S8fQ40A1A1M0S3G0S31S34Z33S33Z2Z40A2A2R2A2VTR;S8cS4aVJAv;S64A1S86R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  apply (X_X_sretG X_sretn X_sretn1 X_sretn2 X_sretn3 C_nul sel_n objsNn ohNn otNn s_sretn 45 z0 rho tp b tp0 X_sretn1_eq objsNn_eq);
    [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
    | vm_compute; reflexivity | vm_compute; reflexivity | exact X_sretn2_eq | exact objsNn2_eq | | vm_compute; reflexivity
    | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
    | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
    | exact X_sretn3_eq | vm_compute; reflexivity | innth 11 | lia | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
    | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | exact Hb].
  intros o Ho. cbn in Ho. unfold objclass. destruct Ho as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]; cbn; auto 12.
Qed.

Lemma X_X_ret : ltac2:(tb__ "0|1|
S16S7S8fQ40A1A1M0S3G0VTR;S8cS4aVJAv;S63A1S84R4R3A5VFAM;R2R1A2A2Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0.
  apply (TR_pre (fun w => exists rho', SPA segs (JAv ndK) P_ok rho' tp w)).
  { intros [tr [ms md]] H1.
    pose proof (JA_unslot segs HTOP AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_ir CST FB FF) FB FF BX PTrue HKc HNP tv_ir [] bd_loop vH vNXl vCAPl vP vNn
                  X_ret (objsR ++ [ohR]) osR rho tp tr ms md objsR_eq ltac:(vm_compute; reflexivity) H1) as H2.
    rewrite X_ret2_eq in H2. set (rho1 := rho_absorb rho [osR] (vms md tp ms)) in H2.
    pose proof (JA_close segs HTOP AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_ir CST FB FF) FB FF BX PTrue HKc HBX HNP tv_ir [] bd_loop [] vH vNXl vCAPl vUc
                  X_ret2 objsR ohR rho1 tp tr ms md objsR2_eq ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; left; reflexivity) eq_refl ltac:(vm_compute; reflexivity) H2) as H3.
    rewrite X_ret3_eq in H3. set (rho2 := rho_absorb rho1 [ohR] (vms md tp ms)) in H3.
    exists (rho_sub rho2 s_ret).
    apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 (P0_ir CST FB FF) FB FF BX PTrue HKc X_ret3 P_ok s_ret (NDA tv_ir [] [] (AHead vH true)) ndK);
      [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | exact H3]. }
  apply TR_exw. intros rho'. apply X_P_ok.
Qed.

Lemma exits_okT : ltac2:(tb__ "0|3|
S39S96S8S3S15A2M0S16S7S8fQ40A1A1M1G1Sa6S8S8S39S96A2M2G0A2S9G2G0S9S39S96R6R5A4R4A4S89A3VTR;S8cS4aVJAv;R6A1R7R4R3A5VFAM;Sa0S9G2G0S9S39S96R7R6A4R5A4R4A2R2A2A2F_;Ftp0;Ftp;Frho;FrvX;FndX;FX;").
Proof.
  intros X ndX rvX rho tp tp0 Hin. cbn [In exitsI] in Hin.
  destruct Hin as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[]]]]]]]]]]]]]]; injection H as <- <- <-.
  - apply X_X_open. meas.
  - apply X_X_nohead. meas.
  - apply X_X_fitc. meas.
  - apply X_X_fitn. meas.
  - apply X_X_nofit. meas.
  - apply X_X_K1. meas.
  - apply X_X_K2. meas.
  - apply X_E_m. meas.
  - apply X_X_sretc. meas.
  - apply X_X_sretn. meas.
  - apply X_X_ret.
  - apply POST. left. reflexivity.
  - apply POST. right. left. reflexivity.
Qed.
End X.

Section Safety.
Variable ok : world -> Prop.
Hypothesis Hok : ltac2:(tb__ "0|0|
Sa4S4aVKc;Vok;A3").
Hypothesis AC : ltac2:(tb__ "0|0|
SdfS4aSd8VAInv;VCST;VXGL;A5").

Theorem intern_rest_sum : ltac2:(tb__ "0|0|
S7S8fQ40A1A1Sc2S4aVok;S8cS4aS9fVAInv;VCST;VXGL;VKc;Sa9VCST;VFB;VFF;A3VFB;VFF;VBX;S97S57AaS6eVrho0;R1A5SbaS4aS95Vrho0;R1Sd6A5A4Ftp0;").
Proof.
  intros tp0.
  eapply triple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_sound_JA segs AInv CST XGL NF Kc rho0 (P0_ir CST FB FF) FB FF BX PTrue HKc ALA FUEL_ir cutpcs_ir 100
                (map edropA cutsI) (map edropA exitsI) ok (Q tp0) Hok (ejcertA_jcertA segs NF _ _ _ _ _ ejcertI_ok))
         with (ndT := nd0); [|left; reflexivity].
       intros X ndX rho tp Hin. apply in_map_iff in Hin as ([[X' nd'] rv] & E0' & Hin). cbn in E0'. injection E0' as <- <-.
       apply (exits_okT (triple segs ok) (fun _ _ w => SPfamGTA segs (map nI (map edropA cutsI)) w \/ Q tp0 w)
                (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok) (@triple_ex segs ok) (call_soundPA3 segs ok))
         with (rvX := rv) (tp0 := tp0).
       - intros Ai rho1 tp1. apply (aca_malloc _ _ _ _ _ AC); [first [left; reflexivity | right; left; reflexivity | right; right; left; reflexivity] | exact HKc| |]. exact (proj1 Hok). exact (proj2 Hok).
       - intros T nd rv' rho1 tp1 b tp2 HinT _. apply (reenter_cutJA segs AInv CST XGL NF Kc rho0 (P0_ir CST FB FF) FB FF BX PTrue ok (map edropA cutsI) T nd).
         apply in_map_iff. exists (T, nd, rv'). auto.
       - intros P nd rho1 tp1 b tp2 HinP. apply (exit_postGA segs AInv CST XGL NF Kc (P0_ir CST FB FF) FB FF BX PTrue ok rho0 tp0 nd Posts_ir P). exact HinP.
       - exact Hin. }
  intros w Hw. apply JA_pre_intro. exact Hw.
Qed.
End Safety.

Section Existence.
Hypothesis ACX : ltac2:(tb__ "0|0|
Se0S4aSd8VAInv;VCST;VXGL;A5").

Theorem intern_rest_sum_ex : ltac2:(tb__ "0|0|
S7S8fQ40A1A1Sc1S4aS8cS4aS9fVAInv;VCST;VXGL;VKc;Sa9VCST;VFB;VFF;A3VFB;VFF;VBX;S97S57AaS6eVrho0;R1A5SbaS4aS95Vrho0;R1Sd6A5A3Ftp0;").
Proof.
  intros tp0.
  eapply etriple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_complete_JA segs AInv CST XGL NF Kc rho0 (P0_ir CST FB FF) FB FF BX PTrue HKc ALA FUEL_ir cutpcs_ir 100 cutsI exitsI (Q tp0) ejcertI_ok)
         with (ndT := nd0) (rv := (100, z0)); [|left; reflexivity].
       intros X ndX rv rho tp Hin.
       apply (exits_okT (etriple segs) (fun b _ w => SPfamETA segs (map (enodeIA AInv CST XGL NF Kc rho0 (P0_ir CST FB FF) FB FF BX PTrue) cutsI) b w \/ Q tp0 w)
                (TRe_facts segs) (TRe_ex segs) (TRe_pre segs) (@etriple_ex segs) (call_completePA3 segs)) with (tp0 := tp0).
       - intros Ai rho1 tp1. apply (acx_malloc _ _ _ _ _ ACX); [first [left; reflexivity | right; left; reflexivity | right; right; left; reflexivity] | exact HKc].
       - intros T nd rv' rho1 tp1 b tp2 HinT Hm. apply (ereenter_cutJA segs AInv CST XGL NF Kc rho0 (P0_ir CST FB FF) FB FF BX PTrue cutsI T nd rv'); [exact HinT | exact Hm].
       - intros P nd rho1 tp1 b tp2 HinP. apply (eexit_postGA segs AInv CST XGL NF Kc (P0_ir CST FB FF) FB FF BX PTrue rho0 tp0 nd Posts_ir P). exact HinP.
       - exact Hin. }
  intros w Hw. apply JA_pre_intro. exact Hw.
Qed.
End Existence.
End Sum.
End Lib_intern_rest_pf.

(* [comment removed for export] *)
Module Lib_tess_polygon_chk3.

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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Lib_tess_scale2d.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_tess_polygon_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nt.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_tess_scale2d OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n2.Lib_tess_run2d_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_tess_polygon_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_tess_polygon_cstates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nt.Lib_tess_polygon_chk0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import TessPolygonAddr.
Lemma cc_11 : CC 11 Kext = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_12 : CC 12 Ke1 = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_13 : CC 13 Ke2 = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_14 : CC 14 Ke3 = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_15 : CC 15 Kproj = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_16 : CC 16 Kbbp = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_17 : CC 17 K708 = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_18 : CC 18 K830 = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End Lib_tess_polygon_chk3.

(* [comment removed for export] *)
Module Start6JStates.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "positive"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "sprop"; "SAlu"; "SPUle"; "SVar"; "reg_sv"; "sstate"; "SPAlign"; "sobj"; "ss_objs"; "ss_pc"; "swf"; "mkSS"; "sprop_eqb"; "ss_facts"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_next"; "ss_regs"; "ss_resv"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "@Corelib.Init.Datatypes"; "cons"; "bool"; "prod"; "nil"; "pair"; "list"; "true"; "app"; "Some"; "option"; "length"; "nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "FE"; "ax_X"; "ax_base"; "ax_setS"; "axwf"; "mkAX"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "instr"; "Ecall"; "@Stdlib.ZArith.BinInt.Z"; "sub"; "eqb"; "mul"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nz.Start6JStates"; "E_s17"; "CF16"; "ebot16"; "DX16"; "DX17"; "F17_of"; "F17n"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nv.Start6Run7"; "F17_7"; "IP16_7"; "IPm_7"; "IPr_7"; "M16_7"; "R16_7"; "s16_7"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Start6States"; "c1"; "R16b"; "classes16"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.StartALib"; "SHB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA"; "noX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Start4States"; "ECALL_MMAP"; "restate_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nt.Start6Run0"; "F17_0"; "IP16_0"; "IPm_0"; "IPr_0"; "M16_0"; "R16_0"; "s16_0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nt.Start6Run1"; "F17_1"; "IP16_1"; "IPm_1"; "IPr_1"; "M16_1"; "R16_1"; "s16_1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nt.Start6Run2"; "F17_2"; "IP16_2"; "IPm_2"; "IPr_2"; "M16_2"; "R16_2"; "s16_2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nt.Start6Run3"; "F17_3"; "IP16_3"; "IPm_3"; "IPr_3"; "M16_3"; "R16_3"; "s16_3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nv.Start6Run4"; "F17_4"; "IP16_4"; "IPm_4"; "IPr_4"; "M16_4"; "R16_4"; "s16_4"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nv.Start6Run5"; "F17_5"; "IP16_5"; "IPm_5"; "IPr_5"; "M16_5"; "R16_5"; "s16_5"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nv.Start6Run6"; "F17_6"; "IP16_6"; "IPm_6"; "IPr_6"; "M16_6"; "R16_6"; "s16_6"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartGlueA"; "bump_next"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "instr_at"; "@Stdlib.Lists.List"; "In"; "existsb"; "forallb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import SysSpec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymCFG Glue3 SymObj SymHeap SymEntail SymCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SysCallA EntailA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.StartALib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import StartDefsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nt.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nv.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Start4States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Start6States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.StartMemsetZ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nt.Start6Run0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nt.Start6Run1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nt.Start6Run2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nt.Start6Run3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nv.Start6Run4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nv.Start6Run5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nv.Start6Run6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nv.Start6Run7.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition M16_of (t : Z) : axst := ltac2:(tb__ "0|3|
S1S27Lt;Vt;S51S0S0S27Lp;R1S0S0S27Lp0;M0R1S0S42Lp1;S0S0S27Lp1;M1R1S0S42Lp2;M2G2S74X0x3Lp1;S66X0x3Lp0;S0G0R1S0G1R1G2G2S7bX0x3Lp1;S0G1R1G2G2S6dX0x3Lp1;S5fX0x3Lp0;S58X0x3Lp;S0S42Lp;X1x3").
Definition s16_of (t : Z) : wsub := ltac2:(tb__ "0|3|
S1S3dLt;Vt;S53S0S0S3dLp;R1S0S0S3dLp0;M0R1S0S44Lp1;S0S0S3dLp1;M1R1S0S44Lp2;M2G2S76X0x3Lp1;S68X0x3Lp0;S0G0R1S0G1R1G2G2S7dX0x3Lp1;S0G1R1G2G2S6fX0x3Lp1;S61X0x3Lp0;S5aX0x3Lp;S0S44Lp;X1x3").
Definition R16_of (t : Z) : list sobj := ltac2:(tb__ "0|4|
S1S20SbA1M0Lt;Vt;S52S0S0G0Lp;R1S0S0G0Lp0;M1R1S0S43Lp1;S0S0G0Lp1;M2R1S0S43Lp2;M3G3S75X0x3Lp1;S67X0x3Lp0;S0G1R1S0G2R1G3G3S7cX0x3Lp1;S0G2R1G3G3S6eX0x3Lp1;S60X0x3Lp0;S59X0x3Lp;S0S43Lp;X1x3").
Definition IP16_of (t : Z) : axst := ltac2:(tb__ "0|3|
S1S27Lt;Vt;S4eS0S0S27Lp;R1S0S0S27Lp0;M0R1S0S3fLp1;S0S0S27Lp1;M1R1S0S3fLp2;M2G2S71X0x3Lp1;S63X0x3Lp0;S0G0R1S0G1R1G2G2S78X0x3Lp1;S0G1R1G2G2S6aX0x3Lp1;S5cX0x3Lp0;S55X0x3Lp;S0S3fLp;X1x3").
Definition IPm_of (t : Z) : sstate := ltac2:(tb__ "0|3|
S1S9Lt;Vt;S4fS0S0S9Lp;R1S0S0S9Lp0;M0R1S0S40Lp1;S0S0S9Lp1;M1R1S0S40Lp2;M2G2S72X0x3Lp1;S64X0x3Lp0;S0G0R1S0G1R1G2G2S79X0x3Lp1;S0G1R1G2G2S6bX0x3Lp1;S5dX0x3Lp0;S56X0x3Lp;S0S40Lp;X1x3").
Definition IPr_of (t : Z) : axst := ltac2:(tb__ "0|3|
S1S27Lt;Vt;S50S0S0S27Lp;R1S0S0S27Lp0;M0R1S0S41Lp1;S0S0S27Lp1;M1R1S0S41Lp2;M2G2S73X0x3Lp1;S65X0x3Lp0;S0G0R1S0G1R1G2G2S7aX0x3Lp1;S0G1R1G2G2S6cX0x3Lp1;S5eX0x3Lp0;S57X0x3Lp;S0S41Lp;X1x3").
Definition F17_of (t : Z) : axst := ltac2:(tb__ "0|3|
S1S27Lt;Vt;S4dS0S0S27Lp;R1S0S0S27Lp0;M0R1S0S3eLp1;S0S0S27Lp1;M1R1S0S3eLp2;M2G2S70X0x3Lp1;S62X0x3Lp0;S0G0R1S0G1R1G2G2S77X0x3Lp1;S0G1R1G2G2S69X0x3Lp1;S5bX0x3Lp0;S54X0x3Lp;S0S3eLp;X1x3").

Definition CF16 : list sprop := ltac2:(tb__ "0|d|
S22S4S1bS4SaP4fM0ZfA2S1bS4SaP50M1ZcM2A2S1eS4A1M3A3A3S22S4S29G1S7G0A1M4A2S1bS4S6S3S32Z7fff7f800000Z7000M5A2A1G4A2S1bS4S6G4S3S32S35Z2Z2fA2M6Z800000M7A2A1A2S1bS4S6S5S2fS7P1A1M8S3S32S32Na0M9G7A2G5A2A1A3G4A2S1bS4S6G4S5S2fG8S3S32Zf5fMaG7A2A1A3A2S1bS4SaP51MbG2A2S1bS4S6S5S2fG8S3G9A1A3S7GbA1McA2S1bS4S6GcS5S2fG8S3GaA1A3A2S1bS4S6GcS3G6A1A2S1bS4S6S3Z7fff80000000A1GcA2G3A3A3A3A3A3A3A3A3A3A3A3").

Definition ebot16 (t : Z) : sv := ltac2:(tb__ "0|1|
S1cS2L_;S33Vt;Z0A2S7P4fA1M0S5S2fG0S3S34Z1000Vt;A2A1A3X1cx2").
Definition DX16 (t : Z) : list (sv * sv) := ltac2:(tb__ "0|2|
S1bS1dS2S2A2M0S1fS2S2S38Vt;A1S5S2fS7P51A1M1S3N800000A1A3A4S1bG0S1fS2S2S5S2fS7P4fA1S3S45Vt;A1A1A3G1A4S1eG0A1A3A3").

Definition F17n (t : Z) : sstate := bump_next (ax_S (F17_of t)) 81%positive.

Definition canon17 (S : sstate) : axst := ltac2:(tb__ "0|0|
S4cS39Z0A1VS;A2S9S2eSfSdR1A1S16R1A1S13R1A1S12R1A1S17R1A1ScR1A1S22S4S37S11S46A1A3P53S14R1A1A9S1eS1dS2S2A2A1S3S48A1A3TS';").
Definition E_s17 : axst := Eval vm_compute in canon17 (F17n 0).

Definition DX17 (t : Z) : list (sv * sv) := ltac2:(tb__ "0|3|
S1bS1dS2S2A2M0S1fS2S2S38Vt;A1S5S2fS7P51A1M1S3N800000A1A3A4M2S1bG0S1fS2S2S5S2fS7P4fA1S3S45Vt;A1A1A3G1A4S1bG0G2S1eG0A1A3A3A3").

Lemma sd17 : ltac2:(tb__ "0|5|
S1S81S1R1S47A3S1aS20S4A1M0G0S19S18S24S1dS20S1dS2S2A2A1M1G0A2M2A1S7fS7eS3cR3A1M3P53A2S28S36A1M4A2S23G2S1fG1G0S3aR3A1R1A4A2A3S19S18S1cS83S4S4S82S4S10R1A1S37A3Lf;R1A3S21A3S19S18S1cSeG4A1S21A3S19S18S1cSeG3A1S21A3S18S1cS2dS2cS49S3bR3A1A1G3A2A1S21A3A2A2A2A2Lnf;A2F_;Ft;").
Proof.
  intros t Ht. destruct Ht as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]; eexists;
    (split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | split; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]]]).
Qed.

Lemma E_s17_at : ltac2:(tb__ "0|4|
S19S18S1SdS28S36A1M0A1M1S4bA3S19S18S0S15G0A1P53A3S19S18S24S30A1S80S4aG1A2S23S30S31A2A3S19S18S20S1dS2S2A2M2A1S2aS36A1S1eG2A1A3S19S18S2S2bS36A1S3S48A1A3S19S18S26S25SbScG0A1A2U19A3S19S18S2S8G0Z11A2S3ZdeA1A3S19S18S2S8G0ZaA2S3Z0A1M3A3S19S18S2S8G0ZbA2S3Zb09000A1A3S19S18S2S8G0ZcA2S3Z3A1A3S19S18S2S8G0ZdA2S3Z22A1A3S19S18S2S8G0ZeA2S3ZffffffffffffffffA1A3S18S2S8G0ZfA2G3A3A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
End Start6JStates.

(* [comment removed for export] *)
Module Lib_tess_polygon_chk4.

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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Lib_tess_scale2d.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_tess_polygon_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nt.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_tess_scale2d OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n2.Lib_tess_run2d_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_tess_polygon_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_tess_polygon_cstates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nt.Lib_tess_polygon_chk0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import TessPolygonAddr.
Lemma cc_19 : CC 19 T_sc3 = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_20 : CC 20 T_sc4 = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_21 : CC 21 T_r2 = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_22 : CC 22 Kaa4 = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_23 : CC 23 Kb08 = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_24 : CC 24 Kb14 = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_25 : CC 25 Kd10 = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_26 : CC 26 Kb64 = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_27 : CC 27 Kd60 = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_28 : CC 28 Ktail = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_29 : CC 29 C_fin = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_30 : CC 30 C_b6cK = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_31 : CC 31 T_sfI = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_32 : CC 32 T_sfK = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End Lib_tess_polygon_chk4.

