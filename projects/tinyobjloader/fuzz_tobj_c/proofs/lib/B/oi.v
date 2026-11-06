(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_handle_f_s10.

(* [comment removed for export] *)
Module Lib_handle_f_eqs.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Init.Datatypes"; "Some"; "option"; "cons"; "list"; "nil"; "prod"; "pair"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "axform"; "AXMerge"; "AXSelect"; "AXSplit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_defs.VN"; "Pre_vr"; "P_keep"; "P_fail"; "P_grown"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "SLit"; "sprop"; "sv"; "ss_objs"; "SPUle"; "DUnknown"; "SAlu"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "T_afterA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s2"; "XkeepF"; "xf_backV"; "E_fv"; "E_mi"; "E_mm"; "R_fv"; "R_mi"; "R_mm"; "s_fv"; "s_mi"; "s_mm"; "vr_need"; "E_dg"; "E_fv0"; "XF1"; "XFV"; "pDfv"; "pKfv"; "want_of"; "E_fv1"; "R_dg"; "T_dg0"; "T_fvf0"; "T_fvg0"; "T_fvk0"; "T_mif0"; "T_mig0"; "T_mik0"; "T_mmf0"; "T_mmg0"; "T_mmk0"; "objs_fv0"; "s_dg"; "E_dg0"; "E_mi0"; "E_mm0"; "NFV"; "NMI"; "NMM"; "NSG"; "T_dg"; "T_fvf"; "T_fvg"; "T_fvk"; "T_mif"; "T_mig"; "T_mik"; "T_mmf"; "T_mmg"; "T_mmk"; "sh_fv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_defs"; "optAp"; "xf_vr"; "pA"; "pDco"; "X_body"; "E_co"; "pD2"; "R_co"; "pKco"; "s_co"; "C_pro0"; "T_sm"; "T_sm1"; "X_pro"; "Xkeep"; "fv_d"; "mi_d"; "mm_d"; "sg_d"; "xf_back"; "E_sm0"; "O_Wf"; "Pre_sm"; "R_sm"; "T_cof0"; "T_cog0"; "T_cok0"; "objs_pro"; "objs_sm1"; "pK2"; "pQ"; "reshapeA"; "s_sm"; "tr_d"; "C_pre"; "C_pro"; "E_co0"; "L_sm"; "T_cof"; "T_cog"; "T_cok"; "X_hf0"; "co_need"; "mid_slot"; "pT0"; "rp_d"; "sel_last"; "sg_c"; "sh_pro"; "slot_obj"; "ts_d"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Lib_diag_append"; "Pre_da"; "P_da"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s4"; "contTR"; "E_trb"; "E_trg"; "R_trb"; "R_trg"; "s_trb"; "s_trg"; "E_tdg"; "R_tdg"; "T_tdg0"; "s_tdg"; "E_tdg0"; "E_trb0"; "E_trg0"; "T_tdg"; "T_trbf"; "T_trbg"; "T_trbk"; "T_trgf"; "T_trgg"; "T_trgk"; "XTR"; "pDtr"; "pKtr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_setX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s3"; "E_sg"; "R_sg"; "s_sg"; "XMM"; "pDmm"; "pKmm"; "T_sgf0"; "T_sgg0"; "T_sgk0"; "E_sg0"; "T_sgf"; "T_sgg"; "T_sgk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s1"; "T_pure"; "E_da"; "E_pc"; "E_pc1"; "sel_da"; "R_da"; "R_pc"; "T_da0"; "T_pc0"; "T_pc1"; "s_da"; "s_pc"; "E_da0"; "E_pc0"; "T_da"; "T_pc"; "pc_need"; "sel_pc"; "xf_pc"; "xslot"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "@Stdlib.Lists.List"; "removelast"; "last"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s5"; "E_rp"; "E_ts"; "E_rp0"; "E_ts0"; "R_rp"; "R_ts"; "T_rpk"; "T_tsk"; "contRP"; "contTS"; "need_facts"; "s_rp"; "s_ts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_parse_corner2"; "Pre_pc"; "P_ret"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS";
"shadow_release_stateA"; "frame_open_stateA"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs"; "hF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "T_afterA"].
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
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAS.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import ResidualA AxArrA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Lib_scan_double Lib_parse_corner2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Asan_set_shadow_iface.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_parse_corner2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Lib_diag_append OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Asan_set_shadow_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs Lib_handle_f_defs Lib_handle_f_s1 Lib_handle_f_s2 Lib_handle_f_s3 Lib_handle_f_s4 Lib_handle_f_s5 Lib_handle_f_s6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require od.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_handle_f_s9 Lib_handle_f_s9b Lib_handle_f_s10.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o9.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Lib_handle_f_s7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.od.Lib_handle_f_s8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s9b OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Lib_handle_f_epi.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_tess_polygon_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_arith.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import MemoFast.
Import ListNotations.
Import ScanDoubleAddr VRAddr RA.ReallocAddr ParseCornerAddr DiagAppendAddr HFAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma R_sm_eq : ltac2:(tb__ "0|1|
S3S5S7S14A1M0A1S1dS66S68S72A3S4G0S69A2A3"). Proof. vmc. Qed.
Lemma T_sm_eq : ltac2:(tb__ "0|0|
S3S0Sd8S68S66S72S69S77A5S5dA3"). Proof. vmc. Qed.
Lemma T_sm1_eq : ltac2:(tb__ "0|0|
S3S5S0A1SbS5dS6ScSeS80S5dU3A2A1S8ScA1A3A2S4S0S5eA2A3"). Proof. vmc. Qed.
Lemma objs_sm1_eq : ltac2:(tb__ "0|0|
S3S7S14A1Sc3S14S18S1S5eA1A1A2S6eA3"). Proof. vmc. Qed.
Lemma C_pro0_eq : ltac2:(tb__ "0|0|
S3S0Sd5S5eS6eS7bPa0Z200A5S5cA3"). Proof. vmc. Qed.
Lemma C_pro_eq : ltac2:(tb__ "0|0|
S3S0Sa0S5cS6S9S17S17A2SaS17S17Sd7S15Z0A1A4S2S5cA1A3A2S75A3"). Proof. vmc. Qed.
Lemma sh_pro_eq : ltac2:(tb__ "0|0|
S3S14Sc4S14S18S1S5fA1A1S67A3S82A3"). Proof. vmc. Qed.
Lemma objs_pro_eq : ltac2:(tb__ "0|0|
S3S7S14A1Sc3S14S18S1S5fA1A1A2S6dA3"). Proof. vmc. Qed.
Lemma C_pre_eq : ltac2:(tb__ "0|0|
S3S0Sd4S5fS6dPa0S8S9S85S85A2A1A4S74A3"). Proof. vmc. Qed.
Lemma E_co_eq : ltac2:(tb__ "0|0|
S3S0S51S7cS70A1S52SbS76S53U13Z2d0A2A2A1A2S57A3"). Proof. vmc. Qed.
Lemma R_co_eq : ltac2:(tb__ "0|1|
S3S5S7S14A1M0A1S1dS57S10S5bA3S4G0S59A2A3"). Proof. vmc. Qed.
Lemma T_cok0_eq : ltac2:(tb__ "0|0|
S3S0S1cS10S57S5bS59S11S60S55A1A6S6cA3"). Proof. vmc. Qed.
Lemma T_cof0_eq : ltac2:(tb__ "0|0|
S3S0S1cS10S57S5bS59S12S60S55A1A6S6aA3"). Proof. vmc. Qed.
Lemma T_cog0_eq : ltac2:(tb__ "0|0|
S3S0S1cS10S57S5bS59S13S60S55A1A6S6bA3"). Proof. vmc. Qed.
Lemma T_cok_eq : ltac2:(tb__ "0|0|
S3S5S0A1SbS6cS65A2S4S0S7aA2A3"). Proof. vmc. Qed.
Lemma T_cof_eq : ltac2:(tb__ "0|0|
S3S5S0A1SbS6aS65A2S4S0S78A2A3"). Proof. vmc. Qed.
Lemma T_cog_eq : ltac2:(tb__ "0|0|
S3S5S0A1SbS6bS65A2S4S0S79A2A3"). Proof. vmc. Qed.

Lemma E_pc1_eq : ltac2:(tb__ "0|0|
S3S5S0A1SbSbbSc0A2S4S0Sb1A2A3"). Proof. vmc. Qed.
Lemma E_pc_eq : ltac2:(tb__ "0|0|
S3S0S51SbeS7eS70A2Sa0S71Sb1U22S83S58S54A2A3S6S9S17S17A2Sc1S58S54A2S2Sb1A1A3A2A2Sb0A3"). Proof. vmc. Qed.
Lemma R_pc_eq : ltac2:(tb__ "0|1|
S3S5S7S14A1M0A1S1dSb0Sd2Sb9A3S4G0Sb4A2A3"). Proof. vmc. Qed.
Lemma T_pc0_eq : ltac2:(tb__ "0|0|
S3S0SaeSd2Sb0Sb9Sb4Sd3A5Sb6A3"). Proof. vmc. Qed.
Lemma T_pc1_eq : ltac2:(tb__ "0|0|
S3S0S71Sb6U2S7dS58S54S1aA3A3Sb7A3"). Proof. vmc. Qed.
Lemma T_pc_eq : ltac2:(tb__ "0|1|
S3S0Sa0S52SbSb7S6ScSeSbfA1S6ScSdU0A1S6ScSdU20A1M0S6ScG0S8ScA1A3A3A3A3A2A1S56S58S6fA2A2SbdA3"). Proof. vmc. Qed.
Lemma E_da_eq : ltac2:(tb__ "0|0|
S3S5S0A1SbSbaS6ScSfU0S15N60A1A2S8ScA1A3A2S4S0SafA2A3"). Proof. vmc. Qed.
Lemma R_da_eq : ltac2:(tb__ "0|1|
S3S5S7S14A1M0A1S1dSafS86Sb8A3S4G0Sb3A2A3"). Proof. vmc. Qed.
Lemma T_da0_eq : ltac2:(tb__ "0|0|
S3S0SaeS86SafSb8Sb3S87A5Sb5A3"). Proof. vmc. Qed.
Lemma T_da_eq : ltac2:(tb__ "0|0|
S3S0Sa0S52SbSb5S6ScSeSb2A1S6ScSdU0A1S8ScA1A3A3A2A1S56S58S6fA2A2SbcA3"). Proof. vmc. Qed.

Lemma E_dg_eq : ltac2:(tb__ "0|0|
S3S5S0A1SbS3fS6ScSfU0S15N60A1A2S8ScA1A3A2S4S0S2aA2A3"). Proof. vmc. Qed.
Lemma R_dg_eq : ltac2:(tb__ "0|1|
S3S5S7S14A1M0A1S1dS2aS86S3eA3S4G0S32A2A3"). Proof. vmc. Qed.
Lemma T_dg0_eq : ltac2:(tb__ "0|0|
S3S0SaeS86S2aS3eS32S87A5S33A3"). Proof. vmc. Qed.
Lemma T_dg_eq : ltac2:(tb__ "0|0|
S3S0Sa0S52SbS33S6ScSeSb2A1S6ScSdU0A1S8ScA1A3A3A2A1S56S55S5aA2A2S46A3"). Proof. vmc. Qed.
Lemma E_mi_eq : ltac2:(tb__ "0|0|
S52SbS40S53UfZ1f0A2A2A1S0S3S0S51S29ZcS30R1A1S43S54A1A3R1A2S21A3TE;"). Proof. vmc. Qed.
Lemma R_mi_eq : ltac2:(tb__ "0|1|
S3S5S7S14A1M0A1S1dS21S10S27A3S4G0S24A2A3"). Proof. vmc. Qed.
Lemma T_mik0_eq : ltac2:(tb__ "0|0|
S3S0S1cS10S21S27S24S11S1eS62S56S55S5aA2A2A6S39A3"). Proof. vmc. Qed.
Lemma T_mif0_eq : ltac2:(tb__ "0|0|
S3S0S1cS10S21S27S24S12S1eS62S56S55S5aA2A2A6S37A3"). Proof. vmc. Qed.
Lemma T_mig0_eq : ltac2:(tb__ "0|0|
S3S0S1cS10S21S27S24S13S1eS62S56S55S5aA2A2A6S38A3"). Proof. vmc. Qed.
Lemma T_mik_eq : ltac2:(tb__ "0|0|
S3S5S0A1SbS39S1fUeU1cZ1f0A3A2S4S0S4cA2A3"). Proof. vmc. Qed.
Lemma T_mif_eq : ltac2:(tb__ "0|0|
S3S5S0A1SbS37S1fUeU1cZ1f0A3A2S4S0S4aA2A3"). Proof. vmc. Qed.
Lemma T_mig_eq : ltac2:(tb__ "0|0|
S3S5S0A1SbS38S1fUeU1cZ1f0A3A2S4S0S4bA2A3"). Proof. vmc. Qed.
Lemma sh_fv_eq : ltac2:(tb__ "0|0|
S3S14Sc4S14S18S1S2bA1A1S67A3S50A3"). Proof. vmc. Qed.
Lemma objs_fv0_eq : ltac2:(tb__ "0|0|
S3S7S14A1Sc3S14S18S1S2bA1A1A2S3dA3"). Proof. vmc. Qed.
Lemma E_fv1_eq : ltac2:(tb__ "0|1|
S3S0Sd4S2bS3dPa0S6S9S85S85A2M0SaS85S85Z20Z4A4S8G0A1A3A4S31A3"). Proof. vmc. Qed.
Lemma E_fv_eq : ltac2:(tb__ "0|0|
S52SbS31S53U10Z210A2A2A1S0S3S0S51S29Z4S30R1A1S42S54A1A3R1A2S20A3TE;"). Proof. vmc. Qed.
Lemma R_fv_eq : ltac2:(tb__ "0|1|
S3S5S7S14A1M0A1S1dS20S10S26A3S4G0S23A2A3"). Proof. vmc. Qed.
Lemma T_fvk0_eq : ltac2:(tb__ "0|0|
S3S0S1cS10S20S26S23S11S1eS61S2cA2A6S36A3"). Proof. vmc. Qed.
Lemma T_fvf0_eq : ltac2:(tb__ "0|0|
S3S0S1cS10S20S26S23S12S1eS61S2cA2A6S34A3"). Proof. vmc. Qed.
Lemma T_fvg0_eq : ltac2:(tb__ "0|0|
S3S0S1cS10S20S26S23S13S1eS61S2cA2A6S35A3"). Proof. vmc. Qed.
Lemma T_fvk_eq : ltac2:(tb__ "0|0|
S3S5S0A1SbS36S1fUfU1dZ210A3A2S4S0S49A2A3"). Proof. vmc. Qed.
Lemma T_fvf_eq : ltac2:(tb__ "0|0|
S3S5S0A1SbS34S1fUfU1dZ210A3A2S4S0S47A2A3"). Proof. vmc. Qed.
Lemma T_fvg_eq : ltac2:(tb__ "0|0|
S3S5S0A1SbS35S1fUfU1dZ210A3A2S4S0S48A2A3"). Proof. vmc. Qed.
Lemma E_mm_eq : ltac2:(tb__ "0|0|
S52SbS41S53U11Z230A2A2A1S0S3S0S51S29Z4S30R1A1S44S54A1A3R1A2S22A3TE;"). Proof. vmc. Qed.
Lemma R_mm_eq : ltac2:(tb__ "0|1|
S3S5S7S14A1M0A1S1dS22S10S28A3S4G0S25A2A3"). Proof. vmc. Qed.
Lemma T_mmk0_eq : ltac2:(tb__ "0|0|
S3S0S1cS10S22S28S25S11S1eS63S2dS2eS2fA2A2A6S3cA3"). Proof. vmc. Qed.
Lemma T_mmf0_eq : ltac2:(tb__ "0|0|
S3S0S1cS10S22S28S25S12S1eS63S2dS2eS2fA2A2A6S3aA3"). Proof. vmc. Qed.
Lemma T_mmg0_eq : ltac2:(tb__ "0|0|
S3S0S1cS10S22S28S25S13S1eS63S2dS2eS2fA2A2A6S3bA3"). Proof. vmc. Qed.
Lemma T_mmk_eq : ltac2:(tb__ "0|0|
S3S5S0A1SbS3cS1fU10U1eZ230A3A2S4S0S4fA2A3"). Proof. vmc. Qed.
Lemma T_mmf_eq : ltac2:(tb__ "0|0|
S3S5S0A1SbS3aS1fU10U1eZ230A3A2S4S0S4dA2A3"). Proof. vmc. Qed.
Lemma T_mmg_eq : ltac2:(tb__ "0|0|
S3S5S0A1SbS3bS1fU10U1eZ230A3A2S4S0S4eA2A3"). Proof. vmc. Qed.

Lemma E_sg_eq : ltac2:(tb__ "0|0|
S3S0S51S29Z4S1bSd6S81S15Z1A1A3S45S54A1A3S52SbSaaS53U12Z250A2A2A1A2Sa1A3"). Proof. vmc. Qed.
Lemma R_sg_eq : ltac2:(tb__ "0|1|
S3S5S7S14A1M0A1S1dSa1S10Sa3A3S4G0Sa2A2A3"). Proof. vmc. Qed.
Lemma T_sgk0_eq : ltac2:(tb__ "0|0|
S3S0S1cS10Sa1Sa3Sa2S11S1eS64Sa4Sa5Sa6A2A2A6Sa9A3"). Proof. vmc. Qed.
Lemma T_sgf0_eq : ltac2:(tb__ "0|0|
S3S0S1cS10Sa1Sa3Sa2S12S1eS64Sa4Sa5Sa6A2A2A6Sa7A3"). Proof. vmc. Qed.
Lemma T_sgg0_eq : ltac2:(tb__ "0|0|
S3S0S1cS10Sa1Sa3Sa2S13S1eS64Sa4Sa5Sa6A2A2A6Sa8A3"). Proof. vmc. Qed.
Lemma T_sgk_eq : ltac2:(tb__ "0|0|
S3S5S0A1SbSa9S1fU11U1fZ250A3A2S4S0SadA2A3"). Proof. vmc. Qed.
Lemma T_sgf_eq : ltac2:(tb__ "0|0|
S3S5S0A1SbSa7S1fU11U1fZ250A3A2S4S0SabA2A3"). Proof. vmc. Qed.
Lemma T_sgg_eq : ltac2:(tb__ "0|0|
S3S5S0A1SbSa8S1fU11U1fZ250A3A2S4S0SacA2A3"). Proof. vmc. Qed.

Lemma E_trg_eq : ltac2:(tb__ "0|0|
S3S5S0A1SbS95S53U15Z310A2A2S4S0S8aA2A3"). Proof. vmc. Qed.
Lemma E_trb_eq : ltac2:(tb__ "0|0|
S3S5S0A1SbS94S53U15Z310A2A2S4S0S89A2A3"). Proof. vmc. Qed.
Lemma R_trg_eq : ltac2:(tb__ "0|1|
S3S5S7S14A1M0A1S1dS8aS10S8eA3S4G0S8cA2A3"). Proof. vmc. Qed.
Lemma R_trb_eq : ltac2:(tb__ "0|1|
S3S5S7S14A1M0A1S1dS89S10S8dA3S4G0S8bA2A3"). Proof. vmc. Qed.
Lemma T_trgk_eq : ltac2:(tb__ "0|0|
S3S0S51S6S16S19S15Sc2A1S73A2S8S16A1A3S88S8aS8eS8cS11A4A2S9cA3"). Proof. vmc. Qed.
Lemma T_trgf_eq : ltac2:(tb__ "0|0|
S3S0S88S8aS8eS8cS12A4S9aA3"). Proof. vmc. Qed.
Lemma T_trgg_eq : ltac2:(tb__ "0|0|
S3S0S88S8aS8eS8cS13A4S9bA3"). Proof. vmc. Qed.
Lemma T_trbk_eq : ltac2:(tb__ "0|0|
S3S0S51S6S16S19S15Sc2A1S73A2S8S16A1A3S88S89S8dS8bS11A4A2S99A3"). Proof. vmc. Qed.
Lemma T_trbf_eq : ltac2:(tb__ "0|0|
S3S0S88S89S8dS8bS12A4S97A3"). Proof. vmc. Qed.
Lemma T_trbg_eq : ltac2:(tb__ "0|0|
S3S0S88S89S8dS8bS13A4S98A3"). Proof. vmc. Qed.
Lemma E_tdg_eq : ltac2:(tb__ "0|0|
S3S5S0A1SbS93S6ScSfU0S15N60A1A2S8ScA1A3A2S4S0S8fA2A3"). Proof. vmc. Qed.
Lemma R_tdg_eq : ltac2:(tb__ "0|1|
S3S5S7S14A1M0A1S1dS8fS86S92A3S4G0S90A2A3"). Proof. vmc. Qed.
Lemma T_tdg0_eq : ltac2:(tb__ "0|0|
S3S0SaeS86S8fS92S90S87A5S91A3"). Proof. vmc. Qed.
Lemma T_tdg_eq : ltac2:(tb__ "0|0|
S3S0Sa0S52SbS91S6ScSeSb2A1S6ScSdU0A1S8ScA1A3A3A2A1S9dS9eS9fA2A2S96A3"). Proof. vmc. Qed.

Lemma E_rp_eq : ltac2:(tb__ "0|0|
S3S5S0A1SbSc7S53U14Z2f0A2A2S4S0Sc5A2A3"). Proof. vmc. Qed.
Lemma R_rp_eq : ltac2:(tb__ "0|1|
S3S5S7S14A1M0A1S1dSc5S10Sd0A3S4G0Sc9A2A3"). Proof. vmc. Qed.
Lemma T_rpk_eq : ltac2:(tb__ "0|0|
S3S0S51S6S16S19S15Sc2A1S7fA2S8S16A1A3ScdS11A1A2ScbA3"). Proof. vmc. Qed.
Lemma T_rpf_eq : contRP VN.P_fail = T_rpf. Proof. vmc. Qed.
Lemma T_rpg_eq : contRP VN.P_grown = T_rpg. Proof. vmc. Qed.
Lemma E_ts_eq : ltac2:(tb__ "0|0|
S3S0S51ScfS52SbSc8S53U16Z330A2A2A1A2Sc6A3"). Proof. vmc. Qed.
Lemma R_ts_eq : ltac2:(tb__ "0|1|
S3S5S7S14A1M0A1S1dSc6S10Sd1A3S4G0ScaA2A3"). Proof. vmc. Qed.
Lemma T_tsk_eq : ltac2:(tb__ "0|0|
S3S0S51S6S16S19S15Sc2A1S84A2S8S16A1A3SceS11A1A2SccA3"). Proof. vmc. Qed.
Lemma T_tsf_eq : contTS VN.P_fail = T_tsf. Proof. vmc. Qed.
Lemma T_tsg_eq : contTS VN.P_grown = T_tsg. Proof. vmc. Qed.
End Lib_handle_f_eqs.

(* [comment removed for export] *)
Module Lib_handle_f_eqs2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_setS"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "Some"; "option"; "cons"; "list"; "nil"; "pair"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "SLit"; "sprop"; "SAlu"; "SPUle"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "axform"; "AXSelect"; "AXMerge"; "AXSplit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_defs"; "optAp"; "pA"; "xf_vr"; "reshapeA"; "sel_last"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s2"; "Pre_mc"; "vr_need"; "L_mc1"; "NFV"; "NMI"; "NMM"; "NSG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.od.Lib_handle_f_s8"; "s_g"; "E_g1"; "E_g2"; "E_g3"; "pL"; "E_g1_1"; "E_g1_2"; "g_back"; "E_g1_0"; "E_g1_3"; "R_g1"; "R_g2"; "R_g3"; "E_g2_0"; "E_g3_0"; "T_g1"; "T_g2"; "T_g3"; "cFV"; "cMI"; "cMM"; "cSG"; "lDfv"; "lDmi"; "lDmm"; "lDsg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "T_afterA"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_defs.VN"; "P_keep"; "Pre_vr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Lib_handle_f_epi"; "Pre_f5"; "T_f5f0"; "T_f5o0"; "E_f5f"; "E_f5o"; "L_f5"; "R_f5f"; "R_f5o"; "s_f5f"; "s_f5o"; "xf_shback"; "T_f5f"; "T_f5o"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s6"; "objs_butlast"; "E_pg"; "E_pg0t"; "R_pg"; "s_pg"; "E_pg0"; "E_pg1"; "E_pg2"; "E_pg3"; "Xk_pg"; "E_pg4"; "O_nxt'"; "O_prv'"; "O_rfx'"; "T_pgi0"; "T_pgo0"; "news72"; "optS"; "rt72"; "xf_pg1"; "xf_pg2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS"; "shadow_release_stateA"; "flag_carve_stateA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_defs.PG"; "Pre_pg"; "P_inv"; "P_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Lib_handle_f_s7"; "E_wdg"; "R_wdg"; "T_wdg0"; "s_wdg"; "E_wdg0"; "T_wdg"; "XT"; "sel_wdg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o1.Lib_b_warn"; "Pre_bw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s9"; "E_fv4"; "E_mi4"; "E_mi4_0"; "E_mi4_1"; "E_fv4_0"; "R_fv4"; "R_mi4"; "T_fv4k"; "T_mi4k"; "contFV4"; "contMI4"; "s_fv4"; "s_mi4"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s9b"; "E_mm4"; "E_sg4"; "E_mm4_0"; "E_sg4_0"; "R_mm4"; "R_sg4"; "T_mm4k"; "T_sg4k"; "contMM4"; "contSG4"; "s_mm4"; "s_sg4"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "T_afterA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o3.Lib_b_warn_H"; "P_bwH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s1"; "T_pure"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s5"; "reopenX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s6.AR"; "ts_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_setX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p0.ObjRetileB"; "retile_at"].
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
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAS.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import ResidualA AxArrA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Lib_scan_double Lib_parse_corner2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Asan_set_shadow_iface.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_parse_corner2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Lib_diag_append OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Asan_set_shadow_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs Lib_handle_f_defs Lib_handle_f_s1 Lib_handle_f_s2 Lib_handle_f_s3 Lib_handle_f_s4 Lib_handle_f_s5 Lib_handle_f_s6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require od.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_handle_f_s9 Lib_handle_f_s9b Lib_handle_f_s10.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o9.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Lib_handle_f_s7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.od.Lib_handle_f_s8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s9b OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Lib_handle_f_epi.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_tess_polygon_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_arith.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p0.ObjRetileB.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o1.Lib_b_warn OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o3.Lib_b_warn_H.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import MemoFast.
Import ListNotations.
Import ScanDoubleAddr VRAddr RA.ReallocAddr ParseCornerAddr DiagAppendAddr HFAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma E_pg0t_eq : ltac2:(tb__ "0|0|
S0S1S3S54S60S92S2S54A1U1S61S5fA4A1A2S51A3"). Proof. vmc. Qed.
Lemma E_pg1_eq : ltac2:(tb__ "0|1|
S0S1S17S90S64S51S4fS51A1Pa0S7SbS4S4A2M0SaS4S4Za0Z18A4S7G0SaS4S4Z30Z48A4S9G0A1A3A3A4A2S55A3"). Proof. vmc. Qed.
Lemma E_pg2_eq : ltac2:(tb__ "0|0|
S0S6S1A1S12S55S62A2S5S1S56A2A3"). Proof. vmc. Qed.
Lemma E_pg3_eq : ltac2:(tb__ "0|0|
S0S6S1A1S12S56S63A2S5S1S57A2A3"). Proof. vmc. Qed.
Lemma E_pg4_eq : ltac2:(tb__ "0|0|
S0S1S1bS1bS1bS57U2bS5aA3U2dS5bA3U2fS5cA3S59A3"). Proof. vmc. Qed.
Lemma R_pg_eq : ltac2:(tb__ "0|1|
S0S6S8ScA1M0A1S11S50S67S53A3S5G0S52A2A3"). Proof. vmc. Qed.
Lemma T_pgo0_eq : ltac2:(tb__ "0|0|
S0S1S8cS67S50S53S52S69S58A6S5eA3"). Proof. vmc. Qed.
Lemma T_pgi0_eq : ltac2:(tb__ "0|0|
S0S1S8cS67S50S53S52S68S58A6S5dA3"). Proof. vmc. Qed.

Lemma T_pgo1_eq : pg_back0 T_pgo0 = T_pgo1. Proof. vmc. Qed.
Lemma T_pgo_eq : pg_back T_pgo1 = T_pgo. Proof. vmc. Qed.
Lemma T_pgi1_eq : pg_back0 T_pgi0 = T_pgi1. Proof. vmc. Qed.
Lemma T_pgi_eq : pg_back T_pgi1 = T_pgi. Proof. vmc. Qed.
Lemma T_pgoR_eq : reopen2 T_pgo = T_pgoR. Proof. vmc. Qed.
Lemma T_pgiR_eq : reopen2 T_pgi = T_pgiR. Proof. vmc. Qed.
Lemma E_wdg_eq : ltac2:(tb__ "0|0|
S0S6S1A1S12S6eS7S13S16U0SdN60A1A2S9S13A1A3A2S5S1S6aA2A3"). Proof. vmc. Qed.
Lemma R_wdg_eq : ltac2:(tb__ "0|1|
S0S6S8ScA1M0A1S11S6aS72S6dA3S5G0S6bA2A3"). Proof. vmc. Qed.
Lemma T_wdg0_eq : ltac2:(tb__ "0|0|
S0S1S8eS72S6aS6dS6bS8dA5S6cA3"). Proof. vmc. Qed.
Lemma T_wdg_eq : ltac2:(tb__ "0|0|
S0S1S91S18S12S6cS7S13S14S71A1S7S13S15U0A1S9S13A1A3A3A2A1S70A2S6fA3"). Proof. vmc. Qed.

Lemma E_g1_1_eq : ltac2:(tb__ "0|0|
S0S6S1A1S12S2cS7S13S14S1cS2cU24A2A1S9S13A1A3A2S5S1S29A2A3"). Proof. vmc. Qed.
Lemma E_g1_2_eq : ltac2:(tb__ "0|1|
S0S1S64S29S4fS29A1Pa0S7SbS4S4A2M0SaS4S4Ze0Z24A4S9G0A1A3A4S2aA3"). Proof. vmc. Qed.
Lemma E_g1_3_eq : ltac2:(tb__ "0|0|
S0S1S64S2aS4fS2aA1Pa0S9SbS4S4A2A1A4S2dA3"). Proof. vmc. Qed.
Lemma E_g1_eq : g_site E_g1_3 224 = E_g1. Proof. vmc. Qed.
Lemma R_g1_eq : ltac2:(tb__ "0|1|
S0S6S8ScA1M0A1S11S25S1dS24S25A1A3S5G0S2eA2A3"). Proof. vmc. Qed.
Lemma T_g1_eq : ltac2:(tb__ "0|0|
S0S1S2bS3eS1dS25S24S25A1S2eS1fA5S2dZe0A3S33A3"). Proof. vmc. Qed.
Lemma E_g2_eq : g_site E_g2_0 236 = E_g2. Proof. vmc. Qed.
Lemma R_g2_eq : ltac2:(tb__ "0|1|
S0S6S8ScA1M0A1S11S26S1dS24S26A1A3S5G0S2fA2A3"). Proof. vmc. Qed.
Lemma T_g2_eq : ltac2:(tb__ "0|0|
S0S1S2bS3eS1dS26S24S26A1S2fS1fA5S31ZecA3S34A3"). Proof. vmc. Qed.
Lemma E_g3_eq : g_site E_g3_0 248 = E_g3. Proof. vmc. Qed.
Lemma R_g3_eq : ltac2:(tb__ "0|1|
S0S6S8ScA1M0A1S11S27S1dS24S27A1A3S5G0S30A2A3"). Proof. vmc. Qed.
Lemma T_g3_eq : ltac2:(tb__ "0|0|
S0S1S8fZ26Z27S2bS3eS1dS27S24S27A1S30S1fA5S32Zf8A3A3S35A3"). Proof. vmc. Qed.

Lemma E_mi4_1_eq : ltac2:(tb__ "0|1|
S0S1S64S75S4fS75A1Pa0S7SbS4S4A2M0SaS4S4Z130Z4A4S9G0A1A3A4S76A3"). Proof. vmc. Qed.
Lemma E_mi4_eq : ltac2:(tb__ "0|0|
S0S1S17S1eZcSfS3fS37S28A1SdZ3A1A3S21S19A1A3S18S12S76S1aUfZ1f0A2A2A1A2S74A3"). Proof. vmc. Qed.
Lemma R_mi4_eq : ltac2:(tb__ "0|1|
S0S6S8ScA1M0A1S11S74S41S7fA3S5G0S79A2A3"). Proof. vmc. Qed.
Lemma T_mi4k_eq : ltac2:(tb__ "0|0|
S0S1S17S7SeS10SdS66A1S3bA2S9SeA1A3S7dS40A1A2S7bA3"). Proof. vmc. Qed.
Lemma T_mi4f_eq : contMI4 VN.P_fail = T_mi4f. Proof. vmc. Qed.
Lemma T_mi4g_eq : contMI4 VN.P_grown = T_mi4g. Proof. vmc. Qed.
Lemma E_fv4_eq : ltac2:(tb__ "0|0|
S0S1S17S1eZ4SfS3fS36S28A1SdZ1A1A3S20S19A1A3S18S12S77S1aU10Z210A2A2A1A2S73A3"). Proof. vmc. Qed.
Lemma R_fv4_eq : ltac2:(tb__ "0|1|
S0S6S8ScA1M0A1S11S73S41S7eA3S5G0S78A2A3"). Proof. vmc. Qed.
Lemma T_fv4k_eq : ltac2:(tb__ "0|0|
S0S1S17S7SeS10SdS66A1S3aA2S9SeA1A3S7cS40A1A2S7aA3"). Proof. vmc. Qed.
Lemma T_fv4f_eq : contFV4 VN.P_fail = T_fv4f. Proof. vmc. Qed.
Lemma T_fv4g_eq : contFV4 VN.P_grown = T_fv4g. Proof. vmc. Qed.

Lemma E_mm4_eq : ltac2:(tb__ "0|0|
S0S1S17S1eZ4SfS3fS38S28A1SdZ1A1A3S22S19A1A3S18S12S82S1aU11Z230A2A2A1A2S80A3"). Proof. vmc. Qed.
Lemma R_mm4_eq : ltac2:(tb__ "0|1|
S0S6S8ScA1M0A1S11S80S41S8aA3S5G0S84A2A3"). Proof. vmc. Qed.
Lemma T_mm4k_eq : ltac2:(tb__ "0|0|
S0S1S17S7SeS10SdS66A1S3cA2S9SeA1A3S88S40A1A2S86A3"). Proof. vmc. Qed.
Lemma T_mm4f_eq : contMM4 VN.P_fail = T_mm4f. Proof. vmc. Qed.
Lemma T_mm4g_eq : contMM4 VN.P_grown = T_mm4g. Proof. vmc. Qed.
Lemma E_sg4_eq : ltac2:(tb__ "0|0|
S0S1S17S1eZ4SfS3fS39S28A1SdZ1A1A3S23S19A1A3S18S12S83S1aU12Z250A2A2A1A2S81A3"). Proof. vmc. Qed.
Lemma R_sg4_eq : ltac2:(tb__ "0|1|
S0S6S8ScA1M0A1S11S81S41S8bA3S5G0S85A2A3"). Proof. vmc. Qed.
Lemma T_sg4k_eq : ltac2:(tb__ "0|0|
S0S1S17S7SeS10SdS66A1S3dA2S9SeA1A3S89S40A1A2S87A3"). Proof. vmc. Qed.
Lemma T_sg4f_eq : contSG4 VN.P_fail = T_sg4f. Proof. vmc. Qed.
Lemma T_sg4g_eq : contSG4 VN.P_grown = T_sg4g. Proof. vmc. Qed.

Lemma E_f5o_eq : f5_site E_f5o0 = E_f5o. Proof. vmc. Qed.
Lemma E_f5f_eq : f5_site E_f5f0 = E_f5f. Proof. vmc. Qed.
Lemma R_f5o_eq : ltac2:(tb__ "0|1|
S0S6S8ScA1M0A1S11S46S42S4bA3S5G0S49A2A3"). Proof. vmc. Qed.
Lemma R_f5f_eq : ltac2:(tb__ "0|1|
S0S6S8ScA1M0A1S11S45S42S4aA3S5G0S48A2A3"). Proof. vmc. Qed.
Lemma T_f5o0_eq : ltac2:(tb__ "0|0|
S0S1S3eS42S46S4bS49S47A5S44A3"). Proof. vmc. Qed.
Lemma T_f5f0_eq : ltac2:(tb__ "0|0|
S0S1S3eS42S45S4aS48S47A5S43A3"). Proof. vmc. Qed.
Lemma T_f5o_eq : ltac2:(tb__ "0|0|
S0S1S65S18S12S44S4cS44A1A2A1PaaA2S4eA3"). Proof. vmc. Qed.
Lemma T_f5f_eq : ltac2:(tb__ "0|0|
S0S1S65S18S12S43S4cS43A1A2A1PaaA2S4dA3"). Proof. vmc. Qed.
Lemma C_rlo_eq : rel_state X_rlo = C_rlo. Proof. vmc. Qed.
Lemma C_rlf_eq : rel_state X_rlf = C_rlf. Proof. vmc. Qed.
End Lib_handle_f_eqs2.

