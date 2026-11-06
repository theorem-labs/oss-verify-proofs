(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require es.

(* [comment removed for export] *)
Module Lib_handle_f_eqs.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Init.Datatypes"; "Some"; "option"; "cons"; "list"; "nil"; "prod"; "pair"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "axform"; "AXMerge"; "AXSelect"; "AXSplit"; "AXRebase"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "SLit"; "sprop"; "sv"; "ss_objs"; "DUnknown"; "SPUle"; "SAlu"; "cell"; "mkObj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_defs.VN"; "Pre_vr"; "P_keep"; "P_fail"; "P_grown"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "T_afterA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s2"; "XkeepF"; "xf_backV"; "E_fv"; "E_mi"; "E_mm"; "R_fv"; "R_mi"; "R_mm"; "pDfv"; "s_fv"; "s_mi"; "s_mm"; "vr_need"; "E_dg"; "E_fv0"; "E_mc"; "XF1"; "XFV"; "pKfv"; "want_of"; "E_fv1"; "E_mc1"; "Pre_mc"; "R_dg"; "R_mcf"; "T_dg0"; "T_fvf0"; "T_fvg0"; "T_fvk0"; "T_mc0"; "T_mc1"; "T_mif0"; "T_mig0"; "T_mik0"; "T_mmf0"; "T_mmg0"; "T_mmk0"; "objs_fv0"; "s_dg"; "s_mcf"; "E_dg0"; "E_mc0"; "E_mi0"; "E_mm0"; "L_mc1"; "NFV"; "NMI"; "NMM"; "NSG"; "T_dg"; "T_fvf"; "T_fvg"; "T_fvk"; "T_mcq"; "T_mif"; "T_mig"; "T_mik"; "T_mmf"; "T_mmg"; "T_mmk"; "a0_mc"; "sel_mcf"; "sh_fv"; "xf_mcf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_defs"; "optAp"; "pA"; "xf_vr"; "pD2"; "pDco"; "X_body"; "reshapeA"; "E_co"; "R_co"; "pKco"; "s_co"; "C_pro0"; "E_ms"; "T_sm"; "T_sm1"; "X_pro"; "Xkeep"; "fv_d"; "mi_d"; "mm_d"; "sg_d"; "xf_back"; "E_ms1"; "E_sm0"; "O_Wf"; "Pre_ms"; "Pre_sm"; "R_ms"; "R_sm"; "T_cof0"; "T_cog0"; "T_cok0"; "T_ms0"; "mid_slot"; "objs_pro"; "objs_sm1"; "pK2"; "pQ"; "s_ms"; "s_sm"; "slot_obj"; "tr_d"; "C_pre"; "C_pro"; "E_co0"; "E_ms0"; "L_ms"; "L_sm"; "T_cof"; "T_cog"; "T_cok"; "X_hf0"; "co_need"; "fv_c"; "pT0"; "rp_d"; "sel_last"; "sg_c"; "sh_pro"; "ts_d"; "xf_ms"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.Lib_diag_append"; "Pre_da"; "P_da"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s4"; "contTR"; "E_trb"; "E_trg"; "R_trb"; "R_trg"; "s_trb"; "s_trg"; "E_tdg"; "R_tdg"; "T_tdg0"; "s_tdg"; "E_tdg0"; "E_trb0"; "E_trg0"; "T_tdg"; "T_trbf"; "T_trbg"; "T_trbk"; "T_trgf"; "T_trgg"; "T_trgk"; "XTR"; "pDtr"; "pKtr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_setX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s3"; "E_sg"; "R_sg"; "s_sg"; "XMM"; "pDmm"; "pKmm"; "T_sgf0"; "T_sgg0"; "T_sgk0"; "E_sg0"; "T_sgf"; "T_sgg"; "T_sgk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s1"; "T_pure"; "E_da"; "E_pc"; "E_pc1"; "sel_da"; "R_da"; "R_pc"; "T_da0"; "T_ms1"; "T_pc0"; "T_pc1"; "s_da"; "s_pc"; "E_da0"; "E_pc0"; "T_da"; "T_ms"; "T_pc"; "pc_need"; "sel_ms"; "sel_pc"; "xf_pc"; "xslot"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "T_afterA";
"@Stdlib.Lists.List"; "removelast"; "last"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s5"; "E_rp"; "E_ts"; "E_rp0"; "E_ts0"; "R_rp"; "R_ts"; "T_rpk"; "T_tsk"; "contRP"; "contTS"; "need_facts"; "s_rp"; "s_ts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_parse_corner2"; "Pre_pc"; "P_ret"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS"; "shadow_release_stateA"; "frame_open_stateA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs"; "hF"; "kb"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAS ResidualA AxArrA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ResidualA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxArrA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double Lib_parse_corner2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Asan_set_shadow_iface.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_parse_corner2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.Lib_diag_append OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Asan_set_shadow_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs Lib_handle_f_defs Lib_handle_f_s1 Lib_handle_f_s2 Lib_handle_f_s3 Lib_handle_f_s4 Lib_handle_f_s5 Lib_handle_f_s6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_s9 Lib_handle_f_s9b.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require es.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require en.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_handle_f_s7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_handle_f_s8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s9b OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.es.Lib_handle_f_s10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.en.Lib_handle_f_epi.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_tess_polygon_states Lib_handle_f_arith.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import MemoFast.
Import ListNotations.
Import ScanDoubleAddr VRAddr RA.ReallocAddr ParseCornerAddr DiagAppendAddr HFAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma R_sm_eq : ltac2:(tb__ "0|1|
S3S5S7S11A1M0A1S1fS79S7cS89A3S4G0S7eA2A3"). Proof. vmc. Qed.
Lemma T_sm_eq : ltac2:(tb__ "0|0|
S3S0Se0S7cS79S89S7eS91A5S6fA3"). Proof. vmc. Qed.
Lemma T_sm1_eq : ltac2:(tb__ "0|0|
S3S5S0A1SbS6fS6ScSeS9aS6fU3A2A1S8ScA1A3A2S4S0S70A2A3"). Proof. vmc. Qed.
Lemma objs_sm1_eq : ltac2:(tb__ "0|0|
S3S7S11A1Se1S11S15S1S70A1A1A2S85A3"). Proof. vmc. Qed.
Lemma C_pro0_eq : ltac2:(tb__ "0|0|
S3S0Sf4S70S85S95Pa0Z200A5S6dA3"). Proof. vmc. Qed.
Lemma C_pro_eq : ltac2:(tb__ "0|0|
S3S0SbaS6dS6S9S14S14A2SaS14S14Sf5S12Z0A1A4S2S6dA1A3A2S8dA3"). Proof. vmc. Qed.
Lemma sh_pro_eq : ltac2:(tb__ "0|0|
S3S11Se2S11S15S1S71A1A1S7aA3S9cA3"). Proof. vmc. Qed.
Lemma objs_pro_eq : ltac2:(tb__ "0|0|
S3S7S11A1Se1S11S15S1S71A1A1A2S84A3"). Proof. vmc. Qed.
Lemma C_pre_eq : ltac2:(tb__ "0|0|
S3S0Sf3S71S84Pa0S8S9S9fS9fA2A1A4S8cA3"). Proof. vmc. Qed.
Lemma E_co_eq : ltac2:(tb__ "0|0|
S3S0S61S96S87A1S62SbS8eS64U13Z2d0A2A2A1A2S69A3"). Proof. vmc. Qed.
Lemma R_co_eq : ltac2:(tb__ "0|1|
S3S5S7S11A1M0A1S1fS69S1bS6cA3S4G0S6aA2A3"). Proof. vmc. Qed.
Lemma T_cok0_eq : ltac2:(tb__ "0|0|
S3S0S20S1bS69S6cS6aS1cS72S66A1A6S81A3"). Proof. vmc. Qed.
Lemma T_cof0_eq : ltac2:(tb__ "0|0|
S3S0S20S1bS69S6cS6aS1dS72S66A1A6S7fA3"). Proof. vmc. Qed.
Lemma T_cog0_eq : ltac2:(tb__ "0|0|
S3S0S20S1bS69S6cS6aS1eS72S66A1A6S80A3"). Proof. vmc. Qed.
Lemma T_cok_eq : ltac2:(tb__ "0|0|
S3S5S0A1SbS81S77A2S4S0S94A2A3"). Proof. vmc. Qed.
Lemma T_cof_eq : ltac2:(tb__ "0|0|
S3S5S0A1SbS7fS77A2S4S0S92A2A3"). Proof. vmc. Qed.
Lemma T_cog_eq : ltac2:(tb__ "0|0|
S3S5S0A1SbS80S77A2S4S0S93A2A3"). Proof. vmc. Qed.
Lemma E_ms1_eq : ltac2:(tb__ "0|0|
S3S5S0A1SbS8fS9eA2S4S0S78A2A3"). Proof. vmc. Qed.
Lemma E_ms_eq : ltac2:(tb__ "0|0|
S3S0S68S78U21S8aS65S63A2A3S6eA3"). Proof. vmc. Qed.
Lemma R_ms_eq : ltac2:(tb__ "0|1|
S3S5S7S11A1M0A1S1fS6eS7bS88A3S4G0S7dA2A3"). Proof. vmc. Qed.
Lemma T_ms0_eq : ltac2:(tb__ "0|0|
S3S0Se0S7bS6eS88S7dS90A5S82A3"). Proof. vmc. Qed.

Lemma T_ms1_eq : ltac2:(tb__ "0|0|
S3S0S68S82U1S83S65S63S16A3A3Sd0A3"). Proof. vmc. Qed.
Lemma T_ms_eq : ltac2:(tb__ "0|1|
S3S5S0A1SbSd0S6ScSeSdbA1S6ScSdU20A1M0S6ScG0S8ScA1A3A3A3A2S4S0Sd8A2A3"). Proof. vmc. Qed.
Lemma E_pc1_eq : ltac2:(tb__ "0|0|
S3S5S0A1SbSd6SddA2S4S0ScbA2A3"). Proof. vmc. Qed.
Lemma E_pc_eq : ltac2:(tb__ "0|0|
S3S0S61SdaS98S87A2SbaS68ScbU22S8aS65S63A2A3S6S9S14S14A2SdeS65S63A2S2ScbA1A3A2A2ScaA3"). Proof. vmc. Qed.
Lemma R_pc_eq : ltac2:(tb__ "0|1|
S3S5S7S11A1M0A1S1fScaSf1Sd4A3S4G0SceA2A3"). Proof. vmc. Qed.
Lemma T_pc0_eq : ltac2:(tb__ "0|0|
S3S0Sc8Sf1ScaSd4SceSf2A5Sd1A3"). Proof. vmc. Qed.
Lemma T_pc1_eq : ltac2:(tb__ "0|0|
S3S0S68Sd1U2S83S65S63S16A3A3Sd2A3"). Proof. vmc. Qed.
Lemma T_pc_eq : ltac2:(tb__ "0|1|
S3S0SbaS62SbSd2S6ScSeSdcA1S6ScSdU0A1S6ScSdU20A1M0S6ScG0S8ScA1A3A3A3A3A2A1S67S65S86A2A2Sd9A3"). Proof. vmc. Qed.
Lemma E_da_eq : ltac2:(tb__ "0|0|
S3S5S0A1SbSd5S6ScSfU0S12N60A1A2S8ScA1A3A2S4S0Sc9A2A3"). Proof. vmc. Qed.
Lemma R_da_eq : ltac2:(tb__ "0|1|
S3S5S7S11A1M0A1S1fSc9Sa0Sd3A3S4G0ScdA2A3"). Proof. vmc. Qed.
Lemma T_da0_eq : ltac2:(tb__ "0|0|
S3S0Sc8Sa0Sc9Sd3ScdSa1A5ScfA3"). Proof. vmc. Qed.
Lemma T_da_eq : ltac2:(tb__ "0|0|
S3S0SbaS62SbScfS6ScSeSccA1S6ScSdU0A1S8ScA1A3A3A2A1S67S65S86A2A2Sd7A3"). Proof. vmc. Qed.

Lemma E_dg_eq : ltac2:(tb__ "0|0|
S3S5S0A1SbS49S6ScSfU0S12N60A1A2S8ScA1A3A2S4S0S2eA2A3"). Proof. vmc. Qed.
Lemma R_dg_eq : ltac2:(tb__ "0|1|
S3S5S7S11A1M0A1S1fS2eSa0S47A3S4G0S38A2A3"). Proof. vmc. Qed.
Lemma T_dg0_eq : ltac2:(tb__ "0|0|
S3S0Sc8Sa0S2eS47S38Sa1A5S3aA3"). Proof. vmc. Qed.
Lemma T_dg_eq : ltac2:(tb__ "0|0|
S3S0SbaS62SbS3aS6ScSeSccA1S6ScSdU0A1S8ScA1A3A3A2A1S67S66S6bA2A2S52A3"). Proof. vmc. Qed.
Lemma E_mi_eq : ltac2:(tb__ "0|0|
S62SbS4bS64UfZ1f0A2A2A1S0S3S0S61S2dZcS34R1A1S4fS63A1A3R1A2S24A3TE;"). Proof. vmc. Qed.
Lemma R_mi_eq : ltac2:(tb__ "0|1|
S3S5S7S11A1M0A1S1fS24S1bS2bA3S4G0S27A2A3"). Proof. vmc. Qed.
Lemma T_mik0_eq : ltac2:(tb__ "0|0|
S3S0S20S1bS24S2bS27S1cS21S74S67S66S6bA2A2A6S42A3"). Proof. vmc. Qed.
Lemma T_mif0_eq : ltac2:(tb__ "0|0|
S3S0S20S1bS24S2bS27S1dS21S74S67S66S6bA2A2A6S40A3"). Proof. vmc. Qed.
Lemma T_mig0_eq : ltac2:(tb__ "0|0|
S3S0S20S1bS24S2bS27S1eS21S74S67S66S6bA2A2A6S41A3"). Proof. vmc. Qed.
Lemma T_mik_eq : ltac2:(tb__ "0|0|
S3S5S0A1SbS42S22UeU1cZ1f0A3A2S4S0S59A2A3"). Proof. vmc. Qed.
Lemma T_mif_eq : ltac2:(tb__ "0|0|
S3S5S0A1SbS40S22UeU1cZ1f0A3A2S4S0S57A2A3"). Proof. vmc. Qed.
Lemma T_mig_eq : ltac2:(tb__ "0|0|
S3S5S0A1SbS41S22UeU1cZ1f0A3A2S4S0S58A2A3"). Proof. vmc. Qed.
Lemma sh_fv_eq : ltac2:(tb__ "0|0|
S3S11Se2S11S15S1S2fA1A1S7aA3S5fA3"). Proof. vmc. Qed.
Lemma objs_fv0_eq : ltac2:(tb__ "0|0|
S3S7S11A1Se1S11S15S1S2fA1A1A2S46A3"). Proof. vmc. Qed.
Lemma E_fv1_eq : ltac2:(tb__ "0|1|
S3S0Sf3S2fS46Pa0S6S9S9fS9fA2M0SaS9fS9fZ20Z4A4S8G0A1A3A4S35A3"). Proof. vmc. Qed.
Lemma E_fv_eq : ltac2:(tb__ "0|0|
S62SbS35S64U10Z210A2A2A1S0S3S0S61S2dZ4S34R1A1S4eS63A1A3R1A2S23A3TE;"). Proof. vmc. Qed.
Lemma R_fv_eq : ltac2:(tb__ "0|1|
S3S5S7S11A1M0A1S1fS23S1bS2aA3S4G0S26A2A3"). Proof. vmc. Qed.
Lemma T_fvk0_eq : ltac2:(tb__ "0|0|
S3S0S20S1bS23S2aS26S1cS21S73S31A2A6S3dA3"). Proof. vmc. Qed.
Lemma T_fvf0_eq : ltac2:(tb__ "0|0|
S3S0S20S1bS23S2aS26S1dS21S73S31A2A6S3bA3"). Proof. vmc. Qed.
Lemma T_fvg0_eq : ltac2:(tb__ "0|0|
S3S0S20S1bS23S2aS26S1eS21S73S31A2A6S3cA3"). Proof. vmc. Qed.
Lemma T_fvk_eq : ltac2:(tb__ "0|0|
S3S5S0A1SbS3dS22UfU1dZ210A3A2S4S0S55A2A3"). Proof. vmc. Qed.
Lemma T_fvf_eq : ltac2:(tb__ "0|0|
S3S5S0A1SbS3bS22UfU1dZ210A3A2S4S0S53A2A3"). Proof. vmc. Qed.
Lemma T_fvg_eq : ltac2:(tb__ "0|0|
S3S5S0A1SbS3cS22UfU1dZ210A3A2S4S0S54A2A3"). Proof. vmc. Qed.
Lemma E_mc1_eq : ltac2:(tb__ "0|0|
S3S5S0A1SbS4aS60A2S4S0S36A2A3"). Proof. vmc. Qed.
Lemma E_mc_eq : ltac2:(tb__ "0|0|
S3S0S68S36U20S1aS5dS12Z0A1S12Z4A1S8S19A1S16A5A3S30A3"). Proof. vmc. Qed.
Lemma R_mcf_eq : ltac2:(tb__ "0|1|
S3S5S7S11A1M0A1S1fS30S37S48A3S4G0S39A2A3"). Proof. vmc. Qed.
Lemma T_mc0_eq : ltac2:(tb__ "0|0|
S3S0Se0S37S30S48S39S4dA5S3eA3"). Proof. vmc. Qed.
Lemma T_mc1_eq : ltac2:(tb__ "0|2|
S3S0S68S3eU1S1aS29Sf6Z4M0S97A2M1S18Se3G1S12G0A1A3S8S19A1S16A5A3S3fA3"). Proof. vmc. Qed.
Lemma T_mcq_eq : ltac2:(tb__ "0|2|
S3S5S0A1SbS3fS6ScS10U2A1S6ScSeS5eA1S6ScSdU1A1M0S6ScG0S6ScSdU1dA1M1S6ScG1S8ScA1A3A3A3A3A3A3A2S4S0S56A2A3"). Proof. vmc. Qed.
Lemma E_mm_eq : ltac2:(tb__ "0|0|
S62SbS4cS64U11Z230A2A2A1S0S3S0S61S2dZ4S34R1A1S50S63A1A3R1A2S25A3TE;"). Proof. vmc. Qed.
Lemma R_mm_eq : ltac2:(tb__ "0|1|
S3S5S7S11A1M0A1S1fS25S1bS2cA3S4G0S28A2A3"). Proof. vmc. Qed.
Lemma T_mmk0_eq : ltac2:(tb__ "0|0|
S3S0S20S1bS25S2cS28S1cS21S75S32S29S33A2A2A6S45A3"). Proof. vmc. Qed.
Lemma T_mmf0_eq : ltac2:(tb__ "0|0|
S3S0S20S1bS25S2cS28S1dS21S75S32S29S33A2A2A6S43A3"). Proof. vmc. Qed.
Lemma T_mmg0_eq : ltac2:(tb__ "0|0|
S3S0S20S1bS25S2cS28S1eS21S75S32S29S33A2A2A6S44A3"). Proof. vmc. Qed.
Lemma T_mmk_eq : ltac2:(tb__ "0|0|
S3S5S0A1SbS45S22U10U1eZ230A3A2S4S0S5cA2A3"). Proof. vmc. Qed.
Lemma T_mmf_eq : ltac2:(tb__ "0|0|
S3S5S0A1SbS43S22U10U1eZ230A3A2S4S0S5aA2A3"). Proof. vmc. Qed.
Lemma T_mmg_eq : ltac2:(tb__ "0|0|
S3S5S0A1SbS44S22U10U1eZ230A3A2S4S0S5bA2A3"). Proof. vmc. Qed.

Lemma E_sg_eq : ltac2:(tb__ "0|0|
S3S0S61S2dZ4S18Se3S9bS12Z1A1A3S51S63A1A3S62SbSc4S64U12Z250A2A2A1A2SbbA3"). Proof. vmc. Qed.
Lemma R_sg_eq : ltac2:(tb__ "0|1|
S3S5S7S11A1M0A1S1fSbbS1bSbdA3S4G0SbcA2A3"). Proof. vmc. Qed.
Lemma T_sgk0_eq : ltac2:(tb__ "0|0|
S3S0S20S1bSbbSbdSbcS1cS21S76SbeSbfSc0A2A2A6Sc3A3"). Proof. vmc. Qed.
Lemma T_sgf0_eq : ltac2:(tb__ "0|0|
S3S0S20S1bSbbSbdSbcS1dS21S76SbeSbfSc0A2A2A6Sc1A3"). Proof. vmc. Qed.
Lemma T_sgg0_eq : ltac2:(tb__ "0|0|
S3S0S20S1bSbbSbdSbcS1eS21S76SbeSbfSc0A2A2A6Sc2A3"). Proof. vmc. Qed.
Lemma T_sgk_eq : ltac2:(tb__ "0|0|
S3S5S0A1SbSc3S22U11U1fZ250A3A2S4S0Sc7A2A3"). Proof. vmc. Qed.
Lemma T_sgf_eq : ltac2:(tb__ "0|0|
S3S5S0A1SbSc1S22U11U1fZ250A3A2S4S0Sc5A2A3"). Proof. vmc. Qed.
Lemma T_sgg_eq : ltac2:(tb__ "0|0|
S3S5S0A1SbSc2S22U11U1fZ250A3A2S4S0Sc6A2A3"). Proof. vmc. Qed.

Lemma E_trg_eq : ltac2:(tb__ "0|0|
S3S5S0A1SbSafS64U15Z310A2A2S4S0Sa4A2A3"). Proof. vmc. Qed.
Lemma E_trb_eq : ltac2:(tb__ "0|0|
S3S5S0A1SbSaeS64U15Z310A2A2S4S0Sa3A2A3"). Proof. vmc. Qed.
Lemma R_trg_eq : ltac2:(tb__ "0|1|
S3S5S7S11A1M0A1S1fSa4S1bSa8A3S4G0Sa6A2A3"). Proof. vmc. Qed.
Lemma R_trb_eq : ltac2:(tb__ "0|1|
S3S5S7S11A1M0A1S1fSa3S1bSa7A3S4G0Sa5A2A3"). Proof. vmc. Qed.
Lemma T_trgk_eq : ltac2:(tb__ "0|0|
S3S0S61S6S13S17S12SdfA1S8bA2S8S13A1A3Sa2Sa4Sa8Sa6S1cA4A2Sb6A3"). Proof. vmc. Qed.
Lemma T_trgf_eq : ltac2:(tb__ "0|0|
S3S0Sa2Sa4Sa8Sa6S1dA4Sb4A3"). Proof. vmc. Qed.
Lemma T_trgg_eq : ltac2:(tb__ "0|0|
S3S0Sa2Sa4Sa8Sa6S1eA4Sb5A3"). Proof. vmc. Qed.
Lemma T_trbk_eq : ltac2:(tb__ "0|0|
S3S0S61S6S13S17S12SdfA1S8bA2S8S13A1A3Sa2Sa3Sa7Sa5S1cA4A2Sb3A3"). Proof. vmc. Qed.
Lemma T_trbf_eq : ltac2:(tb__ "0|0|
S3S0Sa2Sa3Sa7Sa5S1dA4Sb1A3"). Proof. vmc. Qed.
Lemma T_trbg_eq : ltac2:(tb__ "0|0|
S3S0Sa2Sa3Sa7Sa5S1eA4Sb2A3"). Proof. vmc. Qed.
Lemma E_tdg_eq : ltac2:(tb__ "0|0|
S3S5S0A1SbSadS6ScSfU0S12N60A1A2S8ScA1A3A2S4S0Sa9A2A3"). Proof. vmc. Qed.
Lemma R_tdg_eq : ltac2:(tb__ "0|1|
S3S5S7S11A1M0A1S1fSa9Sa0SacA3S4G0SaaA2A3"). Proof. vmc. Qed.
Lemma T_tdg0_eq : ltac2:(tb__ "0|0|
S3S0Sc8Sa0Sa9SacSaaSa1A5SabA3"). Proof. vmc. Qed.
Lemma T_tdg_eq : ltac2:(tb__ "0|0|
S3S0SbaS62SbSabS6ScSeSccA1S6ScSdU0A1S8ScA1A3A3A2A1Sb7Sb8Sb9A2A2Sb0A3"). Proof. vmc. Qed.

Lemma E_rp_eq : ltac2:(tb__ "0|0|
S3S5S0A1SbSe6S64U14Z2f0A2A2S4S0Se4A2A3"). Proof. vmc. Qed.
Lemma R_rp_eq : ltac2:(tb__ "0|1|
S3S5S7S11A1M0A1S1fSe4S1bSefA3S4G0Se8A2A3"). Proof. vmc. Qed.
Lemma T_rpk_eq : ltac2:(tb__ "0|0|
S3S0S61S6S13S17S12SdfA1S99A2S8S13A1A3SecS1cA1A2SeaA3"). Proof. vmc. Qed.
Lemma T_rpf_eq : contRP VN.P_fail = T_rpf. Proof. vmc. Qed.
Lemma T_rpg_eq : contRP VN.P_grown = T_rpg. Proof. vmc. Qed.
Lemma E_ts_eq : ltac2:(tb__ "0|0|
S3S0S61SeeS62SbSe7S64U16Z330A2A2A1A2Se5A3"). Proof. vmc. Qed.
Lemma R_ts_eq : ltac2:(tb__ "0|1|
S3S5S7S11A1M0A1S1fSe5S1bSf0A3S4G0Se9A2A3"). Proof. vmc. Qed.
Lemma T_tsk_eq : ltac2:(tb__ "0|0|
S3S0S61S6S13S17S12SdfA1S9dA2S8S13A1A3SedS1cA1A2SebA3"). Proof. vmc. Qed.
Lemma T_tsf_eq : contTS VN.P_fail = T_tsf. Proof. vmc. Qed.
Lemma T_tsg_eq : contTS VN.P_grown = T_tsg. Proof. vmc. Qed.
End Lib_handle_f_eqs.

(* [comment removed for export] *)
Module Lib_handle_f_eqs2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_setS"; "@Corelib.Init.Datatypes"; "cons"; "nil"; "Some"; "option"; "list"; "prod"; "pair"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "apply_axforms"; "AXMerge"; "AXSelect"; "AXSplit"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "sobj"; "sprop"; "SAlu"; "mkObj"; "DUnknown"; "SPUle"; "cell"; "sv"; "DZero"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_defs"; "optAp"; "reshapeA"; "pA"; "xf_vr"; "Pre_ms"; "L_ms"; "sel_last"; "xfo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s2"; "Pre_mc"; "L_mc1"; "vr_need"; "NFV"; "NMI"; "NMM"; "NSG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "T_afterA"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_handle_f_s8"; "s_g"; "E_g1"; "E_g2"; "E_g3"; "pL"; "E_g1_1"; "E_g1_2"; "g_back"; "E_g1_0"; "E_g1_3"; "R_g1"; "R_g2"; "R_g3"; "E_g2_0"; "E_g3_0"; "T_g1"; "T_g2"; "T_g3"; "cFV"; "cMI"; "cMM"; "cSG"; "lDfv"; "lDmi"; "lDmm"; "lDsg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s6"; "objs_butlast"; "E_md"; "E_pg"; "R_pg"; "T_md1"; "s_pg"; "E_md0"; "E_md1"; "E_pg0"; "E_pg1"; "E_pg2"; "E_pg3"; "R_md"; "T_md0"; "T_md2"; "T_pgi0"; "Xk_pg"; "optS"; "s_md"; "E_pg4"; "O_nxt'"; "O_prv'"; "O_rfx'"; "T_md3"; "T_pgo0"; "sel_md"; "xf_md"; "xf_pg1"; "xf_pg2"; "zc_desc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS"; "shadow_release_stateA"; "flag_carve_stateA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_defs.VN"; "P_keep"; "Pre_vr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.en.Lib_handle_f_epi"; "Pre_f5"; "T_f5f0"; "T_f5o0"; "E_f5f"; "E_f5o"; "L_f5"; "R_f5f"; "R_f5o"; "s_f5f"; "s_f5o"; "xf_shback"; "T_f5f"; "T_f5o"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs"; "hF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_defs.PG"; "Pre_pg"; "P_inv"; "P_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_handle_f_s7"; "E_wdg"; "R_wdg"; "T_wdg0"; "s_wdg"; "E_wdg0"; "T_pgi1"; "T_wdg"; "XT"; "pg_back0"; "sel_wdg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.Lib_diag_append"; "Pre_da"; "P_da"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s9"; "E_c4"; "E_fv4"; "E_m4"; "E_mi4"; "E_mi4_0"; "E_mi4_1"; "R_c4"; "R_m4"; "offd_of"; "s_c4"; "s_m4"; "E_c4_0"; "E_fv4_0"; "E_m4_1"; "R_fv4"; "R_mi4"; "T_c4"; "T_fv4k"; "T_m4"; "T_mi4k"; "contFV4"; "contMI4"; "pDf4"; "pDm4"; "s_fv4"; "s_mi4"; "sel_c4"; "sel_m4"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s9b"; "E_mm4"; "E_sg4"; "E_mm4_0"; "E_sg4_0"; "R_mm4"; "R_sg4"; "T_mm4k"; "T_sg4k"; "contMM4"; "contSG4"; "s_mm4"; "s_sg4"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVAz"; "zcells_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "T_afterA3";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s1"; "T_pure"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s5"; "reopenX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s6.AR"; "ts_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_setX"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAS ResidualA AxArrA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ResidualA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxArrA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double Lib_parse_corner2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Asan_set_shadow_iface.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_parse_corner2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.Lib_diag_append OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Asan_set_shadow_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs Lib_handle_f_defs Lib_handle_f_s1 Lib_handle_f_s2 Lib_handle_f_s3 Lib_handle_f_s4 Lib_handle_f_s5 Lib_handle_f_s6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_s9 Lib_handle_f_s9b.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require es.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require en.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_handle_f_s7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_handle_f_s8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s9b OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.es.Lib_handle_f_s10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.en.Lib_handle_f_epi.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_tess_polygon_states Lib_handle_f_arith.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import MemoFast.
Import ListNotations.
Import ScanDoubleAddr VRAddr RA.ReallocAddr ParseCornerAddr DiagAppendAddr HFAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma E_md1_eq : ltac2:(tb__ "0|1|
S0S1S66S4eS48S4eA1Pa0S4S9S10S10A2M0SaS10S10Z30Z48A4S5G0A1A3A4S4fA3"). Proof. vmc. Qed.
Lemma E_md_eq : ltac2:(tb__ "0|0|
S0S1S1dS1cScS4fS62A2A1U2S15S23Z38A1S11Z0A1S11Z40A1S5S18A1S16A5A3S49A3"). Proof. vmc. Qed.
Lemma R_md_eq : ltac2:(tb__ "0|1|
S0S7S8S12A1M0A1S1bS49S20S5aA3S6G0S54A2A3"). Proof. vmc. Qed.
Lemma T_md0_eq : ltac2:(tb__ "0|0|
S0S1S2cS20S49S5aS54S21A5S55A3"). Proof. vmc. Qed.
Lemma T_md1_eq : ltac2:(tb__ "0|0|
S0S1S1dS55U1S15S78S11Z38A1S11Z78A1S5S18A1S1aA5A3S4cA3"). Proof. vmc. Qed.
Lemma T_md2_eq : ltac2:(tb__ "0|0|
S0S1S3S4cS59Sb0S2S4cA1U1S65A3A1A2S56A3"). Proof. vmc. Qed.
Lemma T_md3_eq : ltac2:(tb__ "0|1|
S0S7S1A1ScS56S4SbSeS61A1S4SbSdU1A1M0S4SbG0S5SbA1A3A3A3A2S6S1S5fA2A3"). Proof. vmc. Qed.
Lemma T_md_eq : reopenX 20 23 T_md3 = T_md. Proof. vmc. Qed.
Lemma E_pg1_eq : ltac2:(tb__ "0|1|
S0S1S2bSb4S66S50S48S50A1Pa0S4S9S10S10A2M0SaS10S10Za0Z18A4S5G0A1A3A4A2S51A3"). Proof. vmc. Qed.
Lemma E_pg2_eq : ltac2:(tb__ "0|0|
S0S7S1A1ScS51S63A2S6S1S52A2A3"). Proof. vmc. Qed.
Lemma E_pg3_eq : ltac2:(tb__ "0|0|
S0S7S1A1ScS52S64A2S6S1S53A2A3"). Proof. vmc. Qed.
Lemma E_pg4_eq : ltac2:(tb__ "0|0|
S0S1S1dS1dS1dS53U2bS5cA3U2dS5dA3U2fS5eA3S5bA3"). Proof. vmc. Qed.
Lemma R_pg_eq : ltac2:(tb__ "0|1|
S0S7S8S12A1M0A1S1bS4aS79S4dA3S6G0S4bA2A3"). Proof. vmc. Qed.
Lemma T_pgo0_eq : ltac2:(tb__ "0|0|
S0S1Sb1S79S4aS4dS4bS7bS58A6S60A3"). Proof. vmc. Qed.
Lemma T_pgi0_eq : ltac2:(tb__ "0|0|
S0S1Sb1S79S4aS4dS4bS7aS58A6S57A3"). Proof. vmc. Qed.

Lemma T_pgo1_eq : pg_back0 T_pgo0 = T_pgo1. Proof. vmc. Qed.
Lemma T_pgo_eq : pg_back T_pgo1 = T_pgo. Proof. vmc. Qed.
Lemma T_pgi1_eq : ltac2:(tb__ "0|2|
S0S1S3S84S57A1M0S59Sb0S2G0A1U3S4S9S10S10A2M1SaS10S10Z8Z4A4S5G1A1A3A3A1A2S81A3"). Proof. vmc. Qed.
Lemma T_pgi_eq : pg_back T_pgi1 = T_pgi. Proof. vmc. Qed.
Lemma T_pgoR_eq : reopen2 T_pgo = T_pgoR. Proof. vmc. Qed.
Lemma T_pgiR_eq : reopen2 T_pgi = T_pgiR. Proof. vmc. Qed.
Lemma E_wdg_eq : ltac2:(tb__ "0|0|
S0S7S1A1ScS80S4SbSfU0S11N60A1A2S5SbA1A3A2S6S1S7cA2A3"). Proof. vmc. Qed.
Lemma R_wdg_eq : ltac2:(tb__ "0|1|
S0S7S8S12A1M0A1S1bS7cS86S7fA3S6G0S7dA2A3"). Proof. vmc. Qed.
Lemma T_wdg0_eq : ltac2:(tb__ "0|0|
S0S1Sb2S86S7cS7fS7dS87A5S7eA3"). Proof. vmc. Qed.
Lemma T_wdg_eq : ltac2:(tb__ "0|0|
S0S1Sb5S1cScS7eS4SbSeS85A1S4SbSdU0A1S5SbA1A3A3A2A1S83A2S82A3"). Proof. vmc. Qed.

Lemma E_g1_1_eq : ltac2:(tb__ "0|0|
S0S7S1A1ScS36S4SbSeS22S36U24A2A1S5SbA1A3A2S6S1S33A2A3"). Proof. vmc. Qed.
Lemma E_g1_2_eq : ltac2:(tb__ "0|1|
S0S1S66S33S48S33A1Pa0S4S9S10S10A2M0SaS10S10Ze0Z24A4S5G0A1A3A4S34A3"). Proof. vmc. Qed.
Lemma E_g1_3_eq : ltac2:(tb__ "0|0|
S0S1S66S34S48S34A1Pa0S5S9S10S10A2A1A4S37A3"). Proof. vmc. Qed.
Lemma E_g1_eq : g_site E_g1_3 224 = E_g1. Proof. vmc. Qed.
Lemma R_g1_eq : ltac2:(tb__ "0|1|
S0S7S8S12A1M0A1S1bS2fS24S2eS2fA1A3S6G0S38A2A3"). Proof. vmc. Qed.
Lemma T_g1_eq : ltac2:(tb__ "0|0|
S0S1S35S2cS24S2fS2eS2fA1S38S25A5S37Ze0A3S3dA3"). Proof. vmc. Qed.
Lemma E_g2_eq : g_site E_g2_0 236 = E_g2. Proof. vmc. Qed.
Lemma R_g2_eq : ltac2:(tb__ "0|1|
S0S7S8S12A1M0A1S1bS30S24S2eS30A1A3S6G0S39A2A3"). Proof. vmc. Qed.
Lemma T_g2_eq : ltac2:(tb__ "0|0|
S0S1S35S2cS24S30S2eS30A1S39S25A5S3bZecA3S3eA3"). Proof. vmc. Qed.
Lemma E_g3_eq : g_site E_g3_0 248 = E_g3. Proof. vmc. Qed.
Lemma R_g3_eq : ltac2:(tb__ "0|1|
S0S7S8S12A1M0A1S1bS31S24S2eS31A1A3S6G0S3aA2A3"). Proof. vmc. Qed.
Lemma T_g3_eq : ltac2:(tb__ "0|0|
S0S1Sb3Z26Z27S35S2cS24S31S2eS31A1S3aS25A5S3cZf8A3A3S3fA3"). Proof. vmc. Qed.

Lemma E_mi4_1_eq : ltac2:(tb__ "0|1|
S0S1S66S8cS48S8cA1Pa0S4S9S10S10A2M0SaS10S10Z130Z4A4S5G0A1A3A4S8dA3"). Proof. vmc. Qed.
Lemma E_mi4_eq : ltac2:(tb__ "0|0|
S0S1S2bS26ZcS14S2dS41S32A1S11Z3A1A3S28S1eA1A3S1cScS8dS1fUfZ1f0A2A2A1A2S8bA3"). Proof. vmc. Qed.
Lemma R_mi4_eq : ltac2:(tb__ "0|1|
S0S7S8S12A1M0A1S1bS8bS69Sa1A3S6G0S97A2A3"). Proof. vmc. Qed.
Lemma T_mi4k_eq : ltac2:(tb__ "0|0|
S0S1S2bS4S13S17S11S77A1S45A2S5S13A1A3S9dS68A1A2S9bA3"). Proof. vmc. Qed.
Lemma T_mi4f_eq : contMI4 VN.P_fail = T_mi4f. Proof. vmc. Qed.
Lemma T_mi4g_eq : contMI4 VN.P_grown = T_mi4g. Proof. vmc. Qed.
Lemma E_c4_eq : c4_site E_c4_0 = E_c4. Proof. vmc. Qed.
Lemma R_c4_eq : ltac2:(tb__ "0|1|
S0S7S8S12A1M0A1S1bS88S24S91A3S6G0S8eA2A3"). Proof. vmc. Qed.
Lemma T_c4_eq : ltac2:(tb__ "0|4|
S0S1S90S93A1S19S2cS24S88S91S8eS25A5S1S1dS1dR1U1M0S15S9fR2S14S2dR2S11Z24A1A3S5S18A1M1S16A5A3U2S15S78S11Ze0A1S11Z104A1G1S16A5A3S1S1cScR1S4SbSeSa2A1S4SbSdG0A1M2S4SbG2S4SbSdU1cA1M3S4SbG3S5SbA1A3A3A3A3A3A2A1TT1;TT;Toff;S98A3"). Proof. vmc. Qed.
Lemma E_fv4_eq : ltac2:(tb__ "0|0|
S0S1S2bS26Z4S14S2dS40S32A1S11Z1A1A3S27S1eA1A3S1cScS94S1fU10Z210A2A2A1A2S89A3"). Proof. vmc. Qed.
Lemma R_fv4_eq : ltac2:(tb__ "0|1|
S0S7S8S12A1M0A1S1bS89S69Sa0A3S6G0S96A2A3"). Proof. vmc. Qed.
Lemma T_fv4k_eq : ltac2:(tb__ "0|0|
S0S1S2bS4S13S17S11S77A1S44A2S5S13A1A3S9cS68A1A2S99A3"). Proof. vmc. Qed.
Lemma T_fv4f_eq : contFV4 VN.P_fail = T_fv4f. Proof. vmc. Qed.
Lemma T_fv4g_eq : contFV4 VN.P_grown = T_fv4g. Proof. vmc. Qed.
Lemma E_m4_eq : m4_site E_m4_1 = E_m4. Proof. vmc. Qed.
Lemma R_m4_eq : ltac2:(tb__ "0|1|
S0S7S8S12A1M0A1S1bS8aS24S92A3S6G0S8fA2A3"). Proof. vmc. Qed.
Lemma T_m4_eq : ltac2:(tb__ "0|4|
S0S1S90S95A1S19S2cS24S8aS92S8fS25A5S1S1dS1dR1U1M0S15S9eR2S14S2dR2S11Z4A1A3S5S18A1M1S16A5A3U2S15S78S11Z130A1S11Z134A1G1S16A5A3S1S1cScR1S4SbSeSa3A1S4SbSdG0A1M2S4SbG2S4SbSdU1dA1M3S4SbG3S5SbA1A3A3A3A3A3A2A1TT1;TT;Toff;S9aA3"). Proof. vmc. Qed.

Lemma E_mm4_eq : ltac2:(tb__ "0|0|
S0S1S2bS26Z4S14S2dS42S32A1S11Z1A1A3S29S1eA1A3S1cScSa6S1fU11Z230A2A2A1A2Sa4A3"). Proof. vmc. Qed.
Lemma R_mm4_eq : ltac2:(tb__ "0|1|
S0S7S8S12A1M0A1S1bSa4S69SaeA3S6G0Sa8A2A3"). Proof. vmc. Qed.
Lemma T_mm4k_eq : ltac2:(tb__ "0|0|
S0S1S2bS4S13S17S11S77A1S46A2S5S13A1A3SacS68A1A2SaaA3"). Proof. vmc. Qed.
Lemma T_mm4f_eq : contMM4 VN.P_fail = T_mm4f. Proof. vmc. Qed.
Lemma T_mm4g_eq : contMM4 VN.P_grown = T_mm4g. Proof. vmc. Qed.
Lemma E_sg4_eq : ltac2:(tb__ "0|0|
S0S1S2bS26Z4S14S2dS43S32A1S11Z1A1A3S2aS1eA1A3S1cScSa7S1fU12Z250A2A2A1A2Sa5A3"). Proof. vmc. Qed.
Lemma R_sg4_eq : ltac2:(tb__ "0|1|
S0S7S8S12A1M0A1S1bSa5S69SafA3S6G0Sa9A2A3"). Proof. vmc. Qed.
Lemma T_sg4k_eq : ltac2:(tb__ "0|0|
S0S1S2bS4S13S17S11S77A1S47A2S5S13A1A3SadS68A1A2SabA3"). Proof. vmc. Qed.
Lemma T_sg4f_eq : contSG4 VN.P_fail = T_sg4f. Proof. vmc. Qed.
Lemma T_sg4g_eq : contSG4 VN.P_grown = T_sg4g. Proof. vmc. Qed.

Lemma E_f5o_eq : f5_site E_f5o0 = E_f5o. Proof. vmc. Qed.
Lemma E_f5f_eq : f5_site E_f5f0 = E_f5f. Proof. vmc. Qed.
Lemma R_f5o_eq : ltac2:(tb__ "0|1|
S0S7S8S12A1M0A1S1bS6eS6aS73A3S6G0S71A2A3"). Proof. vmc. Qed.
Lemma R_f5f_eq : ltac2:(tb__ "0|1|
S0S7S8S12A1M0A1S1bS6dS6aS72A3S6G0S70A2A3"). Proof. vmc. Qed.
Lemma T_f5o0_eq : ltac2:(tb__ "0|0|
S0S1S2cS6aS6eS73S71S6fA5S6cA3"). Proof. vmc. Qed.
Lemma T_f5f0_eq : ltac2:(tb__ "0|0|
S0S1S2cS6aS6dS72S70S6fA5S6bA3"). Proof. vmc. Qed.
Lemma T_f5o_eq : ltac2:(tb__ "0|0|
S0S1S67S1cScS6cS74S6cA1A2A1PaaA2S76A3"). Proof. vmc. Qed.
Lemma T_f5f_eq : ltac2:(tb__ "0|0|
S0S1S67S1cScS6bS74S6bA1A2A1PaaA2S75A3"). Proof. vmc. Qed.
Lemma C_rlo_eq : rel_state X_rlo = C_rlo. Proof. vmc. Qed.
Lemma C_rlf_eq : rel_state X_rlf = C_rlf. Proof. vmc. Qed.
End Lib_handle_f_eqs2.

(* [comment removed for export] *)
Module Lib_fuzz_one_chk.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "bool"; "true"; "nil"; "false"; "app"; "prod"; "cons"; "list"; "andb"; "fst"; "pair"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "sprop"; "SVar"; "sprop_eqb"; "SPUle"; "sobj"; "sv_eqb"; "ss_objs"; "valuation"; "DUnknown"; "SPAlign"; "SPBranch"; "SPEq"; "SPNot"; "cell"; "ob_base"; "ob_hi"; "ob_lo"; "ss_facts"; "ss_next"; "sv_below"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_fuzz_one"; "Fx"; "fr_fz"; "nx"; "s_lo"; "E_lo"; "pF"; "vF"; "E_sm0"; "T_sm1"; "gF"; "E_ms"; "Pre_ms"; "X_rel"; "pH"; "C_pro0"; "X_al"; "Xk_lo"; "C0"; "C_ms1"; "L_alF"; "L_ms"; "L_sm"; "Pre_sm"; "R_lo"; "R_ms"; "R_sm"; "objs_rel"; "objs_sm1"; "pAR"; "pFL"; "s_al"; "s_sm"; "vCFG"; "vFL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "nd_below"; "nd_am"; "nd_bd"; "nd_tv"; "am_subst"; "NDA"; "nd_fr"; "ndesc"; "AHeadN"; "ANone"; "am_eqb"; "amode"; "fr_sub_eqb"; "AHead"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bitem"; "bd_subst"; "KU"; "bd_below"; "BIc"; "bd_wpos"; "bud_le"; "bud_pay"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.es.Lib_fuzz_one_eqs"; "tvA"; "KU1"; "nd_e"; "nd_fa"; "gp"; "nd_CL"; "nd_p"; "nd_A2"; "nd_B2"; "ndT"; "nd_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ev.Lib_fuzz_one_chk"; "ent_chk"; "extraFZ"; "xextraFZ"; "isub_err"; "isub_ok"; "PDk_lo"; "ndA1p"; "@Stdlib.Lists.List"; "existsb"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_X"; "axst"; "ax_base"; "has_facts"; "entailsA"; "g8"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "add"; "ltb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ev.Lib_fuzz_one_chk.K2"; "xrs_chkC"; "robjs_chkC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub_id_below"; "sv_subst"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_fuzz_iface"; "bd_fz"; "nd_fz0"; "vDAT"; "vLEN"; "nd_fz1"; "fz_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_fuzz_one_ad"; "vG"; "X_A1"; "X_B"; "E_fa"; "E_fd"; "C_L"; "K_fa"; "L_L3"; "s_L3"; "vNx"; "L_L1"; "L_sxE"; "L_sxK"; "R_fa"; "R_fd"; "X_A"; "X_fa0"; "X_fa1"; "gA"; "nB"; "s_L1"; "s_fa0"; "s_fa1"; "vNd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ev.Lib_fuzz_one_chk.HK"; "robjs_chkR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ez.Lib_fuzz_one_epi"; "K_sx3"; "K_sx"; "K_sx2"; "X_fin"; "X_rl1"; "s_fin"; "s_sxE"; "s_sxK"; "@Stdlib.ZArith.BinInt.Z"; "sub"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_fuzz_one.LD"; "Pre_lo"; "NP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_fuzz_one.LI"; "nd_lo0"; "nd_lo_err"; "nd_lo_ok"; "P_err"; "P_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_subA"; "xs_framed"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "tv_sub_eqb"; "import_tv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF"; "xrs47_chk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "SHADOW_OFF"; "fs_frame_size"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "pdescA"; "pd_okA"; "xrs_inclb";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAD"; "two52"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR"; "e32"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_EQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eh.Lib_builder_pf"; "frameF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_fuzz_iface2"; "P_fz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eb.Lib_fuzz_one_glue"; "al_facts"; "vDN"; "vG10"; "vH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "new_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS"; "frame_open_stateA"; "shobj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "V_FLAG"; "V_RES"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAD.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAD.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_fuzz_iface2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_fuzz_one.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ez.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require es.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_fuzz_iface2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eb.Lib_fuzz_one_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_fuzz_one OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_fuzz_one_ad OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ez.Lib_fuzz_one_epi OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.es.Lib_fuzz_one_eqs.
Import ListNotations. Close Scope bv_scope. Open Scope Z_scope. Import FZAddr.
Module K2. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_armkit2. End K2. Module HK. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_hvkit. End HK.

Definition extraFZ (o : sobj) : bool := ltac2:(tb__ "0|1|
S2S2L_;M0S15S1eVo;A1S84A2G0S15S20Vo;A1SfZ0A1A2S15S1fVo;A1S85A2S5X2x2S5X2x2").
Definition xextraFZ (r : sv * sv) : bool := ltac2:(tb__ "0|0|
S2S2L_;S15SbSeSeVr;A3S84A2S15SdSeSeVr;A3S85A2S5X2x2").

Definition ent_chk (L T : axst) (s : wsub) (ndi ndj : ndesc) : bool := ltac2:(tb__ "0|2|
S2S2L_;M0S76VL;VT;Vs;A3G0S7fVs;S78A2G0S79S78S27VL;A1M1A2G0S47G1Vndi;A2G0Sb4Vs;S4aVndi;A1S4aVndj;A1A3G0S53Vs;S4dVndi;A1S4dVndj;A1A3G0S5bS25VL;A1S56Vs;S49Vndj;A1A2S49Vndi;A1A3S51S4bVs;S48Vndj;A1A2S48Vndi;A1A2S5X2x2S5X2x2S5X2x2S5X2x2S5X2x2S5X2x2S5X2x2").
Lemma ent_chk_unf : ltac2:(tb__ "0|2|
S73S73S81S4eS4eS0S2S68R5R4R3R2R1A5S3A3S1S0S2S76R6R5R4A3S3A3S1S0S2S7fR4S78A2S3A3S1S0S2S79S78S22S71R6A1M0A1M1A2S3A3S1S0S2S47G1R3A2S3A3S1S0S2Sb4R4S4aR3A1S4aR2A1A3S3A3S1S0S2S53R4S4dR3A1S4dR2A1A3S3A3S1S0S2S5bS21G0A1S56R4S49R2A1A2S49R3A1A3S3A3S0S2S51S4bR4S48R2A1A2S48R3A1A2S3A3A2A2A2A2A2A2A2F_;Fndj;Fndi;Fs;FT;FL;").
Proof.
  intros L T s ndi ndj H. unfold ent_chk in H.
  apply lazy_andb_prop in H as [H1 H]. apply lazy_andb_prop in H as [H2 H]. apply lazy_andb_prop in H as [H3 H]. apply lazy_andb_prop in H as [H4 H].
  apply lazy_andb_prop in H as [H5 H]. apply lazy_andb_prop in H as [H6 H]. apply lazy_andb_prop in H as [H7 H8]. repeat split; assumption.
Qed.

Lemma fz_chk_al : ltac2:(tb__ "0|0|
S0S2S68S38S36S43S83S83A5S3A3").
Proof. vmc1. Qed.

Lemma fz_chk_sm : ltac2:(tb__ "0|7|
S1S0S2S7dS25S2cA1M0S4S7SeSeA2M1A1M2S4S7S7SeSbeA2SeA2A1M3S69S3eA5S3A3S1S0S2S7cG0G2G3S6aS72S2cA1A5S3A3S1S0S2S47S27S2cA1M4S83A2S3A3S1S0S2S5aS82A1S3A3S1S0SeS7eSb2S44S3bS3aS2cA4M5ScbA2S2bA3S1S0S2S79G4S2aA2S3A3S1S0SeS7eG5ScaA2S46A3S1S0S2S79G4S42A2S3A3S1S0SeS74S2dA1SfSb7A1A3S1S0S2S24S71Sc8S2dS40S6G1S34G2A3S2aSb8Z2A1A5A1A1S3A3S1S0S2S79S78S27S2dA1M6A2S3A3S1S0S2S47G6S63A2S3A3S1S0S2S7cS25S2dA1G2G3S6aS34A5S3A3S1S0S2S6fS10S12S19S2aZ5A2A1S25S33A1A3S3A3S0S2S7bS2aS27S33A1A2S3A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Lemma fz_chk_rel : ltac2:(tb__ "0|5|
S1S0SeS74S31A1SfSb7A1A3S1S0S2S75S8S10S1bS77S2eA1S2bA2S8S10S13S11S2eA1SfSa9SaaZ2Z3dA2Z1A2A1A2S4S10A1A3A3S25S31A1M0A2S3A3S1S0S2S47S27S31A1S63A2S3A3S1S0S2Sa0G0S4S7SeSeA2A1M1S26S69S3fA5S3A3S1S0S2S6fS10S12S13S2bSfSa9Z7fffff800000Z100A2A1A2A1S25S37A1A3S3A3S1S0S2S47S27S2fA1M2S63A2S3A3S1S0S2S58G2S82A2S3A3S1S0S2S70S73S73SaSaS9S14A1M3S2Lx;Sc7S71S30A1S71R1A1A2S3S14G3S5Ll;Ls;X9x2Sb3S30R1A2A2S15S74R1A1S74S30A1A2A2LL;S8S73S39S4S73A1A3A3S3A3S1S0S2S7dS25S2fA1M4G1S26S69S3dA5S3A3S0S2S7cG4G1S26S6aS72S2fA1A5S3A3A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Definition PDk_lo : list pdescK := liftPD LI.PD_lo.
Definition isub_err : wsub := ltac2:(tb__ "0|0|
Sb2S28SabSb0S29A4").
Definition isub_ok : wsub := ltac2:(tb__ "0|0|
Sb2S28SabSb1S29A4").
Lemma fz_chk_lo : ltac2:(tb__ "0|9|
S1S0S2S7dS25S29A1M0S4S7SeSeA2M1A1M2S26S69S3cA5S3A3S1S0S2S7cG0G2S26S6aS35A5S3A3S1S0S2SbbS35S72S29A1A2S3A3S1S0S2S47S27S29A1M3S4cS6G1G2G2A3S26S82S50A4A2S3A3S1S0S2S58G3S4S55A1M4A2S3A3S1S0S2Sb4S28G2S4aSadA1A3S3A3S1S0S2S51S4bS28S48SadA1A2S50A2S3A3S1S0S9S55A1M5S6S55S56S28S49SadA1A2G4A3S82A3S1S0S2S5aS82A1S3A3S1S0S2S70S7Sb9S17S17OF_;F_;M6A2M7G7SbaSabSacS28G3SbSb9G6R1A3A5Ld;S6dA3S3A3S1S0SeS7eS28PdA2S84A3S1S0SeS7eS28PeA2S85A3S1S0SeS7eS28PfA2S45A3S1S0SeS7eS28P1cA2S11PaA1A3S1S0S2S6fS10S12S13S2bSfSa9Z7fffff800000Z100A2A1A2A1G0A3S3A3S1S0S2S75S87G0A2S3A3S1S0S2S75Sc3Sc6Sc4Sc5A3G0A2S3A3S1S0S9G1A1M8S6G1G2Sb5S6bS4aSaeA1A2A3G2A3S1S0G5S6S55S56S6bS49SaeA1A2G4A3G4A3S1S0S52S4bS6bS48SaeA1A2S50A3S1S0G8S6G1G2Sb5S6cS4aSafA1A2A3S5dA3S1S0G5S6S55S56S6cS49SafA1A2G4A3S5eA3S0S52S4bS6cS48SafA1A2S54S32S5A2A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Definition ndA1p : ndesc := ltac2:(tb__ "0|0|
S4cS5dS26S5eS4fS32S9aA2A4").
Lemma fz_chk_loop : ltac2:(tb__ "0|e|
S1S0S2S68S98S8eS9dS60S60A5S3A3S1S0S2S68S99S8eS9eS60S60A5S3A3S1S0S2S68S92S8dS9cS64S62A5S3A3S1S0S2S68S8fS8dS90S65S62A5S3A3S1S0S2S79S78S27S97A1M0A2S3A3S1S0S2S47G0S67A2S3A3S1S0S2S79S78S27S89A1M1A2S3A3S1S0S2S47G1S6eA2S3A3S1S0S2Sa0S25S89A1M2S5dS26S69S16S71S89A1A1A5S3A3S1S0S2Sb6G2S5dS72S89A1A3S3A3S1S0S4eS4cS8S7SeSeA2M3ScSeSeS32SbdS11S7aG1P1M4A2A1A1A4S5dA3S26S6S55S5eS8S55S59Z0Z1S57A3S4S55A1A3A3M5S4fS11G1A1S11S7aG1P3M6A2A1A2A4S64A3S1S0S2S79S78S27S8aA1M7A2S3A3S1S0S2S47G7S66S91S88A2A2S3A3S1S0S2Sa0S25S8aA1M8S5dS26S69S16S71S8aA1A1A5S3A3S1S0S2Sb6G8S5dS72S8aA1A3S3A3S1S0S4eS4cS8G3ScSeSeS91SbdS11S7aG7G4A2A1A1A4S5dA3S26G5S4fS11G7A1S11S7aG7G6A2M9A1A2A4S65A3S1S0SbfG9S7aS9bG6A2MaA3S1S0S2S6fS10S12S13S88SfSbcA1MbA2A1G8A3S3A3S1S0S2S6fS10S12S13S11GaA1McGbA2A1S25S8fA1A3S3A3S0SeS80S90S61S88Z8MdA2A2S61GcGdA2A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Lemma fz_chk_fd : ltac2:(tb__ "0|4|
S1S0S2S7dS25S8cA1M0S5dS26S69S96A5S3A3S1S0S2S7cG0S5dS26S6aS72S8cA1A5S3A3S1S0S2S6fS10S12S1cS1aSc0S9fSfZ0M1A1M2A3A1A1G0A3S3A3S1S0S2S5cG0G2S57S6S55S5eS8S55S59G1Z1S57A3S4S55A1A3A3S5eA5S3A3S1S0S2S58S27S8cA1M3S5eA2S3A3S1S0S2S47G3S62A2S3A3S1S0S2S6fS10S12S13S88SfSbcA1A2A1G0A3S3A3S0S2S23G3S61S88Z6A2A2S3A3A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Lemma fz_chk_fa : ltac2:(tb__ "0|2|
S1S0S2S7dS25S8bA1M0S4S7SeSeA2A1M1S26S69S95A5S3A3S1S0S2S7cG0G1S26S6aS72S8bA1A5S3A3S1S0S2S6fS10S12S13SfZ1000A1S41A2A1G0A3S3A3S1S0S2S5cG0SfZ0A1S57S5eS4S55A1A5S3A3S0S2S47S27S8bA1S60A2S3A3A2A2A2A2").
Proof. conj_vmc. Qed.

Lemma fz_chk_sx : ltac2:(tb__ "0|5|
S1S0S2S68S93Sa2Sa7S5fS5fA5S3A3S1S0S2S68S94Sa2Sa8S5fS5fA5S3A3S1S0S2S6fS10S12S13S2bSfSa9Z7fffff800000Z100M0A2A1A2A1S25Sa2A1A3S3A3S1S0S2Sa0S25Sa3A1M1S4S7SeSeA2A1M2S26S69S16S71Sa3A1A1M3A5S3A3S1S0S2Sc1S2eS2aG0G1A4S3A3S1S0S2Sb6S25Sa1A1M4G2S72Sa1A1A3S3A3S1S0SeS74Sa1A1SfSb7A1A3S1S0S9S14A1S16S71Sa1A1A1S6S14G3S8S14Sc9S2eZ0Z20S4S1dA1S18A5S4S14A1A3A3A3S0S9S10A1G4G1A3A2A2A2A2A2A2A2A2").
Proof. conj_vmc. Qed.

Lemma fz_chk_rl : ltac2:(tb__ "0|0|
S1S0S2S47S27Sa5A1S5fA2S3A3S0S2S68Sa4Sc2Sa6S86S86A5S3A3A2").
Proof. conj_vmc. Qed.
End Lib_fuzz_one_chk.

