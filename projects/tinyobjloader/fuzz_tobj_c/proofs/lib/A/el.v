(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ek Lib_finalize_shape em.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require HideA.

(* [comment removed for export] *)
Module Lib_handle_l_chk2.

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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs Lib_handle_l Lib_handle_l_s2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ek.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_l OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_l_s2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ek.Lib_handle_l_chk0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import HLAddr.
Lemma cc_6 : CC 6 K = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_7 : CC 7 C_unp = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_8 : CC 8 T_pc = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_9 : CC 9 T_da = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_10 : CC 10 J = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_11 : CC 11 T_keep = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_12 : CC 12 T_grown = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End Lib_handle_l_chk2.

(* [comment removed for export] *)
Module Lib_handle_l_chk1.

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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs Lib_handle_l Lib_handle_l_s2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ek.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_l OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_l_s2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ek.Lib_handle_l_chk0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import HLAddr.
Lemma cc_0 : CC 0 Pre_hl = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_1 : CC 1 C_pro = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_2 : CC 2 C_pre = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_3 : CC 3 H = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_4 : CC 4 L1 = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_5 : CC 5 L2 = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End Lib_handle_l_chk1.

(* [comment removed for export] *)
Module Lib_finalize_shape_eqs.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_setS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "SLit"; "sprop"; "ss_objs"; "SVar"; "ss_facts"; "DZero"; "SAlu"; "cell"; "mkObj"; "@Corelib.Init.Datatypes"; "cons"; "Some"; "nil"; "option"; "list"; "prod"; "pair"; "true"; "app"; "false"; "length"; "nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "axform"; "AXSelect"; "AXSplit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "AHead"; "am_subst"; "amode"; "nd_bd"; "nd_tv"; "tv_factsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "import_tv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "T_afterA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_finalize_shape"; "vAR"; "vHq"; "Pre_vf"; "Pre_ad"; "Xk_vf"; "Xk_fin"; "xf_back_fin"; "E_vf5"; "E_vf6"; "E_vf7"; "E_vp"; "s_vf5"; "s_vf6"; "s_vf7"; "xf_back_vfk"; "E_ad1"; "E_ad2"; "E_ad3"; "E_ad4"; "Pre_vp"; "vDg"; "E_mg1"; "E_mk1"; "R_vp"; "go_facts"; "s_ad1"; "s_ad2"; "s_ad3"; "s_ad4"; "sh_d"; "vHa"; "vLC"; "vLI"; "vPI"; "xf_call"; "CHf"; "E_mg"; "E_mk"; "R_vf5"; "R_vf6"; "R_vf7"; "X_fit"; "X_nofit"; "X_nofit1"; "X_nzret2"; "X_sret1"; "X_sret2"; "Xk_vp"; "ghZ"; "vFV"; "vHv"; "vKg"; "vMI"; "vMM"; "vSG"; "xf_back_vf"; "xf_back_vp"; "xf_vfcall"; "E_m"; "L_ms"; "NP"; "Pre_m"; "Pre_ms"; "R_ad1"; "R_ad2"; "R_ad3"; "R_ad4"; "R_m"; "T1_fail0"; "T1_ok0"; "T2_fail0"; "T2_ok0"; "T3_fail0"; "T3_ok0"; "T4_fail0"; "T4_ok0"; "T5_z"; "T6_z"; "T7_z"; "T_mg0"; "T_mk0"; "T_mok0"; "T_pf0"; "T_pg"; "T_pg0"; "T_pk"; "T_pk0"; "X_nzret"; "Xof"; "bd_push"; "hole_obj"; "mid_obj"; "s_m"; "s_ma"; "sh_c"; "sh_k"; "vSH"; "xf_mback"; "xf_mcall"; "C_1"; "C_open"; "E_ad1_0"; "E_ad2_0"; "E_ad3_0"; "E_ad4_0"; "E_mg0"; "E_mk0"; "E_vf5_0"; "E_vf6_0"; "E_vf7_0"; "E_vp0"; "R_mg"; "R_mk"; "T1_fail"; "T1_ok"; "T2_fail"; "T2_ok"; "T3_fail"; "T3_ok"; "T4_fail"; "T4_ok"; "T5_f"; "T5_ok"; "T5_zG"; "T6_f"; "T6_ok"; "T6_zG"; "T7_f"; "T7_ok"; "T7_zG"; "T_mg"; "T_mg1"; "T_mk"; "T_mk1"; "T_mnull"; "T_mok"; "T_pf"; "T_pgF"; "T_pkF"; "X_fit3"; "X_nofit2"; "X_nzret3"; "X_open0"; "X_sret"; "blkN"; "fit_facts"; "hse_fact"; "kb"; "lc_c"; "li_c"; "nofit_fact"; "pfit0"; "pi_c"; "s_vp"; "slotx"; "top_factG"; "top_factK"; "vHD"; "xf_vpcall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_finalize_shape.VF"; "tv_vf"; "P_fail"; "P_ok"; "P_zero"; "am_vf"; "vHDn"; "vHDv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.el.Lib_finalize_shape_eqs"; "isub_vf"; "isub_ad"; "objsNs"; "s_vpH"; "hVP"; "objsZ"; "ohNs"; "X_sret2x"; "isub_vp"; "ohZ"; "X_sret3x"; "holeZ"; "sel_s"; "ohF"; "ohNF"; "osZ"; "otNs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_finalize_shape.AD"; "P_fail"; "P_ok"; "tv0"; "am_np"; "am_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bd_subst"; "bitem"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR"; "drop_lastA"; "carve_stateA"; "open_stateA";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "T_afterA"; "@Stdlib.Lists.List"; "nth_error"; "removelast"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.el.Lib_finalize_shape_eqs.VFZ"; "CHz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_subA"; "entails_frA"; "@Corelib.Numbers.BinNums"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_finalize_shape.VP"; "P_push_fail"; "P_push_grown"; "P_push_keep"; "ndp0"; "ndpG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve"; "vDn"; "vKn"; "kbytes"; "tv0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase"; "reshape_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "AE_A"; "UStopLe"; "ulink"; "L_malloc_null"; "L_malloc_ok"; "@Corelib.Init.Nat"; "sub"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ed.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_vec_reserve Lib_vec_push Lib_vec_finalize.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ei.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Lib_finalize_shape.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Module VFZ. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ei.Lib_vec_finalizeZ. End VFZ.
Import RA.ReallocAddr AA.AAAddr AD.ADAddr VP.VPAddr VF.VFAddr FSAddr.

Lemma E_ad1_eq : ltac2:(tb__ "0|0|
S0S13S2A1S1cSc7S40S5cA1S8dA2S4aZ40A1A2S11S2S37A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_ad2_eq : ltac2:(tb__ "0|0|
S0S13S2A1S1cSc7S40S59A1S8eA2S4aZ40A1A2S11S2S38A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_ad3_eq : ltac2:(tb__ "0|0|
S0S13S2A1S1cSc7S40S5dA1S8fA2S4aZ40A1A2S11S2S39A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_ad4_eq : ltac2:(tb__ "0|0|
S0S13S2A1S1cSc7S40S5eA1S90A2S4aZ40A1A2S11S2S3aA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T1_ok0_eq : ltac2:(tb__ "0|0|
S0S2S27S2bS37S41S67Se1S2dS5cA1A6S6dA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T2_ok0_eq : ltac2:(tb__ "0|0|
S0S2S27S2bS38S42S68Se1S2dS59A1A6S6fA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T3_ok0_eq : ltac2:(tb__ "0|0|
S0S2S27S2bS39S43S69Se1S2dS5dA1A6S71A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T4_ok0_eq : ltac2:(tb__ "0|0|
S0S2S27S2bS3aS44S6aSe1S2dS5eA1A6S73A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T1_fail0_eq : ltac2:(tb__ "0|0|
S0S2S27S2bS37S41S67Se0S2dS5cA1A6S6cA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T2_fail0_eq : ltac2:(tb__ "0|0|
S0S2S27S2bS38S42S68Se0S2dS59A1A6S6eA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T3_fail0_eq : ltac2:(tb__ "0|0|
S0S2S27S2bS39S43S69Se0S2dS5dA1A6S70A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T4_fail0_eq : ltac2:(tb__ "0|0|
S0S2S27S2bS3aS44S6aSe0S2dS5eA1A6S72A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T1_ok_eq : ltac2:(tb__ "0|0|
S0S13S2A1S1cS6dS2eU1A1A2S11S2S9aA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T2_ok_eq : ltac2:(tb__ "0|0|
S0S13S2A1S1cS6fS2eU2A1A2S11S2S9cA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T3_ok_eq : ltac2:(tb__ "0|0|
S0S13S2A1S1cS71S2eU3A1A2S11S2S9eA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T4_ok_eq : ltac2:(tb__ "0|0|
S0S13S2A1S1cS73S2eU4A1A2S11S2Sa0A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T1_fail_eq : ltac2:(tb__ "0|0|
S0S13S2A1S1cS6cS2eU1A1A2S11S2S99A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T2_fail_eq : ltac2:(tb__ "0|0|
S0S13S2A1S1cS6eS2eU2A1A2S11S2S9bA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T3_fail_eq : ltac2:(tb__ "0|0|
S0S13S2A1S1cS70S2eU3A1A2S11S2S9dA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T4_fail_eq : ltac2:(tb__ "0|0|
S0S13S2A1S1cS72S2eU4A1A2S11S2S9fA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition isub_ad (E : axst) (s : wsub) (L : axst) : wsub := ltac2:(tb__ "0|0|
SeeVs;S2bVL;VE;A4").
Lemma imp_ad1_ok : ltac2:(tb__ "0|2|
S1S0S14S15S5S5A2M0A1S26Sd0S37S41Se1A3M1Se2A2S10G0S16S5S5S28S7Z40A1A4S12G0A1A3A3S0S22S21G1Se4A2S20S46S17A2A3A2").
Proof. split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_ad2_ok : ltac2:(tb__ "0|2|
S1S0S14S15S5S5A2M0A1S26Sd0S38S42Se1A3M1Se2A2S10G0S16S5S5S28S7Z40A1A4S12G0A1A3A3S0S22S21G1Se4A2S20S46S17A2A3A2").
Proof. split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_ad3_ok : ltac2:(tb__ "0|2|
S1S0S14S15S5S5A2M0A1S26Sd0S39S43Se1A3M1Se2A2S10G0S16S5S5S28S7Z40A1A4S12G0A1A3A3S0S22S21G1Se4A2S20S46S17A2A3A2").
Proof. split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_ad4_ok : ltac2:(tb__ "0|2|
S1S0S14S15S5S5A2M0A1S26Sd0S3aS44Se1A3M1Se2A2S10G0S16S5S5S28S7Z40A1A4S12G0A1A3A3S0S22S21G1Se4A2S20S46S17A2A3A2").
Proof. split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_ad1_fail : ltac2:(tb__ "0|2|
S1S0S14S15S5S5A2M0A1S26Sd0S37S41Se0A3M1Se2A2S10G0S16S5S5S28S7Z40A1A4S12G0A1A3A3S0S22S21G1Se3A2S20S29S19A2A3A2").
Proof. split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_ad2_fail : ltac2:(tb__ "0|2|
S1S0S14S15S5S5A2M0A1S26Sd0S38S42Se0A3M1Se2A2S10G0S16S5S5S28S7Z40A1A4S12G0A1A3A3S0S22S21G1Se3A2S20S29S19A2A3A2").
Proof. split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_ad3_fail : ltac2:(tb__ "0|2|
S1S0S14S15S5S5A2M0A1S26Sd0S39S43Se0A3M1Se2A2S10G0S16S5S5S28S7Z40A1A4S12G0A1A3A3S0S22S21G1Se3A2S20S29S19A2A3A2").
Proof. split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_ad4_fail : ltac2:(tb__ "0|2|
S1S0S14S15S5S5A2M0A1S26Sd0S3aS44Se0A3M1Se2A2S10G0S16S5S5S28S7Z40A1A4S12G0A1A3A3S0S22S21G1Se3A2S20S29S19A2A3A2").
Proof. split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma E_vf5_eq : ltac2:(tb__ "0|0|
S0S13S2A1S1cS93S61UcZ270A2A2S11S2S2fA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_vf6_eq : ltac2:(tb__ "0|0|
S0S13S2A1S1cS94S61UdZ290A2A2S11S2S30A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_vf7_eq : ltac2:(tb__ "0|0|
S0S13S2A1S1cS95S61UeZ2b0A2A2S11S2S31A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T5_z_eq : ltac2:(tb__ "0|0|
S0S13S2A1S1cS27S2aS2fS33S4eScbS2cS48A1A6S5fUcU5A2A2S11S2S74A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T6_z_eq : ltac2:(tb__ "0|0|
S0S13S2A1S1cS27S2aS30S34S4fScbS2cS47A1A6S5fUdU6A2A2S11S2S75A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T7_z_eq : ltac2:(tb__ "0|0|
S0S13S2A1S1cS27S2aS31S35S50ScbS2cS49A1A6S5fUeU7A2A2S11S2S76A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T5_f_eq : ltac2:(tb__ "0|0|
S0S13S2A1S1cS27S2aS2fS33S4eSc9S2cS48A1A6S36UcU5A2A2S11S2Sa1A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T6_f_eq : ltac2:(tb__ "0|0|
S0S13S2A1S1cS27S2aS30S34S4fSc9S2cS47A1A6S36UdU6A2A2S11S2Sa4A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T7_f_eq : ltac2:(tb__ "0|0|
S0S13S2A1S1cS27S2aS31S35S50Sc9S2cS49A1A6S36UeU7A2A2S11S2Sa7A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T5_ok_eq : ltac2:(tb__ "0|0|
S0S13S2A1S1cS27S2aS2fS33S4eScaS2cS48A1A6S36UcU5A2A2S11S2Sa2A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T6_ok_eq : ltac2:(tb__ "0|0|
S0S13S2A1S1cS27S2aS30S34S4fScaS2cS47A1A6S36UdU6A2A2S11S2Sa5A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T7_ok_eq : ltac2:(tb__ "0|0|
S0S13S2A1S1cS27S2aS31S35S50ScaS2cS49A1A6S36UeU7A2A2S11S2Sa8A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition isub_vf (E : axst) (s : wsub) (L : axst) : wsub := ltac2:(tb__ "0|0|
SeeVs;S2aVL;VE;A4").
Lemma imp_vf5_z : ltac2:(tb__ "0|2|
S1S0S14S15S5S5A2M0A1S26ScfS2fS33ScbA3M1Sc8A2S10G0S16S5S5S28S7Z40A1A4S12G0A1A3A3S1S0S22S21G1SccA2S20S29S17A2A3S0S14Se6A1Se5G1SedA2S4bS48SbdA2A3A2A2").
Proof. repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_vf6_z : ltac2:(tb__ "0|2|
S1S0S14S15S5S5A2M0A1S26ScfS30S34ScbA3M1Sc8A2S10G0S16S5S5S28S7Z40A1A4S12G0A1A3A3S1S0S22S21G1SccA2S20S29S17A2A3S0S14Se6A1Se5G1SedA2S4bS47SbcA2A3A2A2").
Proof. repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_vf7_z : ltac2:(tb__ "0|2|
S1S0S14S15S5S5A2M0A1S26ScfS31S35ScbA3M1Sc8A2S10G0S16S5S5S28S7Z40A1A4S12G0A1A3A3S1S0S22S21G1SccA2S20S29S17A2A3S0S14Se6A1Se5G1SedA2S4bS49Sc0A2A3A2A2").
Proof. repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_vf5_f : ltac2:(tb__ "0|2|
S1S0S14S15S5S5A2M0A1S26ScfS2fS33Sc9A3M1Sc8A2S10G0S16S5S5S28S7Z40A1A4S12G0A1A3A3S0S22S21G1S20SceS19A2A2S20S29S19A2A3A2").
Proof. split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_vf6_f : ltac2:(tb__ "0|2|
S1S0S14S15S5S5A2M0A1S26ScfS30S34Sc9A3M1Sc8A2S10G0S16S5S5S28S7Z40A1A4S12G0A1A3A3S0S22S21G1S20SceS19A2A2S20S29S19A2A3A2").
Proof. split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_vf7_f : ltac2:(tb__ "0|2|
S1S0S14S15S5S5A2M0A1S26ScfS31S35Sc9A3M1Sc8A2S10G0S16S5S5S28S7Z40A1A4S12G0A1A3A3S0S22S21G1S20SceS19A2A2S20S29S19A2A3A2").
Proof. split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_vf5_ok : ltac2:(tb__ "0|2|
S1S0S14S15S5S5A2M0A1S26ScfS2fS33ScaA3M1Sc8A2S10G0S16S5S5S28S7Z40A1A4S12G0A1A3A3S0S22S21G1S20ScdS17A2A2S20S5aS17A2A3A2").
Proof. split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_vf6_ok : ltac2:(tb__ "0|2|
S1S0S14S15S5S5A2M0A1S26ScfS30S34ScaA3M1Sc8A2S10G0S16S5S5S28S7Z40A1A4S12G0A1A3A3S0S22S21G1S20ScdS17A2A2S20S5aS17A2A3A2").
Proof. split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_vf7_ok : ltac2:(tb__ "0|2|
S1S0S14S15S5S5A2M0A1S26ScfS31S35ScaA3M1Sc8A2S10G0S16S5S5S28S7Z40A1A4S12G0A1A3A3S0S22S21G1S20ScdS17A2A2S20S5aS17A2A3A2").
Proof. split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma T5_zG_eq : ltac2:(tb__ "0|0|
S0S2Sc7S10S8S58S12S8A1A3S74A2Sa3A3"). Proof. reflexivity. Qed.
Lemma T6_zG_eq : ltac2:(tb__ "0|0|
S0S2Sc7S10S8S58S12S8A1A3S75A2Sa6A3"). Proof. reflexivity. Qed.
Lemma T7_zG_eq : ltac2:(tb__ "0|0|
S0S2Sc7S10S8S58S12S8A1A3S76A2Sa9A3"). Proof. reflexivity. Qed.

Definition hVP : positive := 98%positive.
Definition s_vpH : wsub := ltac2:(tb__ "0|0|
S10S15Sf0S5A2S16Sf0S5Sd3S29A4Sc1A3").
Lemma E_vp_eq : ltac2:(tb__ "0|0|
S0S13S2A1S1cS96Sc6A2S11S2S32A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma R_vp_eqH : ltac2:(tb__ "0|1|
S0S13S14S6A1M0A1SefS32S3bSd2A3S11G0S3fA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_pk0_eqH : ltac2:(tb__ "0|0|
S0S2S27S3bS32Sd2S3fSf3S57A6S7eA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_pf0_eqH : ltac2:(tb__ "0|0|
S0S2S27S3bS32Sd2S3fSf1S57A6S7aA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_pg0_eqH : ltac2:(tb__ "0|0|
S0S2S27S3bS32Sd2S3fSf2S57A6S7cA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_pk_eq : ltac2:(tb__ "0|0|
S0S13S2A1S1cS7eS60A2S11S2S7dA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_pf_eq : ltac2:(tb__ "0|0|
S0S13S2A1S1cS7aS60A2S11S2Sb0A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_pg_eq : ltac2:(tb__ "0|0|
S0S13S2A1S1cS7cS60A2S11S2S7bA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_pkF_eq : ltac2:(tb__ "0|0|
S0S2Sc7S10S8SbaS10S8Sc4S12S8A1A3A3S7dA2Sb2A3"). Proof. reflexivity. Qed.
Lemma T_pgF_eq : ltac2:(tb__ "0|0|
S0S2Sc7S10S8Sc3S12S8A1A3S7bA2Sb1A3"). Proof. reflexivity. Qed.
Definition isub_vp (L : axst) : wsub := ltac2:(tb__ "0|0|
SeeSd2S3bVL;S32A4").
Lemma imp_vp_keep : ltac2:(tb__ "0|2|
S1S0S14S15S5S5A2M0A1S26Sd7Sf3A1M1S24Sf4A1A2S10G0S80S88A1S12G0A1A3A3S1S0S14Se6A1Se5G1S23Sf4A1A2S81S86S87A2A3S0S22S21G1S20SaSd3A1S17A2A2S20S29S17A2A3A2A2").
Proof. repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_vp_fail : ltac2:(tb__ "0|2|
S1S0S14S15S5S5A2M0A1S26Sd7Sf1A1M1Sf9A2S10G0S80S88A1S12G0A1A3A3S0S22S21G1S20SaSd3A1S17A2A2S20S29S17A2A3A2").
Proof. split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_vp_grown : ltac2:(tb__ "0|3|
S1S0S14S15S5S5A2M0A1S26Sd7Sf2A1M1S10G0S16S5S5Sf6Sf8Sf7A1A4S12G0A1M2A3A2S10G0S16S5S5S3cSbbZ80S5bA2A4G2A3A3S1S0S14Se6A1Se5G1S23Sf5Sf6Sf7A2A1A2S81S86S5bA2A3S0S22S21G1S20SaSd3A1S17A2A2S20S29S17A2A3A2A2").
Proof. repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma E_mk1_eq : ltac2:(tb__ "0|0|
S0S13S2A1S1cS92S8aA2S11S2S3eA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_mg1_eq : ltac2:(tb__ "0|0|
S0S13S2A1S1cS91S8aA2S11S2S3dA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_mk_eq : ltac2:(tb__ "0|0|
S0S2S4S3eSfcS3S3eA1U1dS82S45A1A3A2S4dA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_mg_eq : ltac2:(tb__ "0|0|
S0S2S4S3dSfcS3S3dA1U1dS82S3cA1A3A2S4cA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma nth29_mk1 : ltac2:(tb__ "0|0|
S0S13S6A1SebS6S9S3S3eA1A1U1dA3S11S6S83S45A1A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma nth29_mg1 : ltac2:(tb__ "0|0|
S0S13S6A1SebS6S9S3S3dA1A1U1dA3S11S6S83S3cA1A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_mk0_eq : ltac2:(tb__ "0|0|
S0S2SeaS66S4dS84S4dS45S87A3S98S63A5S78A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_mg0_eq : ltac2:(tb__ "0|0|
S0S2SeaS66S4cS84S4cS3cS5bA3S97S63A5S77A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition holeZ (d : sv) : sobj := ltac2:(tb__ "0|0|
SfSdS103Sc2Vd;A1S7Z38A1A3S7Z0A1S7Z10A1S12SeA1ScA5").
Lemma nth1_Tmk0 : ltac2:(tb__ "0|0|
S0S13S6A1SebS6S9S3S78A1A1U1A3S11S6SdaS45A1A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma nth1_Tmg0 : ltac2:(tb__ "0|0|
S0S13S6A1SebS6S9S3S77A1A1U1A3S11S6SdaS3cA1A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_mk_eq : ltac2:(tb__ "0|0|
S0S13S2A1S1cSadS89A2S11S2SacA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_mg_eq : ltac2:(tb__ "0|0|
S0S13S2A1S1cSabS89A2S11S2SaaA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma C_open_eq : ltac2:(tb__ "0|0|
S0S2Se9Sb6Sc5A2S8cA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition ohF : sobj := Eval vm_compute in last (ss_objs (ax_S X_fit)) O_D.
Lemma objsF_eq : ltac2:(tb__ "0|1|
S0S14S6A1S9S3S51A1A1M0S18S6SecS6G0A2S10S6SdcS12S6A1A3A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma X_fit3_eq : ltac2:(tb__ "0|0|
S0S2SfbSe8S51SbfS7Z1A1A3S18S8Sb9SbS3S51A1A1A3A2Sb3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition ohNF : sobj := Eval vm_compute in last (ss_objs (ax_S X_nofit)) O_D.
Lemma objsNF_eq : ltac2:(tb__ "0|1|
S0S14S6A1S9S3S52A1A1M0S18S6SecS6G0A2S10S6SddS12S6A1A3A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma X_nofit1_eq : ltac2:(tb__ "0|0|
S0S2Se7S52SecS6S9S3S52A1A1A2A2S53A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma X_nofit2_eq : ltac2:(tb__ "0|0|
S0S2SfbS53S10S8SbeSbS3S53A1A1A3A2Sb4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma T_mnull_eq : ltac2:(tb__ "0|0|
S0S2SeaS65S62S85S6bS100SfdS12SffA1SfeA3A5SaeA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_mok0_eq : ltac2:(tb__ "0|0|
S0S2SeaS65S62S85S6bS101SfdS12SffA1SfeA3A5S79A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_mok_eq : ltac2:(tb__ "0|0|
S0S2Sc7S25Sb8A1S79A2SafA3"). Proof. reflexivity. Qed.

Definition iNs : nat := Eval vm_compute in find_idxb (fun o => sv_eqb (ob_base o) (SVar pN)) (ss_objs (ax_S X_sret)) 0%nat.
Definition sel_s : list nat := Eval vm_compute in (List.filter (fun j => negb (Nat.eqb j iNs)) (seq 0 (length (ss_objs (ax_S X_sret))))) ++ [iNs].
Lemma X_sret1_eq : ltac2:(tb__ "0|0|
S0S13S2A1S1cSb7S10S1dS1eSdbA1S10S1dS1fS102S1aS1bSdbA2U1A2S7Z18A1A2S12S1dA1A3A3A2S11S2S55A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition objsNs : list sobj := Eval vm_compute in removelast (removelast (ss_objs (ax_S X_sret1))).
Definition ohNs : sobj := Eval vm_compute in nth (length objsNs) (ss_objs (ax_S X_sret1)) O_D.
Definition otNs : sobj := Eval vm_compute in nth (S (length objsNs)) (ss_objs (ax_S X_sret1)) O_D.
Lemma objsNs_eq : ltac2:(tb__ "0|1|
S0S14S6A1S9S3S55A1A1S18S6S18S6Sd1S10S6Sd5S12S6A1M0A3A3S10S6SdfG0A3A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma X_sret2_eq : ltac2:(tb__ "0|0|
S0S2Se7S55S18S6Sd1S10S6Sd5S12S6A1A3A3A2S56A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma objsNs2_eq : ltac2:(tb__ "0|0|
S0S14S6A1S9S3S56A1A1S18S6Sd1S10S6Sd5S12S6A1A3A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition X_sret2x : axst := Eval vm_compute in ax_setX X_sret2 ((SVar pN, e32 (SLit 65536)) :: removelast (ax_X X_sret2)).
Definition s_idx : wsub := ltac2:(tb__ "0|0|
SfaS64S3S56A1S3Sd6A1A3").
Lemma objsNs2x_eq : ltac2:(tb__ "0|0|
S0S14S6A1S9S3Sd6A1A1S18S6Sd1S10S6Sd5S12S6A1A3A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition X_sret3x : axst := Eval vm_compute in drop_lastA X_sret2x objsNs.
Lemma X_sret3x_eq : ltac2:(tb__ "0|0|
S0S2Se7Sd6Sd1A2Sd9A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition s_sretx : wsub := ltac2:(tb__ "0|0|
SfaS64S3Sd9A1S3S8bA1A3").

Definition objsZ : list sobj := Eval vm_compute in removelast (removelast (ss_objs (ax_S X_nzret))).
Definition ohZ : sobj := Eval vm_compute in nth (length objsZ) (ss_objs (ax_S X_nzret)) O_D.
Definition osZ : sobj := Eval vm_compute in nth (S (length objsZ)) (ss_objs (ax_S X_nzret)) O_D.
Lemma objsZ_eq : ltac2:(tb__ "0|1|
S0S14S6A1S9S3S7fA1A1S18S6S18S6Sd4S10S6Sd8S12S6A1M0A3A3S10S6SdeG0A3A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma X_nzret2_eq : ltac2:(tb__ "0|0|
S0S2Se7S7fS18S6Sd4S10S6Sd8S12S6A1A3A3A2S54A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma objsZ2_eq : ltac2:(tb__ "0|0|
S0S14S6A1S9S3S54A1A1S18S6Sd4S10S6Sd8S12S6A1A3A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma X_nzret3_eq : ltac2:(tb__ "0|0|
S0S2Se7S54Sd4A2Sb5A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
End Lib_finalize_shape_eqs.

(* [comment removed for export] *)
Module Lib_vec_reserve_rom_eqs.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "Some"; "app"; "option"; "list"; "pair"; "bool"; "cons"; "fst"; "nat"; "nil"; "prod"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sv"; "ss_facts"; "sobj"; "SVar"; "SLit"; "ss_objs"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.Lib_vec_reserve_rom"; "E_c8'"; "E_r15f"; "E_rW1f"; "Xk_r"; "s_r"; "xf_rback"; "E_r15x"; "E_rW1x"; "T_c8ok0"; "T_c8okZ"; "inj"; "kn15"; "vW"; "Pre_c"; "R_c8"; "R_r15"; "R_rW1"; "T_c8n00"; "T_c8ok00"; "T_r15f0"; "T_r15ok0"; "T_r15okB"; "T_rW1f0"; "T_rW1ok0"; "T_rW1okB"; "X15"; "X8"; "XW1"; "injR"; "kbytes"; "s_c"; "tvf0"; "xf_rcall"; "E_c8"; "E_r15"; "E_rW1"; "FUEL_vr"; "N15"; "N8"; "NW1"; "PhisV"; "T_c8n0"; "T_c8ok"; "T_r15f"; "T_r15ok"; "T_rW1f"; "T_rW1ok"; "cutpcs_vr"; "cutsE"; "exitsE"; "injZ"; "xf_cbackN"; "xf_cbackZ"; "xf_ccall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.Lib_vec_reserve_rom.RR"; "Pre_rr"; "P_fail"; "P_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "T_afterA3"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "tv_factsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF"; "ejcertAF"; "efnode"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "T_afterA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "AE_A"; "UStopLeOrPc"; "Wcan"; "L_calloc_null"; "L_calloc_ok"; "@LinuxProcessSemantics.LinuxProcessSem.MemImageType"; "Segment"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.el.Lib_vec_reserve_rom_eqs"; "o_blk8"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR"; "drop_lastA"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM TobjJAR TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ej.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require em.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.Lib_vec_reserve_rom.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import VRRAddr RR.RRAddr.

Goal True. idtac "checking ejcertAF (vm_compute)". Abort.
Lemma ejcertAF_ok0 : ltac2:(tb__ "0|0|
S2S9S58S62S64S41S3dS48P64S49S4aA8SfA3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma ejcertAF_V : ltac2:(tb__ "0|6|
S7S61A1S54S7SeS7S54A1M0S18OF_;M1A2M2A1M3G3ScS7S55A1S54S7S59A1M4G4S2S7G0A1S5aG2G0SbG0G1A2M5R7A4S5aG2G0G5R6A4A3S2S9S58RaR9R8R6R5R4R3R2A8S58RaR9R7R6R5R4R3R2A8A3F_;Fexits;Fcuts;Fg;Fcps;Ffuel;FPhis';FPhis;Fnp;Fsg;").
Proof.
  intros sg np Phis Phis' fuel cps g cuts exits H. unfold ejcertAF, eecheckJAF_pf, echeckJAF_pf, VK. rewrite H. reflexivity.
Qed.

Lemma E_r15x_eq : ltac2:(tb__ "0|0|
S2S6S0A1S10S3bS39A2S4S0S1fA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_rW1x_eq : ltac2:(tb__ "0|0|
S2S6S0A1S10S3cS39A2S4S0S20A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_r15f_eq : ltac2:(tb__ "0|0|
S2S0S4fS1fS5S11S38S13S1S1fA1A1A3A2S1aA3"). Proof. reflexivity. Qed.
Lemma E_rW1f_eq : ltac2:(tb__ "0|0|
S2S0S4fS20S5S11S38S13S1S20A1A1A3A2S1bA3"). Proof. reflexivity. Qed.
Lemma T_r15f0_eq : ltac2:(tb__ "0|0|
S2S0S53S50S1aS1dS1aA1S28S51S1cA6S2cA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_r15ok0_eq : ltac2:(tb__ "0|0|
S2S0S53S50S1aS1dS1aA1S28S52S1cA6S2dA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_rW1f0_eq : ltac2:(tb__ "0|0|
S2S0S53S50S1bS1dS1bA1S29S51S1cA6S2fA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_rW1ok0_eq : ltac2:(tb__ "0|0|
S2S0S53S50S1bS1dS1bA1S29S52S1cA6S30A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_r15f_eq : ltac2:(tb__ "0|0|
S2S6S0A1S10S2cS1eA2S4S0S44A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_rW1f_eq : ltac2:(tb__ "0|0|
S2S6S0A1S10S2fS1eA2S4S0S46A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_r15okB_eq : ltac2:(tb__ "0|0|
S2S6S0A1S10S2dS1eA2S4S0S2eA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_rW1okB_eq : ltac2:(tb__ "0|0|
S2S6S0A1S10S30S1eA2S4S0S31A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_r15ok_eq : ltac2:(tb__ "0|0|
S2S0S56S57S8S12S12S15P8dA1S36S24A1A4A1S2eA2S45A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_rW1ok_eq : ltac2:(tb__ "0|0|
S2S0S56S57S8S12S12S15P8dA1S36S25A1A4A1S31A2S47A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_c8n00_eq : ltac2:(tb__ "0|0|
S2S0S5bS26S19S37S19A1S27S5fS5cS5eU1A1S5dA3A5S2aA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_c8n0_eq : ltac2:(tb__ "0|0|
S2S6S0A1S10S2aS4cA2S4S0S42A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_c8'_eq : ltac2:(tb__ "0|0|
S2S6S0A1S10S3aS4eA2S4S0S19A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_c8ok00_eq : ltac2:(tb__ "0|0|
S2S0S5bS26S19S37S19A1S27S60S5cS5eU1A1S5dA3A5S2bA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_c8ok0_eq : ltac2:(tb__ "0|0|
S2S6S0A1S10S2bS4dA2S4S0S21A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition o_blk8 : sobj := Eval vm_compute in last (ss_objs (ax_S T_c8ok0)) O_W.
Lemma T_c8okZ_eq : ltac2:(tb__ "0|1|
S3S2S7S14A1S17S1S21A1A1S5S14S17S1S22A1A1M0SaS14S63SdS14A1A3A3A3S2S0S65S21G0A2S22A3A2"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma T_c8ok_eq : ltac2:(tb__ "0|0|
S2S0S56S57S8S12S12S15P70A1S16Z80A1A4A1S22A2S43A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma N15_eq : ltac2:(tb__ "0|0|
S2S0S4fS32S5S11S5S11S35S24A1S23S24A1A3S13S1S32A1A1A3A2S3eA3"). Proof. reflexivity. Qed.
Lemma NW1_eq : ltac2:(tb__ "0|0|
S2S0S4fS34S5S11S5S11S35S25A1S23S25A1A3S13S1S34A1A1A3A2S40A3"). Proof. reflexivity. Qed.
Lemma N8_eq : ltac2:(tb__ "0|0|
S2S0S4fS33S5S11S5S11S4bS23S16Z8A1A1A3S13S1S33A1A1A3A2S3fA3"). Proof. reflexivity. Qed.
End Lib_vec_reserve_rom_eqs.

(* [comment removed for export] *)
Module Lib_vec_reserve_rom_pf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "uval"; "zlog15"; "bitem"; "KU"; "bd_nn"; "bsumK"; "bsumV"; "bd_below"; "bd_subst"; "BIc"; "BIs"; "BXok_d"; "ZK"; "bud_le"; "bxt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "valuation"; "sprop"; "ss_facts"; "SLit"; "sprop_eqb"; "sobj"; "SPUle"; "SVar"; "ss_next"; "rm"; "holds"; "SPBranch"; "DUnknown"; "SPNot"; "mkObj"; "rw"; "ob_cells"; "SAlu"; "sprop_below"; "cell"; "eval"; "ss_objs"; "sv_below"; "dflt_writable"; "ob_base"; "ob_dflt"; "ob_hi"; "ob_lo"; "@Corelib.Init.Datatypes"; "bool"; "true"; "list"; "pair"; "prod"; "cons"; "nil"; "nat"; "option"; "None"; "app"; "Some"; "fst"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@Stdlib.ZArith.BinInt.Z"; "le"; "mul"; "add"; "lt"; "pow"; "sub"; "div"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.Lib_vec_reserve_rom"; "vK"; "vW"; "bdP"; "s_r"; "nd0"; "vDt"; "kbytes"; "vE"; "cutsE"; "vC"; "kn15"; "ndG"; "vAl"; "E_c8'"; "O_W"; "Pre_c"; "Xk_r"; "tv0"; "B32"; "O_vec"; "vV"; "PD_rr"; "s_c"; "two47"; "vKn"; "z0"; "E_r15f"; "E_rW1f"; "P_fail"; "P_grown"; "P_keep"; "Pre_vr"; "R_c8"; "X15"; "X8"; "XW1"; "c8"; "exitsE"; "inj"; "ndN"; "spm"; "tvP"; "tvf0"; "vDn"; "B_EW"; "E_c8"; "E_r15"; "E_rW1"; "FUEL_vr"; "G_15"; "G_8"; "G_W1"; "O_alv"; "X_vr"; "cutpcs_vr"; "kbytesN"; "two48"; "xf_cbackN"; "xf_cbackZ"; "xf_ccall"; "xf_rback"; "xf_rcall"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "smatchA"; "@Stdlib.Lists.List"; "existsb"; "In"; "forallb"; "hd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "PTrue"; "ND"; "JA_pre"; "nd_below"; "tv_factsA"; "ffinA"; "JA"; "ok_frameKA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "rho_absorb"; "rho_sub"; "wsub"; "in_ranges"; "sv_subst"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.el.Lib_vec_reserve_rom_pf.Sum"; "baseF"; "basez"; "Phis"; "s_rbd"; "Phi1"; "Posts_vrr"; "d0"; "injF"; "C0"; "Phi0"; "K0"; "KN15"; "Phi3"; "W0"; "injz"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.Lib_vec_reserve_rom.RR"; "Pre_rr"; "P_ok"; "P0_rr"; "tv0"; "P_fail"; "bd0"; "vPn"; "ndR"; "tvP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "payA"; "csz"; "T_afterA"; "call_checkTA"; "site_okA"; "robjs_okA"; "xrs_okA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLeOrPc"; "AE_A"; "V_TOP"; "Wcan"; "unwind_stopJ"; "J_alloc_pre"; "L_calloc_null"; "L_calloc_ok"; "Posts_calloc"; "Pre_calloc"; "V_RES"; "alloc_contractsA"; "alloc_contractsA_ex"; "alloc_lawsA"; "calloc_size"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "pos_add_nat"; "call_linkP"; "sv_vars_all"; "wsub_dom_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "import_subA"; "call_checkPA"; "entails_frA"; "J_ofPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_geom"; "topG"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_EQ"; "ALU_ADD"; "BC_NE"; "BC_LTU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA"; "infrFF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF"; "JAF"; "phiK"; "efmeasA"; "phi_reads"; "JLAP"; "ejcertAF"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.el.Lib_vec_reserve_rom_pf"; "P0_vrr"; "Psi_keep"; "P0_vr"; "PDk_vrr"; "Psi_gdef"; "Psi_grown"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "T0"; "T_ok"; "import_tv"; "tv_sub_eqb"; "FBx"; "ivar_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "T_afterA3"; "pdescA"; "robjs_okF"; "xrs_okF"; "FFx"; "pd_okA"; "xrs_inclb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK"; "PostsCk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3"; "import_okPA3"; "import_postA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR"; "drop_lastA"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ej.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require em.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.em.Lib_vec_reserve_rom OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.el.Lib_vec_reserve_rom_eqs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import VRRAddr RR.RRAddr.

Lemma uval_kn15 : ltac2:(tb__ "0|1|
S19S44S5R1S4bA2S5dA2S0S3S5R2S55A2S46S5R2S4bA2M0S4aG0Z2A2A2A3F_;Frho;").
Proof.
  intros rho HK. unfold kn15. pose proof (uval_range rho vK).
  assert (E1 : uval rho (SAlu ALU_SRL vK (SLit 1)) = uval rho vK / 2).
  { unfold uval. rewrite U_srl_lit. change (2 ^ (1 mod 64)) with 2. reflexivity. }
  unfold B32 in HK. rewrite uval_add_small; rewrite E1; [lia|]. pose proof (Z.div_le_upper_bound (uval rho vK) 2). lia.
Qed.

Definition P0_vr (FB : list (Z * Z)) (FF : list (Z * Z * Z)) (r : valuation) : Prop := ltac2:(tb__ "0|2|
S1S2S0S3S8bQ40M0S28Vr;P11A2A2Z0M1A3A1S2S0S3S8bG0S28Vr;PfA2A2G1A3A1F_;SedVFF;S8bG0S28Vr;PeA2A2Z30A3A2").

Definition P0_vrr (FB : list (Z * Z)) (FF : list (Z * Z * Z)) (r : valuation) : Prop := ltac2:(tb__ "0|2|
S1SfaVFB;VFF;Vr;A3S3S1S44S5Vr;S50A2M0R1A2S47R1S46G0S45Z10S5Vr;S4bA2A2A2A2A2S2S0S3dS89Q8A1M1A1S22Vr;S8aQ40R2A2A2S3eG1A1A3A1F_;Fz;A2").

Definition Psi_keep (r0 rho : valuation) : Prop := ltac2:(tb__ "0|2|
S3S1S44S5Vr0;S50A2M0R1A2S47R1S46G0S45Z10S5Vr0;S4bA2A2A2A2A2S0S3dS89Q8A1A1S22Vrho;S8aQ40R2A2M1A2S22Vr0;G1A2A3F_;Fz;").

Definition Psi_gdef (r0 rho : valuation) : Prop := ltac2:(tb__ "0|2|
S3S1S44S5Vrho;S76A2M0R1A2S47R1S46G0S45Z10S5Vrho;S63A2A2A2A2A2S2S0S3dS89Q8A1M1A1S22Vrho;S8aQ40R2A2A2S3eG1A1A3A1F_;Fz;").
Definition Psi_grown (r0 rho : valuation) : Prop := ltac2:(tb__ "0|4|
S1S3S1S44Z0R1A2S47R1S45Z10S5Vr0;S54A2A2A2A2S1S0S3dS89Q8A1M0A1M1S22Vrho;S8aQ40M2S46S5Vrho;S76A2R2A2A2A2S22Vr0;S8aG2S46S5Vr0;S50A2R2A2A2A2M3A3S2S0G1G3S3eG0A1A3A1A2F_;Fj;SfcVr0;Vrho;A2A2").
Definition PDk_vrr : list pdescK := ltac2:(tb__ "0|4|
S3aS39S39S14S94A2M0S19S19OFrho;Fr0;M1A2M2S38G0G1S38S14S94S69S4fA4Sf9A4S3aG2S38G0G1S38S14S94S67S96S5cS3bS39S39S18S3A2S18A2A1M3S3bS7A1A3A4Sf9A4S3aG2S38G0G1S38S14S94S68S96S74G3S4dS4cS63A2A3A4SfdA4S3bG2A1A3A3A3").

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
Se5S19S37S89Q40A1A1Sf4OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
Sd6S43VAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S3S111VCST;R1A2S1S44Z0R2A2S47R2S110A2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S3S111VXGL;R1A2S1S44Z0R2A2S47R2S110A2A2F_;Fa;").
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S37S39S39S3S3A2S3A2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 3 BX.
Variable rho0 : valuation.

Let HTOP : InitState.segs_top segs <= IMG_HI := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eb.Lib_arena_alloc.HTOP_ok.
Let P0 := P0_vrr FB FF.
Definition Posts_vrr : list (axst * jpostA) := ltac2:(tb__ "0|0|
S10fVAInv;VCST;VXGL;VKc;Sf8S95SfbVFB;VFF;VBX;Aa").

Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S9bVAInv;VCST;VXGL;S8cVKc;Vrho0;VP0;VFB;VFF;VBX;S95Vnd;Ac").
Let Q (tp0 : list word) : assn := ltac2:(tb__ "0|0|
SdeS43S8cVrho0;Vtp0;SadA5").

Definition d0 : Z := uval rho0 vDt.
Definition C0 : Z := uval rho0 vC.
Definition K0 : Z := uval rho0 vK.
Definition KN15 : Z := uval rho0 kn15.
Definition W0 : Z := uval rho0 vW.

Definition Phi0 (rho : valuation) : Prop := ltac2:(tb__ "0|1|
S3S1S44SaeR1A2S47R1S46SaeS45Z10Sb2A2A2A2A2S0S3dS89Q8A1A1S22Vrho;S8aQ40R2A2M0A2S22Vrho0;G0A2A3F_;Fz;").

Definition Phi1 (kn : Z) (rho : valuation) : Prop := ltac2:(tb__ "0|6|
S1S3S1S44Z0R1A2M0S47R1S45Z10M1Sb0A2A2A2S0S3dS89Q8A1M2A1M3S22Vrho;S8aQ40M4S46S5Vrho;S20P8dA1A2R2A2A2A2M5S22Vrho0;S8aG4S46SaeR2A2A2A2A3F_;Fj;S3S1G0S47R1S45G1Vkn;A2A2A2S2S0G3G5S3eG2A1A3A1F_;Fj;A2").

Definition Phi3 (rho : valuation) : Prop := ltac2:(tb__ "0|1|
S3S1S44Z0R1A2S47R1Z80A2A2S2S0S3dS89Q8A1M0A1S22Vrho;S8aQ40S46S5Vrho;S20P70A1A2R2A2A2A2S3eG0A1A3A1F_;Fj;").
Definition Phis : list (list positive * (valuation -> Prop)) := ltac2:(tb__ "0|5|
S3aS39S37S4A1M0S19OFrho;M1A2M2S38G0G1S3bS4A1M3Sb1A4S3aG2S38G0G1S3aS4P8dG3A3M4SacSb3A1A4S3aG2S38G0G1G4SacSb5A1A4S3aG2S38G0G1S3aS4P70G3A3Sb4A4S3bG2A1A3A3A3A3").
Let JAFv (k : nat) (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
SeeVAInv;VCST;VXGL;S8cVKc;Vrho0;VP0;VFB;VFF;VBX;S95SefSaaVk;A2Vnd;Ad").

Lemma Phi1_reads : ltac2:(tb__ "0|0|
S3Sf1S3aS4P8dS3bS4A1A3SacR1A1A2Fkn;").
Proof.
  intros kn rho rho' HV _ HM [H1 H2].
  assert (E141 : uval rho' (SVar 141) = uval rho (SVar 141)) by (unfold uval; cbn [eval]; rewrite <- (HV 141%positive) by (cbn; tauto); reflexivity).
  unfold Phi1. rewrite E141. split; intros j Hj; rewrite <- HM; [exact (H1 j Hj) | exact (H2 j Hj)].
Qed.
Lemma Phis_reads : ltac2:(tb__ "0|3|
Sb7S39S37S4A1M0S19OF_;M1A2M2G2Sf1S41G0G1R1A3S42G0G1R1A3A2Lp;SaaA3").
Proof.
  unfold Phis. constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]; cbn [fst snd]; try apply Phi1_reads; unfold Phi3, Phi0.
  - intros rho rho' _ _ HM H z Hz. rewrite <- HM. exact (H z Hz).
  - intros rho rho' HV _ HM H j Hj.
    assert (E112 : uval rho' (SVar 112) = uval rho (SVar 112)) by (unfold uval; cbn [eval]; rewrite <- (HV 112%positive) by (cbn; tauto); reflexivity).
    rewrite E112, <- HM. exact (H j Hj).
Qed.
Lemma ejcertAF_ok : ltac2:(tb__ "0|0|
S0S35Sf3S43S8cSaaS7bS81P64S53S70A8S36A3").
Proof. rewrite (ejcertAF_V segs NF Phis PhisV FUEL_vr cutpcs_vr 100 cutsE exitsE eq_refl). exact ejcertAF_ok0. Qed.

Lemma JA_P0 : ltac2:(tb__ "0|0|
S94S14S19S37S89Q40A1A1S9eS8dS43VJAv;R5A1R4R3R2R1A6S1VP0;Vrho0;A1Sd9S8cVrho0;R4A3A2F_;Fw;Ftp;Frho;FS;Fnd;").
Proof. intros nd S rho tp [tr [ms md]] [_ (Ai & kc & HJ)]. pose proof HJ as (Hav & _ & _ & _ & _ & _ & _ & _ & _ & HP0 & _). split; [exact HP0 | exact Hav]. Qed.
Lemma vals_uval : ltac2:(tb__ "0|1|
S19S4Sd9S8cVrho0;R2A3SffR2S8cA2S0S3S5R4S20R3A1M0A2S5Vrho0;G0A2A3F_;F_;Fv;Frho;").
Proof. intros rho v Hav Hv. unfold uval. cbn [eval]. rewrite <- (proj1 Hav v Hv). reflexivity. Qed.

Definition baseF (F : list sprop) : Prop := ltac2:(tb__ "0|4|
S1S0S35S90S1aS1dS1fS20P1eA1M0S73Z40A1A2A1VF;A3S36A3S1S0S35S90S1aS1dS1fG0S20PaA1M1A2A1VF;A3S36A3S1S0S35S90S1aS1dS1fG1S5fA2A1VF;A3S36A3S1S0S35S90S1aS1dS1fS2aSe9S5fS1cZ20A1A3S1cS62A1M2A2A1VF;A3S36A3S1S0S35S90S1aS1dS1fS5fG2A2A1VF;A3S36A3S1S0S35S90S1aS1dS1fG1G2A2A1VF;A3S36A3S1S0S35S90S1aS1dS1fS1cZ1A1S52A2A1VF;A3S36A3S1S0S35S90S1aS1dS1fS52S1cZ1000A1A2A1VF;A3S36A3S1S0S35S90S1aS1dS1fS4cS1cS83A1A2A1VF;A3S36A3S1S0S35S90S1aS1dS1fS4bS1cS5dA1M3A2A1VF;A3S36A3S1S0S35S90S1aS1dS1fS51S4cA1S1cS77A1A2A1VF;A3S36A3S1S0S35S90S1aS1dS1fS51S4bA1G3A2A1VF;A3S36A3S1S0S35S90S1aS1dS1fS1cZ7fff7f800000A1G0A2A1VF;A3S36A3S0S35S90S1aS1dS1fG0S1cZ7fffff800000A1A2A1VF;A3S36A3A2A2A2A2A2A2A2A2A2A2A2A2A2").
Record basez (rho : valuation) : Prop := BZ {
  bz_sp : aceil + 64 <= uval rho (SVar 10) <= 2 ^ 47;
  bz_v : uval rho (SVar 10) <= uval rho vV /\ uval rho vV + 32 <= 2 ^ 47;
  bz_e : 1 <= uval rho vE <= 4096;
  bz_w : uval rho vW <= 2 ^ 48;
  bz_k : uval rho vK <= B32;
  bz_ew : uval rho (kbytes vW) = uval rho vE * uval rho vW /\ uval rho (kbytes vW) <= B_EW;
  bz_ek : uval rho (kbytes vK) = uval rho vE * uval rho vK /\ uval rho (kbytes vK) <= B32;

  bz_top : bv_unsigned (rw rho V_TOP) + 64 <= uval rho (SVar 10) /\ 140735332483072 <= bv_unsigned (rw rho V_TOP) <= 140737479966720 }.
Lemma uval_spm : ltac2:(tb__ "0|1|
S19S3S1S44Z0R1A2S44R1S5R2S20PaA1M0A2A2A2S0S3S5R3S73R2A1A2S49S5R3G0A2R2A2A3F_;Fk;Frho;").
Proof.
  intros rho k Hk. unfold spm, RR.spm, uval in *. rewrite U_add, U_lit. pose proof (U_range (eval rho (SVar 10))) as R. unfold M64v in *.
  set (x := bv_unsigned (eval rho (SVar 10))) in *.
  rewrite Zplus_mod_idemp_r. replace (x + - k) with (x - k) by lia. apply Z.mod_small. lia.
Qed.
Lemma basez_of : ltac2:(tb__ "0|0|
S19S37S1aA1Sb7S1aS23R2A1R1A3Sa8R2A1Sa9R4A1F_;F_;FF;Frho;").
Proof.
  intros rho F HF (B1 & B1' & BV1 & BV2 & BV3 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & BT1 & BT2).
  pose proof (holds_mem _ _ _ HF BT1) as HT1. pose proof (holds_mem _ _ _ HF BT2) as HT2. zf HT1. zf HT2.
  pose proof (holds_mem _ _ _ HF BV1) as V1. pose proof (holds_mem _ _ _ HF BV2) as V2. pose proof (holds_mem _ _ _ HF BV3) as V3. zf V1. zf V2. zf V3.
  pose proof (holds_mem _ _ _ HF B1) as H1. pose proof (holds_mem _ _ _ HF B1') as H1'. pose proof (holds_mem _ _ _ HF B2) as H2. pose proof (holds_mem _ _ _ HF B3) as H3.
  pose proof (holds_mem _ _ _ HF B4) as H4. pose proof (holds_mem _ _ _ HF B5) as H5. pose proof (holds_mem _ _ _ HF B6) as H6.
  pose proof (holds_mem _ _ _ HF B7) as H7. pose proof (holds_mem _ _ _ HF B8) as H8.
  zf H1. zf H1'. zf H2. zf H3. zf H4. zf H5. zf H6. zf H7. zf H8.
  repeat change (bv_unsigned (eval ?r ?e)) with (uval r e) in *.
  assert (E30 : uval rho (SVar 30) = bv_unsigned (rw rho V_TOP)) by reflexivity. rewrite E30 in *.
  unfold aceil, two47, RR.two47, two48, B_EW, B32 in *.
  rewrite !uval_lit in H2, H3, H4, H5, H6, H7, H8, HT1, HT2 by lia.
  rewrite uval_spm in H1 by lia.
  assert (EW : uval rho (kbytes vW) = uval rho vE * uval rho vW) by (unfold kbytes; apply uval_mul_small; nia).
  assert (EK : uval rho (kbytes vK) = uval rho vE * uval rho vK) by (unfold kbytes; apply uval_mul_small; nia).
  pose proof (uval_range rho vV). unfold two47, RR.two47 in V2, V3. rewrite uval_lit in V3 by lia. rewrite uval_add_small in V2 by (rewrite uval_lit by lia; lia). rewrite !uval_lit in V2 by lia.
  constructor; unfold aceil, B_EW, B32; lia.
Qed.

Lemma robjs_r : ltac2:(tb__ "0|1|
S19S37S1eA1M0S0G0R1S3aS1eS27S20PaA1S1cN40A1S1cZ0A1S29S93S1eS59R1A3A1S25A5S3aS1eS5eS50S54S4bS52A4S3bS1eA1A3A3A3Sa9R3A1S0S3S102Vrho0;A1S8bQ40S28R4ScbA2A2A3S10aVCST;Vrho0;VFB;VFF;R5S3bS39S18S18A2A1S3bS39S39S18S3A2S18A2A1R4A8F_;F_;F_;FR;Frho;").
Proof.
  intros rho R -> BZ ET o a Ho Hr. cbn in Ho. destruct Ho as [<-|[<-|[]]].
  - left. apply range_lit' in Hr; [|lia|lia]. destruct BZ. lia.
  - unfold O_vec in Hr. apply range_lit' in Hr; [|lia|lia]. left. destruct BZ. lia.
Qed.
Lemma xrs_r : ltac2:(tb__ "0|0|
S19Sa9R1A1S0S3S102Vrho0;A1S8bQ40S28R2ScbA2A2A3SedVFF;S5R3S57A2Z30A3S10bVCST;VXGL;Vrho0;VFB;VFF;R4S3bS39S18S18A2A1S3bS39S39S18S3A2S18A2A1S5bA9F_;F_;F_;Frho;").
Proof.
  intros rho BZ ET HA r a Hr Ha. cbn in Hr. destruct Hr as [<-|[<-|[]]]; cbn [fst snd] in Ha; left.
  - rewrite uval_lit in Ha by lia. left. destruct BZ. lia.
  - rewrite uval_lit in Ha by lia. eapply (infrFF_pclMA CST rho0 FF); [exact HA | lia].
Qed.

Lemma P0_now : ltac2:(tb__ "0|1|
S19Sd9S8cVrho0;R1A3VP0;Vrho0;A1S1S2S0S3S5R3S4bA2Z0M0A3A1S2S0S3S5R4S50A2G0A3A1F_;SedVFF;S5R3S57A2Z30A3A2F_;F_;Frho;").
Proof.
  intros rho Hav [(A & C) _]. unfold uval, vK, vDt, vV, vAl. cbn [eval].
  rewrite <- (proj1 Hav 17%positive eq_refl), <- (proj1 Hav 15%positive eq_refl), <- (proj1 Hav 14%positive eq_refl).
  auto.
Qed.

Lemma HIN_r : ltac2:(tb__ "0|3|
S14S37S1eA1M0S19Sd8S0G0R3S3aS1eS27S20PaA1S1cN40A1S1cZ0A1S29S93S1eS59R3A3A1S25A5S3aS1eS5eS50S54S4bS52A4S3bS1eA1A3A3A3Sa8S1bS15R5A1A1A1S0S18Sa1S4eR6A1PcA2S57A3S0S18Sa1S4eR7A1PdA2S50A3S0S18Sa1S4eR8A1PeA2S4bA3S0S35S90S1aS1dS1fS2aSe9S50S51S4bA1A3S20P1eA1A2A1S1bS15R9A1A1A3S36A3S0S35S90S1aS1dS1fS50S1cS62A1A2A1S1bS15RaA1A1A3S36A3Sb1R9A1Sb7S1aS23RaA1S1bS15RcA1A1A3VP0;Vrho0;A1Sd9S8cVrho0;RcA3S1S10aVCST;Vrho0;VFB;VFF;RdS3bS39S18S18A2A1M1S3bS39S39S18S3A2S18A2A1M2ReA8S1S10bVCST;VXGL;Vrho0;VFB;VFF;RdG1G2S5bA9SbbS106VFB;RdG1A3S10cVFF;RdG2A3Sa3Sa2RdReRcA3S4eRfA1A2A3A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fms;Frho;FR;FE;").
Proof.
  intros E R rho ms HR HB Hs12 Hs13 Hs14 HD30 HD47 HPhi HF HP0 Hav. destruct (P0_now rho Hav HP0) as (_ & HA).
  pose proof (holds_mem _ _ _ HF HD47) as F4. zf F4. unfold two47, RR.two47 in F4. rewrite uval_lit in F4 by lia.
  pose proof (basez_of rho _ HF HB) as BZ. pose proof (T0_agreeA rho0 NF rho Hav eq_refl) as ET.
  pose proof (holds_mem _ _ _ HF HD30) as F3. zf F3.
  split; [exact (robjs_r rho R HR BZ ET)|]. split; [exact (xrs_r rho BZ ET HA)|].
  split.
  - unfold RR.P0_ra. rewrite rw_call', Hs12. destruct HA as (f & sz & fl & Hin & H1 & H2). exists f, sz, fl.
    split; [unfold FFx; cbn; rewrite app_nil_r; exact Hin|]. unfold uval in H1, H2. lia.
  -
    intros z Hz. unfold uval, RR.vP, RR.vK in Hz. cbn [eval] in Hz. rewrite !rw_call', Hs13, Hs14 in Hz. repeat change (bv_unsigned (eval rho ?e)) with (uval rho e) in Hz.
    assert (ED : uval rho vDt = d0) by (unfold d0; exact (vals_uval rho 15 Hav ltac:(reflexivity))).
    assert (EK : uval rho vK = K0) by (unfold K0; exact (vals_uval rho 17 Hav ltac:(reflexivity))).
    destruct BZ as [Bsp Bv Be Bw Bk _ [EK16 _] [BT1 BT2]]. change (uval rho (SVar 30)) with (bv_unsigned (rw rho V_TOP)) in F3.
    pose proof (uval_range rho vDt). unfold B32 in Bk. change (uval rho vE) with 16 in EK16.
    rewrite uval_add_small in F3 by (rewrite EK16; lia). rewrite EK16 in F3.
    rewrite rm_absorb_out.
    + rewrite (HPhi z) by lia. destruct HP0 as [_ HDEF]. apply HDEF. unfold d0, K0 in *. lia.
    + intros (o & Ho & Hr). rewrite HR in Ho. cbn in Ho. rewrite Z_to_bv_unsigned, bv_wrap_small in Hr by (rewrite two64; lia).
      destruct Ho as [<-|[<-|[]]].
      * apply range_lit' in Hr; [|lia|lia]. lia.
      * unfold O_vec in Hr. apply range_lit' in Hr; [|lia|lia]. lia.
Qed.

Lemma robjs_c : ltac2:(tb__ "0|3|
S19Se5S37S1eA1M0S0G0R1S3aS1eS27S20PaA1S1cN40A1S1cZ0M1A1S29S93S1eS59R1A3A1S25A5S3aS1eS27S5fS1cZ10M2A1S1cZ20A1S3aS2cS6fG2S4bA2S3aS2cS6fZ18S52A2S3bS2cA1A3A3S25A5S3aS1eS7fS3bS1eA1A3A3A3A3Sa9R4A1S103R5Se7Se6R4A1A1A2S0S3S5R6S4bA2G1A3S9aVFF;R6A2SedVFF;S5R8S57A2Z30A3Sc7VCST;R8S3eS3A1R9R7A5F_;F_;F_;F_;F_;F_;FR;FAi;Frho;").
Proof.
  intros rho Ai R -> BZ HTK HK0 HFF HA o a Ho Hr. cbn in Ho. apply T_ok_rw in HTK as [HTK HTR]. destruct Ho as [<-|[<-|[<-|[]]]].
  - left. apply range_lit' in Hr; [|lia|lia]. destruct BZ. lia.
  - apply range_lit' in Hr; [|lia|lia]. left. destruct BZ. lia.
  - unfold O_alv in Hr. apply range_lit' in Hr; [|lia|lia]. eapply (infrFF_cmaddrA CST FF); [exact HFF | exact HA | lia].
Qed.
Lemma xrs_c : ltac2:(tb__ "0|1|
S19Se5S37S39S18S18A2A1M0S0G0R1S80S50S4bA2A3Sa9R4A1S103R5Se7Se6R4A1A1A2S0S3S5R6S4bA2Z0A3S9aVFF;R6A2SedVFF;S5R8S57A2Z30A3Sc8VCST;VXGL;R8S3eS3A1R9R7A6F_;F_;F_;F_;F_;F_;FX;FAi;Frho;").
Proof.
  intros rho Ai X -> BZ HTK HK0 HFF HA r a Hr Ha. cbn in Hr. apply T_ok_rw in HTK as [HTK HTR]. destruct Hr as [<-|[<-|[<-|[]]]]; cbn [fst snd] in Ha; left.
  - rewrite uval_lit in Ha by lia. left. destruct BZ. lia.
  - rewrite uval_lit in Ha by lia. eapply (infrFF_cmaddrA CST FF); [exact HFF | exact HA | lia].
  - exfalso. destruct BZ as [_ _ _ _ _ _ [EK _] _]. rewrite EK, HK0 in Ha. lia.
Qed.

Lemma baseF_E_c8' : ltac2:(tb__ "0|0|
Sa8S1bS15S58A1A1A1"). Proof. repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma baseF_E_r15f : ltac2:(tb__ "0|0|
Sa8S1bS15S65A1A1A1"). Proof. repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma baseF_E_rW1f : ltac2:(tb__ "0|0|
Sa8S1bS15S66A1A1A1"). Proof. repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma baseF_X15 : ltac2:(tb__ "0|0|
Sa8S1bS15S6cA1A1A1"). Proof. repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma baseF_XW1 : ltac2:(tb__ "0|0|
Sa8S1bS15S6eA1A1A1"). Proof. repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma baseF_X8 : ltac2:(tb__ "0|0|
Sa8S1bS15S6dA1A1A1"). Proof. repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma site_c8 : ltac2:(tb__ "0|2|
S19Sc6VAInv;VCST;VXGL;S8cVrho0;VP0;VFB;VFF;S58S61S58A1M0S6bR1S4fS3eS3A1Se5Sd8S1S1S44Z1S5R3Sc3G0A1A2M1A2S47G1S48Z2Z27A2A2A2S1S0S3S45S5R3Sa1G0PcA2A2S5R3Sa1G0PdA2A2A2G1A3ScdSccU1A1Sc9Sa3Sa2R3S6bR1A3G0A2A3A2A2Lms;LAi;AfFrho;").
Proof.
  intros rho Ai ms HF HP0 Hav HB HFF HN HD HZ HFR HM HT HTK. destruct (P0_now rho Hav HP0) as (_ & HA).
  pose proof (basez_of rho _ HF baseF_E_c8') as BZ.
  factz HF (SPNot (SPBranch BC_NE vK (SLit 0))) HK0. rewrite uval_lit in HK0 by lia.
  split; [apply (robjs_c rho Ai); [reflexivity | exact BZ | exact HTK | exact HK0 | exact HFF | exact HA]|].
  split; [apply (xrs_c rho Ai); [reflexivity | exact BZ | exact HTK | exact HK0 | exact HFF | exact HA]|].
  change (csz (s_c E_c8')) with (SMd M_MUL (SLit 8) vE). change (wsub_get (s_c E_c8') 12) with (SLit 8). change (wsub_get (s_c E_c8') 13) with vE.
  factz HF (SPUle vDt (SVar 30)) HDA. change (uval rho (SVar 30)) with (bv_unsigned (rw rho V_TOP)) in HDA.
  destruct BZ as [Bsp [BV1 BV2] Be Bw Bk [EW BEW] [EK BEK] [BT1 BT2]]. rewrite uval_mul_lit by lia. rewrite uval_lit by lia.
  split; [lia|]. split; [lia |].
  unfold unwind_stopJ. cbn [last_link link_var nth Wcan Wcan_from eval]. right. rewrite !rw_call'. change (wsub_get (s_c E_c8') 52) with vDt. change (wsub_get (s_c E_c8') 28) with (SAlu ALU_ADD vV (SLit 16)).
  repeat change (bv_unsigned (eval rho ?e)) with (uval rho e). rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia. lia.
Qed.

Definition s_rbd (kn : sv) : list bitem := ltac2:(tb__ "0|2|
S3fS7S3aS7SfZ1M0Z0M1S51Vkn;A1A3S3aS7SeG1S45Z2S8A2G0A3S3bS7A1A3A3S4dS4cVkn;A2A3").

Lemma sums_bdP : ltac2:(tb__ "0|1|
S19S18S18S1S0S3SbS4dR2R1A2M0R3A2S46S49S45Z6S5R3S51R2A1A2A2S45Z4S5R3S51R1A1A2A2A2S45Z20S5R3S52A2A2A2A3S0S3SaG0R3A2S45S45Z2S8A2S49S11S6S5R3R1A2A1A2A2A3A2Fk;Fw;Frho;").
Proof. intros. unfold bdP, PHI, KLG. cbn [bsumV bsumK]. unfold BudA.bival. cbn [lfval aval bi_v bi_k bi_f bi_c]. split; lia. Qed.
Lemma sums_s_rbd : ltac2:(tb__ "0|2|
S19S18S1S0S3SbSabR1A1M0R2A2S46S5R2S51R1A1A2SbS4dS4cR1A2M1R2A2A2A3S0S3SaG0R2A2S46S45Z2S8A2SaG1R2A2A2A3A2Fkn;Frho;").
Proof. intros. unfold s_rbd, BIs, BIc. cbn [bsumV bsumK app]. unfold BudA.bival. cbn [lfval aval bi_v bi_k bi_f bi_c]. split; lia. Qed.
Lemma bd_nn_bdP : ltac2:(tb__ "0|1|
S19S18S18S44S45Z4S5R3S51R1A1A2A2S46S45Z6S5R3S51R2A1A2A2S45Z20M0S5R3S52A2A2A2A2S44S5R4R2A2S48Z2G0A2A2S9S4dR4R3A2R5A2F_;F_;Fk;Fw;Frho;").
Proof.
  intros rho w k H1 H2. unfold bd_nn, bdP, PHI, KLG. repeat constructor; unfold BudA.bival; cbn [lfval aval bi_f bi_c]; [lia|].
  pose proof (zlog15_ZK _ H2). lia.
Qed.
Lemma bd_nn_s_rbd : ltac2:(tb__ "0|0|
S19S18S9S4dS4cR1A2R2A2S9SabR2A1R3A2F_;Fkn;Frho;").
Proof.
  intros rho kn H. unfold s_rbd. apply bd_nn_app. split; [|exact H]. unfold bd_nn, BIs, BIc. repeat constructor; unfold BudA.bival; cbn [lfval aval bi_f bi_c].
  - pose proof (uval_range rho (kbytes kn)). lia.
  - lia.
Qed.

Record injz (rho : valuation) (kn : sv) : Prop := IJ {
  ij_b : 4 * uval rho (kbytes vK) <= 3 * uval rho (kbytes kn);
  ij_a : 4 * uval rho (kbytes kn) <= 6 * uval rho (kbytes vW) + 32 * uval rho vE;
  ij_c : 1 <= uval rho (kbytes kn) <= B32;
  ij_e : uval rho (kbytes kn) = uval rho vE * uval rho kn }.
Definition injF (kn : sv) (F : list sprop) : Prop := ltac2:(tb__ "0|0|
S0S35S92S1aS1aS90S1aS1dR1A1VF;A3Lf;S71Vkn;A1A3S36A3").
Lemma injz_of : ltac2:(tb__ "0|0|
S19S18S37S1aA1Sb7S1aS23R3A1R1A3Sa9R4A1SafR4R3A2S44S5R6R5A2S48Z2Z31A2A2Sb6R7R6A2F_;F_;F_;F_;FF;Fkn;Frho;").
Proof.
  intros rho kn F HF BZ H Hkn. unfold injF, inj in H. cbn [forallb] in H.
  apply andb_prop in H as [H1 H]. apply andb_prop in H as [H2 H]. apply andb_prop in H as [H3 H]. apply andb_prop in H as [H4 _].
  pose proof (holds_mem _ _ _ HF H1) as F1. pose proof (holds_mem _ _ _ HF H2) as F2. pose proof (holds_mem _ _ _ HF H3) as F3. pose proof (holds_mem _ _ _ HF H4) as F4.
  zf F1. zf F2. zf F3. zf F4. repeat change (bv_unsigned (eval ?r ?e)) with (uval r e) in *.
  destruct BZ as [Bsp Bv Be Bw Bk [EW BEW] [EK BEK] Btop]. unfold B_EW, B32 in *.
  pose proof (uval_range rho kn) as Rkn.
  assert (EKn : uval rho (kbytes kn) = uval rho vE * uval rho kn) by (unfold kbytes; apply uval_mul_small; nia).
  rewrite !uval_lit in F3, F4 by lia.
  rewrite !uval_mul_lit in F1 by (rewrite ?EKn; lia). rewrite uval_add_small in F2 by (rewrite !uval_mul_lit by lia; lia).
  rewrite !uval_mul_lit in F2 by lia.
  constructor; unfold B32; lia.
Qed.

Lemma grow15 : ltac2:(tb__ "0|0|
S19Sa9R1A1S2S0S3S5R2S4bA2Z0A3A1S47S5R3S4bA2S5R3S4cA2A2S47S5R4S4cA2S5R4S55A2A2S44S46S6S5R5S4bA2A1Z1A2S6S5R5S55A2A1A2F_;F_;F_;F_;Frho;").
Proof.
  intros rho BZ H0 H1 H2. destruct BZ as [Bsp Bv Be Bw Bk _ _ _]. pose proof (uval_kn15 rho Bk) as E. rewrite E in H2 |- *.
  pose proof (uval_range rho vK). pose proof (zlog15_grow (uval rho vK) ltac:(lia) ltac:(lia)). lia.
Qed.
Lemma growW1 : ltac2:(tb__ "0|0|
S19Sa9R1A1S2S0S3S5R2S4bA2Z0A3A1S47S5R3S4bA2S5R3S4cA2A2S44S5R4S55A2S5R4S4cA2A2S44S46S6S5R5S4bA2A1Z1A2S6S5R5S4cA2A1A2F_;F_;F_;F_;Frho;").
Proof.
  intros rho BZ H0 H1 H2. destruct BZ as [Bsp Bv Be Bw Bk _ _ _]. pose proof (uval_kn15 rho Bk) as E. rewrite E in H2.
  pose proof (uval_range rho vK).
  destruct (Z_lt_ge_dec (uval rho vK) 2).
  - assert (E1 : uval rho vK = 1) by lia. rewrite E1, zlog15_1. pose proof (zlog15_ge1 (uval rho vW) ltac:(lia)). lia.
  - pose proof (zlog15_grow (uval rho vK) ltac:(lia) ltac:(lia)). pose proof (zlog15_mono (uval rho vK + uval rho vK / 2) (uval rho vW) ltac:(lia)). lia.
Qed.
Lemma grow0 : ltac2:(tb__ "0|0|
S19S18S0S3S5R2S4bA2Z0A3S44Z8S5R3R2A2A2S44S46S6S5R4S4bA2A1Z1A2S6S5R4R3A2A1A2F_;F_;Fkn;Frho;").
Proof. intros rho kn -> H. rewrite zlog15_0. pose proof (zlog15_ge1 (uval rho kn) ltac:(lia)). lia. Qed.

Lemma pay_r : ltac2:(tb__ "0|3|
S14S18Sa8S1bS15R2A1A1A1SafR2S1bS15R3A1A1A2S19Sb7S1aS23R1A1S1bS15R5A1A1M0A3Sa9R2A1S1S44S5R3R6A2M1S48Z2Z31A2A2S44S46S6S5R3S4bA2A1Z1A2S6G1A1A2A2F_;F_;Frho;Sc2S8cVrho0;VP0;G0S1cZ0M2A1G2S4dS4cS4bA2SabR4A1A8F_;F_;F_;Fkn;FE;").
Proof.
  intros E kn HB HI HG. split; [reflexivity|]. split; [lia|]. intros rho HF _ _ Hn. unfold pay_sem.
  pose proof (basez_of rho _ HF HB) as BZ. destruct (HG rho HF BZ) as [Hkn HL]. pose proof (injz_of rho kn _ HF BZ HI Hkn) as [I1 I2 I3 I4].
  destruct BZ as [Bsp Bv Be Bw Bk [EW BEW] [EK BEK] Btop]. unfold B32 in I3.
  assert (NN : bd_nn (bdP vW kn) rho) by (apply bd_nn_bdP; nia).
  split; [|split; [|apply bd_nn_s_rbd; exact NN]].
  - rewrite uval_lit by lia. destruct (sums_s_rbd rho kn) as [-> _]. destruct (sums_bdP rho vW kn) as [-> _]. destruct (sums_bdP rho vW vK) as [-> _]. lia.
  - destruct (sums_s_rbd rho kn) as [_ ->]. destruct (sums_bdP rho vW kn) as [_ ->]. destruct (sums_bdP rho vW vK) as [_ ->]. unfold KU. nia.
Qed.
Lemma pay_r15 : ltac2:(tb__ "0|1|
Sc2S8cVrho0;VP0;S1bS15S65A1A1S1cZ0M0A1G0S4dS4cS4bA2SabS55A1A8").
Proof.
  apply pay_r; [exact baseF_E_r15f | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc |].
  intros rho HF BZ.
  factz HF (SPBranch BC_NE vK (SLit 0)) HK0. factz HF (SPNot (SPBranch BC_GEU vK vW)) HKW. factz HF (SPBranch BC_LTU vW kn15) HWn.
  rewrite uval_lit in HK0 by lia.
  split; [| exact (grow15 rho BZ HK0 HKW HWn)].
  destruct BZ as [Bsp Bv Be Bw Bk _ _ _]. rewrite (uval_kn15 rho Bk). pose proof (uval_range rho vK). lia.
Qed.
Lemma pay_rW1 : ltac2:(tb__ "0|1|
Sc2S8cVrho0;VP0;S1bS15S66A1A1S1cZ0M0A1G0S4dS4cS4bA2SabS4cA1A8").
Proof.
  apply pay_r; [exact baseF_E_rW1f | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc |].
  intros rho HF BZ.
  factz HF (SPBranch BC_NE vK (SLit 0)) HK0. factz HF (SPNot (SPBranch BC_GEU vK vW)) HKW. factz HF (SPNot (SPBranch BC_LTU vW kn15)) HWn.
  rewrite uval_lit in HK0 by lia.
  split; [| exact (growW1 rho BZ HK0 HKW HWn)]. destruct BZ; lia.
Qed.

Lemma pay_c : ltac2:(tb__ "0|2|
S14S18S18Sa8S1bS15R3A1A1A1SafR3S1bS15R4A1A1A2S19Sb7S1aS23R1A1S1bS15R6A1A1M0A3Sa9R2A1S1S44S5R3R7A2M1S48Z2Z31A2A2S1S0S3S5R3S4bA2Z0A3S1S44Z8G1A2S0S3S5R3R6A2S5R3S51R7A1A2A3A2A2A2F_;F_;Frho;Sc2S8cVrho0;VP0;G0R4S8S4dS4cS4bA2S4dS4cR5A2A8F_;F_;F_;Fcst;Fkn;FE;").
Proof.
  intros E kn cst HB HI HG. split; [reflexivity|]. split; [unfold KU; lia|]. intros rho HF _ _ Hn. unfold pay_sem.
  pose proof (basez_of rho _ HF HB) as BZ. destruct (HG rho HF BZ) as (Hkn & HK0 & H8 & ->). pose proof (injz_of rho kn _ HF BZ HI Hkn) as [I1 I2 I3 I4].
  pose proof (grow0 rho kn HK0 H8) as HL.
  destruct BZ as [Bsp Bv Be Bw Bk [EW BEW] [EK BEK] Btop]. unfold B32 in I3.
  assert (NN : bd_nn (bdP vW kn) rho) by (apply bd_nn_bdP; nia).
  split; [|split; [|exact NN]].
  - destruct (sums_bdP rho vW kn) as [-> _]. destruct (sums_bdP rho vW vK) as [-> _]. rewrite EK, HK0. lia.
  - destruct (sums_bdP rho vW kn) as [_ ->]. destruct (sums_bdP rho vW vK) as [_ ->]. unfold KU. nia.
Qed.
Lemma pay_c8 : ltac2:(tb__ "0|0|
Sc2S8cVrho0;VP0;S1bS15S58A1A1Sc3S61S58A1A1S8S4dS4cS4bA2S4dS4cS1cZ8A1A2A8").
Proof.
  apply pay_c; [exact baseF_E_c8' | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc |].
  intros rho HF BZ.
  factz HF (SPNot (SPBranch BC_NE vK (SLit 0))) HK0. rewrite uval_lit in HK0 by lia.
  change (csz (s_c E_c8')) with (SMd M_MUL (SLit 8) vE). rewrite uval_mul_comm. fold (kbytes (SLit 8)).
  rewrite uval_lit by lia. destruct BZ; repeat split; lia.
Qed.

Lemma inj_holds : ltac2:(tb__ "0|4|
S19S18Sa9R2A1S44S5R3R2A2S48Z2Z31A2A2S44S45Z4M0S45S5R4S52A2M1S5R4S4bA2A2A2S45Z3S45G1S5R4R3A2A2A2A2S44S45G0S45S5R5S52A2M2S5R5R4A2A2A2S46S45Z6S45G2S5R5S4cA2A2A2S45Z20G2A2A2A2S1S44Z1S45S5R6S52A2S5R6R5A2A2M3A2S44G3S5dA2A2Sb7S1aS23R7A1S71R6A1A3F_;F_;F_;F_;F_;Fkn;Frho;").
Proof.
  intros rho kn BZ Hkn H1 H2 H3. destruct BZ as [Bsp Bv Be Bw Bk [EW BEW] [EK BEK] Btop]. unfold B_EW, B32 in *.
  assert (Hkn32 : uval rho kn <= 4294967295) by nia.
  pose proof (uval_range rho kn).
  assert (EKn : uval rho (kbytes kn) = uval rho vE * uval rho kn) by (unfold kbytes; apply uval_mul_small; nia).
  unfold inj, B32. repeat constructor; apply (proj2 (holds_ule _ _ _)); repeat change (bv_unsigned (eval ?r ?e)) with (uval r e).
  - rewrite !uval_mul_lit by (rewrite ?EK, ?EKn; lia). rewrite EK, EKn. lia.
  - rewrite uval_add_small by (rewrite !uval_mul_lit by (rewrite ?EW; lia); rewrite EW; lia).
    rewrite !uval_mul_lit by (rewrite ?EW, ?EKn; lia). rewrite EW, EKn. lia.
  - rewrite uval_lit by lia. rewrite EKn. lia.
  - rewrite uval_lit by lia. rewrite EKn. lia.
  - rewrite uval_lit by lia. exact Hkn32.
Qed.

Section X.
Variable TR : assn -> assn -> Prop.
Variable FAM : ltac2:(tb__ "0|0|
S3S37S89Q40A1A1S9dF_;F_;").
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S8eS14S19S37S89Q40A1A1S9dSb7S1aS23R3A1S1bS15R4A1A1A3VTR;S8dS43R6R5R4R3A5R2A2M0F_;G0F_;FQa;Ftp;Frho;FS;FJ;").
Hypothesis TR_ex : forall (T : Type) (J : T -> jpredA) S rho tp (Qa : assn),
  (forall x, TR (SPA segs (J x) S rho tp) Qa) -> TR (SPA segs (fun r p t m => exists x, J x r p t m) S rho tp) Qa.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S9dS9dS9dS9eR3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQa;FP';FP;").
Hypothesis TR_false : ltac2:(tb__ "0|0|
S9dS9dS9eS2R3R1A1A1Fw;VTR;R3R2A2F_;FQa;FP;").
Hypothesis TR_pureP : ltac2:(tb__ "0|1|
S9dOS9dS9eR4R1A1R4F_;Fw;R3VTR;R5R3A2M0F_;G0F_;F_;FQa;FX;FP;").
Hypothesis TR_exw : forall (T : Type) (P : T -> assn) (Qa : assn), (forall a, TR (P a) Qa) -> TR (fun w => exists a, P a w) Qa.
Hypothesis TR_callP : ltac2:(tb__ "0|5|
S8eS8eS14S14Sa4S37S1eA1M0S37S39S14SdfA2M1A1S37S39S18S18A2M2A1S9dS19S37S89Q40A1A1M3G2S91G2R1R5A3S91G2R2S16RbA1A3F_;Fr;S0S3dG0A1Se2RaR9R8A3S40G0R7A2A3S0S35Se1RbRaR9R8Sb8G1S14S41S14SdfA2R7A4A5S36A3S19G3VTR;S8dS43RfRdR2R1A5SdeS43S21S15RdA1A1R2R1RaA5A2Ftp1;Frho1;S37Sf5A1M4Sd8Sf4S8fS43R9R8R10S38G4Sf6R3Sf7R2R1A2A4A5R13RaR9R4R2A4R13Sa3Sa2RbRfSe4R3RaR4A3A3R10A2RaR5R3A4F_;F_;Fmd;Fms;Ftr;S14SdfG4Sd8Sf4S19G3G4Sd8Sf4S91G1S38S14SdfRaR9A4R14A3S8fS43R12R11R19S38G4Sf6R9Sf7R8R7A2A4A5R1cR13R12RaR8A4Sd9S21S15R1aA1A1Sa3Sa2R14R18Se4R9R13RaA3A3R19A2R8A3S8fS43R9R8ReS38G4Sf6R7Sf7R6R5A2A4A5ReSa3Sa2R16R1aSe4RbR15RcA3A3R1bA2R15RaR9R8R6A6S1S112R17Se4RcR16RdA3R1bR1cR1dR10R1eR19RbA9S19SdbR18Se4RdR17ReA3R1cR1dS15R1eA1S15R1fA1S15R11A1R1RcA9VTR;S8dS43Se3R11Sa3Sa2R19R1dSe4ReR18RfA3A3R1eA2R18RdRcA5S113R1eR1fR12R20R1dR1bA6R2RcA5R1aA2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S8dS43R11RfR8R7A5R9A2F_;F_;F_;F_;F_;F_;Ftp;Frho;FQa;FXk;FPosts;FR;Fs;FPre;FC;FJp;FJ;").
Hypothesis TR_phi : ltac2:(tb__ "0|0|
S19OF_;S94S14S19S37S89Q40A1A1S9dR6R3A1VTR;S8dS43VJAv;R6A1R5R4R3A5R2A2F_;VTR;S8dS43SeeVAInv;VCST;VXGL;S8cVKc;Vrho0;VP0;VFB;VFF;VBX;S95R7R6AdR5R4R3A5R2A2F_;FQa;Ftp;Frho;FS;Fnd;FPhi;").
Hypothesis CCALLOC : ltac2:(tb__ "0|1|
Se5S19S37S89Q40A1A1VTR;S8dS43SceVAInv;SccU1A1M0Sc9R3VKc;Sd7A6Sd2ScaG0Sc9A3R2R1A5SdeS43S8cR2R1Sd1ScaVAInv;VCST;VXGL;G0Sc9R3VKc;A8A5A2Ftp1;Frho1;FAi;").
Hypothesis CREALLOC : ltac2:(tb__ "0|1|
S37S39S3S3A2M0A1S37S39G0S3A2A1S13S19S37S89Q40A1A1S10Z2R3A2VTR;S8dS43S97VAInv;VCST;VXGL;VKc;SbbR6R5A2R6R5R4S95Sc0SbcSbeA2AaSb9R3R2A5SdeS43S8cR3R2S10fVAInv;VCST;VXGL;VKc;SbbS95S60R6R5R4AaA5A2F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Hypothesis REENTER : ltac2:(tb__ "0|5|
S14S94S3cS39S3S18A2M0S19S37S89Q40A1A1M1S3G1S91S39S39S39S14S94A2M2S3cA2M3G0A2S38G3G0S38G2S3cS38S14S94R8R7A4R6A4R5A4S53A3SefSaaR7R5A3S1S44Z0Sf0S38G3G0S38G2S3cS38S14S94RaR9A4R8A4R7A4R6A2M4A2S47G4R4A2A2VTR;S8dS43VJAv;RaA1RbR7R6A5VFAM;R5R4A2A2F_;F_;F_;Ftp0;Fb;Ftp;Frho;Frv;Fk;Fnd;FT;").
Hypothesis POST : ltac2:(tb__ "0|2|
S14S94S19OF_;M0S19G0F_;S19S37S89Q40A1A1M1S3G1S91S39S14SdfA2S38S14SdfR8Sf2VAInv;VCST;VXGL;VKc;VP0;VFB;VFF;VBX;S95R7R5AbA4SadA3S19R8R1A1R8Vrho0;R2A2F_;Fr;VTR;S8dS43SeeVAInv;VCST;VXGL;S8cVKc;Vrho0;VP0;VFB;VFF;VBX;S95R8R9AdRaR6R5A5VFAM;R4R3A2A2F_;F_;Ftp0;Fb;Ftp;Frho;FPsi;FPhi;Fnd;FP;").

Ltac meas := unfold efmeasA; cbn [ef_rank ef_var fst snd z0 eval]; rewrite lit_unsigned; cbn; lia.
Tactic Notation "innth" integer(n) := cbn [In cutsE exitsE Posts_vrr PDk_vrr PostsCk map fst snd]; do n right; left; reflexivity.

Lemma TR_phi_in : ltac2:(tb__ "0|0|
S19OF_;S94S14S19S37S89Q40A1A1S9dR6R3A1VTR;S8dS43SeeVAInv;VCST;VXGL;S8cVKc;Vrho0;VP0;VFB;VFF;VBX;S95R7R6AdR5R4R3A5R2A2VTR;S8dS43VJAv;R7A1R6R5R4A5R3A2F_;F_;FQa;Ftp;Frho;FS;Fnd;FPhi;").
Proof. intros Phi nd S rho tp Qa HP H. eapply TR_pre; [|exact H]. intros w Hw. apply SPA_JAF_intro; [exact Hw | exact HP]. Qed.

Lemma X_N : ltac2:(tb__ "0|6|
S14S14S37S1aA1S3S19S37S89Q40A1A1M0S3G0S0S14S101R8S3fS1aR6S1bS15R8A1A1A3A2R7A3S91S39S39S39S14S94A2M1S3cA2M2S39S3S18A2M3A2S38G2G3S38G1S3cS38S14S94R8S4fA4U0M4A4S38S3S18R6S64A4A4S53A3S44S45S46R7Z1A2S48Z2Z40A2A2R4A2S44Z0R8A2S0S35S92S1aS2bS21S15RcA1M5A1A1S3fS1aRaS1bG5A1A3A3S36A3S19Sb7S1aS23R1A1S1bS15ReA1A1A3Sb7S1aS23R2A1RdA3F_;Frho;VTR;S8dS43VJAFv;G4S4fA2ReRaR9A5VFAM;R8R7A2A2F_;F_;F_;F_;F_;F_;Ftp0;Fb;Ftp;Frho;Fr;Ffl;FNs;FXs;").
Proof.
  intros Xs Ns fl r rho tp b tp0 HN Hin Hb Hr Hbelow Hinj. apply TR_phi. intros HPhi.
  eapply TR_pre; [|apply (REENTER Ns nd0 0%nat (r, z0)); [exact Hin | exact HPhi | meas]].
  intros w Hw. rewrite <- HN. apply (SPA_refacts_JA segs); [exact Hw | exact Hbelow |].
  intros tr md _ HF. apply Forall_app. split; [exact (Hinj _ HF) | exact HF].
Qed.

Lemma X_X15 : ltac2:(tb__ "0|1|
S19S37S89Q40A1A1M0S3G0S44S45Z5aS48Z2Z40A2A2R2A2VTR;S8dS43VJAFv;U0S4fA2S6cR5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply (X_N X15 N15 (injR kn15 ++ inj kn15) 80 rho tp b tp0 N15_eq); [innth 1 | lia | lia | reflexivity |].
  intros r HF. pose proof (basez_of r _ HF baseF_X15) as BZ.
  factz HF (SPBranch BC_NE vK (SLit 0)) HK0. factz HF (SPNot (SPBranch BC_GEU vK vW)) HKW. factz HF (SPBranch BC_LTU vW kn15) HWn.
  factz HF (SPUle vW (SAlu ALU_ADD vC (SLit 1))) HWC. factz HF (SPUle vC vK) HCK.
  rewrite uval_lit in HK0 by lia. pose proof BZ as [Bsp Bv Be Bw Bk [EW BEW] [EK BEK]]. unfold B_EW, B32 in *.
  rewrite (uval_kn15 r Bk) in HWn. pose proof (uval_range r vK).
  pose proof (Z.div_mod (uval r vK) 2 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (uval r vK) 2 ltac:(lia)) as MB.
  rewrite uval_add_small in HWC by (rewrite uval_lit by lia; lia). rewrite uval_lit in HWC by lia.
  apply Forall_app. split.
  { unfold injR. constructor; [apply (proj2 (h_ule _ _ _)); lia|]. constructor; [|constructor].
    apply (proj2 (holds_bltu _ _ _)). repeat change (bv_unsigned (eval ?rr ?e)) with (uval rr e). rewrite (uval_kn15 r Bk). lia. }
  apply (inj_holds r kn15 BZ); rewrite ?(uval_kn15 r Bk); unfold B32; try nia.
Qed.
Lemma X_XW1 : ltac2:(tb__ "0|1|
S19S37S89Q40A1A1M0S3G0S44S45Z5aS48Z2Z40A2A2R2A2VTR;S8dS43VJAFv;U0S4fA2S6eR5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply (X_N XW1 NW1 (injR vW ++ inj vW) 80 rho tp b tp0 NW1_eq); [innth 2 | lia | lia | reflexivity |].
  intros r HF. pose proof (basez_of r _ HF baseF_XW1) as BZ.
  factz HF (SPBranch BC_NE vK (SLit 0)) HK0. factz HF (SPNot (SPBranch BC_GEU vK vW)) HKW. factz HF (SPNot (SPBranch BC_LTU vW kn15)) HWn.
  factz HF (SPUle vW (SAlu ALU_ADD vC (SLit 1))) HWC. factz HF (SPUle vC vK) HCK.
  rewrite uval_lit in HK0 by lia. pose proof BZ as [Bsp Bv Be Bw Bk [EW BEW] [EK BEK]]. unfold B_EW, B32 in *.
  rewrite (uval_kn15 r Bk) in HWn. pose proof (uval_range r vK).
  pose proof (Z.div_mod (uval r vK) 2 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (uval r vK) 2 ltac:(lia)) as MB.
  rewrite uval_add_small in HWC by (rewrite uval_lit by lia; lia). rewrite uval_lit in HWC by lia.
  apply Forall_app. split.
  { unfold injR. constructor; [apply (proj2 (h_ule _ _ _)); lia|]. constructor; [|constructor].
    apply (proj2 (holds_bltu _ _ _)). repeat change (bv_unsigned (eval ?rr ?e)) with (uval rr e). lia. }
  apply (inj_holds r vW BZ); unfold B32; try nia.
Qed.
Lemma X_X8 : ltac2:(tb__ "0|1|
S19S37S89Q40A1A1M0S3G0S44S45Z5aS48Z2Z40A2A2R2A2VTR;S8dS43VJAFv;U0S4fA2S6dR5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply (X_N X8 N8 (injZ ++ inj (SLit 8)) 80 rho tp b tp0 N8_eq); [innth 3 | lia | lia | reflexivity |].
  intros r HF. pose proof (basez_of r _ HF baseF_X8) as BZ.
  factz HF (SPNot (SPBranch BC_NE vK (SLit 0))) HK0. factz HF (SPUle vW (SAlu ALU_ADD vC (SLit 1))) HW8. factz HF (SPUle vC vK) HCK.
  rewrite uval_lit in HK0 by lia. pose proof BZ as [Bsp Bv Be Bw Bk [EW BEW] [EK BEK]]. unfold B_EW, B32 in *.
  pose proof (uval_range r vW). pose proof (uval_range r vC). rewrite uval_add_small in HW8 by (rewrite uval_lit by lia; lia). rewrite uval_lit in HW8 by lia.
  apply Forall_app. split.
  { unfold injZ. constructor; [|constructor]. apply (proj2 (h_ule _ _ _)). rewrite uval_lit by lia. lia. }
  apply (inj_holds r (SLit 8) BZ); rewrite ?uval_lit by lia; unfold B32; try nia.
Qed.

Lemma C_calloc_contra : ltac2:(tb__ "0|1|
S14S19S37S89Q40A1A1S9dS0S35S90S1aS1dS24SeaS4bS1cZ0A1M0A3A1S1bS15R4A1A1A3S36A3S0S35S90S1aS1dS24Se8S50G0A3A1S1bS15R5A1A1A3S36A3VTR;S8dS43VJAFv;U0S4fA2R6R5R4A5R3A2F_;F_;FQx;Ftp;Frho;FC;").
Proof.
  intros C rho tp Qx H1 H2. apply TR_phi. intros _. apply TR_facts. intros HF. apply TR_false. intros w [_ (Ai & kc & HJ)].
  pose proof HJ as (Hav & _ & _ & _ & _ & _ & _ & _ & _ & HP0 & _).
  destruct (P0_now rho Hav HP0) as (HKD & _ & _).
  pose proof (holds_mem _ _ _ HF H1) as F1. pose proof (holds_mem _ _ _ HF H2) as F2. zf F1. zf F2.
  repeat change (bv_unsigned (eval ?r ?e)) with (uval r e) in *. rewrite uval_lit in F1, F2 by lia. exact (HKD F1 F2).
Qed.
Lemma C_realloc_contra : ltac2:(tb__ "0|1|
S14S19S37S89Q40A1A1S9dS0S35S90S1aS1dS26S24SeaS4bS1cZ0A1M0A3A1A1S1bS15R4A1A1A3S36A3S0S35S90S1aS1dS26S24Se8S50G0A3A1A1S1bS15R5A1A1A3S36A3Sa8S1bS15R6A1A1A1VTR;S8dS43VJAFv;U0S4fA2R7R6R5A5R4A2F_;F_;F_;FQx;Ftp;Frho;FC;").
Proof.
  intros C rho tp Qx H1 H2 HB. apply TR_phi. intros _. apply TR_facts. intros HF. apply TR_false. intros w [_ (Ai & kc & HJ)].
  pose proof HJ as (Hav & _ & _ & _ & _ & _ & (HN & _ & _) & _).
  pose proof (basez_of rho _ HF HB) as [_ _ _ _ _ _ [EK _] _].
  pose proof (holds_mem _ _ _ HF H1) as F1. pose proof (holds_mem _ _ _ HF H2) as F2.
  pose proof (tnz_of_fact rho vDt (kbytes vK) F2) as Hnz. zf F1.
  repeat change (bv_unsigned (eval ?r ?e)) with (uval r e) in *. rewrite uval_lit in F1 by lia.
  cbn [nd_tv nd0] in HN. destruct (proj1 (Forall_forall _ _) HN (vDt, kbytes vK) ltac:(left; reflexivity) Hnz) as (Hpos & _).
  unfold tvv in Hpos. cbn [snd] in Hpos. change (bv_unsigned (eval rho (kbytes vK))) with (uval rho (kbytes vK)) in Hpos.
  rewrite EK, F1 in Hpos. lia.
Qed.

Lemma X_P_keep : ltac2:(tb__ "0|1|
S19S37S89Q40A1A1M0S3G0VTR;S8dS43VJAFv;U0S4fA2S69R4R3A5VFAM;R2R1A2A2Ftp0;Fb;Ftp;Frho;").
Proof. intros. apply (POST P_keep nd0 (phiK Phis 0) Psi_keep); [innth 0 | intros r Hr z Hz; exact (Hr z Hz)]. Qed.
Lemma X_P_fail : ltac2:(tb__ "0|1|
S19S37S89Q40A1A1M0S3G0VTR;S8dS43VJAFv;U0S96S5cS3bS39S39S18S3A2S18A2A1S3bS7A1A3A2S67R4R3A5VFAM;R2R1A2A2Ftp0;Fb;Ftp;Frho;").
Proof. intros. apply (POST P_fail (ND tv0 [] []) (phiK Phis 0) Psi_keep); [innth 1 | intros r Hr z Hz; exact (Hr z Hz)]. Qed.

Lemma X_G : ltac2:(tb__ "0|8|
S14Sa4S18S18S19OF_;S19S37S89Q40M0A1A1M1S3G1S0S35S17R9S68R8A3S36A3S0S35Sa7R9S8cA2S36A3S0S35SfeS8cS21S15RbA1A1A2S36A3S0S35S98S21S15RcA1A1S56RaR9A2A2S36A3S0S35S105RcS3aS39S18S18A2M2S38S18S18RbS82RaA1A4S3bG2A1A3S74A3S36A3S0S35S12S1bS15ReA1A1SdRdS4dS4cS63A2A2S4dS4cRbA2A3S36A3S0S18Sa1ReP8cA2RdA3S0S18Sa1RfP8dA2RdA3S0S35S90S1aS1dS1fS54S4bA2A1S1bS15R11A1A1A3S36A3S19Sb7S1aS23R1A1S1bS15R13A1A1A3Sd9S8cVrho0;R2A3R11R3A1S1S3S1S44Z0R1A2M3S47R1S45Z10M4Sb0A2A2A2S0S3dS89Q8A1M5A1M6S22R6S8aG0S46S5R6R16A2R2A2A2A2M7S22Vrho0;S8aG0S46SaeR2A2A2A2A3F_;Fj;S3S1G3S47R1S45G4S5R5R14A2A2A2A2S2S0G6G7S3eG5A1A3A1F_;Fj;A2F_;F_;F_;Fr;VTR;S8dS43SeeVAInv;VCST;VXGL;S8cVKc;Vrho0;VP0;VFB;VFF;VBX;S95RfS56R11R10A2AdR13ReRdA5VFAM;RcRbA2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Ftp0;Fb;Ftp;Frho;FPhi;Fkn;Fp;Fs;FG;").
Proof.
  intros G s p kn Phi rho tp b tp0 Hent Hid Hnf Hnb Htv Hbud Hs140 Hs141 HCK HPSI.
  apply TR_phi. intros HPhi. apply TR_facts. intros HF.
  apply (TR_pureP _ (P0 rho0 /\ agree_vals NF rho0 rho)); [intros w Hw; exact (JA_P0 _ _ _ _ w Hw)|]. intros [HP0 Hav].
  destruct (HPSI rho HF Hav HPhi) as [HC HDF].
  apply (TR_pre (SPA segs (JAv (ND tvP [] (bdP vW vKn))) P_grown (rho_sub rho s) tp)).
  { intros w Hw. exact (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 P0 FB FF BX PTrue HKc G P_grown s (ndG p kn) (ND tvP [] (bdP vW vKn)) rho tp w Hent Hid Hnf Hnb Htv eq_refl Hbud eq_refl Hw). }
  apply (TR_phi_in (fun r => Psi_grown rho0 r) (ND tvP [] (bdP vW vKn)) P_grown (rho_sub rho s) tp).
  - assert (E140 : uval (rho_sub rho s) vDn = uval rho p) by (unfold uval, vDn; rewrite <- eval_subst; cbn [sv_subst]; rewrite Hs140; reflexivity).
    assert (E141 : uval (rho_sub rho s) vKn = uval rho kn) by (unfold uval, vKn; rewrite <- eval_subst; cbn [sv_subst]; rewrite Hs141; reflexivity).
    assert (EM : rm (rho_sub rho s) = rm rho) by reflexivity. unfold Psi_grown, Psi_gdef. rewrite E140, E141, EM. split.
    + intros j Hj. split; [exact (HC j Hj) | apply (proj2 HP0); unfold d0, C0 in *].
      pose proof (vals_uval rho 16 Hav ltac:(reflexivity)) as EC. pose proof (vals_uval rho 17 Hav ltac:(reflexivity)) as EK.
      pose proof (holds_mem _ _ _ HF HCK) as FCK. zf FCK. change (uval rho vC) with (uval rho (SVar 16)) in FCK. change (uval rho vK) with (uval rho (SVar 17)) in FCK.
      change vDt with (SVar 15). change vK with (SVar 17). change vC with (SVar 16) in Hj. lia.
    + intros z Hz. replace z with (uval rho p + (z - uval rho p)) by lia. apply HDF. lia.
  - apply (POST P_grown (ND tvP [] (bdP vW vKn)) (fun r => Psi_grown rho0 r) Psi_grown); [innth 2 | intros r Hr; exact Hr].
Qed.

Lemma X_G15 : ltac2:(tb__ "0|1|
S19S37S89Q40A1A1M0S3G0VTR;S8dS43VJAFv;U1S56S20P8dA1S55A2A2S7cR4R3A5VFAM;R2R1A2A2Ftp0;Fb;Ftp;Frho;").
Proof.
  intros. apply (X_G G_15 s_g15 (SVar 141) kn15 (phiK Phis 1) rho tp b tp0);
    [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | reflexivity | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc |].
  intros r HF Hav [H1 H2]. split; [exact H1|]. intros j Hj. apply H2. unfold KN15.
  replace (uval rho0 kn15) with (uval r kn15); [exact Hj|]. unfold uval. rewrite (eval_agree_vals NF rho0 r kn15 Hav eq_refl). reflexivity.
Qed.
Lemma X_GW1 : ltac2:(tb__ "0|1|
S19S37S89Q40A1A1M0S3G0VTR;S8dS43VJAFv;U2S56S20P8dA1S4cA2A2S7eR4R3A5VFAM;R2R1A2A2Ftp0;Fb;Ftp;Frho;").
Proof.
  intros. apply (X_G G_W1 s_gW1 (SVar 141) vW (phiK Phis 2) rho tp b tp0);
    [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | reflexivity | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc |].
  intros r HF Hav [H1 H2]. split; [exact H1|]. intros j Hj. apply H2. unfold W0, vW. rewrite <- (vals_uval r 13 Hav ltac:(reflexivity)). exact Hj.
Qed.
Lemma X_G8 : ltac2:(tb__ "0|1|
S19S37S89Q40A1A1M0S3G0VTR;S8dS43VJAFv;U3S56S20P70A1S1cZ8A1A2A2S7dR4R3A5VFAM;R2R1A2A2Ftp0;Fb;Ftp;Frho;").
Proof.
  intros. apply (X_G G_8 s_g8 (SVar 112) (SLit 8) (phiK Phis 3) rho tp b tp0);
    [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | reflexivity | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc |].
  intros r HF Hav H. split.
  - intros j Hj. exfalso. pose proof (uval_range r vC).
    factz HF (SPNot (SPBranch BC_NE vK (SLit 0))) F1. factz HF (SPUle vC vK) F2. rewrite uval_lit in F1 by lia.
    pose proof (vals_uval r 16 Hav ltac:(reflexivity)) as EC. change (uval r vC) with (uval r (SVar 16)) in F2. unfold C0 in Hj. change vC with (SVar 16) in Hj. lia.
  - intros j Hj. apply H. rewrite uval_lit in Hj by lia. lia.
Qed.

Lemma U_Z_to_bv : ltac2:(tb__ "0|1|
S3S1S44Z0R1A2S47R1S48Z2Z40A2A2A2S0S3S8bQ40M0S8aG0R2A2A2R2A3F_;Fz;").
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. rewrite two64. exact Hz. Qed.

Lemma not_in_R : ltac2:(tb__ "0|3|
S37S1eA1M0S19S3S0G0R3S3aS1eS27S20PaA1S1cN40A1S1cZ0M1A1S29S93S1eS59R3A3A1S25A5S3aS1eS5eS50S54S4bS52A4S3bS1eA1A3A3A3Sa9R3A1S1S44G1R3A2S47R3S8bQ40M2S28R4ScbA2A2A2A2S2Sa5R5R6S8aG2R4A2A3A1F_;F_;F_;Fz;Frho;FR;").
Proof.
  intros R rho z HR BZ Hz (o & Ho & Hr). destruct BZ as [Bsp Bv Be Bw Bk _ _ [BT1 BT2]]. rewrite U_Z_to_bv in Hr by lia.
  rewrite HR in Ho. cbn in Ho. destruct Ho as [<-|[<-|[]]].
  - apply range_lit' in Hr; [|lia|lia]. lia.
  - unfold O_vec in Hr. apply range_lit' in Hr; [|lia|lia]. lia.
Qed.

Lemma X_E_r : ltac2:(tb__ "0|1c|
S14S14S14S14S14S14S14S14S37S1eA1M0S18S3S3cS19S37S89Q40A1A1M1S3G1S0S3dS14A1M2SecR10S88A2S40S14RfA2A3S0S14S101R10S3fS1aS75S1bS15R10A1A1A3A2RfA3S0S35S90S1aS1dS26S24Se8S50S1cZ0M3A1M4A3A1A1S1bS15R11A1A1A3S36A3S0G0RbS3aS1eS27S20PaA1S1cN40A1G4S29S93S1eS59RbA3A1S25A5S3aS1eS5eS50S54S4bS52A4S3bS1eA1A3A3A3Sa8S1bS15R12A1A1A1S0S18Sa1S4eR13A1PcA2S57A3S0S18Sa1S4eR14A1PdA2S50A3S0S18Sa1S4eR15A1PeA2S4bA3S0S18Sa1S4eR16A1P21A2RfA3S0S35S90S1aS1dS1fS54S4bA2A1S1bS15R17A1A1A3S36A3S0S35S90S1aS1dS1fS2aSe9S50S51S4bA1A3S20P1eA1M5A2A1S1bS15R18A1A1A3S36A3S0S35S90S1aS1dS1fS50S1cS62A1M6A2A1S1bS15R19A1A1A3S36A3S0S35S10eS5bS16R1aA1A2S36A3S0S3dG0A1Se2R1bSb9S4eR1bA1A3S40G0R15A2A3S0S35Se1R1cSb9S4eR1cA1R16Sb8S39S39S14S94A2M7S19S19OF_;M8F_;M9A2MaS14GaS41S14S94S41G7G9R1A3A3Ld;S60A4A5S36A3S0S35Sc5S8cS4eR1dA1A2S36A3S0S35SddS4eR1eA1S8cA2S36A3S0S35SfeS8cS21S15R1fA1A1A2S36A3S0S35S98S21S15R20A1A1S96S3fS39S18S18A2MbS3bGbA1McS5cA3S3bS39S39S18S3A2S18A2A1MdS4dS4cS4bA2MeA3A2S36A3S0S35ScS21S15R21A1A1S4dS4cR1aA2A2S36A3S0S35S105S4eR22A1S5cSbcA3S36A3Sc2S8cVrho0;VP0;S1bS15R23A1A1G4G3GeS3fS7SdS4eR23A1SbeA2S4dS4cR1cA2A3A8S0S35S92S39S109G9A2MfGfS10dSb9S8cS4eR25A1M10S21S15R25A1A1S41S109G9R1A3A5Ld;S60A3S36A3S0S14S108Sb9R25G10R1fSbdS5bA6R24A3S0G2SecR25S87A2S40S14R24A2A3M11S0S14S108Sb9R27S4eR27A1R21SbaS5bA6R24A3G11S0S14S100S99S38S18S18S20P8dA1M12S51R22A1A4A1R25A2R24A3S0S37GbA1M13S104Se0S4eR2aA1Sb9SbaR2aA4Sc1A2S3aGbS38S18S18G12S51R23A1A4GcA3A3S0G13S104Se0S4eR2bA1Sb9SbdR2bA4SbcA2S5cA3S0S18Sa6Se0S4eR2cA1Sb9SbaR2cA4SbfA2G12A3S0S35SdcS107S8cS4eR2dA1S21S15R2dA1M14A1S15SbaA1A4SbfA2S36A3S0S35S90S1aS1dS1fS2aSe9G12S51R27A1A3G5A2A1S1bS15R2bA1A1A3S36A3S0S35S90S1aS1dS1fR28S1cS5dA1A2A1S1bS15R2cA1A1A3S36A3S0S35S90S1aS1dS1fG12G6A2A1S1bG14A1A3S36A3S0S35S2fS8cR2aA2S36A3S0S3R2aS5Vrho0;R2bA2A3S0S35S90S1aS1dS24SebS4bR2cA3A1S1bS15R33A1A1A3S36A3S0S35S90S1aS1dS26S24Se8G12G4A3A1A1S1bS15R30A1A1A3S36A3S0S35S92S1aS2bS21S15R31A1M15A1A1S3fS1aS99S38S18S18G12S51R2eA1A4A1S1bG15A1A3A3S36A3S0S35S92S1aS2bS21S15R37A1M16A1A1S3fS1aS75S1bG16A1A3A3S36A3S91S39S39G7S3cA2M17S39S3S18A2M18A2M19S38G17G18S38G7S3cS38S14S94R35S72R30A1A4U0M1aA4S38S3S18Z3cS64A4M1bA4S53A3S91G19S38G17G18S38G7S3cS38S14S94R33S96S3aGbS38S18S18G12S51R31A1A4GcA3GdS4dS4cR31A2A3A4R2fA4G1bA4S53A3S0G8SefSaaR30A2SacR31A1A3S44S45Z46S48Z2Z40A2A2R2eA2VTR;S8dS43VJAFv;G1aS4fA2R3dR31R30A5VFAM;R2fR2eA2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Ftp0;Fb;Ftp;Frho;Fk;FKN;Fkn;FR;FTok;FTokB;FTok0;FTf;FTf0;FEf;FEx;FE;").
Proof.
  intros E Ex Ef Tf0 Tf Tok0 TokB Tok R kn KN k rho tp b tp0 HEx HEf HD HR HB Hs12 Hs13 Hs14 Hs33 HCK HD30 HD47 HXk He Hchk Htp Hdom Hnf Hnb Hbr Hpass HPAY Hpd
         HTf0 HTf HTok0 HTokB HTok Htvok Htvf Himp Hiv HN30 HknB HN47 Hknb HKN HKkn HpN Hbelow HbelowE HinF HinOK HPhik Hb.
  apply TR_phi. intros HPhi.

  eapply TR_pre with (P := SPA segs (JAv nd0) Ef rho tp).
  { intros w Hw. pose proof (SPA_axforms segs _ xf_rcall rho E Ex tp w HEx Hw) as Hw1.
    rewrite <- HEf. apply (SPA_refacts_JA segs); [exact Hw1 | exact HbelowE | ].
    intros tr md HJ HF. apply Forall_app. split; [|exact HF].
    eapply (JA_tv_facts segs AInv CST XGL NF Kc rho0 P0 FB FF BX PTrue ALA); [ | exact HJ | left; reflexivity |]; [reflexivity|].
    apply tnz_of_fact. exact (holds_mem _ _ _ HF HD). }
  apply TR_facts. intros HF.
  apply (TR_pureP _ (P0 rho0 /\ agree_vals NF rho0 rho)); [intros w Hw; exact (JA_P0 _ _ _ _ w Hw)|]. intros [HP0 Hav].
  pose proof (basez_of rho _ HF HB) as BZ.
  pose proof (holds_mem _ _ _ HF HCK) as FCK. pose proof (holds_mem _ _ _ HF HD30) as FD30. pose proof (holds_mem _ _ _ HF HD47) as FD47.
  pose proof (holds_mem _ _ _ HF HKkn) as FKkn.
  zf FCK. zf FD30. zf FD47. zf FKkn. unfold two47, RR.two47 in FD47. rewrite uval_lit in FD47 by lia.
  assert (ED : uval rho vDt = d0) by (unfold d0; exact (vals_uval rho 15 Hav ltac:(reflexivity))).
  assert (EC : uval rho vC = C0) by (unfold C0; exact (vals_uval rho 16 Hav ltac:(reflexivity))).
  assert (EK : uval rho vK = K0) by (unfold K0; exact (vals_uval rho 17 Hav ltac:(reflexivity))).
  assert (EKN : uval rho kn = KN) by (rewrite HKN; unfold uval; rewrite (eval_agree_vals NF rho0 rho kn Hav Hknb); reflexivity).
  assert (EK16 : uval rho (kbytes vK) = 16 * uval rho vK) by (destruct BZ as [_ _ _ _ Bk _ [EKb _] _]; rewrite EKb; reflexivity).
  rewrite uval_add_small in FD30 by (rewrite EK16; destruct BZ; unfold B32 in *; lia). rewrite EK16 in FD30.
  change (uval rho (SVar 30)) with (bv_unsigned (rw rho V_TOP)) in FD30.
  apply (client_callT_k segs AInv CST XGL ALA HCST HXGL NF Kc rho0 P0 FB FF BX PTrue HKc HBX RR.P0_rr PTrue (fun _ H => H) (fun _ _ _ H => H) RR.Pre_rr (RR.ndR RR.tv0 RR.bd0) PD_rr NF
           eq_refl eq_refl eq_refl TR TR_facts TR_ex TR_pre TR_callP CREALLOC eq_refl
           Ef (s_r Ef) R Xk_r rho tp [] tv0 [] (bdP vW vK) (bdP vW kn) ANone (FAM b tp0) HXk He Hchk Htp Hdom Hnf Hnb Hbr Hpass eq_refl HPAY Hpd).
  - intros Ai ms HF' HP0' Hav' HBf HFF HN HD' HZ HFR HM HT HTK. apply (HIN_r Ef R rho ms HR HB Hs12 Hs13 Hs14 HD30 HD47 HPhi HF' HP0' Hav').
  - intros [[Ld ndL] PsiL] rho' tp' Hd Hag _ HPSI. cbn [PD_rr RRP.PDk_rr In] in Hd.
    destruct Hd as [Hd|[Hd|[]]]; injection Hd as <- <- <-; cbn [fst snd nd_tv nd_bd nd_am RR.ndR ND am_subst app];
      destruct HPSI as (r0c & rhoL & HPsi & Hd1 & Hd2 & Hd3); cbn [fst snd] in HPsi, Hd1, Hd2, Hd3.
    +
      rewrite HTf0, Htvf. change (bd_subst _ []) with (@nil bitem). cbn [app].
      eapply TR_pre; [|apply (REENTER Tf (ndN kn) 0%nat (60, z0)); [exact HinF | | meas]].
      { intros w Hw. exact (SPA_axforms segs _ xf_rback rho' Tf0 Tf tp' w HTf Hw). }
      intros z Hz. pose proof (uval_range rho vDt).
      assert (NR : ~ in_ranges rho R (Z_to_bv 64 z)) by (apply (not_in_R R rho z HR BZ); lia).
      destruct (Hd2 _ NR) as [E1 E2]. rewrite E2. rewrite (HPsi z); [rewrite E1; exact (HPhi z Hz)|].
      unfold uval, RR.vP, RR.vK. rewrite !Hd1. cbn [sv_subst]. rewrite Hs13, Hs14. repeat change (bv_unsigned (eval rho ?e)) with (uval rho e). lia.
    +
      rewrite HTok0, Htvok. change (bd_subst _ []) with (@nil bitem). cbn [app].
      apply TR_facts. intros HF2.
      pose proof (holds_mem _ _ _ HF2 HN30) as FN30. pose proof (holds_mem _ _ _ HF2 HknB) as FknB. zf FN30. zf FknB. unfold B32 in FknB. rewrite uval_lit in FknB by lia.
      assert (H30 : (30 < ss_next (ax_S Ef))%positive) by (eapply Pos.lt_le_trans; [|apply (proj1 (Pos.leb_le _ _)); exact Hnf]; reflexivity).
      assert (E30 : uval rho' (SVar 30) = bv_unsigned (rw rho V_TOP)) by (unfold uval; cbn [eval]; rewrite <- (proj1 Hag 30%positive H30); reflexivity).
      assert (HknN : sv_below (ss_next (ax_S Ef)) kn = true) by (eapply sv_below_mono; [apply (proj1 (Pos.leb_le _ _)); exact Hnf | exact Hknb]).
      assert (EKn' : uval rho' kn = uval rho kn) by (unfold uval; rewrite <- (eval_agree_vals _ rho rho' kn Hag HknN); reflexivity).
      assert (EKn : uval rho' (kbytes kn) = 16 * uval rho' kn) by (unfold kbytes, vE; apply uval_mul_lit; lia).
      pose proof (uval_range rho' (SVar 141)) as R141. pose proof (holds_mem _ _ _ HF2 HN47) as FN47. zf FN47. unfold two47, RR.two47 in FN47. rewrite uval_lit in FN47 by lia.
      rewrite uval_add_small in FN30 by (rewrite EKn; lia). rewrite EKn, E30 in FN30.
      assert (E141 : uval rho' (SVar 141) = uval rhoL RR.vPn).
      { unfold uval. rewrite <- (Hd3 RR.vPn Hiv), Himp. reflexivity. }
      assert (ER0K : uval r0c RR.vK = uval rho vK) by (unfold uval, RR.vK; rewrite Hd1; cbn [sv_subst]; rewrite Hs14; reflexivity).
      assert (ER0P : uval r0c RR.vP = uval rho vDt) by (unfold uval, RR.vP; rewrite Hd1; cbn [sv_subst]; rewrite Hs13; reflexivity).
      assert (ER0N : uval r0c RR.vKn = uval rho kn) by (unfold uval, RR.vKn; rewrite Hd1; cbn [sv_subst]; rewrite Hs33; reflexivity).
      destruct HPsi as [HPsiC HPsiD]. rewrite ER0K, ER0P in HPsiC. rewrite ER0N in HPsiD.
      assert (NR1 : forall j, 0 <= j < 16 * uval rho kn -> ~ in_ranges rho R (Z_to_bv 64 (uval rho' (SVar 141) + j))).
      { intros j Hj. apply (not_in_R R rho _ HR BZ). lia. }
      assert (HP1 : Phi1 KN rho').
      { split.
        - intros j Hj.
          assert (HjK : 0 <= j < 16 * uval rho vK) by lia.
          assert (NR2 : ~ in_ranges rho R (Z_to_bv 64 (uval rho vDt + j))) by (apply (not_in_R R rho _ HR BZ); pose proof (uval_range rho vDt); lia).
          destruct (Hd2 _ (NR1 j ltac:(lia))) as [_ E2]. destruct (Hd2 _ NR2) as [E3 _].
          rewrite E2, E141. destruct (HPsiC j HjK) as [E4 _]. rewrite E4, E3, ED. apply HPhi. unfold K0 in *. rewrite <- ED. lia.
        - intros j Hj. rewrite <- EKN in Hj. destruct (Hd2 _ (NR1 j Hj)) as [_ E2]. rewrite E2, E141. apply HPsiD. exact Hj. }
      eapply TR_pre; [|apply (REENTER Tok (ND [(SVar 141, kbytes kn)] [] (bdP vW kn)) k (60, z0)); [exact HinOK | rewrite HPhik; exact HP1 | meas]].
      intros w Hw. pose proof (SPA_axforms segs _ xf_rback rho' Tok0 TokB tp' w HTokB Hw) as Hw1.
      rewrite <- HTok. unfold ax_add_facts.
      change (ax_setS TokB (add_facts (tv_factsA (SVar 141, kbytes kn)) (ax_S TokB))) with (ax_with_facts TokB (tv_factsA (SVar 141, kbytes kn) ++ ss_facts (ax_S TokB))).
      apply (SPA_refacts_JA segs); [exact Hw1 | exact Hbelow |].
      intros tr md HJ HF3. apply Forall_app. split; [|exact HF3].
      eapply (JA_tv_facts segs AInv CST XGL NF Kc rho0 P0 FB FF BX PTrue ALA); [ | exact HJ | left; reflexivity |]; [reflexivity|].
      apply tnz_of_fact. exact (holds_mem _ _ _ HF3 HpN).
Qed.

Lemma X_E_r15 : ltac2:(tb__ "0|1|
S19S37S89Q40A1A1M0S3G0S44S45Z46S48Z2Z40A2A2R2A2VTR;S8dS43VJAFv;U0S4fA2S79R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  apply (X_E_r E_r15 E_r15x E_r15f T_r15f0 T_r15f T_r15ok0 T_r15okB T_r15ok R_r15 kn15 KN15 1%nat rho tp b tp0 E_r15x_eq E_r15f_eq);
    [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | exact baseF_E_r15f | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc
    | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc
    | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc
    | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc
    | | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc
    | exact T_r15f0_eq | exact T_r15f_eq | exact T_r15ok0_eq | exact T_r15okB_eq | exact T_r15ok_eq
    | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc
    | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | reflexivity | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc
    | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | innth 4 | innth 5 | reflexivity | exact Hb].
  pose proof pay_r15 as P. unfold s_rbd in P. match goal with |- payA _ _ _ _ _ _ _ ?x => replace x with ([BIs 1 0 (kbytes kn15); BIc 0 (2 * KU) 1] ++ bdP vW kn15) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) end. exact P.
Qed.
Lemma X_E_rW1 : ltac2:(tb__ "0|1|
S19S37S89Q40A1A1M0S3G0S44S45Z46S48Z2Z40A2A2R2A2VTR;S8dS43VJAFv;U0S4fA2S7aR5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  apply (X_E_r E_rW1 E_rW1x E_rW1f T_rW1f0 T_rW1f T_rW1ok0 T_rW1okB T_rW1ok R_rW1 vW W0 2%nat rho tp b tp0 E_rW1x_eq E_rW1f_eq);
    [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | exact baseF_E_rW1f | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc
    | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc
    | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc
    | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc
    | | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc
    | exact T_rW1f0_eq | exact T_rW1f_eq | exact T_rW1ok0_eq | exact T_rW1okB_eq | exact T_rW1ok_eq
    | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc
    | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | reflexivity | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc
    | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | innth 6 | innth 7 | reflexivity | exact Hb].
  pose proof pay_rW1 as P. unfold s_rbd in P. match goal with |- payA _ _ _ _ _ _ _ ?x => replace x with ([BIs 1 0 (kbytes vW); BIc 0 (2 * KU) 1] ++ bdP vW vW) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) end. exact P.
Qed.

Lemma X_E_c : ltac2:(tb__ "0|19|
S14S14S14S14S14S14S14S14Sa4S37S1eA1M0S1eS19S37S89Q40A1M1A1M2S3G2S0S3dS14A1M3SecRfS86A2S40S14ReA2A3S0Sa4R8S61RfA1A3S0S3dG0A1Se2R10S5aR9A3S40G0R8A2A3S0S35Se1R11S5aRaR9S3aS14ScfScaSccU1A1M4Sc9A3M5S3aS14Sd0ScaG4Sc9A3M6S3bS14A1A3A3A5S36A3S0S35Sc5S8cRbA2S36A3S0S35SfeS8cS21S15R13A1A1A2S36A3S0S35S98S21S15R14A1A1S4fA2S36A3S0S35ScS21S15R15A1A1S4dS4cS1cZ8A1M7A2M8A2S36A3S0S35S2fS21S15R16A1A1Sc3RfA1A2S36A3S0S18Sa1Se0R10S5aG6R17A4Sd3A2S20SdaS21S15R17A1A1UaM9A2A1A3S0S18S20SdaS21S15R18A1A1G9A2A1S20P70A1MaA3Sc2S8cVrho0;VP0;S1bS15R19A1A1Sc3R12A1S8S4dS4cS4bA2G8A8Sc6VAInv;VCST;VXGL;S8cVrho0;VP0;VFB;VFF;R1aR13R12R10S4fS3eS3A1Se5Sd8S1S1S44Z1S5R12Sc3R15A1A2MbA2S47GbS48Z2McZ27A2A2A2S1S0S3S45S5R12Sa1R15PcA2A2S5R12Sa1R15PdA2A2A2GbA3ScdG4Sc9Sa3Sa2R12R14R1A3R15A2A3A2A2Lms;LAi;AfS0S35S90S1aS1dS26S24SeaS4bS1cZ0A1MdA3A1A1S1bS15R1bA1A1A3S36A3S0S14Sc4S5aR1cR15R14G5A5R1bA3S0G3SecR1cS84A2S40S14R1bA2MeA3S0S14Sc4S5aR1eR17R16G6A5R1bA3S0G3SecR1cS85A2GeA3S19S0G1S2dR1Sc3R1aA1A2S2dR1S1cZ80A1MfA2A3Fr;S0G0S2eS15R1dA1A1M10S3fS1eS2eS15R1cA1A1S3aS1eR18S3bS1eA1A3A3A3S0S14S114R1eG10A2R1dA3S0S18S31R1aA1GaA3S0S18S34R1bA1GdA3S0S18S33R1cA1GfA3S0S35S30S32R1dA1A1S36A3S0S14S100S99S38S18S18GaGfA4A1M11R22A2R21A3S0S35S90S1aS1dS26S24Se8GaGdA3A1A1S1bS15R23A1A1A3S36A3S0S35S92S1aS2bS21S15R24A1M12A1A1S3fS1aG11S1bG12A1A3A3S36A3S91S39S39S39S14S94A2M13S3cA2M14S39S3S18A2M15A2M16S38G14G15S38G13S3cS38S14S94R28S72G7A1A4U0M17A4S38S3S18Z3cS64A4M18A4S53A3S91G16S38G14G15S38G13S3cS38S14S94R25S56GaG7A2A4U3A4G18A4S53A3S44S45Z46S48GcZ40A2A2R20A2VTR;S8dS43VJAFv;G17S4fA2R2eR23R22A5VFAM;R21R20A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Ftp0;Fb;Ftp;Frho;FoB;FR;Fs;FTok;FTokZ;FTok0;FTok00;FTn;FTn0;FE;FE0;").
Proof.
  intros E0 E Tn0 Tn Tok00 Tok0 TokZ Tok s R oB rho tp b tp0 HE0 Hs He Hchk Htp Hnf Hnb Hbr Hcsz Hres H112 HPAY HSITE HK0
         HTn0 HTn HTok00 HTok0 Hcst HoZ HdZ Hb Hl Hh Hdw HTok Hp0 Hbelow HinN HinOK Hbnd.
  apply TR_phi. intros _.
  eapply TR_pre with (P := SPA segs (JAv nd0) E rho tp); [intros w Hw; exact (SPA_axforms segs _ xf_ccall rho E0 E tp w HE0 Hw)|].
  apply TR_facts. intros HF.
  apply (TR_pureP _ (P0 rho0 /\ agree_vals NF rho0 rho)); [intros w Hw; exact (JA_P0 _ _ _ _ w Hw)|]. intros [HP0 Hav].

  pose proof (holds_mem _ _ _ HF HK0) as FK0. zf FK0. rewrite uval_lit in FK0 by lia.
  assert (EK : uval rho vK = K0) by (unfold K0; exact (vals_uval rho 17 Hav ltac:(reflexivity))).
  assert (PHI0 : forall r, Phi0 r) by (intros r z Hz; exfalso; pose proof (uval_range rho vK); lia).
  subst s. unfold Pre_c in *.
  apply (calloc_callT segs AE_A AInv CST XGL ALA HCST HXGL NF Kc rho0 P0 FB FF BX PTrue HKc HBX TR TR_facts TR_ex TR_pre TR_callP
           (Wcan 1) UStopLeOrPc E (s_c E) R rho tp nd0 (bdP vW (SLit 8)) (FAM b tp0) CCALLOC He Hchk Htp Hnf Hnb Hbr Hcsz Hres HPAY (fun _ _ _ _ => I) HSITE).
  -   intros rho' tp'. rewrite HTn0. cbn [nd_tv nd_fr nd0].
    eapply TR_pre; [|apply (REENTER Tn (ndN (SLit 8)) 0%nat (60, z0)); [exact HinN | exact (PHI0 rho') | meas]]. intros w Hw. exact (SPA_axforms segs _ xf_cbackN rho' Tn0 Tn tp' w HTn Hw).
  -   intros rho' tp'. rewrite HTok00, H112. cbn [nd_tv nd_fr nd0].
    apply (TR_pre (fun w => exists r2, Phi3 r2 /\ SPA segs (JAv (ndG (SVar 112) (SLit 8))) Tok r2 tp' w)).
    { intros w Hw0. pose proof (SPA_axforms segs _ xf_cbackZ rho' Tok00 Tok0 tp' w HTok0 Hw0) as Hw. clear Hw0.

      apply (SPA_JA_tv_ext segs AInv CST XGL NF Kc rho0 P0 FB FF BX PTrue ((SVar 112, csz (s_c E)) :: tv0) ((SVar 112, SLit 128) :: tv0)) in Hw.
      2: { intros _. split; [cbn [map]; unfold tvv; cbn [fst snd]; rewrite (Hcst rho'); reflexivity|].
           intros [|k] t t' Ht Ht'; cbn [nth_error] in Ht, Ht'; [injection Ht as <-; injection Ht' as <-; unfold tnz; cbn [fst]; tauto|].
           rewrite Ht in Ht'. injection Ht' as <-. tauto. }
      apply (SPA_JA_drop_tv segs AInv CST XGL NF Kc rho0 P0 FB FF BX PTrue _ [] (bdP vW (SLit 8)) 1) in Hw.
      2: {
           intros _ t Ht. unfold tv0 in Ht. cbn [nth_error] in Ht. injection Ht as <-. right.
           destruct (JA_P0 _ _ _ _ w Hw) as [_ Hav'].
           assert (EK' : uval rho' vK = 0).
           { transitivity (uval rho0 (SVar 17)); [exact (vals_uval rho' 17 Hav' ltac:(reflexivity))|].
             transitivity (uval rho vK); [symmetry; exact (vals_uval rho 17 Hav ltac:(reflexivity)) | exact FK0]. }
           unfold tvv. cbn [snd]. change (bv_unsigned (eval rho' (kbytes vK))) with (uval rho' (kbytes vK)).
           unfold kbytes. rewrite uval_mul_small by (rewrite EK'; lia). rewrite EK'. lia. }
      cbn [remove_nth] in Hw.
      change (ND [(SVar 112, SLit 128)] [] (bdP vW (SLit 8))) with (NDA [(SVar 112, SLit 128)] [] (bdP vW (SLit 8)) ANone) in Hw.
      destruct w as [tr [ms md]].

      destruct (JA_absorb_tr segs HTOP AInv CST XGL ALA HCST HXGL NF Kc rho0 P0 FB FF BX PTrue [(SVar 112, SLit 128)] [] (bdP vW (SLit 8)) ANone 0 (SVar 112) (SLit 128)
                  Tok0 (ss_objs (ax_S TokZ)) oB (SLit 128) rho' tp' tr ms md HoZ eq_refl Hl Hh Hdw) as (Hw6 & OUT & DEF & _).
      { intros r _. rewrite Hb. rewrite !uval_lit by lia. lia. }
      { exact Hw. }
      rewrite HdZ in Hw6. rewrite Hb, (uval_lit rho' 128) in DEF by lia.
      set (r2 := rho_absorb rho' [oB] (vms md tp' ms)) in *. exists r2. split.
      - intros j Hj. apply DEF. unfold r2, uval. rewrite eval_absorb. change (bv_unsigned (eval rho' (SVar 112))) with (uval rho' (SVar 112)). lia.
      - rewrite <- HTok. unfold ax_add_facts.
        change (ax_setS TokZ (add_facts (tv_factsA (SVar 112, SLit 128)) (ax_S TokZ))) with (ax_with_facts TokZ (tv_factsA (SVar 112, SLit 128) ++ ss_facts (ax_S TokZ))).
        apply (SPA_refacts_JA segs); [exact Hw6 | exact Hbelow |].
        intros tr' md' HJ HF2. apply Forall_app. split; [|exact HF2].
        eapply (JA_tv_facts segs AInv CST XGL NF Kc rho0 P0 FB FF BX PTrue ALA); [ | exact HJ | left; reflexivity |]; [reflexivity|].
        apply tnz_of_fact. exact (holds_mem _ _ _ HF2 Hp0). }
    apply TR_exw; intros r2. eapply TR_pureP; [intros w [H _]; exact H|]. intros HP3.
    eapply TR_pre; [intros w [_ Hw]; exact Hw|].
    apply (REENTER Tok (ndG (SVar 112) (SLit 8)) 3%nat (60, z0)); [exact HinOK | exact HP3 | meas].
Qed.
Lemma X_E_c8 : ltac2:(tb__ "0|1|
S19S37S89Q40A1A1M0S3G0S44S45Z46S48Z2Z40A2A2R2A2VTR;S8dS43VJAFv;U0S4fA2S78R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  apply (X_E_c E_c8 E_c8' T_c8n00 T_c8n0 T_c8ok00 T_c8ok0 T_c8okZ T_c8ok (s_c E_c8') R_c8 o_blk8 rho tp b tp0 E_c8'_eq eq_refl);
    [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc
    | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | exact pay_c8 | exact (site_c8 rho) | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc
    | exact T_c8n00_eq | exact T_c8n0_eq | exact T_c8ok00_eq | exact T_c8ok0_eq
    | intros r; apply bv_eq; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc
    | exact (proj1 T_c8okZ_eq) | exact (proj2 T_c8okZ_eq) | reflexivity | reflexivity | reflexivity | reflexivity
    | exact T_c8ok_eq | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | innth 8 | innth 9 | exact Hb].
Qed.

Lemma exits_okT : ltac2:(tb__ "0|4|
S14S94S3cS39S3S18A2M0S19S37S89Q40A1A1M1G1S91S39S39S39S14S94A2M2S3cA2M3G0A2S38G3G0S38G2S3cS38S14S94R7R6A4R5A4R4A4S70A3VTR;S8dS43VJAFv;R6R7A2R8R4R3A5VFAM;Sf0S38G3G0S38G2S3cS38S14S94R8R7A4R6A4R5A4R4A2R2A2A2F_;Ftp0;Ftp;Frho;FrvX;FkX;FndX;FX;").
Proof.
  intros X ndX kX rvX rho tp tp0 Hin. cbn [In exitsE] in Hin.
  destruct Hin as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[]]]]]]]]]]]]]]]; injection H as <- <- <- <-.
  - apply X_X15. meas.
  - apply X_XW1. meas.
  - apply X_X8. meas.
  - apply X_E_r15. meas.
  - apply X_E_rW1. meas.
  - apply C_calloc_contra; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - apply C_calloc_contra; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - apply X_E_c8. meas.
  - apply C_realloc_contra; [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | repeat split; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
  - apply X_P_keep.
  - apply X_P_fail.
  - apply X_G15.
  - apply X_GW1.
  - apply X_G8.
Qed.
End X.

Section Safety.
Variable ok : world -> Prop.
Hypothesis Hok : ltac2:(tb__ "0|0|
S9cS43VKc;Vok;A3").
Hypothesis AC : ltac2:(tb__ "0|0|
Sd4S43ScaVAInv;VCST;VXGL;A5").

Theorem vec_reserve_rom_sum : ltac2:(tb__ "0|0|
S37S89Q40A1A1Sa0S43Vok;S8dS43S97VAInv;VCST;VXGL;VKc;Sf8VFB;VFF;A2VFB;VFF;VBX;S95S4fAaS6aVrho0;R1A5SdeS43S8cVrho0;R1SadA5A4Ftp0;").
Proof.
  intros tp0.
  eapply triple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_sound_JAF segs AInv CST XGL ALA NF Kc rho0 P0 FB FF BX PTrue HKc Phis Phis_reads FUEL_vr cutpcs_vr 100
                (map efdrop cutsE) (map efdrop exitsE) ok (Q tp0) Hok (ejcertAF_jcertAF segs NF Phis _ _ _ _ _ ejcertAF_ok))
         with (ndT := nd0) (kT := 0%nat); [|left; reflexivity].
       intros X ndX kX rho tp Hin. apply in_map_iff in Hin as ([[[X' nd'] k'] rv] & E0 & Hin). cbn in E0. injection E0 as <- <- <-.
       apply (exits_okT (triple segs ok) (fun _ _ w => SPfamGTA segs (map (nodeIAF AInv CST XGL NF Kc rho0 P0 FB FF BX PTrue Phis) (map efdrop cutsE)) w \/ Q tp0 w)
                (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok) (TRs_false segs ok) (TRs_pureP segs ok) (@triple_ex segs ok) (call_soundPA3 segs ok)) with (rvX := rv) (tp0 := tp0).
       - intros Phi nd S rho1 tp1 Qa H. exact (triple_JAF segs AInv CST XGL NF Kc rho0 P0 FB FF BX PTrue Phi ok nd S rho1 tp1 Qa H).
       - intros Ai rho1 tp1. apply (aca_calloc _ _ _ _ _ AC); [first [left; reflexivity | right; left; reflexivity | right; right; left; reflexivity] | exact HKc| |]. exact (proj1 Hok). exact (proj2 Hok).
       - intros FBc FFc BXc rho1 tp1 HB. apply (RRP.realloc_rom_sum AInv CST XGL ALA HCST HXGL Kc HKc FBc FFc BXc HB rho1 ok Hok AC tp1).
       - intros T nd k rv' rho1 tp1 b tp2 HinT HP _. apply (reenter_cutJAF segs AInv CST XGL NF Kc rho0 P0 FB FF BX PTrue Phis ok (map efdrop cutsE) T nd k); [|exact HP].
         apply in_map_iff. exists (T, nd, k, rv'). auto.
       - intros P nd Phi Psi rho1 tp1 b tp2 HinP HPsi. apply (exit_postGAF segs AInv CST XGL NF Kc P0 FB FF BX PTrue ok rho0 tp0 Phi Psi nd Posts_vrr P); [exact HinP | exact HPsi].
       - exact Hin. }
  intros w Hw. apply SPA_JAF_intro; [apply JA_pre_intro; exact Hw|]. intros z Hz. reflexivity.
Qed.
End Safety.

Section Existence.
Hypothesis ACX : ltac2:(tb__ "0|0|
Sd5S43ScaVAInv;VCST;VXGL;A5").

Theorem vec_reserve_rom_sum_ex : ltac2:(tb__ "0|0|
S37S89Q40A1A1S9fS43S8dS43S97VAInv;VCST;VXGL;VKc;Sf8VFB;VFF;A2VFB;VFF;VBX;S95S4fAaS6aVrho0;R1A5SdeS43S8cVrho0;R1SadA5A3Ftp0;").
Proof.
  intros tp0.
  eapply etriple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_complete_JAF segs AInv CST XGL ALA NF Kc rho0 P0 FB FF BX PTrue HKc Phis Phis_reads FUEL_vr cutpcs_vr 100 cutsE exitsE (Q tp0) ejcertAF_ok)
         with (ndT := nd0) (kT := 0%nat) (rv := (100, z0)); [|left; reflexivity].
       intros X ndX kX rv rho tp Hin.
       apply (exits_okT (etriple segs) (fun b _ w => SPfamETA segs (map (enodeIAF AInv CST XGL NF Kc rho0 P0 FB FF BX PTrue Phis) cutsE) b w \/ Q tp0 w)
                (TRe_facts segs) (TRe_ex segs) (TRe_pre segs) (TRe_false segs) (TRe_pureP segs) (@etriple_ex segs) (call_completePA3 segs)) with (tp0 := tp0).
       - intros Phi nd S rho1 tp1 Qa H. exact (etriple_JAF segs AInv CST XGL NF Kc rho0 P0 FB FF BX PTrue Phi nd S rho1 tp1 Qa H).
       - intros Ai rho1 tp1. apply (acx_calloc _ _ _ _ _ ACX); [first [left; reflexivity | right; left; reflexivity | right; right; left; reflexivity] | exact HKc].
       - intros FBc FFc BXc rho1 tp1 HB. apply (RRP.realloc_rom_sum_ex AInv CST XGL ALA HCST HXGL Kc HKc FBc FFc BXc HB rho1 ACX tp1).
       - intros T nd k rv' rho1 tp1 b tp2 HinT HP Hm. apply (ereenter_cutJAF segs AInv CST XGL NF Kc rho0 P0 FB FF BX PTrue Phis cutsE T nd k rv'); [exact HinT | exact HP | exact Hm].
       - intros P nd Phi Psi rho1 tp1 b tp2 HinP HPsi. apply (eexit_postGAF segs AInv CST XGL NF Kc P0 FB FF BX PTrue rho0 tp0 Phi Psi nd Posts_vrr P); [exact HinP | exact HPsi].
       - exact Hin. }
  intros w Hw. apply SPA_JAF_intro; [apply JA_pre_intro; exact Hw|]. intros z Hz. reflexivity.
Qed.
End Existence.

End Sum.

Print Assumptions vec_reserve_rom_sum.
Print Assumptions vec_reserve_rom_sum_ex.
End Lib_vec_reserve_rom_pf.

(* [comment removed for export] *)
Module Lib_finalize_shape_chk.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SVar"; "sprop"; "SPUle"; "SLit"; "SAlu"; "SMd"; "@Corelib.Init.Datatypes"; "cons"; "app"; "bool"; "nil"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "edescA"; "ejcertA"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_finalize_shape"; "NP"; "FUEL_fs"; "cutsE"; "cutsN"; "exitsE"; "exitsN"; "cutpcsN"; "cutsC"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.HideA"; "hideE"; "hide_setE"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "M_MUL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.el.Lib_finalize_shape_chk"; "H_ejcert_fs_ok"; "H_ejcert_nm_ok"; "keep_ejcert_fs_ok"; "keep_ejcert_nm_ok"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR HideA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.HideA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ed.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_vec_reserve Lib_vec_push Lib_vec_finalize.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ei.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Lib_finalize_shape.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import RA.ReallocAddr FSAddr.

Definition keep_ejcert_fs_ok : list sprop := ltac2:(tb__ "0|d|
S6S1S2S0PcA1S3Z800000000000A1M0A2S6S1S2S0P66A1S0P1eA1M1A2S6S1S2S0P72A1S0P73A1M2A2S6S1S2G2S3ZffffffffA1M3A2S6S1S2S0P75A1S0P76A1M4A2S6S1S2G4G3A2S6S1S2S0P78A1S0P79A1M5A2S6S1S2G5G3A2S6S1S2S0P7bA1S0P7cA1M6A2S6S1S2G6G3A2S6S1S2S0P7eA1S0P7fA1M7A2S6S1S2G7G3A2S6S1S2S0P81A1S0P82A1M8A2S6S1S2G8G3A2S6S1S2S0P84A1S0P85A1M9A2S6S1S2G9G3A2S6S1S2S4S1aS0P6eA1MaS5S1bS3Z80A1S0P70A1MbA3McA3G1A2S6S1S2GaG0A2S6S1S2GbG3A2S6S1S2GcG3A2S9S1A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition H_ejcert_fs_ok : list sprop := ltac2:(tb__ "0|0|
S19S1eS7SbS10S12A3A2").
Lemma ejcert_fs_ok : ltac2:(tb__ "0|1|
S16S8ScS17SeSfS15SeSdSbSbS18S1cA1M0S10A4SdSbSbG0S12A4A7SaA3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Definition keep_ejcert_nm_ok : list sprop := ltac2:(tb__ "0|3|
S6S1S2S0P66A1S0P1eA1M0A2M1S6S1S2S0PcA1S3Z800000000000A1M2A2S6S1S2S0P65A1G2A2S6S1G1S6S1S2G0S3Z7fffff800000A1A2S6S1S2S0P72A1S0P73A1A2S6S1S2S0P75A1S0P76A1A2S6S1S2S0P78A1S0P79A1A2S6S1S2S0P7bA1S0P7cA1A2S6S1S2S0P7eA1S0P7fA1A2S6S1S2S0P81A1S0P82A1A2S6S1S2S0P84A1S0P85A1A2S9S1A1A3A3A3A3A3A3A3A3A3A3A3A3").
Definition H_ejcert_nm_ok : list sprop := ltac2:(tb__ "0|0|
S19S1fS7SbS11S13A3A2").
Lemma ejcert_nm_ok : ltac2:(tb__ "0|1|
S16S8ScS17SeSfS14SeSdSbSbS18S1dA1M0S11A4SdSbSbG0S13A4A7SaA3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End Lib_finalize_shape_chk.

