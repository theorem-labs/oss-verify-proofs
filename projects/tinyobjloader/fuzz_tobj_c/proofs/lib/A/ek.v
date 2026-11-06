(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_l_s2 Lib_handle_p eg.

(* [comment removed for export] *)
Module Lib_handle_l_chk0.

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
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_l OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_l_s2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import HLAddr.

Abbreviation TG := (etargets cutsL exitsL).
Abbreviation PE := (eecheckJA NPH (cutsL ++ exitsL)).
Abbreviation CC i T := (cut_okE segs FUEL_hl cutpcs_hl NPH PE i T TG).
End Lib_handle_l_chk0.

(* [comment removed for export] *)
Module Lib_handle_l_eqs.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "sprop"; "SLit"; "ss_facts"; "ss_objs"; "DUnknown"; "SPUle"; "cell"; "DZero"; "mkCell"; "@Corelib.Init.Datatypes"; "cons"; "nil"; "Some"; "option"; "list"; "app"; "prod"; "pair"; "bool"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "axform"; "AXSelect"; "AXSplit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ek.Lib_handle_l_eqs.VN"; "Pre_vr"; "P_grown"; "P_keep"; "P_fail"; "bdP"; "tv0"; "vN"; "tvP"; "vK"; "vKn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs"; "lc_d"; "lc_k"; "hG"; "kb"; "NPH"; "bd_vec"; "hF"; "li_d"; "li_k"; "hFL"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_l"; "pD"; "pK"; "vKg"; "X_hl"; "vDg"; "E_vr"; "s_v"; "reshapeA"; "L_mc1"; "Pre_mc"; "T_sm1"; "optAp"; "C_pro0"; "E_da"; "E_mg"; "E_mg0"; "E_mk"; "E_mk0"; "E_pc"; "R_v"; "T_grown0"; "T_keep0"; "Xk_v"; "xf_mc"; "E_pc0"; "E_pc1"; "E_unp0"; "PHIN"; "T_da0"; "T_pc0"; "T_sm"; "X_pro"; "X_r2g"; "X_r2k"; "dst_obj"; "objs_pc0"; "objs_pro"; "objs_sm1"; "pQ"; "s_mc"; "slot_facts"; "xf_cm"; "C_mg"; "C_mk"; "C_pre"; "C_pro"; "C_rlg"; "C_rlk"; "C_unp"; "E_da0"; "E_sm0"; "E_vr0"; "R_da"; "R_mg"; "R_mk"; "R_pc"; "R_sm"; "T_da"; "T_fail0"; "T_grown"; "T_keep"; "T_mcg"; "T_mck"; "T_pc"; "X_rpg"; "X_rpk"; "mid_dst"; "s_da"; "s_pc"; "s_sm"; "xf_pc"; "xf_tda"; "xf_tpc"; "xf_vr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_subA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bitem"; "bd_subst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_l_s2"; "E_vc"; "s_v2"; "E_da2x"; "E_m2g"; "E_m2g0"; "E_m2k"; "E_m2k0"; "R_v2"; "T_grown2_0"; "T_keep2_0"; "Xk_v2"; "xf_mc2"; "C_epf"; "E_vc0"; "E_vc1"; "T_da2"; "X_ok0"; "dst4_obj"; "lcn1"; "objs_vc0"; "s_mc2"; "sel_rel"; "slot4_facts"; "xf_e8"; "xf_f"; "xf_f2"; "C_ok"; "E_da2"; "R_da2"; "R_m2g"; "R_m2k"; "T_fail2"; "T_grown2"; "T_keep2"; "T_m2g"; "T_m2k"; "X_e8g"; "X_e8k"; "X_f2a"; "X_f2b"; "X_fp0"; "X_fp1"; "X_rlf"; "X_rlo"; "Y_e8g"; "Y_e8k"; "Y_f2a"; "Y_f2b"; "Y_few"; "Y_fp0"; "Y_fp1"; "Z_f7a"; "Z_f7b"; "mid4_dst"; "s_da2"; "xf_tda2"; "xf_vc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_setX"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "import_tv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "T_afterA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "T_afterA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS"; "shadow_release_stateA"; "shobj"; "shadow_reopen_stateA"; "frame_open_stateA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ek.Lib_handle_l_eqs"; "E_mc1"; "E_mc21"; "Y_rpg"; "Y_rpk"; "Z_e8g"; "Z_e8k"; "Z_f2a"; "Z_f2b"; "Z_fp0"; "Z_fp1"; "cm1"; "cm2"; "objs_r2g"; "objs_r2k"; "cells_pro"; "cells_r2g"; "cells_r2k"; "cells_unp"; "cells_vc"; "sel_sm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.Lib_diag_append"; "P_da"; "Pre_da"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve"; "KLG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ResidualA"; "leaf_matches1A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "fs_frame_size"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "AE_A"; "L_stack_malloc"; "Pre_stack_malloc"; "flagbyte_obj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_parse_corner"; "P_ret"; "Pre_pc"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAS ResidualA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ResidualA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double Lib_parse_corner.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_parse_corner OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.Lib_diag_append.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs Lib_handle_l Lib_handle_l_s2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_l OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_l_s2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Import ScanDoubleAddr VRAddr RA.ReallocAddr ParseCornerAddr DiagAppendAddr HLAddr.
Close Scope bv_scope.
Open Scope Z_scope.
Module VN. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_vec_reserveN. End VN.

Lemma T_sm_eq : ltac2:(tb__ "0|1|
S3S0SbdSdfSddZ1M0A2S64S77S6aSdeSddG0A2A5S50A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition sel_sm : list nat := Eval vm_compute in sel_last T_sm 3.
Lemma T_sm1_eq : ltac2:(tb__ "0|0|
S3S12S0A1S19S50SfS1aS1bSd5A1S10S1aA1A3A2S11S0S3cA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_sm1_objs : ltac2:(tb__ "0|1|
S3S13S5A1S9S1S3cA1A1S14S5S57SfS5Se0S30SfScSeS7Z0A1Z1M0S7G0A1A3S10ScA1A3A2S10S5A1A3A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_sm1_X : ltac2:(tb__ "0|1|
S3S13S15S4S4A2M0A1S2S3cA1S14G0S35S2eS2fS27S28A4SfG0S16S4S4S2dS7SdcZ1A1A1A4S10G0A1A3A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma C_pro0_eq : ltac2:(tb__ "0|0|
S3S0Sc1S3cS57S35S2eS2fS27S28A4Pa0SdcZ1A1A5S3eA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma C_pro_eq : ltac2:(tb__ "0|0|
S3S0Sb9S3eSfS15S4S4A2S16S4S4S2dS7Z0A1A4S2S3eA1A3A2S5fA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition cells_pro : list cell := Eval vm_compute in ob_cells sh_pro.
Lemma X_pro_objs : ltac2:(tb__ "0|0|
S3S13S5A1S9S1S51A1A1S14S5S56SfS5SbfS29Z0Z10Sd0SdA5S10S5A1A3A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma C_pre_eq : ltac2:(tb__ "0|0|
S3S0SbeS51S56Pa0S10S15S31S31A2A1A4S5eA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma C_unp_eq : ltac2:(tb__ "0|0|
S3S0Sc0S4cS2S4cA1S29Z4Z6A5S62A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition cells_unp : list cell := Eval vm_compute in ob_cells sh_unp.
Lemma E_pc0_objs : ltac2:(tb__ "0|0|
S3S13S5A1S9S1S4aA1A1S14S5S55SfS5SbfS29Z4Z6Sd3SaA5S10S5A1A3A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_pc1_eq : ltac2:(tb__ "0|1|
S3S0SbeS4aS55Pa0SfS15S31S31A2M0S16S31S31Z20ZcA4S10G0A1A3A4S4bA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_pc_eq : ltac2:(tb__ "0|0|
S3S12S0A1S19S4bS78A2S11S0S44A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_pc0_eq : ltac2:(tb__ "0|0|
S3S0Sd6S8S1S44A1A1S7dS76Se2Se1S44S69A5A2S4fA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_pc_eq : ltac2:(tb__ "0|0|
S3S12S0A1S19S4fS7aA2S11S0S71A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_da_eq : ltac2:(tb__ "0|0|
S3S12S0A1S19S63SfS1aS1cU0S7N60A1A2S10S1aA1A3A2S11S0S3fA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_da0_eq : ltac2:(tb__ "0|0|
S3S0Sd6S8S1S3fA1A1S7dS75Sd8Sd7S3fS66A5A2S4eA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_da_eq : ltac2:(tb__ "0|0|
S3S12S0A1S19S4eS79A2S11S0S6bA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma E_vr_eq : ltac2:(tb__ "0|0|
S3S12S0A1S19S65S7bA2S11S0S37A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_keep0_eq : ltac2:(tb__ "0|0|
S3S0SbcS1dS37S38S45S1fS48A6S47A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_fail0_eq : ltac2:(tb__ "0|0|
S3S0SbcS1dS37S38S45S20S48A6S6cA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_grown0_eq : ltac2:(tb__ "0|0|
S3S0SbcS1dS37S38S45S1eS48A6S46A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_keep_eq : ltac2:(tb__ "0|0|
S3S0SbaS47S14S6S14S6S5aS33A1SfS6SbS7SdbA1S32A2S10S6A1A3A3S8S1S47A1A1A3A2S6eA3"). Proof. reflexivity. Qed.
Lemma T_grown_eq : ltac2:(tb__ "0|0|
S3S0SbaS46S14S6S5aS34A1S8S1S46A1A1A3A2S6dA3"). Proof. reflexivity. Qed.
Lemma imp_keep_tv : ltac2:(tb__ "0|1|
S3S13S15S4S4A2M0A1SbbS7cS38S1dS1fS37A4S22A2SfG0S16S4S4S32S2aZcS33A2A4S10G0A1A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_keep_bd : ltac2:(tb__ "0|0|
S3S13S7eA1S7fS7cS38S1dS1fS37A4S21S23S25A2A2SfS7eS4dS58S33A2SfS7eSd9S33A1S10S7eA1A3A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_fail_tv : ltac2:(tb__ "0|1|
S3S13S15S4S4A2M0A1SbbS7cS38S1dS20S37A4S22A2SfG0S16S4S4S32S2aZcS33A2A4S10G0A1A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_grown_tv : ltac2:(tb__ "0|1|
S3S13S15S4S4A2M0A1SbbS7cS38S1dS1eS37A4S24A2SfG0S16S4S4S36S2aZcS34A2A4S10G0A1A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_grown_bd : ltac2:(tb__ "0|0|
S3S13S7eA1S7fS7cS38S1dS1eS37A4S21S23S26A2A2SfS7eS4dS58S34A2SfS7eSd9S34A1S10S7eA1A3A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition E_mc1 (E0 : axst) : axst := ltac2:(tb__ "0|0|
S3dS19VE0;S49A2A1").
Lemma E_mk1_eq : ltac2:(tb__ "0|0|
S3S12S0A1S19S43S49A2S11S0Sc2S43A1A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_mg1_eq : ltac2:(tb__ "0|0|
S3S12S0A1S19S41S49A2S11S0Sc2S41A1A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_mk_eq : ltac2:(tb__ "0|0|
S3S0S39Sc2S43A1U4S54S32A1A3S42A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_mg_eq : ltac2:(tb__ "0|0|
S3S0S39Sc2S41A1U4S54S36A1A3S40A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_mck_eq : ltac2:(tb__ "0|0|
S3S0SbdS3bS42S59S42S32S33A3S68S3aA5S70A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_mcg_eq : ltac2:(tb__ "0|0|
S3S0SbdS3bS40S59S40S36S34A3S67S3aA5S6fA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition cm1 (A : axst) (d : sv) : axst := ltac2:(tb__ "0|0|
S39VA;U1S74Vd;A1A3").
Definition Y_rpk : axst := Eval vm_compute in optAp (apply_axforms (cm1 X_rpk pD) xf_cm).
Definition Y_rpg : axst := Eval vm_compute in optAp (apply_axforms (cm1 X_rpg vDg) xf_cm).
Lemma Y_rpk_eq : ltac2:(tb__ "0|0|
S3S12S0A1S19SccS73S32A2S5bA2S11S0Sc5A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Y_rpg_eq : ltac2:(tb__ "0|0|
S3S12S0A1S19SccS72S36A2S5bA2S11S0Sc4A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma C_mk_eq : ltac2:(tb__ "0|0|
S3S0Sc0Sc5S35S32S33S27S28A4S29Z4Z6A5S5dA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma C_mg_eq : ltac2:(tb__ "0|0|
S3S0Sc0Sc4S35S36S34S27S28A4S29Z4Z6A5S5cA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition objs_r2k : list sobj := Eval vm_compute in removelast (ss_objs (ax_S X_r2k)).
Definition objs_r2g : list sobj := Eval vm_compute in removelast (ss_objs (ax_S X_r2g)).
Definition cells_r2k : list cell := Eval vm_compute in ob_cells (last (ss_objs (ax_S X_r2k)) O_Wl).
Definition cells_r2g : list cell := Eval vm_compute in ob_cells (last (ss_objs (ax_S X_r2g)) O_Wl).
Lemma X_r2k_objs : ltac2:(tb__ "0|0|
S3S13S5A1S9S1S53A1A1S14S5ScfSfS5SbfS29Z4Z6Sd2SaA5S10S5A1A3A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma X_r2g_objs : ltac2:(tb__ "0|0|
S3S13S5A1S9S1S52A1A1S14S5SceSfS5SbfS29Z4Z6Sd1SaA5S10S5A1A3A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma C_rlk_eq : ltac2:(tb__ "0|0|
S3S0SbeS53ScfPa0S10S15S31S31A2A1A4S61A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma C_rlg_eq : ltac2:(tb__ "0|0|
S3S0SbeS52ScePa0S10S15S31S31A2A1A4S60A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition Z_fp0 : axst := Eval vm_compute in optAp (apply_axforms X_fp0 xf_f).
Definition Z_fp1 : axst := Eval vm_compute in optAp (apply_axforms X_fp1 xf_f).
Lemma Z_fp0_eq : ltac2:(tb__ "0|0|
S3S12S0A1S19Sa8S98A2S11S0ScaA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Z_fp1_eq : ltac2:(tb__ "0|0|
S3S12S0A1S19Sa9S98A2S11S0ScbA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Y_fp0_eq : ltac2:(tb__ "0|0|
S3S0Sb9ScaS35S32S33S27S28A4A2Sb1A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Y_fp1_eq : ltac2:(tb__ "0|0|
S3S0Sb9ScbS35S32S33S27S28A4A2Sb2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma C_fa0_eq : epi_state Y_fp0 = C_fa0. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma C_fa1_eq : epi_state Y_fp1 = C_fa1. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma Z_f7a_eq : epi_state X_f7a = Z_f7a. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Z_f7b_eq : epi_state X_f7b = Z_f7b. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Z_f7a_ent : ltac2:(tb__ "0|0|
S3S17SdaS2bSb3S8cA3S18A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Z_f7b_ent : ltac2:(tb__ "0|0|
S3S17SdaS2bSb4S8cA3S18A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma C_ok_eq : ltac2:(tb__ "0|0|
S3S0Sc0S90S2S90A1S29Z8Z9A5S9aA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_da2x_eq : ltac2:(tb__ "0|0|
S3S12S0A1S19S9bSfS1aS1cU0S7N60A1A2S10S1aA1A3A2S11S0S82A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_da2_eq : ltac2:(tb__ "0|0|
S3S0Sd6S8S1S82A1A1S7dSb6Sd8Sd7S82S9cA5A2S8fA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Y_few_eq : ltac2:(tb__ "0|0|
S3S12S0A1S19S8fSb7A2S11S0Sb0A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma C_few_eq : epi_state Y_few = C_few. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition cells_vc : list cell := Eval vm_compute in ob_cells sh_ok.
Lemma E_vc0_objs : ltac2:(tb__ "0|0|
S3S13S5A1S9S1S8dA1A1S14S5S93SfS5SbfS29Z8Z9Sd4SaA5S10S5A1A3A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_vc1_eq : ltac2:(tb__ "0|1|
S3S0SbeS8dS93Pa0SfS15S31S31A2M0S16S31S31Z40Z4A4S10G0A1A3A4S8eA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_vc_eq : ltac2:(tb__ "0|0|
S3S12S0A1S19S8eSb8A2S11S0S80A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma T_keep2_0_eq : ltac2:(tb__ "0|0|
S3S0SbcS1dS80S81S87S1fS8aA6S89A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_fail2_eq : ltac2:(tb__ "0|0|
S3S0SbcS1dS80S81S87S20S8aA6S9fA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_grown2_0_eq : ltac2:(tb__ "0|0|
S3S0SbcS1dS80S81S87S1eS8aA6S88A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_keep2_eq : ltac2:(tb__ "0|0|
S3S0SbaS89S14S6S14S6S96S28A1SfS6SbS7SdbA1S27A2S10S6A1A3A3S8S1S89A1A1A3A2Sa1A3"). Proof. reflexivity. Qed.
Lemma T_grown2_eq : ltac2:(tb__ "0|0|
S3S0SbaS88S14S6S96S34A1S8S1S88A1A1A3A2Sa0A3"). Proof. reflexivity. Qed.
Lemma imp_keep2_tv : ltac2:(tb__ "0|1|
S3S13S15S4S4A2M0A1SbbS7cS81S1dS1fS80A4S22A2SfG0S16S4S4S27S2aZ4S28A2A4S10G0A1A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_keep2_bd : ltac2:(tb__ "0|0|
S3S13S7eA1S7fS7cS81S1dS1fS80A4S21S23S25A2A2S2cZ4S92S28A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_fail2_tv : ltac2:(tb__ "0|1|
S3S13S15S4S4A2M0A1SbbS7cS81S1dS20S80A4S22A2SfG0S16S4S4S27S2aZ4S28A2A4S10G0A1A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_grown2_tv : ltac2:(tb__ "0|1|
S3S13S15S4S4A2M0A1SbbS7cS81S1dS1eS80A4S24A2SfG0S16S4S4S36S2aZ4S34A2A4S10G0A1A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_grown2_bd : ltac2:(tb__ "0|0|
S3S13S7eA1S7fS7cS81S1dS1eS80A4S21S23S26A2A2S2cZ4S92S34A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition E_mc21 (E0 : axst) : axst := ltac2:(tb__ "0|0|
S3dS19VE0;S8bA2A1").
Lemma E_m2k1_eq : ltac2:(tb__ "0|0|
S3S12S0A1S19S86S8bA2S11S0Sc3S86A1A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_m2g1_eq : ltac2:(tb__ "0|0|
S3S12S0A1S19S84S8bA2S11S0Sc3S84A1A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_m2k_eq : ltac2:(tb__ "0|0|
S3S0S39Sc3S86A1U4S91S27A1A3S85A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_m2g_eq : ltac2:(tb__ "0|0|
S3S0S39Sc3S84A1U4S91S36A1A3S83A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_m2k_eq : ltac2:(tb__ "0|0|
S3S0SbdS3bS85S94S85S27S28A3S9eS3aA5Sa3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_m2g_eq : ltac2:(tb__ "0|0|
S3S0SbdS3bS83S94S83S36S34A3S9dS3aA5Sa2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition cm2 (A : axst) (d2 : sv) : axst := ltac2:(tb__ "0|0|
S39VA;U1Sb5Vd2;A1A3").
Definition Z_e8k : axst := Eval vm_compute in optAp (apply_axforms (cm2 X_e8k lc_d) xf_e8).
Definition Z_e8g : axst := Eval vm_compute in optAp (apply_axforms (cm2 X_e8g vDg) xf_e8).
Lemma Z_e8k_eq : ltac2:(tb__ "0|0|
S3S12S0A1S19ScdSa5S27A2S97A2S11S0Sc7A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Z_e8g_eq : ltac2:(tb__ "0|0|
S3S12S0A1S19ScdSa4S36A2S97A2S11S0Sc6A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Y_e8k_eq : ltac2:(tb__ "0|0|
S3S0Sb9Sc7S35S32S33S27S28A4A2SadA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Y_e8g_eq : ltac2:(tb__ "0|0|
S3S0Sb9Sc6S35S32S33S36S34A4A2SacA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma C_e8k_eq : epi_state Y_e8k = C_e8k. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma C_e8g_eq : epi_state Y_e8g = C_e8g. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition Z_f2a : axst := Eval vm_compute in optAp (apply_axforms X_f2a xf_f2).
Definition Z_f2b : axst := Eval vm_compute in optAp (apply_axforms X_f2b xf_f2).
Lemma Z_f2a_eq : ltac2:(tb__ "0|0|
S3S12S0A1S19Sa6S99A2S11S0Sc8A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Z_f2b_eq : ltac2:(tb__ "0|0|
S3S12S0A1S19Sa7S99A2S11S0Sc9A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Y_f2a_eq : ltac2:(tb__ "0|0|
S3S0Sb9Sc8S35S32S33S27S28A4A2SaeA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Y_f2b_eq : ltac2:(tb__ "0|0|
S3S0Sb9Sc9S35S32S33S27S28A4A2SafA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma C_f2a_eq : epi_state Y_f2a = C_f2a. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma C_f2b_eq : epi_state Y_f2b = C_f2b. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma X_rlo_eq : ltac2:(tb__ "0|1|
S3S12S0A1S19SabSfS1aS1bS95A1S10S1aA1A3A2M0S11S0S3dG0A1A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma X_rlf_eq : ltac2:(tb__ "0|1|
S3S12S0A1S19SaaSfS1aS1bS95A1S10S1aA1A3A2M0S11S0S3dG0A1A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
End Lib_handle_l_eqs.

(* [comment removed for export] *)
Module Lib_handle_p_eqs.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Init.Datatypes"; "cons"; "nil"; "Some"; "option"; "list"; "app"; "prod"; "pair"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "apply_axforms"; "AXSelect"; "AXMerge"; "AXUnbase"; "AXRebase"; "AXSplit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "SLit"; "sprop"; "ss_objs"; "ss_facts"; "DUnknown"; "cell"; "DZero"; "SPUle"; "mkCell"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_p"; "pD"; "pK"; "E_vr"; "s_v"; "X_hp"; "vKg"; "T_sm1"; "optAp"; "vDg"; "C_pro0"; "E_da"; "E_mg"; "E_mg0"; "E_mk"; "E_mk0"; "E_pc"; "R_v"; "T_grown0"; "T_keep0"; "Xk_v"; "epi_state"; "reshapeA"; "sel_rel"; "xf_mc"; "E_pc0"; "E_pc1"; "E_unp0"; "L_mc1"; "PHIN"; "Pre_mc"; "T_da0"; "T_pc0"; "T_sm"; "X_pro"; "X_r2g"; "X_r2k"; "Y_fp0"; "Y_fp1"; "dst_obj"; "objs_pc0"; "objs_pro"; "objs_sm1"; "pQ"; "s_mc"; "slot_facts"; "tvL"; "C_epn"; "C_fp0"; "C_fp1"; "C_mg"; "C_mk"; "C_pre"; "C_pro"; "C_rlg"; "C_rlk"; "C_unp"; "E_da0"; "E_sm0"; "E_vr0"; "R_da"; "R_mg"; "R_mk"; "R_pc"; "R_sm"; "T_da"; "T_fail0"; "T_grown"; "T_keep"; "T_mcg"; "T_mck"; "T_pc"; "XN"; "X_fp0"; "X_fp1"; "X_rlf0"; "X_rlf1"; "X_rln"; "X_rpg"; "X_rpk"; "mid_dst"; "s_da"; "s_pc"; "s_sm"; "sel_body"; "sel_f"; "tvG"; "xf_pc"; "xf_tda"; "xf_tpc"; "xf_vr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_p.VN"; "Pre_vr"; "P_grown"; "P_keep"; "P_fail"; "bdP"; "tv0"; "vN"; "tvP"; "vK"; "vKn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bitem"; "bd_subst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs"; "hG"; "hF"; "pi_d"; "pi_k"; "hFL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_subA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ek.Lib_handle_p_eqs"; "E_mc1"; "Y_rpg"; "Y_rpk"; "Z_fp0"; "Z_fp1"; "cm1"; "objs_r2g"; "objs_r2k"; "xf_cm"; "xf_f"; "cells_pro"; "cells_r2g"; "cells_r2k"; "cells_unp"; "sel_sm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS"; "shadow_release_stateA"; "shobj"; "shadow_reopen_stateA"; "frame_open_stateA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_setX"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "import_tv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "T_afterA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "T_afterA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve"; "KLG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "fs_frame_size"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "AE_A"; "L_stack_malloc"; "Pre_stack_malloc"; "flagbyte_obj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.Lib_diag_append"; "P_da"; "Pre_da"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_parse_corner"; "P_ret"; "Pre_pc"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAS ResidualA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ResidualA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double Lib_parse_corner.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_parse_corner OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.Lib_diag_append.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs Lib_handle_p.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_p.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Import ScanDoubleAddr VRAddr RA.ReallocAddr ParseCornerAddr DiagAppendAddr HPAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma T_sm_eq : ltac2:(tb__ "0|1|
S3S0Sa3SaaSa8Z0M0A2S58S71S5eSa9Sa8G0A2A5S3fA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition sel_sm : list nat := Eval vm_compute in sel_last T_sm 3.
Lemma T_sm1_eq : ltac2:(tb__ "0|0|
S3S7S0A1SdS3fS4ScSeS9aA1S5ScA1A3A2S6S0S25A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_sm1_objs : ltac2:(tb__ "0|1|
S3S8S13A1S17S1S25A1A1S9S13S48S4S13SabS89S4S1aS1dS15Z0A1Z1M0S15G0A1A3S5S1aA1A3A2S5S13A1A3A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_sm1_X : ltac2:(tb__ "0|1|
S3S8SaS14S14A2M0A1S2S25A1S9G0S23S87S88A2S4G0SbS14S14S86S15Sa6Z0A1A1A4S5G0A1A3A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma C_pro0_eq : ltac2:(tb__ "0|0|
S3S0S9eS25S48S23S87S88A2Pa0Sa6Z0A1A5S28A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma C_pro_eq : ltac2:(tb__ "0|0|
S3S0S9fS28S4SaS14S14A2SbS14S14S86S15Z0A1A4S2S28A1A3A2S53A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition cells_pro : list cell := Eval vm_compute in ob_cells sh_pro.
Lemma X_pro_objs : ltac2:(tb__ "0|0|
S3S8S13A1S17S1S40A1A1S9S13S47S4S13S9cS85Z0Z8S96S1bA5S5S13A1A3A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma C_pre_eq : ltac2:(tb__ "0|0|
S3S0S9bS40S47Pa0S5SaS1eS1eA2A1A4S52A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma C_unp_eq : ltac2:(tb__ "0|0|
S3S0S9dS39S2S39A1S85Z4Z6A5S56A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition cells_unp : list cell := Eval vm_compute in ob_cells sh_unp.
Lemma E_pc0_objs : ltac2:(tb__ "0|0|
S3S8S13A1S17S1S37A1A1S9S13S46S4S13S9cS85Z4Z6S99S19A5S5S13A1A3A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_pc1_eq : ltac2:(tb__ "0|1|
S3S0S9bS37S46Pa0S4SaS1eS1eA2M0SbS1eS1eZ20ZcA4S5G0A1A3A4S38A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_pc_eq : ltac2:(tb__ "0|0|
S3S7S0A1SdS38S75A2S6S0S2eA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_pc0_eq : ltac2:(tb__ "0|0|
S3S0Sa5S18S1S2eA1A1S8bS70SafSaeS2eS5dA5A2S3eA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_pc_eq : ltac2:(tb__ "0|0|
S3S7S0A1SdS3eS77A2S6S0S65A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_da_eq : ltac2:(tb__ "0|0|
S3S7S0A1SdS57S4ScS12U0S15N60A1A2S5ScA1A3A2S6S0S29A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_da0_eq : ltac2:(tb__ "0|0|
S3S0Sa5S18S1S29A1A1S8bS6fSadSacS29S5aA5A2S3dA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_da_eq : ltac2:(tb__ "0|0|
S3S7S0A1SdS3dS76A2S6S0S5fA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma E_vr_eq : ltac2:(tb__ "0|0|
S3S7S0A1SdS59S78A2S6S0S21A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma T_keep0_eq : ltac2:(tb__ "0|0|
S3S0Sa2S79S21S22S2fS7bS32A6S31A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_fail0_eq : ltac2:(tb__ "0|0|
S3S0Sa2S79S21S22S2fS7cS32A6S60A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_grown0_eq : ltac2:(tb__ "0|0|
S3S0Sa2S79S21S22S2fS7aS32A6S30A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_keep_eq : ltac2:(tb__ "0|0|
S3S0Sa0S31S9S16S9S16S4bS20A1S4S16S1cS15Sa7A1S1fA2S5S16A1A3A3S18S1S31A1A1A3A2S62A3"). Proof. reflexivity. Qed.
Lemma T_grown_eq : ltac2:(tb__ "0|0|
S3S0Sa0S30S9S16S4bS24A1S18S1S30A1A1A3A2S61A3"). Proof. reflexivity. Qed.
Lemma imp_keep_tv : ltac2:(tb__ "0|0|
S3S8SaS14S14A2A1Sa1S8aS22S79S7bS21A4S7eA2S4cA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_keep_bd : ltac2:(tb__ "0|0|
S3S8S83A1S84S8aS22S79S7bS21A4S7dS7fS81A2A2S4S83S3bS49S20A2S4S83Sa4S20A1S5S83A1A3A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_fail_tv : ltac2:(tb__ "0|0|
S3S8SaS14S14A2A1Sa1S8aS22S79S7cS21A4S7eA2S4cA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_grown_tv : ltac2:(tb__ "0|0|
S3S8SaS14S14A2A1Sa1S8aS22S79S7aS21A4S80A2S74A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_grown_bd : ltac2:(tb__ "0|0|
S3S8S83A1S84S8aS22S79S7aS21A4S7dS7fS82A2A2S4S83S3bS49S24A2S4S83Sa4S24A1S5S83A1A3A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition E_mc1 (E0 : axst) : axst := ltac2:(tb__ "0|0|
S26SdVE0;S36A2A1").
Lemma E_mk1_eq : ltac2:(tb__ "0|0|
S3S7S0A1SdS2dS36A2S6S0S8cS2dA1A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_mg1_eq : ltac2:(tb__ "0|0|
S3S7S0A1SdS2bS36A2S6S0S8cS2bA1A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_mk_eq : ltac2:(tb__ "0|0|
S3S0S34S8cS2dA1U4S45S1fA1A3S2cA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_mg_eq : ltac2:(tb__ "0|0|
S3S0S34S8cS2bA1U4S45S27A1A3S2aA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_mck_eq : ltac2:(tb__ "0|0|
S3S0Sa3S3cS2cS4aS2cS1fS20A3S5cS3aA5S64A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_mcg_eq : ltac2:(tb__ "0|0|
S3S0Sa3S3cS2aS4aS2aS27S24A3S5bS3aA5S63A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition cm1 (A : axst) (d : sv) : axst := ltac2:(tb__ "0|0|
S34VA;U1S6eVd;A1A3").
Definition xf_cm : list axform := ltac2:(tb__ "0|2|
S4ScS11U2A1S4ScS10U5N2b0A2S4ScSeS72A1S4ScSfU1A1M0S4ScG0S4ScSfU13A1M1S4ScG1S5ScA1A3A3A3A3A3A3A3").
Definition Y_rpk : axst := Eval vm_compute in optAp (apply_axforms (cm1 X_rpk pD) xf_cm).
Definition Y_rpg : axst := Eval vm_compute in optAp (apply_axforms (cm1 X_rpg vDg) xf_cm).
Lemma Y_rpk_eq : ltac2:(tb__ "0|0|
S3S7S0A1SdS91S6dS1fA2S94A2S6S0S8eA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Y_rpg_eq : ltac2:(tb__ "0|0|
S3S7S0A1SdS91S6cS27A2S94A2S6S0S8dA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma C_mk_eq : ltac2:(tb__ "0|0|
S3S0S9dS8eS23S1fS20A2S85Z4Z6A5S51A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma C_mg_eq : ltac2:(tb__ "0|0|
S3S0S9dS8dS23S27S24A2S85Z4Z6A5S50A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition objs_r2k : list sobj := Eval vm_compute in removelast (ss_objs (ax_S X_r2k)).
Definition objs_r2g : list sobj := Eval vm_compute in removelast (ss_objs (ax_S X_r2g)).
Definition cells_r2k : list cell := Eval vm_compute in ob_cells (last (ss_objs (ax_S X_r2k)) O_Wp).
Definition cells_r2g : list cell := Eval vm_compute in ob_cells (last (ss_objs (ax_S X_r2g)) O_Wp).
Lemma X_r2k_objs : ltac2:(tb__ "0|0|
S3S8S13A1S17S1S42A1A1S9S13S93S4S13S9cS85Z4Z6S98S19A5S5S13A1A3A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma X_r2g_objs : ltac2:(tb__ "0|0|
S3S8S13A1S17S1S41A1A1S9S13S92S4S13S9cS85Z4Z6S97S19A5S5S13A1A3A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma C_rlk_eq : ltac2:(tb__ "0|0|
S3S0S9bS42S93Pa0S5SaS1eS1eA2A1A4S55A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma C_rlg_eq : ltac2:(tb__ "0|0|
S3S0S9bS41S92Pa0S5SaS1eS1eA2A1A4S54A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma C_epn_eq : ltac2:(tb__ "0|0|
S3S0S33S66S1fS20A3S4dA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition xf_f : list axform := ltac2:(tb__ "0|2|
S4ScS10U1M0Z40A2S4ScS10U2N2b0A2S4ScSeS73A1S4ScSfU0A1S4ScSfG0A1M1S4ScG1S5ScA1A3A3A3A3A3A3").
Definition Z_fp0 : axst := Eval vm_compute in optAp (apply_axforms X_fp0 xf_f).
Definition Z_fp1 : axst := Eval vm_compute in optAp (apply_axforms X_fp1 xf_f).
Lemma Z_fp0_eq : ltac2:(tb__ "0|0|
S3S7S0A1SdS67S95A2S6S0S8fA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Z_fp1_eq : ltac2:(tb__ "0|0|
S3S7S0A1SdS68S95A2S6S0S90A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Y_fp0_eq : ltac2:(tb__ "0|0|
S3S0S9fS8fS23S1fS20A2A2S43A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Y_fp1_eq : ltac2:(tb__ "0|0|
S3S0S9fS90S23S1fS20A2A2S44A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma C_fp0_eq : ltac2:(tb__ "0|0|
S3S0S33S43S1fS20A3S4eA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma C_fp1_eq : ltac2:(tb__ "0|0|
S3S0S33S44S1fS20A3S4fA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma X_rln_eq : ltac2:(tb__ "0|1|
S3S7S0A1SdS6bS4ScSeS35A1S5ScA1A3A2M0S6S0S26G0A1A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma X_rlf0_eq : ltac2:(tb__ "0|1|
S3S7S0A1SdS69S4ScSeS35A1S5ScA1A3A2M0S6S0S26G0A1A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma X_rlf1_eq : ltac2:(tb__ "0|1|
S3S7S0A1SdS6aS4ScSeS35A1S5ScA1A3A2M0S6S0S26G0A1A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
End Lib_handle_p_eqs.

(* [comment removed for export] *)
Module Lib_handle_p_chk.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs"; "NPH"; "@Corelib.Init.Datatypes"; "bool"; "true"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_p"; "FUEL_hp"; "cutpcs_hp"; "cutsH"; "exitsH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ejcertA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG SymSummary.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import BudA TobjJA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs Lib_handle_p.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_p.
Import ListNotations.
Open Scope Z_scope.

Lemma ejcertH_ok : ltac2:(tb__ "0|0|
S3S1S9S4S0S5S6S0S7S8A7S2A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End Lib_handle_p_chk.

(* [comment removed for export] *)
Module Lib_handle_p_pf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "or"; "True"; "ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "ax_X"; "g8"; "has_facts"; "la_state"; "ax_base"; "ax_setS"; "mkLeafA"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "valuation"; "sprop"; "ss_facts"; "ss_next"; "sobj"; "SLit"; "SPUle"; "ss_objs"; "holds"; "sprop_eqb"; "eval"; "SPEq"; "SVar"; "sv_below"; "swf"; "SAlu"; "sprop_below"; "agree_below"; "cell"; "DUnknown"; "mkObj"; "obj_range"; "obj_wf"; "soff"; "dflt_writable"; "odefault"; "@Corelib.Init.Datatypes"; "list"; "prod"; "pair"; "bool"; "true"; "cons"; "nil"; "nat"; "Some"; "option"; "None"; "fst"; "andb"; "snd"; "app"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "emeasA"; "ANone"; "NDA"; "PTrue"; "nd_below"; "TPA"; "frinA"; "tvinA"; "JA_pre"; "fbinA"; "ffinA"; "JA"; "JLA"; "frozen"; "nodeIA"; "ok_frameKA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "smatchA"; "stableA"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "pow"; "mul"; "add"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_p"; "fr_hp"; "pQ"; "VR"; "ndJ"; "cutsH"; "X_hp"; "ndG"; "ndX"; "L_mc1"; "Pre_mc"; "epi_state"; "pC"; "z0"; "cmul12"; "nd0"; "pD"; "pK"; "tvL"; "E_da0"; "E_mg0"; "E_mk0"; "E_pc0"; "E_unp0"; "E_vr0"; "P_fail"; "P_ok"; "Pre_hp"; "R_v"; "X_r2g"; "X_r2k"; "X_rpg"; "X_rpk"; "dst_obj"; "ndN"; "nd_fail"; "nd_ok"; "E_sm0"; "E_vr"; "L_sm"; "PD_vr"; "Pre_sm"; "XN"; "X_fp0"; "X_fp1"; "X_pro"; "X_rlf0"; "X_rlf1"; "X_rln"; "Xk_v"; "exitsH"; "mid_dst"; "ndP"; "pC1"; "reshapeA"; "s_v"; "sel_rel"; "slot_facts"; "xf_mc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs"; "NPH"; "hG"; "hF"; "tE"; "tL"; "kb"; "tB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ek.Lib_handle_p_pf"; "P0_hp"; "vrF"; "P0_hp_b"; "bF"; "DW_rng"; "fF"; "@Stdlib.Lists.List"; "In"; "existsb"; "forallb"; "nth_error"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "uval"; "bitem"; "bd_wpos"; "BXok_d"; "bd_below"; "bxt"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "firstn"; "skipn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "entails_frA"; "call_checkA"; "import_postA"; "call_checkPA"; "J_ofPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_p.HPAddr"; "DW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eg.Lib_builderH_pf"; "extraOH"; "extraXH"; "extraOH_client"; "frozen_stableH"; "payA_sameH"; "siteFH"; "siteHH"; "sitePH"; "siteXH"; "site_pureH"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "call_linkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_geom"; "topG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "rho_absorb"; "rho_sub";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS"; "robjs_checkF"; "xrs_checkL"; "shadow_reopen_stateA"; "release_objs_ok"; "shadow_release_stateA"; "shobj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ek.Lib_handle_p_pf.Sum"; "HNPH"; "Posts_hpJ"; "JLh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "tvz"; "T_ok"; "tvd"; "FBx"; "remove_nth"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eh.Lib_builder_pf"; "baseF"; "P0_builder"; "basez"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve"; "B32"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "axform"; "AXSelect"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "SHADOW_OFF"; "IMG_HI"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "jnodeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "xrs_inclb"; "FFx"; "pclMA"; "PostsC"; "robjs_okF"; "xrs_okF"; "xrs_okL"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.Lib_diag_append"; "Pre_da"; "Posts_da"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ek.Lib_handle_p_pf.VNP"; "P0_vr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_parse_corner"; "Pre_pc"; "Posts_pc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAT"; "robjs_checkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA"; "infrFF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "ccount"; "T_afterA"; "call_checkTA"; "is_shadowZ"; "payA"; "robjs_okA"; "site_okA"; "xrs_okA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "AE_A"; "JL_pure"; "JL_stack_malloc"; "J_memcpy_pre"; "J_stack_malloc_pre"; "alloc_contractsA"; "alloc_contractsA_ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs"; "vAL"; "vb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_p.VN"; "Pre_vr"; "nd0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ek.Lib_handle_p_eqs"; "cm1"; "xf_cm"; "xf_f"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ek.Lib_handle_p_pf.Sum.X"; "pure_rule"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double"; "two26"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsSymJump"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_setX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3"; "import_okPA3"; "import_postA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR"; "robjs_okF"; "xrs_ok47"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAT.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAM2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAT.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double Lib_parse_corner.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_parse_corner OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.Lib_diag_append.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eg.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_p.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eb.Lib_vec_reserve_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eh.Lib_builder_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eg.Lib_builderH_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_p OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ek.Lib_handle_p_eqs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ek.Lib_handle_p_chk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Module VNP. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Lib_vec_reserveN_pf. End VNP.
Import ScanDoubleAddr VRAddr RA.ReallocAddr ParseCornerAddr DiagAppendAddr HPAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Definition P0_hp (CST : list (Z * Z)) (FB : list (Z * Z)) (FF : list (Z * Z * Z)) (r : valuation) : Prop := ltac2:(tb__ "0|1|
S1Se0VCST;VFB;VFF;Vr;A4S0S34SfdZ0SabS2eS2eS10S10A2M0S10A2G0S38G0S10A2VFF;A4A2U0A3A2").
Lemma P0_hp_b : ltac2:(tb__ "0|2|
S2dS2eS10S10A2M0A1M1G1S2dS2eG0S10A2A1S13S9aR4R3R2R1A4Se0R5R4R3R2A4F_;Fr;FFF;FFB;FCST;").
Proof. intros CST FB FF r [H _]. exact H. Qed.

Definition bF (F : list sprop) : bool := baseF DW F.
Definition fF (F : list sprop) : bool := frameF hG 160 64 F.
Lemma DW_rng : 0 <= DW < 2 ^ 40. Proof. unfold DW. lia. Qed.
Lemma sz_rng : 0 <= 64 < 2 ^ 40. Proof. lia. Qed.

Definition vrF (q : sv) (F : list sprop) : bool := ltac2:(tb__ "0|0|
S39S39Sa1S14S1cS19Vq;S96A2A1VF;A3Sa1S14S1cS19S96S97A2A1VF;A3A2Sa1S14S1cS19S97S18S115A1A2A1VF;A3A2").
Lemma VR_val : ltac2:(tb__ "0|3|
S13S2dS14A1S12S10SaaS14S1bR4A1R3A3S0S30S9bR3R4A2S31A3S1S53Z0M0R3A2S54R3Z40M1A2A2S1S0S10Sa4R7S5bR5R4A2A2S57S56G1S58Sa4R7S96A2Sa4R7R5A2A2M2A2R4A2A3S1S53G0G2A2S53G2S55Z2Z1aA2A2A2A2F_;F_;F_;Fa;Fq;FF;Frho;").
Proof.
  intros rho F q a HF HV Ha. unfold vrF in HV. apply andb_prop in HV as [HV H3]. apply andb_prop in HV as [H1 H2].
  pose proof (holds_mem _ _ _ HF H1) as F1. pose proof (holds_mem _ _ _ HF H2) as F2. pose proof (holds_mem _ _ _ HF H3) as F3.
  rewrite h_ule in F1, F2, F3. unfold two26 in F3. rewrite uval_lit in F3 by lia.
  pose proof (uval_range rho q) as Rq. pose proof (uval_range rho tE) as RE.
  assert (ES : uval rho (SAlu ALU_SUB tE q) = uval rho tE - uval rho q).
  { destruct (U_sub_q rho tE q) as [k Hk]. unfold U in Hk. unfold uval in *.
    pose proof (bv_urange (eval rho (SAlu ALU_SUB tE q))) as R. change (bv_modulus 64) with (2 ^ 64) in R. nia. }
  assert (EM : uval rho (kb 64 (SAlu ALU_SUB tE q)) = 64 * (uval rho tE - uval rho q)).
  { unfold kb. rewrite uval_mul_lit by lia. rewrite ES. reflexivity. }
  unfold VR. rewrite uval_add_litZ by (rewrite ?EM; lia). rewrite EM. lia.
Qed.
Lemma VR_meas : ltac2:(tb__ "0|3|
S13S13S2dS14A1S12S10S10SaaS14S1bR6A1R4A3S0S30S9bR4R5A2S31A3S0S4eQ40A1M0S1dR7S96A2S1dR8S96A2A3S0G0S1dR8R6A2S1dR9R6A2A3S53Z0M1R6A2S54R7R6A2S54R7Z40A2S1S53G1Sa4RcS5bRaR9A2A2M2A2S54G2Sa4RdS5bRaR8A2A2A2A2F_;F_;F_;F_;F_;F_;F_;Fb;Fa;Fq;FF;Frho';Frho;").
Proof.
  intros rho rho' F q a b HF HV H1 H2 Ha Hab Hb.
  assert (EQ : uval rho' (VR q a) = uval rho (VR q a)).
  { unfold uval, VR, kb. cbn [eval]. rewrite H1, H2. reflexivity. }
  rewrite EQ. destruct (VR_val rho F q a HF HV ltac:(lia)) as [-> R1]. destruct (VR_val rho F q b HF HV ltac:(lia)) as [-> _]. lia.
Qed.

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
Sc8S13S2dS4eQ40A1A1Sc4OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : alloc_lawsA segs AInv CST.
Hypothesis HCST : ltac2:(tb__ "0|0|
S10S10cVCST;R1A2S1S53Z0R2A2S54R2Se7A2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S10S10cVXGL;R1A2S1S53Z0R2A2S54R2Se7A2A2F_;Fa;").
Hypothesis LFLAG : law_flag_stmt AInv.
Hypothesis LFSH : law_fshadow_stmt AInv.
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S2dS2eS2eS10S10A2S10A2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 5 BX.
Let HNP : NP_okA NF := NP_okA_intro NF eq_refl.
Variable rho0 : valuation.
Let HTOP : InitState.segs_top segs <= IMG_HI := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eb.Lib_arena_alloc.HTOP_ok.
Lemma HNPH : (NF <= NPH)%positive. Proof. unfold NF, NPH. lia. Qed.

Definition JLh (nd : ndesc) : jpostA := ltac2:(tb__ "0|0|
S49VAInv;VCST;VXGL;VKc;S9aVCST;VFB;VFF;A3VFB;VFF;VBX;S40Vnd;Aa").
Definition Posts_hpJ : list (axst * jpostA) := ltac2:(tb__ "0|1|
S32S2eS6SaeA2M0S2fS6SaeS71Sd6S7bA1A4S32G0S2fS6SaeS72Sd6S7cA1A4S33G0A1A3A3").
Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S48VAInv;VCST;VXGL;S93VKc;Vrho0;S9aVCST;VFB;VFF;A3VFB;VFF;VBX;S40Vnd;Ac").
Let nI : ltac2:(tb__ "0|0|
S2eS6S3cA2SebFn;") := ltac2:(tb__ "0|0|
S4bVAInv;VCST;VXGL;S93VKc;Vrho0;S9aVCST;VFB;VFF;A3VFB;VFF;VBX;S40Ab").
Let Q (tp0 : list word) : assn := ltac2:(tb__ "0|0|
SafS4dS93Vrho0;Vtp0;Sd5A5").

Let siteP : ltac2:(tb__ "0|0|
Sc8S13S2dS14A1S2dS2eS12S12A2A1S2dS2eS2eS12S10A2S12A2A1S36S34A1S2dS17A1S13S2dS4eQ40A1A1Sc4VAInv;RaR3R2R1A4SaaS14S1bRaA1R9A3S0S30SdfSb5RaA2S31A3Sc6S93Vrho0;RcA3S9aVCST;VFB;VFF;Vrho0;A4S42Vrho0;RfA2Sd9RfScaSc9R10A1A1A2S46VFB;R11A2S47VFF;R12A2S44VFB;R13R12R10A4SdaR13R11A2Sd8R14R12A2S43VFF;R16R15R12A4S0S30SfbR15R14R13R12SbaR11A6S31A3S102VCST;R18S37S10A1R17R12A5F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FR;Fskip;Ffr;Ftv;Ffacts;Frho;FAi;") := ltac2:(tb__ "0|0|
Sc1VAInv;VCST;VALA;S93Sd4VFB;VFF;Vrho0;S9aVCST;VFB;VFF;A3S9cVCST;VFB;VFF;A3Sb5S9eAc").
Let siteF : ltac2:(tb__ "0|0|
Sc8S13S2dS14A1S2dS2eS12S12A2A1S2dS2eS2eS12S10A2S12A2A1S2dS17A1S13S2dS4eQ40A1A1Sc4VAInv;R9R3R2R1A4SaaS14S1bR9A1R8A3S0S30SdfSb5R9A2S31A3Sc6S93Vrho0;RbA3S9aVCST;VFB;VFF;Vrho0;A4S42Vrho0;ReA2Sd9ReScaSc9RfA1A1A2S44VFB;R10RfRdA4SdaR10ReA2Sd8R11RfA2S43VFF;R13R12RfA4S0S30SceR12R11R10S37S34A1SbaRfA6S31A3S11bVCST;Vrho0;VFB;VFF;R14R12R11R10A8F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FR;Ffr;Ftv;Ffacts;Frho;FAi;") := ltac2:(tb__ "0|0|
SbfVAInv;VCST;VALA;S93Sd4VFB;VFF;Vrho0;S9aVCST;VFB;VFF;A3S9cVCST;VFB;VFF;A3Sb5S9eAc").
Let siteH : ltac2:(tb__ "0|1|
Sc8S13S2dS14A1S2dS2eS12S12A2A1S2dS2eS2eS12S10A2S12A2A1S2dS17A1S13S2dS4eQ40A1A1Sc4VAInv;R9R3R2R1A4SaaS14S1bR9A1R8A3S0S30SdfSb5R9A2S31A3Sc6S93Vrho0;RbA3S9aVCST;VFB;VFF;Vrho0;A4S42Vrho0;ReA2Sd9ReScaSc9RfA1A1A2S44VFB;R10RfRdA4SdaR10ReA2Sd8R11RfA2S43VFF;R13R12RfA4S0S30SceR12R11R10S37S34A1SbaRfA6S31A3S17S10Sa0S17R2R12A3S1S53S38S10S10S28R17R3A2M0A3R2A2S54R2S3aS10S10G0A3A2A2S3SeeVCST;Vrho0;SdbVFB;R18R16A3SedVFF;R18R15A3R3A5S3S1S53Z0R3A2S54R3Se7A2A2S100R3A1A2A2F_;F_;Fa;Fo;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FR;Ffr;Ftv;Ffacts;Frho;FAi;") := ltac2:(tb__ "0|0|
Sc0VAInv;VCST;VALA;S93Sd4VFB;VFF;Vrho0;S9aVCST;VFB;VFF;A3S9cVCST;VFB;VFF;A3Sb5S9eAc").
Let siteX : ltac2:(tb__ "0|4|
Sc8S13S2dS14A1S2dS2eS12S12A2A1M0S2dS2eS2eS12S10A2S12A2M1A1M2S36S34A1M3S2dS17A1G0S13S2dS4eQ40A1A1Sc4VAInv;RbR3R2R1A4SaaS14S1bRbA1RaA3S0S30SdfSb5RbA2S31A3Sc6S93Vrho0;RdA3S9aVCST;VFB;VFF;Vrho0;A4S42Vrho0;R10A2Sd9R10ScaSc9R11A1A1A2S46VFB;R12A2S47VFF;R13A2S44VFB;R14R13R11A4SdaR14R12A2Sd8R15R13A2S43VFF;R17R16R13A4S0S30ScfVXGL;R16R15R14R13R12SbbR11A8S31A3S1Sf2VCST;VXGL;Vrho0;VFB;VFF;R18R16G3G2Lskip;R14S34SdcG1R1R16A3Li;R15X36x2R12A9S1S104VCST;VXGL;R19S37S10A1R18R12A6S11cR18R12A2A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FX;Fobjs;Fskip;Ffr;Ftv;Ffacts;Frho;FAi;") := ltac2:(tb__ "0|0|
Sc2VAInv;VCST;VXGL;VALA;VHCST;VHXGL;S93Sd4VFB;VFF;Vrho0;S9aVCST;VFB;VFF;A3S9cVCST;VFB;VFF;A3Sb5S9eAf").
Let site_pure : ltac2:(tb__ "0|2|
S6ScbS2dS17A1S13S2dS2eS12S12A2A1S2dS2eS2eS12S10A2S12A2A1S2dSa5A1S0S30SdfSb5S15S7R7A1A1A2S31A3S0S30SfbS15S7R8A1A1R4R3S37S34A1M0SbaR6A6S31A3S0S30ScfVXGL;S15S7R9A1M1A1R5R4G0S1aG1A1SbbS9R9A1A8S31A3S103VAInv;VCST;VXGL;S93Vrho0;S9aVCST;VFB;VFF;A3VFB;VFF;RaR9R8R7S3fR6R5R4S3eA4S37S10A1Sc8SddS4L_;L_;AfF_;F_;F_;Fbd;Ffr;Ftv;Frho;FR;Fs;FE;") := ltac2:(tb__ "0|0|
Sc3VAInv;VCST;VXGL;VALA;VHCST;VHXGL;S93Sd4VFB;VFF;Vrho0;S9aVCST;VFB;VFF;A3S9cVCST;VFB;VFF;A3Sb5S9eAf").
Let payA_same : ltac2:(tb__ "0|1|
S2dS14A1S2dSa5A1S0S30Sa6R1A1S31A3S101S93Vrho0;S9aVCST;VFB;VFF;A3R3S18Z0M0A1G0R2R2A8F_;Fbd;Ffacts;") := ltac2:(tb__ "0|0|
SbeS93Vrho0;S9aVCST;VFB;VFF;A3A3").
Let frozen_stable : ltac2:(tb__ "0|0|
S11S11S3cS13Se9S93R3A2S0S30S41R4R3A2S31A3S52S4dR6S4aVAInv;VCST;VXGL;S93VKc;Vrho0;S9aVCST;VFB;VFF;A3VFB;VFF;VBX;S40R4R3AdA3F_;F_;Frho;Fnd;Fm;Fn;") := ltac2:(tb__ "0|0|
SbdVAInv;VCST;VXGL;VALA;S93VKc;VHKc;VFB;VFF;VBX;Vrho0;S9aVCST;VFB;VFF;A3Ac").
Let extra_client : ltac2:(tb__ "0|1|
S13S17S10S2dS2eS12S12A2A1S2dS2eS2eS12S10A2S12A2A1Se1Sb5R5A2Sc6S93Vrho0;R6A3S9aVCST;VFB;VFF;Vrho0;A4S0S30SbaR7A1S31A3S1S53S38S10S10S28R9R8A2M0A3R7A2S54R7S3aS10S10G0A3A2A2SeeVCST;Vrho0;SdbVFB;RaR7A3SedVFF;RaR6A3R8A5F_;F_;F_;F_;F_;Ffrs;Fkept;Fa;Fo;Frho;") := ltac2:(tb__ "0|0|
SbcVCST;S93Sd4VFB;VFF;Vrho0;S9aVCST;VFB;VFF;A3S9cVCST;VFB;VFF;A3Sb5A9").

Lemma P0_now : ltac2:(tb__ "0|2|
S13Sc6S93Vrho0;R1A3S9aVCST;VFB;VFF;Vrho0;A4S1S10S1S53Sa4R4S99A2M0R1A2S54R1S57G0Sa4R4S97A2A2A2A2SeeVCST;Vrho0;VFB;VFF;R2A5F_;Fa;S1SfcVFF;Sa4R3S10eA2Z518A3S1SfcVFF;Sa4R3S10dA2Z30A3S0S34SfdZ0SabS2eS2eS10S10A2M1S10A2G1S38G1S10A2VFF;A4A2U0A3A2A2A2F_;F_;Frho;").
Proof.
  intros rho Hav HP. destruct (P0b_nowH CST NPH HNPH FB FF rho0 (P0_hp CST FB FF) (P0_hp_b CST FB FF) rho Hav HP) as (A & B & C).
  destruct HP as [_ D]. auto.
Qed.

Lemma tvz_kd : ltac2:(tb__ "0|2|
S13S12S12Sd8R3S32S2eS12S12A2M0S2fS12S12R2S98ZcR1A2A4S33G0A1A3A2S53Sa4R4R2A2Se2A2S2S0S10Sa4R5R3A2Z0M1A3A1S2S0S10Sa4R6R5A2G1A3A1F_;F_;F_;Fk;Fd;Frho;").
Proof.
  intros rho d k HZ HK Hk Hd. apply Forall_inv in HZ. unfold tnz, tvv in HZ. cbn [fst snd] in HZ. unfold uval in Hd, Hk, HK.
  specialize (HZ ltac:(intros H; exact (H Hd))). unfold B32 in HK.
  pose proof (uval_mul_lit rho 12 k ltac:(lia) ltac:(unfold uval; lia)) as E12. unfold uval, kb in E12. unfold kb in HZ. rewrite E12 in HZ. lia.
Qed.

Lemma slot_holds : ltac2:(tb__ "0|1|
S13S2dS14A1S12SaaS14S1bR3A1R2A3S0S30Sa1S14S1cS19S8dR2A2A1R3A3S31A3S0S30Sa1S14S1cS19R3S18Se2A1M0A2A1R4A3S31A3S0S30Sa1S14S1cS19S64R4A2A1R5A3S31A3S0S30Sa1S14S1cS19S98ZcR5A2G0A2A1R6A3S31A3SaaS14S1bR8A1S91R6A1A3F_;F_;F_;F_;F_;Fk;FF;Frho;").
Proof.
  intros rho F k HF H1 H2 H3 H5.
  pose proof (holds_mem _ _ _ HF H1) as F1. pose proof (holds_mem _ _ _ HF H2) as F2. pose proof (holds_mem _ _ _ HF H3) as F3. pose proof (holds_mem _ _ _ HF H5) as F5.
  rewrite h_ule in F1, F2, F3, F5. unfold B32 in *. rewrite uval_lit in F2 by lia. rewrite uval_lit in F5 by lia.
  pose proof (uval_range rho pC) as RC. pose proof (uval_range rho k) as Rk.
  unfold pC1 in F1. rewrite uval_add_litZ in F1 by lia.
  assert (E12k : uval rho (kb 12 k) = 12 * uval rho k) by (unfold kb; apply uval_mul_lit; lia). rewrite E12k in F5.
  assert (E12c : uval rho (cmul12 pC) = 12 * uval rho pC) by (unfold cmul12; rewrite uval_mul_comm; apply uval_mul_lit; lia).
  unfold slot_facts.
  constructor; [|constructor; [|constructor; [|constructor]]]; rewrite h_ule.
  - rewrite uval_add_litZ by (rewrite ?E12c; lia). rewrite E12c, E12k. lia.
  - rewrite E12c, E12k. lia.
  - unfold B32. rewrite E12c, uval_lit by lia. lia.
Qed.

Lemma f32_rng : ltac2:(tb__ "0|1|
S13S2dS14A1SaaS14S1bR2A1R1A3S0S30S9fR2A1S31A3S0S10Sa4R4S22SdeS95S18Z20M0A1A3A2S57Sa4R4S95A2G0A2A3F_;F_;FF;Fr;").
Proof. intros r F HF HFR. unfold hF. apply (frame_off_rng hG 160 64 32 r F sz_rng ltac:(lia) HF HFR). Qed.
Lemma slot_rng : ltac2:(tb__ "0|3|
S13S2dS14A1S12SaaS14S1bR3A1R2A3S0S30Sa1S14S1cS19R2S18Z800000000000A1A2A1R3A3S31A3S0S30Sa1S14S1cS19S66S64A1M0S18Se2A1A2A1R4A3S31A3S1S0S10Sa4R6S22SdeR4G0A3A2S57Sa4R6R4A2Sa4R6G0A2M1A2A3S1S0S10S2aR6G0A2G1A3S0S10S2aR6S22SdeG0S18ZcM2A1A3A2S57G1G2A2A3A2A2F_;F_;F_;Fd;FF;Fr;").
Proof.
  intros r F d HF Hd Hs.
  pose proof (holds_mem _ _ _ HF Hd) as F1. pose proof (holds_mem _ _ _ HF Hs) as F2.
  rewrite h_ule in F1, F2. unfold B32 in F2. rewrite uval_lit in F1 by lia. rewrite uval_lit in F2 by lia.
  pose proof (uval_range r (cmul12 pC)) as Rc. pose proof (uval_range r d) as Rd.
  assert (A12 : uval r (SAlu ALU_ADD (cmul12 pC) (SLit 12)) = uval r (cmul12 pC) + 12) by (apply uval_add_litZ; lia).
  split; [apply uval_add_small; lia|]. split; [apply soff_smallu; lia|]. rewrite <- A12. apply soff_smallu. rewrite A12. lia.
Qed.

Section X.
Variable TR : assn -> assn -> Prop.
Variable FAM : ltac2:(tb__ "0|0|
S10S2dS4eQ40A1A1Sb6F_;F_;").
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S50S6S13S2dS4eQ40A1A1Sb6SaaS14S1bR3A1S15S7R4A1A1A3VTR;S4fS4dR6R5R4R3A5R2A2M0F_;G0F_;FQ;Ftp;Frho;FS;FJ;").
Hypothesis TR_ex : forall (T : Type) (J : T -> jpredA) S rho tp (Q : assn),
  (forall x, TR (SPA segs (J x) S rho tp) Q) -> TR (SPA segs (fun r p t m => exists x, J x r p t m) S rho tp) Q.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
Sb6Sb6Sb6Sb7R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_exw : forall (T : Type) (P : T -> assn) (Q : assn), (forall a, TR (P a) Q) -> TR (fun w => exists a, P a w) Q.
Hypothesis TR_pureP : ltac2:(tb__ "0|1|
Sb6OSb6Sb7R4R1A1R4F_;Fw;R3VTR;R5R3A2M0F_;G0F_;F_;FQ;FX;FP;").
Hypothesis TR_callP : ltac2:(tb__ "0|5|
S50S50S6S6ScbS2dS17A1M0S2dS2eS6SaeA2M1A1S2dS2eS12S12A2M2A1Sb6S13S2dS4eQ40A1A1M3G2Sa0G2R1R5A3Sa0G2R2S9RbA1A3F_;Fr;S0S36G0A1Sb0RaR9R8A3S35G0R7A2A3S0S30Sb3RbRaR9R8SabG1S6S38S6SaeA2R7A4A5S31A3S13G3VTR;S4fS4dRfRdR2R1A5SafS4dS16S7RdA1A1R2R1RaA5A2Ftp1;Frho1;S2dSc5A1M4SddSc4S51S4dR9R8R10S2fG4Sf3R3Sf4R2R1A2A4A5R13RaR9R4R2A4R13ScdSccRbRfSd7R3RaR4A3A3R10A2RaR5R3A4F_;F_;Fmd;Fms;Ftr;S6SaeG4SddSc4S13G3G4SddSc4Sa0G1S2fS6SaeRaR9A4R14A3S51S4dR12R11R19S2fG4Sf3R9Sf4R8R7A2A4A5R1cR13R12RaR8A4Sc6S16S7R1aA1A1ScdSccR14R18Sd7R9R13RaA3A3R19A2R8A3S51S4dR9R8ReS2fG4Sf3R7Sf4R6R5A2A4A5ReScdSccR16R1aSd7RbR15RcA3A3R1bA2R15RaR9R8R6A6S1S119R17Sd7RcR16RdA3R1bR1cR1dR10R1eR19RbA9S13Sc7R18Sd7RdR17ReA3R1cR1dS7R1eA1S7R1fA1S7R11A1R1RcA9VTR;S4fS4dSb4R11ScdSccR19R1dSd7ReR18RfA3A3R1eA2R18RdRcA5S11aR1eR1fR12R20R1dR1bA6R2RcA5R1aA2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S4fS4dR11RfR8R7A5R9A2F_;F_;F_;F_;F_;F_;Ftp;Frho;FQ;FXk;FPosts;FR;Fs;FPre;FC;FJp;FJ;").
Hypothesis CVRES : ltac2:(tb__ "0|1|
S2dS2eS10S10A2M0A1S2dS2eG0S10A2A1Sa9S13S2dS4eQ40A1A1Sa7Z3R3A2VTR;S4fS4dS45VAInv;VCST;VXGL;VKc;Sf7R6R5A2R6R5R4S40S110AaS10fR3R2A5SafS4dSfaR3R2SefVAInv;VCST;VXGL;VKc;Sf7S40S80R6R5R4AaA5A2F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Hypothesis CSM : ltac2:(tb__ "0|2|
Sc8S13S2dS4eQ40A1A1VTR;S4fS4dS109VAInv;Z0M0R3VKc;A4S81R2R1A5SafS4dSfaR2R1S32S2eS6SaeA2M1S2fS6SaeS7fS107VAInv;VCST;VXGL;G0R3VKc;A6A4S33G1A1A3A5A2Ftp1;Frho1;FAi;").
Hypothesis CMEMCPY : ltac2:(tb__ "0|2|
Sc8S13S2dS4eQ40A1A1VTR;S4fS4dS108VAInv;R3VKc;A3S62R2R1A5SafS4dSfaR2R1S32S2eS6SaeA2M0S2fS6SaeS61S106VAInv;VCST;VXGL;R3VKc;A5A4M1S32G0G1S33G0A1A3A3A5A2Ftp1;Frho1;FAi;").

Hypothesis CALL_pc : ltac2:(tb__ "0|2|
S6ScbS2dS17A1M0S13S2dS4eQ40A1A1S3cSb6S0S36G0A1Sb0R7Sf8R6A3S35G0R5A2A3S0S30Sb1R8Sf8R7R6SabS8S6ScSf9A4A5S31A3S0S30Se8S93S16S7R9A1A1A2S31A3S0S30S41S16S7RaA1A1R5A2S31A3S0S30Sa2S14S23S16S7RbA1M1A1A1S15G1A1A3S31A3S8S13Sa0S8R2Sf9A3S24S16S7RfA1A1RcR2A3VTR;S4fS4dVJAv;RbA1SeaS15S7R10A1A1Sb2RfSf8ScR4A1R10ReA5A2R3RcA5RaA2F_;F_;Frho';FL;VTR;S4fS4dVJAv;R8A1RdRaR9A5R7A2F_;F_;F_;F_;F_;F_;FQ;Fnd;Ftp;Frho;FR;Fs;FCl;").
Hypothesis CALL_da : ltac2:(tb__ "0|2|
S6ScbS2dS17A1M0S13S2dS4eQ40A1A1S3cSb6S0S36G0A1Sb0R7Sf5R6A3S35G0R5A2A3S0S30Sb1R8Sf5R7R6SabS8S6ScSf6A4A5S31A3S0S30Se8S93S16S7R9A1A1A2S31A3S0S30S41S16S7RaA1A1R5A2S31A3S0S30Sa2S14S23S16S7RbA1M1A1A1S15G1A1A3S31A3S8S13Sa0S8R2Sf6A3S24S16S7RfA1A1RcR2A3VTR;S4fS4dVJAv;RbA1SeaS15S7R10A1A1Sb2RfSf5ScR4A1R10ReA5A2R3RcA5RaA2F_;F_;Frho';FL;VTR;S4fS4dVJAv;R8A1RdRaR9A5R7A2F_;F_;F_;F_;F_;F_;FQ;Fnd;Ftp;Frho;FR;Fs;FCl;").
Hypothesis REENTER : ltac2:(tb__ "0|4|
S6S3cS2eS10S12A2M0S13S2dS4eQ40A1A1M1S10G1Sa0S2eS2eS6S3cA2M2G0A2S2fG2G0S2fS6S3cR7R6A4R5A4S5dA3S1S53Z0S3dS2fG2G0S2fS6S3cR8R7A4R6A4R5A2M3A2S54G3R3A2A2VTR;S4fS4dVJAv;R8A1R9R6R5A5VFAM;R4R3A2A2F_;F_;Ftp0;Fb;Ftp;Frho;Frv;Fnd;FT;").
Hypothesis POST : ltac2:(tb__ "0|1|
S6S3cS13S2dS4eQ40A1A1M0S10G0Sa0S2eS6SaeA2S2fS6SaeR6Sd6R5A1A4Sd5A3VTR;S4fS4dVJAv;R6A1R7R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;Fnd;FP;").

Ltac meas := unfold emeasA; cbn [eda_rank eda_var fst snd z0 eval]; rewrite lit_unsigned; cbn; lia.

Ltac vmr := first [ lazymatch goal with |- @eq ?T ?t ?v => tryif first [ has_evar t | has_evar v ] then fail else vm_cast_no_check (@eq_refl T v) end
                  | vm_compute; reflexivity ].
Tactic Notation "innth" integer(n) := cbn [In cutsH exitsH Posts_hpJ PD_vr]; do n right; left; reflexivity.

Lemma loop_meas : ltac2:(tb__ "0|5|
S13S13S2dS14A1S11S10S10S6S6S3cS3cSaaS14S1bRaA1R8A3S0S30S9bS5aR9A2S31A3Sc6R9RcRbA3S0S30S20RaS96A2S31A3S0S30S20RbS5aA2S31A3S53Z0M0RbA2S54RcRbA2S54RcZ40A2S1S53G0S3dS2fS2eS6S3cA2M1S2eS10S12A2M2S2fS6S3cRbR9A4S2fS10S12Z50M3S5bS5aReA2A4A4R11A2M4A2S54G4S3dS2fG1G2S2fS6S3cRcRaA4S2fS10S12G3S5bS5aRdA2A4A4R12A2A2A2F_;F_;F_;F_;F_;F_;F_;F_;FndT;FndX;FT;FX;Fb;Fa;Fn;FF;Frho';Frho;").
Proof.
  intros rho rho' F n a b X T ndX ndT HF HV Hag HbE HbQ Ha Hab Hb. unfold emeasA. cbn [eda_rank eda_var fst snd].
  pose proof (VR_meas rho rho' F pQ a b HF HV (eq_sym (eval_agree_vals n rho rho' tE Hag HbE)) (eq_sym (eval_agree_vals n rho rho' pQ Hag HbQ)) Ha Hab Hb) as M.
  unfold uval in M. lia.
Qed.
Lemma loop_meas_same : ltac2:(tb__ "0|5|
S13S2dS14A1S10S10S6S6S3cS3cSaaS14S1bR8A1R7A3S0S30S9bS5aR8A2S31A3S53Z0M0R8A2S54R9R8A2S54R9Z40A2S1S53G0S3dS2fS2eS6S3cA2M1S2eS10S12A2M2S2fS6S3cR8R6A4S2fS10S12Z50M3S5bS5aRbA2A4A4RdA2M4A2S54G4S3dS2fG1G2S2fS6S3cR9R7A4S2fS10S12G3S5bS5aRaA2A4A4RdA2A2A2F_;F_;F_;F_;F_;FndT;FndX;FT;FX;Fb;Fa;FF;Frho;").
Proof.
  intros rho F a b X T ndX ndT HF HV Ha Hab Hb. unfold emeasA. cbn [eda_rank eda_var fst snd].
  pose proof (VR_meas rho rho F pQ a b HF HV eq_refl eq_refl Ha Hab Hb) as M. unfold uval in M. lia.
Qed.

Lemma X_reopen : ltac2:(tb__ "0|7|
S6S6S2dS2eS12S12A2A1S2dSa5A1S10S10S13S2dS4eQ40A1A1M0S10G0S2eS10S12A2M1S0S12SdRbA1S18Se6A1A3S53Z0M2R8A2S1S53R9R8A2S53R8Z8A2A2S0S30SbS32S14S1eSaS94A1S95A2S32S14S19S1fS94A1S18S58S55Z2Z3dA2Z1A2A1A2S33S14A1A3A3S15S7ReA1A1A2S31A3S0S30S21S7Sd0RfS9RfA1S94RbRaA5A1A1S31A3S0S30S9dS15S7R10A1A1A1S31A3S0S30SceS15S7R11A1M3A1RfS59S37S34A1SbaS1aG3A1A6S31A3S0S30ScfVXGL;S15S7R12A1M4A1R10S59S35S34U0A2S1aG4A1SbbS9R12A1A8S31A3S0S6Sd0R13S9R13A1S94RfReA5R12A3Sa0S2eS2eS6S3cA2M5G1A2S2fG5G1S2fS6S3cR13S3fR12S59R11S3eA4A4RaA4S5dA3S1S53G2S3dS2fG5G1S2fS6S3cR14S3fR13S59R12S3eA4A4RbA4RfA2M6A2S54G6RdA2A2VTR;S4fS4dVJAv;S3fR14S59R13S3eA4A1R16R10RfA5VFAM;ReRdA2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Frv;Ftp0;Fb;Ftp;Frho;Fk2;Fk1;Fbd;Ftv;FC;FA;").
Proof.
  intros A C tv bd k1 k2 rho tp b tp0 rv Hbase Hk1 Hk2 Hfe Hwf HB HRO HXL HC HinC Hm.
  eapply TR_pre; [|apply (REENTER C (NDA tv fr_hp bd ANone) rv); [exact HinC | exact Hm]].
  intros w Hw. rewrite <- HC.
  apply (JA_shadow_reopen segs HTOP AInv CST XGL ALA HCST HXGL LFSH NPH Kc rho0 (P0_hp CST FB FF) FB FF BX PTrue HKc HBX HNP
           tv fr_hp bd ANone 0%nat 160%positive 0 170%positive hG k1 k2 A (ax_X A) rho tp w eq_refl ltac:(lia) Hbase Hk1
           ltac:(change (fs_frame_size 0) with 64; lia) Hfe (fun r H => H) Hwf); [|exact Hw].
  intros Ai rho1 tp1 md1 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR. split.
  - exact (siteF Ai rho _ tv fr_hp _ rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HN HD HZ HFR HRO).
  - intros r y Hr Hy. left. exact (proj1 (siteX Ai rho _ tv fr_hp (Some 0%nat) _ _ rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HBf HFF HN HD HZ HFR HXL) r y Hr Hy).
Qed.
Lemma XH_E_unp : ltac2:(tb__ "0|1|
S13S2dS4eQ40A1A1M0G0VTR;S4fS4dVJAv;S5cA1S6fR3R2A5VFAM;S3dS2fS2eS6S3cA2S2eS10S12A2S2fS6S3cS6fS5cA4S2fS10S12Z50S5bS5aZ3bA2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_facts. intros HF. unfold ndJ, ndF.
  apply (X_reopen E_unp0 C_unp tvL (bd_hpN pK pQ) 4 6 rho tp _ tp0 (80, VR pQ 58) eq_refl ltac:(lia) ltac:(lia));
    [vmr|vmr|vmr|vmr|vmr| exact C_unp_eq | innth 7 | exact (loop_meas_same rho _ 58 59 E_unp0 C_unp _ _ HF ltac:(vmr) ltac:(lia) ltac:(lia) ltac:(lia))].
Qed.

Lemma reenter_abs : ltac2:(tb__ "0|6|
S6S3cS2eS10S12A2M0S13S2dS4eQ40A1M1A1M2S10G2Sb6Sa0S2eS2eS6S3cA2M3G0A2S2fG3G0S2fS6S3cR8R7A4R6A4S5dA3Sb7R3R1A1S5S13S13S1S12S0G1S1dR2R1A2M4S1dRaR1A2A3Fe;S4fS4dVJAv;RbA1RcR1R8R3A6A2Lrho';A2F_;Fw;S13S12S0G1G4S1dR9R1A2A3Fe;S1S53Z0S3dS2fG3G0S2fS6S3cRcRbA4RaA4R2A2M5A2S54G5R7A2A2F_;Frho';VTR;R4VFAM;R6R5A2A2F_;F_;F_;FP;Ftp0;Fb;Ftp;Frho;Frv;Fnd;FC;").
Proof.
  intros C nd rv rho tp b tp0 P HinC HP Hm. eapply TR_pre; [exact HP|]. apply TR_exw. intros rho'.
  apply (TR_pureP _ (forall e, eval rho' e = eval rho e)); [intros w [HE _]; exact HE|]. intros HE.
  eapply TR_pre; [intros w [_ Hw]; exact Hw|]. apply (REENTER C nd rv); [exact HinC | exact (Hm rho' HE)].
Qed.

Lemma X_release : ltac2:(tb__ "0|7|
S6S6S2dS17A1M0S10S10S2dS25A1S2cS2dS2eS12S12A2A1S2dSa5A1S13S2dS4eQ40A1M1A1M2S10G2S2eS10S12A2M3S0S12SdReA1S18Se6A1A3S53Z0M4RcA2S1S53RdRcA2S53RcZ8A2A2S0S30S2bRbA1S31A3S0G0S1aS7R12A1A1S3bS17R10S32S17Sd3S94RfReRdRcA5S33S17A1A3A3A3S0S30SbS32S14S1eSaS94A1S95A2S32S14S19S1fS94A1S18S58S55Z2Z3dA2Z1A2A1A2S33S14A1A3A3S15S7R13A1A1A2S31A3S0S30S41S16S7R14A1A1S3fRdS59RcS3eA4A2S31A3S0S30S9dS15S7R15A1A1A1S31A3S0S30SceS15S7R16A1A1RfS59S37S34A1SbaR14A6S31A3S0S6Sd2R17R15Pa0S33S2eS10S10A2A1A4R16A3Sa0S2eS2eS6S3cA2M5G3A2S2fG5G3S2fS6S3cR17S3fR11S59R10S3eA4A4RbA4S5dA3S13S12S0G1S1dR2R1A2S1dR12R1A2A3Fe;S1S53G4S3dS2fG5G3S2fS6S3cR1aS3fR14S59R13S3eA4A4ReA4R2A2M6A2S54G6R10A2A2F_;Frho';VTR;S4fS4dVJAv;S3fR13S59R12S3eA4A1R1aR11R10A5VFAM;RfReA2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Frv;Ftp0;Fb;Ftp;Frho;Fbd;Ftv;Fd;Fcells;Fk2;Fk1;Fobjs;FC;FA;").
Proof.
  intros A C objs k1 k2 cells d tv bd rho tp b tp0 rv Hbase Hk1 Hk2 Hdw Ho Hfe Hnb HB HRO HC HinC Hm.
  apply (reenter_abs C (NDA tv fr_hp bd ANone) rv rho tp b tp0); [exact HinC | | exact Hm].
  intros [tr [ms md]] Hw. exists (rho_absorb rho [shobj hG k1 k2 cells d] (vms md tp ms)). split; [intros e; apply eval_absorb|].
  rewrite <- HC.
  apply (JA_shadow_release segs HTOP AInv CST XGL ALA HCST HXGL LFSH NPH Kc rho0 (P0_hp CST FB FF) FB FF BX PTrue HKc HBX HNP
           tv fr_hp bd ANone 0%nat 160%positive 0 170%positive hG k1 k2 cells d A objs [] rho tp tr ms md
           eq_refl ltac:(lia) Hbase Ho Hk1 ltac:(change (fs_frame_size 0) with 64; lia) Hdw Hfe eq_refl Hnb); [|exact Hw].
  intros Ai rho1 tp1 md1 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR.
  exact (siteF Ai rho _ tv fr_hp objs rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HN HD HZ HFR HRO).
Qed.
Lemma emeas_z0 : ltac2:(tb__ "0|0|
S6S3cS10S13S0S10S3dS2fS2eS6S3cA2S2eS10S12A2S2fS6S3cR4R3A4S2fS10S12R2S65A4A4R1A2S56R2S55Z2Z40A2A2A3Frho;Fr;Fnd;FT;").
Proof. intros. unfold emeasA. cbn [eda_rank eda_var fst snd z0 eval]. rewrite lit_unsigned by lia. lia. Qed.
Lemma emeas_eq : ltac2:(tb__ "0|1|
S6S3cS10S12S13S13S12S0S4eQ40A1S1dR2R1A2S1dR3R1A2A3Fe;S0S10S3dS2fS2eS6S3cA2S2eS10S12A2S2fS6S3cR7R6A4S2fS10S12R5R4A4A4M0R2A2S3dG0R3A2A3F_;Frho';Frho;Fv;Fr;Fnd;FT;").
Proof. intros. unfold emeasA. cbn [eda_rank eda_var fst snd]. rewrite H. reflexivity. Qed.

Lemma XH_X_pro : ltac2:(tb__ "0|1|
S13S2dS4eQ40A1A1M0S10G0S53S56Z5eS55Z2Z40A2A2R2A2VTR;S4fS4dVJAv;S8cA1S85R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. unfold ndP, ndF.
  apply (X_release X_pro C_pre objs_pro 0 8 cells_pro DZero _ _ rho tp b tp0 (92, z0) eq_refl ltac:(lia) ltac:(lia) eq_refl X_pro_objs);
    [vmr|vmr|vmr|vmr| exact C_pre_eq | innth 2 | intros rho' _; rewrite emeas_z0; lia].
Qed.
Lemma XH_X_r2k : ltac2:(tb__ "0|1|
S13S2dS4eQ40A1A1M0G0VTR;S4fS4dVJAv;S5cA1S76R3R2A5VFAM;S3dS2fS2eS6S3cA2S2eS10S12A2S2fS6S3cS76S5cA4S2fS10S12Z50S5bS5aZ2eA2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_facts. intros HF. unfold ndJ, ndF.
  apply (X_release X_r2k C_rlk objs_r2k 4 6 cells_r2k DUnknown _ _ rho tp _ tp0 (80, VR pQ 45) eq_refl ltac:(lia) ltac:(lia) eq_refl X_r2k_objs);
    [vmr|vmr|vmr|vmr| exact C_rlk_eq | innth 18 |].
  intros rho' HE. rewrite (emeas_eq C_rlk _ 80 (VR pQ 45) rho rho' HE).
  exact (loop_meas_same rho _ 45 46 X_r2k C_rlk _ _ HF ltac:(vmr) ltac:(lia) ltac:(lia) ltac:(lia)).
Qed.
Lemma XH_X_r2g : ltac2:(tb__ "0|1|
S13S2dS4eQ40A1A1M0G0VTR;S4fS4dVJAv;S5fA1S75R3R2A5VFAM;S3dS2fS2eS6S3cA2S2eS10S12A2S2fS6S3cS75S5fA4S2fS10S12Z50S5bS5aZ2eA2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_facts. intros HF. unfold ndG, ndF.
  apply (X_release X_r2g C_rlg objs_r2g 4 6 cells_r2g DUnknown _ _ rho tp _ tp0 (80, VR pQ 45) eq_refl ltac:(lia) ltac:(lia) eq_refl X_r2g_objs);
    [vmr|vmr|vmr|vmr| exact C_rlg_eq | innth 19 |].
  intros rho' HE. rewrite (emeas_eq C_rlg _ 80 (VR pQ 45) rho rho' HE).
  exact (loop_meas_same rho _ 45 46 X_r2g C_rlg _ _ HF ltac:(vmr) ltac:(lia) ltac:(lia) ltac:(lia)).
Qed.

Definition pure_rule (Pre : axst) (Posts : list leafA) : Prop := ltac2:(tb__ "0|2|
S6ScbS2dS17A1M0S13S2dS4eQ40A1A1S3cSb6S0S36G0A1Sb0R7VPre;R6A3S35G0R5A2A3S0S30Sb1R8VPre;R7R6SabS8S6ScVPosts;A4A5S31A3S0S30Se8S93S16S7R9A1A1A2S31A3S0S30S41S16S7RaA1A1R5A2S31A3S0S30Sa2S14S23S16S7RbA1M1A1A1S15G1A1A3S31A3S8S13Sa0S8R2VPosts;A3S24S16S7RfA1A1RcR2A3VTR;S4fS4dVJAv;RbA1SeaS15S7R10A1A1Sb2RfVPre;ScR4A1R10ReA5A2R3RcA5RaA2F_;F_;Frho';FL;VTR;S4fS4dVJAv;R8A1RdRaR9A5R7A2F_;F_;F_;F_;F_;F_;FQ;Fnd;Ftp;Frho;FR;Fs;FCl;").
Lemma X_pure : ltac2:(tb__ "0|6|
S6S6S6S6S6S6S2dSe4A1ScbS2dS17A1M0S13S2dS4eQ40A1A1M1G1S10S10S114ReS32S8SfRdS116A2S33S8A1A3A2S0S36G0A1Sb0RdRfR8A3S35G0R7A2A3S0S30Sb1ReR10R9R8S32S6RfS33S6A1A3A5S31A3S0S30Se8S93S16S7RfA1A1A2S31A3S0S30S41S16S7R10A1A1S5cA2S31A3S0S30Sa2S14S23S16S7R11A1M2A1A1S15G2A1A3S31A3S0S6SeaS15S7R12A1A1Sb2RdR14R13R12RcA5A2R11A3S0S36S6A1Se3R12RfA2S35S6R11A2A3Sa0S2eS2eS6S3cA2M3S2eS10S12A2M4A2S2fG3G4S2fS6S3cR12S5cA4S2fS10S12Z50M5S5bS5aRaA2A4A4S5dA3S0S30S9bS5aS15S7R15A1A1A2S31A3S0S30S20S16S7R16A1A1S96A2S31A3S0S30S20S16S7R17A1A1S5aA2S31A3S53Z0ReA2S54RfReA2S54RfZ40A2VTR;S4fS4dVJAv;S5cA1R1bR14R13A5VFAM;S3dS2fG3G4S2fS6S3cR18S5cA4S2fS10S12G5S5bS5aR10A2A4A4R14A2R12A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fbpos;Fa;Ftp0;Ftp;Frho;FR;Fs;Fxf2;FX0;FT;FT0;FE;FP;FPre;").
Proof.
  intros Pre P E T0 T X0 xf2 s R rho tp tp0 a bpos CALL He Hchk Hnf Hnb Hfb HT0 HT HinT HV HbE HbQ Ha Hab Hb.
  apply TR_facts. intros HF.
  apply (CALL E s R rho tp ndJ _ He Hchk Hnf Hnb Hfb).
  intros L rho' HL Hag. cbn [In] in HL. destruct HL as [<-|[]]. cbn [la_state]. rewrite HT0.
  eapply TR_pre; [intros w Hw; exact (SPA_axforms segs _ xf2 rho' T0 T tp w HT Hw)|].
  apply (REENTER T ndJ (80, VR pQ a)); [exact HinT|].
  exact (loop_meas rho rho' _ _ a bpos X0 T ndJ ndJ HF HV (agree_below_vals _ _ _ Hag) HbE HbQ Ha Hab Hb).
Qed.

Lemma XH_E_pc : ltac2:(tb__ "0|1|
S13S2dS4eQ40A1A1M0G0VTR;S4fS4dVJAv;S5cA1S6eR3R2A5VFAM;S3dS2fS2eS6S3cA2S2eS10S12A2S2fS6S3cS6eS5cA4S2fS10S12Z50S5bS5aZ39A2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  apply (TR_pre (fun w => exists rho', (fun w' => (forall e, eval rho' e = eval rho e) /\ SPA segs (JAv ndJ) E_pc1 rho' tp w') w)).
  { intros [tr [ms md]] Hw. exists (rho_absorb rho [shobj hG 4 6 cells_unp DUnknown] (vms md tp ms)). split; [intros e; apply eval_absorb|].
    rewrite <- E_pc1_eq. unfold ndJ, ndF.
    apply (JA_shadow_release segs HTOP AInv CST XGL ALA HCST HXGL LFSH NPH Kc rho0 (P0_hp CST FB FF) FB FF BX PTrue HKc HBX HNP
             tvL fr_hp (bd_hpN pK pQ) ANone 0%nat 160%positive 0 170%positive hG 4 6 cells_unp DUnknown E_pc0 objs_pc0 [(32, 12)] rho tp tr ms md
             eq_refl ltac:(lia) eq_refl E_pc0_objs ltac:(lia) ltac:(change (fs_frame_size 0) with 64; lia) eq_refl ltac:(vmr) ltac:(vmr) ltac:(vmr)); [|exact Hw].
    intros Ai rho1 tp1 md1 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR.
    exact (siteF Ai rho _ tvL fr_hp objs_pc0 rho1 tp1 md1 HM HF ltac:(vmr) Hav HP0 HT HTK HN HD HZ HFR ltac:(vmr)). }
  apply TR_exw. intros rho'. apply (TR_pureP _ (forall e, eval rho' e = eval rho e)); [intros w [HE _]; exact HE|]. intros HE.
  eapply TR_pre; [intros w [_ Hw]; exact (SPA_axforms segs _ xf_pc rho' E_pc1 E_pc tp w E_pc_eq Hw)|].
  rewrite <- (emeas_eq E_pc0 ndJ 80 (VR pQ 57) rho rho' HE).
  apply (X_pure Pre_pc P_ret E_pc T_pc0 T_pc E_pc0 xf_tpc s_pc R_pc rho' tp tp0 56 57 CALL_pc);
    [vmr|vmr|vmr|vmr|vmr| exact T_pc0_eq | exact T_pc_eq | innth 8 |vmr|vmr|vmr|lia|lia|lia].
Qed.

Lemma XH_E_da : ltac2:(tb__ "0|1|
S13S2dS4eQ40A1A1M0G0VTR;S4fS4dVJAv;S5cA1S6bR3R2A5VFAM;S3dS2fS2eS6S3cA2S2eS10S12A2S2fS6S3cS6bS5cA4S2fS10S12Z50S5bS5aZ37A2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  eapply TR_pre; [intros w Hw; exact (SPA_axforms segs _ [AXSplit 0 (SLit (-96))] rho E_da0 E_da tp w E_da_eq Hw)|].
  apply (X_pure Pre_da P_da E_da T_da0 T_da E_da0 xf_tda s_da R_da rho tp tp0 54 55 CALL_da);
    [vmr|vmr|vmr|vmr|vmr| exact T_da0_eq | exact T_da_eq | innth 9 |vmr|vmr|vmr|lia|lia|lia].
Qed.

Lemma HIN_v : ltac2:(tb__ "0|1|
S13SddSc8S13S2dS4eQ40A1A1Sc4SaaS14S1bR6A1S15S7S7eA1A1A3S9aVCST;VFB;VFF;Vrho0;A4Sc6S93Vrho0;R8A3VAInv;R7R6R5R4A4S42Vrho0;R8A2Sd9RbScaSc9R9A1A1A2S46VFB;RaA2S47VFF;RbA2Sd8ReS6aA2S43VFF;RdRfS59A4S1Sf0VCST;Vrho0;VFB;VFF;R10S33S2eS12S12A2A1M0S59S74A8S1Sf1VCST;VXGL;Vrho0;VFB;VFF;R10G0S59S89A9Sf7SdbVFB;R10G0A3SedVFF;R10S59A3ScdSccR10S74RfA3S8fA2A3A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FAi;Fms;Frho;").
Proof.
  intros rho ms Ai rho1 tp1 md1 HF HP0 Hav HM HTP HTK HBf HFF HZ HFR. destruct (P0_now rho Hav HP0) as (HT & Hb & Hal & _).
  assert (HB : bF (ss_facts (ax_S E_vr)) = true) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
  pose proof (basez_of DW rho _ DW_rng HF HB) as BZ. pose proof BZ as [Bsp Bb Bal BL BB Btop]. rewrite aceil_val in *.
  assert (HN0 : tvinA FB Ai rho []) by constructor. assert (HZ0 : tvz rho []) by constructor.
  split; [|split].
  - intros o a Ho Hr. eapply (robjs_checkP_sound segs AInv CST ALA rho0 FB FF Ai rho _ [] fr_hp None extraOH R_v rho1 tp1 md1 HM HF (T_ok_T0 rho0 _ Ai HTP HTK) HN0 I HZ0 HFR ltac:(vmr));
      [intros o' a' Ho' HE Hr'; exact (extra_client rho o' a' _ _ BZ Hav HP0 HE Hr') | exact Ho | exact Hr].
  - exact (proj1 (siteX Ai rho _ [] fr_hp None (ss_objs (ax_S E_vr)) Xk_v rho1 tp1 md1 HM HF HB Hav HP0 HTP HTK HBf HFF HN0 I HZ0 HFR ltac:(vmr))).
  - unfold VNP.P0_vr. rewrite !rw_call'.
    change (wsub_get s_v 17) with pK. change (wsub_get s_v 15) with pD. change (wsub_get s_v 14) with vAL. change (wsub_get s_v 12) with (xbo 688).
    split; [|split].
    + pose proof (holds_mem _ _ (SPUle pK (SLit B32)) HF ltac:(vmr)) as FK. rewrite h_ule in FK. unfold B32 in FK. rewrite uval_lit in FK by lia.
      intros HK. apply (tvz_kd rho pD pK HZ); [unfold B32; lia | exact HK].
    + destruct Hb as (f & sz & fl & Hin & H1 & H2). exists f, sz, fl. split; [apply In_FFx; left; exact Hin|].
      assert (E688 : uval rho (xbo 688) = uval rho vb + 688) by (unfold xbo; apply uval_add_litZ; unfold IMG_HI in *; lia).
      unfold uval in E688, H1, H2. rewrite E688. lia.
    + destruct Hal as (f & sz & fl & Hin & H1 & H2). exists f, sz, fl. split; [apply In_FFx; left; exact Hin|]. unfold uval in H1, H2. lia.
Qed.

Lemma XH_E_vr : ltac2:(tb__ "0|1|
S13S2dS4eQ40A1A1M0G0VTR;S4fS4dVJAv;S5cA1S70R3R2A5VFAM;S3dS2fS2eS6S3cA2S2eS10S12A2S2fS6S3cS70S5cA4S2fS10S12Z50S5bS5aZ34A2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  eapply TR_pre with (P := SPA segs (JAv ndJ) E_vr rho tp).
  { intros w Hw. exact (SPA_axforms segs _ xf_vr rho E_vr0 E_vr tp w E_vr_eq Hw). }
  apply TR_facts. intros HF. unfold ndJ, ndF. change tvL with ([] ++ tvL).
  apply (client_callT segs AInv CST XGL ALA HCST HXGL NPH Kc rho0 (P0_hp CST FB FF) FB FF BX PTrue HKc HBX VNP.P0_vr PTrue (fun _ H => H) (fun _ _ _ H => H)
           VN.Pre_vr VN.nd0 PD_vr NF eq_refl eq_refl eq_refl TR TR_facts TR_ex TR_pre TR_callP CVRES eq_refl
           E_vr s_v R_v Xk_v rho tp [] tvL fr_hp (bd_hpN pK pQ) [PROG 72 pQ] ANone (FAM (emeasA (E_vr0, ndJ, (80, VR pQ 52)) rho) tp0)).
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
  - intros Ai ms HF' HP0 Hav HBf HFF HN HD HZ HFR (rho1 & tp1 & md1 & HM) HT HTK. cbn [app] in HZ. exact (HIN_v rho ms Ai rho1 tp1 md1 HF' HP0 Hav HM HT HTK HBf HFF HZ HFR).
  - intros [Ld ndL] rho' tp' Hd Hag. cbn [PD_vr In] in Hd. destruct Hd as [Hd|[Hd|[Hd|[]]]]; injection Hd as <- <-;
      cbn [fst snd nd_tv nd_bd nd_am VN.nd0 ND am_subst app].
    +
      rewrite T_keep0_eq, imp_keep_tv, imp_keep_bd. change ([PHIN pQ pK; KLG pK] ++ [PROG 72 pQ]) with (bd_hpN pK pQ).
      eapply TR_pre; [|apply (REENTER T_keep ndJ (80, VR pQ 51)); [innth 11 | exact (loop_meas rho rho' _ _ 51 52 E_vr0 T_keep ndJ ndJ HF ltac:(vmr) Hag ltac:(vmr) ltac:(vmr) ltac:(lia) ltac:(lia) ltac:(lia))]].
      intros w Hw. rewrite <- T_keep_eq. apply (SPA_refacts_JA segs); [exact Hw | vmr |].
      intros tr md HJ HF2. apply Forall_app. split; [|exact HF2]. apply Forall_app. split.
      * apply (slot_holds rho' _ pK HF2); vmr.
      * assert (TNZ : tnz rho' (pD, kb 12 pK)).
        { destruct HJ as (Ai & kc & Hav' & _ & _ & _ & _ & _ & (_ & _ & HZ') & _).
          pose proof (holds_mem _ _ (SPUle pC1 pK) HF2 ltac:(vmr)) as F1. pose proof (holds_mem _ _ (SPUle pK (SLit B32)) HF2 ltac:(vmr)) as F4.
          pose proof (holds_mem _ _ (SPUle pC pK) HF2 ltac:(vmr)) as F3.
          rewrite h_ule in F1, F3, F4. unfold B32 in F4. rewrite uval_lit in F4 by lia. pose proof (uval_range rho' pC) as RC.
          unfold pC1 in F1. rewrite uval_add_litZ in F1 by lia. unfold tnz. cbn [fst]. apply (tvz_kd rho' pD pK HZ'); unfold B32; lia. }
        pose proof (JA_tv_facts segs AInv CST XGL NPH Kc rho0 (P0_hp CST FB FF) FB FF BX PTrue ALA _ _ _ _ _ (pD, kb 12 pK) eq_refl HJ (or_introl eq_refl) TNZ) as TF.
        constructor; [|constructor]. apply (proj1 (Forall_forall _ _) TF). unfold tv_factsA. cbn [fst snd]. do 5 right. left. reflexivity.
    +
      rewrite T_fail0_eq, imp_fail_tv. change (bd_subst _ [] ++ [PROG 72 pQ]) with ([PROG 72 pQ]).
      apply (REENTER T_fail0 ndX (30, z0)); [innth 13|]. rewrite emeas_z0. unfold emeasA. cbn [eda_rank eda_var fst snd]. pose proof (bv_urange (eval rho (VR pQ 52))). lia.
    +
      rewrite T_grown0_eq, imp_grown_tv, imp_grown_bd. change ([PHIN pQ vKg; KLG vKg] ++ [PROG 72 pQ]) with (bd_hpN vKg pQ). fold tvG.
      eapply TR_pre; [|apply (REENTER T_grown ndG (80, VR pQ 51)); [innth 12 | exact (loop_meas rho rho' _ _ 51 52 E_vr0 T_grown ndJ ndG HF ltac:(vmr) Hag ltac:(vmr) ltac:(vmr) ltac:(lia) ltac:(lia) ltac:(lia))]].
      intros w Hw. rewrite <- T_grown_eq. apply (SPA_refacts_JA segs); [exact Hw | vmr |].
      intros tr md _ HF2. apply Forall_app. split; [|exact HF2]. apply (slot_holds rho' _ vKg HF2); vmr.
Qed.

Lemma X_E_mc : ltac2:(tb__ "0|a|
S6S6S6S6S12S12S2dS2eS12S12A2A1S2dSa5A1ScbS2dS17A1M0S13S2dS4eQ40A1A1M1G1S0S36S6A1Se3RdS92A2S35S6RcA2A3S0S36S17A1Sa3S17S1aS7RdA1A1U4M2A3S35S17S27RaS66S64A1M3S22SdeG3S18ZcA1A3S33S25A1S26A5A2A3S0S30S29S16S7ReA1A1S79RbA1A2S31A3S0S30Sa1S14S1cS19RcS18Z800000000000A1A2A1S15S7RfA1A1A3S31A3S0S30Sa1S14S1cS19G3S18Se2A1A2A1S15S7R10A1A1A3S31A3S0S6S8eR11G2S79ReA1A3R10A3S0S36G0A1Sb0R11S62RbA3S35G0RaA2A3S0S30Sb3R12S62RcRbS32S6S61S32S6S61S33S6A1A3A3A5S31A3S0S30SffS93RdA2S31A3S0S30Se8S93S16S7R14A1A1A2S31A3S0S30S41S16S7R15A1A1S3fR11S59R10S3eA4A2S31A3S0S30Sa8S16S7R16A1A1R11A2S31A3S0S30Sa6R12A1S31A3S0S30S9dS15S7R18A1A1A1S31A3S0S30SfbS15S7R19A1A1R15S59S37S34A1M4SbaR12A6S31A3S0S30ScfVXGL;S15S7R1aA1M5A1R16S59G4S1aG5A1SbbS9R1aA1A8S31A3S0S6SfeS62R1bR15R14S61A5R1aA3Sa0S2eS2eS6S3cA2M6S2eS10S12A2M7A2S2fG6G7S2fS6S3cR1bS3fR18S59R17S3eA4A4S2fS10S12Z50M8S5bS5aZ31A2A4A4S5dA3S0S30S9bS5aS15S7R1dA1A1A2S31A3S0S30S20S16S7R1eA1A1S96A2S31A3S0S30S20S16S7R1fA1A1S5aA2S31A3VTR;S4fS4dVJAv;S3fR1cS59R1bS3eA4M9A1R22R18R17A5VFAM;S3dS2fG6G7S2fS6S3cR22G9A4S2fS10S12G8S5bS5aZ32A2A4A4R18A2R16A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Ftp0;Ftp;Frho;FR;Fs;Fbd;Ftv;Fk;Fd;FT;FE;FE1;FE0;").
Proof.
  intros E0 E1 E T d k tv bd s R rho tp tp0 HE1 H4 Hwf4 Hd Hs HE He Hchk Htp Hnf Hnb Hbb Hwp HB HR HX HT HinT HV HbE HbQ.
  eapply TR_pre with (P := SPA segs (JAv (NDA tv fr_hp bd ANone)) E rho tp).
  { intros w Hw. pose proof (SPA_axforms segs _ xf_mc rho E0 E1 tp w HE1 Hw) as Hw1. rewrite <- HE. unfold reshapeA.
    apply (SPA_reshape segs _ rho E1 4 _ _ tp w H4); [reflexivity | reflexivity | reflexivity | exact Hwf4 | | exact Hw1].
    intros HF. destruct (slot_rng rho _ d HF Hd Hs) as (A1 & A2 & A3).
    unfold dst_obj, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite !soff_lit_small by lia. rewrite A2, A3.
    change (bv_unsigned (eval rho (SAlu ALU_ADD d (cmul12 pC)))) with (uval rho (SAlu ALU_ADD d (cmul12 pC))). rewrite A1. unfold uval. lia. }
  apply TR_facts. intros HF.
  apply (purec_callT_ag_xp segs AInv CST XGL ALA HCST HXGL NPH Kc rho0 (P0_hp CST FB FF) FB FF BX PTrue HKc TR TR_facts TR_ex TR_pre TR_callP
           XP_memcpy Pre_mc [L_mc1; L_mc1] E s R rho tp (NDA tv fr_hp bd ANone) bd (FAM (emeasA (E0, NDA tv fr_hp bd ANone, (80, VR pQ 50)) rho) tp0)).
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
  - exact (site_pure E s R rho tv fr_hp bd HB HR HX).
  - intros Ai tr ms md Hsm HM HX'. exact (XP_memcpy_site segs AInv CST XGL ALA HCST HXGL Ai E memcpy_pc s R rho tp tr ms md Hsm HM HX' ltac:(first [assumption | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc])).
  - intros L rho' tp' HL Hag. cbn [In] in HL. assert (HL' : L = L_mc1) by (destruct HL as [<-|[<-|[]]]; reflexivity). subst L. cbn [nd_tv nd_fr nd_am]. rewrite HT.
    apply (REENTER T (NDA tv fr_hp bd ANone) (80, VR pQ 49)); [exact HinT|].
    exact (loop_meas rho rho' _ _ 49 50 E0 T _ _ HF HV Hag HbE HbQ ltac:(lia) ltac:(lia) ltac:(lia)).
Qed.
Lemma XH_E_mk : ltac2:(tb__ "0|1|
S13S2dS4eQ40A1A1M0G0VTR;S4fS4dVJAv;S5cA1S6dR3R2A5VFAM;S3dS2fS2eS6S3cA2S2eS10S12A2S2fS6S3cS6dS5cA4S2fS10S12Z50S5bS5aZ32A2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. unfold ndJ, ndF.
  apply (X_E_mc E_mk0 (E_mc1 E_mk0) E_mk T_mck pD pK _ _ (s_mc E_mk pD pK) R_mk rho tp tp0 E_mk1_eq);
    [vmr|vmr|vmr|vmr| exact E_mk_eq |vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr| exact T_mck_eq | innth 14 |vmr|vmr|vmr].
Qed.
Lemma XH_E_mg : ltac2:(tb__ "0|1|
S13S2dS4eQ40A1A1M0G0VTR;S4fS4dVJAv;S5fA1S6cR3R2A5VFAM;S3dS2fS2eS6S3cA2S2eS10S12A2S2fS6S3cS6cS5fA4S2fS10S12Z50S5bS5aZ32A2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. unfold ndG, ndF, tvG.
  apply (X_E_mc E_mg0 (E_mc1 E_mg0) E_mg T_mcg vDg vKg _ _ (s_mc E_mg vDg vKg) R_mg rho tp tp0 E_mg1_eq);
    [vmr|vmr|vmr|vmr| exact E_mg_eq |vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr| exact T_mcg_eq | innth 15 |vmr|vmr|vmr].
Qed.

Lemma X_cm : ltac2:(tb__ "0|a|
S6S6S6S12S12S2dS2eS12S12A2A1S2dSa5A1S13S2dS4eQ40A1A1M0G0S0S36S17A1Sa3S17S1aS7RaA1A1U1A3S35S17S27S22SdeR7S66S64A1M1A3S18Z0A1S18ZcA1S33S25A1S26A5A2A3S0S30S29S16S7RbA1A1S8bR8A1A2S31A3S0S30Sa1S14S1cS19R9S18Z800000000000A1A2A1S15S7RcA1A1A3S31A3S0S30Sa1S14S1cS19G1S18Se2A1A2A1S15S7RdA1A1A3S31A3S0S36S6A1Se3S111ReRbA2S112A2S35S6RdA2A3S0S12SdReA1S18Se6A1A3S0S30SbS32S14S1eSaS94A1S95A2S32S14S19S1fS94A1S18S58S55Z2Z3dA2Z1A2A1A2S33S14A1A3A3S15S7RfA1A1A2S31A3S0S30SecS5eReRdA2S9R10A1A2S31A3S0S30S21S7Sd0R11S5eRfReA2S94Z4M2Z6M3A5A1A1S31A3S0S30S9dS15S7R12A1A1A1S31A3S0S30SceS15S7R13A1M4A1RfS59S37S34A1SbaS1aG4A1A6S31A3S0S30ScfVXGL;S15S7R14A1M5A1R10S59S35S34U0A2S1aG5A1SbbS5eR12R11A2A8S31A3S0S6Sd0R15S5eR13R12A2S94G2G3A5R14A3Sa0S2eS2eS6S3cA2M6S2eS10S12A2M7A2S2fG6G7S2fS6S3cR15S3fR12S59R11S3eA4A4S2fS10S12Z50M8S5bS5aZ2fA2A4A4S5dA3S0S30S9bS5aS15S7R18A1A1A2S31A3VTR;S4fS4dVJAv;S3fR14S59R13S3eA4M9A1R19R12R11A5VFAM;S3dS2fG6G7S2fS6S3cR19G9A4S2fS10S12G8S5bS5aZ30A2A4A4R12A2R10A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Ftp0;Ftp;Frho;Fbd;Ftv;Fk;Fd;FC;FY;FX;").
Proof.
  intros X Y C d k tv bd rho tp tp0 H1 Hwf1 Hd Hs HY Hbase Hfe HXi Hwf HB HRO HXL HC HinC HV.
  apply TR_facts. intros HF.
  eapply TR_pre; [|apply (REENTER C (NDA tv fr_hp bd ANone) (80, VR pQ 47)); [exact HinC | exact (loop_meas_same rho _ 47 48 X C _ _ HF HV ltac:(lia) ltac:(lia) ltac:(lia))]].
  intros w Hw. rewrite <- HC.
  assert (Hw1 : SPA segs (JAv (NDA tv fr_hp bd ANone)) (cm1 X d) rho tp w).
  { unfold cm1, reshapeA. apply (SPA_reshape segs _ rho X 1 _ _ tp w H1); [reflexivity | reflexivity | reflexivity | exact Hwf1 | | exact Hw].
    intros HF'. destruct (slot_rng rho _ d HF' Hd Hs) as (A1 & A2 & A3).
    unfold mid_dst, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite !soff_lit_small by lia. rewrite A2, A3.
    change (bv_unsigned (eval rho (SAlu ALU_ADD d (cmul12 pC)))) with (uval rho (SAlu ALU_ADD d (cmul12 pC))). rewrite A1. unfold uval. lia. }
  pose proof (SPA_axforms segs _ xf_cm rho (cm1 X d) Y tp w HY Hw1) as Hw2.
  apply (JA_shadow_reopen segs HTOP AInv CST XGL ALA HCST HXGL LFSH NPH Kc rho0 (P0_hp CST FB FF) FB FF BX PTrue HKc HBX HNP
           tv fr_hp bd ANone 0%nat 160%positive 0 170%positive hG 4 6 Y (X_hp d k) rho tp w eq_refl ltac:(lia) Hbase ltac:(lia)
           ltac:(change (fs_frame_size 0) with 64; lia) Hfe (xrs_inclb_sound _ _ HXi) Hwf); [|exact Hw2].
  intros Ai rho1 tp1 md1 HF2 HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR. split.
  - exact (siteF Ai rho _ tv fr_hp _ rho1 tp1 md1 HM HF2 HB Hav HP0 HT HTK HN HD HZ HFR HRO).
  - intros r y Hr Hy. left. exact (proj1 (siteX Ai rho _ tv fr_hp (Some 0%nat) _ _ rho1 tp1 md1 HM HF2 HB Hav HP0 HT HTK HBf HFF HN HD HZ HFR HXL) r y Hr Hy).
Qed.
Lemma XH_X_rpk : ltac2:(tb__ "0|1|
S13S2dS4eQ40A1A1M0G0VTR;S4fS4dVJAv;S5cA1S78R3R2A5VFAM;S3dS2fS2eS6S3cA2S2eS10S12A2S2fS6S3cS78S5cA4S2fS10S12Z50S5bS5aZ30A2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. unfold ndJ, ndF, tvL, tv_hp.
  apply (X_cm X_rpk Y_rpk C_mk pD pK _ _ rho tp tp0); [vmr|vmr|vmr|vmr| exact Y_rpk_eq |vmr|vmr|vmr|vmr|vmr|vmr|vmr| exact C_mk_eq | innth 16 | vmr].
Qed.
Lemma XH_X_rpg : ltac2:(tb__ "0|1|
S13S2dS4eQ40A1A1M0G0VTR;S4fS4dVJAv;S5fA1S77R3R2A5VFAM;S3dS2fS2eS6S3cA2S2eS10S12A2S2fS6S3cS77S5fA4S2fS10S12Z50S5bS5aZ30A2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. unfold ndG, ndF, tvG, tv_hp.
  apply (X_cm X_rpg Y_rpg C_mg vDg vKg _ _ rho tp tp0); [vmr|vmr|vmr|vmr| exact Y_rpg_eq |vmr|vmr|vmr|vmr|vmr|vmr|vmr| exact C_mg_eq | innth 17 | vmr].
Qed.

Lemma X_Y_ep : ltac2:(tb__ "0|8|
S6S6S2dS2eS12S12A2A1S2dSa5A1S12S12S13S2dS4eQ40A1A1M0S10G0S10S0S12SdRbA1S18Se6A1A3S0S30SbS32S14S1eSaS94A1S95A2S32S14S19S1fS94A1S18S58S55Z2M1Z3dA2Z1M2A2A1A2S33S14A1A3A3S15S7RcA1A1A2S31A3S0S30SecS5eR9R8A2S9RdA1A2S31A3S0S30S21S7Sd0ReS5eRaR9A2S94Z0M3Z8A5A1A1S31A3S0S30S21S7S63RfRbRaA3A1A1S31A3S0S30S9dS15S7R10A1A1A1S31A3S0S30S9fS15S7R11A1A1A1S31A3S0S30SceS15S7R12A1M4A1R10S59S37S34A1SbaS1aG4A1A6S31A3S0S30ScfVXGL;S15S7R13A1M5A1R11S59S35S34U0A2S1aG5A1SbbS5eRfReA2A8S31A3S0S6S63R14R10RfA3R13A3Sa0S2eS2eS6S3cA2M6S2eS10S12A2M7A2S2fG6G7S2fS6S3cR14S3fR13S59R12S3eA4A4S2fS10S12RbS65A4A4S5dA3S53G3RcA2S53S56S57RdG2A2S55G1Z40A2A2RfA2VTR;S4fS4dVJAv;S3fR16S59R15S3eA4A1R18R12R11A5VFAM;R10RfA2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Frk;Ftp0;Fb;Ftp;Frho;Fk;Fd;Fbd;Ftv;FC;FY;").
Proof.
  intros Y C tv bd d k rho tp b tp0 rk Hbase Hfe HXi Hwf1 Hwf2 HB HFRF HRO HXL HC HinC Hrk Hb.
  eapply TR_pre; [|apply (REENTER C (NDA tv fr_hp bd ANone) (rk, z0)); [exact HinC | rewrite emeas_z0; lia]].
  intros w Hw. rewrite <- HC. unfold epi_state.
  apply (JA_flag_carve segs HTOP AInv CST XGL ALA HCST HXGL LFLAG NPH Kc rho0 (P0_hp CST FB FF) FB FF BX PTrue HKc HBX HNP
           tv fr_hp bd ANone 0%nat 160%positive 0 170%positive (shadow_reopen_stateA Y (X_hp d k) hG 0 8) rho tp w eq_refl ltac:(lia)).
  - exact Hbase.
  - exact Hwf2.
  - intros Ai rho1 tp1 md1 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR. cbn [shadow_reopen_stateA ax_S ss_facts ss_objs ax_X] in HF |- *. split.
    + intros o a Ho Hr. apply in_app_or in Ho as [Ho|[<-|[]]].
      * exact (siteH Ai rho _ tv fr_hp _ rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HN HD HZ HFR HRO o a Ho Hr).
      * right. right. exact (shobj_range_hse hG 160 64 0 8 rho _ a sz_rng ltac:(lia) ltac:(cbn; lia) HF HFRF Hr).
    + exact (proj2 (proj2 (siteX Ai rho _ tv fr_hp (Some 0%nat) _ _ rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HBf HFF HN HD HZ HFR HXL))).
  - apply (JA_shadow_reopen segs HTOP AInv CST XGL ALA HCST HXGL LFSH NPH Kc rho0 (P0_hp CST FB FF) FB FF BX PTrue HKc HBX HNP
             tv fr_hp bd ANone 0%nat 160%positive 0 170%positive hG 0 8 Y (X_hp d k) rho tp w eq_refl ltac:(lia) Hbase ltac:(lia)
             ltac:(change (fs_frame_size 0) with 64; lia) Hfe (xrs_inclb_sound _ _ HXi) Hwf1); [|exact Hw].
    intros Ai rho1 tp1 md1 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR. split.
    + exact (siteF Ai rho _ tv fr_hp _ rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HN HD HZ HFR HRO).
    + intros r y Hr Hy. left. exact (proj1 (siteX Ai rho _ tv fr_hp (Some 0%nat) _ _ rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HBf HFF HN HD HZ HFR HXL) r y Hr Hy).
Qed.
Lemma XH_XN : ltac2:(tb__ "0|1|
S13S2dS4eQ40A1A1M0S10G0S53S56Z28S55Z2Z40A2A2R2A2VTR;S4fS4dVJAv;S7aA1S82R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. unfold ndN, ndF.
  apply (X_Y_ep XN C_epn _ _ pD pK rho tp b tp0 38); [vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr| exact C_epn_eq | innth 22 | lia | lia].
Qed.
Lemma X_fp : ltac2:(tb__ "0|7|
S6S6S6S6S13S2dS4eQ40A1A1M0S10G0S0S36S6A1Se3R8S113A2S35S6R7A2A3S0S30SecS5eS68S69A2M1S9R8A1A2S31A3S0S6S118R9G1A2R8A3S0S12SdR9A1S18Se6A1A3S0S30SbS32S14S1eSaS94A1S95A2S32S14S19S1fS94A1S18S58S55Z2M2Z3dA2Z1A2A1A2S33S14A1A3A3S15S7RaA1A1A2S31A3S0S30SecG1S9RbA1A2S31A3S0S30S21S7Sd0RcG1S94Z0Z8A5A1A1S31A3S0S30S21S7S63RdS68S69A3A1A1S31A3S0S30S9dS15S7ReA1A1A1S31A3S0S30S9fS15S7RfA1A1A1S31A3S0S30SceS15S7R10A1M3A1S6aS59S37S34A1SbaS1aG3A1A6S31A3S0S30ScfVXGL;S15S7R11A1M4A1S6aS59S35S34U0A2S1aG4A1SbbG1A8S31A3S0S6S63R12S68S69A3R11A3Sa0S2eS2eS6S3cA2M5S2eS10S12A2M6A2S2fG5G6S2fS6S3cR12S60A4S2fS10S12Z1aS65A4A4S5dA3S53S56Z1cS55G2Z40A2A2R10A2VTR;S4fS4dVJAv;S60A1R17R13R12A5VFAM;R11R10A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Ftp0;Fb;Ftp;Frho;FC;FY;FZ;FX;").
Proof.
  intros X Z Y C rho tp b tp0 HZ HXZ HY Hbase Hfe HXi Hwf1 Hwf2 HB HFRF HRO HXL HC HinC Hb.
  eapply TR_pre with (P := SPA segs (JAv ndX) Y rho tp).
  { intros w Hw. rewrite <- HY. apply (SPA_x_sub segs); [exact (xrs_inclb_sound _ _ HXZ)|]. exact (SPA_axforms segs _ xf_f rho X Z tp w HZ Hw). }
  unfold ndX, ndF. apply (X_Y_ep Y C tvL [PROG 72 pQ] pD pK rho tp b tp0 26 Hbase Hfe HXi Hwf1 Hwf2 HB HFRF HRO HXL HC HinC ltac:(lia) ltac:(lia)).
Qed.
Lemma XH_X_fp0 : ltac2:(tb__ "0|1|
S13S2dS4eQ40A1A1M0S10G0S53S56Z1cS55Z2Z40A2A2R2A2VTR;S4fS4dVJAv;S60A1S83R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply (X_fp X_fp0 Z_fp0 Y_fp0 C_fp0 rho tp b tp0 Z_fp0_eq); [vmr| exact Y_fp0_eq |vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr| exact C_fp0_eq | innth 23 | exact Hb].
Qed.
Lemma XH_X_fp1 : ltac2:(tb__ "0|1|
S13S2dS4eQ40A1A1M0S10G0S53S56Z1cS55Z2Z40A2A2R2A2VTR;S4fS4dVJAv;S60A1S84R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply (X_fp X_fp1 Z_fp1 Y_fp1 C_fp1 rho tp b tp0 Z_fp1_eq); [vmr| exact Y_fp1_eq |vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr| exact C_fp1_eq | innth 24 | exact Hb].
Qed.

Lemma X_X_rl : ltac2:(tb__ "0|8|
S6S6S6S2dS2eS12S12A2A1S2dSa5A1S13S2dS4eQ40A1A1M0S10G0S10S0S36S6A1Se3RaS32Se4Se5S90A1S33Se4A1A3A2S35S6R9A2A3S0S6SeRaS117S7RaA1M1SacS17U12M2S1aG1A1A3A2A2R9A3S0S30Sd1Pa0PaaS94Z0M3SadS17G2S1aS7RbA1A1A3A5S31A3S0S30SbS32S14S1eSaS94A1S95A2S32S14S19S1fS94A1S18S58S55Z2M4Z3dA2Z1M5A2A1A2S33S14A1A3A3S15S7RcA1A1A2S31A3S0S30S41S16S7RdA1A1S3fRbS59RaS3eA4A2S31A3Sa0S2eS2eS6S3cA2M6S2eS10S12A2M7A2S2fG6G7S2fS6S3cRdS3fRcS33S2eS2eS12S10A2S12A2A1RbS3eA4A4S2fS10S12R6S65A4A4S5dA3S53G3R7A2S53S56S57R8G5A2S55G4Z40A2A2RaA2VTR;S4fS4dVJAv;S3fRfS59ReS3eA4A1R12RdRcA5VFAM;RbRaA2A2F_;F_;F_;F_;F_;F_;F_;F_;Frk;Ftp0;Fb;Ftp;Frho;Fbd;Ftv;FC;FX1;FX;").
Proof.
  intros X X1 C tv bd rho tp b tp0 rk HX1 HC HR Hfe Hnb HinC Hrk Hb.
  apply (TR_pre (fun w => exists rho', SPA segs (JAv (NDA tv [] bd ANone)) C rho' tp w)).
  { intros [tr [ms md]] Hw. pose proof (SPA_axforms segs _ [AXSelect sel_rel] rho X X1 tp _ HX1 Hw) as Hw1.
    exists (rho_absorb rho (skipn 18 (ss_objs (ax_S X1))) (vms md tp ms)). rewrite <- HC.
    change (ax_setS X1 (set_objs (ax_S X1) (firstn 18 (ss_objs (ax_S X1))))) with (drop_lastA X1 (firstn 18 (ss_objs (ax_S X1)))).
    change (@nil (sv * Z * sv)) with (remove_nth 0 fr_hp).
    apply (JA_release_inline segs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eb.Lib_arena_alloc.HTOP_ok AInv CST XGL ALA HCST HXGL LFLAG LFSH NPH Kc rho0 (P0_hp CST FB FF) FB FF BX PTrue HKc HBX HNP
             tv fr_hp bd ANone 0%nat 160%positive 0 170%positive hG X1 (firstn 18 (ss_objs (ax_S X1))) (skipn 18 (ss_objs (ax_S X1))) rho tp tr ms md);
      [reflexivity | lia | symmetry; apply firstn_skipn | exact HR | exact Hfe | exact Hnb | intros A1 A2 _; exact I | exact Hw1]. }
  apply TR_exw. intros rho'. apply (REENTER C (NDA tv [] bd ANone) (rk, z0)); [exact HinC | rewrite emeas_z0; lia].
Qed.
Lemma XH_X_rln : ltac2:(tb__ "0|1|
S13S2dS4eQ40A1A1M0S10G0S53S56Z24S55Z2Z40A2A2R2A2VTR;S4fS4dVJAv;S7aA1S88R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. unfold ndN, ndF. apply (X_X_rl X_rln _ C_rln _ _ rho tp b tp0 34 X_rln_eq); [vmr|vmr|vmr|vmr| innth 25 | lia | lia].
Qed.
Lemma XH_X_rlf0 : ltac2:(tb__ "0|1|
S13S2dS4eQ40A1A1M0S10G0S53S56Z16S55Z2Z40A2A2R2A2VTR;S4fS4dVJAv;S60A1S86R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. unfold ndX, ndF. apply (X_X_rl X_rlf0 _ C_rlf0 _ _ rho tp b tp0 20 X_rlf0_eq); [vmr|vmr|vmr|vmr| innth 26 | lia | lia].
Qed.
Lemma XH_X_rlf1 : ltac2:(tb__ "0|1|
S13S2dS4eQ40A1A1M0S10G0S53S56Z16S55Z2Z40A2A2R2A2VTR;S4fS4dVJAv;S60A1S87R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. unfold ndX, ndF. apply (X_X_rl X_rlf1 _ C_rlf1 _ _ rho tp b tp0 20 X_rlf1_eq); [vmr|vmr|vmr|vmr| innth 27 | lia | lia].
Qed.

Lemma XH_E_sm : ltac2:(tb__ "0|1|
S13S2dS4eQ40A1A1M0S10G0S53S56Z62S55Z2Z40A2A2R2A2VTR;S4fS4dVJAv;S67A1S7dR5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply TR_facts. intros HF.
  apply (smalloc_callT segs AE_A AInv CST XGL ALA HCST HXGL NPH Kc rho0 (P0_hp CST FB FF) FB FF BX PTrue HKc TR TR_facts TR_ex TR_pre TR_callP
           0 E_sm0 s_sm R_sm rho tp nd0 160 170 (FAM b tp0) CSM).
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
    intros Ai ms HF' HP0 Hav HBf HFF HN HD HZ HFR (rho1 & tp1 & md1 & HM) HT HTK. destruct (P0_now rho Hav HP0) as (_ & _ & _ & HC0).
    cbn [nd_tv nd_fr nd0 ND] in HN, HD, HZ, HFR |- *.
    split; [|split].
    + exact (siteP Ai rho _ (tv_hp pi_d pi_k) [] None R_sm rho1 tp1 md1 HM HF' ltac:(vmr) Hav HP0 HT HTK HBf HFF HN HD HZ HFR ltac:(vmr)).
    + exact (proj1 (proj2 (siteX Ai rho _ (tv_hp pi_d pi_k) [] None (ss_objs (ax_S E_sm0)) (ax_X E_sm0) rho1 tp1 md1 HM HF' ltac:(vmr) Hav HP0 HT HTK HBf HFF HN HD HZ HFR ltac:(vmr)))).
    + split; [change (wsub_get s_sm 12) with (SLit 64); rewrite uval_lit by lia; change (fs_frame_size 0) with 64; lia|].
      unfold ffpairs. change (map (fun y : Z * Z * Z => fst y) FF) with (map fst FF). rewrite HC0. cbn. lia.
  -
    intros rho' tp'. rewrite T_sm_eq.
    eapply TR_pre with (P := SPA segs (JAv ndP) T_sm1 rho' tp').
    { intros w Hw. exact (SPA_axforms segs _ [AXSelect sel_sm] rho' T_sm T_sm1 tp' w T_sm1_eq Hw). }
    apply (TR_pre (fun w => exists rho2, SPA segs (JAv ndP) C_pro rho2 tp' w)).
    { intros w Hw.
      destruct (JA_frame_open segs HTOP AInv CST XGL ALA HCST HXGL LFLAG NPH Kc rho0 (P0_hp CST FB FF) FB FF BX PTrue HKc HBX HNP
                  (tv_hp pi_d pi_k) fr_hp (bd_hp pi_n pi_k tI) ANone 0%nat 160 0 170
                  T_sm1 objs_sm1 (X_hp pi_d pi_k) [] rho' tp' w eq_refl ltac:(lia) eq_refl T_sm1_objs T_sm1_X
                  ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) eq_refl ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc)) as (rho2 & _ & Hw2); [| exact Hw |].
      - intros Ai rho1 tp1 md1 HF2 HP0 Hav HM HT HTK HBf HFF HN HDt HZt HFR. rewrite app_nil_r.
        exact (proj1 (siteX Ai rho' _ (tv_hp pi_d pi_k) fr_hp (Some 0%nat) (ss_objs (ax_S T_sm1)) (X_hp pi_d pi_k) rho1 tp1 md1 HM HF2 ltac:(vmr) Hav HP0 HT HTK HBf HFF HN HDt HZt HFR ltac:(vmr))).
      - exists rho2. rewrite app_nil_r in Hw2. rewrite C_pro0_eq in Hw2. rewrite <- C_pro_eq.
        apply (SPA_x_len0 segs (JAv ndP) C_pro0 160 5 rho2 tp' w); [vmr | lia | vmr | exact Hw2]. }
    apply TR_exw. intros rho2. apply (REENTER C_pro ndP (96, z0)); [innth 1 | rewrite emeas_z0; lia].
Qed.

Lemma X_P_ok : ltac2:(tb__ "0|1|
S13S2dS4eQ40A1A1M0S10G0VTR;S4fS4dVJAv;S7cA1S72R4R3A5VFAM;R2R1A2A2Ftp0;Fb;Ftp;Frho;").
Proof. intros. apply POST. innth 1. Qed.
Lemma X_P_fail : ltac2:(tb__ "0|1|
S13S2dS4eQ40A1A1M0S10G0VTR;S4fS4dVJAv;S7bA1S71R4R3A5VFAM;R2R1A2A2Ftp0;Fb;Ftp;Frho;").
Proof. intros. apply POST. innth 0. Qed.

Lemma exits_okT : ltac2:(tb__ "0|3|
S6S3cS2eS10S12A2M0S13S2dS4eQ40A1A1M1G1Sa0S2eS2eS6S3cA2M2G0A2S2fG2G0S2fS6S3cR6R5A4R4A4S8aA3VTR;S4fS4dVJAv;R6A1R7R4R3A5VFAM;S3dS2fG2G0S2fS6S3cR7R6A4R5A4R4A2R2A2A2F_;Ftp0;Ftp;Frho;FrvX;FndX;FX;").
Proof.
  intros X ndX rvX rho tp tp0 Hin. cbn [In exitsH] in Hin.
  destruct Hin as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[]]]]]]]]]]]]]]]]]]]]]; injection H as <- <- <-.
  - apply XH_E_sm. rewrite emeas_z0. lia.
  - apply XH_X_pro. rewrite emeas_z0. lia.
  - apply XH_E_unp.
  - apply XH_E_pc.
  - apply XH_E_da.
  - apply XH_E_vr.
  - apply XH_E_mk.
  - apply XH_E_mg.
  - apply XH_X_rpk.
  - apply XH_X_rpg.
  - apply XH_X_r2k.
  - apply XH_X_r2g.
  - apply XH_XN. rewrite emeas_z0. lia.
  - apply XH_X_rln. rewrite emeas_z0. lia.
  - apply XH_X_fp0. rewrite emeas_z0. lia.
  - apply XH_X_fp1. rewrite emeas_z0. lia.
  - apply XH_X_rlf0. rewrite emeas_z0. lia.
  - apply XH_X_rlf1. rewrite emeas_z0. lia.
  - apply X_P_fail.
  - apply X_P_ok.
Qed.
End X.

Section Safety.
Variable ok : world -> Prop.
Hypothesis Hok : ltac2:(tb__ "0|0|
S4cS4dVKc;Vok;A3").
Hypothesis AC : ltac2:(tb__ "0|0|
S10aS4dS105VAInv;VCST;VXGL;A5").

Theorem handle_p_sum : ltac2:(tb__ "0|0|
S2dS4eQ40A1A1Sb9S4dVok;S4fS4dS45VAInv;VCST;VXGL;VKc;S9aVCST;VFB;VFF;A3VFB;VFF;VBX;S40S67AaS73Vrho0;R1A5SafS4dS93Vrho0;R1Sd5A5A4Ftp0;").
Proof.
  intros tp0.
  eapply triple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_sound_JA segs AInv CST XGL NPH Kc rho0 (P0_hp CST FB FF) FB FF BX PTrue HKc ALA FUEL_hp cutpcs_hp NPH
                (map edropA cutsH) (map edropA exitsH) ok (Q tp0) Hok (ejcertA_jcertA segs NPH _ _ _ _ _ ejcertH_ok))
         with (ndT := nd0); [|left; reflexivity].
       intros X ndX rho tp Hin. apply in_map_iff in Hin as ([[X' nd'] rv] & E0 & Hin). cbn in E0. injection E0 as <- <-.
       apply (exits_okT (triple segs ok) (fun _ _ w => SPfamGTA segs (map nI (map edropA cutsH)) w \/ Q tp0 w)
                (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok) (@triple_ex segs ok) (TRs_pureP segs ok) (call_soundPA3 segs ok)) with (rvX := rv) (tp0 := tp0).
       - intros FBc FFc BXc rho1 tp1 HB0. apply (VNP.vec_reserveN_sum AInv CST XGL ALA HCST HXGL Kc HKc FBc FFc BXc HB0 rho1 ok Hok AC tp1).
       - intros Ai rho1 tp1. apply (aca_stack_malloc _ _ _ _ _ AC 0 ltac:(cbn; tauto)); [exact HKc|]. eapply ok_frameA_of_K; [exact Hok|]. intros r p t m (_ & K & _). exact K.
       - intros Ai rho1 tp1. apply (aca_asan_memcpy _ _ _ _ _ AC); [exact HKc|]. eapply ok_frameA_of_K; [exact Hok|]. intros r p t m (_ & K & _). exact K.
       - intros Cl s R rho1 tp1 nd Q' He Hc Hn Hb Hf Hk.
         apply (pure_callA segs AInv CST XGL NPH Kc rho0 (P0_hp CST FB FF) FB FF BX PTrue HKc ALA ok Cl Pre_pc s R Posts_pc rho1 tp1 nd Q'); try assumption.
         intros rho2 tp2. apply parse_corner_sum; [apply frozen_ok_frameA; exact Hok | apply (frozen_stable NF (ss_next (ax_S Cl)) nd rho1); [apply Pos.leb_le; exact Hn | exact Hb]].
       - intros Cl s R rho1 tp1 nd Q' He Hc Hn Hb Hf Hk.
         apply (pure_callA segs AInv CST XGL NPH Kc rho0 (P0_hp CST FB FF) FB FF BX PTrue HKc ALA ok Cl Pre_da s R Posts_da rho1 tp1 nd Q'); try assumption.
         intros rho2 tp2. apply diag_append_sum; [apply frozen_ok_frameA; exact Hok | apply (frozen_stable NF (ss_next (ax_S Cl)) nd rho1); [apply Pos.leb_le; exact Hn | exact Hb]].
       - intros T nd rv' rho1 tp1 b tp2 HinT _. apply (reenter_cutJA segs AInv CST XGL NPH Kc rho0 (P0_hp CST FB FF) FB FF BX PTrue ok (map edropA cutsH) T nd).
         apply in_map_iff. exists (T, nd, rv'). auto.
       - intros P nd rho1 tp1 b tp2 HinP. apply (exit_postGA segs AInv CST XGL NPH Kc (P0_hp CST FB FF) FB FF BX PTrue ok rho0 tp0 nd Posts_hpJ P). exact HinP.
       - exact Hin. }
  intros w Hw. apply JA_pre_intro. exact Hw.
Qed.
End Safety.

Section Existence.
Hypothesis ACX : ltac2:(tb__ "0|0|
S10bS4dS105VAInv;VCST;VXGL;A5").

Theorem handle_p_sum_ex : ltac2:(tb__ "0|0|
S2dS4eQ40A1A1Sb8S4dS4fS4dS45VAInv;VCST;VXGL;VKc;S9aVCST;VFB;VFF;A3VFB;VFF;VBX;S40S67AaS73Vrho0;R1A5SafS4dS93Vrho0;R1Sd5A5A3Ftp0;").
Proof.
  intros tp0.
  eapply etriple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_complete_JA segs AInv CST XGL NPH Kc rho0 (P0_hp CST FB FF) FB FF BX PTrue HKc ALA FUEL_hp cutpcs_hp NPH cutsH exitsH (Q tp0) ejcertH_ok)
         with (ndT := nd0) (rv := (100, z0)); [|left; reflexivity].
       intros X ndX rv rho tp Hin.
       apply (exits_okT (etriple segs) (fun b _ w => SPfamETA segs (map (enodeIA AInv CST XGL NPH Kc rho0 (P0_hp CST FB FF) FB FF BX PTrue) cutsH) b w \/ Q tp0 w)
                (TRe_facts segs) (TRe_ex segs) (TRe_pre segs) (@etriple_ex segs) (TRe_pureP segs) (call_completePA3 segs)) with (tp0 := tp0).
       - intros FBc FFc BXc rho1 tp1 HB0. apply (VNP.vec_reserveN_sum_ex AInv CST XGL ALA HCST HXGL Kc HKc FBc FFc BXc HB0 rho1 ACX tp1).
       - intros Ai rho1 tp1. apply (acx_stack_malloc _ _ _ _ _ ACX 0 ltac:(cbn; tauto)). exact HKc.
       - intros Ai rho1 tp1. apply (acx_asan_memcpy _ _ _ _ _ ACX). exact HKc.
       - intros Cl s R rho1 tp1 nd Q' He Hc Hn Hb Hf Hk.
         apply (pure_callA_ex segs AInv CST XGL NPH Kc rho0 (P0_hp CST FB FF) FB FF BX PTrue HKc ALA Cl Pre_pc s R Posts_pc rho1 tp1 nd Q'); try assumption.
         intros rho2 tp2. apply parse_corner_sum_ex. apply (frozen_stable NF (ss_next (ax_S Cl)) nd rho1); [apply Pos.leb_le; exact Hn | exact Hb].
       - intros Cl s R rho1 tp1 nd Q' He Hc Hn Hb Hf Hk.
         apply (pure_callA_ex segs AInv CST XGL NPH Kc rho0 (P0_hp CST FB FF) FB FF BX PTrue HKc ALA Cl Pre_da s R Posts_da rho1 tp1 nd Q'); try assumption.
         intros rho2 tp2. apply diag_append_sum_ex. apply (frozen_stable NF (ss_next (ax_S Cl)) nd rho1); [apply Pos.leb_le; exact Hn | exact Hb].
       - intros T nd rv' rho1 tp1 b tp2 HinT Hm. apply (ereenter_cutJA segs AInv CST XGL NPH Kc rho0 (P0_hp CST FB FF) FB FF BX PTrue cutsH T nd rv'); [exact HinT | exact Hm].
       - intros P nd rho1 tp1 b tp2 HinP. apply (eexit_postGA segs AInv CST XGL NPH Kc (P0_hp CST FB FF) FB FF BX PTrue rho0 tp0 nd Posts_hpJ P). exact HinP.
       - exact Hin. }
  intros w Hw. apply JA_pre_intro. exact Hw.
Qed.
End Existence.
End Sum.
End Lib_handle_p_pf.

