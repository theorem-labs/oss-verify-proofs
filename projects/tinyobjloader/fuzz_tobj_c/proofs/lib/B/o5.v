(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Ox.F128_004.   (* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_handle_l_s2 Lib_handle_p Lib_tess_run2d Lib_tess_run2d_ex Lib_tess_polygon_chk o3.

(* [comment removed for export] *)
Module Lib_handle_l_eqs.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "sprop"; "SLit"; "ss_facts"; "ss_objs"; "DUnknown"; "SPUle"; "cell"; "DZero"; "mkCell"; "@Corelib.Init.Datatypes"; "cons"; "nil"; "Some"; "option"; "list"; "app"; "prod"; "pair"; "bool"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "axform"; "AXSelect"; "AXSplit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o5.Lib_handle_l_eqs.VN"; "Pre_vr"; "P_grown"; "P_keep"; "P_fail"; "bdP"; "tv0"; "vN"; "tvP"; "vK"; "vKn"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs"; "lc_k"; "lc_d"; "hG"; "kb"; "NPH"; "bd_vec"; "hF"; "li_d"; "li_k"; "hFL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_l"; "pK"; "X_hl"; "pD"; "E_vr"; "vKg"; "s_v"; "T_sm1"; "vDg"; "C_pro0"; "E_da"; "E_pc"; "R_v"; "T_grown0"; "T_keep0"; "Xk_v"; "E_pc0"; "E_pc1"; "E_unp0"; "PHIN"; "T_da0"; "T_pc0"; "T_sm"; "X_pro"; "X_r2g"; "X_r2k"; "objs_pc0"; "objs_pro"; "objs_sm1"; "optAp"; "pQ"; "slot_facts"; "xf_cm"; "C_mg"; "C_mk"; "C_pre"; "C_pro"; "C_rlg"; "C_rlk"; "C_unp"; "E_da0"; "E_sm0"; "E_vr0"; "R_da"; "R_pc"; "R_sm"; "T_da"; "T_fail0"; "T_grown"; "T_keep"; "T_pc"; "X_rpg"; "X_rpk"; "s_da"; "s_pc"; "s_sm"; "xf_pc"; "xf_tda"; "xf_tpc"; "xf_vr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_subA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bitem"; "bd_subst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_l_s2"; "E_vc"; "s_v2"; "E_da2x"; "R_v2"; "T_grown2_0"; "T_keep2_0"; "Xk_v2"; "C_epf"; "E_vc0"; "E_vc1"; "T_da2"; "X_ok0"; "lcn1"; "objs_vc0"; "sel_rel"; "slot4_facts"; "xf_e8"; "xf_f"; "xf_f2"; "C_ok"; "E_da2"; "R_da2"; "T_fail2"; "T_grown2"; "T_keep2"; "X_e8g"; "X_e8k"; "X_f2a"; "X_f2b"; "X_fp0"; "X_fp1"; "X_rlf"; "X_rlo"; "Y_e8g"; "Y_e8k"; "Y_f2a"; "Y_f2b"; "Y_few"; "Y_fp0"; "Y_fp1"; "Z_f7a"; "Z_f7b"; "s_da2"; "xf_tda2"; "xf_vc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_setX"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "import_tv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "T_afterA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS"; "shadow_release_stateA"; "shobj"; "shadow_reopen_stateA"; "frame_open_stateA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Lib_diag_append"; "P_da"; "Pre_da"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o5.Lib_handle_l_eqs"; "Y_rpg"; "Y_rpk"; "Z_e8g"; "Z_e8k"; "Z_f2a"; "Z_f2b"; "Z_fp0"; "Z_fp1"; "objs_r2g"; "objs_r2k"; "cells_pro"; "cells_r2g"; "cells_r2k"; "cells_unp"; "cells_vc"; "sel_sm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve"; "KLG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ResidualA"; "leaf_matches1A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "fs_frame_size"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "AE_A"; "L_stack_malloc"; "Pre_stack_malloc";
"flagbyte_obj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_parse_corner"; "P_ret"; "Pre_pc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "T_afterA"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAS.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import ResidualA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Lib_scan_double Lib_parse_corner.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_parse_corner OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Lib_diag_append.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs Lib_handle_l Lib_handle_l_s2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_l OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_l_s2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Import ScanDoubleAddr VRAddr RA.ReallocAddr ParseCornerAddr DiagAppendAddr HLAddr.
Close Scope bv_scope.
Open Scope Z_scope.
Module VN. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n9.Lib_vec_reserveN. End VN.

Lemma T_sm_eq : ltac2:(tb__ "0|1|
S0S1Sc3SbfSbdZ1M0A2S5aS68S5eSbeSbdG0A2A5S47A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition sel_sm : list nat := Eval vm_compute in sel_last T_sm 3.
Lemma T_sm1_eq : ltac2:(tb__ "0|0|
S0S12S1A1S19S47SfS1aS1bSb8A1S10S1aA1A3A2S11S1S38A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_sm1_objs : ltac2:(tb__ "0|1|
S0S13S5A1S9S2S38A1A1S14S5S4dSfS5Sc0S31SfScSeS7Z0A1Z1M0S7G0A1A3S10ScA1A3A2S10S5A1A3A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_sm1_X : ltac2:(tb__ "0|1|
S0S13S15S4S4A2M0A1S3S38A1S14G0S33S2fS30S29S28A4SfG0S16S4S4S2eS7SbcZ1A1A1A4S10G0A1A3A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma C_pro0_eq : ltac2:(tb__ "0|0|
S0S1Sa5S38S4dS33S2fS30S29S28A4Pa0SbcZ1A1A5S3aA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma C_pro_eq : ltac2:(tb__ "0|0|
S0S1S9eS3aSfS15S4S4A2S16S4S4S2eS7Z0A1A4S3S3aA1A3A2S55A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition cells_pro : list cell := Eval vm_compute in ob_cells sh_pro.
Lemma X_pro_objs : ltac2:(tb__ "0|0|
S0S13S5A1S9S2S48A1A1S14S5S4cSfS5Sa3S2aZ0Z10Sb3SdA5S10S5A1A3A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma C_pre_eq : ltac2:(tb__ "0|0|
S0S1Sa2S48S4cPa0S10S15S27S27A2A1A4S54A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma C_unp_eq : ltac2:(tb__ "0|0|
S0S1Sa4S43S3S43A1S2aZ4Z6A5S58A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition cells_unp : list cell := Eval vm_compute in ob_cells sh_unp.
Lemma E_pc0_objs : ltac2:(tb__ "0|0|
S0S13S5A1S9S2S41A1A1S14S5S4bSfS5Sa3S2aZ4Z6Sb6SaA5S10S5A1A3A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_pc1_eq : ltac2:(tb__ "0|1|
S0S1Sa2S41S4bPa0SfS15S27S27A2M0S16S27S27Z20ZcA4S10G0A1A3A4S42A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_pc_eq : ltac2:(tb__ "0|0|
S0S12S1A1S19S42S69A2S11S1S3cA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_pc0_eq : ltac2:(tb__ "0|0|
S0S1Sa6S8S2S3cA1A1S6eS67Sc2Sc1S3cS5dA5A2S46A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_pc_eq : ltac2:(tb__ "0|0|
S0S12S1A1S19S46S6bA2S11S1S63A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_da_eq : ltac2:(tb__ "0|0|
S0S12S1A1S19S59SfS1aS1cU0S7N60A1A2S10S1aA1A3A2S11S1S3bA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_da0_eq : ltac2:(tb__ "0|0|
S0S1Sa6S8S2S3bA1A1S6eS66Sa8Sa7S3bS5cA5A2S45A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_da_eq : ltac2:(tb__ "0|0|
S0S12S1A1S19S45S6aA2S11S1S5fA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma E_vr_eq : ltac2:(tb__ "0|0|
S0S12S1A1S19S5bS6cA2S11S1S35A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_keep0_eq : ltac2:(tb__ "0|0|
S0S1Sa1S1dS35S37S3dS1fS40A6S3fA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_fail0_eq : ltac2:(tb__ "0|0|
S0S1Sa1S1dS35S37S3dS20S40A6S60A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_grown0_eq : ltac2:(tb__ "0|0|
S0S1Sa1S1dS35S37S3dS1eS40A6S3eA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_keep_eq : ltac2:(tb__ "0|0|
S0S1S9fS3fS14S6S14S6S50S32A1SfS6SbS7SbbA1S34A2S10S6A1A3A3S8S2S3fA1A1A3A2S62A3"). Proof. reflexivity. Qed.
Lemma T_grown_eq : ltac2:(tb__ "0|0|
S0S1S9fS3eS14S6S50S36A1S8S2S3eA1A1A3A2S61A3"). Proof. reflexivity. Qed.
Lemma imp_keep_tv : ltac2:(tb__ "0|1|
S0S13S15S4S4A2M0A1Sa0S6dS37S1dS1fS35A4S22A2SfG0S16S4S4S34S2bZcS32A2A4S10G0A1A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_keep_bd : ltac2:(tb__ "0|0|
S0S13S6fA1S70S6dS37S1dS1fS35A4S21S23S25A2A2SfS6fS44S4fS32A2SfS6fSb9S32A1S10S6fA1A3A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_fail_tv : ltac2:(tb__ "0|1|
S0S13S15S4S4A2M0A1Sa0S6dS37S1dS20S35A4S22A2SfG0S16S4S4S34S2bZcS32A2A4S10G0A1A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_grown_tv : ltac2:(tb__ "0|1|
S0S13S15S4S4A2M0A1Sa0S6dS37S1dS1eS35A4S24A2SfG0S16S4S4S39S2bZcS36A2A4S10G0A1A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_grown_bd : ltac2:(tb__ "0|0|
S0S13S6fA1S70S6dS37S1dS1eS35A4S21S23S26A2A2SfS6fS44S4fS36A2SfS6fSb9S36A1S10S6fA1A3A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition Y_rpk : axst := Eval vm_compute in optAp (apply_axforms X_rpk xf_cm).
Definition Y_rpg : axst := Eval vm_compute in optAp (apply_axforms X_rpg xf_cm).
Lemma Y_rpk_eq : ltac2:(tb__ "0|0|
S0S12S1A1S19S65S51A2S11S1SaaA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Y_rpg_eq : ltac2:(tb__ "0|0|
S0S12S1A1S19S64S51A2S11S1Sa9A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma C_mk_eq : ltac2:(tb__ "0|0|
S0S1Sa4SaaS33S34S32S29S28A4S2aZ4Z6A5S53A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma C_mg_eq : ltac2:(tb__ "0|0|
S0S1Sa4Sa9S33S39S36S29S28A4S2aZ4Z6A5S52A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition objs_r2k : list sobj := Eval vm_compute in removelast (ss_objs (ax_S X_r2k)).
Definition objs_r2g : list sobj := Eval vm_compute in removelast (ss_objs (ax_S X_r2g)).
Definition cells_r2k : list cell := Eval vm_compute in ob_cells (last (ss_objs (ax_S X_r2k)) O_Wl).
Definition cells_r2g : list cell := Eval vm_compute in ob_cells (last (ss_objs (ax_S X_r2g)) O_Wl).
Lemma X_r2k_objs : ltac2:(tb__ "0|0|
S0S13S5A1S9S2S4aA1A1S14S5Sb2SfS5Sa3S2aZ4Z6Sb5SaA5S10S5A1A3A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma X_r2g_objs : ltac2:(tb__ "0|0|
S0S13S5A1S9S2S49A1A1S14S5Sb1SfS5Sa3S2aZ4Z6Sb4SaA5S10S5A1A3A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma C_rlk_eq : ltac2:(tb__ "0|0|
S0S1Sa2S4aSb2Pa0S10S15S27S27A2A1A4S57A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma C_rlg_eq : ltac2:(tb__ "0|0|
S0S1Sa2S49Sb1Pa0S10S15S27S27A2A1A4S56A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition Z_fp0 : axst := Eval vm_compute in optAp (apply_axforms X_fp0 xf_f).
Definition Z_fp1 : axst := Eval vm_compute in optAp (apply_axforms X_fp1 xf_f).
Lemma Z_fp0_eq : ltac2:(tb__ "0|0|
S0S12S1A1S19S8eS82A2S11S1SafA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Z_fp1_eq : ltac2:(tb__ "0|0|
S0S12S1A1S19S8fS82A2S11S1Sb0A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Y_fp0_eq : ltac2:(tb__ "0|0|
S0S1S9eSafS33S34S32S29S28A4A2S97A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Y_fp1_eq : ltac2:(tb__ "0|0|
S0S1S9eSb0S33S34S32S29S28A4A2S98A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma C_fa0_eq : epi_state Y_fp0 = C_fa0. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma C_fa1_eq : epi_state Y_fp1 = C_fa1. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma Z_f7a_eq : epi_state X_f7a = Z_f7a. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Z_f7b_eq : epi_state X_f7b = Z_f7b. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Z_f7a_ent : ltac2:(tb__ "0|0|
S0S17SbaS2cS99S78A3S18A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Z_f7b_ent : ltac2:(tb__ "0|0|
S0S17SbaS2cS9aS78A3S18A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma C_ok_eq : ltac2:(tb__ "0|0|
S0S1Sa4S7cS3S7cA1S2aZ8Z9A5S84A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_da2x_eq : ltac2:(tb__ "0|0|
S0S12S1A1S19S85SfS1aS1cU0S7N60A1A2S10S1aA1A3A2S11S1S73A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_da2_eq : ltac2:(tb__ "0|0|
S0S1Sa6S8S2S73A1A1S6eS9bSa8Sa7S73S86A5A2S7bA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Y_few_eq : ltac2:(tb__ "0|0|
S0S12S1A1S19S7bS9cA2S11S1S96A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma C_few_eq : epi_state Y_few = C_few. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition cells_vc : list cell := Eval vm_compute in ob_cells sh_ok.
Lemma E_vc0_objs : ltac2:(tb__ "0|0|
S0S13S5A1S9S2S79A1A1S14S5S7eSfS5Sa3S2aZ8Z9Sb7SaA5S10S5A1A3A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_vc1_eq : ltac2:(tb__ "0|1|
S0S1Sa2S79S7ePa0SfS15S27S27A2M0S16S27S27Z40Z4A4S10G0A1A3A4S7aA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_vc_eq : ltac2:(tb__ "0|0|
S0S12S1A1S19S7aS9dA2S11S1S71A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma T_keep2_0_eq : ltac2:(tb__ "0|0|
S0S1Sa1S1dS71S72S74S1fS77A6S76A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_fail2_eq : ltac2:(tb__ "0|0|
S0S1Sa1S1dS71S72S74S20S77A6S87A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_grown2_0_eq : ltac2:(tb__ "0|0|
S0S1Sa1S1dS71S72S74S1eS77A6S75A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_keep2_eq : ltac2:(tb__ "0|0|
S0S1S9fS76S14S6S14S6S80S28A1SfS6SbS7SbbA1S29A2S10S6A1A3A3S8S2S76A1A1A3A2S89A3"). Proof. reflexivity. Qed.
Lemma T_grown2_eq : ltac2:(tb__ "0|0|
S0S1S9fS75S14S6S80S36A1S8S2S75A1A1A3A2S88A3"). Proof. reflexivity. Qed.
Lemma imp_keep2_tv : ltac2:(tb__ "0|1|
S0S13S15S4S4A2M0A1Sa0S6dS72S1dS1fS71A4S22A2SfG0S16S4S4S29S2bZ4S28A2A4S10G0A1A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_keep2_bd : ltac2:(tb__ "0|0|
S0S13S6fA1S70S6dS72S1dS1fS71A4S21S23S25A2A2S2dZ4S7dS28A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_fail2_tv : ltac2:(tb__ "0|1|
S0S13S15S4S4A2M0A1Sa0S6dS72S1dS20S71A4S22A2SfG0S16S4S4S29S2bZ4S28A2A4S10G0A1A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_grown2_tv : ltac2:(tb__ "0|1|
S0S13S15S4S4A2M0A1Sa0S6dS72S1dS1eS71A4S24A2SfG0S16S4S4S39S2bZ4S36A2A4S10G0A1A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_grown2_bd : ltac2:(tb__ "0|0|
S0S13S6fA1S70S6dS72S1dS1eS71A4S21S23S26A2A2S2dZ4S7dS36A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition Z_e8k : axst := Eval vm_compute in optAp (apply_axforms X_e8k xf_e8).
Definition Z_e8g : axst := Eval vm_compute in optAp (apply_axforms X_e8g xf_e8).
Lemma Z_e8k_eq : ltac2:(tb__ "0|0|
S0S12S1A1S19S8bS81A2S11S1SacA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Z_e8g_eq : ltac2:(tb__ "0|0|
S0S12S1A1S19S8aS81A2S11S1SabA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Y_e8k_eq : ltac2:(tb__ "0|0|
S0S1S9eSacS33S34S32S29S28A4A2S93A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Y_e8g_eq : ltac2:(tb__ "0|0|
S0S1S9eSabS33S34S32S39S36A4A2S92A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma C_e8k_eq : epi_state Y_e8k = C_e8k. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma C_e8g_eq : epi_state Y_e8g = C_e8g. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition Z_f2a : axst := Eval vm_compute in optAp (apply_axforms X_f2a xf_f2).
Definition Z_f2b : axst := Eval vm_compute in optAp (apply_axforms X_f2b xf_f2).
Lemma Z_f2a_eq : ltac2:(tb__ "0|0|
S0S12S1A1S19S8cS83A2S11S1SadA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Z_f2b_eq : ltac2:(tb__ "0|0|
S0S12S1A1S19S8dS83A2S11S1SaeA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Y_f2a_eq : ltac2:(tb__ "0|0|
S0S1S9eSadS33S34S32S29S28A4A2S94A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Y_f2b_eq : ltac2:(tb__ "0|0|
S0S1S9eSaeS33S34S32S29S28A4A2S95A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma C_f2a_eq : epi_state Y_f2a = C_f2a. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma C_f2b_eq : epi_state Y_f2b = C_f2b. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma X_rlo_eq : ltac2:(tb__ "0|1|
S0S12S1A1S19S91SfS1aS1bS7fA1S10S1aA1A3A2M0S11S1S4eG0A1A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma X_rlf_eq : ltac2:(tb__ "0|1|
S0S12S1A1S19S90SfS1aS1bS7fA1S10S1aA1A3A2M0S11S1S4eG0A1A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
End Lib_handle_l_eqs.

(* [comment removed for export] *)
Module Lib_handle_p_chk.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs"; "NPH"; "@Corelib.Init.Datatypes"; "bool"; "true"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_p"; "FUEL_hp"; "cutpcs_hp"; "cutsH"; "exitsH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ejcertA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG SymSummary.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA TobjJA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs Lib_handle_p.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_p.
Import ListNotations.
Open Scope Z_scope.

Lemma ejcertH_ok : ltac2:(tb__ "0|0|
S3S1S9S4S0S5S6S0S7S8A7S2A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End Lib_handle_p_chk.

(* [comment removed for export] *)
Module Lib_handle_p_eqs.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "SLit"; "sprop"; "ss_objs"; "ss_facts"; "DUnknown"; "cell"; "DZero"; "SPUle"; "mkCell"; "@Corelib.Init.Datatypes"; "cons"; "nil"; "Some"; "option"; "list"; "app"; "prod"; "pair"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "axform"; "AXSelect"; "AXSplit"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_p"; "E_vr"; "pK"; "s_v"; "pD"; "X_hp"; "T_sm1"; "vKg"; "xf_f"; "C_pro0"; "E_da"; "E_pc"; "R_v"; "T_grown0"; "T_keep0"; "Xk_v"; "epi_state"; "optAp"; "sel_rel"; "E_pc0"; "E_pc1"; "E_unp0"; "PHIN"; "T_da0"; "T_pc0"; "T_sm"; "X_pro"; "X_r2g"; "X_r2k"; "Y_fp0"; "Y_fp1"; "objs_pc0"; "objs_pro"; "objs_sm1"; "pQ"; "slot_facts"; "tvL"; "C_epn"; "C_fp0"; "C_fp1"; "C_mg"; "C_mk"; "C_pre"; "C_pro"; "C_rlg"; "C_rlk"; "C_unp"; "E_da0"; "E_sm0"; "E_vr0"; "R_da"; "R_pc"; "R_sm"; "T_da"; "T_fail0"; "T_grown"; "T_keep"; "T_pc"; "XN"; "X_fp0"; "X_fp1"; "X_rlf0"; "X_rlf1"; "X_rln"; "X_rpg"; "X_rpk"; "s_da"; "s_pc"; "s_sm"; "tvG"; "vDg"; "xf_pc"; "xf_tda"; "xf_tpc"; "xf_vr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_p.VN"; "Pre_vr"; "P_grown"; "P_keep"; "P_fail"; "bdP"; "tv0"; "vN"; "tvP"; "vK"; "vKn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bitem"; "bd_subst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs"; "hG"; "hF"; "pi_d"; "pi_k"; "hFL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_subA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS"; "shadow_release_stateA"; "shobj"; "shadow_reopen_stateA"; "frame_open_stateA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_setX"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "import_tv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "T_afterA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o5.Lib_handle_p_eqs"; "Y_rpg"; "Y_rpk"; "Z_fp0"; "Z_fp1"; "objs_r2g"; "objs_r2k"; "cells_pro"; "cells_r2g"; "cells_r2k"; "cells_unp"; "sel_sm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve"; "KLG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "fs_frame_size"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "AE_A"; "L_stack_malloc"; "Pre_stack_malloc"; "flagbyte_obj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Lib_diag_append"; "P_da"; "Pre_da"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_parse_corner"; "P_ret"; "Pre_pc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "T_afterA"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAS.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import ResidualA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Lib_scan_double Lib_parse_corner.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_parse_corner OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Lib_diag_append.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs Lib_handle_p.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_p.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Import ScanDoubleAddr VRAddr RA.ReallocAddr ParseCornerAddr DiagAppendAddr HPAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma T_sm_eq : ltac2:(tb__ "0|1|
S3S0S98S92S90Z0M0A2S4bS5fS4fS91S90G0A2A5S34A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition sel_sm : list nat := Eval vm_compute in sel_last T_sm 3.
Lemma T_sm1_eq : ltac2:(tb__ "0|0|
S3S12S0A1S17S34SfS18S19S8bA1S10S18A1A3A2S11S0S21A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_sm1_objs : ltac2:(tb__ "0|1|
S3S13S4A1S8S1S21A1A1S14S4S3cSfS4S93S76SfSbSeS6Z0A1Z1M0S6G0A1A3S10SbA1A3A2S10S4A1A3A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_sm1_X : ltac2:(tb__ "0|1|
S3S13S15S5S5A2M0A1S2S21A1S14G0S20S74S75A2SfG0S16S5S5S73S6S8eZ0A1A1A4S10G0A1A3A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma C_pro0_eq : ltac2:(tb__ "0|0|
S3S0S7cS21S3cS20S74S75A2Pa0S8eZ0A1A5S24A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma C_pro_eq : ltac2:(tb__ "0|0|
S3S0S7dS24SfS15S5S5A2S16S5S5S73S6Z0A1A4S2S24A1A3A2S46A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition cells_pro : list cell := Eval vm_compute in ob_cells sh_pro.
Lemma X_pro_objs : ltac2:(tb__ "0|0|
S3S13S4A1S8S1S35A1A1S14S4S3bSfS4S7aS72Z0Z8S87ScA5S10S4A1A3A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma C_pre_eq : ltac2:(tb__ "0|0|
S3S0S79S35S3bPa0S10S15S1bS1bA2A1A4S45A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma C_unp_eq : ltac2:(tb__ "0|0|
S3S0S7bS30S2S30A1S72Z4Z6A5S49A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition cells_unp : list cell := Eval vm_compute in ob_cells sh_unp.
Lemma E_pc0_objs : ltac2:(tb__ "0|0|
S3S13S4A1S8S1S2eA1A1S14S4S3aSfS4S7aS72Z4Z6S8aSaA5S10S4A1A3A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_pc1_eq : ltac2:(tb__ "0|1|
S3S0S79S2eS3aPa0SfS15S1bS1bA2M0S16S1bS1bZ20ZcA4S10G0A1A3A4S2fA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_pc_eq : ltac2:(tb__ "0|0|
S3S12S0A1S17S2fS62A2S11S0S26A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_pc0_eq : ltac2:(tb__ "0|0|
S3S0S8dS9S1S26A1A1S78S5eS97S96S26S4eA5A2S33A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_pc_eq : ltac2:(tb__ "0|0|
S3S12S0A1S17S33S64A2S11S0S54A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_da_eq : ltac2:(tb__ "0|0|
S3S12S0A1S17S4aSfS18S1aU0S6N60A1A2S10S18A1A3A2S11S0S25A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_da0_eq : ltac2:(tb__ "0|0|
S3S0S8dS9S1S25A1A1S78S5dS95S94S25S4dA5A2S32A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_da_eq : ltac2:(tb__ "0|0|
S3S12S0A1S17S32S63A2S11S0S50A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma E_vr_eq : ltac2:(tb__ "0|0|
S3S12S0A1S17S4cS65A2S11S0S1cA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma T_keep0_eq : ltac2:(tb__ "0|0|
S3S0S80S66S1cS1eS27S68S2aA6S29A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_fail0_eq : ltac2:(tb__ "0|0|
S3S0S80S66S1cS1eS27S69S2aA6S51A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_grown0_eq : ltac2:(tb__ "0|0|
S3S0S80S66S1cS1eS27S67S2aA6S28A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_keep_eq : ltac2:(tb__ "0|0|
S3S0S7eS29S14S7S14S7S3eS1dA1SfS7SdS6S8fA1S1fA2S10S7A1A3A3S9S1S29A1A1A3A2S53A3"). Proof. reflexivity. Qed.
Lemma T_grown_eq : ltac2:(tb__ "0|0|
S3S0S7eS28S14S7S3eS22A1S9S1S28A1A1A3A2S52A3"). Proof. reflexivity. Qed.
Lemma imp_keep_tv : ltac2:(tb__ "0|0|
S3S13S15S5S5A2A1S7fS77S1eS66S68S1cA4S6bA2S3fA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_keep_bd : ltac2:(tb__ "0|0|
S3S13S70A1S71S77S1eS66S68S1cA4S6aS6cS6eA2A2SfS70S31S3dS1dA2SfS70S8cS1dA1S10S70A1A3A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_fail_tv : ltac2:(tb__ "0|0|
S3S13S15S5S5A2A1S7fS77S1eS66S69S1cA4S6bA2S3fA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_grown_tv : ltac2:(tb__ "0|0|
S3S13S15S5S5A2A1S7fS77S1eS66S67S1cA4S6dA2S60A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_grown_bd : ltac2:(tb__ "0|0|
S3S13S70A1S71S77S1eS66S67S1cA4S6aS6cS6fA2A2SfS70S31S3dS22A2SfS70S8cS22A1S10S70A1A3A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition Y_rpk : axst := Eval vm_compute in optAp (apply_axforms X_rpk xf_f).
Definition Y_rpg : axst := Eval vm_compute in optAp (apply_axforms X_rpg xf_f).
Lemma Y_rpk_eq : ltac2:(tb__ "0|0|
S3S12S0A1S17S5cS23A2S11S0S82A2A3"). Proof. vm_compute. reflexivity. Qed.
Lemma Y_rpg_eq : ltac2:(tb__ "0|0|
S3S12S0A1S17S5bS23A2S11S0S81A2A3"). Proof. vm_compute. reflexivity. Qed.
Lemma C_mk_eq : ltac2:(tb__ "0|0|
S3S0S7bS82S20S1fS1dA2S72Z4Z6A5S44A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma C_mg_eq : ltac2:(tb__ "0|0|
S3S0S7bS81S20S61S22A2S72Z4Z6A5S43A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition objs_r2k : list sobj := Eval vm_compute in removelast (ss_objs (ax_S X_r2k)).
Definition objs_r2g : list sobj := Eval vm_compute in removelast (ss_objs (ax_S X_r2g)).
Definition cells_r2k : list cell := Eval vm_compute in ob_cells (last (ss_objs (ax_S X_r2k)) O_Wp).
Definition cells_r2g : list cell := Eval vm_compute in ob_cells (last (ss_objs (ax_S X_r2g)) O_Wp).
Lemma X_r2k_objs : ltac2:(tb__ "0|0|
S3S13S4A1S8S1S37A1A1S14S4S86SfS4S7aS72Z4Z6S89SaA5S10S4A1A3A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma X_r2g_objs : ltac2:(tb__ "0|0|
S3S13S4A1S8S1S36A1A1S14S4S85SfS4S7aS72Z4Z6S88SaA5S10S4A1A3A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma C_rlk_eq : ltac2:(tb__ "0|0|
S3S0S79S37S86Pa0S10S15S1bS1bA2A1A4S48A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma C_rlg_eq : ltac2:(tb__ "0|0|
S3S0S79S36S85Pa0S10S15S1bS1bA2A1A4S47A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma C_epn_eq : ltac2:(tb__ "0|0|
S3S0S2bS55S1fS1dA3S40A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition Z_fp0 : axst := Eval vm_compute in optAp (apply_axforms X_fp0 xf_f).
Definition Z_fp1 : axst := Eval vm_compute in optAp (apply_axforms X_fp1 xf_f).
Lemma Z_fp0_eq : ltac2:(tb__ "0|0|
S3S12S0A1S17S56S23A2S11S0S83A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Z_fp1_eq : ltac2:(tb__ "0|0|
S3S12S0A1S17S57S23A2S11S0S84A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Y_fp0_eq : ltac2:(tb__ "0|0|
S3S0S7dS83S20S1fS1dA2A2S38A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Y_fp1_eq : ltac2:(tb__ "0|0|
S3S0S7dS84S20S1fS1dA2A2S39A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma C_fp0_eq : ltac2:(tb__ "0|0|
S3S0S2bS38S1fS1dA3S41A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma C_fp1_eq : ltac2:(tb__ "0|0|
S3S0S2bS39S1fS1dA3S42A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma X_rln_eq : ltac2:(tb__ "0|1|
S3S12S0A1S17S5aSfS18S19S2dA1S10S18A1A3A2M0S11S0S2cG0A1A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma X_rlf0_eq : ltac2:(tb__ "0|1|
S3S12S0A1S17S58SfS18S19S2dA1S10S18A1A3A2M0S11S0S2cG0A1A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma X_rlf1_eq : ltac2:(tb__ "0|1|
S3S12S0A1S17S59SfS18S19S2dA1S10S18A1A3A2M0S11S0S2cG0A1A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
End Lib_handle_p_eqs.

(* [comment removed for export] *)
Module Lib_handle_p_pf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "leafA"; "ax_X"; "g8"; "has_facts"; "la_state"; "ax_base"; "ax_setS"; "mkLeafA"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "or"; "True"; "ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "valuation"; "sprop"; "ss_facts"; "ss_next"; "sobj"; "SLit"; "SPUle"; "holds"; "ss_objs"; "eval"; "sprop_eqb"; "SPEq"; "SVar"; "swf"; "sprop_below"; "sv_below"; "SAlu"; "agree_below"; "obj_range"; "soff"; "cell"; "dflt_writable"; "odefault"; "@Corelib.Init.Datatypes"; "list"; "prod"; "pair"; "bool"; "true"; "cons"; "nat"; "nil"; "Some"; "option"; "None"; "fst"; "andb"; "snd"; "app"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "emeasA"; "ANone"; "NDA"; "PTrue"; "nd_below"; "TPA"; "frinA"; "tvinA"; "JA_pre"; "fbinA"; "ffinA"; "JA"; "JLA"; "frozen"; "nodeIA"; "ok_frameKA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "smatchA"; "stableA"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "pow"; "mul"; "add"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs"; "NPH"; "hG"; "hF"; "tE"; "tL"; "kb"; "tB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_p"; "fr_hp"; "pQ"; "VR"; "ndJ"; "cutsH"; "X_hp"; "ndX"; "epi_state"; "ndG"; "z0"; "nd0"; "pD"; "pK"; "tvL"; "E_da0"; "E_pc0"; "E_unp0"; "E_vr0"; "P_fail"; "P_ok"; "Pre_hp"; "R_v"; "X_r2g"; "X_r2k"; "X_rpg"; "X_rpk"; "ndN"; "nd_fail"; "nd_ok"; "pC"; "xf_f"; "E_sm0"; "E_vr"; "L_sm"; "PD_vr"; "Pre_sm"; "XN"; "X_fp0"; "X_fp1"; "X_pro"; "X_rlf0"; "X_rlf1"; "X_rln"; "Xk_v"; "cmul12"; "exitsH"; "ndP"; "pC1"; "s_v"; "sel_rel"; "slot_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o5.Lib_handle_p_pf"; "P0_hp"; "P0_hp_b"; "vrF"; "DW_rng"; "bF"; "fF"; "@Stdlib.Lists.List"; "In"; "existsb"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "uval"; "bitem"; "BXok_d"; "bd_wpos"; "bxt"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "firstn"; "skipn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_p.HPAddr"; "DW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "entails_frA"; "call_checkA"; "import_postA"; "J_ofPA"; "call_checkPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o1.Lib_builderH_pf"; "extraOH"; "extraXH"; "extraOH_client"; "frozen_stableH"; "payA_sameH"; "siteFH"; "siteHH"; "sitePH"; "siteXH"; "site_pureH"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "call_linkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "topG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS"; "robjs_checkF"; "shadow_reopen_stateA"; "xrs_checkL"; "release_objs_ok"; "shadow_release_stateA"; "shobj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o5.Lib_handle_p_pf.Sum"; "HNPH"; "Posts_hpJ"; "JLh";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "rho_absorb"; "rho_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "tvz"; "T_ok"; "tvd"; "FBx"; "remove_nth"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ny.Lib_builder_pf"; "baseF"; "P0_builder"; "basez"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "SHADOW_OFF"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "jnodeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "axform"; "AXSelect"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "xrs_inclb"; "FFx"; "pclMA"; "PostsC"; "robjs_okF"; "xrs_okF"; "xrs_okL"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "le"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Lib_diag_append"; "Pre_da"; "Posts_da"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o5.Lib_handle_p_pf.VNP"; "P0_vr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_parse_corner"; "Pre_pc"; "Posts_pc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve"; "B32"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA"; "infrFF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "ccount"; "is_shadowZ"; "payA"; "robjs_okA"; "site_okA"; "xrs_okA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAT"; "robjs_checkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "AE_A"; "JL_stack_malloc"; "J_stack_malloc_pre"; "alloc_contractsA"; "alloc_contractsA_ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs"; "vAL"; "vb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_p.VN"; "Pre_vr"; "nd0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o5.Lib_handle_p_pf.Sum.X"; "pure_rule"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double"; "two26"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsSymJump"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_setX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3"; "import_okPA3"; "import_postA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR"; "robjs_okF"; "xrs_ok47"].
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
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAM2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR TobjJAS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAT.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAT.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Lib_scan_double Lib_parse_corner.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_parse_corner OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Lib_diag_append.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ny.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_handle_p.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nn.Lib_vec_reserve_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ny.Lib_builder_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o1.Lib_builderH_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_p OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o5.Lib_handle_p_eqs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o5.Lib_handle_p_chk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Module VNP. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nu.Lib_vec_reserveN_pf. End VNP.
Import ScanDoubleAddr VRAddr RA.ReallocAddr ParseCornerAddr DiagAppendAddr HPAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Definition P0_hp (CST : list (Z * Z)) (FB : list (Z * Z)) (FF : list (Z * Z * Z)) (r : valuation) : Prop := ltac2:(tb__ "0|1|
SdSd3VCST;VFB;VFF;Vr;A4ScS30Sf0Z0S9fS2bS2bS0S0A2M0S0A2G0S35G0S0A2VFF;A4A2U0A3A2").
Lemma P0_hp_b : ltac2:(tb__ "0|2|
S2aS2bS0S0A2M0A1M1G1S2aS2bG0S0A2A1S13S90R4R3R2R1A4Sd3R5R4R3R2A4F_;Fr;FFF;FFB;FCST;").
Proof. intros CST FB FF r [H _]. exact H. Qed.

Definition bF (F : list sprop) : bool := baseF DW F.
Definition fF (F : list sprop) : bool := frameF hG 160 64 F.
Lemma DW_rng : 0 <= DW < 2 ^ 40. Proof. unfold DW. lia. Qed.
Lemma sz_rng : 0 <= 64 < 2 ^ 40. Proof. lia. Qed.

Definition vrF (q : sv) (F : list sprop) : bool := ltac2:(tb__ "0|0|
S36S36S97S14S1dS19Vq;S59A2A1VF;A3S97S14S1dS19S59S5aA2A1VF;A3A2S97S14S1dS19S5aS18S102A1A2A1VF;A3A2").
Lemma VR_val : ltac2:(tb__ "0|3|
S13S2aS14A1S12S0S9eS14S1aR4A1R3A3ScS2dS92R3R4A2S2eA3SdS50Z0M0R3A2S51R3Z40M1A2A2SdScS0S99R7S5fR5R4A2A2S54S53G1S55S99R7S59A2S99R7R5A2A2M2A2R4A2A3SdS50G0G2A2S50G2S52Z2Z1aA2A2A2A2F_;F_;F_;Fa;Fq;FF;Frho;").
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
S13S13S2aS14A1S12S0S0S9eS14S1aR6A1R4A3ScS2dS92R4R5A2S2eA3ScS4bQ40A1M0S1cR7S59A2S1cR8S59A2A3ScG0S1cR8R6A2S1cR9R6A2A3S50Z0M1R6A2S51R7R6A2S51R7Z40A2SdS50G1S99RcS5fRaR9A2A2M2A2S51G2S99RdS5fRaR8A2A2A2A2F_;F_;F_;F_;F_;F_;F_;Fb;Fa;Fq;FF;Frho';Frho;").
Proof.
  intros rho rho' F q a b HF HV H1 H2 Ha Hab Hb.
  assert (EQ : uval rho' (VR q a) = uval rho (VR q a)).
  { unfold uval, VR, kb. cbn [eval]. rewrite H1, H2. reflexivity. }
  rewrite EQ. destruct (VR_val rho F q a HF HV ltac:(lia)) as [-> R1]. destruct (VR_val rho F q b HF HV ltac:(lia)) as [-> _]. lia.
Qed.

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
SbcS13S2aS4bQ40A1A1Sb8OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : alloc_lawsA segs AInv CST.
Hypothesis HCST : ltac2:(tb__ "0|0|
S0SfcVCST;R1A2SdS50Z0R2A2S51R2Sd6A2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S0SfcVXGL;R1A2SdS50Z0R2A2S51R2Sd6A2A2F_;Fa;").
Hypothesis LFLAG : law_flag_stmt AInv.
Hypothesis LFSH : law_fshadow_stmt AInv.
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S2aS2bS2bS0S0A2S0A2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 5 BX.
Let HNP : NP_okA NF := NP_okA_intro NF eq_refl.
Variable rho0 : valuation.
Let HTOP : InitState.segs_top segs <= IMG_HI := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nn.Lib_arena_alloc.HTOP_ok.
Lemma HNPH : (NF <= NPH)%positive. Proof. unfold NF, NPH. lia. Qed.

Definition JLh (nd : ndesc) : jpostA := ltac2:(tb__ "0|0|
S46VAInv;VCST;VXGL;VKc;S90VCST;VFB;VFF;A3VFB;VFF;VBX;S3dVnd;Aa").
Definition Posts_hpJ : list (axst * jpostA) := ltac2:(tb__ "0|1|
S2fS2bS2Sa7A2M0S2cS2Sa7S6fSc7S78A1A4S2fG0S2cS2Sa7S70Sc7S79A1A4S31G0A1A3A3").
Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S45VAInv;VCST;VXGL;S56VKc;Vrho0;S90VCST;VFB;VFF;A3VFB;VFF;VBX;S3dVnd;Ac").
Let nI : ltac2:(tb__ "0|0|
S2bS2S39A2Sd8Fn;") := ltac2:(tb__ "0|0|
S48VAInv;VCST;VXGL;S56VKc;Vrho0;S90VCST;VFB;VFF;A3VFB;VFF;VBX;S3dAb").
Let Q (tp0 : list word) : assn := ltac2:(tb__ "0|0|
Sa8S4aS56Vrho0;Vtp0;Sc6A5").

Let siteP : ltac2:(tb__ "0|0|
SbcS13S2aS14A1S2aS2bS12S12A2A1S2aS2bS2bS12S0A2S12A2A1S33S30A1S2aS17A1S13S2aS4bQ40A1A1Sb8VAInv;RaR3R2R1A4S9eS14S1aRaA1R9A3ScS2dSd2Sa2RaA2S2eA3SbaS56Vrho0;RcA3S90VCST;VFB;VFF;Vrho0;A4S3fVrho0;RfA2ScdRfSbeSbdR10A1A1A2S43VFB;R11A2S44VFF;R12A2S41VFB;R13R12R10A4SceR13R11A2SccR14R12A2S40VFF;R16R15R12A4ScS2dSf6R15R14R13R12SaeR11A6S2eA3Sf3VCST;R18S34S0A1R17R12A5F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FR;Fskip;Ffr;Ftv;Ffacts;Frho;FAi;") := ltac2:(tb__ "0|0|
Sb5VAInv;VCST;VALA;S56Sc5VFB;VFF;Vrho0;S90VCST;VFB;VFF;A3S91VCST;VFB;VFF;A3Sa2S93Ac").
Let siteF : ltac2:(tb__ "0|0|
SbcS13S2aS14A1S2aS2bS12S12A2A1S2aS2bS2bS12S0A2S12A2A1S2aS17A1S13S2aS4bQ40A1A1Sb8VAInv;R9R3R2R1A4S9eS14S1aR9A1R8A3ScS2dSd2Sa2R9A2S2eA3SbaS56Vrho0;RbA3S90VCST;VFB;VFF;Vrho0;A4S3fVrho0;ReA2ScdReSbeSbdRfA1A1A2S41VFB;R10RfRdA4SceR10ReA2SccR11RfA2S40VFF;R13R12RfA4ScS2dSbfR12R11R10S34S30A1SaeRfA6S2eA3S108VCST;Vrho0;VFB;VFF;R14R12R11R10A8F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FR;Ffr;Ftv;Ffacts;Frho;FAi;") := ltac2:(tb__ "0|0|
Sb3VAInv;VCST;VALA;S56Sc5VFB;VFF;Vrho0;S90VCST;VFB;VFF;A3S91VCST;VFB;VFF;A3Sa2S93Ac").
Let siteH : ltac2:(tb__ "0|1|
SbcS13S2aS14A1S2aS2bS12S12A2A1S2aS2bS2bS12S0A2S12A2A1S2aS17A1S13S2aS4bQ40A1A1Sb8VAInv;R9R3R2R1A4S9eS14S1aR9A1R8A3ScS2dSd2Sa2R9A2S2eA3SbaS56Vrho0;RbA3S90VCST;VFB;VFF;Vrho0;A4S3fVrho0;ReA2ScdReSbeSbdRfA1A1A2S41VFB;R10RfRdA4SceR10ReA2SccR11RfA2S40VFF;R13R12RfA4ScS2dSbfR12R11R10S34S30A1SaeRfA6S2eA3S17S0S96S17R2R12A3SdS50S35S0S0S25R17R3A2M0A3R2A2S51R2S37S0S0G0A3A2A2SfSdeVCST;Vrho0;ScfVFB;R18R16A3SddVFF;R18R15A3R3A5SfSdS50Z0R3A2S51R3Sd6A2A2Sf1R3A1A2A2F_;F_;Fa;Fo;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FR;Ffr;Ftv;Ffacts;Frho;FAi;") := ltac2:(tb__ "0|0|
Sb4VAInv;VCST;VALA;S56Sc5VFB;VFF;Vrho0;S90VCST;VFB;VFF;A3S91VCST;VFB;VFF;A3Sa2S93Ac").
Let siteX : ltac2:(tb__ "0|4|
SbcS13S2aS14A1S2aS2bS12S12A2A1M0S2aS2bS2bS12S0A2S12A2M1A1M2S33S30A1M3S2aS17A1G0S13S2aS4bQ40A1A1Sb8VAInv;RbR3R2R1A4S9eS14S1aRbA1RaA3ScS2dSd2Sa2RbA2S2eA3SbaS56Vrho0;RdA3S90VCST;VFB;VFF;Vrho0;A4S3fVrho0;R10A2ScdR10SbeSbdR11A1A1A2S43VFB;R12A2S44VFF;R13A2S41VFB;R14R13R11A4SceR14R12A2SccR15R13A2S40VFF;R17R16R13A4ScS2dSc1VXGL;R16R15R14R13R12SafR11A8S2eA3SdSe2VCST;VXGL;Vrho0;VFB;VFF;R18R16G3G2Lskip;R14S30Sd0G1R1R16A3Li;R15X33x2R12A9SdSf5VCST;VXGL;R19S34S0A1R18R12A6S109R18R12A2A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FX;Fobjs;Fskip;Ffr;Ftv;Ffacts;Frho;FAi;") := ltac2:(tb__ "0|0|
Sb6VAInv;VCST;VXGL;VALA;VHCST;VHXGL;S56Sc5VFB;VFF;Vrho0;S90VCST;VFB;VFF;A3S91VCST;VFB;VFF;A3Sa2S93Af").
Let site_pure : ltac2:(tb__ "0|2|
S2Sc8S2aS17A1S13S2aS2bS12S12A2A1S2aS2bS2bS12S0A2S12A2A1S2aS9aA1ScS2dSd2Sa2S15S3R7A1A1A2S2eA3ScS2dSf6S15S3R8A1A1R4R3S34S30A1M0SaeR6A6S2eA3ScS2dSc1VXGL;S15S3R9A1M1A1R5R4G0S1bG1A1SafS5R9A1A8S2eA3Sf4VAInv;VCST;VXGL;S56Vrho0;S90VCST;VFB;VFF;A3VFB;VFF;RaR9R8R7S3cR6R5R4S3bA4S34S0A1SbcSd1S10L_;L_;AfF_;F_;F_;Fbd;Ffr;Ftv;Frho;FR;Fs;FE;") := ltac2:(tb__ "0|0|
Sb7VAInv;VCST;VXGL;VALA;VHCST;VHXGL;S56Sc5VFB;VFF;Vrho0;S90VCST;VFB;VFF;A3S91VCST;VFB;VFF;A3Sa2S93Af").
Let payA_same : ltac2:(tb__ "0|1|
S2aS14A1S2aS9aA1ScS2dS9cR1A1S2eA3Sf2S56Vrho0;S90VCST;VFB;VFF;A3R3S18Z0M0A1G0R2R2A8F_;Fbd;Ffacts;") := ltac2:(tb__ "0|0|
Sb2S56Vrho0;S90VCST;VFB;VFF;A3A3").
Let frozen_stable : ltac2:(tb__ "0|0|
S1S1S39S13Se4S56R3A2ScS2dS3eR4R3A2S2eA3S4fS4aR6S47VAInv;VCST;VXGL;S56VKc;Vrho0;S90VCST;VFB;VFF;A3VFB;VFF;VBX;S3dR4R3AdA3F_;F_;Frho;Fnd;Fm;Fn;") := ltac2:(tb__ "0|0|
Sb1VAInv;VCST;VXGL;VALA;S56VKc;VHKc;VFB;VFF;VBX;Vrho0;S90VCST;VFB;VFF;A3Ac").
Let extra_client : ltac2:(tb__ "0|1|
S13S17S0S2aS2bS12S12A2A1S2aS2bS2bS12S0A2S12A2A1Sd4Sa2R5A2SbaS56Vrho0;R6A3S90VCST;VFB;VFF;Vrho0;A4ScS2dSaeR7A1S2eA3SdS50S35S0S0S25R9R8A2M0A3R7A2S51R7S37S0S0G0A3A2A2SdeVCST;Vrho0;ScfVFB;RaR7A3SddVFF;RaR6A3R8A5F_;F_;F_;F_;F_;Ffrs;Fkept;Fa;Fo;Frho;") := ltac2:(tb__ "0|0|
Sb0VCST;S56Sc5VFB;VFF;Vrho0;S90VCST;VFB;VFF;A3S91VCST;VFB;VFF;A3Sa2A9").

Lemma P0_now : ltac2:(tb__ "0|2|
S13SbaS56Vrho0;R1A3S90VCST;VFB;VFF;Vrho0;A4SdS0SdS50S99R4S5cA2M0R1A2S51R1S54G0S99R4S5aA2A2A2A2SdeVCST;Vrho0;VFB;VFF;R2A5F_;Fa;SdSefVFF;S99R3SfeA2Z518A3SdSefVFF;S99R3SfdA2Z30A3ScS30Sf0Z0S9fS2bS2bS0S0A2M1S0A2G1S35G1S0A2VFF;A4A2U0A3A2A2A2F_;F_;Frho;").
Proof.
  intros rho Hav HP. destruct (P0b_nowH CST NPH HNPH FB FF rho0 (P0_hp CST FB FF) (P0_hp_b CST FB FF) rho Hav HP) as (A & B & C).
  destruct HP as [_ D]. auto.
Qed.

Lemma tvz_kd : ltac2:(tb__ "0|2|
S13S12S12SccR3S2fS2bS12S12A2M0S2cS12S12R2S5bZcR1A2A4S31G0A1A3A2S50S99R4R2A2SedA2SeScS0S99R5R3A2Z0M1A3A1SeScS0S99R6R5A2G1A3A1F_;F_;F_;Fk;Fd;Frho;").
Proof.
  intros rho d k HZ HK Hk Hd. apply Forall_inv in HZ. unfold tnz, tvv in HZ. cbn [fst snd] in HZ. unfold uval in Hd, Hk, HK.
  specialize (HZ ltac:(intros H; exact (H Hd))). unfold B32 in HK.
  pose proof (uval_mul_lit rho 12 k ltac:(lia) ltac:(unfold uval; lia)) as E12. unfold uval, kb in E12. unfold kb in HZ. rewrite E12 in HZ. lia.
Qed.

Lemma slot_holds : ltac2:(tb__ "0|1|
S13S2aS14A1S12S9eS14S1aR3A1R2A3ScS2dS97S14S1dS19S8cR2A2A1R3A3S2eA3ScS2dS97S14S1dS19R3S18SedA1M0A2A1R4A3S2eA3ScS2dS97S14S1dS19S7aR4A2A1R5A3S2eA3ScS2dS97S14S1dS19S5bZcR5A2G0A2A1R6A3S2eA3S9eS14S1aR8A1S8fR6A1A3F_;F_;F_;F_;F_;Fk;FF;Frho;").
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
S13S2aS14A1S9eS14S1aR2A1R1A3ScS2dS95R2A1S2eA3ScS0S99R4S23Se7S58S18Z20M0A1A3A2S54S99R4S58A2G0A2A3F_;F_;FF;Fr;").
Proof. intros r F HF HFR. unfold hF. apply (frame_off_rng hG 160 64 32 r F sz_rng ltac:(lia) HF HFR). Qed.
Lemma slot_rng : ltac2:(tb__ "0|3|
S13S2aS14A1S12S9eS14S1aR3A1R2A3ScS2dS97S14S1dS19R2S18Z800000000000A1A2A1R3A3S2eA3ScS2dS97S14S1dS19S89S7aA1M0S18SedA1A2A1R4A3S2eA3SdScS0S99R6S23Se7R4G0A3A2S54S99R6R4A2S99R6G0A2M1A2A3SdScS0S26R6G0A2G1A3ScS0S26R6S23Se7G0S18ZcM2A1A3A2S54G1G2A2A3A2A2F_;F_;F_;Fd;FF;Fr;").
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
S0S2aS4bQ40A1A1Sa3F_;F_;").
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S4dS2S13S2aS4bQ40A1A1Sa3S9eS14S1aR3A1S15S3R4A1A1A3VTR;S4cS4aR6R5R4R3A5R2A2M0F_;G0F_;FQ;Ftp;Frho;FS;FJ;").
Hypothesis TR_ex : forall (T : Type) (J : T -> jpredA) S rho tp (Q : assn),
  (forall x, TR (SPA segs (J x) S rho tp) Q) -> TR (SPA segs (fun r p t m => exists x, J x r p t m) S rho tp) Q.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
Sa3Sa3Sa3Sa4R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_exw : forall (T : Type) (P : T -> assn) (Q : assn), (forall a, TR (P a) Q) -> TR (fun w => exists a, P a w) Q.
Hypothesis TR_pureP : ltac2:(tb__ "0|1|
Sa3OSa3Sa4R4R1A1R4F_;Fw;R3VTR;R5R3A2M0F_;G0F_;F_;FQ;FX;FP;").
Hypothesis TR_callP : ltac2:(tb__ "0|5|
S4dS4dS2S2Sc8S2aS17A1M0S2aS2bS2Sa7A2M1A1S2aS2bS12S12A2M2A1Sa3S13S2aS4bQ40A1A1M3G2S96G2R1R5A3S96G2R2S5RbA1A3F_;Fr;ScS33G0A1Sa9RaR9R8A3S32G0R7A2A3ScS2dSadRbRaR9R8S9fG1S2S35S2Sa7A2R7A4A5S2eA3S13G3VTR;S4cS4aRfRdR2R1A5Sa8S4aS16S3RdA1A1R2R1RaA5A2Ftp1;Frho1;S2aSb9A1M4Sd1Sb8S4eS4aR9R8R10S2cG4Se5R3Se6R2R1A2A4A5R13RaR9R4R2A4R13ScaSc9RbRfScbR3RaR4A3A3R10A2RaR5R3A4F_;F_;Fmd;Fms;Ftr;S2Sa7G4Sd1Sb8S13G3G4Sd1Sb8S96G1S2cS2Sa7RaR9A4R14A3S4eS4aR12R11R19S2cG4Se5R9Se6R8R7A2A4A5R1cR13R12RaR8A4SbaS16S3R1aA1A1ScaSc9R14R18ScbR9R13RaA3A3R19A2R8A3S4eS4aR9R8ReS2cG4Se5R7Se6R6R5A2A4A5ReScaSc9R16R1aScbRbR15RcA3A3R1bA2R15RaR9R8R6A6SdS106R17ScbRcR16RdA3R1bR1cR1dR10R1eR19RbA9S13SbbR18ScbRdR17ReA3R1cR1dS3R1eA1S3R1fA1S3R11A1R1RcA9VTR;S4cS4aSacR11ScaSc9R19R1dScbReR18RfA3A3R1eA2R18RdRcA5S107R1eR1fR12R20R1dR1bA6R2RcA5R1aA2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S4cS4aR11RfR8R7A5R9A2F_;F_;F_;F_;F_;F_;Ftp;Frho;FQ;FXk;FPosts;FR;Fs;FPre;FC;FJp;FJ;").
Hypothesis CVRES : ltac2:(tb__ "0|1|
S2aS2bS0S0A2M0A1S2aS2bG0S0A2A1S9dS13S2aS4bQ40A1A1S9bZ3R3A2VTR;S4cS4aS42VAInv;VCST;VXGL;VKc;SeaR6R5A2R6R5R4S3dS100AaSffR3R2A5Sa8S4aSeeR3R2SdfVAInv;VCST;VXGL;VKc;SeaS3dS7fR6R5R4AaA5A2F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Hypothesis CSM : ltac2:(tb__ "0|2|
SbcS13S2aS4bQ40A1A1VTR;S4cS4aSf9VAInv;Z0M0R3VKc;A4S80R2R1A5Sa8S4aSeeR2R1S2fS2bS2Sa7A2M1S2cS2Sa7S7eSf8VAInv;VCST;VXGL;G0R3VKc;A6A4S31G1A1A3A5A2Ftp1;Frho1;FAi;").

Hypothesis CALL_pc : ltac2:(tb__ "0|2|
S2Sc8S2aS17A1M0S13S2aS4bQ40A1A1S39Sa3ScS33G0A1Sa9R7SebR6A3S32G0R5A2A3ScS2dSaaR8SebR7R6S9fS4S2S8SecA4A5S2eA3ScS2dSe3S56S16S3R9A1A1A2S2eA3ScS2dS3eS16S3RaA1A1R5A2S2eA3ScS2dS98S14S21S16S3RbA1M1A1A1S15G1A1A3S2eA3S4S13S96S4R2SecA3S24S16S3RfA1A1RcR2A3VTR;S4cS4aVJAv;RbA1Sd7S15S3R10A1A1SabRfSebS8R4A1R10ReA5A2R3RcA5RaA2F_;F_;Frho';FL;VTR;S4cS4aVJAv;R8A1RdRaR9A5R7A2F_;F_;F_;F_;F_;F_;FQ;Fnd;Ftp;Frho;FR;Fs;FCl;").
Hypothesis CALL_da : ltac2:(tb__ "0|2|
S2Sc8S2aS17A1M0S13S2aS4bQ40A1A1S39Sa3ScS33G0A1Sa9R7Se8R6A3S32G0R5A2A3ScS2dSaaR8Se8R7R6S9fS4S2S8Se9A4A5S2eA3ScS2dSe3S56S16S3R9A1A1A2S2eA3ScS2dS3eS16S3RaA1A1R5A2S2eA3ScS2dS98S14S21S16S3RbA1M1A1A1S15G1A1A3S2eA3S4S13S96S4R2Se9A3S24S16S3RfA1A1RcR2A3VTR;S4cS4aVJAv;RbA1Sd7S15S3R10A1A1SabRfSe8S8R4A1R10ReA5A2R3RcA5RaA2F_;F_;Frho';FL;VTR;S4cS4aVJAv;R8A1RdRaR9A5R7A2F_;F_;F_;F_;F_;F_;FQ;Fnd;Ftp;Frho;FR;Fs;FCl;").
Hypothesis REENTER : ltac2:(tb__ "0|4|
S2S39S2bS0S12A2M0S13S2aS4bQ40A1A1M1S0G1S96S2bS2bS2S39A2M2G0A2S2cG2G0S2cS2S39R7R6A4R5A4S61A3SdS50Z0S3aS2cG2G0S2cS2S39R8R7A4R6A4R5A2M3A2S51G3R3A2A2VTR;S4cS4aVJAv;R8A1R9R6R5A5VFAM;R4R3A2A2F_;F_;Ftp0;Fb;Ftp;Frho;Frv;Fnd;FT;").
Hypothesis POST : ltac2:(tb__ "0|1|
S2S39S13S2aS4bQ40A1A1M0S0G0S96S2bS2Sa7A2S2cS2Sa7R6Sc7R5A1A4Sc6A3VTR;S4cS4aVJAv;R6A1R7R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;Fnd;FP;").

Ltac meas := unfold emeasA; cbn [eda_rank eda_var fst snd z0 eval]; rewrite lit_unsigned; cbn; lia.

Ltac vmr := first [ lazymatch goal with |- @eq ?T ?t ?v => tryif first [ has_evar t | has_evar v ] then fail else vm_cast_no_check (@eq_refl T v) end
                  | vm_compute; reflexivity ].
Tactic Notation "innth" integer(n) := cbn [In cutsH exitsH Posts_hpJ PD_vr]; do n right; left; reflexivity.

Lemma loop_meas : ltac2:(tb__ "0|5|
S13S13S2aS14A1S1S0S0S2S2S39S39S9eS14S1aRaA1R8A3ScS2dS92S5eR9A2S2eA3SbaR9RcRbA3ScS2dS22RaS59A2S2eA3ScS2dS22RbS5eA2S2eA3S50Z0M0RbA2S51RcRbA2S51RcZ40A2SdS50G0S3aS2cS2bS2S39A2M1S2bS0S12A2M2S2cS2S39RbR9A4S2cS0S12Z50M3S5fS5eReA2A4A4R11A2M4A2S51G4S3aS2cG1G2S2cS2S39RcRaA4S2cS0S12G3S5fS5eRdA2A4A4R12A2A2A2F_;F_;F_;F_;F_;F_;F_;F_;FndT;FndX;FT;FX;Fb;Fa;Fn;FF;Frho';Frho;").
Proof.
  intros rho rho' F n a b X T ndX ndT HF HV Hag HbE HbQ Ha Hab Hb. unfold emeasA. cbn [eda_rank eda_var fst snd].
  pose proof (VR_meas rho rho' F pQ a b HF HV (eq_sym (eval_agree_vals n rho rho' tE Hag HbE)) (eq_sym (eval_agree_vals n rho rho' pQ Hag HbQ)) Ha Hab Hb) as M.
  unfold uval in M. lia.
Qed.
Lemma loop_meas_same : ltac2:(tb__ "0|5|
S13S2aS14A1S0S0S2S2S39S39S9eS14S1aR8A1R7A3ScS2dS92S5eR8A2S2eA3S50Z0M0R8A2S51R9R8A2S51R9Z40A2SdS50G0S3aS2cS2bS2S39A2M1S2bS0S12A2M2S2cS2S39R8R6A4S2cS0S12Z50M3S5fS5eRbA2A4A4RdA2M4A2S51G4S3aS2cG1G2S2cS2S39R9R7A4S2cS0S12G3S5fS5eRaA2A4A4RdA2A2A2F_;F_;F_;F_;F_;FndT;FndX;FT;FX;Fb;Fa;FF;Frho;").
Proof.
  intros rho F a b X T ndX ndT HF HV Ha Hab Hb. unfold emeasA. cbn [eda_rank eda_var fst snd].
  pose proof (VR_meas rho rho F pQ a b HF HV eq_refl eq_refl Ha Hab Hb) as M. unfold uval in M. lia.
Qed.

Lemma X_reopen : ltac2:(tb__ "0|7|
S2S2S2aS2bS12S12A2A1S2aS9aA1S0S0S13S2aS4bQ40A1A1M0S0G0S2bS0S12A2M1ScS12S9RbA1S18Sd5A1A3S50Z0M2R8A2SdS50R9R8A2S50R8Z8A2A2ScS2dS7S2fS14S1eS6S57A1S58A2S2fS14S19S1fS57A1S18S55S52Z2Z3dA2Z1A2A1A2S31S14A1A3A3S15S3ReA1A1A2S2eA3ScS2dS20S3Sc0RfS5RfA1S57RbRaA5A1A1S2eA3ScS2dS94S15S3R10A1A1A1S2eA3ScS2dSbfS15S3R11A1M3A1RfS5dS34S30A1SaeS1bG3A1A6S2eA3ScS2dSc1VXGL;S15S3R12A1M4A1R10S5dS32S30U0A2S1bG4A1SafS5R12A1A8S2eA3ScS2Sc0R13S5R13A1S57RfReA5R12A3S96S2bS2bS2S39A2M5G1A2S2cG5G1S2cS2S39R13S3cR12S5dR11S3bA4A4RaA4S61A3SdS50G2S3aS2cG5G1S2cS2S39R14S3cR13S5dR12S3bA4A4RbA4RfA2M6A2S51G6RdA2A2VTR;S4cS4aVJAv;S3cR14S5dR13S3bA4A1R16R10RfA5VFAM;ReRdA2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Frv;Ftp0;Fb;Ftp;Frho;Fk2;Fk1;Fbd;Ftv;FC;FA;").
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
S13S2aS4bQ40A1A1M0G0VTR;S4cS4aVJAv;S60A1S6dR3R2A5VFAM;S3aS2cS2bS2S39A2S2bS0S12A2S2cS2S39S6dS60A4S2cS0S12Z50S5fS5eZ3bA2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_facts. intros HF. unfold ndJ, ndF.
  apply (X_reopen E_unp0 C_unp tvL (bd_hpN pK pQ) 4 6 rho tp _ tp0 (80, VR pQ 58) eq_refl ltac:(lia) ltac:(lia));
    [vmr|vmr|vmr|vmr|vmr| exact C_unp_eq | innth 7 | exact (loop_meas_same rho _ 58 59 E_unp0 C_unp _ _ HF ltac:(vmr) ltac:(lia) ltac:(lia) ltac:(lia))].
Qed.

Lemma reenter_abs : ltac2:(tb__ "0|6|
S2S39S2bS0S12A2M0S13S2aS4bQ40A1M1A1M2S0G2Sa3S96S2bS2bS2S39A2M3G0A2S2cG3G0S2cS2S39R8R7A4R6A4S61A3Sa4R3R1A1S11S13S13SdS12ScG1S1cR2R1A2M4S1cRaR1A2A3Fe;S4cS4aVJAv;RbA1RcR1R8R3A6A2Lrho';A2F_;Fw;S13S12ScG1G4S1cR9R1A2A3Fe;SdS50Z0S3aS2cG3G0S2cS2S39RcRbA4RaA4R2A2M5A2S51G5R7A2A2F_;Frho';VTR;R4VFAM;R6R5A2A2F_;F_;F_;FP;Ftp0;Fb;Ftp;Frho;Frv;Fnd;FC;").
Proof.
  intros C nd rv rho tp b tp0 P HinC HP Hm. eapply TR_pre; [exact HP|]. apply TR_exw. intros rho'.
  apply (TR_pureP _ (forall e, eval rho' e = eval rho e)); [intros w [HE _]; exact HE|]. intros HE.
  eapply TR_pre; [intros w [_ Hw]; exact Hw|]. apply (REENTER C nd rv); [exact HinC | exact (Hm rho' HE)].
Qed.

Lemma X_release : ltac2:(tb__ "0|7|
S2S2S2aS17A1M0S0S0S2aS27A1S29S2aS2bS12S12A2A1S2aS9aA1S13S2aS4bQ40A1M1A1M2S0G2S2bS0S12A2M3ScS12S9ReA1S18Sd5A1A3S50Z0M4RcA2SdS50RdRcA2S50RcZ8A2A2ScS2dS28RbA1S2eA3ScG0S1bS3R12A1A1S38S17R10S2fS17Sc4S57RfReRdRcA5S31S17A1A3A3A3ScS2dS7S2fS14S1eS6S57A1S58A2S2fS14S19S1fS57A1S18S55S52Z2Z3dA2Z1A2A1A2S31S14A1A3A3S15S3R13A1A1A2S2eA3ScS2dS3eS16S3R14A1A1S3cRdS5dRcS3bA4A2S2eA3ScS2dS94S15S3R15A1A1A1S2eA3ScS2dSbfS15S3R16A1A1RfS5dS34S30A1SaeR14A6S2eA3ScS2Sc3R17R15Pa0S31S2bS0S0A2A1A4R16A3S96S2bS2bS2S39A2M5G3A2S2cG5G3S2cS2S39R17S3cR11S5dR10S3bA4A4RbA4S61A3S13S12ScG1S1cR2R1A2S1cR12R1A2A3Fe;SdS50G4S3aS2cG5G3S2cS2S39R1aS3cR14S5dR13S3bA4A4ReA4R2A2M6A2S51G6R10A2A2F_;Frho';VTR;S4cS4aVJAv;S3cR13S5dR12S3bA4A1R1aR11R10A5VFAM;RfReA2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Frv;Ftp0;Fb;Ftp;Frho;Fbd;Ftv;Fd;Fcells;Fk2;Fk1;Fobjs;FC;FA;").
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
S2S39S0S13ScS0S3aS2cS2bS2S39A2S2bS0S12A2S2cS2S39R4R3A4S2cS0S12R2S66A4A4R1A2S53R2S52Z2Z40A2A2A3Frho;Fr;Fnd;FT;").
Proof. intros. unfold emeasA. cbn [eda_rank eda_var fst snd z0 eval]. rewrite lit_unsigned by lia. lia. Qed.
Lemma emeas_eq : ltac2:(tb__ "0|1|
S2S39S0S12S13S13S12ScS4bQ40A1S1cR2R1A2S1cR3R1A2A3Fe;ScS0S3aS2cS2bS2S39A2S2bS0S12A2S2cS2S39R7R6A4S2cS0S12R5R4A4A4M0R2A2S3aG0R3A2A3F_;Frho';Frho;Fv;Fr;Fnd;FT;").
Proof. intros. unfold emeasA. cbn [eda_rank eda_var fst snd]. rewrite H. reflexivity. Qed.

Lemma XH_X_pro : ltac2:(tb__ "0|1|
S13S2aS4bQ40A1A1M0S0G0S50S53Z5eS52Z2Z40A2A2R2A2VTR;S4cS4aVJAv;S8bA1S84R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. unfold ndP, ndF.
  apply (X_release X_pro C_pre objs_pro 0 8 cells_pro DZero _ _ rho tp b tp0 (92, z0) eq_refl ltac:(lia) ltac:(lia) eq_refl X_pro_objs);
    [vmr|vmr|vmr|vmr| exact C_pre_eq | innth 2 | intros rho' _; rewrite emeas_z0; lia].
Qed.
Lemma XH_X_r2k : ltac2:(tb__ "0|1|
S13S2aS4bQ40A1A1M0G0VTR;S4cS4aVJAv;S60A1S74R3R2A5VFAM;S3aS2cS2bS2S39A2S2bS0S12A2S2cS2S39S74S60A4S2cS0S12Z50S5fS5eZ1cA2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_facts. intros HF. unfold ndJ, ndF.
  apply (X_release X_r2k C_rlk objs_r2k 4 6 cells_r2k DUnknown _ _ rho tp _ tp0 (80, VR pQ 27) eq_refl ltac:(lia) ltac:(lia) eq_refl X_r2k_objs);
    [vmr|vmr|vmr|vmr| exact C_rlk_eq | innth 18 |].
  intros rho' HE. rewrite (emeas_eq C_rlk _ 80 (VR pQ 27) rho rho' HE).
  exact (loop_meas_same rho _ 27 28 X_r2k C_rlk _ _ HF ltac:(vmr) ltac:(lia) ltac:(lia) ltac:(lia)).
Qed.
Lemma XH_X_r2g : ltac2:(tb__ "0|1|
S13S2aS4bQ40A1A1M0G0VTR;S4cS4aVJAv;S65A1S73R3R2A5VFAM;S3aS2cS2bS2S39A2S2bS0S12A2S2cS2S39S73S65A4S2cS0S12Z50S5fS5eZ1cA2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_facts. intros HF. unfold ndG, ndF.
  apply (X_release X_r2g C_rlg objs_r2g 4 6 cells_r2g DUnknown _ _ rho tp _ tp0 (80, VR pQ 27) eq_refl ltac:(lia) ltac:(lia) eq_refl X_r2g_objs);
    [vmr|vmr|vmr|vmr| exact C_rlg_eq | innth 19 |].
  intros rho' HE. rewrite (emeas_eq C_rlg _ 80 (VR pQ 27) rho rho' HE).
  exact (loop_meas_same rho _ 27 28 X_r2g C_rlg _ _ HF ltac:(vmr) ltac:(lia) ltac:(lia) ltac:(lia)).
Qed.

Definition pure_rule (Pre : axst) (Posts : list leafA) : Prop := ltac2:(tb__ "0|2|
S2Sc8S2aS17A1M0S13S2aS4bQ40A1A1S39Sa3ScS33G0A1Sa9R7VPre;R6A3S32G0R5A2A3ScS2dSaaR8VPre;R7R6S9fS4S2S8VPosts;A4A5S2eA3ScS2dSe3S56S16S3R9A1A1A2S2eA3ScS2dS3eS16S3RaA1A1R5A2S2eA3ScS2dS98S14S21S16S3RbA1M1A1A1S15G1A1A3S2eA3S4S13S96S4R2VPosts;A3S24S16S3RfA1A1RcR2A3VTR;S4cS4aVJAv;RbA1Sd7S15S3R10A1A1SabRfVPre;S8R4A1R10ReA5A2R3RcA5RaA2F_;F_;Frho';FL;VTR;S4cS4aVJAv;R8A1RdRaR9A5R7A2F_;F_;F_;F_;F_;F_;FQ;Fnd;Ftp;Frho;FR;Fs;FCl;").
Lemma X_pure : ltac2:(tb__ "0|6|
S2S2S2S2S2S2S2aSdaA1Sc8S2aS17A1M0S13S2aS4bQ40A1A1M1G1S0S0S101ReS2fS4SbRdS103A2S31S4A1A3A2ScS33G0A1Sa9RdRfR8A3S32G0R7A2A3ScS2dSaaReR10R9R8S2fS2RfS31S2A1A3A5S2eA3ScS2dSe3S56S16S3RfA1A1A2S2eA3ScS2dS3eS16S3R10A1A1S60A2S2eA3ScS2dS98S14S21S16S3R11A1M2A1A1S15G2A1A3S2eA3ScS2Sd7S15S3R12A1A1SabRdR14R13R12RcA5A2R11A3ScS33S2A1Sd9R12RfA2S32S2R11A2A3S96S2bS2bS2S39A2M3S2bS0S12A2M4A2S2cG3G4S2cS2S39R12S60A4S2cS0S12Z50M5S5fS5eRaA2A4A4S61A3ScS2dS92S5eS15S3R15A1A1A2S2eA3ScS2dS22S16S3R16A1A1S59A2S2eA3ScS2dS22S16S3R17A1A1S5eA2S2eA3S50Z0ReA2S51RfReA2S51RfZ40A2VTR;S4cS4aVJAv;S60A1R1bR14R13A5VFAM;S3aS2cG3G4S2cS2S39R18S60A4S2cS0S12G5S5fS5eR10A2A4A4R14A2R12A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fbpos;Fa;Ftp0;Ftp;Frho;FR;Fs;Fxf2;FX0;FT;FT0;FE;FP;FPre;").
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
S13S2aS4bQ40A1A1M0G0VTR;S4cS4aVJAv;S60A1S6cR3R2A5VFAM;S3aS2cS2bS2S39A2S2bS0S12A2S2cS2S39S6cS60A4S2cS0S12Z50S5fS5eZ39A2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
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
S13S2aS4bQ40A1A1M0G0VTR;S4cS4aVJAv;S60A1S6bR3R2A5VFAM;S3aS2cS2bS2S39A2S2bS0S12A2S2cS2S39S6bS60A4S2cS0S12Z50S5fS5eZ37A2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  eapply TR_pre; [intros w Hw; exact (SPA_axforms segs _ [AXSplit 0 (SLit (-96))] rho E_da0 E_da tp w E_da_eq Hw)|].
  apply (X_pure Pre_da P_da E_da T_da0 T_da E_da0 xf_tda s_da R_da rho tp tp0 54 55 CALL_da);
    [vmr|vmr|vmr|vmr|vmr| exact T_da0_eq | exact T_da_eq | innth 9 |vmr|vmr|vmr|lia|lia|lia].
Qed.

Lemma HIN_v : ltac2:(tb__ "0|1|
S13Sd1SbcS13S2aS4bQ40A1A1Sb8S9eS14S1aR6A1S15S3S7dA1A1A3S90VCST;VFB;VFF;Vrho0;A4SbaS56Vrho0;R8A3VAInv;R7R6R5R4A4S3fVrho0;R8A2ScdRbSbeSbdR9A1A1A2S43VFB;RaA2S44VFF;RbA2SccReS6aA2S40VFF;RdRfS5dA4SdSe0VCST;Vrho0;VFB;VFF;R10S31S2bS12S12A2A1M0S5dS72A8SdSe1VCST;VXGL;Vrho0;VFB;VFF;R10G0S5dS88A9SeaScfVFB;R10G0A3SddVFF;R10S5dA3ScaSc9R10S72RfA3S8dA2A3A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FAi;Fms;Frho;").
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
S13S2aS4bQ40A1A1M0G0VTR;S4cS4aVJAv;S60A1S6eR3R2A5VFAM;S3aS2cS2bS2S39A2S2bS0S12A2S2cS2S39S6eS60A4S2cS0S12Z50S5fS5eZ34A2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
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

Lemma X_cm : ltac2:(tb__ "0|9|
S2S2S2S12S12S2aS2bS12S12A2A1S2aS9aA1S13S2aS4bQ40A1A1M0G0ScS33S2A1Sd9RaS7bA2S32S2R9A2A3ScS12S9RaA1S18Sd5A1A3ScS2dS7S2fS14S1eS6S57A1S58A2S2fS14S19S1fS57A1S18S55S52Z2Z3dA2Z1A2A1A2S31S14A1A3A3S15S3RbA1A1A2S2eA3ScS2dSdcS62RaR9A2S5RcA1A2S2eA3ScS2dS20S3Sc0RdS62RbRaA2S57Z4M1Z6M2A5A1A1S2eA3ScS2dS94S15S3ReA1A1A1S2eA3ScS2dSbfS15S3RfA1M3A1RbS5dS34S30A1SaeS1bG3A1A6S2eA3ScS2dSc1VXGL;S15S3R10A1M4A1RcS5dS32S30U0A2S1bG4A1SafS62ReRdA2A8S2eA3ScS2Sc0R11S62RfReA2S57G1G2A5R10A3S96S2bS2bS2S39A2M5S2bS0S12A2M6A2S2cG5G6S2cS2S39R11S3cReS5dRdS3bA4A4S2cS0S12Z50M7S5fS5eZ1dA2A4A4S61A3ScS2dS92S5eS15S3R14A1A1A2S2eA3VTR;S4cS4aVJAv;S3cR10S5dRfS3bA4M8A1R15ReRdA5VFAM;S3aS2cG5G6S2cS2S39R15G8A4S2cS0S12G7S5fS5eZ1eA2A4A4ReA2RcA2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Ftp0;Ftp;Frho;Fbd;Ftv;Fk;Fd;FC;FY;FX;").
Proof.
  intros X Y C d k tv bd rho tp tp0 HY Hbase Hfe HXi Hwf HB HRO HXL HC HinC HV.
  apply TR_facts. intros HF.
  eapply TR_pre; [|apply (REENTER C (NDA tv fr_hp bd ANone) (80, VR pQ 29)); [exact HinC | exact (loop_meas_same rho _ 29 30 X C _ _ HF HV ltac:(lia) ltac:(lia) ltac:(lia))]].
  intros w Hw. rewrite <- HC.
  pose proof (SPA_axforms segs _ xf_f rho X Y tp w HY Hw) as Hw2.
  apply (JA_shadow_reopen segs HTOP AInv CST XGL ALA HCST HXGL LFSH NPH Kc rho0 (P0_hp CST FB FF) FB FF BX PTrue HKc HBX HNP
           tv fr_hp bd ANone 0%nat 160%positive 0 170%positive hG 4 6 Y (X_hp d k) rho tp w eq_refl ltac:(lia) Hbase ltac:(lia)
           ltac:(change (fs_frame_size 0) with 64; lia) Hfe (xrs_inclb_sound _ _ HXi) Hwf); [|exact Hw2].
  intros Ai rho1 tp1 md1 HF2 HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR. split.
  - exact (siteF Ai rho _ tv fr_hp _ rho1 tp1 md1 HM HF2 HB Hav HP0 HT HTK HN HD HZ HFR HRO).
  - intros r y Hr Hy. left. exact (proj1 (siteX Ai rho _ tv fr_hp (Some 0%nat) _ _ rho1 tp1 md1 HM HF2 HB Hav HP0 HT HTK HBf HFF HN HD HZ HFR HXL) r y Hr Hy).
Qed.
Lemma XH_X_rpk : ltac2:(tb__ "0|1|
S13S2aS4bQ40A1A1M0G0VTR;S4cS4aVJAv;S60A1S76R3R2A5VFAM;S3aS2cS2bS2S39A2S2bS0S12A2S2cS2S39S76S60A4S2cS0S12Z50S5fS5eZ1eA2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. unfold ndJ, ndF, tvL, tv_hp.
  apply (X_cm X_rpk Y_rpk C_mk pD pK _ _ rho tp tp0); [exact Y_rpk_eq |vmr|vmr|vmr|vmr|vmr|vmr|vmr| exact C_mk_eq | innth 16 | vmr].
Qed.
Lemma XH_X_rpg : ltac2:(tb__ "0|1|
S13S2aS4bQ40A1A1M0G0VTR;S4cS4aVJAv;S65A1S75R3R2A5VFAM;S3aS2cS2bS2S39A2S2bS0S12A2S2cS2S39S75S65A4S2cS0S12Z50S5fS5eZ1eA2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. unfold ndG, ndF, tvG, tv_hp.
  apply (X_cm X_rpg Y_rpg C_mg vDg vKg _ _ rho tp tp0); [exact Y_rpg_eq |vmr|vmr|vmr|vmr|vmr|vmr|vmr| exact C_mg_eq | innth 17 | vmr].
Qed.

Lemma X_Y_ep : ltac2:(tb__ "0|8|
S2S2S2aS2bS12S12A2A1S2aS9aA1S12S12S13S2aS4bQ40A1A1M0S0G0S0ScS12S9RbA1S18Sd5A1A3ScS2dS7S2fS14S1eS6S57A1S58A2S2fS14S19S1fS57A1S18S55S52Z2M1Z3dA2Z1M2A2A1A2S31S14A1A3A3S15S3RcA1A1A2S2eA3ScS2dSdcS62R9R8A2S5RdA1A2S2eA3ScS2dS20S3Sc0ReS62RaR9A2S57Z0M3Z8A5A1A1S2eA3ScS2dS20S3S64RfRbRaA3A1A1S2eA3ScS2dS94S15S3R10A1A1A1S2eA3ScS2dS95S15S3R11A1A1A1S2eA3ScS2dSbfS15S3R12A1M4A1R10S5dS34S30A1SaeS1bG4A1A6S2eA3ScS2dSc1VXGL;S15S3R13A1M5A1R11S5dS32S30U0A2S1bG5A1SafS62RfReA2A8S2eA3ScS2S64R14R10RfA3R13A3S96S2bS2bS2S39A2M6S2bS0S12A2M7A2S2cG6G7S2cS2S39R14S3cR13S5dR12S3bA4A4S2cS0S12RbS66A4A4S61A3S50G3RcA2S50S53S54RdG2A2S52G1Z40A2A2RfA2VTR;S4cS4aVJAv;S3cR16S5dR15S3bA4A1R18R12R11A5VFAM;R10RfA2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Frk;Ftp0;Fb;Ftp;Frho;Fk;Fd;Fbd;Ftv;FC;FY;").
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
S13S2aS4bQ40A1A1M0S0G0S50S53Z28S52Z2Z40A2A2R2A2VTR;S4cS4aVJAv;S77A1S81R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. unfold ndN, ndF.
  apply (X_Y_ep XN C_epn _ _ pD pK rho tp b tp0 38); [vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr| exact C_epn_eq | innth 22 | lia | lia].
Qed.
Lemma X_fp : ltac2:(tb__ "0|7|
S2S2S2S2S13S2aS4bQ40A1A1M0S0G0ScS33S2A1Sd9R8S7bA2S32S2R7A2A3ScS2dSdcS62S68S69A2M1S5R8A1A2S2eA3ScS2S105R9G1A2R8A3ScS12S9R9A1S18Sd5A1A3ScS2dS7S2fS14S1eS6S57A1S58A2S2fS14S19S1fS57A1S18S55S52Z2M2Z3dA2Z1A2A1A2S31S14A1A3A3S15S3RaA1A1A2S2eA3ScS2dSdcG1S5RbA1A2S2eA3ScS2dS20S3Sc0RcG1S57Z0Z8A5A1A1S2eA3ScS2dS20S3S64RdS68S69A3A1A1S2eA3ScS2dS94S15S3ReA1A1A1S2eA3ScS2dS95S15S3RfA1A1A1S2eA3ScS2dSbfS15S3R10A1M3A1S6aS5dS34S30A1SaeS1bG3A1A6S2eA3ScS2dSc1VXGL;S15S3R11A1M4A1S6aS5dS32S30U0A2S1bG4A1SafG1A8S2eA3ScS2S64R12S68S69A3R11A3S96S2bS2bS2S39A2M5S2bS0S12A2M6A2S2cG5G6S2cS2S39R12S63A4S2cS0S12Z1aS66A4A4S61A3S50S53Z1cS52G2Z40A2A2R10A2VTR;S4cS4aVJAv;S63A1R17R13R12A5VFAM;R11R10A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Ftp0;Fb;Ftp;Frho;FC;FY;FZ;FX;").
Proof.
  intros X Z Y C rho tp b tp0 HZ HXZ HY Hbase Hfe HXi Hwf1 Hwf2 HB HFRF HRO HXL HC HinC Hb.
  eapply TR_pre with (P := SPA segs (JAv ndX) Y rho tp).
  { intros w Hw. rewrite <- HY. apply (SPA_x_sub segs); [exact (xrs_inclb_sound _ _ HXZ)|]. exact (SPA_axforms segs _ xf_f rho X Z tp w HZ Hw). }
  unfold ndX, ndF. apply (X_Y_ep Y C tvL [PROG 72 pQ] pD pK rho tp b tp0 26 Hbase Hfe HXi Hwf1 Hwf2 HB HFRF HRO HXL HC HinC ltac:(lia) ltac:(lia)).
Qed.
Lemma XH_X_fp0 : ltac2:(tb__ "0|1|
S13S2aS4bQ40A1A1M0S0G0S50S53Z1cS52Z2Z40A2A2R2A2VTR;S4cS4aVJAv;S63A1S82R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply (X_fp X_fp0 Z_fp0 Y_fp0 C_fp0 rho tp b tp0 Z_fp0_eq); [vmr| exact Y_fp0_eq |vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr| exact C_fp0_eq | innth 23 | exact Hb].
Qed.
Lemma XH_X_fp1 : ltac2:(tb__ "0|1|
S13S2aS4bQ40A1A1M0S0G0S50S53Z1cS52Z2Z40A2A2R2A2VTR;S4cS4aVJAv;S63A1S83R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply (X_fp X_fp1 Z_fp1 Y_fp1 C_fp1 rho tp b tp0 Z_fp1_eq); [vmr| exact Y_fp1_eq |vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr| exact C_fp1_eq | innth 24 | exact Hb].
Qed.

Lemma X_X_rl : ltac2:(tb__ "0|8|
S2S2S2S2aS2bS12S12A2A1S2aS9aA1S13S2aS4bQ40A1A1M0S0G0S0ScS33S2A1Sd9RaS2fSdaSdbS8eA1S31SdaA1A3A2S32S2R9A2A3ScS2SaRaS104S3RaA1M1Sa0S17U12M2S1bG1A1A3A2A2R9A3ScS2dSc2Pa0PaaS57Z0M3Sa1S17G2S1bS3RbA1A1A3A5S2eA3ScS2dS7S2fS14S1eS6S57A1S58A2S2fS14S19S1fS57A1S18S55S52Z2M4Z3dA2Z1M5A2A1A2S31S14A1A3A3S15S3RcA1A1A2S2eA3ScS2dS3eS16S3RdA1A1S3cRbS5dRaS3bA4A2S2eA3S96S2bS2bS2S39A2M6S2bS0S12A2M7A2S2cG6G7S2cS2S39RdS3cRcS31S2bS2bS12S0A2S12A2A1RbS3bA4A4S2cS0S12R6S66A4A4S61A3S50G3R7A2S50S53S54R8G5A2S52G4Z40A2A2RaA2VTR;S4cS4aVJAv;S3cRfS5dReS3bA4A1R12RdRcA5VFAM;RbRaA2A2F_;F_;F_;F_;F_;F_;F_;F_;Frk;Ftp0;Fb;Ftp;Frho;Fbd;Ftv;FC;FX1;FX;").
Proof.
  intros X X1 C tv bd rho tp b tp0 rk HX1 HC HR Hfe Hnb HinC Hrk Hb.
  apply (TR_pre (fun w => exists rho', SPA segs (JAv (NDA tv [] bd ANone)) C rho' tp w)).
  { intros [tr [ms md]] Hw. pose proof (SPA_axforms segs _ [AXSelect sel_rel] rho X X1 tp _ HX1 Hw) as Hw1.
    exists (rho_absorb rho (skipn 18 (ss_objs (ax_S X1))) (vms md tp ms)). rewrite <- HC.
    change (ax_setS X1 (set_objs (ax_S X1) (firstn 18 (ss_objs (ax_S X1))))) with (drop_lastA X1 (firstn 18 (ss_objs (ax_S X1)))).
    change (@nil (sv * Z * sv)) with (remove_nth 0 fr_hp).
    apply (JA_release_inline segs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nn.Lib_arena_alloc.HTOP_ok AInv CST XGL ALA HCST HXGL LFLAG LFSH NPH Kc rho0 (P0_hp CST FB FF) FB FF BX PTrue HKc HBX HNP
             tv fr_hp bd ANone 0%nat 160%positive 0 170%positive hG X1 (firstn 18 (ss_objs (ax_S X1))) (skipn 18 (ss_objs (ax_S X1))) rho tp tr ms md);
      [reflexivity | lia | symmetry; apply firstn_skipn | exact HR | exact Hfe | exact Hnb | intros A1 A2 _; exact I | exact Hw1]. }
  apply TR_exw. intros rho'. apply (REENTER C (NDA tv [] bd ANone) (rk, z0)); [exact HinC | rewrite emeas_z0; lia].
Qed.
Lemma XH_X_rln : ltac2:(tb__ "0|1|
S13S2aS4bQ40A1A1M0S0G0S50S53Z24S52Z2Z40A2A2R2A2VTR;S4cS4aVJAv;S77A1S87R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. unfold ndN, ndF. apply (X_X_rl X_rln _ C_rln _ _ rho tp b tp0 34 X_rln_eq); [vmr|vmr|vmr|vmr| innth 25 | lia | lia].
Qed.
Lemma XH_X_rlf0 : ltac2:(tb__ "0|1|
S13S2aS4bQ40A1A1M0S0G0S50S53Z16S52Z2Z40A2A2R2A2VTR;S4cS4aVJAv;S63A1S85R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. unfold ndX, ndF. apply (X_X_rl X_rlf0 _ C_rlf0 _ _ rho tp b tp0 20 X_rlf0_eq); [vmr|vmr|vmr|vmr| innth 26 | lia | lia].
Qed.
Lemma XH_X_rlf1 : ltac2:(tb__ "0|1|
S13S2aS4bQ40A1A1M0S0G0S50S53Z16S52Z2Z40A2A2R2A2VTR;S4cS4aVJAv;S63A1S86R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. unfold ndX, ndF. apply (X_X_rl X_rlf1 _ C_rlf1 _ _ rho tp b tp0 20 X_rlf1_eq); [vmr|vmr|vmr|vmr| innth 27 | lia | lia].
Qed.

Lemma XH_E_sm : ltac2:(tb__ "0|1|
S13S2aS4bQ40A1A1M0S0G0S50S53Z62S52Z2Z40A2A2R2A2VTR;S4cS4aVJAv;S67A1S7cR5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
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
S13S2aS4bQ40A1A1M0S0G0VTR;S4cS4aVJAv;S79A1S70R4R3A5VFAM;R2R1A2A2Ftp0;Fb;Ftp;Frho;").
Proof. intros. apply POST. innth 1. Qed.
Lemma X_P_fail : ltac2:(tb__ "0|1|
S13S2aS4bQ40A1A1M0S0G0VTR;S4cS4aVJAv;S78A1S6fR4R3A5VFAM;R2R1A2A2Ftp0;Fb;Ftp;Frho;").
Proof. intros. apply POST. innth 0. Qed.

Lemma exits_okT : ltac2:(tb__ "0|3|
S2S39S2bS0S12A2M0S13S2aS4bQ40A1A1M1G1S96S2bS2bS2S39A2M2G0A2S2cG2G0S2cS2S39R6R5A4R4A4S8aA3VTR;S4cS4aVJAv;R6A1R7R4R3A5VFAM;S3aS2cG2G0S2cS2S39R7R6A4R5A4R4A2R2A2A2F_;Ftp0;Ftp;Frho;FrvX;FndX;FX;").
Proof.
  intros X ndX rvX rho tp tp0 Hin. cbn [In exitsH] in Hin.
  destruct Hin as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[]]]]]]]]]]]]]]]]]]]; injection H as <- <- <-.
  - apply XH_E_sm. rewrite emeas_z0. lia.
  - apply XH_X_pro. rewrite emeas_z0. lia.
  - apply XH_E_unp.
  - apply XH_E_pc.
  - apply XH_E_da.
  - apply XH_E_vr.
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
S49S4aVKc;Vok;A3").
Hypothesis AC : ltac2:(tb__ "0|0|
SfaS4aSf7VAInv;VCST;VXGL;A5").

Theorem handle_p_sum : ltac2:(tb__ "0|0|
S2aS4bQ40A1A1Sa6S4aVok;S4cS4aS42VAInv;VCST;VXGL;VKc;S90VCST;VFB;VFF;A3VFB;VFF;VBX;S3dS67AaS71Vrho0;R1A5Sa8S4aS56Vrho0;R1Sc6A5A4Ftp0;").
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
SfbS4aSf7VAInv;VCST;VXGL;A5").

Theorem handle_p_sum_ex : ltac2:(tb__ "0|0|
S2aS4bQ40A1A1Sa5S4aS4cS4aS42VAInv;VCST;VXGL;VKc;S90VCST;VFB;VFF;A3VFB;VFF;VBX;S3dS67AaS71Vrho0;R1A5Sa8S4aS56Vrho0;R1Sc6A5A3Ftp0;").
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

(* [comment removed for export] *)
Module Lib_tess_polygon_pf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "valuation"; "sobj"; "SLit"; "ss_facts"; "sprop"; "ss_objs"; "SVar"; "ss_next"; "cell"; "SAlu"; "holds"; "rw"; "DUnknown"; "eval"; "ob_base"; "obj_hi_of"; "obj_lo_of"; "obj_range"; "mkObj"; "sv_eqb"; "DZero"; "agree_below"; "ob_hi"; "ob_lo"; "soff"; "sprop_below"; "sprop_eqb"; "SPUle"; "swf"; "@Corelib.Init.Logic"; "eq"; "and"; "or"; "ex"; "True"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "leafA"; "la_state"; "ax_base"; "@Corelib.Init.Datatypes"; "list"; "prod"; "pair"; "nil"; "bool"; "cons"; "true"; "option"; "Some"; "fst"; "nat"; "snd"; "app"; "None"; "andb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "mul"; "pow"; "opp"; "sub"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "uval"; "bitem"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "smatchA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "entails_frA"; "call_checkA"; "call_checkPA"; "import_postA"; "J_ofPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o5.Lib_tess_polygon_pf"; "P0_pg"; "inFB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "PTrue"; "frinA"; "TPA"; "nd_below"; "tvinA"; "fbinA"; "ffinA"; "JA_pre"; "emeasA"; "ANone"; "JA"; "JLA"; "NDA"; "frozen"; "nodeIA"; "ok_frameKA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "axform"; "AXSplit"; "AXSelect"; "@Stdlib.Lists.List"; "In"; "forallb"; "nth_error"; "existsb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "AE_A"; "V_FL"; "JL_pure"; "J_pure_pre"; "L_stack_free"; "Pre_stack_free"; "JL_stack_free"; "JL_stack_malloc"; "J_stack_free_pre"; "J_stack_malloc_pre"; "L_stack_malloc"; "Pre_stack_malloc"; "alloc_contractsA"; "alloc_contractsA_ex"; "alloc_lawsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_tess_polygon_states"; "pN"; "X_pg"; "gF"; "pSCR"; "O_pp2d"; "vF"; "vFL"; "pOUT"; "pPTS"; "Pre_pg"; "n12"; "o12"; "pNXT"; "pPRV"; "pRFX"; "P_inv"; "P_ok"; "pg_base_facts"; "spo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "topG"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_tess_polygon_cstates"; "ndF"; "objs_butlast"; "E_f8a0"; "E_ms0"; "T_f8a1"; "T_f8b1"; "T_s00_1"; "nd0"; "Pre_sf"; "reshapeA"; "E_f8a2"; "E_f8b0"; "E_f8b1"; "E_s00_0"; "E_s00_1"; "E_sc3_0"; "E_sc4_0"; "L_sf"; "O_pp2d_lit"; "T_f8a0"; "T_f8a2"; "T_f8b0"; "T_pure"; "T_s00_0"; "T_sc3_0"; "T_sc4_0"; "T_sm0"; "T_sm1"; "xf_shback"; "xf_shcall"; "E_f8a"; "E_f8a1"; "E_f8b"; "E_ms1"; "E_r2_0"; "E_s00"; "E_sc3"; "E_sc3_1"; "E_sc4"; "E_sc4_1"; "E_sfI"; "E_sfI0"; "E_sfK"; "E_sfK0"; "E_sm0"; "T_r2_0"; "T_sc3_1"; "T_sc4_1"; "cutsE"; "xf_wback"; "C_fin"; "C_pro0"; "C_pro2"; "C_s1"; "E_ms"; "E_r2"; "E_r2_1"; "L_00";
"L_f8"; "L_sm"; "Pre_00"; "Pre_f8"; "Pre_sm"; "R_f8a"; "R_f8b"; "R_r2"; "R_s00"; "R_sc3"; "R_sc4"; "R_sfI"; "R_sfK"; "R_sm"; "T_r2"; "T_sc3"; "T_sc4"; "T_sfI"; "T_sfK"; "exitsE"; "s_f8a"; "s_f8b"; "s_r2"; "s_s00"; "s_sc3"; "s_sc4"; "s_sfI"; "s_sfK"; "s_sm"; "sel_last"; "shc_f8a"; "shc_ms"; "xf_r2back"; "xf_r2call"; "z0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o5.Lib_tess_polygon_pf.Sum"; "baseF"; "extraX"; "extraO"; "Posts_pg"; "basez"; "robjs_checkP"; "in_callers"; "JL"; "extra_tab"; "extz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "call_linkP"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "wsub_get"; "rho_absorb"; "rho_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS"; "xrs_checkL"; "shadow_release_stateA"; "shobj"; "shadow_reopen_stateA"; "flag_carve_stateA"; "robjs_checkF"; "frame_open_stateA"; "robj_ownframe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_tess_scale2d"; "Pre_sc"; "P_sc"; "Posts_sc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "T_ok"; "tvd"; "tvz"; "FBx"; "remove_nth"; "T0"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SLL"; "ALU_SRL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n2.Lib_tess_run2d_states"; "Pre_r2"; "Posts_r2"; "P_ret"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA"; "infrFF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "pclMA"; "FFx"; "T_afterA3"; "xrs_okL"; "robjs_okL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "T_afterA"; "ccount"; "call_checkTA"; "is_shadowZ"; "payA"; "robj_stackA"; "site_okA"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Asan_set_shadow_iface"; "L_set_shadow"; "Pre_set_shadow"; "set_shadow_contractA"; "set_shadow_contractA_ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "SHADOW_OFF"; "fs_frame_size"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "jnodeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3"; "import_okPA3"; "import_postA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR"; "robjs_okF"; "xrs_ok47"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAS.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.JcertCutA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Asan_set_shadow_iface Lib_tess_scale2d.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_tess_run2d Lib_tess_run2d_ex Lib_tess_polygon_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nt.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_tess_polygon_chk.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Asan_set_shadow_iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_tess_scale2d OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n2.Lib_tess_run2d_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_tess_run2d OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_tess_run2d_ex OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_tess_polygon_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_tess_polygon_cstates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nt.Lib_tess_polygon_chk0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_tess_polygon_chk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import TessPolygonAddr.

Definition inFB (FB : list (Z * Z)) (x n : Z) : Prop := ltac2:(tb__ "0|0|
S23S0S0S23S0S0S21S6aS2dS0S0A2S2eS0S0R2R1A4VFB;A3S21S3cR2Vx;A2S3cS3dVx;Vn;A2S3dR2R1A2A2A2A2Lm;A2Lb;A2").

Definition P0_pg (FB : list (Z * Z)) (FF : list (Z * Z * Z)) (r : valuation) : Prop := ltac2:(tb__ "0|4|
S21S20S36S128Z6S103S2dS2dS0S0A2M0S0A2G0S35G0S0A2VFF;A4A2U0A3S21S121VFF;S44Q40M1SeVr;PcA2A2Z48A3S21S121VFF;S44G1SeVr;PdA2A2Z18A3S21S54VFB;S44G1SeVr;PfA2A2S3fZcM2S44G1SeVr;PeA2A2M3A2A3S21S54VFB;S44G1SeVr;P10A2A2S3fG2S42G3Z2A2A2A3S54VFB;S44G1SeVr;P11A2A2S44G1SeVr;P12A2A2A3A2A2A2A2A2").

Lemma T_sm0_eq : ltac2:(tb__ "0|1|
S20S26S127S79S6eZ6M0A2Sc1SebSdcS78S6eG0A2A5SafA3"). Proof. vm_compute. reflexivity. Qed.
Lemma T_sm1_eq : ltac2:(tb__ "0|0|
S20S33S26A1S66SafS31S67S69SecSafU3A2A1S2fS67A1A3A2S34S26Sb0A2A3"). Proof. vm_compute. reflexivity. Qed.
Lemma C_pro0_eq : ltac2:(tb__ "0|1|
S20S26S10fSb0S96Sb0A1S38S2dS2S2A2M0S7eS2fG0A1A3P6eS136Z6A1A5Sc8A3"). Proof. vm_compute. reflexivity. Qed.
Lemma E_f8a0_objs : ltac2:(tb__ "0|0|
S20S2cS4A1S8S27S97A1A1S38S4S96S97A1S31S4S10bS7fZ0Z200SedS17A5S2fS4A1A3A3A3"). Proof. vm_compute. reflexivity. Qed.
Lemma E_f8a1_eq : ltac2:(tb__ "0|0|
S20S26S10aS97S96S97A1P6eS2fS2dS0S0A2A1A4Sb4A3"). Proof. vm_compute. reflexivity. Qed.
Lemma E_f8a2_eq : ltac2:(tb__ "0|0|
S20S26S10cSb4S7eS7fZ4Z104A5S9fA3"). Proof. vm_compute. reflexivity. Qed.
Lemma E_f8a_eq : ltac2:(tb__ "0|0|
S20S33S26A1S66S9fSb2S9fA1A2S34S26Sb3A2A3"). Proof. vm_compute. reflexivity. Qed.
Lemma T_f8a0_eq : ltac2:(tb__ "0|1|
S20S26S127S131S6eZf8M0A2Sb3Se3Sd4S130G0A1A5Sa8A3"). Proof. vm_compute. reflexivity. Qed.
Lemma T_f8a1_eq : ltac2:(tb__ "0|0|
S20S33S26A1S66Sa8Sb1Sa8A1A2S34S26S99A2A3"). Proof. vm_compute. reflexivity. Qed.
Lemma T_f8a1_objs : ltac2:(tb__ "0|0|
S20S2cS4A1S8S27S99A1A1S38S4S96S99A1S31S4S10bS7fZ4Z104S2fSbA1SfA5S2fS4A1A3A3A3"). Proof. vm_compute. reflexivity. Qed.
Lemma T_f8a2_eq : ltac2:(tb__ "0|0|
S20S26S10aS99S96S99A1P6eS2fS2dS0S0A2A1A4Sa9A3"). Proof. vm_compute. reflexivity. Qed.
Lemma C_pro2_eq : ltac2:(tb__ "0|0|
S20S26S10cSa9S28Sa9A1S7fZ104Z114A5Sc9A3"). Proof. vm_compute. reflexivity. Qed.

Lemma E_ms0_objs : ltac2:(tb__ "0|0|
S20S2cS4A1S8S27S98A1A1S38S4S96S98A1S31S4S10bS7fZ104Z114SeeSfA5S2fS4A1A3A3A3"). Proof. vm_compute. reflexivity. Qed.
Lemma E_ms1_eq : ltac2:(tb__ "0|0|
S20S26S10aS98S96S98A1P6eS2fS2dS0S0A2A1A4Sb6A3"). Proof. vm_compute. reflexivity. Qed.
Lemma E_ms_eq : ltac2:(tb__ "0|0|
S20S33S26A1S66Sb6S31S67S68U7S5Z10A1A2S2fS67A1A3A2S34S26ScbA2A3"). Proof. vm_compute. reflexivity. Qed.

Lemma E_s00_1_eq : ltac2:(tb__ "0|0|
S20S26S10cSa2S28Sa2A1S7fZ4Z104A5Sa3A3"). Proof. vm_compute. reflexivity. Qed.
Lemma E_s00_eq : ltac2:(tb__ "0|0|
S20S33S26A1S66Sa3Sb2Sa3A1A2S34S26Sb8A2A3"). Proof. vm_compute. reflexivity. Qed.
Lemma T_s00_0_eq : ltac2:(tb__ "0|1|
S20S26S127S131S6eZ0M0A2Sb8Se6Sd7S130G0A1A5SacA3"). Proof. vm_compute. reflexivity. Qed.
Lemma T_s00_1_eq : ltac2:(tb__ "0|0|
S20S33S26A1S66SacSb1SacA1A2S34S26S9bA2A3"). Proof. vm_compute. reflexivity. Qed.
Lemma T_s00_1_objs : ltac2:(tb__ "0|0|
S20S2cS4A1S8S27S9bA1A1S38S4S96S9bA1S31S4S10bS7fZ4Z104S2fSbA1S17A5S2fS4A1A3A3A3"). Proof. vm_compute. reflexivity. Qed.
Lemma C_s1_eq : ltac2:(tb__ "0|0|
S20S26S10aS9bS96S9bA1P6eS2fS2dS0S0A2A1A4ScaA3"). Proof. vm_compute. reflexivity. Qed.
Lemma E_f8b1_eq : ltac2:(tb__ "0|0|
S20S26S10cSa0S28Sa0A1S7fZ4Z104A5Sa1A3"). Proof. vm_compute. reflexivity. Qed.
Lemma E_f8b_eq : ltac2:(tb__ "0|0|
S20S33S26A1S66Sa1Sb2Sa1A1A2S34S26Sb5A2A3"). Proof. vm_compute. reflexivity. Qed.
Lemma T_f8b0_eq : ltac2:(tb__ "0|1|
S20S26S127S131S6eZf8M0A2Sb5Se4Sd5S130G0A1A5SaaA3"). Proof. vm_compute. reflexivity. Qed.
Lemma T_f8b1_eq : ltac2:(tb__ "0|0|
S20S33S26A1S66SaaSb1SaaA1A2S34S26S9aA2A3"). Proof. vm_compute. reflexivity. Qed.
Lemma T_f8b1_objs : ltac2:(tb__ "0|0|
S20S2cS4A1S8S27S9aA1A1S38S4S96S9aA1S31S4S10bS7fZ4Z104S2fSbA1SfA5S2fS4A1A3A3A3"). Proof. vm_compute. reflexivity. Qed.
Lemma C_fin_eq : ltac2:(tb__ "0|0|
S20S26S10aS9aS96S9aA1P6eS2fS2dS0S0A2A1A4Sc7A3"). Proof. vm_compute. reflexivity. Qed.
Lemma E_sc3_0_p2d : ltac2:(tb__ "0|0|
S20S33S4A1S6cS4S8S27Sa4A1A1U7A3S34S4S81S2fSbA1A1A2A3"). Proof. vm_compute. reflexivity. Qed.
Lemma E_sc3_1_eq : ltac2:(tb__ "0|0|
S20S26S9eSa4U7Sa7Z3A1A3SbaA3"). Proof. vm_compute. reflexivity. Qed.
Lemma E_sc3_eq : ltac2:(tb__ "0|0|
S20S33S26A1S66SbaS31S67S68U1S5N10A1A2S2fS67A1A3A2S34S26Sb9A2A3"). Proof. vm_compute. reflexivity. Qed.
Lemma T_sc3_0_eq : ltac2:(tb__ "0|0|
S20S26SabS111Sb9Se7Sd8S112A5SadA3"). Proof. vm_compute. reflexivity. Qed.
Lemma T_sc3_0_p2d : ltac2:(tb__ "0|0|
S20S33S4A1S6cS4S8S27SadA1A1U1A3S34S4S15S80S5Z0A1S5Z30A1S2fSbA1SfA5A2A3"). Proof. vm_compute. reflexivity. Qed.
Lemma T_sc3_1_eq : ltac2:(tb__ "0|0|
S20S26S9eSadU1S81S2fSbA1A1A3Sc3A3"). Proof. vm_compute. reflexivity. Qed.
Lemma T_sc3_eq : ltac2:(tb__ "0|0|
S20S33S26A1S66Sc3Sc6A2S34S26SdeA2A3"). Proof. vm_compute. reflexivity. Qed.
Lemma E_sc4_0_p2d : ltac2:(tb__ "0|0|
S20S33S4A1S6cS4S8S27Sa5A1A1U7A3S34S4S81S2fSbA1A1A2A3"). Proof. vm_compute. reflexivity. Qed.
Lemma E_sc4_1_eq : ltac2:(tb__ "0|0|
S20S26S9eSa5U7Sa7Z4A1A3SbcA3"). Proof. vm_compute. reflexivity. Qed.
Lemma E_sc4_eq : ltac2:(tb__ "0|0|
S20S33S26A1S66SbcS31S67S68U1S5N10A1A2S2fS67A1A3A2S34S26SbbA2A3"). Proof. vm_compute. reflexivity. Qed.
Lemma T_sc4_0_eq : ltac2:(tb__ "0|0|
S20S26SabS111SbbSe8Sd9S112A5SaeA3"). Proof. vm_compute. reflexivity. Qed.
Lemma T_sc4_0_p2d : ltac2:(tb__ "0|0|
S20S33S4A1S6cS4S8S27SaeA1A1U1A3S34S4S15S80S5Z0A1S5Z40A1S2fSbA1SfA5A2A3"). Proof. vm_compute. reflexivity. Qed.
Lemma T_sc4_1_eq : ltac2:(tb__ "0|0|
S20S26S9eSaeU1S81S2fSbA1A1A3Sc4A3"). Proof. vm_compute. reflexivity. Qed.
Lemma T_sc4_eq : ltac2:(tb__ "0|0|
S20S33S26A1S66Sc4Sc6A2S34S26SdfA2A3"). Proof. vm_compute. reflexivity. Qed.
Lemma E_r2_eq : ltac2:(tb__ "0|0|
S20S33S26A1S66Sb7Sf0A2S34S26ScdA2A3").     Proof. vm_compute. reflexivity. Qed.
Lemma T_r2_0_eq : ltac2:(tb__ "0|0|
S20S26SabS11eSccSe5Sd6S120A5Sc2A3"). Proof. vm_compute. reflexivity. Qed.
Lemma T_r2_eq : ltac2:(tb__ "0|0|
S20S33S26A1S66Sc2SefA2S34S26SddA2A3"). Proof. vm_compute. reflexivity. Qed.
Lemma E_sfI_eq : ltac2:(tb__ "0|0|
S20S26S10dSbeP78A2SbdA3"). Proof. vm_compute. reflexivity. Qed.
Lemma E_sfK_eq : ltac2:(tb__ "0|0|
S20S26S10dSc0P78A2SbfA3"). Proof. vm_compute. reflexivity. Qed.
Lemma T_sfI_eq : ltac2:(tb__ "0|1|
S20S26S124S73S6eZ6M0A2SbdSe9SdaS72S6eG0A2S7eA6Se0A3"). Proof. vm_compute. reflexivity. Qed.
Lemma T_sfK_eq : ltac2:(tb__ "0|1|
S20S26S124S73S6eZ6M0A2SbfSeaSdbS72S6eG0A2S7eA6Se1A3"). Proof. vm_compute. reflexivity. Qed.

Section Sum.
Let HTOP : InitState.segs_top segs <= IMG_HI := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nn.Lib_arena_alloc.HTOP_ok.
Variable AInv : ltac2:(tb__ "0|0|
S90S3S2cS43Q40A1A1S93OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
S7cS3bVAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S0S13bVCST;R1A2S21S3cZ0R2A2S3eR2S134A2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S0S13bVXGL;R1A2S21S3cZ0R2A2S3eR2S134A2A2F_;Fa;").
Hypothesis LFLAG : law_flag_stmt AInv.
Hypothesis LFSH : law_fshadow_stmt AInv.
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S2cS2dS2dS0S0A2S0A2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 5 BX.
Let HNP : NP_okA NF := NP_okA_intro NF eq_refl.
Variable rho0 : valuation.

Definition JL (nd : ndesc) : jpostA := ltac2:(tb__ "0|0|
S61VAInv;VCST;VXGL;VKc;S53VFB;VFF;A2VFB;VFF;VBX;S56Vnd;Aa").
Definition Posts_pg : list (axst * jpostA) := ltac2:(tb__ "0|2|
S31S2dS26S4cA2M0S2eS26S4cS8cSfdS9cA1M1A4S31G0S2eS26S4cS8dG1A4S2fG0A1A3A3").
Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S60VAInv;VCST;VXGL;S4bVKc;Vrho0;S53VFB;VFF;A2VFB;VFF;VBX;S56Vnd;Ac").
Let nI : ltac2:(tb__ "0|0|
S2dS26S55A2S13aFn;") := ltac2:(tb__ "0|0|
S64VAInv;VCST;VXGL;S4bVKc;Vrho0;S53VFB;VFF;A2VFB;VFF;VBX;S56Ab").
Let Q (tp0 : list word) : assn := ltac2:(tb__ "0|0|
S4dS3bS4bVrho0;Vtp0;Sf9A5").

Definition baseF (F : list sprop) : bool := ltac2:(tb__ "0|0|
S6bS7S7S6dS7S1dR1A1VF;A3Lp;S8eA3").

Definition frameB (F : list sprop) : bool := ltac2:(tb__ "0|0|
S6dS7S1dS1eScS11bS82S5Z1000A1A3S9P1eA1A2A1VF;A3").

Record basez (rho : valuation) : Prop := BZ {
  bz_sp : uval rho (SVar 30) + 2688 <= uval rho (SVar 10) <= 2 ^ 47;
  bz_D : uval rho (SVar V_DEPTH) = uval rho (SVar V_DEPTH) - 0 /\ 2 ^ 64 - 2 ^ 40 <= uval rho (SVar V_DEPTH) <= 2 ^ 64 - PG_DEPTH;
  bz_win : uval rho (SVar 30) <= uval rho (SVar 10) - 384 + (uval rho (SVar V_DEPTH) - 2 ^ 64);
  bz_n : 3 <= uval rho pN <= 2 ^ 20;
  bz_res : uval rho (SVar 13) + 24 <= 140737479966720;
  bz_scr : 4096 <= uval rho pSCR /\ uval rho (SVar 18) <= 2 ^ 26 /\ uval rho pSCR + uval rho (SVar 18) <= 140737479966720;
  bz_need : 16 * uval rho pN + 2 * uval rho A16 + (uval rho pN + 7) / 8 <= uval rho (SVar 18);
  bz_a16 : uval rho A16 = 4 * uval rho pN + 15 - (4 * uval rho pN + 15) mod 16;
  bz_top : aceil <= uval rho (SVar 30) <= 140737479966720 }.

Lemma uval_spo : ltac2:(tb__ "0|2|
S3S0S21S3cZ0S41R1A1M0A2S3cG0S45R2S9PaA1M1A2A2A2S20S0S45R3S8fR2A1A2S3dS45R3G1A2R2A2A3F_;Fk;Frho;").
Proof.
  intros rho k Hk. unfold spo, uval in *. rewrite U_add, U_lit. pose proof (U_range (eval rho (SVar 10))) as R. unfold M64v in *.
  set (x := bv_unsigned (eval rho (SVar 10))) in *. rewrite Zplus_mod_idemp_r. apply Z.mod_small. lia.
Qed.

Lemma basez_of : ltac2:(tb__ "0|0|
S3S2cS7A1S102S7SdR2A1R1A3S20S30Sf6R2A1S32A3SfaR4A1F_;F_;FF;Frho;").
Proof.
  intros rho F HF HB.
  assert (HPF : Forall (holds rho) pg_base_facts).
  { apply Forall_forall. intros p Hp. apply (holds_mem rho F p HF). exact (proj1 (forallb_forall _ _) HB p Hp). }
  clear HF HB.
  factz HPF (SPUle (SLit 3) pN) N1. factz HPF (SPUle pN (SLit two20)) N2.
  fact HPF (SPBranch BC_GE (SLit (- PG_DEPTH)) (SVar V_DEPTH)) D1. fact HPF (SPBranch BC_GE (SVar V_DEPTH) (SLit (- 2 ^ 40))) D2.
  factz HPF (SPUle (SLit 131072) (SVar 10)) S1. factz HPF (SPUle (SVar 10) (SLit two47)) S2.
  factz HPF (SPUle (SVar 30) (SAlu ALU_ADD psp (SVar V_DEPTH))) W1. factz HPF (SPUle (SVar 30) psp) W2.
  factz HPF (SPUle (SAlu ALU_ADD (SVar 13) (SLit 24)) (SLit 140737479966720)) R1. factz HPF (SPUle (SVar 13) (SLit two47)) R0.
  factz HPF (SPUle (SLit 4096) (SVar 17)) C1. factz HPF (SPUle (SVar 18) (SLit (2 ^ 26))) C2. factz HPF (SPUle (SVar 17) (SLit 140737479966720)) C0.
  factz HPF (SPUle (SAlu ALU_ADD (SVar 17) (SVar 18)) (SLit 140737479966720)) C3.
  factz HPF (SPUle (SLit 140735332483072) (SVar 30)) T1. factz HPF (SPUle (SVar 30) (SLit 140737479966720)) T2.
  factz HPF F_scr FS.
  apply (proj1 (holds_bge _ _ _)) in D1. apply (proj1 (holds_bge _ _ _)) in D2.
  repeat change (bv_unsigned (eval ?r ?e)) with (uval r e) in *.
  unfold two20, two47, ACEIL, PG_DEPTH in *. rewrite !uval_lit in N1, N2, S1, S2, R1, R0, C1, C2, C0, C3, T1, T2 by lia.
  change (uval rho (SLit (Z.opp 2304))) with (bv_unsigned (eval rho (SLit (Z.opp 2304)))) in D1. rewrite U_lit in D1. change ((Z.opp 2304) mod M64v) with 18446744073709549312 in D1.
  change (uval rho (SLit (- 2 ^ 40))) with (bv_unsigned (eval rho (SLit (- 2 ^ 40)))) in D2. rewrite U_lit in D2. change ((- 2 ^ 40) mod M64v) with 18446742974197923840 in D2.
  pose proof (uval_range rho (SVar V_DEPTH)) as RD. pose proof (uval_range rho (SVar 13)) as R13. pose proof (uval_range rho pN) as RN.
  pose proof (uval_range rho (SVar 17)) as R17.
  destruct (Zsigned_spec (uval rho (SVar V_DEPTH))) as [[L1 E1]|[L1 E1]]; rewrite E1 in D1, D2;
    [destruct (Zsigned_spec 18446744073709549312) as [[? E2]|[? E2]]; rewrite E2 in D1; lia|].
  destruct (Zsigned_spec 18446744073709549312) as [[? E2]|[? E2]]; rewrite E2 in D1; [lia|].
  destruct (Zsigned_spec 18446742974197923840) as [[? E3]|[? E3]]; rewrite E3 in D2; [lia|].
  assert (EP : uval rho psp = uval rho (SVar 10) - 384) by (unfold psp; apply uval_spo; lia). rewrite EP in W2.
  assert (EA : uval rho (SAlu ALU_ADD psp (SVar V_DEPTH)) = uval rho (SVar 10) - 384 + (uval rho (SVar V_DEPTH) - 2 ^ 64)).
  { unfold uval at 1. rewrite U_add. change (bv_unsigned (eval rho psp)) with (uval rho psp). change (bv_unsigned (eval rho (SVar V_DEPTH))) with (uval rho (SVar V_DEPTH)).
    rewrite EP. unfold M64v in *. unfold H63v in *.
    replace (uval rho (SVar 10) - 384 + uval rho (SVar V_DEPTH)) with ((uval rho (SVar 10) - 384 + (uval rho (SVar V_DEPTH) - 2 ^ 64)) + 1 * 2 ^ 64) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
  rewrite EA in W1.
  rewrite uval_add_small in R1 by (rewrite uval_lit by lia; lia). rewrite uval_lit in R1 by lia.
  rewrite uval_add_small in C3 by lia.

  assert (EA16 : uval rho A16 = 4 * uval rho pN + 15 - (4 * uval rho pN + 15) mod 16).
  { unfold A16, M16, uval. rewrite (U_and_hmask rho _ 18446744073709551600 16 eq_refl), U_add, U_sll_lit, U_lit. change (2 ^ (2 mod 64)) with 4. unfold M64v.
    change (bv_unsigned (eval rho pN)) with (uval rho pN). rewrite (Z.mod_small (uval rho pN * 4)) by lia. change (15 mod 2 ^ 64) with 15.
    rewrite Z.mod_small by lia. lia. }
  assert (E2A : uval rho (SAlu ALU_AND (SAlu ALU_ADD (SAlu ALU_SLL pN (SLit 3)) (SLit 30)) M32) = 2 * uval rho A16).
  { rewrite EA16. unfold M32, uval. rewrite (U_and_hmask rho _ 18446744073709551584 32 eq_refl), U_add, U_sll_lit, U_lit. change (2 ^ (3 mod 64)) with 8. unfold M64v.
    change (bv_unsigned (eval rho pN)) with (uval rho pN). rewrite (Z.mod_small (uval rho pN * 8)) by lia. change (30 mod 2 ^ 64) with 30.
    rewrite Z.mod_small by lia.
    pose proof (Z.div_mod (4 * uval rho pN + 15) 16 ltac:(lia)). pose proof (Z.mod_pos_bound (4 * uval rho pN + 15) 16 ltac:(lia)).
    pose proof (Z.div_mod (uval rho pN * 8 + 30) 32 ltac:(lia)). pose proof (Z.mod_pos_bound (uval rho pN * 8 + 30) 32 ltac:(lia)). nia. }
  assert (ER : uval rho (SAlu ALU_SRL (SAlu ALU_ADD pN (SLit 7)) (SLit 3)) = (uval rho pN + 7) / 8).
  { unfold uval. rewrite U_srl_lit, U_add, U_lit. change (2 ^ (3 mod 64)) with 8. unfold M64v. change (bv_unsigned (eval rho pN)) with (uval rho pN).
    change (7 mod 2 ^ 64) with 7. rewrite Z.mod_small by lia. reflexivity. }
  assert (HD8 : 0 <= (uval rho pN + 7) / 8 < 2 ^ 18).
  { split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
  assert (ER8 : uval rho (SAlu ALU_AND (SAlu ALU_ADD (SAlu ALU_SRL (SAlu ALU_ADD pN (SLit 7)) (SLit 3)) (SLit 15)) M16)
                = (uval rho pN + 7) / 8 + 15 - ((uval rho pN + 7) / 8 + 15) mod 16).
  { unfold M16. unfold uval at 1. rewrite (U_and_hmask rho _ 18446744073709551600 16 eq_refl), U_add, U_lit.
    change (bv_unsigned (eval rho (SAlu ALU_SRL (SAlu ALU_ADD pN (SLit 7)) (SLit 3)))) with (uval rho (SAlu ALU_SRL (SAlu ALU_ADD pN (SLit 7)) (SLit 3))).
    rewrite ER. unfold M64v. change (15 mod 2 ^ 64) with 15. rewrite Z.mod_small by lia. reflexivity. }
  set (r8 := uval rho (SAlu ALU_AND (SAlu ALU_ADD (SAlu ALU_SRL (SAlu ALU_ADD pN (SLit 7)) (SLit 3)) (SLit 15)) M16)) in *.
  set (a2 := uval rho (SAlu ALU_AND (SAlu ALU_ADD (SAlu ALU_SLL pN (SLit 3)) (SLit 30)) M32)) in *.
  assert (A16B : 0 <= uval rho A16 <= 4 * uval rho pN + 15) by (pose proof (Z.mod_pos_bound (4 * uval rho pN + 15) 16 ltac:(lia)); lia).
  assert (R8B : (uval rho pN + 7) / 8 <= r8 < 2 ^ 40) by (pose proof (Z.mod_pos_bound ((uval rho pN + 7) / 8 + 15) 16 ltac:(lia)); lia).
  unfold uval at 1 in FS. rewrite U_add in FS. rewrite U_add in FS.
  change (bv_unsigned (eval rho (SAlu ALU_AND (SAlu ALU_ADD (SAlu ALU_SLL pN (SLit 3)) (SLit 30)) M32))) with a2 in FS.
  change (bv_unsigned (eval rho (SAlu ALU_AND (SAlu ALU_ADD (SAlu ALU_SRL (SAlu ALU_ADD pN (SLit 7)) (SLit 3)) (SLit 15)) M16))) with r8 in FS.
  rewrite U_sll_lit in FS. change (2 ^ (4 mod 64)) with 16 in FS. change (bv_unsigned (eval rho pN)) with (uval rho pN) in FS. unfold M64v in FS.
  rewrite (Z.mod_small (uval rho pN * 16)) in FS by lia. rewrite (Z.mod_small (a2 + uval rho pN * 16)) in FS by lia.
  rewrite Z.mod_small in FS by lia.
  constructor; rewrite ?aceil_val; unfold PG_DEPTH, pSCR in *; try lia.
Qed.

Lemma P0_now : ltac2:(tb__ "0|3|
S3S100S4bVrho0;R1A3S53VFB;VFF;Vrho0;A3S21S20S36S128Z6S103S2dS2dS0S0A2M0S0A2G0S35G0S0A2VFF;A4A2U0A3S21S121VFF;S45R3S9PcA1A2Z48A3S21S121VFF;S45R3S9PdA1A2Z18A3S21S54VFB;S45R3S85A2S3fZcM1S45R3S7dA2M2A2A3S21S54VFB;S45R3S84A2S3fG1S42G2Z2A2A2A3S54VFB;S45R3S80A2S45R3S9P12A1A2A3A2A2A2A2A2F_;F_;Frho;").
Proof.
  intros rho Hav (A & B & C & D & E & F). unfold uval, pPTS, pOUT, pSCR, pN. cbn [eval].
  rewrite <- (proj1 Hav 12%positive eq_refl), <- (proj1 Hav 13%positive eq_refl), <- (proj1 Hav 14%positive eq_refl), <- (proj1 Hav 15%positive eq_refl),
          <- (proj1 Hav 16%positive eq_refl), <- (proj1 Hav 17%positive eq_refl), <- (proj1 Hav 18%positive eq_refl).
  repeat (split; [assumption|]). assumption.
Qed.

Abbreviation sz16n := (SAlu ALU_SLL pN (SLit 4)).
Abbreviation sz4n := (SAlu ALU_SLL pN (SLit 2)).
Abbreviation szr := (SAlu ALU_SRL (SAlu ALU_ADD pN (SLit 7)) (SLit 3)).
Definition extra_tab : list (sv * sv * sv) := ltac2:(tb__ "0|8|
S31S2dS2dS2S2A2M0S2A2M1S2eG0S2S2eS2S2S9PcA1S5Z0A1M2A4S5Z48A1A4S31G1S2eG0S2S2eS2S2S9PdA1M3G2A4M4S5Z18A1M5A4S31G1S2eG0S2G4S5Z10A1M6A4S31G1S2eG0S2S2eS2S2G3G6A4G5A4S31G1S2eG0S2S2eS2S2S85G2A4S87A4S31G1S2eG0S2S2eS2S2S84G2A4S88A4S31G1S2eG0S2S2eS2S2S80G2A4ScS11cS7dS5Z4A1A3A4S31G1S2eG0S2S2eS2S2S89G2A4ScS11cS7dS5Z2A1A3M7A4S31G1S2eG0S2S2eS2S2S8aG2A4G7A4S31G1S2eG0S2S2eS2S2S8bG2A4ScS11dScS11bS7dS5Z7A1A3S5Z3A1A3A4S2fG1A1A3A3A3A3A3A3A3A3A3A3").
Definition extraO (o : sobj) : bool := ltac2:(tb__ "0|3|
S6dS2dS2dS2S2A2M0S2A2M1G1S3aS3aS16S11Vo;A1S35S2S2S35G0S2R1A3M2A3A2S16S1aVo;A1S37S2S2G2A3A2A2S16S19Vo;A1S37G0S2R1A3A2A2Lt;SfeA3").
Definition extraX_tab : list (sv * sv) := ltac2:(tb__ "0|2|
S31S2dS2S2A2M0S2eS2S2S9PcA1S5Z48A1A4S31G0S2eS2S2S9PdA1S5Z18A1A4S31G0S2eS2S2S85S87A4S31G0S2eS2S2S84S88A4S31G0S2eS2S2S80ScS11cS7dS5Z4A1A3A4S31G0S2eS2S2S89ScS11cS7dS5Z2A1A3M1A4S31G0S2eS2S2S8aG1A4S31G0S2eS2S2S8bScS11dScS11bS7dS5Z7A1A3S5Z3A1A3A4S2fG0A1A3A3A3A3A3A3A3A3").
Definition extraX (r : sv * sv) : bool := existsb (xr_eqb r) extraX_tab.

Definition in_callers (rho : valuation) (a : Z) : Prop := ltac2:(tb__ "0|7|
S22S21S3cS45Vrho;S9PcA1A2M0Va;A2S3eVa;S3dG0Z48A2A2A2S22S21S3cS45Vrho;S9PdA1A2M1Va;A2S3eVa;S3dG1Z18A2A2A2S22S21S3cS45Vrho;S85A2M2Va;A2S3eVa;S3dG2S3fZcM3S45Vrho;S7dA2M4A2A2A2A2S22S21S3cS45Vrho;S84A2M5Va;A2S3eVa;S3dG5S3fG3S42G4Z2A2A2A2A2A2S21S3cS45Vrho;S80A2M6Va;A2S3eVa;S3dG6S45Vrho;S9P12A1A2A2A2A2A2A2A2A2").

Lemma uval_add_neglit : ltac2:(tb__ "0|0|
S3S2S0S3eR1Z0A2S3cS41R2A1S45R4R3A2A2S3cS41S40Z2Z3fA2A1R3A2S20S0S45R6ScS11bR5S5R4A1A3A2S3dS45R6R5A2R4A2A3F_;F_;F_;Fk;Fa;Frho;").
Proof.
  intros rho a k Hk Ha Hk2. unfold uval in *. rewrite U_add, U_lit. pose proof (U_range (eval rho a)) as R. unfold M64v in *.
  rewrite Zplus_mod_idemp_r. apply Z.mod_small. lia.
Qed.

Record extz (rho : valuation) : Prop := EZ {
  ez_n12 : uval rho n12 = 12 * uval rho pN;
  ez_o12 : uval rho o12 = 12 * (uval rho pN - 2);
  ez_16n : uval rho sz16n = 16 * uval rho pN;
  ez_4n : uval rho sz4n = 4 * uval rho pN;
  ez_r : uval rho szr = (uval rho pN + 7) / 8;
  ez_nxt : uval rho pNXT = uval rho pSCR + 16 * uval rho pN;
  ez_prv : uval rho pPRV = uval rho pSCR + 16 * uval rho pN + uval rho A16;
  ez_rfx : uval rho pRFX = uval rho pSCR + 16 * uval rho pN + 2 * uval rho A16;
  ez_a16 : 4 * uval rho pN <= uval rho A16 <= 4 * uval rho pN + 15;
  ez_fit : 16 * uval rho pN + 2 * uval rho A16 + (uval rho pN + 7) / 8 <= uval rho (SVar 18) }.
Lemma extz_of : ltac2:(tb__ "0|0|
S3SfaR1A1SffR2A1F_;Frho;").
Proof.
  intros rho [Bsp BD Bwin Bn Bres Bscr Bneed Ba16 Btop]. rewrite aceil_val in *.
  assert (E12 : uval rho n12 = 12 * uval rho pN) by (unfold n12; rewrite uval_mul_comm, uval_mul_lit; lia).
  assert (Em2 : uval rho nm2 = uval rho pN - 2) by (unfold nm2; rewrite uval_add_neglit; lia).
  assert (Eo12 : uval rho o12 = 12 * (uval rho pN - 2)) by (unfold o12; rewrite uval_mul_comm, uval_mul_lit; rewrite ?Em2; lia).
  assert (E16 : uval rho sz16n = 16 * uval rho pN).
  { unfold uval. rewrite U_sll_lit. change (2 ^ (4 mod 64)) with 16. change (bv_unsigned (eval rho pN)) with (uval rho pN). unfold M64v. rewrite Z.mod_small by lia. lia. }
  assert (E4 : uval rho sz4n = 4 * uval rho pN).
  { unfold uval. rewrite U_sll_lit. change (2 ^ (2 mod 64)) with 4. change (bv_unsigned (eval rho pN)) with (uval rho pN). unfold M64v. rewrite Z.mod_small by lia. lia. }
  assert (Er : uval rho szr = (uval rho pN + 7) / 8).
  { unfold uval. rewrite U_srl_lit, U_add, U_lit. change (2 ^ (3 mod 64)) with 8. unfold M64v. change (bv_unsigned (eval rho pN)) with (uval rho pN).
    change (7 mod 2 ^ 64) with 7. rewrite Z.mod_small by lia. reflexivity. }
  pose proof (Z.mod_pos_bound (4 * uval rho pN + 15) 16 ltac:(lia)) as M16B.
  assert (HD8 : 0 <= (uval rho pN + 7) / 8) by (apply Z.div_pos; lia).
  assert (EN : uval rho pNXT = uval rho pSCR + 16 * uval rho pN) by (unfold pNXT; rewrite uval_add_small by (rewrite E16; lia); rewrite E16; reflexivity).
  assert (EP : uval rho pPRV = uval rho pSCR + 16 * uval rho pN + uval rho A16) by (unfold pPRV; rewrite uval_add_small by (rewrite EN; lia); rewrite EN; reflexivity).
  assert (ER : uval rho pRFX = uval rho pSCR + 16 * uval rho pN + 2 * uval rho A16) by (unfold pRFX; rewrite uval_add_small by (rewrite EP; lia); rewrite EP; lia).
  constructor; try assumption; lia.
Qed.

Lemma obj_rangeZ : ltac2:(tb__ "0|2|
S3S4S0S0S0S21S3cS35S0S0S14R5R4A2M0A3R3A2S3eR3S37S0S0G0A3A2A2S20S0S1bR6S1aR5A1A2R3A3S20S0S1bR7S19R6A1A2R3A3S21S3cS3dS45R8S11R7A1A2M1R5A2R6A2S3eR6S3dG1R4A2A2A2F_;F_;F_;Fhi;Flo;Fa;Fo;Frho;").
Proof. intros rho o a lo hi Hr <- <-. unfold obj_range, obj_lo_of, obj_hi_of in Hr. unfold uval. exact Hr. Qed.

Lemma extraO_sound : ltac2:(tb__ "0|1|
S3S4S0SfaR3A1S20S30Sf8R3A1S32A3S21S3cS35S0S0S14R5R4A2M0A3R3A2S3eR3S37S0S0G0A3A2A2SfcR6R4A2F_;F_;F_;Fa;Fo;Frho;").
Proof.
  intros rho o a BZ HE Hr. pose proof (extz_of rho BZ) as [E12 Eo12 E16 E4 Er EN EP ERF EA EF]. destruct BZ as [Bsp BD Bwin Bn Bres Bscr Bneed Ba16 Btop].
  rewrite aceil_val in *. pose proof (Z.mod_pos_bound (4 * uval rho pN + 15) 16 ltac:(lia)) as M16B. assert (HD8 : 0 <= (uval rho pN + 7) / 8) by (apply Z.div_pos; lia).
  unfold extraO in HE. apply existsb_exists in HE as (t & Hin & Heq).
  apply andb_prop in Heq as [Heq Hh]. apply andb_prop in Heq as [Hb Hl]. apply sv_eqb_sound in Hb. apply sv_eqb_sound in Hl. apply sv_eqb_sound in Hh.
  unfold in_callers.
  cbn [extra_tab In] in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]; cbn [fst snd] in Hb, Hl, Hh;
    (eapply obj_rangeZ in Hr; [| rewrite Hl; first [apply soff_lit_small; lia | apply soff_smallu; lia] | rewrite Hh; first [apply soff_lit_small; lia | apply soff_smallu; lia]]);
    rewrite Hb in Hr; rewrite ?E12, ?Eo12, ?E16, ?E4, ?Er, ?EN, ?EP, ?ERF in Hr; unfold pPTS, pOUT, pSCR in *; lia.
Qed.

Lemma extraX_sound : ltac2:(tb__ "0|1|
S3S2dS2S2A2S0SfaR3A1S20S30Sf7R3A1S32A3S21S3cS45R5S35S2S2R4A3A2M0R3A2S3eR3S3dG0S45R5S37S2S2R4A3A2A2A2A2SfcR6R4A2F_;F_;F_;Fa;Fr;Frho;").
Proof.
  intros rho r a BZ HE Hr. pose proof (extz_of rho BZ) as [E12 Eo12 E16 E4 Er EN EP ERF EA EF]. destruct BZ as [Bsp BD Bwin Bn Bres Bscr Bneed Ba16 Btop].
  rewrite aceil_val in *. pose proof (Z.mod_pos_bound (4 * uval rho pN + 15) 16 ltac:(lia)) as M16B. assert (HD8 : 0 <= (uval rho pN + 7) / 8) by (apply Z.div_pos; lia).
  unfold extraX in HE. apply existsb_exists in HE as (t & Hin & Heq). apply xr_eqb_sound in Heq. subst t.
  unfold in_callers. cbn [extraX_tab In] in Hin.
  destruct Hin as [E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]; destruct r as [b l]; injection E as <- <-; cbn [fst snd] in Hr;
    rewrite ?uval_lit in Hr by lia; rewrite ?E12, ?Eo12, ?E16, ?E4, ?Er, ?EN, ?EP, ?ERF in Hr; unfold pPTS, pOUT, pSCR in *; lia.
Qed.

Lemma in_callers_pclMA : ltac2:(tb__ "0|0|
S3S0S2cS2dS2S2A2A1S2cS2dS2dS2S0A2S2A2A1S100S4bVrho0;R4A3S53VFB;VFF;Vrho0;A3SfcR6R5A2S122VCST;Vrho0;S117VFB;R7R5A3S123VFF;R7R4A3R6A5F_;F_;F_;Ffrs;Fkept;Fa;Frho;").
Proof.
  intros rho a kept frs Hav HP0 H. destruct (P0_now rho Hav HP0) as (_ & HD & HR & HP & HO & HS).
  destruct H as [H|[H|[H|[H|H]]]].
  - destruct HD as (f & sz & fl & Hin & H1 & H2). right; right; right. exists f, sz, fl. split; [apply In_FFx; left; exact Hin | lia].
  - destruct HR as (f & sz & fl & Hin & H1 & H2). right; right; right. exists f, sz, fl. split; [apply In_FFx; left; exact Hin | lia].
  - destruct HP as (b & m & Hin & H1 & H2). right; right; left. exists b, m. split; [apply In_FBx; left; exact Hin | lia].
  - destruct HO as (b & m & Hin & H1 & H2). right; right; left. exists b, m. split; [apply In_FBx; left; exact Hin | lia].
  - destruct HS as (b & m & Hin & H1 & H2). right; right; left. exists b, m. split; [apply In_FBx; left; exact Hin | lia].
Qed.

Definition robjs_checkP (facts : list sprop) (fr : list (sv * Z * sv)) (skip : option nat) (R : list sobj) : bool := ltac2:(tb__ "0|1|
S6bS4S4S30S30L_;M0S12cVfacts;R1A2S32G0S110Vfr;U0Vskip;R1A4S32Sf8R1A1X30x2X30x2Lo;VR;A3").

Ltac top_rng H := match type of H with context [topG ?G] => let TG := fresh "TG" in pose proof (topG_range G) as TG end.

Lemma robjs_checkP_sound : ltac2:(tb__ "0|4|
S90S3S2cS7A1S2cS2dS2S2A2A1S2cS2dS2dS2S0A2S2A2M0A1M1S33S36A1M2S2cS4A1S3S2cS43Q40A1A1S93VAInv;RaR3R2R1A4S102S7SdRaA1R9A3S20S30Sf6RaA1S32A3S100S4bVrho0;RcA3S53VFB;VFF;Vrho0;A3S114ReS119Vrho0;A1A2S57VFF;R10RfRcA4S20S30SfbRfRdRcRbA4S32A3G2G1Lskip;RdS36S118G0R1RfA3Li;ReX33x2G1S4S0S6aS4R2RfA3S21S3cS35S0S0S14R15R3A2M3A3R2A2S3eR2S37S0S0G3A3A2A2S122VCST;Vrho0;S117VFB;R16R14A3S123VFF;R16R5A3R3A5F_;F_;Fa;Fo;Tfrs;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FR;Fskip;Ffr;Ftv;Ffacts;Frho;FAi;").
Proof.
  intros Ai rho facts tv fr skip R rho1 tp1 md1 HM HF HB Hav HP0 HT0 HFR Hchk frs o a Ho Hr.
  unfold robjs_checkP in Hchk. pose proof (proj1 (forallb_forall _ _) Hchk o Ho) as Hc. cbn beta in Hc.
  apply lazy_orb_prop in Hc as [Hc|Hc]; [left; exact (robj_stackA_sound facts rho _ o a HF HT0 Hc Hr)|].
  apply lazy_orb_prop in Hc as [Hc|Hc].
  { destruct (robj_ownframe_sound fr 0 skip o Hc) as (j & x & lo & hi & Hj & Hsk & Hb & Hl & Hh & H1 & H2 & H3 & Hc6). rewrite Nat.add_0_l in Hsk.
    pose proof (nth_error_In _ _ Hj) as Hinx.
    pose proof (proj1 (Forall_forall _ _) (proj1 HFR) x Hinx) as (X1 & _ & _).
    destruct (law_blocks _ _ _ ALA Ai rho1 tp1 md1 HM) as (_ & _ & HFrl).
    destruct (HFrl _ _ X1) as (_ & _ & _ & F4 & F5 & _). top_rng F5.
    assert (Hin' : In x frs).
    { subst frs. destruct skip as [i|]; [|exact Hinx]. eapply In_remove_nth_ne; [exact Hj | intros ->; apply Hsk; reflexivity]. }
    right; right; right. exists (fst (frv rho x)), (snd (frv rho x)), (uval rho (snd x)). split.
    - apply In_FFx. right. exists x. split; [exact Hin' | reflexivity].
    - unfold obj_range, obj_lo_of, obj_hi_of in Hr. rewrite Hb, Hl, Hh in Hr.
      pose proof (fs_frame_size_bounds (snd (fst x))) as B.
      unfold frv in *. cbn [fst snd] in *. unfold uval in *. unfold IMG_HI, HIGH_SHADOW_END in *.
      pose proof (fs_frame_size_bounds' (snd (fst x)) Hc6) as Bsz.
      rewrite !soff_lit_small in Hr by lia. cbn [fst snd] in Hr. lia. }
  apply in_callers_pclMA; [exact Hav | exact HP0 |]. eapply extraO_sound; [eapply basez_of; [exact HF | exact HB] | exact Hc | exact Hr].
Qed.

Lemma pclMA_lt47 : ltac2:(tb__ "0|1|
S90S3S2cS43Q40A1A1S93S2cS2dS0S0A2M0A1S2cS2dG0S0A2A1S0VAInv;R7R6R5R4A4S5bR4R8A2S5cR4R9A2S122VCST;Vrho0;R6R5R4A5S21S3cZ0R5A2S3eR5S40Z2Z2fA2A2A2F_;F_;F_;F_;Fa;FFFc;FFBc;Fmd1;Ftp1;Frho1;FAi;").
Proof.
  intros Ai rho1 tp1 md1 FBc FFc a HM HB HFF [H|[H|[(b & n & Hin & Hr)|(f & sz & fl & Hin & Hr)]]].
  - unfold T0 in H. pose proof (bv_urange (rw rho0 Contract.V_TOP)). lia.
  - pose proof (HCST a (proj1 H)). unfold IMG_HI, LOW_SHADOW_BEG in *. lia.
  - destruct (law_blocks _ _ _ ALA Ai rho1 tp1 md1 HM) as (_ & HBl & _). destruct (HBl b n (HB _ Hin)) as (B1 & _ & B3 & B4 & _).
    top_rng B4. lia.
  - destruct (law_blocks _ _ _ ALA Ai rho1 tp1 md1 HM) as (_ & _ & HFr). destruct (HFr f sz (proj1 (HFF _ _ _ Hin))) as (_ & _ & F3 & F4 & F5 & _).
    top_rng F5. unfold IMG_HI in F4. lia.
Qed.

Lemma xrs_ok_site : ltac2:(tb__ "0|4|
S90S3S2cS7A1S2cS2dS2S2A2A1M0S2cS2dS2dS2S0A2S2A2M1A1M2S33S36A1M3S2cS4A1G0S3S2cS43Q40A1A1S93VAInv;RbR3R2R1A4S102S7SdRbA1RaA3S20S30Sf6RbA1S32A3S100S4bVrho0;RdA3S53VFB;VFF;Vrho0;A3S58Vrho0;R10A2S114R10S92S91R11A1A1A2S5aVFB;R12R11RfA4S115R12R10A2S116R13R11A2S57VFF;R15R14R11A4S20S30S109VXGL;R14R13R12R11R10Sf7RfA8S32A3S125VCST;VXGL;Vrho0;VFB;VFF;R16R14G3G2Lskip;R12S36S118G1R1R14A3Li;R13X33x2R10A9F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FX;Fobjs;Fskip;Ffr;Ftv;Ffacts;Frho;FAi;").
Proof.
  intros Ai rho facts tv fr skip objs X rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HN HD HZ HFR Hchk.
  apply (xrs_checkL_sound segs AInv CST XGL ALA rho0 FB FF Ai rho facts tv fr skip objs extraX X rho1 tp1 md1 HM HF (T_ok_T0 rho0 _ Ai HT HTK) HN HD HZ HFR Hchk).
  intros r a Hr HE Ha. left. apply in_callers_pclMA; [exact Hav | exact HP0 |]. eapply extraX_sound; [eapply basez_of; [exact HF | exact HB] | exact HE | exact Ha].
Qed.

Lemma robjs_okF_site : ltac2:(tb__ "0|0|
S90S3S2cS7A1S2cS2dS2S2A2A1S2cS2dS2dS2S0A2S2A2A1S2cS4A1S3S2cS43Q40A1A1S93VAInv;R9R3R2R1A4S102S7SdR9A1R8A3S20S30Sf6R9A1S32A3S100S4bVrho0;RbA3S53VFB;VFF;Vrho0;A3S58Vrho0;ReA2S114ReS92S91RfA1A1A2S5aVFB;R10RfRdA4S115R10ReA2S116R11RfA2S57VFF;R13R12RfA4S20S30S10eR12R11R10S39S36A1Sf8RfA6S32A3S13eVCST;Vrho0;VFB;VFF;R14R12R11R10A8F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FR;Ffr;Ftv;Ffacts;Frho;FAi;").
Proof.
  intros Ai rho facts tv fr R rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HN HD HZ HFR Hchk o a Ho Hr.
  apply (robjs_checkF_sound segs AInv CST ALA rho0 FB FF Ai rho facts tv fr None extraO R rho1 tp1 md1 HM HF (T_ok_T0 rho0 _ Ai HT HTK) HN HD HZ HFR Hchk) with (o := o); [|exact Ho|exact Hr].
  intros o' a' Ho' HE Hr'. left. apply in_callers_pclMA; [exact Hav | exact HP0 |]. eapply extraO_sound; [eapply basez_of; [exact HF | exact HB] | exact HE | exact Hr'].
Qed.

Lemma frozen_stableA' : ltac2:(tb__ "0|0|
S1S1S55S3S138S4bR3A2S20S30S59R4R3A2S32A3S4aS3bR6S63VAInv;VCST;VXGL;S4bVKc;Vrho0;S53VFB;VFF;A2VFB;VFF;VBX;S56R4R3AdA3F_;F_;Frho;Fnd;Fm;Fn;").
Proof.
  intros n m nd rho Hm Hb r r' tp tr md md' _ Hme (Ai & kc & HJ). exists Ai, kc.
  eapply (JAi_stable segs AInv CST XGL NF Kc rho0 (P0_pg FB FF) FB FF BX PTrue HKc ALA m nd Ai kc rho rho tp tr md md'); [exact Hm | exact Hb | apply agree_below_refl | exact Hme | exact HJ].
Qed.

Lemma payA_nil : ltac2:(tb__ "0|2|
S2cS7A1S12bS4bVrho0;S53VFB;VFF;A2R1S5Z0M0A1G0S2fS46A1M1G1A8Ffacts;").
Proof.
  intros facts. split; [reflexivity|]. split; [lia|]. intros rho HF _ _ Hn. unfold pay_sem. rewrite uval_lit by lia. split; [cbn; lia|]. split; [cbn; lia | exact Hn].
Qed.

Section X.
Variable TR : assn -> assn -> Prop.
Variable FAM : ltac2:(tb__ "0|0|
S0S2cS43Q40A1A1Sf2F_;F_;").
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S48S26S3S2cS43Q40A1A1Sf2S102S7SdR3A1S6S27R4A1A1A3VTR;S47S3bR6R5R4R3A5R2A2M0F_;G0F_;FQ;Ftp;Frho;FS;FJ;").
Hypothesis TR_ex : forall (T : Type) (J : T -> jpredA) S rho tp (Q : assn),
  (forall x, TR (SPA segs (J x) S rho tp) Q) -> TR (SPA segs (fun r p t m => exists x, J x r p t m) S rho tp) Q.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
Sf2Sf2Sf2Sf3R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_false : ltac2:(tb__ "0|0|
Sf2Sf2Sf3S25R3R1A1A1Fw;VTR;R3R2A2F_;FQ;FP;").
Hypothesis TR_exw : forall (T : Type) (P : T -> assn) (Q : assn), (forall a, TR (P a) Q) -> TR (fun w => exists a, P a w) Q.
Hypothesis TR_callP : ltac2:(tb__ "0|5|
S48S48S26S26S104S2cS4A1M0S2cS2dS26S4cA2M1A1S2cS2dS2S2A2M2A1Sf2S3S2cS43Q40A1A1M3G2S6aG2R1R5A3S6aG2R2S28RbA1A3F_;Fr;S20S33G0A1S4eRaR9R8A3S34G0R7A2A3S20S30S50RbRaR9R8S103G1S26S35S26S4cA2R7A4A5S32A3S3G3VTR;S47S3bRfRdR2R1A5S4dS3bSaS27RdA1A1R2R1RaA5A2Ftp1;Frho1;S2cS94A1M4S11aS93S49S3bR9R8R10S2eG4S12eR3S12fR2R1A2A4A5R13RaR9R4R2A4R13S107S106RbRfS108R3RaR4A3A3R10A2RaR5R3A4F_;F_;Fmd;Fms;Ftr;S26S4cG4S11aS93S3G3G4S11aS93S6aG1S2eS26S4cRaR9A4R14A3S49S3bR12R11R19S2eG4S12eR9S12fR8R7A2A4A5R1cR13R12RaR8A4S100SaS27R1aA1A1S107S106R14R18S108R9R13RaA3A3R19A2R8A3S49S3bR9R8ReS2eG4S12eR7S12fR6R5A2A4A5ReS107S106R16R1aS108RbR15RcA3A3R1bA2R15RaR9R8R6A6S21S13cR17S108RcR16RdA3R1bR1cR1dR10R1eR19RbA9S3S101R18S108RdR17ReA3R1cR1dS27R1eA1S27R1fA1S27R11A1R1RcA9VTR;S47S3bS52R11S107S106R19R1dS108ReR18RfA3A3R1eA2R18RdRcA5S13dR1eR1fR12R20R1dR1bA6R2RcA5R1aA2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S47S3bR11RfR8R7A5R9A2F_;F_;F_;F_;F_;F_;Ftp;Frho;FQ;FXk;FPosts;FR;Fs;FPre;FC;FJp;FJ;").

Hypothesis CSM : ltac2:(tb__ "0|2|
S90S3S2cS43Q40A1A1VTR;S47S3bS77VAInv;Z6M0R3VKc;A4Sd3R2R1A5S4dS3bS4bR2R1S31S2dS26S4cA2M1S2eS26S4cSd0S75VAInv;VCST;VXGL;G0R3VKc;A6A4S2fG1A1A3A5A2Ftp1;Frho1;FAi;").
Hypothesis CSF : ltac2:(tb__ "0|2|
S90S3S2cS43Q40A1A1VTR;S47S3bS76VAInv;Z6M0R3VKc;A4S9dR2R1A5S4dS3bS4bR2R1S31S2dS26S4cA2M1S2eS26S4cSa6S74VAInv;VCST;VXGL;G0R3VKc;A6A4S2fG1A1A3A5A2Ftp1;Frho1;FAi;").
Hypothesis CF8 : ltac2:(tb__ "0|1|
S90S3S2cS43Q40A1A1VTR;S47S3bS71VAInv;R3VKc;A3Sd2R2R1A5S4dS3bS4bR2R1S31S2dS26S4cA2M0S2eS26S4cScfS70VAInv;VCST;VXGL;R3VKc;A5A4S2fG0A1A3A5A2Ftp1;Frho1;FAi;").
Hypothesis C00 : ltac2:(tb__ "0|1|
S90S3S2cS43Q40A1A1VTR;S47S3bS71VAInv;R3VKc;A3Sd1R2R1A5S4dS3bS4bR2R1S31S2dS26S4cA2M0S2eS26S4cSceS70VAInv;VCST;VXGL;R3VKc;A5A4S2fG0A1A3A5A2Ftp1;Frho1;FAi;").

Hypothesis CALL_sc : ltac2:(tb__ "0|2|
S26S104S2cS4A1M0S3S2cS43Q40A1A1S55Sf2S20S33G0A1S4eR7S111R6A3S34G0R5A2A3S20S30S4fR8S111R7R6S103S29S26S2aS113A4A5S32A3S20S30S137S4bSaS27R9A1A1A2S32A3S20S30S59SaS27RaA1A1R5A2S32A3S20S30S6bS7S1cSaS27RbA1M1A1A1S6G1A1A3S32A3S29S3S6aS29R2S113A3S18SaS27RfA1A1RcR2A3VTR;S47S3bVJAv;RbA1S139S6S27R10A1A1S51RfS111S2aR4A1R10ReA5A2R3RcA5RaA2F_;F_;Frho';FL;VTR;S47S3bVJAv;R8A1RdRaR9A5R7A2F_;F_;F_;F_;F_;F_;FQ;Fnd;Ftp;Frho;FR;Fs;FCl;").
Hypothesis CALL_r2 : ltac2:(tb__ "0|2|
S26S104S2cS4A1M0S3S2cS43Q40A1A1S55Sf2S20S33G0A1S4eR7S11eR6A3S34G0R5A2A3S20S30S4fR8S11eR7R6S103S29S26S2aS11fA4A5S32A3S20S30S137S4bSaS27R9A1A1A2S32A3S20S30S59SaS27RaA1A1R5A2S32A3S20S30S6bS7S1cSaS27RbA1M1A1A1S6G1A1A3S32A3S29S3S6aS29R2S11fA3S18SaS27RfA1A1RcR2A3VTR;S47S3bVJAv;RbA1S139S6S27R10A1A1S51RfS11eS2aR4A1R10ReA5A2R3RcA5RaA2F_;F_;Frho';FL;VTR;S47S3bVJAv;R8A1RdRaR9A5R7A2F_;F_;F_;F_;F_;F_;FQ;Fnd;Ftp;Frho;FR;Fs;FCl;").
Hypothesis REENTER : ltac2:(tb__ "0|4|
S26S55S2dS0S2A2M0S3S2cS43Q40A1A1M1S0G1S6aS2dS2dS26S55A2M2G0A2S2eG2G0S2eS26S55R7R6A4R5A4Sc5A3S21S3cZ0S5eS2eG2G0S2eS26S55R8R7A4R6A4R5A2M3A2S3eG3R3A2A2VTR;S47S3bVJAv;R8A1R9R6R5A5VFAM;R4R3A2A2F_;F_;Ftp0;Fb;Ftp;Frho;Frv;Fnd;FT;").
Hypothesis POST : ltac2:(tb__ "0|1|
S26S55S3S2cS43Q40A1A1M0S0G0S6aS2dS26S4cA2S2eS26S4cR6SfdR5A1A4Sf9A3VTR;S47S3bVJAv;R6A1R7R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;Fnd;FP;").

Ltac meas := unfold emeasA; cbn [eda_rank eda_var fst snd z0 eval]; rewrite lit_unsigned; cbn; lia.

Tactic Notation "innth" integer(k) := cbn [In cutsE]; do k right; left; reflexivity.

Lemma X_E_sm : ltac2:(tb__ "0|1|
S3S2cS43Q40A1A1M0S0G0S3cS3fZ61S40Z2Z40A2A2R2A2VTR;S47S3bVJAv;S9cA1Sc1R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply TR_facts. intros HF.
  apply (smalloc_callT segs AE_A AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_pg FB FF) FB FF BX PTrue HKc TR TR_facts TR_ex TR_pre TR_callP
           6 E_sm0 s_sm R_sm rho tp nd0 110 120 (FAM b tp0) CSM).
  - lia.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - intros A A' _; exact I.
  -
    intros Ai ms HF' HP0 Hav HBf HFF HN HD HZ HFR (rho1 & tp1 & md1 & HM) HT HTK. destruct (P0_now rho Hav HP0) as (HC0 & _).
    assert (HBc : fbinA (FBx FB rho []) Ai) by (apply (fbinA_FBx FB Ai rho [] []); [exact HBf | exact HN]).
    assert (HFc : ffinA (FFx FF rho []) Ai) by (apply ffinA_FFx; [exact HFF | exact HFR]).
    split; [|split].
    + intros o a Ho Hr. apply (pclMA_cmaddrA CST rho0 (FBx FB rho []) (FFx FF rho []) Ai a HBc HFc HT).
      eapply (robjs_checkP_sound Ai rho _ [] [] None R_sm rho1 tp1 md1 HM HF' ltac:(vm_compute; reflexivity) Hav HP0 (T_ok_T0 rho0 _ Ai HT HTK) HFR ltac:(vm_compute; reflexivity)); [exact Ho | exact Hr].
    + intros r a Hr Ha.
      destruct (xrs_ok_site Ai rho _ [] [] None (ss_objs (ax_S E_sm0)) (ax_X E_sm0) rho1 tp1 md1 HM HF' ltac:(vm_compute; reflexivity) Hav HP0 HT HTK HN HD HZ HFR
                  ltac:(vm_compute; reflexivity) r a Hr Ha) as [H|H]; [left; exact (pclMA_cmaddrA CST rho0 _ _ Ai a HBc HFc HT H) | right; exact H].
    + split; [change (wsub_get s_sm 12) with (SLit 2208); rewrite uval_lit by lia; change (fs_frame_size 6) with 4096; lia|].
      unfold ffpairs. change (map (fun y : Z * Z * Z => fst y) FF) with (map fst FF). rewrite HC0. cbn. lia.
  -
    intros rho' tp'. rewrite T_sm0_eq.
    eapply TR_pre with (P := SPA segs (JAv ndF) T_sm1 rho' tp').
    { intros w Hw. exact (SPA_axforms segs _ [AXSelect (sel_last T_sm0 3)] rho' T_sm0 T_sm1 tp' w T_sm1_eq Hw). }
    apply (TR_pre (fun w => exists rho2, SPA segs (JAv ndF) C_pro rho2 tp' w)).
    { intros w Hw.
      destruct (JA_frame_open segs HTOP AInv CST XGL ALA HCST HXGL LFLAG NF Kc rho0 (P0_pg FB FF) FB FF BX PTrue HKc HBX HNP [] [(vF, 6, vFL)] [] ANone 0%nat 110 6 120
                  T_sm1 (objs_butlast T_sm1) X_pg [] rho' tp' w eq_refl ltac:(lia) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                  ltac:(vm_compute; reflexivity) eq_refl eq_refl) as (rho2 & _ & Hw2); [| exact Hw |].
      - intros Ai rho1 tp1 md1 HF2 HP0 Hav HM HT HTK HBf HFF HN HDt HZt HFR. rewrite app_nil_r.
        apply (xrs_ok_site Ai rho' _ [] [(vF, 6, vFL)] (Some 0%nat) (ss_objs (ax_S T_sm1)) X_pg rho1 tp1 md1 HM HF2 ltac:(vm_compute; reflexivity) Hav HP0 HT HTK HN I ltac:(constructor) HFR).
        vm_compute. reflexivity.
      - exists rho2. rewrite C_pro0_eq in Hw2. unfold C_pro.
        apply (SPA_x_len0 segs (JAv ndF) C_pro0 110 5 rho2 tp' w); [vm_compute; reflexivity | lia | vm_compute; reflexivity | exact Hw2]. }
    apply TR_exw. intros rho2. apply (REENTER C_pro ndF (96, z0)); [innth 1 | meas].
Qed.

Lemma site_pure : ltac2:(tb__ "0|3|
S26S104S2cS4A1S3S2cS2dS2dS2S0A2S2A2A1S20S30Sf6S6S27R5A1A1A1S32A3S20S30SfbS6S27R6A1A1R2S39S36A1M0R4A4S32A3S20S30S109VXGL;S6S27R7A1M1A1S2fS2dS2S2A2A1M2R3G0S8G1A1Sf7S28R7A1A8S32A3S12dVAInv;VCST;VXGL;S4bVrho0;S53VFB;VFF;A2VFB;VFF;R8R7R6R5S62G2R4S2fS46A1S5fA4S39S0A1S90S11aS24L_;L_;AfF_;F_;F_;Ffr;Frho;FR;Fs;FE;").
Proof.
  intros E s R rho fr HB HR HX Ai ms HF HP0 Hav HBf HFF HN HD HZ HFR (rho1 & tp1 & md1 & HM) HT HTK. cbn [nd_tv nd_fr] in HN, HD, HZ, HFR.
  assert (HBc : fbinA (FBx FB rho []) Ai) by (apply (fbinA_FBx FB Ai rho [] []); [exact HBf | exact HN]).
  assert (HFc : ffinA (FFx FF rho fr) Ai) by (apply ffinA_FFx; [exact HFF | exact HFR]).
  split; [|split; [|exact I]].
  - intros o a Ho Hr. apply (pclMA_cmaddrA CST rho0 (FBx FB rho []) (FFx FF rho fr) Ai a HBc HFc HT).
    eapply (robjs_checkP_sound Ai rho _ [] fr None R rho1 tp1 md1 HM HF HB Hav HP0 (T_ok_T0 rho0 _ Ai HT HTK) HFR HR); [exact Ho | exact Hr].
  - intros r a Hr Ha.
    destruct (xrs_ok_site Ai rho _ [] fr None (ss_objs (ax_S E)) (ax_X E) rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HN HD HZ HFR HX r a Hr Ha) as [H|H];
      [left; exact (pclMA_cmaddrA CST rho0 _ _ Ai a HBc HFc HT H) | right; exact H].
Qed.

Lemma X_E_f8a : ltac2:(tb__ "0|1|
S3S2cS43Q40A1A1M0S0G0S3cS3fZ5fS40Z2Z40A2A2R2A2VTR;S47S3bVJAv;S95A1S97R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.

  apply (TR_pre (fun w => exists rho1, SPA segs (JAv ndF) E_f8a1 rho1 tp w)).
  { intros [tr [ms md]] Hw. exists (rho_absorb rho [shobj gF 0 512 shc_f8a DZero] (vms md tp ms)). rewrite <- E_f8a1_eq.
    apply (JA_shadow_release segs HTOP AInv CST XGL ALA HCST HXGL LFSH NF Kc rho0 (P0_pg FB FF) FB FF BX PTrue HKc HBX HNP [] [(vF, 6, vFL)] [] ANone 0%nat 110 6 120
             gF 0 512 shc_f8a DZero E_f8a0 (objs_butlast E_f8a0) [] rho tp tr ms md eq_refl ltac:(lia) eq_refl E_f8a0_objs ltac:(lia)
             ltac:(change (fs_frame_size 6 / 8) with 512; lia) eq_refl ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)); [|exact Hw].
    intros Ai rho1 tp1 md1 HF HP0 Hav HM HT HTK HBf HFF HN HDt HZt HFR.
    apply (robjs_okF_site Ai rho _ [] _ (objs_butlast E_f8a0) rho1 tp1 md1 HM HF ltac:(vm_compute; reflexivity) Hav HP0 HT HTK HN I ltac:(constructor) HFR). vm_compute. reflexivity. }
  apply TR_exw. intros rho1.

  eapply TR_pre with (P := SPA segs (JAv ndF) E_f8a rho1 tp).
  { intros w Hw. apply (SPA_axforms segs _ (xf_shcall E_f8a2) rho1 E_f8a2 E_f8a tp w E_f8a_eq). rewrite <- E_f8a2_eq.
    apply (JA_shadow_reopen segs HTOP AInv CST XGL ALA HCST HXGL LFSH NF Kc rho0 (P0_pg FB FF) FB FF BX PTrue HKc HBX HNP [] [(vF, 6, vFL)] [] ANone 0%nat 110 6 120
             gF 4 260 E_f8a1 X_pg rho1 tp w eq_refl ltac:(lia) eq_refl ltac:(lia) ltac:(change (fs_frame_size 6 / 8) with 512; lia)
             ltac:(vm_compute; reflexivity) (fun r H => or_intror H) ltac:(vm_compute; reflexivity)); [|exact Hw].
    intros Ai rho2 tp2 md2 HF HP0 Hav HM HT HTK HBf HFF HN HDt HZt HFR. split.
    - apply (robjs_okF_site Ai rho1 _ [] _ (ss_objs (ax_S E_f8a1)) rho2 tp2 md2 HM HF ltac:(vm_compute; reflexivity) Hav HP0 HT HTK HN I ltac:(constructor) HFR). vm_compute. reflexivity.
    - intros r y Hr Hy. left.
      exact (xrs_ok_site Ai rho1 _ [] [(vF, 6, vFL)] (Some 0%nat) (ss_objs (ax_S E_f8a1)) X_pg rho2 tp2 md2 HM HF ltac:(vm_compute; reflexivity) Hav HP0 HT HTK HN I ltac:(constructor) HFR
               ltac:(vm_compute; reflexivity) r y Hr Hy). }

  apply TR_facts. intros HF.
  apply (purec_callT segs AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_pg FB FF) FB FF BX PTrue HKc TR TR_facts TR_ex TR_pre TR_callP
           Pre_f8 [L_f8] E_f8a s_f8a R_f8a rho1 tp ndF [] (FAM b tp0)).
  - intros Ai rho2 tp2. cbn [map]. apply CF8.
  - reflexivity.
  - reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - apply payA_nil.
  - vm_compute. reflexivity.
  - apply site_pure; vm_compute; reflexivity.
  -
    intros L rho' tp' [<-|[]]. cbn [nd_tv nd_fr nd_bd nd_am]. unfold Pre_f8, L_f8. rewrite T_f8a0_eq.
    eapply TR_pre with (P := SPA segs (JAv ndF) T_f8a1 rho' tp').
    { intros w Hw. exact (SPA_axforms segs _ (xf_shback T_f8a0) rho' T_f8a0 T_f8a1 tp' w T_f8a1_eq Hw). }
    apply (TR_pre (fun w => exists rho2, SPA segs (JAv ndF) C_pro2 rho2 tp' w)).
    { intros [tr [ms md]] Hw. exists (rho_absorb rho' [shobj gF 4 260 [] DUnknown] (vms md tp' ms)). rewrite <- C_pro2_eq.
      apply (JA_shadow_reopen segs HTOP AInv CST XGL ALA HCST HXGL LFSH NF Kc rho0 (P0_pg FB FF) FB FF BX PTrue HKc HBX HNP [] [(vF, 6, vFL)] [] ANone 0%nat 110 6 120
               gF 260 276 T_f8a2 (ax_X T_f8a2) _ tp' (tr, mkCfg ms md) eq_refl ltac:(lia) eq_refl ltac:(lia) ltac:(change (fs_frame_size 6 / 8) with 512; lia)
               ltac:(vm_compute; reflexivity) (fun r H => H) ltac:(vm_compute; reflexivity)).
      - intros Ai rho2 tp2 md2 HF2 HP0 Hav HM HT HTK HBf HFF HN HDt HZt HFR. split.
        + apply (robjs_okF_site Ai _ _ [] _ (ss_objs (ax_S T_f8a2)) rho2 tp2 md2 HM HF2 ltac:(vm_compute; reflexivity) Hav HP0 HT HTK HN I ltac:(constructor) HFR). vm_compute. reflexivity.
        + intros r y Hr Hy. left.
          exact (xrs_ok_site Ai _ _ [] [(vF, 6, vFL)] (Some 0%nat) (ss_objs (ax_S T_f8a2)) (ax_X T_f8a2) rho2 tp2 md2 HM HF2 ltac:(vm_compute; reflexivity) Hav HP0 HT HTK HN I ltac:(constructor) HFR
                   ltac:(vm_compute; reflexivity) r y Hr Hy).
      - rewrite <- T_f8a2_eq.
        apply (JA_shadow_release segs HTOP AInv CST XGL ALA HCST HXGL LFSH NF Kc rho0 (P0_pg FB FF) FB FF BX PTrue HKc HBX HNP [] [(vF, 6, vFL)] [] ANone 0%nat 110 6 120
                 gF 4 260 [] DUnknown T_f8a1 (objs_butlast T_f8a1) [] rho' tp' tr ms md eq_refl ltac:(lia) eq_refl T_f8a1_objs ltac:(lia)
                 ltac:(change (fs_frame_size 6 / 8) with 512; lia) eq_refl ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)); [|exact Hw].
        intros Ai rho2 tp2 md2 HF2 HP0 Hav HM HT HTK HBf HFF HN HDt HZt HFR.
        apply (robjs_okF_site Ai rho' _ [] _ (objs_butlast T_f8a1) rho2 tp2 md2 HM HF2 ltac:(vm_compute; reflexivity) Hav HP0 HT HTK HN I ltac:(constructor) HFR). vm_compute. reflexivity. }
    apply TR_exw. intros rho2. apply (REENTER C_pro2 ndF (94, z0)); [innth 2 | meas].
Qed.

Lemma X_E_ms : ltac2:(tb__ "0|1|
S3S2cS43Q40A1A1M0S0G0S3cS3fZ5dS40Z2Z40A2A2R2A2VTR;S47S3bVJAv;S95A1S98R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  apply (TR_pre (fun w => exists rho1, SPA segs (JAv ndF) E_ms rho1 tp w)).
  { intros [tr [ms md]] Hw. exists (rho_absorb rho [shobj gF 260 276 shc_ms DUnknown] (vms md tp ms)).
    apply (SPA_axforms segs _ [AXSplit 7 (SLit 16)] _ E_ms1 E_ms tp _ E_ms_eq). rewrite <- E_ms1_eq.
    apply (JA_shadow_release segs HTOP AInv CST XGL ALA HCST HXGL LFSH NF Kc rho0 (P0_pg FB FF) FB FF BX PTrue HKc HBX HNP [] [(vF, 6, vFL)] [] ANone 0%nat 110 6 120
             gF 260 276 shc_ms DUnknown E_ms0 (objs_butlast E_ms0) [] rho tp tr ms md eq_refl ltac:(lia) eq_refl E_ms0_objs ltac:(lia)
             ltac:(change (fs_frame_size 6 / 8) with 512; lia) eq_refl ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)); [|exact Hw].
    intros Ai rho1 tp1 md1 HF HP0 Hav HM HT HTK HBf HFF HN HDt HZt HFR.
    apply (robjs_okF_site Ai rho _ [] _ (objs_butlast E_ms0) rho1 tp1 md1 HM HF ltac:(vm_compute; reflexivity) Hav HP0 HT HTK HN I ltac:(constructor) HFR). vm_compute. reflexivity. }

  apply TR_exw. intros rho1. change E_ms with C_body0.
  apply (REENTER C_body0 ndF (92, z0)); [innth 3 | meas].
Qed.

Lemma X_E_s00 : ltac2:(tb__ "0|1|
S3S2cS43Q40A1A1M0S0G0S3cS3fZ57S40Z2Z40A2A2R2A2VTR;S47S3bVJAv;S95A1Sa2R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  eapply TR_pre with (P := SPA segs (JAv ndF) E_s00 rho tp).
  { intros w Hw. apply (SPA_axforms segs _ (xf_shcall E_s00_1) rho E_s00_1 E_s00 tp w E_s00_eq). rewrite <- E_s00_1_eq.
    apply (JA_shadow_reopen segs HTOP AInv CST XGL ALA HCST HXGL LFSH NF Kc rho0 (P0_pg FB FF) FB FF BX PTrue HKc HBX HNP [] [(vF, 6, vFL)] [] ANone 0%nat 110 6 120
             gF 4 260 E_s00_0 (ax_X E_s00_0) rho tp w eq_refl ltac:(lia) eq_refl ltac:(lia) ltac:(change (fs_frame_size 6 / 8) with 512; lia)
             ltac:(vm_compute; reflexivity) (fun r H => H) ltac:(vm_compute; reflexivity)); [|exact Hw].
    intros Ai rho2 tp2 md2 HF HP0 Hav HM HT HTK HBf HFF HN HDt HZt HFR. split.
    - apply (robjs_okF_site Ai rho _ [] _ (ss_objs (ax_S E_s00_0)) rho2 tp2 md2 HM HF ltac:(vm_compute; reflexivity) Hav HP0 HT HTK HN I ltac:(constructor) HFR). vm_compute. reflexivity.
    - intros r y Hr Hy. left.
      exact (xrs_ok_site Ai rho _ [] [(vF, 6, vFL)] (Some 0%nat) (ss_objs (ax_S E_s00_0)) (ax_X E_s00_0) rho2 tp2 md2 HM HF ltac:(vm_compute; reflexivity) Hav HP0 HT HTK HN I ltac:(constructor) HFR
               ltac:(vm_compute; reflexivity) r y Hr Hy). }
  apply TR_facts. intros HF.
  apply (purec_callT segs AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_pg FB FF) FB FF BX PTrue HKc TR TR_facts TR_ex TR_pre TR_callP
           Pre_00 [L_00] E_s00 s_s00 R_s00 rho tp ndF [] (FAM b tp0)).
  - intros Ai rho2 tp2. cbn [map]. apply C00.
  - reflexivity.
  - reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - apply payA_nil.
  - vm_compute. reflexivity.
  - apply site_pure; vm_compute; reflexivity.
  - intros L rho' tp' [<-|[]]. cbn [nd_tv nd_fr nd_bd nd_am]. unfold Pre_00, L_00. rewrite T_s00_0_eq.
    eapply TR_pre with (P := SPA segs (JAv ndF) T_s00_1 rho' tp').
    { intros w Hw. exact (SPA_axforms segs _ (xf_shback T_s00_0) rho' T_s00_0 T_s00_1 tp' w T_s00_1_eq Hw). }
    apply (TR_pre (fun w => exists rho2, SPA segs (JAv ndF) C_s1 rho2 tp' w)).
    { intros [tr [ms md]] Hw. exists (rho_absorb rho' [shobj gF 4 260 [] DZero] (vms md tp' ms)). rewrite <- C_s1_eq.
      apply (JA_shadow_release segs HTOP AInv CST XGL ALA HCST HXGL LFSH NF Kc rho0 (P0_pg FB FF) FB FF BX PTrue HKc HBX HNP [] [(vF, 6, vFL)] [] ANone 0%nat 110 6 120
               gF 4 260 [] DZero T_s00_1 (objs_butlast T_s00_1) [] rho' tp' tr ms md eq_refl ltac:(lia) eq_refl T_s00_1_objs ltac:(lia)
               ltac:(change (fs_frame_size 6 / 8) with 512; lia) eq_refl ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)); [|exact Hw].
      intros Ai rho2 tp2 md2 HF2 HP0 Hav HM HT HTK HBf HFF HN HDt HZt HFR.
      apply (robjs_okF_site Ai rho' _ [] _ (objs_butlast T_s00_1) rho2 tp2 md2 HM HF2 ltac:(vm_compute; reflexivity) Hav HP0 HT HTK HN I ltac:(constructor) HFR). vm_compute. reflexivity. }
    apply TR_exw. intros rho2. apply (REENTER C_s1 ndF (86, z0)); [innth 7 | meas].
Qed.

Lemma X_E_f8b : ltac2:(tb__ "0|1|
S3S2cS43Q40A1A1M0S0G0S3cS3fZ2dS40Z2Z40A2A2R2A2VTR;S47S3bVJAv;S95A1Sa0R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  eapply TR_pre with (P := SPA segs (JAv ndF) E_f8b rho tp).
  { intros w Hw. apply (SPA_axforms segs _ (xf_shcall E_f8b1) rho E_f8b1 E_f8b tp w E_f8b_eq). rewrite <- E_f8b1_eq.
    apply (JA_shadow_reopen segs HTOP AInv CST XGL ALA HCST HXGL LFSH NF Kc rho0 (P0_pg FB FF) FB FF BX PTrue HKc HBX HNP [] [(vF, 6, vFL)] [] ANone 0%nat 110 6 120
             gF 4 260 E_f8b0 (ax_X E_f8b0) rho tp w eq_refl ltac:(lia) eq_refl ltac:(lia) ltac:(change (fs_frame_size 6 / 8) with 512; lia)
             ltac:(vm_compute; reflexivity) (fun r H => H) ltac:(vm_compute; reflexivity)); [|exact Hw].
    intros Ai rho2 tp2 md2 HF HP0 Hav HM HT HTK HBf HFF HN HDt HZt HFR. split.
    - apply (robjs_okF_site Ai rho _ [] _ (ss_objs (ax_S E_f8b0)) rho2 tp2 md2 HM HF ltac:(vm_compute; reflexivity) Hav HP0 HT HTK HN I ltac:(constructor) HFR). vm_compute. reflexivity.
    - intros r y Hr Hy. left.
      exact (xrs_ok_site Ai rho _ [] [(vF, 6, vFL)] (Some 0%nat) (ss_objs (ax_S E_f8b0)) (ax_X E_f8b0) rho2 tp2 md2 HM HF ltac:(vm_compute; reflexivity) Hav HP0 HT HTK HN I ltac:(constructor) HFR
               ltac:(vm_compute; reflexivity) r y Hr Hy). }
  apply TR_facts. intros HF.
  apply (purec_callT segs AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_pg FB FF) FB FF BX PTrue HKc TR TR_facts TR_ex TR_pre TR_callP
           Pre_f8 [L_f8] E_f8b s_f8b R_f8b rho tp ndF [] (FAM b tp0)).
  - intros Ai rho2 tp2. cbn [map]. apply CF8.
  - reflexivity.
  - reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - apply payA_nil.
  - vm_compute. reflexivity.
  - apply site_pure; vm_compute; reflexivity.
  - intros L rho' tp' [<-|[]]. cbn [nd_tv nd_fr nd_bd nd_am]. unfold Pre_f8, L_f8. rewrite T_f8b0_eq.
    eapply TR_pre with (P := SPA segs (JAv ndF) T_f8b1 rho' tp').
    { intros w Hw. exact (SPA_axforms segs _ (xf_shback T_f8b0) rho' T_f8b0 T_f8b1 tp' w T_f8b1_eq Hw). }
    apply (TR_pre (fun w => exists rho2, SPA segs (JAv ndF) C_fin rho2 tp' w)).
    { intros [tr [ms md]] Hw. exists (rho_absorb rho' [shobj gF 4 260 [] DUnknown] (vms md tp' ms)). rewrite <- C_fin_eq.
      apply (JA_shadow_release segs HTOP AInv CST XGL ALA HCST HXGL LFSH NF Kc rho0 (P0_pg FB FF) FB FF BX PTrue HKc HBX HNP [] [(vF, 6, vFL)] [] ANone 0%nat 110 6 120
               gF 4 260 [] DUnknown T_f8b1 (objs_butlast T_f8b1) [] rho' tp' tr ms md eq_refl ltac:(lia) eq_refl T_f8b1_objs ltac:(lia)
               ltac:(change (fs_frame_size 6 / 8) with 512; lia) eq_refl ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)); [|exact Hw].
      intros Ai rho2 tp2 md2 HF2 HP0 Hav HM HT HTK HBf HFF HN HDt HZt HFR.
      apply (robjs_okF_site Ai rho' _ [] _ (objs_butlast T_f8b1) rho2 tp2 md2 HM HF2 ltac:(vm_compute; reflexivity) Hav HP0 HT HTK HN I ltac:(constructor) HFR). vm_compute. reflexivity. }
    apply TR_exw. intros rho2. apply (REENTER C_fin ndF (40, z0)); [innth 29 | meas].
Qed.

Lemma n_is : ltac2:(tb__ "0|1|
S3S0S7S21S3cZ0R2A2S3eR2S40Z2Z40A2A2A2SdR4R2A2S20S0S44Q40M0S10R5S7dA2A2S44G0S10R5S5R4A1A2A2A3F_;SdR5R3A2S20S0S45R6S7dA2R5A3F_;F_;F_;Ff;Fk;Frho;").
Proof. intros rho k f Hk Hf H. pose proof (Hf H) as E. cbn [eval] in E. rewrite (u64_lit k Hk) in E. exact E. Qed.

Lemma reshape_rng : ltac2:(tb__ "0|5|
S3S0S21S3cZ3R1A2S3cR1Z4A2A2S20S0S45R3S7dA2R2A3S21S20S0S3dS44Q40M0S10R4S11Sa7R3A1M1A1A2A2M2S13R4G1A2A2S3dS44G0S10R4S11S81S2fSbA1A1M3A1A2A2M4S13R4G3A2A2A3S20S0S3dG2S12R4G1A2A2S3dG4S12R4G3A2A2A3A2F_;F_;Fk;Frho;").
Proof.
  intros rho k Hk Hn. unfold O_pp2d_lit, O_pp2d, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. split; [reflexivity|].
  assert (A : uval rho (SAlu ALU_SLL (SLit k) (SLit 4)) = 16 * k).
  { unfold uval. rewrite U_sll_lit, U_lit. change (2 ^ (4 mod 64)) with 16. unfold M64v. rewrite (Z.mod_small k) by lia. rewrite Z.mod_small by lia. lia. }
  assert (B : uval rho (SAlu ALU_SLL pN (SLit 4)) = 16 * uval rho pN).
  { unfold uval. rewrite U_sll_lit. change (2 ^ (4 mod 64)) with 16. unfold M64v. change (bv_unsigned (eval rho pN)) with (uval rho pN). rewrite Hn, Z.mod_small by lia. lia. }
  rewrite !soff_smallu by (rewrite ?A, ?B; lia). rewrite A, B, Hn. lia.
Qed.
Lemma reshape_rng_lit : ltac2:(tb__ "0|6|
S3S0S21S3cZ3R1A2S3cR1Z4A2A2S20S0S45R3S7dA2R2A3S21S20S0S3dS44Q40M0S10R4S11S81S2fSbA1M1A1M2A1A2A2M3S13R4G2A2A2S3dS44G0S10R4S11S15S80S5Z0A1S5S3fZ10R3A2A1G1SfA5M4A1A2A2M5S13R4G4A2A2A3S20S0S3dG3S12R4G2A2A2S3dG5S12R4G4A2A2A3A2F_;F_;Fk;Frho;").
Proof.
  intros rho k Hk Hn. unfold O_pp2d, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. split; [reflexivity|].
  assert (B : uval rho (SAlu ALU_SLL pN (SLit 4)) = 16 * uval rho pN).
  { unfold uval. rewrite U_sll_lit. change (2 ^ (4 mod 64)) with 16. unfold M64v. change (bv_unsigned (eval rho pN)) with (uval rho pN). rewrite Hn, Z.mod_small by lia. lia. }
  rewrite soff_smallu by (rewrite B; lia). rewrite soff_lit_small by lia. rewrite B, Hn. lia.
Qed.

Lemma X_E_sc3 : ltac2:(tb__ "0|1|
S3S2cS43Q40A1A1M0S0G0S3cS3fZ42S40Z2Z40A2A2R2A2VTR;S47S3bVJAv;S95A1Sa4R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply TR_facts. intros HF0.
  assert (N3 : forall r, Forall (holds r) (ss_facts (ax_S E_sc3_0)) -> uval r pN = 3).
  { intros r HFr. fact HFr F3 H3. apply (n_is r 3 F3); [lia | intros H; exact (proj1 (holds_nbne _ _ _) H) | exact H3]. }
  eapply TR_pre with (P := SPA segs (JAv ndF) E_sc3 rho tp).
  { intros w Hw. apply (SPA_axforms segs _ [AXSplit 1 (SLit (-16))] rho E_sc3_1 E_sc3 tp w E_sc3_eq). rewrite <- E_sc3_1_eq. unfold reshapeA.
    apply (SPA_reshape segs _ rho E_sc3_0 7 _ _ tp w E_sc3_0_p2d); [reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | | exact Hw].
    intros HF. apply reshape_rng; [lia | exact (N3 rho HF)]. }
  apply (CALL_sc E_sc3 s_sc3 R_sc3 rho tp ndF (FAM b tp0)); [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity |].
  intros L rho' [<-|[]] Hag. cbn [la_state]. change (ax_add_facts (ss_facts (ax_S E_sc3)) (import_postA s_sc3 Pre_sc P_sc E_sc3 R_sc3)) with (T_pure Pre_sc E_sc3 s_sc3 R_sc3 P_sc).
  rewrite T_sc3_0_eq.
  eapply TR_pre with (P := SPA segs (JAv ndF) T_sc3 rho' tp).
  { intros w Hw. apply (SPA_axforms segs _ xf_wback rho' T_sc3_1 T_sc3 tp w T_sc3_eq). rewrite <- T_sc3_1_eq. unfold reshapeA.
    apply (SPA_reshape segs _ rho' T_sc3_0 1 _ _ tp w T_sc3_0_p2d); [reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | | exact Hw].
    intros HF. apply (reshape_rng_lit rho' 3); [lia|].
    fact HF F3 H3. apply (n_is rho' 3 F3); [lia | intros H; exact (proj1 (holds_nbne _ _ _) H) | exact H3]. }
  apply (REENTER T_sc3 ndF (60, z0)); [innth 19 | meas].
Qed.

Lemma X_E_sc4 : ltac2:(tb__ "0|1|
S3S2cS43Q40A1A1M0S0G0S3cS3fZ42S40Z2Z40A2A2R2A2VTR;S47S3bVJAv;S95A1Sa5R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply TR_facts. intros HF0.
  eapply TR_pre with (P := SPA segs (JAv ndF) E_sc4 rho tp).
  { intros w Hw. apply (SPA_axforms segs _ [AXSplit 1 (SLit (-16))] rho E_sc4_1 E_sc4 tp w E_sc4_eq). rewrite <- E_sc4_1_eq. unfold reshapeA.
    apply (SPA_reshape segs _ rho E_sc4_0 7 _ _ tp w E_sc4_0_p2d); [reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | | exact Hw].
    intros HF. apply reshape_rng; [lia|]. fact HF F4 H4. apply (n_is rho 4 F4); [lia | intros H; exact (proj1 (holds_beq _ _ _) H) | exact H4]. }
  apply (CALL_sc E_sc4 s_sc4 R_sc4 rho tp ndF (FAM b tp0)); [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity |].
  intros L rho' [<-|[]] Hag. cbn [la_state]. change (ax_add_facts (ss_facts (ax_S E_sc4)) (import_postA s_sc4 Pre_sc P_sc E_sc4 R_sc4)) with (T_pure Pre_sc E_sc4 s_sc4 R_sc4 P_sc).
  rewrite T_sc4_0_eq.
  eapply TR_pre with (P := SPA segs (JAv ndF) T_sc4 rho' tp).
  { intros w Hw. apply (SPA_axforms segs _ xf_wback rho' T_sc4_1 T_sc4 tp w T_sc4_eq). rewrite <- T_sc4_1_eq. unfold reshapeA.
    apply (SPA_reshape segs _ rho' T_sc4_0 1 _ _ tp w T_sc4_0_p2d); [reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | | exact Hw].
    intros HF. apply (reshape_rng_lit rho' 4); [lia|].
    fact HF F4 H4. apply (n_is rho' 4 F4); [lia | intros H; exact (proj1 (holds_beq _ _ _) H) | exact H4]. }
  apply (REENTER T_sc4 ndF (60, z0)); [innth 20 | meas].
Qed.

Lemma X_E_r2 : ltac2:(tb__ "0|1|
S3S2cS43Q40A1A1M0S0G0S3cS3fZ42S40Z2Z40A2A2R2A2VTR;S47S3bVJAv;S95A1Sb7R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  eapply TR_pre with (P := SPA segs (JAv ndF) E_r2 rho tp).
  { intros w Hw. pose proof (SPA_axforms segs _ xf_r2call rho E_r2_0 E_r2_1 tp w E_r2_eq Hw) as Hw1.

    unfold E_r2. apply (SPA_refacts_JA segs); [exact Hw1 | vm_compute; reflexivity |].
    intros tr md HJ HF2.
    assert (BZ : basez rho) by (eapply basez_of; [exact HF2 | vm_compute; reflexivity]).
    pose proof (extz_of rho BZ) as [E12 Eo12 E16 E4 Er EN EP ERF EA EF]. destruct BZ as [Bsp BD Bwin Bn Bres Bscr Bneed Ba16 Btop].
    assert (HD8 : 0 <= (uval rho pN + 7) / 8) by (apply Z.div_pos; lia).
    unfold r2_ptr_facts. constructor; [|constructor; [|constructor; [|exact HF2]]];
      apply (proj2 (holds_ule _ _ _)); repeat change (bv_unsigned (eval ?r ?e)) with (uval r e); rewrite uval_lit by lia; lia. }
  apply (CALL_r2 E_r2 s_r2 R_r2 rho tp ndF (FAM b tp0)); [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity |].
  intros L rho' [<-|[]] Hag. cbn [la_state]. change (ax_add_facts (ss_facts (ax_S E_r2)) (import_postA s_r2 Pre_r2 P_ret E_r2 R_r2)) with (T_pure Pre_r2 E_r2 s_r2 R_r2 P_ret).
  rewrite T_r2_0_eq.
  eapply TR_pre with (P := SPA segs (JAv ndF) T_r2 rho' tp).
  { intros w Hw. exact (SPA_axforms segs _ xf_r2back rho' T_r2_0 T_r2 tp w T_r2_eq Hw). }
  apply (REENTER T_r2 ndF (60, z0)); [innth 21 | meas].
Qed.

Lemma site_sf : ltac2:(tb__ "0|b|
S26S104S2cS4A1S3S20S30Sf6S6S27R4A1A1A1S32A3S20S30SfbS6S27R5A1A1S31S2dS2dS2S0A2M0S2A2M1S2eG0S2S2eS2S0S82Z6A4S83A4M2S2fG1A1A3M3S34S36U0M4A2M5R3A4S32A3S20S30S109VXGL;S6S27R6A1M6A1S2fS2dS2S2A2A1M7G3G5S8G6A1Sf7S7eA8S32A3S20S2S105R6PcM8A2S82A3S20S2S105R7S6fA2S83A3S90S102S7SdR7A1S6S27RaA1A1A3S53VFB;VFF;Vrho0;A3S100S4bVrho0;R9A3S5bVFB;R4A2S5cVFF;R5A2S5aVFB;R6RcG7A4S115RdG7A2S116ReG7A2S57VFF;R9RfG3A4S23S3S3S23S2cS43Q40A1A1M9G9S23S93S93VAInv;RdR3R2R1A4Lmd1;A2Ltp1;A2Lrho1;A2S58Vrho0;RbA2S114R12S92S91RcA1A1A2S21S126VCST;Vrho0;VFB;VFF;R13G7S118G1G4G3A3MaR14A8S21S125VCST;VXGL;Vrho0;VFB;VFF;R13G7GaS7eA9S21S20S0S45R13S105R15G8A2A2S45R13S35S2S0S35G0S2G2A3A3A2A3S20S0S45R13S105R15S6fA2A2S45R13S37G0S2G2A3A2A3A2A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FAi;F_;F_;F_;F_;F_;Frho;FR;Fs;FE;").
Proof.
  intros E s R rho HB HR HX Hs12 Hs16 Ai HF HP0 Hav HBf HFF HN HD HZ HFR (rho1 & tp1 & md1 & HM) HT HTK.
  split; [|split; [|rewrite Hs12, Hs16; cbn [fst snd]; split; reflexivity]].
  - intros o a Ho Hr. eapply (robjs_checkP_sound Ai rho _ [] [(vF, 6, vFL)] (Some 0%nat) R rho1 tp1 md1 HM HF HB Hav HP0 (T_ok_T0 rho0 _ Ai HT HTK) HFR HR); [exact Ho | exact Hr].
  - exact (xrs_ok_site Ai rho _ [] [(vF, 6, vFL)] (Some 0%nat) (ss_objs (ax_S E)) X_pg rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HN HD HZ HFR HX).
Qed.

Lemma flag_carve_site : ltac2:(tb__ "0|8|
S26S3S20S30Sf6S6S27R2A1A1A1S32A3S20S30S10eS6S27R3A1M0A1S2fS2dS2S2A2A1M1S31S2dS2dS2S0A2M2S2A2M3S2eG2S2S2eS2S0S82Z6A4S83A4S2fG3A1A3M4S39S36A1M5Sf8S8G0A1A6S32A3S20S30S109VXGL;S6S27R4A1M6A1G1G4G5S8G6A1Sf7S28R4A1A8S32A3S90S3S2cS43Q40A1A1S93S102S7SdR8A1S6S27R9A1A1A3S53VFB;VFF;Vrho0;A3S100S4bVrho0;RaA3VAInv;R7R6R5R4A4S58Vrho0;R8A2S114RdS92S91R9A1A1A2S5bVFB;RaA2S5cVFF;RbA2S5aVFB;RcR10G1A4S115R11G1A2S116R12G1A2S57VFF;RfR13G4A4S21S4S0S6aS4R2S8S27R17A1A1A3S21S3cS35S0S0S14R17R3A2M7A3R2A2S3eR2S37S0S0G7A3A2A2S22S122VCST;Vrho0;S117VFB;R18G1A3S123VFF;R18G4A3R3A5S22S21S3cZ0R3A2S3eR3S134A2A2S12aR3A1A2A2F_;F_;Fa;Fo;S13fR14S28R15A1A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FAi;F_;F_;F_;Frho;FE;").
Proof.
  intros E rho HB HR HX Ai rho1 tp1 md1 HF HP0 Hav HM HT HTK HBf HFF HN HDt HZt HFR. split.
  - intros o a Ho Hr. destruct (robjs_okF_site Ai rho _ [] _ (ss_objs (ax_S E)) rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HN I ltac:(constructor) HFR HR o a Ho Hr) as [H|H];
      [left; exact H | right; left; exact H].
  - intros r a Hr Ha.
    assert (HBc : fbinA (FBx FB rho []) Ai) by (apply (fbinA_FBx FB Ai rho [] []); [exact HBf | exact HN]).
    assert (HFc : ffinA (FFx FF rho [(vF, 6, vFL)]) Ai) by (apply ffinA_FFx; [exact HFF | exact HFR]).
    destruct (xrs_ok_site Ai rho _ [] [(vF, 6, vFL)] None (ss_objs (ax_S E)) (ax_X E) rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HN I ltac:(constructor) HFR HX r a Hr Ha) as [H|H].
    + exact (pclMA_lt47 Ai rho1 tp1 md1 _ _ a HM HBc HFc H).
    + pose proof (HXGL a H). unfold IMG_HI, LOW_SHADOW_BEG in *. lia.
Qed.

Lemma X_E_sf : ltac2:(tb__ "0|f|
S26S26S26S104S2cS4A1M0S26S3S2cS43Q40A1A1M1S0G1S20S26S10dRaP78A2R9A3S20S30S1fS27RaA1A1S32A3S20S2S2bRcA1S5S135A1A3S20S30Sf6S6S27RdA1A1A1S32A3S20S30S10eS6S27ReA1M2A1S2fS2dS2S2A2M3A1M4S31S2dS2dS2S0A2M5S2A2M6S2eG5S2S2eS2S0S82Z6A4S83A4S2fG6A1A3M7S39S36A1M8Sf8S8G2A1A6S32A3S20S30S109VXGL;S6S27RfA1M9A1G4G7G8S8G9A1Sf7S28RfA1MaA8S32A3S20S2cG3A1GaS7eA3S20S33G0A1S4eR10S9dReA3S34G0RdA2A3S20S30S50R11S9dRfReS31S26Sa6S2fS26A1A3A5S32A3S20S30S129S4bR10A2S32A3S20S30S137S4bSaS27R13A1A1A2S32A3S20S30S59SaS27R14A1A1S95A2S32A3S20S30Sf6S6S27R15A1A1A1S32A3S20S30SfbS6S27R16A1A1G7S34S36U0A2MbR13A4S32A3S20S30S109VXGL;S6S27R17A1McA1G4G7GbS8GcA1Sf7S7eA8S32A3S20S2S105R16PcA2S82A3S20S2S105R17S6fA2S83A3S20S26S124S9dR1aR18R17Sa6S7eA6R19A3S6aS2dS2dS26S55A2MdS2dS0S2A2MeA2S2eGdGeS2eS26S55R1aS9cA4S2eS0S2ZaSf1A4A4Sc5A3S3cS3fZfS40Z2Z40A2A2R15A2VTR;S47S3bVJAv;S95A1R1eR18R17A5VFAM;R16R15A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Ftp0;Fb;Ftp;Frho;FP;FR;Fs;FT;FE;FE0;").
Proof.
  intros E0 E T s R P rho tp b tp0 HE Hwf Hbase HB0 HR0 HX0 HXE He Hchk Htp Hnf Hnb HB HR HX Hs12 Hs16 HT HinT Hb.
  eapply TR_pre with (P := SPA segs (JAv ndF) E rho tp).
  { intros w Hw. rewrite <- HE.
    apply (JA_flag_carve segs HTOP AInv CST XGL ALA HCST HXGL LFLAG NF Kc rho0 (P0_pg FB FF) FB FF BX PTrue HKc HBX HNP [] [(vF, 6, vFL)] [] ANone 0%nat 110 6 120 E0 rho tp w
             eq_refl ltac:(lia) Hbase ltac:(rewrite HE; exact Hwf)); [|exact Hw].
    exact (flag_carve_site E0 rho HB0 HR0 HX0). }
  apply TR_facts. intros HF.
  apply (sfree_callT segs AE_A AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_pg FB FF) FB FF BX PTrue HKc TR TR_facts TR_ex TR_pre TR_callP
           6 E s R X_pg rho tp ndF 0%nat (vF, 6, vFL) (FAM b tp0) CSF ltac:(lia)).
  - rewrite HXE. intros r H. exact H.
  - exact He.
  - exact Hchk.
  - exact Htp.
  - exact Hnf.
  - exact Hnb.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - intros A A' _; exact I.
  - exact (site_sf E s R rho HB HR HX Hs12 Hs16).
  - intros rho' tp'. cbn [nd_tv nd_fr nd_bd nd_am remove_nth]. unfold Pre_sf, L_sf in HT. rewrite HT. apply (REENTER T nd0 (10, z0)); [exact HinT | meas].
Qed.

Lemma X_E_sfI : ltac2:(tb__ "0|1|
S3S2cS43Q40A1A1M0S0G0S3cS3fZfS40Z2Z40A2A2R2A2VTR;S47S3bVJAv;S95A1SbeR5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  apply (X_E_sf E_sfI0 E_sfI T_sfI s_sfI R_sfI P_inv rho tp b tp0 E_sfI_eq); try (vm_compute; reflexivity); try reflexivity; try exact Hb; try exact T_sfI_eq.
  innth 31.
Qed.
Lemma X_E_sfK : ltac2:(tb__ "0|1|
S3S2cS43Q40A1A1M0S0G0S3cS3fZfS40Z2Z40A2A2R2A2VTR;S47S3bVJAv;S95A1Sc0R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  apply (X_E_sf E_sfK0 E_sfK T_sfK s_sfK R_sfK P_ok rho tp b tp0 E_sfK_eq); try (vm_compute; reflexivity); try reflexivity; try exact Hb; try exact T_sfK_eq.
  innth 32.
Qed.

Lemma exits_okT : ltac2:(tb__ "0|3|
S26S55S2dS0S2A2M0S3S2cS43Q40A1A1M1G1S6aS2dS2dS26S55A2M2G0A2S2eG2G0S2eS26S55R6R5A4R4A4Se2A3VTR;S47S3bVJAv;R6A1R7R4R3A5VFAM;S5eS2eG2G0S2eS26S55R7R6A4R5A4R4A2R2A2A2F_;Ftp0;Ftp;Frho;FrvX;FndX;FX;").
Proof.
  intros X ndX rvX rho tp tp0 Hin. cbn [In exitsE] in Hin.
  destruct Hin as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[]]]]]]]]]]]]]; injection H as <- <- <-.
  - apply X_E_sm. meas.
  - apply X_E_f8a. meas.
  - apply X_E_ms. meas.
  - apply X_E_s00. meas.
  - apply X_E_sc3. meas.
  - apply X_E_sc4. meas.
  - apply X_E_r2. meas.
  - apply X_E_f8b. meas.
  - apply X_E_sfI. meas.
  - apply X_E_sfK. meas.
  - apply POST. left. reflexivity.
  - apply POST. right. left. reflexivity.
Qed.
End X.

Section Safety.
Variable ok : world -> Prop.
Hypothesis Hok : ltac2:(tb__ "0|0|
S65S3bVKc;Vok;A3").
Hypothesis AC : ltac2:(tb__ "0|0|
S7aS3bS6eVAInv;VCST;VXGL;A5").
Hypothesis SSC : ltac2:(tb__ "0|0|
S0S6aS0R1S31S0Z0S31S0Zf8S2fS0A1A3A3A3S132S3bS6eVAInv;VCST;VXGL;R2A6F_;Fxx;").

Theorem tess_polygon_sum : ltac2:(tb__ "0|0|
S2cS43Q40A1A1Sf5S3bVok;S47S3bS5dVAInv;VCST;VXGL;VKc;S53VFB;VFF;A2VFB;VFF;VBX;S56S9cAaS86Vrho0;R1A5S4dS3bS4bVrho0;R1Sf9A5A4Ftp0;").
Proof.
  intros tp0.
  eapply triple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_sound_JA segs AInv CST XGL NF Kc rho0 (P0_pg FB FF) FB FF BX PTrue HKc ALA FUEL_pg cutpcs_pg 100
                (map edropA cutsE) (map edropA exitsE) ok (Q tp0) Hok (ejcertA_jcertA segs NF _ _ _ _ _ ejcert_pg))
         with (ndT := nd0); [|left; reflexivity].
       intros X ndX rho tp Hin. apply in_map_iff in Hin as ([[X' nd'] rv] & E0 & Hin). cbn in E0. injection E0 as <- <-.
       apply (exits_okT (triple segs ok) (fun _ _ w => SPfamGTA segs (map nI (map edropA cutsE)) w \/ Q tp0 w)
                (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok) (@triple_ex segs ok) (call_soundPA3 segs ok)) with (rvX := rv) (tp0 := tp0).
       - intros Ai rho1 tp1. apply (aca_stack_malloc _ _ _ _ _ AC 6 ltac:(cbn; tauto)); [exact HKc|]. eapply ok_frameA_of_K; [exact Hok|]. intros r p t m (_ & K & _). exact K.
       - intros Ai rho1 tp1. apply (aca_stack_free _ _ _ _ _ AC 6 ltac:(cbn; tauto)); [exact HKc|]. eapply ok_frameA_of_K; [exact Hok|]. intros r p t m (_ & K & _). exact K.
       - intros Ai rho1 tp1. apply (SSC 248 ltac:(cbn; tauto)); [exact HKc|]. eapply ok_frameA_of_K; [exact Hok|]. intros r p t m (_ & K & _). exact K.
       - intros Ai rho1 tp1. apply (SSC 0 ltac:(cbn; tauto)); [exact HKc|]. eapply ok_frameA_of_K; [exact Hok|]. intros r p t m (_ & K & _). exact K.
       - intros Cl s R rho1 tp1 nd Q' He Hc Hn Hb Hf Hk.
         apply (pure_callA segs AInv CST XGL NF Kc rho0 (P0_pg FB FF) FB FF BX PTrue HKc ALA ok Cl Pre_sc s R Posts_sc rho1 tp1 nd Q'); try assumption.
         intros rho2 tp2. apply scale2d_sum; [apply frozen_ok_frameA; exact Hok | apply (frozen_stableA' NF (ss_next (ax_S Cl)) nd rho1); [apply Pos.leb_le; exact Hn | exact Hb]].
       - intros Cl s R rho1 tp1 nd Q' He Hc Hn Hb Hf Hk.
         apply (pure_callA segs AInv CST XGL NF Kc rho0 (P0_pg FB FF) FB FF BX PTrue HKc ALA ok Cl Pre_r2 s R Posts_r2 rho1 tp1 nd Q'); try assumption.
         intros rho2 tp2. apply run2d_sum; [apply frozen_ok_frameA; exact Hok | apply (frozen_stableA' NF (ss_next (ax_S Cl)) nd rho1); [apply Pos.leb_le; exact Hn | exact Hb]].
       - intros T nd rv' rho1 tp1 b tp2 HinT _. apply (reenter_cutJA segs AInv CST XGL NF Kc rho0 (P0_pg FB FF) FB FF BX PTrue ok (map edropA cutsE) T nd).
         apply in_map_iff. exists (T, nd, rv'). auto.
       - intros P nd rho1 tp1 b tp2 HinP. apply (exit_postGA segs AInv CST XGL NF Kc (P0_pg FB FF) FB FF BX PTrue ok rho0 tp0 nd Posts_pg P). exact HinP.
       - exact Hin. }
  intros w Hw. apply JA_pre_intro. exact Hw.
Qed.
End Safety.

Section Existence.
Hypothesis ACX : ltac2:(tb__ "0|0|
S7bS3bS6eVAInv;VCST;VXGL;A5").
Hypothesis SSCX : ltac2:(tb__ "0|0|
S0S6aS0R1S31S0Z0S31S0Zf8S2fS0A1A3A3A3S133S3bS6eVAInv;VCST;VXGL;R2A6F_;Fxx;").

Theorem tess_polygon_sum_ex : ltac2:(tb__ "0|0|
S2cS43Q40A1A1Sf4S3bS47S3bS5dVAInv;VCST;VXGL;VKc;S53VFB;VFF;A2VFB;VFF;VBX;S56S9cAaS86Vrho0;R1A5S4dS3bS4bVrho0;R1Sf9A5A3Ftp0;").
Proof.
  intros tp0.
  eapply etriple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_complete_JA segs AInv CST XGL NF Kc rho0 (P0_pg FB FF) FB FF BX PTrue HKc ALA FUEL_pg cutpcs_pg 100 cutsE exitsE (Q tp0) ejcert_pg)
         with (ndT := nd0) (rv := (100, z0)); [|left; reflexivity].
       intros X ndX rv rho tp Hin.
       apply (exits_okT (etriple segs) (fun b _ w => SPfamETA segs (map (enodeIA AInv CST XGL NF Kc rho0 (P0_pg FB FF) FB FF BX PTrue) cutsE) b w \/ Q tp0 w)
                (TRe_facts segs) (TRe_ex segs) (TRe_pre segs) (@etriple_ex segs) (call_completePA3 segs)) with (tp0 := tp0).
       - intros Ai rho1 tp1. apply (acx_stack_malloc _ _ _ _ _ ACX 6 ltac:(cbn; tauto)). exact HKc.
       - intros Ai rho1 tp1. apply (acx_stack_free _ _ _ _ _ ACX 6 ltac:(cbn; tauto)). exact HKc.
       - intros Ai rho1 tp1. apply (SSCX 248 ltac:(cbn; tauto)). exact HKc.
       - intros Ai rho1 tp1. apply (SSCX 0 ltac:(cbn; tauto)). exact HKc.
       - intros Cl s R rho1 tp1 nd Q' He Hc Hn Hb Hf Hk.
         apply (pure_callA_ex segs AInv CST XGL NF Kc rho0 (P0_pg FB FF) FB FF BX PTrue HKc ALA Cl Pre_sc s R Posts_sc rho1 tp1 nd Q'); try assumption.
         intros rho2 tp2. apply scale2d_sum_ex. apply (frozen_stableA' NF (ss_next (ax_S Cl)) nd rho1); [apply Pos.leb_le; exact Hn | exact Hb].
       - intros Cl s R rho1 tp1 nd Q' He Hc Hn Hb Hf Hk.
         apply (pure_callA_ex segs AInv CST XGL NF Kc rho0 (P0_pg FB FF) FB FF BX PTrue HKc ALA Cl Pre_r2 s R Posts_r2 rho1 tp1 nd Q'); try assumption.
         intros rho2 tp2. apply run2d_sum_ex. apply (frozen_stableA' NF (ss_next (ax_S Cl)) nd rho1); [apply Pos.leb_le; exact Hn | exact Hb].
       - intros T nd rv' rho1 tp1 b tp2 HinT Hm. apply (ereenter_cutJA segs AInv CST XGL NF Kc rho0 (P0_pg FB FF) FB FF BX PTrue cutsE T nd rv'); [exact HinT | exact Hm].
       - intros P nd rho1 tp1 b tp2 HinP. apply (eexit_postGA segs AInv CST XGL NF Kc (P0_pg FB FF) FB FF BX PTrue rho0 tp0 nd Posts_pg P). exact HinP.
       - exact Hin. }
  intros w Hw. apply JA_pre_intro. exact Hw.
Qed.
End Existence.

End Sum.
End Lib_tess_polygon_pf.

(* [comment removed for export] *)
Module Start7States.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nat"; "pair"; "true"; "nil"; "bool"; "Some"; "list"; "option"; "false"; "prod"; "length"; "app"; "negb"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "sobj"; "sprop"; "SAlu"; "ss_objs"; "cell"; "SVar"; "sstate"; "SPUle"; "mkObj"; "SExt"; "DUnknown"; "ss_facts"; "DImage"; "ob_base"; "ob_hi"; "ob_lo"; "ss_next"; "swf"; "ob_dflt"; "odefault"; "ss_pc"; "ss_regs"; "SPAlign"; "ob_cells"; "DZero"; "mkCell"; "sprop_below"; "ss_fregs"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "leafA"; "ax_S"; "sym_runA"; "entailsA"; "mkAX"; "mkLeafA"; "ax_setS"; "axwf"; "cell_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o5.Start7States"; "C18e"; "JPC18"; "J18S"; "K18S"; "XB18"; "o18ssp"; "o18win"; "sJ18"; "C18"; "E18g"; "R18"; "SP18"; "T18c1"; "U18b"; "U18c"; "s18"; "AUXV18"; "C18a"; "C18b"; "C18c"; "C18d"; "C18d'"; "J18"; "L18a"; "T18b"; "T18c"; "myregs18"; "ogrp18c"; "I18af"; "I18bf"; "I18cf"; "L18b"; "L18c"; "X18"; "XE18"; "XL18"; "bytes18"; "o18errno"; "o18ssp_m"; "refact18"; "EV18"; "I18a"; "I18b"; "I18c"; "K18a"; "o18ssp_s"; "oarea18b"; "oarea18c"; "owin18"; "E18b"; "F18"; "odummy18"; "splits18"; "@Corelib.Lists.ListDef"; "nth"; "map"; "seq"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SRL"; "ALU_SLL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "same_but_objs"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA"; "replace_obj_at"; "move_obj_last"; "obj_to_unknown"; "split_chain"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.MuslMallocIface"; "Pre_M"; "@Stdlib.Lists.List"; "nth_error"; "existsb"; "forallb"; "filter"; "@Stdlib.ZArith.BinInt.Z"; "pow"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.StartALib"; "SHB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3"; "import_postA3"; "@Corelib.Init.Nat"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.MuslMalloc40Post"; "P_null0"; "P_null1"; "P_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "merge_objs_at"; "@Stdlib.PArith.BinPos.Pos"; "of_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o3.Start6bStates"; "E18"; "MALLOC_ENTRY"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkPA"; "entails_frA"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "@Stdlib.Bool.Bool"; "Is_true"; "@stdpp.base"; "filter"; "@stdpp.decidable"; "Is_true_dec"; "@stdpp.list_basics.list"; "list_filter"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymCall SymSummary Glue3 SymHeap SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Init Code KxA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Init OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.KxA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.MuslMallocIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.MuslMalloc40Post.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.StartALib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import StartDefsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.StartGlueB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Start4States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Start6States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nz.Start6JStates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o3.Start6bStates.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition AUXV18 : sv := ltac2:(tb__ "0|1|
S14S72S14S72S14S72S17P1A1S14S74S17P2A1S11Z3A1M0A3A3S14S74S17P3A1G0A3A3S11Z18A1A3").
Definition SP18 : sv := SAlu ALU_ADD (SVar 1%positive) (SLit (-240)).
Definition XB18 : sv := SVar 84%positive.
Definition XL18 : sv := SVar 85%positive.
Definition XE18 : sv := SAlu ALU_ADD XB18 XL18.
Definition F18 : list sprop := ltac2:(tb__ "0|4|
S0S13S28P54Z6M0A2S0S13S28P55G0A2S0S13S19S14S72S3eS11Z200A1A3S45A2S0S13S19S45S5cA2S0S13S19S3eS17P6A1M1A2S0S13S19S14S72G1S11Z10A1A3S5cA2S0S13S19S5dS11S81Z2M2Z28A2A1A2S0S13S19S11Z7fff7f000000A1S3eA2S0S13S19S3eS11S81G2Z30A2A1A2S0S13S19S5cS11S81G2Z2fA2M3A1A2S0S13S19S14S72S45S11Z140A1A3G1A2S0S13S19S14S72S45S11Z40A1A3S4aA2S0S13S19S11Z7fff80000000A1S4aA2S0S13S19S4aS11S82G3S81G2Z16A2A2A1A2S4S13A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition X18 : list (sv * sv) := ltac2:(tb__ "0|1|
S0SaS10S10A2M0S2S10S10S3eS5dA4S4G0A1A3").

Definition E18b : sstate := Eval vm_compute in
  (let St := ax_S E18 in mkSS (ss_pc St) (ss_regs St) (ss_fregs St) (ss_fcsr St) (ss_resv St) (ss_objs St) (ss_facts St) 86%positive (ss_lenient St)).
Definition E18g : sstate := Eval vm_compute in
  (let St := ax_S E18 in mkSS (ss_pc St) (ss_regs St) (ss_fregs St) (ss_fcsr St) (ss_resv St) (ss_objs St) (F18 ++ ss_facts St) 86%positive (ss_lenient St)).
Lemma sd18 : ltac2:(tb__ "0|4|
SfSeS8SaS7SaS10S10A2M0A1M1S7S13A1M2A2M3A1S76S6bS43A2S6G3S2G1G2S4G0A1S6cA4A2A3SfSeS5S23S43A1S3A3SeS2eS22S43A1P56A3A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition splits18 : list (nat * sv) := ltac2:(tb__ "0|4|
S0SaS1S10A2M0S2S1S10U16M1S11Nbf0A1A4S0G0S2S1S10U17M2S11Nf0A1A4S0G0S2S1S10UeS11Z6211d4A1A4S0G0S2S1S10UfS11Z6211d8A1A4S0G0S2S1S10U10S11Z6412b8A1A4S0G0S2S1S10U11S11Z6412c0A1A4S0G0S2S1S10U12S11Z64150bA1A4S0G0S2S1S10U13S11Z64150cA1A4S0G0S2S1S10U14S11Z641510A1A4S0G0S2S1S10U15S11Z641518A1A4S0G0S2S1S10G1S11Z641538A1A4S0G0S2S1S10G2S11Z641540A1A4S0G0S2S1S10U18S11Z641580A1A4S0G0S2S1S10U19S11Z641928A1A4S0G0S2S1S10U1aS11Z6421d0A1A4S0G0S2S1S10U1bS11Z6421d8A1A4S0G0S2S1S10U1cS11Z642a98A1A4S0G0S2S1S10U1dS11Z642aa8A1A4S0G0S2S1S10UaM3S11Zeed98A1A4S0G0S2S1S10UbS11Zeed9aA1A4S0G0S2S1S10U9S11Ze6758A1A4S0G0S2S1S10G3S11Ze6788A1A4S4G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition C18a : sstate := Eval vm_compute in (match split_chain E18g splits18 with Some St => St | None => E18g end).
Lemma split18_ok : ltac2:(tb__ "0|0|
SeS8S18A1S7bS43S6eA2S6S18S4bA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition odummy18 : sobj := ltac2:(tb__ "0|1|
S1aS11Z0A1M0G0G0S4S16A1S2aA5").
Definition ob18 (St : sstate) (i : nat) : sobj := ltac2:(tb__ "0|0|
S6fS12Vi;S15VSt;A1S6dA4").

Definition o18errno : sobj := Eval vm_compute in ob18 C18a 19.
Definition C18b : sstate := Eval vm_compute in replace_obj_at C18a 19 (obj_to_unknown o18errno).
Lemma C18b_facts : ltac2:(tb__ "0|2|
SfSeS8S12A1S7dS12S15S4bA1U13M0A3S6S12S5fA2A3SfSeS25S24S5fA1S1eA3SfSeS5S75S4bS78S4bG0S7aS5fA1A3M1A2S3A3SeS18G1S4cA3A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition o18ssp : sobj := Eval vm_compute in ob18 C18b 21.
Definition es18 : list sv := ltac2:(tb__ "0|2|
S0S10S1bS9Q8M0S17P9A1M1A3S0S10S11Z0A1S0S10S1bS9G0S14S73G1S11Z10A1A3A3S0S10S1bS9G0S14S73G1S11Z18A1A3A3S0S10S1bS9G0S14S73G1S11Z20A1A3A3S0S10S1bS9G0S14S73G1S11Z28A1A3A3S0S10S1bS9G0S14S73G1S11Z30A1A3A3S0S10S14S73G1S11Z38A1A3S4S10A1A3A3A3A3A3A3A3A3").
Definition bytes18 : list cell := byte_cells 0x6412b8 es18.
Definition EV18 : sv := SAlu ALU_AND (SVar 9%positive) (SLit 18446744073709486335).
Definition o18ssp_s : sobj := ltac2:(tb__ "0|0|
S1aS11Z0A1S11Z6412b8A1S11Z6412c0A1S5eS1eA5").
Definition C18c : sstate := Eval vm_compute in replace_obj_at C18b 21 o18ssp_s.
Definition o18ssp_m : sobj := ltac2:(tb__ "0|1|
S1aS11Z0A1S11Z6412b8A1M0S11Z6412c0A1S0S16S2bG0Z8S62A3S4S16A1A3S1eA5").
Definition C18d : sstate := Eval vm_compute in replace_obj_at C18c 21 o18ssp_m.
Definition C18d' : sstate := Eval vm_compute in replace_obj_at C18d 21 (obj_to_unknown o18ssp_m).
Lemma C18c_facts : ltac2:(tb__ "0|4|
SfSeS8S12A1S7dS12S15S4cA1U15M0A3S6S12S3fA2A3SfSeS10S1fS3fA1S11Z0A1A3SfSeS10S21S3fA1S11Z6412b8A1A3SfSeS10S20S3fA1S11Z6412c0A1A3SfSeS25S24S3fA1S1eA3SfSeS5S7fS16S16S7eS16S39R1A1M1S5eA3Lc;S29S3fA1M2A3S3A3SfSeS5S7fS16S16S7eS16G1G2A3Lc;S5eA3S3A3SfSeS5S75S4cS78S4cG0S67A3M3A2S3A3SeS18G3S4dA3A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma C18d_facts : ltac2:(tb__ "0|4|
SfSeS8S12A1M0S7dS12S15S4dA1U15M1A3S6S12S67A2A3SfSeS5S75S4dS78S4dG1S60A3M2A2S3A3SfSeS18G2S4eA3SfSeG0S7dS12S15S4eA1G1A3S6S12S60A2A3SfSeS5S75S4eS78S4eG1S7aS60A1A3M3A2S3A3SeS18G3S4fA3A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition o18win : sobj := Eval vm_compute in ob18 C18d' 43.
Definition owin18 : sobj := ltac2:(tb__ "0|0|
S1aS17P1A1S11Nbf0A1S11Nf0A1S4S16A1S1cA5").
Definition C18e : sstate := Eval vm_compute in replace_obj_at C18d' 43 owin18.
Lemma C18e_facts : ltac2:(tb__ "0|3|
SfSeS8S12A1S7dS12S15S4fA1U2bM0A3S6S12S40A2A3SfSeS25S24S40A1M1S1cA3SfSeS12S1aS1fS40A1S21S40A1S20S40A1S80S16S16S9L_;S29S40A1A3G1A5S6aA3SfSeS5S75S4fS78S4fG0S6aA3M2A2S3A3SeS18G2S3aA3A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition C18 : axst := ltac2:(tb__ "0|0|
S35S3aS5bS11S83A1A3").
Lemma C18_at : ltac2:(tb__ "0|0|
SfSeS2fS26S3aA1S8fA3SfSeS2eS22S3aA1P56A3SfSeS1SbS12S15S3aA1A2U30A3SfSeS5S23S3aA1S3A3SfSeS7S13A1S1dS3aA1S1dS43A1A3SeS7S10A1S27S3aA1S27S32S8eA1A1A3A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma C18e_facts_below : ltac2:(tb__ "0|0|
SeS5S7fS13S2cP56A1S1dS3aA1A3S3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition myregs18 : list sv := ss_regs C18e.
Definition s18 : wsub := ltac2:(tb__ "0|8|
ScSaS2eS10A2M0S0G0S2S2eS10PaM1S45A4S0G0S2S2eS10PbS6fS10U1M2S54S11Z0A1M3A4A4S0G0S2S2eS10PdS6fS10UbM4S54G3A4A4S0G0S2S2eS10PeS6fS10UcM5S54G3A4A4S0G0S2S2eS10PfS62A4S0G0S2S2eS10P10S4aA4S0G0S2S2eS10P11S17P6A1A4S0G0S2S2eS10P12S17P7A1A4S0G0S2S2eS10P13S17P8A1A4S0G0S2S2eS10P34S3eA4S0G0S2S2eS10P35S5dA4S0G0S2S2eS10P36S17P9A1A4S0G0S2S2eS10P37S17G1A1A4S4G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3ScG0S70S1G0S1S2S2eS10S8dS88U14R1A2A1S6fS10R1S54G3A4A4Lr;S95S1S7S1A1S97S1A1S1S94SdS7eS1S93R1A1S0S1G2S0S1U2S0S1UaS0S1G4S0S1G5S4S1A1A3A3A3A3A3A3A1M6A1Lr;S1S96G6A1Lx;S71U0U20A2M7A6A4S70S1G0S1S2S2eS10S8dS88U3cR1A2A1S6fS10R1S2dS3aA1G3A4A4Lr;G7A4A3A3").
Definition R18 : list sobj := Eval vm_compute in (match entails_frA C18 Pre_M s18 with Some R => R | None => [] end).
Lemma ent18 : ltac2:(tb__ "0|1|
SeS8S7S12A1M0A1S92S42S7cS49A3S6G0S44A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma chk18 : ltac2:(tb__ "0|0|
SeS5S91S42S7cS49S44S0S30S89S0S30S8aS0S30S8bS4S30A1A3A3A3A5S3A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma R18_len : length R18 = 34%nat. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition I18a : axst := Eval vm_compute in (import_postA3 s18 Pre_M P_null0 C18 R18 []).
Definition I18b : axst := Eval vm_compute in (import_postA3 s18 Pre_M P_null1 C18 R18 []).
Definition I18c : axst := Eval vm_compute in (import_postA3 s18 Pre_M P_ok C18 R18 []).
Lemma I18_eq : ltac2:(tb__ "0|1|
SfSeS30S87S49S7cS89S42S44S4SaS10S10A2A1M0A6S63A3SfSeS30S87S49S7cS8aS42S44G0A6S64A3SeS30S87S49S7cS8bS42S44G0A6S65A3A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition refact18 (A : axst) : axst := ltac2:(tb__ "0|0|
S90VA;ScS13S1dS32VA;A1A1S1dS3aA1A3A2").
Definition I18af : axst := Eval vm_compute in refact18 I18a.
Definition I18bf : axst := Eval vm_compute in refact18 I18b.
Definition I18cf : axst := Eval vm_compute in refact18 I18c.
Lemma I18f_eq : ltac2:(tb__ "0|0|
SfSeS30S61S63A1S56A3SfSeS30S61S64A1S57A3SeS30S61S65A1S58A3A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition JPC18 : Z := 0x65970.
Definition run18a__R : option (list leafA) := ltac2:(tb__ "0|0|
S33S77Ubb8S0S2fS3bS4S2fA1A3S56S3A5").
Local Strategy expand [run18a__R].
Definition L18a : axst := Eval vm_compute in ((fun ro1__ : option (list leafA) => (leaf1 I18af (ro1__))) run18a__R).
Definition run18b__R : option (list leafA) := ltac2:(tb__ "0|0|
S33S77Ubb8S0S2fS3bS4S2fA1A3S57S3A5").
Local Strategy expand [run18b__R].
Definition L18b : axst := Eval vm_compute in ((fun ro2__ : option (list leafA) => (leaf1 I18bf (ro2__))) run18b__R).
Definition run18c__R : option (list leafA) := ltac2:(tb__ "0|0|
S33S77Ubb8S0S2fS3bS4S2fA1A3S58S3A5").
Local Strategy expand [run18c__R].
Definition L18c : axst := Eval vm_compute in ((fun ro3__ : option (list leafA) => (leaf1 I18cf (ro3__))) run18c__R).
Lemma run18a : ltac2:(tb__ "0|1|
SeS8S7S31A1M0A1S33S77Ubb8S0S2fS3bS4S2fA1A3S56S3A5S6G0S0S31S36S51S85A2S4S31A1A3A2A3"). Proof. exact (@eq_refl (option (list leafA)) run18a__R <: run18a__R = Some [mkLeafA L18a RsCut]). Qed.
Lemma run18b : ltac2:(tb__ "0|1|
SeS8S7S31A1M0A1S33S77Ubb8S0S2fS3bS4S2fA1A3S57S3A5S6G0S0S31S36S59S85A2S4S31A1A3A2A3"). Proof. exact (@eq_refl (option (list leafA)) run18b__R <: run18b__R = Some [mkLeafA L18b RsCut]). Qed.
Lemma run18c : ltac2:(tb__ "0|1|
SeS8S7S31A1M0A1S33S77Ubb8S0S2fS3bS4S2fA1A3S58S3A5S6G0S0S31S36S5aS85A2S4S31A1A3A2A3"). Proof. exact (@eq_refl (option (list leafA)) run18c__R <: run18c__R = Some [mkLeafA L18c RsCut]). Qed.

Definition T18b : sstate := Eval vm_compute in move_obj_last (ax_S L18b) 14.
Definition U18b : axst := Eval vm_compute in ax_setS L18b (set_objs T18b (firstn 48 (ss_objs T18b))).
Definition oarea18b : sobj := Eval vm_compute in nth 48 (ss_objs T18b) odummy18.
Lemma T18b_facts : ltac2:(tb__ "0|3|
SfSeS18S79S32S59A1M0UeA2S52A3SfSeS5S75G0S52A2S3A3SfSeS1SbS12S15G0A1A2U31A3SfSeS7S12A1S15S52A1ScS12S15S32S47A1A1M1S0S12S68S4S12A1A3A3A3SfSeS30S37S59S86S52G1A2A2S47A3SeS12S68S1aS14S72S17P94A1S11Z1000A1M2A3S11Z0A1G2S4S16A1S1cA5A3A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition T18c1 : sstate := Eval vm_compute in move_obj_last (ax_S L18c) 14.
Definition T18c : sstate := Eval vm_compute in move_obj_last T18c1 14.
Definition U18c : axst := Eval vm_compute in ax_setS L18c (set_objs T18c (firstn 48 (ss_objs T18c))).
Definition oarea18c : sobj := Eval vm_compute in nth 48 (ss_objs T18c) odummy18.
Definition ogrp18c : sobj := Eval vm_compute in nth 49 (ss_objs T18c) odummy18.
Lemma T18c_facts : ltac2:(tb__ "0|6|
SfSeS18S79S32S5aA1M0UeM1A2S46A3SfSeS5S75G0S46A2S3A3SfSeS1SbS12S15G0A1A2U32M2A3SfSeS18S79S46G1A2S53A3SfSeS5S75S46S53A2S3A3SfSeS1SbS12S15S46A1A2G2A3SfSeS7S12A1S15S53A1ScS12S15S32S48A1A1M3S0S12S69S0S12S55S4S12A1A3A3A3A3SfSeS30S37S5aS86S53G3A2A2S48A3SfSeS12S69S1aS14S72S17P94A1S11Z1000A1M4A3S11Z0A1M5G4S4S16A1S1cA5A3SfSeS10S1fS55A1S17P95A1A3SfSeS10S21S55A1G5A3SeS10S20S55A1G4A3A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition ounk18 (o : sobj) : sobj := ltac2:(tb__ "0|0|
S1aS1fVo;A1S21Vo;A1S20Vo;A1S4S16A1S1cA5").
Definition J18objs2 : list sobj := Eval vm_compute in
  (let l := ss_objs (ax_S L18a) in
   let o i := nth i l odummy18 in
   [o 14; o 12; o 13; o 15; o 16; o 8; o 17; o 9; o 18;
    o 19; o 11; o 20; o 21; o 10; o 22; o 23; o 24; o 25;
    o 26; o 6; o 27; o 5; o 28; o 2; o 29; o 3; o 30; o 4; o 31; o 1; o 32; ounk18 (o 33); o 34; o 7; o 35;
    o 36; o 37; o 38; o 39; o 40; o 41; o 42;
    o 43; owin18; o 44;
    o 45; o 46; o 47]%nat).
Definition J18S : sstate := Eval vm_compute in
  (let St := ax_S L18a in
   mkSS JPC18 (list_set (list_set (list_set (ss_regs St) 10 (SVar 156%positive)) 11 (SVar 157%positive)) 13 (SVar 158%positive))
        (ss_fregs St) (ss_fcsr St) (ss_resv St) J18objs2 (ss_facts C18e) 159%positive (ss_lenient St)).
Definition J18 : axst := ltac2:(tb__ "0|0|
S35S3cS5bS11S83A1A3").
Definition sJ18 (L : axst) : wsub := ltac2:(tb__ "0|3|
S0SaS2eS10A2M0S2S2eS10P9cS6fS10UaS27S32VL;A1A1M1S11Z0A1M2A4A4S0G0S2S2eS10P9dS6fS10UbG1G2A4A4S0G0S2S2eS10P9eS6fS10UdG1G2A4A4S4G0A1A3A3A3").
Lemma entJ18a : ltac2:(tb__ "0|0|
SeS5S34S51S50S41S51A1A3S3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma entJ18b : ltac2:(tb__ "0|0|
SeS5S34S47S50S41S47A1A3S3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma entJ18c : ltac2:(tb__ "0|0|
SeS5S34S48S50S41S48A1A3S3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma sJ18_id : ltac2:(tb__ "0|1|
SfSeS5S84S41S51A1P9cM0A2S3A3SfSeS5S84S41S47A1G0A2S3A3SeS5S84S41S48A1G0A2S3A3A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma J18_at : ltac2:(tb__ "0|0|
SfSeS2fS26S3cA1S3bA3SfSeS2eS22S3cA1P9fA3SfSeS1SbS12S15S3cA1A2U30A3SfSeS5S23S3cA1S3A3SeS5S38S50A1S3A3A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition K18a : sstate := Eval vm_compute in (match merge_objs_at J18S 42 with Some St => St | None => J18S end).
Definition K18S : sstate := Eval vm_compute in (match merge_objs_at K18a 42 with Some St => St | None => K18a end).
Lemma K18_eq : ltac2:(tb__ "0|2|
SfSeS8S18A1M0S8cS3cU2aM1A2S6S18S66A2A3SeG0S8cS66G1A2S6S18S3dA2A3A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition K18 : axst := ltac2:(tb__ "0|0|
S35S3dS5bS11S83A1A3").
Lemma K18_at : ltac2:(tb__ "0|0|
SfSeS2fS26S3dA1S3bA3SfSeS2eS22S3dA1P9fA3SfSeS1SbS12S15S3dA1A2U2eA3SeS5S23S3dA1S3A3A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
End Start7States.

