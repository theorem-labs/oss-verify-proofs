(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_handle_vt o2.

(* [comment removed for export] *)
Module Lib_handle_vt_eqs.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "SLit"; "sprop"; "ss_objs"; "DUnknown"; "SVar"; "cell"; "ss_facts"; "DZero"; "SPUle"; "mkCell"; "@Corelib.Init.Datatypes"; "cons"; "nil"; "list"; "Some"; "option"; "pair"; "prod"; "app"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "axform"; "AXSelect"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs"; "avt_k"; "avt_d"; "hG"; "kb"; "bd_vec"; "hF"; "hFL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_subA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_vt"; "E_vr"; "T_pure"; "s_v"; "X_vt"; "vKg"; "E_opgc"; "E_opkc"; "gK"; "oK"; "s_opg"; "s_opk"; "vDg"; "T_sm1"; "epi_state"; "gD"; "oD"; "xf_opb"; "C_pro0"; "E_A"; "E_Dgc"; "E_Dkc"; "R_v"; "T_grown0"; "T_keep0"; "Xk_v"; "aw_d"; "aw_k"; "optAp"; "E_A1"; "E_A2"; "E_B"; "E_opg"; "E_opg1"; "E_opk"; "E_opk1"; "R_A"; "R_B"; "R_Dg"; "R_Dk"; "R_opg"; "R_opk"; "T_fail0"; "T_sm"; "Wp1"; "X_A"; "avt_cnt2"; "objs_A"; "objs_opg"; "objs_opk"; "objs_sm1"; "reshapeA"; "s_A"; "s_B"; "s_Dg"; "s_Dk"; "sel_rel"; "slot_facts"; "xf_D"; "xf_op"; "C_pro"; "E_Dg"; "E_Dk"; "E_sm0"; "E_vr0"; "O_fr0"; "R_sm"; "T_A0"; "T_A1"; "T_B0"; "T_B1"; "T_Dg0"; "T_Dg1"; "T_Dk0"; "T_Dk1"; "T_grown"; "T_keep"; "T_opg0"; "T_opg1"; "T_opk0"; "T_opk1"; "X_rlf"; "X_rlo"; "Xk_op"; "Y_fl"; "mid_dst"; "s_sm"; "xf_fl"; "xf_mc"; "xf_sd"; "xf_vr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double"; "Pre_sd"; "P_none"; "P_num"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve"; "Pre_vr"; "P_grown"; "P_keep"; "P_fail"; "bdP"; "tv0"; "vW"; "tvP"; "vK"; "vKn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o6.Lib_handle_vt_eqs.OP"; "Pre_op"; "P_op1"; "P_op0"; "tvQ"; "bd_op"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "import_tv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_setX"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o6.Lib_handle_vt_eqs"; "V_op"; "U_Dg0"; "U_Dg1"; "U_Dk0"; "U_Dk1"; "V_opg0"; "V_opg1"; "V_opk0"; "V_opk1"; "Z_fl"; "Z_opg0"; "Z_opg1"; "Z_opk0"; "Z_opk1"; "cells_op"; "cells_A"; "sel_sm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bd_subst"; "bitem"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "T_afterA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS"; "shadow_reopen_stateA"; "shadow_release_stateA"; "shobj"; "frame_open_stateA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "fs_frame_size"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "AE_A"; "L_stack_malloc"; "Pre_stack_malloc"; "flagbyte_obj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "T_afterA"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Code Lib_scan_double.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs Lib_handle_vt.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_vt.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_opt_push1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Import ScanDoubleAddr VRAddr RA.ReallocAddr HVTAddr.
Close Scope bv_scope.
Open Scope Z_scope.
Module OP. Include Lib_opt_push1. End OP.

Lemma T_sm_eq : ltac2:(tb__ "0|1|
S0S1Sb1SafSadZ1M0A2S62S79S65SaeSadG0A2A5S4eA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition sel_sm : list nat := Eval vm_compute in sel_last T_sm 3.
Lemma T_sm1_eq : ltac2:(tb__ "0|0|
S0S14S1A1S19S4eS10S1aS1bSa3A1S11S1aA1A3A2S13S1S30A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_sm1_objs : ltac2:(tb__ "0|1|
S0S12S5A1S8S2S30A1A1S17S5S55S10S5Sb0S22S10SbSfS6Z0A1Z1M0S6G0A1A3S11SbA1A3A2S11S5A1A3A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_sm1_X : ltac2:(tb__ "0|1|
S0S12S16S4S4A2M0A1S3S30A1S17G0S27S1dS1cS3dS3eA4S10G0S15S4S4S21S6SabZ1A1A1A4S11G0A1A3A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma C_pro0_eq : ltac2:(tb__ "0|0|
S0S1SaaS30S55S27S1dS1cS3dS3eA4Pa0SabZ1A1A5S35A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma C_pro_eq : ltac2:(tb__ "0|0|
S0S1S91S35S10S16S4S4A2S15S4S4S21S6Z0A1A4S3S35A1A3A2S5fA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition cells_A : list cell := Eval vm_compute in ob_cells sh_pro.
Lemma X_A_objs : ltac2:(tb__ "0|0|
S0S12S5A1S8S2S50A1A1S17S5S52S10S5Sa9S1eZ0Z10Sa2SdA5S11S5A1A3A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_A1_eq : ltac2:(tb__ "0|1|
S0S1Sa8S50S52Pa0S10S16S18S18A2M0S15S18S18Z20Z8A4S11G0A1A3A4S40A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_A2_eq : ltac2:(tb__ "0|0|
S0S1S56S40U1S64A3S41A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_A_eq : ltac2:(tb__ "0|0|
S0S14S1A1S19S41S7cA2S13S1S36A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_A0_eq : ltac2:(tb__ "0|0|
S0S1S25S7eS36S57S47S7fA5S66A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_A1_eq : ltac2:(tb__ "0|0|
S0S1S25S7eS36S57S47S80A5S67A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma T_B0_eq : ltac2:(tb__ "0|0|
S0S1S25S7eS42S58S48S7fA5S68A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_B1_eq : ltac2:(tb__ "0|0|
S0S1S25S7eS42S58S48S80A5S69A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma E_vr_eq : ltac2:(tb__ "0|0|
S0S14S1A1S19S63S7dA2S13S1S24A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_keep0_eq : ltac2:(tb__ "0|0|
S0S1Sa6S81S24S26S39S83S3cA6S3bA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_fail0_eq : ltac2:(tb__ "0|0|
S0S1Sa6S81S24S26S39S84S3cA6S4dA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_grown0_eq : ltac2:(tb__ "0|0|
S0S1Sa6S81S24S26S39S82S3cA6S3aA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_keep_eq : ltac2:(tb__ "0|0|
S0S1S92S3bS17S7S17S7S5cS1cA1S10S7SeS6SacA1S1dA2S11S7A1A3A3ScS2S3bA1A1A3A2S6fA3"). Proof. reflexivity. Qed.
Lemma T_grown_eq : ltac2:(tb__ "0|0|
S0S1S92S3aS17S7S5cS28A1ScS2S3aA1A1A3A2S6eA3"). Proof. reflexivity. Qed.
Lemma imp_keep_tv : ltac2:(tb__ "0|1|
S0S12S16S4S4A2M0A1S90S23S26S81S83S24A4S86A2S10G0S15S4S4S1dS1fZ4S1cA2A4S11G0A1A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_keep_bd : ltac2:(tb__ "0|0|
S0S12Sa5A1Sa4S23S26S81S83S24A4S85S87S89A2A2S20Z4S51S1cA3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_fail_tv : ltac2:(tb__ "0|1|
S0S12S16S4S4A2M0A1S90S23S26S81S84S24A4S86A2S10G0S15S4S4S1dS1fZ4S1cA2A4S11G0A1A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_grown_tv : ltac2:(tb__ "0|1|
S0S12S16S4S4A2M0A1S90S23S26S81S82S24A4S88A2S10G0S15S4S4S2fS1fZ4S28A2A4S11G0A1A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_grown_bd : ltac2:(tb__ "0|0|
S0S12Sa5A1Sa4S23S26S81S82S24A4S85S87S8aA2A2S20Z4S51S28A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition Z_fl : axst := Eval vm_compute in optAp (apply_axforms T_fail0 xf_fl).
Lemma Z_fl_eq : ltac2:(tb__ "0|0|
S0S14S1A1S19S4dS7aA2S13S1S9cA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Y_fl_eq : ltac2:(tb__ "0|0|
S0S1S91S9cS27S1dS1cS3dS3eA4A2S77A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_fl_eq : epi_state Y_fl = T_fl. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition E_mc1 (E0 : axst) : axst := ltac2:(tb__ "0|0|
S3fS19VE0;S7bA2A1").

Definition cmD (A : axst) (d : sv) : axst := ltac2:(tb__ "0|0|
S56VA;U1S78Vd;A1A3").
Lemma E_Dkc_eq : ltac2:(tb__ "0|0|
S0S14S1A1S19S61S5dA2S13S1S38A2A3").     Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_Dgc_eq : ltac2:(tb__ "0|0|
S0S14S1A1S19S60S5dA2S13S1S37A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition U_Dk0 : axst := Eval vm_compute in T_pure Pre_sd E_Dkc s_Dk R_Dk P_none.
Definition U_Dk1 : axst := Eval vm_compute in T_pure Pre_sd E_Dkc s_Dk R_Dk P_num.
Definition U_Dg0 : axst := Eval vm_compute in T_pure Pre_sd E_Dgc s_Dg R_Dg P_none.
Definition U_Dg1 : axst := Eval vm_compute in T_pure Pre_sd E_Dgc s_Dg R_Dg P_num.
Lemma U_Dk0_eq : ltac2:(tb__ "0|0|
S0S1S25S7eS38S5aS4aS7fA5S96A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma U_Dk1_eq : ltac2:(tb__ "0|0|
S0S1S25S7eS38S5aS4aS80A5S97A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma U_Dg0_eq : ltac2:(tb__ "0|0|
S0S1S25S7eS37S59S49S7fA5S94A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma U_Dg1_eq : ltac2:(tb__ "0|0|
S0S1S25S7eS37S59S49S80A5S95A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_Dk0_eq : ltac2:(tb__ "0|0|
S0S1Sa7S96S3S96A1S1eZ8ZbA5S6cA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_Dk1_eq : ltac2:(tb__ "0|0|
S0S1Sa7S97S3S97A1S1eZ8ZbA5S6dA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_Dg0_eq : ltac2:(tb__ "0|0|
S0S1Sa7S94S3S94A1S1eZ8ZbA5S6aA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_Dg1_eq : ltac2:(tb__ "0|0|
S0S1Sa7S95S3S95A1S1eZ8ZbA5S6bA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition cells_op : list cell := Eval vm_compute in ob_cells sh_op.
Lemma E_opk_objs : ltac2:(tb__ "0|0|
S0S12S5A1S8S2S45A1A1S17S5S54S10S5Sa9S1eZ8ZbSa1S9A5S11S5A1A3A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_opg_objs : ltac2:(tb__ "0|0|
S0S12S5A1S8S2S43A1A1S17S5S53S10S5Sa9S1eZ8ZbSa1S9A5S11S5A1A3A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_opk1_eq : ltac2:(tb__ "0|2|
S0S1Sa8S45S54Pa0S10S16S18S18A2M0S15S18S18Z40Z4M1A4S10G0S15S18S18Z50G1A4S11G0A1A3A3A4S46A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_opg1_eq : ltac2:(tb__ "0|2|
S0S1Sa8S43S53Pa0S10S16S18S18A2M0S15S18S18Z40Z4M1A4S10G0S15S18S18Z50G1A4S11G0A1A3A3A4S44A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_opkc_eq : ltac2:(tb__ "0|0|
S0S14S1A1S19S46S5eA2S13S1S2aA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_opgc_eq : ltac2:(tb__ "0|0|
S0S14S1A1S19S44S5eA2S13S1S29A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition V_op (E : axst) (s : wsub) (R : list sobj) (P : axst) (d k : sv) : axst := ltac2:(tb__ "0|0|
Sa6S8bVE;Vs;VR;VP;S76Vd;Vk;A2A6").
Definition V_opk1 : axst := Eval vm_compute in V_op E_opkc s_opk R_opk OP.P_op1 avt_d avt_k.
Definition V_opk0 : axst := Eval vm_compute in V_op E_opkc s_opk R_opk OP.P_op0 avt_d avt_k.
Definition V_opg1 : axst := Eval vm_compute in V_op E_opgc s_opg R_opg OP.P_op1 vDg vKg.
Definition V_opg0 : axst := Eval vm_compute in V_op E_opgc s_opg R_opg OP.P_op0 vDg vKg.
Lemma V_opk1_eq : ltac2:(tb__ "0|0|
S0S1S93S2aS2eS4cS8cS1dS1cA6S9bA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma V_opk0_eq : ltac2:(tb__ "0|0|
S0S1S93S2aS2eS4cS8dS1dS1cA6S9aA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma V_opg1_eq : ltac2:(tb__ "0|0|
S0S1S93S29S2dS4bS8cS2fS28A6S99A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma V_opg0_eq : ltac2:(tb__ "0|0|
S0S1S93S29S2dS4bS8dS2fS28A6S98A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition Z_opk1 : axst := Eval vm_compute in optAp (apply_axforms V_opk1 xf_opb).
Definition Z_opk0 : axst := Eval vm_compute in optAp (apply_axforms V_opk0 xf_opb).
Definition Z_opg1 : axst := Eval vm_compute in optAp (apply_axforms V_opg1 xf_opb).
Definition Z_opg0 : axst := Eval vm_compute in optAp (apply_axforms V_opg0 xf_opb).
Lemma Z_opk1_eq : ltac2:(tb__ "0|0|
S0S14S1A1S19S9bS34A2S13S1Sa0A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Z_opk0_eq : ltac2:(tb__ "0|0|
S0S14S1A1S19S9aS34A2S13S1S9fA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Z_opg1_eq : ltac2:(tb__ "0|0|
S0S14S1A1S19S99S34A2S13S1S9eA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Z_opg0_eq : ltac2:(tb__ "0|0|
S0S14S1A1S19S98S34A2S13S1S9dA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_opk1_eq : ltac2:(tb__ "0|0|
S0S1S31S91Sa0S27S1dS1cS33S2cA4A2A1S73A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_opk0_eq : ltac2:(tb__ "0|0|
S0S1S31S91S9fS27S1dS1cS33S2cA4A2A1S72A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_opg1_eq : ltac2:(tb__ "0|0|
S0S1S31S91S9eS27S2fS28S32S2bA4A2A1S71A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_opg0_eq : ltac2:(tb__ "0|0|
S0S1S31S91S9dS27S2fS28S32S2bA4A2A1S70A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_opk1_tv : ltac2:(tb__ "0|1|
S0S12S16S4S4A2M0A1S90S23S2eS8bS8cS2aA4S8eA2S10G0S15S4S4S33S1fZ4S2cA2A4S11G0A1A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_opk1_bd : ltac2:(tb__ "0|0|
S0S12Sa5A1Sa4S23S2eS8bS8cS2aA4S8fSaP8eA1A1A2S20Z4S4fS2cA3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_opk0_tv : ltac2:(tb__ "0|1|
S0S12S16S4S4A2M0A1S90S23S2eS8bS8dS2aA4S8eA2S10G0S15S4S4S33S1fZ4S2cA2A4S11G0A1A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_opg1_tv : ltac2:(tb__ "0|1|
S0S12S16S4S4A2M0A1S90S23S2dS8bS8cS29A4S8eA2S10G0S15S4S4S32S1fZ4S2bA2A4S11G0A1A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_opg1_bd : ltac2:(tb__ "0|0|
S0S12Sa5A1Sa4S23S2dS8bS8cS29A4S8fSaP8eA1A1A2S20Z4S4fS2bA3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_opg0_tv : ltac2:(tb__ "0|1|
S0S12S16S4S4A2M0A1S90S23S2dS8bS8dS29A4S8eA2S10G0S15S4S4S32S1fZ4S2bA2A4S11G0A1A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma X_rlo_eq : ltac2:(tb__ "0|1|
S0S14S1A1S19S75S10S1aS1bS5bA1S11S1aA1A3A2M0S13S1S3fG0A1A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma X_rlf_eq : ltac2:(tb__ "0|1|
S0S14S1A1S19S74S10S1aS1bS5bA1S11S1aA1A3A2M0S13S1S3fG0A1A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
End Lib_handle_vt_eqs.

(* [comment removed for export] *)
Module Lib_handle_vt_chk.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs"; "NPH"; "@Corelib.Init.Datatypes"; "bool"; "true"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_vt"; "FUEL_vt"; "cutpcs_vt"; "cutsV"; "exitsV"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ejcertA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG SymSummary.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA TobjJA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs Lib_handle_vt.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_vt.
Import ListNotations.
Open Scope Z_scope.

Lemma ejcertV_ok : ltac2:(tb__ "0|0|
S3S1S9S4S0S5S6S0S7S8A7S2A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End Lib_handle_vt_chk.

(* [comment removed for export] *)
Module Lib_handle_vt_pf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "or"; "not"; "True"; "ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "valuation"; "ss_facts"; "sprop"; "sobj"; "SLit"; "ss_next"; "ss_objs"; "SPUle"; "holds"; "SAlu"; "sprop_eqb"; "SVar"; "swf"; "SPEq"; "DUnknown"; "cell"; "mkObj"; "obj_range"; "obj_wf"; "soff"; "sprop_below"; "agree_below"; "@Corelib.Init.Datatypes"; "list"; "bool"; "true"; "prod"; "pair"; "cons"; "nil"; "Some"; "nat"; "option"; "None"; "fst"; "orb"; "snd"; "app"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "has_facts"; "ax_base"; "g8"; "leafA"; "la_state"; "ax_setS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_vt"; "fr_vt"; "aw_d"; "aw_k"; "cutsV"; "Xk_op"; "z0"; "L_mc1"; "Pre_mc"; "bdK"; "epi_state"; "tv_vt"; "PD_op"; "avt_cnt2"; "cm4"; "nd0"; "ndO"; "ndP"; "ndX"; "tvI"; "tvP"; "Pre_vt"; "R_v"; "T_pure"; "dst_obj"; "gD"; "gK"; "ndG"; "ndK"; "oD"; "oK"; "reshapeA"; "src_obj"; "vDg"; "vKg"; "E_A1"; "E_B"; "E_Dg"; "E_Dk"; "E_opg"; "E_opk"; "E_sm0"; "E_vr"; "E_vr0"; "L_sm"; "PD_vr"; "P_fail"; "P_ok"; "Pre_sm"; "Wp1"; "X_A"; "X_rlf"; "X_rlo"; "Xk_v"; "avt_cnt"; "exitsV"; "ndEf"; "ndEo"; "ndF"; "nd_fail"; "nd_ok"; "s_v"; "sel_rel"; "slot_facts"; "xf_D"; "xf_mc"; "xf_op"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "smatchA"; "stableA"; "@Stdlib.ZArith.BinInt.Z"; "le"; "pow"; "mul"; "lt"; "add"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs"; "NPH"; "hG"; "hF"; "kb"; "bd_vec"; "avt_d"; "avt_k"; "tB"; "tL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "ANone"; "NDA"; "PTrue"; "TPA"; "frinA"; "nd_below"; "tvinA"; "JA_pre"; "emeasA"; "fbinA"; "ffinA"; "JA"; "JLA"; "frozen"; "nodeIA"; "ok_frameKA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o6.Lib_handle_vt_pf"; "P0_vt"; "bF"; "extraXV"; "fF"; "P0_vt_b"; "DW_rng"; "O_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "uval"; "bitem"; "BXok_d"; "bd_below"; "bd_subst"; "bd_wpos"; "bxt"; "bud_pay"; "@Stdlib.Lists.List"; "In"; "existsb"; "forallb"; "nth_error"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "entails_frA"; "call_checkPA"; "import_subA"; "call_checkA"; "J_ofPA"; "import_postA"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "firstn"; "skipn"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "call_linkP"; "wsub_dom_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "topG"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o1.Lib_builderH_pf"; "extraOH"; "extraOH_client"; "extraXH"; "frozen_stableH"; "payA_sameH"; "siteFH"; "siteHH"; "sitePH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS"; "xrs_checkL"; "shadow_reopen_stateA"; "robjs_checkF"; "xlocal"; "release_objs_ok"; "shadow_release_stateA";
"shobj"; "wclear"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_vt.HVTAddr"; "DW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o6.Lib_handle_vt_pf.OP"; "Pre_op"; "P_op1"; "P_op0"; "bd_op"; "tvQ"; "nd0"; "tv0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub"; "rho_absorb"; "rho_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "tvd"; "tvz"; "T_ok"; "FBx"; "import_tv"; "remove_nth"; "tv_sub_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o6.Lib_handle_vt_pf.Sum"; "robjs_checkFP"; "HNPH"; "Posts_vtJ"; "JLv"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAT"; "robjs_checkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "axform"; "AXSelect"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "FFx"; "pclMA"; "xr_eqb"; "PostsC"; "T_afterA3"; "robjs_okF"; "xrs_inclb"; "xrs_okF"; "pd_okA"; "pdescA"; "xrs_okL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "SHADOW_OFF"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double"; "Pre_sd"; "P_none"; "P_num"; "Posts_sd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve"; "B32"; "Pre_vr"; "nd0"; "vK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "le"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs"; "vAL"; "vb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ny.Lib_builder_pf"; "baseF"; "P0_builder"; "basez"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o6.Lib_handle_vt_pf.OPP"; "P0_op"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double.ScanDoubleAddr"; "pow10_tab"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nn.Lib_vec_reserve_pf"; "P0_vr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA"; "infrFF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "call_checkTA"; "ccount"; "T_afterA"; "is_shadowZ"; "payA"; "robjs_okA"; "site_okA"; "xrs_okA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR"; "robjs_okF"; "xrs_ok47"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "AE_A"; "JL_pure"; "JL_stack_malloc"; "J_memcpy_pre"; "J_stack_malloc_pre"; "alloc_contractsA"; "alloc_contractsA_ex"; "alloc_lawsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o6.Lib_handle_vt_eqs"; "V_opg0"; "V_opg1"; "V_opk0"; "V_opk1"; "cells_op"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "jnodeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_setX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3"; "import_okPA3"; "import_postA3"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Lib_scan_double.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n9.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n9.Lib_scan_double_ex.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ny.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_handle_vt.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nn.Lib_vec_reserve_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ny.Lib_builder_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o1.Lib_builderH_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_vt OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o6.Lib_handle_vt_eqs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o6.Lib_handle_vt_chk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_opt_push1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Import ScanDoubleAddr VRAddr RA.ReallocAddr HVTAddr.
Close Scope bv_scope.
Open Scope Z_scope.
Module OP. Include Lib_opt_push1. End OP.
Module OPP. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o2.Lib_opt_push1_pf. End OPP.

Definition P0_vt (CST : list (Z * Z)) (FB : list (Z * Z)) (FF : list (Z * Z * Z)) (r : valuation) : Prop := ltac2:(tb__ "0|1|
S1S116VCST;VFB;VFF;Vr;A4S0S25S11dZ1SbbS20S20S2cS2cA2M0S2cA2G0S28G0S2cA2VFF;A4A2U0A3A2").
Lemma P0_vt_b : ltac2:(tb__ "0|2|
S1dS20S2cS2cA2M0A1M1G1S1dS20G0S2cA2A1S7S9fR4R3R2R1A4S116R5R4R3R2A4F_;Fr;FFF;FFB;FCST;").
Proof. intros CST FB FF r [H _]. exact H. Qed.

Definition bF (F : list sprop) : bool := baseF DW F.
Definition fF (F : list sprop) : bool := frameF hG 160 128 F.
Lemma DW_rng : 0 <= DW < 2 ^ 40. Proof. unfold DW. lia. Qed.
Lemma sz_rng : 0 <= 128 < 2 ^ 40. Proof. lia. Qed.

Definition extraXV (r : sv * sv) : bool := ltac2:(tb__ "0|0|
S29Sc9Vr;A1SfbVr;S21S6S6SbS119A1SbZb8A1A4A2A2").

Definition O_frA : sobj := Eval vm_compute in nth 1 (ss_objs (ax_S E_A1)) O_Wv.
Lemma E_A1_o1 : ltac2:(tb__ "0|0|
S0S26SaA1Sb1SaSdS2fS5bA1A1U1A3S24SaSa5A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
Sc3S7S1dS38Q40A1A1SbeOF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
S12dS37VAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S2cS10eVCST;R1A2S1S7fZ0R2A2S82R2S105A2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S2cS10eVXGL;R1A2S1S7fZ0R2A2S82R2S105A2A2F_;Fa;").
Hypothesis HXpow : ltac2:(tb__ "0|0|
S2cS1S7fS119R1A2S82R1S83S119Zb8A2A2A2S10eVXGL;R2A2F_;Fa;").
Hypothesis LFLAG : law_flag_stmt AInv.
Hypothesis LFSH : law_fshadow_stmt AInv.
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S1dS20S20S2cS2cA2S2cA2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 5 BX.
Let HNP : NP_okA NF := NP_okA_intro NF eq_refl.
Variable rho0 : valuation.
Let HTOP : InitState.segs_top segs <= IMG_HI := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nn.Lib_arena_alloc.HTOP_ok.
Lemma HNPH : (NF <= NPH)%positive. Proof. unfold NF, NPH. lia. Qed.

Definition JLv (nd : ndesc) : jpostA := ltac2:(tb__ "0|0|
S9bVAInv;VCST;VXGL;VKc;S9fVCST;VFB;VFF;A3VFB;VFF;VBX;S91Vnd;Aa").
Definition Posts_vtJ : list (axst * jpostA) := ltac2:(tb__ "0|1|
S22S20S2eSb2A2M0S21S2eSb2S66Sf1S73A1A4S22G0S21S2eSb2S67Sf1S74A1A4S23G0A1A3A3").
Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S9aVAInv;VCST;VXGL;S85VKc;Vrho0;S9fVCST;VFB;VFF;A3VFB;VFF;VBX;S91Vnd;Ac").
Let nI : ltac2:(tb__ "0|0|
S20S2eS8eA2S135Fn;") := ltac2:(tb__ "0|0|
S9dVAInv;VCST;VXGL;S85VKc;Vrho0;S9fVCST;VFB;VFF;A3VFB;VFF;VBX;S91Ab").
Let Q (tp0 : list word) : assn := ltac2:(tb__ "0|0|
Sb3S37S85Vrho0;Vtp0;Sf0A5").
Let siteP : ltac2:(tb__ "0|0|
Sc3S7S1dS9A1S1dS20S6S6A2A1S1dS20S20S6S2cA2S6A2A1S26S25A1S1dSaA1S7S1dS38Q40A1A1SbeVAInv;RaR3R2R1A4SbaS9SfRaA1R9A3S0S1eS115Sd7RaA2S1fA3Sc0S85Vrho0;RcA3S9fVCST;VFB;VFF;Vrho0;A4S92Vrho0;RfA2Se9RfSc5Sc4R10A1A1A2S98VFB;R11A2S99VFF;R12A2S95VFB;R13R12R10A4Se7R13R11A2Se8R14R12A2S93VFF;R16R15R12A4S0S1eSf5R15R14R13R12Sc7R11A6S1fA3S121VCST;R18S27S2cA1R17R12A5F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FR;Fskip;Ffr;Ftv;Ffacts;Frho;FAi;") := ltac2:(tb__ "0|0|
SceVAInv;VCST;VALA;S85SefVFB;VFF;Vrho0;S9fVCST;VFB;VFF;A3Sa3VCST;VFB;VFF;A3Sd7Sa4Ac").
Let siteF : ltac2:(tb__ "0|0|
Sc3S7S1dS9A1S1dS20S6S6A2A1S1dS20S20S6S2cA2S6A2A1S1dSaA1S7S1dS38Q40A1A1SbeVAInv;R9R3R2R1A4SbaS9SfR9A1R8A3S0S1eS115Sd7R9A2S1fA3Sc0S85Vrho0;RbA3S9fVCST;VFB;VFF;Vrho0;A4S92Vrho0;ReA2Se9ReSc5Sc4RfA1A1A2S95VFB;R10RfRdA4Se7R10ReA2Se8R11RfA2S93VFF;R13R12RfA4S0S1eSd1R12R11R10S27S25A1Sc7RfA6S1fA3S124VCST;Vrho0;VFB;VFF;R14R12R11R10A8F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FR;Ffr;Ftv;Ffacts;Frho;FAi;") := ltac2:(tb__ "0|0|
SccVAInv;VCST;VALA;S85SefVFB;VFF;Vrho0;S9fVCST;VFB;VFF;A3Sa3VCST;VFB;VFF;A3Sd7Sa4Ac").
Let siteH : ltac2:(tb__ "0|1|
Sc3S7S1dS9A1S1dS20S6S6A2A1S1dS20S20S6S2cA2S6A2A1S1dSaA1S7S1dS38Q40A1A1SbeVAInv;R9R3R2R1A4SbaS9SfR9A1R8A3S0S1eS115Sd7R9A2S1fA3Sc0S85Vrho0;RbA3S9fVCST;VFB;VFF;Vrho0;A4S92Vrho0;ReA2Se9ReSc5Sc4RfA1A1A2S95VFB;R10RfRdA4Se7R10ReA2Se8R11RfA2S93VFF;R13R12RfA4S0S1eSd1R12R11R10S27S25A1Sc7RfA6S1fA3SaS2cSaeSaR2R12A3S1S7fS28S2cS2cS18R17R3A2M0A3R2A2S82R2S2aS2cS2cG0A3A2A2S2SfaVCST;Vrho0;SeaVFB;R18R16A3Sf9VFF;R18R15A3R3A5S2S1S7fZ0R3A2S82R3S105A2A2S11fR3A1A2A2F_;F_;Fa;Fo;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FR;Ffr;Ftv;Ffacts;Frho;FAi;") := ltac2:(tb__ "0|0|
ScdVAInv;VCST;VALA;S85SefVFB;VFF;Vrho0;S9fVCST;VFB;VFF;A3Sa3VCST;VFB;VFF;A3Sd7Sa4Ac").
Let payA_same : ltac2:(tb__ "0|1|
S1dS9A1S1dSa7A1S0S1eSabR1A1S1fA3S120S85Vrho0;S9fVCST;VFB;VFF;A3R3SbZ0M0A1G0R2R2A8F_;Fbd;Ffacts;") := ltac2:(tb__ "0|0|
ScbS85Vrho0;S9fVCST;VFB;VFF;A3A3").
Let frozen_stable : ltac2:(tb__ "0|0|
S2dS2dS8eS7S110S85R3A2S0S1eS94R4R3A2S1fA3S7eS37R6S9cVAInv;VCST;VXGL;S85VKc;Vrho0;S9fVCST;VFB;VFF;A3VFB;VFF;VBX;S91R4R3AdA3F_;F_;Frho;Fnd;Fm;Fn;") := ltac2:(tb__ "0|0|
ScaVAInv;VCST;VXGL;VALA;S85VKc;VHKc;VFB;VFF;VBX;Vrho0;S9fVCST;VFB;VFF;A3Ac").
Let extra_client : ltac2:(tb__ "0|1|
S7SaS2cS1dS20S6S6A2A1S1dS20S20S6S2cA2S6A2A1S117Sd7R5A2Sc0S85Vrho0;R6A3S9fVCST;VFB;VFF;Vrho0;A4S0S1eSc7R7A1S1fA3S1S7fS28S2cS2cS18R9R8A2M0A3R7A2S82R7S2aS2cS2cG0A3A2A2SfaVCST;Vrho0;SeaVFB;RaR7A3Sf9VFF;RaR6A3R8A5F_;F_;F_;F_;F_;Ffrs;Fkept;Fa;Fo;Frho;") := ltac2:(tb__ "0|0|
Sc8VCST;S85SefVFB;VFF;Vrho0;S9fVCST;VFB;VFF;A3Sa3VCST;VFB;VFF;A3Sd7A9").

Lemma P0_now : ltac2:(tb__ "0|2|
S7Sc0S85Vrho0;R1A3S9fVCST;VFB;VFF;Vrho0;A4S1S2cS1S7fSa6R4S8cA2M0R1A2S82R1S83G0Sa6R4S8dA2A2A2A2SfaVCST;Vrho0;VFB;VFF;R2A5F_;Fa;S1S11bVFF;Sa6R3S114A2Z518A3S1S11bVFF;Sa6R3S113A2Z30A3S0S25S11dZ1SbbS20S20S2cS2cA2M1S2cA2G1S28G1S2cA2VFF;A4A2U0A3A2A2A2F_;F_;Frho;").
Proof.
  intros rho Hav HP. destruct (P0b_nowH CST NPH HNPH FB FF rho0 (P0_vt CST FB FF) (P0_vt_b CST FB FF) rho Hav HP) as (A & B & C).
  destruct HP as [_ D]. auto.
Qed.

Lemma extraXV_client : ltac2:(tb__ "0|2|
S7S20S6S6A2M0S2cS1dG0A1S1dS20S20S6S2cA2S6A2A1S117Sd7R5A2Sc0S85Vrho0;R6A3S9fVCST;VFB;VFF;Vrho0;A4S0S1eSa1R7A1S1fA3S1S7fSa6R9S28S6S6R8A3A2M1R7A2S82R7S83G1Sa6R9S2aS6S6R8A3A2A2A2A2S2SfaVCST;Vrho0;SeaVFB;RaR7A3Sf9VFF;RaR6A3R8A5S10eVXGL;R8A2A2F_;F_;F_;F_;F_;Ffrs;Fkept;Fa;Fr;Frho;").
Proof.
  intros rho r a kept frs BZ Hav HP0 HE Hr. unfold extraXV in HE. apply orb_prop in HE as [HE|HE].
  - left. apply (in_callersH_ok CST NPH HNPH FB FF rho0 (P0_vt CST FB FF) (P0_vt_b CST FB FF) rho a kept frs Hav HP0). exact (extraXH_sound DW rho r a BZ HE Hr).
  - apply xr_eqb_sound in HE. subst r. cbn [fst snd] in Hr. rewrite !uval_lit in Hr by (unfold pow10_tab; lia). right. apply HXpow. exact Hr.
Qed.
Lemma siteX : ltac2:(tb__ "0|4|
Sc3S7S1dS9A1S1dS20S6S6A2A1M0S1dS20S20S6S2cA2S6A2M1A1M2S26S25A1M3S1dSaA1G0S7S1dS38Q40A1A1SbeVAInv;RbR3R2R1A4SbaS9SfRbA1RaA3S0S1eSa0RbA1S1fA3Sc0S85Vrho0;RdA3S9fVCST;VFB;VFF;Vrho0;A4S92Vrho0;R10A2Se9R10Sc5Sc4R11A1A1A2S98VFB;R12A2S99VFF;R13A2S95VFB;R14R13R11A4Se7R14R12A2Se8R15R13A2S93VFF;R17R16R13A4S0S1eScfVXGL;R16R15R14R13R12Sa1R11A8S1fA3S1S103VCST;VXGL;Vrho0;VFB;VFF;R18R16G3G2Lskip;R14S25SecG1R1R16A3Li;R15X26x2R12A9S1S123VCST;VXGL;R19S27S2cA1R18R12A6S125R18R12A2A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FX;Fobjs;Fskip;Ffr;Ftv;Ffacts;Frho;FAi;").
Proof.
  intros Ai rho facts tv fr skip objs X rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HBf HFF HN HD HZ HFR Hchk.
  assert (HEX : forall r a, In r X -> extraXV r = true -> uval rho (fst r) <= a < uval rho (fst r) + uval rho (snd r) ->
            pclMA CST rho0 (FBx FB rho tv) (FFx FF rho (match skip with Some i => remove_nth i fr | None => fr end)) a \/ RtCells.in_rangesZ XGL a).
  { intros r a Hr HE Ha. exact (extraXV_client rho r a _ _ (basez_of DW rho facts DW_rng HF HB) Hav HP0 HE Ha). }
  split; [exact (xrs_checkL_sound segs AInv CST XGL ALA rho0 FB FF Ai rho facts tv fr skip objs extraXV X rho1 tp1 md1 HM HF (T_ok_T0 rho0 _ Ai HT HTK) HN HD HZ HFR Hchk HEX)|].
  exact (xrs_checkL_okA segs AInv CST XGL ALA HCST HXGL rho0 FB FF Ai rho facts tv fr skip objs extraXV X rho1 tp1 md1 HM HF HT HTK HBf HFF HN HD HZ HFR Hchk HEX).
Qed.
Lemma site_pure : ltac2:(tb__ "0|2|
S2eSe4S1dSaA1S7S1dS20S6S6A2A1S1dS20S20S6S2cA2S6A2A1S1dSa7A1S0S1eSa0S8S2fR7A1A1A1S1fA3S0S1eSf5S8S2fR8A1A1R4R3S27S25A1M0Sc7R6A6S1fA3S0S1eScfVXGL;S8S2fR9A1M1A1R5R4G0SdG1A1Sa1S30R9A1A8S1fA3S122VAInv;VCST;VXGL;S85Vrho0;S9fVCST;VFB;VFF;A3VFB;VFF;RaR9R8R7S90R6R5R4S8fA4S27S2cA1Sc3Sf2S4L_;L_;AfF_;F_;F_;Fbd;Ffr;Ftv;Frho;FR;Fs;FE;").
Proof.
  intros E s R rho tv fr bd HB HR HX Ai ms HF HP0 Hav HBf HFF HN HD HZ HFR (rho1 & tp1 & md1 & HM) HT HTK. cbn [nd_tv nd_fr] in HN, HD, HZ, HFR.
  split; [exact (siteP Ai rho _ tv fr None R rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HBf HFF HN HD HZ HFR HR)|].
  split; [exact (proj1 (proj2 (siteX Ai rho _ tv fr None _ _ rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HBf HFF HN HD HZ HFR HX))) | exact I].
Qed.

Definition robjs_checkFP (facts : list sprop) (tv : list (sv * sv)) (fr : list (sv * Z * sv)) (R : list sobj) : bool := ltac2:(tb__ "0|2|
Sb0SaSaS29Sd1Vfacts;Vtv;Vfr;S27S25A1M0Sc7S22SaR1S23SaA1A3M1A6Sf5Vfacts;Vtv;Vfr;G0Sc7G1A6A2Lo;VR;A3").
Lemma siteF2 : ltac2:(tb__ "0|0|
Sc3S7S1dS9A1S1dS20S6S6A2A1S1dS20S20S6S2cA2S6A2A1S1dSaA1S7S1dS38Q40A1A1SbeVAInv;R9R3R2R1A4SbaS9SfR9A1R8A3S0S1eSa0R9A1S1fA3Sc0S85Vrho0;RbA3S9fVCST;VFB;VFF;Vrho0;A4S92Vrho0;ReA2Se9ReSc5Sc4RfA1A1A2S95VFB;R10RfRdA4Se7R10ReA2Se8R11RfA2S93VFF;R13R12RfA4S0S1eSeeR12R11R10RfA4S1fA3S124VCST;Vrho0;VFB;VFF;R14R12R11R10A8F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FR;Ffr;Ftv;Ffacts;Frho;FAi;").
Proof.
  intros Ai rho facts tv fr R rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HN HD HZ HFR Hchk o a Ho Hr.
  pose proof (proj1 (forallb_forall _ _) Hchk o Ho) as Hc. cbn beta in Hc. apply orb_prop in Hc as [Hc|Hc].
  - exact (siteF Ai rho facts tv fr [o] rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HN HD HZ HFR Hc o a (or_introl eq_refl) Hr).
  - left. eapply (robjs_checkP_sound segs AInv CST ALA rho0 FB FF Ai rho facts tv fr None extraOH [o] rho1 tp1 md1 HM HF (T_ok_T0 rho0 _ Ai HT HTK) HN HD HZ HFR Hc);
      [intros o' a' Ho' HE Hr'; exact (extra_client rho o' a' _ _ (basez_of DW rho facts DW_rng HF HB) Hav HP0 HE Hr') | left; reflexivity | exact Hr].
Qed.

Lemma JA_tv_swap2 : ltac2:(tb__ "0|1|
S20S6S6A2M0G0S1dG0A1S1dS20S20S6S2cA2S6A2A1S1dSa7A1S7S1dS38Q40A1A1S1dSbfA1SbeVJAv;S90S22G0R9S22G0R8R7A3A3R6R5S8fA4R4R3R2R1A5VJAv;S90S22G0R9S22G0RaR8A3A3R7R6S8fA4R5R4R3R2A5F_;Fmd;Ftr;Ftp;Frho;Fbd;Ffr;Fr;Fb;Fa;").
Proof.
  intros a b r fr bd rho tp tr md (Ai & kc & HJ).
  pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & HFR & HK0 & HP0 & HXA & HBU & HPA).
  cbn [nd_tv nd_fr nd_bd nd_am] in HN, HD, HZ, HFR, HXA, HBU.
  assert (HCNT : cntS rho (a :: b :: r) <= cntS rho (b :: a :: r)) by (rewrite !cntS_cons; lia).
  exists Ai, kc. unfold JAi. cbn [nd_tv nd_fr nd_bd nd_am].
  split; [exact Hav|]. split; [exact Hk|]. split; [exact HM|]. split; [exact HT|]. split; [exact HB|]. split; [exact HFF|].
  split.
  - split; [|split].
    + inversion HN as [|x l Ha HN1]; subst. inversion HN1 as [|y l' Hb HN2]; subst. constructor; [exact Hb|]. constructor; [exact Ha | exact HN2].
    + cbn [tvd] in HD |- *. destruct HD as (Da & Db & Dr). split; [|split; [|exact Dr]].
      * intros t' Ht' Hzb Hzt. destruct Ht' as [<-|Ht'].
        -- intros E. apply (Da b (or_introl eq_refl) Hzt Hzb). symmetry. exact E.
        -- exact (Db t' Ht' Hzb Hzt).
      * intros t' Ht' Hza Hzt. exact (Da t' (or_intror Ht') Hza Hzt).
    + inversion HZ as [|x l Ha HZ1]; subst. inversion HZ1 as [|y l' Hb HZ2]; subst. constructor; [exact Hb|]. constructor; [exact Ha | exact HZ2].
  - split; [exact HFR|]. split; [exact HK0|]. split; [exact HP0|]. split; [|split; [exact HBU | exact (JA_tail_le _ _ _ rho rho _ _ HCNT HPA)]].

    unfold XA in HXA |- *. destruct HXA as [HX0 HCEN]. split; [exact HX0|].
    intros bn L1 L2 L3 L4. apply (HCEN bn L1 L2 L3). intros v Hv. apply L4. unfold tvals in *. cbn [map In] in Hv |- *. tauto.
Qed.
Lemma SPA_swap2 : ltac2:(tb__ "0|1|
S20S6S6A2M0G0S1dG0A1S1dS20S20S6S2cA2S6A2A1S1dSa7A1S2eS7S1dS38Q40A1A1Se0S7bS37VJAv;S90S22G0R9S22G0R8R7A3A3R6R5S8fA4A1R4R3R2R1A6S7bS37VJAv;S90S22G0R9S22G0RaR8A3A3R7R6S8fA4A1R5R4R3R2A6F_;Fw;Ftp;Frho;FS;Fbd;Ffr;Fr;Fb;Fa;").
Proof. intros a b r fr bd S rho tp w [Hsm HJ]. split; [exact Hsm | apply JA_tv_swap2; exact HJ]. Qed.

Lemma tvz_kd : ltac2:(tb__ "0|2|
S7S2cS6S6S1dS20S6S6A2M0A1Se8R5S22G0S21S6S6R3S88R4R2A2A4R1A3A2S1S82Z0M1R5A2S7fR5ZcA2A2S7fSa6R7R4A2S10aA2S3S0S2cSa6R8R5A2G1A3A1S3S0S2cSa6R9R7A2G1A3A1F_;F_;F_;F_;Fr;Fk;Fd;Fe;Frho;").
Proof.
  intros rho e d k r HZ He HK Hk Hd. apply Forall_inv in HZ. unfold tnz, tvv in HZ. cbn [fst snd] in HZ. unfold uval in Hd, Hk, HK.
  specialize (HZ ltac:(intros H; exact (H Hd))). unfold B32 in HK.
  pose proof (uval_mul_lit rho e k ltac:(lia) ltac:(unfold uval; nia)) as E12. unfold uval, kb in E12. unfold kb in HZ. rewrite E12 in HZ. nia.
Qed.
Lemma Forall_single : forall {A} (P : A -> Prop) a l, Forall P (a :: l) -> Forall P [a].
Proof. intros A P a l H. constructor; [exact (Forall_inv H) | constructor]. Qed.
Lemma tvd_single : ltac2:(tb__ "0|1|
S7S20S6S6A2M0Se7R2S22G0R1S23G0A1A3A2Ft;Frho;"). Proof. intros rho t. cbn. split; [intros t' [] | exact I]. Qed.
Lemma foff_rng : ltac2:(tb__ "0|0|
S7S1dS9A1S2cSbaS9SfR3A1R2A3S0S1eSa2R3A1S1fA3S1S7fZ0R3A2S7fR3Z80A2A2S0S2cSa6R6S10Sc6S87SbR4A1A3A2S83Sa6R6S87A2R4A2A3F_;F_;F_;Foff;FF;Fr;").
Proof. intros r F off HF HFR Ho. unfold hF. apply (frame_off_rng hG 160 128 off r F sz_rng Ho HF HFR). Qed.
Lemma slot_rng : ltac2:(tb__ "0|1|
S7S1dS9A1S6S6S2cS1S7fZ0R1A2S7fR1ZcA2A2SbaS9SfR6A1R5A3S0S1eSafS9S11SeR5SbZ800000000000A1A2A1R6A3S1fA3S0S1eSafS9S11SeR5SbS10aA1A2A1R7A3S1fA3S1S0S2cSa6R9S10Sc6R7R6A3A2S83Sa6R9R7A2Sa6R9R6A2M0A2A3S1S0S2cS1aR9R6A2G0A3S0S2cS1aR9S10Sc6R6SbR5A1A3A2S83G0R5A2A3A2A2F_;F_;F_;F_;Fw;Fcm;Fd;FF;Fr;").
Proof.
  intros r F d cm w Hw HF Hd Hs.
  pose proof (holds_mem _ _ _ HF Hd) as F1. pose proof (holds_mem _ _ _ HF Hs) as F2.
  rewrite h_ule in F1, F2. unfold B32 in F2. rewrite uval_lit in F1 by lia. rewrite uval_lit in F2 by lia.
  pose proof (uval_range r cm) as Rc. pose proof (uval_range r d) as Rd.
  assert (A12 : uval r (SAlu ALU_ADD cm (SLit w)) = uval r cm + w) by (apply uval_add_litZ; lia).
  split; [apply uval_add_small; lia|]. split; [apply soff_smallu; lia|]. rewrite <- A12. apply soff_smallu. rewrite A12. lia.
Qed.

Lemma slot_holds : ltac2:(tb__ "0|1|
S7S1dS9A1S6SbaS9SfR3A1R2A3S0S1eSafS9S11SeS45R2A2A1R3A3S1fA3S0S1eSafS9S11SeR3SbS10aA1M0A2A1R4A3S1fA3S0S1eSafS9S11SeS6eR4A2A1R5A3S1fA3S0S1eSafS9S11SeS88Z4R5A2G0A2A1R6A3S1fA3SbaS9SfR8A1S77R6A1A3F_;F_;F_;F_;F_;Fk;FF;Frho;").
Proof.
  intros rho F k HF H1 H2 H3 H5.
  pose proof (holds_mem _ _ _ HF H1) as F1. pose proof (holds_mem _ _ _ HF H2) as F2. pose proof (holds_mem _ _ _ HF H3) as F3. pose proof (holds_mem _ _ _ HF H5) as F5.
  rewrite h_ule in F1, F2, F3, F5. unfold B32 in *. rewrite uval_lit in F2 by lia. rewrite uval_lit in F5 by lia.
  pose proof (uval_range rho avt_cnt) as RC. pose proof (uval_range rho k) as Rk.
  unfold avt_cnt2 in F1. rewrite uval_add_litZ in F1 by lia.
  assert (E4k : uval rho (kb 4 k) = 4 * uval rho k) by (unfold kb; apply uval_mul_lit; lia). rewrite E4k in F5.
  assert (E4c : uval rho cm4 = 4 * uval rho avt_cnt) by (unfold cm4; rewrite uval_mul_comm; apply uval_mul_lit; lia).
  unfold slot_facts.
  constructor; [|constructor; [|constructor; [|constructor]]]; rewrite h_ule.
  - rewrite uval_add_litZ by (rewrite ?E4c; lia). rewrite E4c, E4k. lia.
  - rewrite E4c, E4k. lia.
  - unfold B32. rewrite E4c, uval_lit by lia. lia.
Qed.

Section X.
Variable TR : assn -> assn -> Prop.
Variable FAM : ltac2:(tb__ "0|0|
S2cS1dS38Q40A1A1SdfF_;F_;").
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S7cS2eS7S1dS38Q40A1A1SdfSbaS9SfR3A1S8S2fR4A1A1A3VTR;S7bS37R6R5R4R3A5R2A2M0F_;G0F_;FQ;Ftp;Frho;FS;FJ;").
Hypothesis TR_ex : forall (T : Type) (J : T -> jpredA) S rho tp (Q : assn),
  (forall x, TR (SPA segs (J x) S rho tp) Q) -> TR (SPA segs (fun r p t m => exists x, J x r p t m) S rho tp) Q.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
SdfSdfSdfSe0R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_exw : forall (T : Type) (P : T -> assn) (Q : assn), (forall a, TR (P a) Q) -> TR (fun w => exists a, P a w) Q.
Hypothesis TR_pureP : ltac2:(tb__ "0|1|
SdfOSdfSe0R4R1A1R4F_;Fw;R3VTR;R5R3A2M0F_;G0F_;F_;FQ;FX;FP;").
Hypothesis TR_callP : ltac2:(tb__ "0|5|
S7cS7cS2eS2eSe4S1dSaA1M0S1dS20S2eSb2A2M1A1S1dS20S6S6A2M2A1SdfS7S1dS38Q40A1A1M3G2SaeG2R1R5A3SaeG2R2S30RbA1A3F_;Fr;S0S26G0A1Sb4RaR9R8A3S24G0R7A2A3S0S1eSb5RbRaR9R8SbbG1S2eS28S2eSb2A2R7A4A5S1fA3S7G3VTR;S7bS37RfRdR2R1A5Sb3S37ScS2fRdA1A1R2R1RaA5A2Ftp1;Frho1;S1dSbfA1M4Sf2SbeS7dS37R9R8R10S21G4S111R3S112R2R1A2A4A5R13RaR9R4R2A4R13Se6Se5RbRfSf3R3RaR4A3A3R10A2RaR5R3A4F_;F_;Fmd;Fms;Ftr;S2eSb2G4Sf2SbeS7G3G4Sf2SbeSaeG1S21S2eSb2RaR9A4R14A3S7dS37R12R11R19S21G4S111R9S112R8R7A2A4A5R1cR13R12RaR8A4Sc0ScS2fR1aA1A1Se6Se5R14R18Sf3R9R13RaA3A3R19A2R8A3S7dS37R9R8ReS21G4S111R7S112R6R5A2A4A5ReSe6Se5R16R1aSf3RbR15RcA3A3R1bA2R15RaR9R8R6A6S1S137R17Sf3RcR16RdA3R1bR1cR1dR10R1eR19RbA9S7Sc1R18Sf3RdR17ReA3R1cR1dS2fR1eA1S2fR1fA1S2fR11A1R1RcA9VTR;S7bS37Sb8R11Se6Se5R19R1dSf3ReR18RfA3A3R1eA2R18RdRcA5S138R1eR1fR12R20R1dR1bA6R2RcA5R1aA2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S7bS37R11RfR8R7A5R9A2F_;F_;F_;F_;F_;F_;Ftp;Frho;FQ;FXk;FPosts;FR;Fs;FPre;FC;FJp;FJ;").

Hypothesis CVRES : ltac2:(tb__ "0|1|
S1dS20S2cS2cA2M0A1S1dS20G0S2cA2A1SacS7S1dS38Q40A1A1Sa8Z3R3A2VTR;S7bS37S96VAInv;VCST;VXGL;VKc;S11aR6R5A2R6R5R4S91S10cAaS10bR3R2A5Sb3S37Sf4R3R2SfcVAInv;VCST;VXGL;VKc;S11aS91S65R6R5R4AaA5A2F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Hypothesis CVOP : ltac2:(tb__ "0|1|
S1dS20S2cS2cA2M0A1S1dS20G0S2cA2A1SacS7S1dS38Q40A1A1Sa8Z4R3A2VTR;S7bS37S96VAInv;VCST;VXGL;VKc;S118R6R5A2R6R5R4S91SddAaSd8R3R2A5Sb3S37Sf4R3R2SfcVAInv;VCST;VXGL;VKc;S118S91S44R6R5R4AaA5A2F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Hypothesis CSM : ltac2:(tb__ "0|2|
Sc3S7S1dS38Q40A1A1VTR;S7bS37S12aVAInv;Z1M0R3VKc;A4S68R2R1A5Sb3S37Sf4R2R1S22S20S2eSb2A2M1S21S2eSb2S64S128VAInv;VCST;VXGL;G0R3VKc;A6A4S23G1A1A3A5A2Ftp1;Frho1;FAi;").
Hypothesis CMEMCPY : ltac2:(tb__ "0|2|
Sc3S7S1dS38Q40A1A1VTR;S7bS37S129VAInv;R3VKc;A3S40R2R1A5Sb3S37Sf4R2R1S22S20S2eSb2A2M0S21S2eSb2S3fS127VAInv;VCST;VXGL;R3VKc;A5A4M1S22G0G1S23G0A1A3A3A5A2Ftp1;Frho1;FAi;").
Definition pure_rule (Pre : axst) (Posts : list leafA) : Prop := ltac2:(tb__ "0|2|
S2eSe4S1dSaA1M0S7S1dS38Q40A1A1S8eSdfS0S26G0A1Sb4R7VPre;R6A3S24G0R5A2A3S0S1eSb7R8VPre;R7R6SbbS34S2eS35VPosts;A4A5S1fA3S0S1eS10fS85ScS2fR9A1A1A2S1fA3S0S1eS94ScS2fRaA1A1R5A2S1fA3S0S1eSb0S9S1bScS2fRbA1M1A1A1S8G1A1A3S1fA3S34S7SaeS34R2VPosts;A3S1cScS2fRfA1A1RcR2A3VTR;S7bS37VJAv;RbA1S134S8S2fR10A1A1Sb9RfVPre;S35R4A1R10ReA5A2R3RcA5RaA2F_;F_;Frho';FL;VTR;S7bS37VJAv;R8A1RdRaR9A5R7A2F_;F_;F_;F_;F_;F_;FQ;Fnd;Ftp;Frho;FR;Fs;FCl;").
Hypothesis CALL_sd : pure_rule Pre_sd Posts_sd.
Hypothesis REENTER : ltac2:(tb__ "0|4|
S2eS8eS20S2cS6A2M0S7S1dS38Q40A1A1M1S2cG1SaeS20S20S2eS8eA2M2G0A2S21G2G0S21S2eS8eR7R6A4R5A4S3cA3S1S7fZ0S97S21G2G0S21S2eS8eR8R7A4R6A4R5A2M3A2S82G3R3A2A2VTR;S7bS37VJAv;R8A1R9R6R5A5VFAM;R4R3A2A2F_;F_;Ftp0;Fb;Ftp;Frho;Frv;Fnd;FT;").
Hypothesis POST : ltac2:(tb__ "0|1|
S2eS8eS7S1dS38Q40A1A1M0S2cG0SaeS20S2eSb2A2S21S2eSb2R6Sf1R5A1A4Sf0A3VTR;S7bS37VJAv;R6A1R7R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;Fnd;FP;").

Ltac vmr := first [ lazymatch goal with |- @eq ?T ?t ?v => tryif first [ has_evar t | has_evar v ] then fail else vm_cast_no_check (@eq_refl T v) end
                  | vm_compute; reflexivity ].
Tactic Notation "innth" integer(n) := cbn [In cutsV exitsV Posts_vtJ PD_vr PD_op]; do n right; left; reflexivity.
Lemma emeas_z0 : ltac2:(tb__ "0|0|
S2eS8eS2cS7S0S2cS97S21S20S2eS8eA2S20S2cS6A2S21S2eS8eR4R3A4S21S2cS6R2S3eA4A4R1A2S81R2S80Z2Z40A2A2A3Frho;Fr;Fnd;FT;").
Proof. intros. unfold emeasA. cbn [eda_rank eda_var fst snd z0 eval]. rewrite lit_unsigned by lia. lia. Qed.

Lemma X_reopen : ltac2:(tb__ "0|a|
S2eS2eS1dS20S6S6A2M0A1S1dSa7A1S2cS2cS7S1dS38Q40A1A1M1S2cG1S20S2cS6A2M2S0S6S32RbA1SbS104A1A3S7fZ0M3R8A2S1S7fR9R8A2S7fR8Z10A2A2S0S1eS31S22S9S14S33S86A1S87A2S22S9SeS12S86A1SbS84S80Z2Z3dA2Z1A2A1A2S23S9A1A3A3S8S2fReA1A1A2S1fA3S0S1eS13S2fSd0RfS30RfA1S86RbRaA5A1A1S1fA3S0S1eSa0S8S2fR10A1A1A1S1fA3S0S1eSeeS8S2fR11A1M4A1RfS39SdG4A1A4S1fA3S0S1eSb0G0G0S29SfbR1Sd2Pa0S21S2cS2cZ20M5Z8M6A4A2A2ScfVXGL;S8S2fR13A1M7A1R11S39S24S25U0A2SdG7A1Sa1S22G0R1S23G0A1A3A8A2Lr;S30R12A1A3S1fA3S0S1eSd6RfReG5G6A4S1fA3S0S2eSd0R14S30R14A1S86R10RfA5R13A3SaeS20S20S2eS8eA2M8G2A2S21G8G2S21S2eS8eR14S90R13S39R12S8fA4A4RbA4S3cA3S1S7fG3S97S21G8G2S21S2eS8eR15S90R14S39R13S8fA4A4RcA4R10A2M9A2S82G9ReA2A2VTR;S7bS37VJAv;S90R15S39R14S8fA4A1R17R11R10A5VFAM;RfReA2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Frv;Ftp0;Fb;Ftp;Frho;Fk2;Fk1;Fbd;Ftv;FC;FA;").
Proof.
  intros A C tv bd k1 k2 rho tp b tp0 rv Hbase Hk1 Hk2 Hfe Hwf HB HRO HXL HWC HC HinC Hm.
  eapply TR_pre; [|apply (REENTER C (NDA tv fr_vt bd ANone) rv); [exact HinC | exact Hm]].
  intros w Hw. rewrite <- HC.
  apply (JA_shadow_reopen segs HTOP AInv CST XGL ALA HCST HXGL LFSH NPH Kc rho0 (P0_vt CST FB FF) FB FF BX PTrue HKc HBX HNP
           tv fr_vt bd ANone 0%nat 160%positive 1 170%positive hG k1 k2 A (ax_X A) rho tp w eq_refl ltac:(lia) Hbase Hk1
           ltac:(change (fs_frame_size 1) with 128; lia) Hfe (fun r H => H) Hwf); [|exact Hw].
  intros Ai rho1 tp1 md1 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR. split.
  - exact (siteF2 Ai rho _ tv fr_vt _ rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HN HD HZ HFR HRO).
  - intros r y Hr Hy. pose proof (proj1 (forallb_forall _ _) HXL r Hr) as Hc. cbn beta in Hc. apply orb_prop in Hc as [Hc|Hc].
    + apply xr_eqb_sound in Hc. subst r. right. exists 32, 8. split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [change (fs_frame_size 1) with 128; lia | exact HWC].
    + left. exact (proj1 (siteX Ai rho _ tv fr_vt (Some 0%nat) _ _ rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HBf HFF HN HD HZ HFR Hc) r y (or_introl eq_refl) Hy).
Qed.
Lemma epi_glue : ltac2:(tb__ "0|2|
S2eS1dS20S6S6A2A1S1dSa7A1S7S1dS38Q40A1A1Se0S0S6S32R6A1SbS104A1A3S0S1eS31S22S9S14S33S86A1S87A2S22S9SeS12S86A1SbS84S80Z2Z3dA2Z1A2A1A2S23S9A1A3A3S8S2fR7A1A1A2S1fA3S0S1eS13S2fSd0R8S30R8A1S86Z0Z10A5A1A1S1fA3S0S1eS13S2fS42R9A1A1A1S1fA3S0S1eSa0S8S2fRaA1A1A1S1fA3S0S1eSa2S8S2fRbA1A1A1S1fA3S0S1eSeeS8S2fRcA1M0A1RbS39SdG0A1A4S1fA3S0S1eScfVXGL;S8S2fRdA1M1A1RcS39S24S25U0A2SdG1A1Sa1S30RdA1A8S1fA3S7bS37VJAv;S90RdS39RcS8fA4A1ReRbRaR9A6S7bS37VJAv;S90ReS39RdS8fA4A1S42RfA1RcRbRaA6F_;F_;F_;F_;F_;F_;F_;F_;F_;Fw;Ftp;Frho;Fbd;Ftv;FY;").
Proof.
  intros Y tv bd rho tp w Hbase Hfe Hwf1 Hwf2 HB HFRF HRO HXL Hw. unfold epi_state.
  apply (JA_flag_carve segs HTOP AInv CST XGL ALA HCST HXGL LFLAG NPH Kc rho0 (P0_vt CST FB FF) FB FF BX PTrue HKc HBX HNP
           tv fr_vt bd ANone 0%nat 160%positive 1 170%positive (shadow_reopen_stateA Y (ax_X Y) hG 0 16) rho tp w eq_refl ltac:(lia)).
  - exact Hbase.
  - exact Hwf2.
  - intros Ai rho1 tp1 md1 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR. cbn [shadow_reopen_stateA ax_S ss_facts ss_objs ax_X] in HF |- *. split.
    + intros o a Ho Hr. apply in_app_or in Ho as [Ho|[<-|[]]].
      * destruct (siteF2 Ai rho _ tv fr_vt _ rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HN HD HZ HFR HRO o a Ho Hr) as [Hc|Hc]; [left; exact Hc | right; left; exact Hc].
      * right. right. exact (shobj_range_hse hG 160 128 0 16 rho _ a sz_rng ltac:(lia) ltac:(cbn; lia) HF HFRF Hr).
    + exact (proj2 (proj2 (siteX Ai rho _ tv fr_vt (Some 0%nat) _ _ rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HBf HFF HN HD HZ HFR HXL))).
  - apply (JA_shadow_reopen segs HTOP AInv CST XGL ALA HCST HXGL LFSH NPH Kc rho0 (P0_vt CST FB FF) FB FF BX PTrue HKc HBX HNP
             tv fr_vt bd ANone 0%nat 160%positive 1 170%positive hG 0 16 Y (ax_X Y) rho tp w eq_refl ltac:(lia) Hbase ltac:(lia)
             ltac:(change (fs_frame_size 1) with 128; lia) Hfe (fun r H => H) Hwf1); [|exact Hw].
    intros Ai rho1 tp1 md1 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR. split.
    + exact (siteF2 Ai rho _ tv fr_vt _ rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HN HD HZ HFR HRO).
    + intros r y Hr Hy. left. exact (proj1 (siteX Ai rho _ tv fr_vt (Some 0%nat) _ _ rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HBf HFF HN HD HZ HFR HXL) r y Hr Hy).
Qed.

Lemma X_arr : ltac2:(tb__ "0|9|
S2eS2eS2eS2eS1dSf7A1S1dS20S6S6A2A1M0G0S1dSa7A1S7S1dS38Q40A1A1M1S2cG1S2cS0S26S2eA1Sf6RdR9A2S24S2eRcA2A3S0S1eSffR9S30RdA1A2S1fA3S0S2eS136ReRaA2RdA3S0G0S30ReA1RbA3S0S6S32RfA1SbS104A1A3S0S1eS31S22S9S14S33S86A1S87A2S22S9SeS12S86A1SbS84S80Z2M2Z3dA2Z1M3A2A1A2S23S9A1A3A3S8S2fR10A1A1A2S1fA3S0S1eS13S2fSd0R11S30R11A1S86Z0M4Z10A5A1A1S1fA3S0S1eS13S2fS42R12A1A1A1S1fA3S0S1eSa0S8S2fR13A1A1A1S1fA3S0S1eSa2S8S2fR14A1A1A1S1fA3S0S1eSeeS8S2fR15A1M5A1R11S39SdG5A1A4S1fA3S0S1eScfVXGL;S8S2fR16A1M6A1R12S39S24S25U0A2SdG6A1Sa1S30R16A1A8S1fA3S0S2eS42R17A1R16A3SaeS20S20S2eS8eA2M7S20S2cS6A2M8A2S21G7G8S21S2eS8eR17S90R14S39R13S8fA4A4S21S2cS6ReS3eA4A4S3cA3S7fG4RfA2S7fS81S83R10G3A2S80G2Z40A2A2R12A2VTR;S7bS37VJAv;S90R17S39R16S8fA4A1R1dR15R14A5VFAM;R13R12A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Frk;Ftp0;Fb;Ftp;Frho;Fbd;Ftv;FXc;Fxf;FC;FY;FZ;FX;").
Proof.
  intros X Z Y C xf Xc tv bd rho tp b tp0 rk HZ HXZ HY HXY Hbase Hfe Hwf1 Hwf2 HB HFRF HRO HXL HC HinC Hrk Hb.
  eapply TR_pre; [|apply (REENTER C (NDA tv fr_vt bd ANone) (rk, z0)); [exact HinC | rewrite emeas_z0; lia]].
  intros w Hw. rewrite <- HC. apply (epi_glue Y tv bd rho tp w Hbase Hfe Hwf1 Hwf2 HB HFRF HRO HXL). rewrite <- HY.
  apply (SPA_x_sub segs); [exact (xrs_inclb_sound _ _ HXZ)|]. exact (SPA_axforms segs _ xf rho X Z tp w HZ Hw).
Qed.
Lemma X_X_rl : ltac2:(tb__ "0|7|
S2eS2eS2eS1dS20S6S6A2A1S1dSa7A1S7S1dS38Q40A1A1M0S2cG0S2cS0S26S2eA1Sf6RaS22Sf7Sf8S76A1S23Sf7A1A3A2S24S2eR9A2A3S0S2eS36RaS133S2fRaA1M1SbcSaUeM2SdG1A1A3A2A2R9A3S0S1eSd3Pa0PaaS86Z1M3SbdSaG2SdS2fRbA1A1A3A5S1fA3S0S1eS31S22S9S14S33S86A1S87A2S22S9SeS12S86A1SbS84S80Z2M4Z3dA2G3A2A1A2S23S9A1A3A3S8S2fRcA1A1A2S1fA3S0S1eS94ScS2fRdA1A1S90RbS39RaS8fA4A2S1fA3SaeS20S20S2eS8eA2M5S20S2cS6A2M6A2S21G5G6S21S2eS8eRdS90RcS23S20S20S6S2cA2S6A2A1RbS8fA4A4S21S2cS6R6S3eA4A4S3cA3S7fZ0R7A2S7fS81S83R8G3A2S80G4Z40A2A2RaA2VTR;S7bS37VJAv;S90RfS39ReS8fA4A1R12RdRcA5VFAM;RbRaA2A2F_;F_;F_;F_;F_;F_;F_;F_;Frk;Ftp0;Fb;Ftp;Frho;Fbd;Ftv;FC;FX1;FX;").
Proof.
  intros X X1 C tv bd rho tp b tp0 rk HX1 HC HR Hfe Hnb HinC Hrk Hb.
  apply (TR_pre (fun w => exists rho', SPA segs (JAv (NDA tv [] bd ANone)) C rho' tp w)).
  { intros [tr [ms md]] Hw. pose proof (SPA_axforms segs _ [AXSelect sel_rel] rho X X1 tp _ HX1 Hw) as Hw1.
    exists (rho_absorb rho (skipn 14 (ss_objs (ax_S X1))) (vms md tp ms)). rewrite <- HC.
    change (ax_setS X1 (set_objs (ax_S X1) (firstn 14 (ss_objs (ax_S X1))))) with (drop_lastA X1 (firstn 14 (ss_objs (ax_S X1)))).
    change (@nil (sv * Z * sv)) with (remove_nth 0 fr_vt).
    apply (JA_release_inline segs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nn.Lib_arena_alloc.HTOP_ok AInv CST XGL ALA HCST HXGL LFLAG LFSH NPH Kc rho0 (P0_vt CST FB FF) FB FF BX PTrue HKc HBX HNP
             tv fr_vt bd ANone 0%nat 160%positive 1 170%positive hG X1 (firstn 14 (ss_objs (ax_S X1))) (skipn 14 (ss_objs (ax_S X1))) rho tp tr ms md);
      [reflexivity | lia | symmetry; apply firstn_skipn | exact HR | exact Hfe | exact Hnb | intros A1 A2 _; exact I | exact Hw1]. }
  apply TR_exw. intros rho'. apply (REENTER C (NDA tv [] bd ANone) (rk, z0)); [exact HinC | rewrite emeas_z0; lia].
Qed.
Lemma XH_X_rlo : ltac2:(tb__ "0|1|
S7S1dS38Q40A1A1M0S2cG0S7fS81Z28S80Z2Z40A2A2R2A2VTR;S7bS37VJAv;S71A1S6cR5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. unfold ndEo, ndF. apply (X_X_rl X_rlo _ C_rlo _ _ rho tp b tp0 30 X_rlo_eq); [vmr|vmr|vmr|vmr| innth 25 | lia | lia].
Qed.
Lemma XH_X_rlf : ltac2:(tb__ "0|1|
S7S1dS38Q40A1A1M0S2cG0S7fS81Z28S80Z2Z40A2A2R2A2VTR;S7bS37VJAv;S70A1S6bR5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. unfold ndEf, ndF. apply (X_X_rl X_rlf _ C_rlf _ _ rho tp b tp0 30 X_rlf_eq); [vmr|vmr|vmr|vmr| innth 24 | lia | lia].
Qed.

Lemma XH_X_A : ltac2:(tb__ "0|1|
S7S1dS38Q40A1A1M0S2cG0S7fS81Z5eS80Z2Z40A2A2R2A2VTR;S7bS37VJAv;S49A1S6aR5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  apply (TR_pre (fun w => exists rho', (fun w' => (forall e, eval rho' e = eval rho e) /\ SPA segs (JAv ndP) E_A1 rho' tp w') w)).
  { intros [tr [ms md]] Hw. exists (rho_absorb rho [shobj hG 0 16 cells_A DZero] (vms md tp ms)). split; [intros e; apply eval_absorb|].
    rewrite <- E_A1_eq. unfold ndP, ndF.
    apply (JA_shadow_release segs HTOP AInv CST XGL ALA HCST HXGL LFSH NPH Kc rho0 (P0_vt CST FB FF) FB FF BX PTrue HKc HBX HNP
             tvP fr_vt bdPre ANone 0%nat 160%positive 1 170%positive hG 0 16 cells_A DZero X_A objs_A [(32, 8)] rho tp tr ms md
             eq_refl ltac:(lia) eq_refl X_A_objs ltac:(lia) ltac:(change (fs_frame_size 1) with 128; lia) eq_refl ltac:(vmr) ltac:(vmr) ltac:(vmr)); [|exact Hw].
    intros Ai rho1 tp1 md1 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR.
    exact (siteF Ai rho _ tvP fr_vt objs_A rho1 tp1 md1 HM HF ltac:(vmr) Hav HP0 HT HTK HN HD HZ HFR ltac:(vmr)). }
  apply TR_exw. intros rho'. apply (TR_pureP _ (forall e, eval rho' e = eval rho e)); [intros w [HE _]; exact HE|]. intros HE.
  eapply TR_pre with (P := SPA segs (JAv ndP) E_A rho' tp).
  { intros w [_ Hw]. apply (SPA_axforms segs _ xf_sd rho' E_A2 E_A tp w E_A_eq). rewrite <- E_A2_eq. unfold reshapeA.
    apply (SPA_reshape segs _ rho' E_A1 1 O_frA O_fr0 tp w E_A1_o1); [reflexivity | reflexivity | reflexivity | vmr | intros _; split; reflexivity | exact Hw]. }
  apply (CALL_sd E_A s_A R_A rho' tp ndP _); [vmr|vmr|vmr|vmr|vmr|].
  intros L rho2 HL Hag. cbn [In Posts_sd] in HL. destruct HL as [<-|[<-|[]]]; cbn [la_state].
  - fold (T_pure Pre_sd E_A s_A R_A P_none). rewrite T_A0_eq. apply (REENTER T_A0 ndP (90, z0)); [innth 2 | rewrite emeas_z0; lia].
  - fold (T_pure Pre_sd E_A s_A R_A P_num). rewrite T_A1_eq. apply (REENTER T_A1 ndP (90, z0)); [innth 3 | rewrite emeas_z0; lia].
Qed.
Lemma XH_E_B : ltac2:(tb__ "0|1|
S7S1dS38Q40A1A1M0S2cG0S7fS81Z58S80Z2Z40A2A2R2A2VTR;S7bS37VJAv;S49A1S5cR5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  apply (CALL_sd E_B s_B R_B rho tp ndP _); [vmr|vmr|vmr|vmr|vmr|].
  intros L rho2 HL Hag. cbn [In Posts_sd] in HL. destruct HL as [<-|[<-|[]]]; cbn [la_state].
  - fold (T_pure Pre_sd E_B s_B R_B P_none). rewrite T_B0_eq. apply (REENTER T_B0 ndP (86, z0)); [innth 4 | rewrite emeas_z0; lia].
  - fold (T_pure Pre_sd E_B s_B R_B P_num). rewrite T_B1_eq. apply (REENTER T_B1 ndP (86, z0)); [innth 5 | rewrite emeas_z0; lia].
Qed.

Lemma X_D : ltac2:(tb__ "0|14|
S2eS2eS2eS2eS2eS2eS6S6S1dS20S6S6A2M0A1S1dSa7A1Se4S1dSaA1M1S7S1dS38Q40A1A1M2S2cG2S0S26S2eA1Sf6R10S78A2S24S2eRbA2A3S0S26G1A1Sb4RcS106R7A3S24G1R6A2A3S0S1eSb7RdS106R8R7SbbS34S2eS35S109A4A5S1fA3S0S1eS10fS85ScS2fReA1A1A2S1fA3S0S1eS94ScS2fRfA1A1S90RcS39RbS8fA4A2S1fA3S0S1eSb0S9S1bScS2fR10A1M3A1A1S8G3A1A3S1fA3S0S2eS4fS106R11RcRbS107A5R15A3S0S2eS4fS106R12RdRcS108A5R15A3S0S6S32R17A1SbS104A1M4A3S0S1eS31S22S9S14S33S86A1S87A2S22S9SeS12S86A1SbS84S80Z2M5Z3dA2Z1A2A1A2S23S9A1A3A3M6S8S2fR18A1A1A2S1fA3S0S1eS13S2fSd0R19S30R19A1S86Z8M7ZbM8A5A1A1S1fA3S0S1eSa0S8S2fR1aA1A1A1S1fA3S0S1eSeeS8S2fR1bA1M9A1R14S39SdG9A1A4S1fA3S0S1eSb0G0G0S29SfbR1Sd2Pa0S21S2cS2cZ20G7A4A2A2MaScfVXGL;S8S2fR1dA1MbA1R16S39S24S25U0A2McSdGbA1Sa1S22G0R1S23G0A1A3MdA8A2Lr;S30R1cA1A3S1fA3S0S2eSd0R1dS30R1dA1S86G7G8A5R1bA3S0S6S32R1dA1G4A3S0S1eS31G6S8S2fR1eA1A1A2S1fA3S0S1eS13S2fSd0R1fS30R1fA1S86G7G8A5A1A1S1fA3S0S1eSa0S8S2fR20A1A1A1S1fA3S0S1eSeeS8S2fR21A1MeA1R1bS39SdGeA1A4S1fA3S0S1eSb0G0G0S29GaScfVXGL;S8S2fR23A1MfA1R1dS39GcSdGfA1Sa1GdA8A2Lr;S30R22A1A3S1fA3S0S2eSd0R23S30R23A1S86G7G8A5R21A3SaeS20S20S2eS8eA2M10S20S2cS6A2M11A2M12S21G10G11S21S2eS8eR23S90R1eS39R1dS8fA4A4S21S2cS6Z42S3eA4M13A4S3cA3SaeG12S21G10G11S21S2eS8eR23S90R1fS39R1eS8fA4A4G13A4S3cA3S7fS81Z43S80G5Z40A2A2R1aA2VTR;S7bS37VJAv;S90R21S39R20S8fA4A1R29R1dR1cA5VFAM;R1bR1aA2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Ftp0;Fb;Ftp;Frho;FR;Fs;Fbd;Ftv;Fk;Fd;FEc;FT1;FT0;FU1;FU0;FX;").
Proof.
  intros X U0 U1 T0 T1 Ec d k tv bd s R rho tp b tp0 HEc He Hchk Hnf Hnb Hfb HU0 HU1
         Hb0 Hfe0 Hwf0 HB0 HRO0 HXL0 HT0 Hb1 Hfe1 Hwf2 HB1 HRO1 HXL1 HT1 Hin0 Hin1 Hb.
  apply TR_facts. intros HF.
  eapply TR_pre with (P := SPA segs (JAv (NDA tv fr_vt bd ANone)) Ec rho tp).
  { intros w Hw. exact (SPA_axforms segs _ xf_D rho X Ec tp w HEc Hw). }
  apply (CALL_sd Ec s R rho tp (NDA tv fr_vt bd ANone) _ He Hchk Hnf Hnb Hfb).
  intros L rho2 HL Hag. cbn [In Posts_sd] in HL. destruct HL as [<-|[<-|[]]]; cbn [la_state].
  - fold (T_pure Pre_sd Ec s R P_none). rewrite HU0.
    apply (X_reopen U0 T0 tv bd 8 11 rho2 tp b tp0 (66, z0) Hb0 ltac:(lia) ltac:(lia) Hfe0 Hwf0 HB0 HRO0 HXL0 eq_refl HT0 Hin0). rewrite emeas_z0. lia.
  - fold (T_pure Pre_sd Ec s R P_num). rewrite HU1.
    apply (X_reopen U1 T1 tv bd 8 11 rho2 tp b tp0 (66, z0) Hb1 ltac:(lia) ltac:(lia) Hfe1 Hwf2 HB1 HRO1 HXL1 eq_refl HT1 Hin1). rewrite emeas_z0. lia.
Qed.
Lemma XH_E_Dk : ltac2:(tb__ "0|1|
S7S1dS38Q40A1A1M0S2cG0S7fS81Z44S80Z2Z40A2A2R2A2VTR;S7bS37VJAv;S54A1S5eR5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. unfold ndK, ndF.
  apply (X_D E_Dk U_Dk0 U_Dk1 T_Dk0 T_Dk1 E_Dkc avt_d avt_k _ _ s_Dk R_Dk rho tp b tp0);
    [ exact E_Dkc_eq |vmr|vmr|vmr|vmr|vmr| exact U_Dk0_eq | exact U_Dk1_eq |vmr|vmr|vmr|vmr|vmr|vmr| exact T_Dk0_eq |vmr|vmr|vmr|vmr|vmr|vmr| exact T_Dk1_eq | innth 12 | innth 13 | lia].
Qed.
Lemma XH_E_Dg : ltac2:(tb__ "0|1|
S7S1dS38Q40A1A1M0S2cG0S7fS81Z44S80Z2Z40A2A2R2A2VTR;S7bS37VJAv;S53A1S5dR5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. unfold ndG, ndF.
  apply (X_D E_Dg U_Dg0 U_Dg1 T_Dg0 T_Dg1 E_Dgc vDg vKg _ _ s_Dg R_Dg rho tp b tp0);
    [ exact E_Dgc_eq |vmr|vmr|vmr|vmr|vmr| exact U_Dg0_eq | exact U_Dg1_eq |vmr|vmr|vmr|vmr|vmr|vmr| exact T_Dg0_eq |vmr|vmr|vmr|vmr|vmr|vmr| exact T_Dg1_eq | innth 14 | innth 15 | lia].
Qed.

Lemma HIN_v : ltac2:(tb__ "0|2|
S7Sf2Sc3S7S1dS38Q40A1A1SbeSbaS9SfR6A1S8S2fS62A1A1A3S9fVCST;VFB;VFF;Vrho0;A4Sc0S85Vrho0;R8A3VAInv;R7R6R5R4A4S92Vrho0;R8A2Se9RbSc5Sc4R9A1A1A2S98VFB;RaA2S99VFF;RbA2S95VFB;RcReS4cA4Se7RfS4cA2Se8R10S4cA2S93VFF;RfR11S39A4S1SfeVCST;Vrho0;VFB;VFF;R12S22S20S6S6A2M0S21S6S6S3aS88Z4S3bA2A4S23G0A1A3M1S39S4eA8S1S100VCST;VXGL;Vrho0;VFB;VFF;R12G1S39S6dA9S11aSeaVFB;R12G1A3Sf9VFF;R12S39A3Se6Se5R12S4eR11A3S75A2A3A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FAi;Fms;Frho;").
Proof.
  intros rho ms Ai rho1 tp1 md1 HF HP0 Hav HM HTP HTK HBf HFF HN HD HZ HFR. destruct (P0_now rho Hav HP0) as (HT & Hb & Hal & _).
  assert (HB : bF (ss_facts (ax_S E_vr)) = true) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
  pose proof (basez_of DW rho _ DW_rng HF HB) as BZ. pose proof BZ as [Bsp Bb Bal BL BB Btop]. rewrite aceil_val in *.
  pose proof (Forall_single _ _ _ HN) as HN1. pose proof (Forall_single _ _ _ HZ) as HZ1. pose proof (tvd_single rho (aw_d, kb 4 aw_k)) as HD1.
  split; [|split].
  - intros o a Ho Hr. eapply (robjs_checkP_sound segs AInv CST ALA rho0 FB FF Ai rho _ [(aw_d, kb 4 aw_k)] fr_vt None extraOH R_v rho1 tp1 md1 HM HF (T_ok_T0 rho0 _ Ai HTP HTK) HN1 HD1 HZ1 HFR ltac:(vmr));
      [intros o' a' Ho' HE Hr'; exact (extra_client rho o' a' _ _ BZ Hav HP0 HE Hr') | exact Ho | exact Hr].
  - exact (proj1 (siteX Ai rho _ [(aw_d, kb 4 aw_k)] fr_vt None (ss_objs (ax_S E_vr)) Xk_v rho1 tp1 md1 HM HF HB Hav HP0 HTP HTK HBf HFF HN1 HD1 HZ1 HFR ltac:(vmr))).
  - unfold P0_vr. rewrite !rw_call'.
    change (wsub_get s_v 17) with avt_k. change (wsub_get s_v 15) with avt_d. change (wsub_get s_v 14) with vAL. change (wsub_get s_v 12) with (SAlu ALU_ADD vb (SLit 216)).
    split; [|split].
    + pose proof (holds_mem _ _ (SPUle avt_k (SLit B32)) HF ltac:(vmr)) as FK. rewrite h_ule in FK. unfold B32 in FK. rewrite uval_lit in FK by lia.
      intros HK. apply Forall_inv_tail in HZ. apply (tvz_kd rho 4 avt_d avt_k [] HZ); [lia | unfold B32; lia | exact HK].
    + destruct Hb as (f & sz & fl & Hin & H1 & H2). exists f, sz, fl. split; [apply In_FFx; left; exact Hin|].
      assert (E216 : uval rho (SAlu ALU_ADD vb (SLit 216)) = uval rho vb + 216) by (apply uval_add_litZ; unfold IMG_HI in *; lia).
      unfold uval in E216, H1, H2. rewrite E216. lia.
    + destruct Hal as (f & sz & fl & Hin & H1 & H2). exists f, sz, fl. split; [apply In_FFx; left; exact Hin|]. unfold uval in H1, H2. lia.
Qed.

Lemma XH_E_vr : ltac2:(tb__ "0|1|
S7S1dS38Q40A1A1M0S2cG0S7fS81Z4eS80Z2Z40A2A2R2A2VTR;S7bS37VJAv;S49A1S63R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  eapply TR_pre with (P := SPA segs (JAv ndP) E_vr rho tp).
  { intros w Hw. exact (SPA_axforms segs _ xf_vr rho E_vr0 E_vr tp w E_vr_eq Hw). }
  apply TR_facts. intros HF. unfold ndP, ndF, tvP, tvI, bdPre, bd_vt.
  change [(aw_d, kb 4 aw_k); (avt_d, kb 4 avt_k)] with ([(aw_d, kb 4 aw_k)] ++ [(avt_d, kb 4 avt_k)]).
  apply (client_callT segs AInv CST XGL ALA HCST HXGL NPH Kc rho0 (P0_vt CST FB FF) FB FF BX PTrue HKc HBX P0_vr PTrue (fun _ H => H) (fun _ _ _ H => H)
           Pre_vr Lib_vec_reserve.nd0 PD_vr NF eq_refl eq_refl eq_refl TR TR_facts TR_ex TR_pre TR_callP CVRES eq_refl
           E_vr s_v R_v Xk_v rho tp [(aw_d, kb 4 aw_k)] [(avt_d, kb 4 avt_k)] fr_vt (bd_vec 4 avt_cnt2 avt_k ++ bd_vec 4 Wp1 aw_k) (bd_vec 4 Wp1 aw_k) ANone (FAM b tp0)).
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
  - intros Ai ms HF' HP0 Hav HBf HFF HN HD HZ HFR (rho1 & tp1 & md1 & HM) HT HTK. exact (HIN_v rho ms Ai rho1 tp1 md1 HF' HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR).
  - intros [Ld ndL] rho' tp' Hd Hag. cbn [PD_vr In] in Hd. destruct Hd as [Hd|[Hd|[Hd|[]]]]; injection Hd as <- <-;
      cbn [fst snd nd_tv nd_bd nd_am Lib_vec_reserve.nd0 ND am_subst app].
    +
      rewrite T_keep0_eq, imp_keep_tv, imp_keep_bd. change ([(aw_d, kb 4 aw_k)] ++ [(avt_d, kb 4 avt_k)]) with tvP. change (bd_vec 4 avt_cnt2 avt_k ++ bd_vec 4 Wp1 aw_k) with (bdK avt_k).
      eapply TR_pre; [|apply (REENTER T_keep ndK (74, z0)); [innth 7 | rewrite emeas_z0; lia]].
      intros w Hw. rewrite <- T_keep_eq. apply (SPA_refacts_JA segs); [exact Hw | vmr |].
      intros tr md HJ HF2. apply Forall_app. split; [|exact HF2]. apply Forall_app. split.
      * apply (slot_holds rho' _ avt_k HF2); vmr.
      * assert (TNZ : tnz rho' (avt_d, kb 4 avt_k)).
        { destruct HJ as (Ai & kc & Hav' & _ & _ & _ & _ & _ & (_ & _ & HZ') & _).
          pose proof (holds_mem _ _ (SPUle avt_cnt2 avt_k) HF2 ltac:(vmr)) as F1. pose proof (holds_mem _ _ (SPUle avt_k (SLit B32)) HF2 ltac:(vmr)) as F4.
          pose proof (holds_mem _ _ (SPUle avt_cnt avt_k) HF2 ltac:(vmr)) as F3.
          rewrite h_ule in F1, F3, F4. unfold B32 in F4. rewrite uval_lit in F4 by lia. pose proof (uval_range rho' avt_cnt) as RC.
          unfold avt_cnt2 in F1. rewrite uval_add_litZ in F1 by lia. unfold tnz. cbn [fst]. cbn [nd_tv] in HZ'. apply Forall_inv_tail in HZ'.
          apply (tvz_kd rho' 4 avt_d avt_k [] HZ'); unfold B32; lia. }
        pose proof (JA_tv_facts segs AInv CST XGL NPH Kc rho0 (P0_vt CST FB FF) FB FF BX PTrue ALA _ _ _ _ _ (avt_d, kb 4 avt_k) eq_refl HJ (or_intror (or_introl eq_refl)) TNZ) as TF.
        constructor; [|constructor]. apply (proj1 (Forall_forall _ _) TF). unfold tv_factsA. cbn [fst snd]. do 5 right. left. reflexivity.
    +
      rewrite T_fail0_eq, imp_fail_tv. change (bd_subst _ [] ++ bd_vec 4 Wp1 aw_k) with bdFl.
      eapply TR_pre; [intros w Hw; exact (SPA_swap2 _ _ [] _ _ _ _ _ _ Hw)|]. change [(avt_d, kb 4 avt_k); (aw_d, kb 4 aw_k)] with (tv_vt avt_d avt_k aw_d aw_k).
      apply (X_arr T_fail0 Z_fl Y_fl T_fl xf_fl (X_vt avt_d avt_k aw_d aw_k) (tv_vt avt_d avt_k aw_d aw_k) bdFl rho' tp' b tp0 74 Z_fl_eq);
        [vmr| exact Y_fl_eq |vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr| exact T_fl_eq | innth 9 | lia | lia].
    +
      rewrite T_grown0_eq, imp_grown_tv, imp_grown_bd. change ([(aw_d, kb 4 aw_k)] ++ [(vDg, kb 4 vKg)]) with tvG. change (bd_vec 4 avt_cnt2 vKg ++ bd_vec 4 Wp1 aw_k) with (bdK vKg).
      eapply TR_pre; [|apply (REENTER T_grown ndG (74, z0)); [innth 8 | rewrite emeas_z0; lia]].
      intros w Hw. rewrite <- T_grown_eq. apply (SPA_refacts_JA segs); [exact Hw | vmr |].
      intros tr md _ HF2. apply Forall_app. split; [|exact HF2]. apply (slot_holds rho' _ vKg HF2); vmr.
Qed.

Lemma X_E_mc : ltac2:(tb__ "0|b|
S2eS2eS2eS2eS2eS6S1dS20S6S6A2A1S1dSa7A1Se4S1dSaA1M0S7S1dS38Q40A1A1M1S2cG1S2cS0S26S2eA1Sf6RfS79A2S24S2eReA2A3S0S26SaA1M2Sb1SaSdS2fRfA1A1U4M3A3S24SaS17RbS46S10Sc6S46SbZ8A1A3S23S16A1S15A5A2A3S0S1eS19ScS2fR10A1A1S50RcA1A2S1fA3S0S1eSafS9S11SeRdSbZ800000000000A1A2A1S8S2fR11A1A1A3S1fA3S0S1eSafS9S11SeS46SbS10aA1A2A1S8S2fR12A1A1A3S1fA3S0S2eS57R13G3S50RfA1A3R12A3S5S1dS16A1M4G4S0G2Sb1SaSdS2fR14A1M5A1UcM6A3S24SaS17S87SbZ20A1SbZ28A1R1S15A5A2A3Lcs;A2S0S1eS19ScG5A1S58A2S1fA3S0S1eSa2S8S2fR15A1A1A1S1fA3S0S2eS57R16G6S58A3R15A3S0S26G0A1Sb4R16S40R11A3S24G0R10A2A3S0S1eSb5R17S40R12R11S22S2eS3fS22S2eS3fS23S2eA1A3A3A5S1fA3S0S1eS11cS85R13A2S1fA3S0S1eS10fS85ScS2fR19A1A1A2S1fA3S0S1eS94ScS2fR1aA1A1S90R17S39R16S8fA4A2S1fA3S0S1eSa9ScS2fR1bA1A1R17A2S1fA3S0S1eSabR18A1S1fA3S0S1eSa0S8S2fR1dA1A1A1S1fA3S0S1eSf5S8S2fR1eA1A1R1bS39S27S25A1M7Sc7R18A6S1fA3S0S1eScfVXGL;S8S2fR1fA1M8A1R1cS39G7SdG8A1Sa1S30R1fA1A8S1fA3S0S2eS11eS40R20R1bR1aS3fA5R1fA3SaeS20S20S2eS8eA2M9S20S2cS6A2MaA2S21G9GaS21S2eS8eR20S90R1eS39R1dS8fA4A4S21S2cS6R16S3eA4A4S3cA3S7fZ0R17A2S7fS81S83R18Z1A2S80Z2Z40A2A2R1aA2VTR;S7bS37VJAv;S90R21S39R20S8fA4A1R27R1dR1cA5VFAM;R1bR1aA2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Frk;Ftp0;Fb;Ftp;Frho;FR;Fs;Fbd;Ftv;Fd;FT;FE;FE2;FE1;FE0;").
Proof.
  intros E0 E1 E2 E T d tv bd s R rho tp b tp0 rk HE1 H4 Hwf4 Hd Hs HE2 [cs H12] Hwf12 HFR2 HE He Hchk Htp Hnf Hnb Hbb Hwp HB HR HX HT HinT Hrk Hb.
  eapply TR_pre with (P := SPA segs (JAv (NDA tv fr_vt bd ANone)) E rho tp).
  { intros w0 Hw0. pose proof (SPA_axforms segs _ xf_mc rho E0 E1 tp w0 HE1 Hw0) as Hw1.
    assert (Hw2 : SPA segs (JAv (NDA tv fr_vt bd ANone)) E2 rho tp w0).
    { rewrite <- HE2. unfold reshapeA.
      apply (SPA_reshape segs _ rho E1 4 _ _ tp w0 H4); [reflexivity | reflexivity | reflexivity | exact Hwf4 | | exact Hw1].
      intros HF. destruct (slot_rng rho _ d cm4 8 ltac:(lia) HF Hd Hs) as (A1 & A2 & A3).
      unfold dst_obj, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite !soff_lit_small by lia. rewrite A2, A3.
      change (bv_unsigned (eval rho (SAlu ALU_ADD d cm4))) with (uval rho (SAlu ALU_ADD d cm4)). rewrite A1. unfold uval. lia. }
    rewrite <- HE. unfold reshapeA.
    apply (SPA_reshape segs _ rho E2 12 _ _ tp w0 H12); [reflexivity | reflexivity | reflexivity | exact Hwf12 | | exact Hw2].
    intros HF. unfold src_obj, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite !soff_lit_small by lia.
    change (bv_unsigned (eval rho (SAlu ALU_ADD hF (SLit 32)))) with (uval rho (SAlu ALU_ADD hF (SLit 32))). rewrite (foff_rng rho _ 32 HF HFR2 ltac:(lia)). unfold uval, hF. lia. }
  apply TR_facts. intros HF.
  apply (purec_callT_ag_xp segs AInv CST XGL ALA HCST HXGL NPH Kc rho0 (P0_vt CST FB FF) FB FF BX PTrue HKc TR TR_facts TR_ex TR_pre TR_callP
           XP_memcpy Pre_mc [L_mc1; L_mc1] E s R rho tp (NDA tv fr_vt bd ANone) bd (FAM b tp0)).
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
  - exact (site_pure E s R rho tv fr_vt bd HB HR HX).
  - intros Ai tr ms md Hsm HM HX'. exact (XP_memcpy_site segs AInv CST XGL ALA HCST HXGL Ai E memcpy_pc s R rho tp tr ms md Hsm HM HX' ltac:(first [assumption | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc])).
  - intros L rho' tp' HL Hag. cbn [In] in HL. assert (HL' : L = L_mc1) by (destruct HL as [<-|[<-|[]]]; reflexivity). subst L. cbn [nd_tv nd_fr nd_am]. rewrite HT.
    apply (REENTER T (NDA tv fr_vt bd ANone) (rk, z0)); [exact HinT | rewrite emeas_z0; lia].
Qed.

Lemma HIN_op : ltac2:(tb__ "0|6|
S2eS6S6Se4S1dSaA1S7Sf2Sc3S7S1dS38Q40A1A1SbeS0S1eSa0S8S2fRbA1A1A1S1fA3S0S1eSa2S8S2fRcA1A1A1S1fA3S0S1eSf5S8S2fRdA1A1S22S20S6S6A2M0S21S6S6RcS88Z4M1RbA2A4S23G0A1M2A3S39S27S25A1M3Sc7R9A6S1fA3S0S1eScfVXGL;S8S2fReA1M4A1S22G0S21S6S6RdS88G1RcA2A4G2A3S39G3SdG4A1Sa1S3dRdRcA2A8S1fA3S0S6Se3RcPcA2S10Sc6S114SbZf8A1A3A3S0S6Se3RdP24A2S113A3S0S6Se3ReP21A2S10Sc6S87SbZ40A1A3A3S0S6Se3RfP22A2S10Sc6S87SbZ50A1A3A3SbaS9SfReA1S8S2fR13A1A1A3S9fVCST;VFB;VFF;Vrho0;A4Sc0S85Vrho0;R10A3VAInv;RfReRdRcA4S92Vrho0;R10A2Se9R13Sc5Sc4R11A1A1A2S98VFB;R12A2S99VFF;R13A2S95VFB;R14R16S43R1aR19S3aS3bA4A4Se7R17S43R1bR1aS3aS3bA4A2Se8R18S43R1cR1bS3aS3bA4A2S93VFF;R17R19S39A4S1SfeVCST;Vrho0;VFB;VFF;R1aS22G0S21S6S6R1eS88G1R1dA2A4G2A3M5S39R1bA8S1S100VCST;VXGL;Vrho0;VFB;VFF;R1aG5S39S3dR1eR1dA2A9S118SeaVFB;R1aG5A3Sf9VFF;R1aS39A3Se6Se5R1aR1bR19A3R1cA2A3A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FAi;Fms;Frho;FR;Fs;Fk;Fd;FEc;").
Proof.
  intros Ec d k s R rho ms Ai rho1 tp1 md1 HB HFRF HR HX E12 E36 E33 E34 HF HP0 Hav HM HTP HTK HBf HFF HN HD HZ HFR. destruct (P0_now rho Hav HP0) as (HT & Hb & Hal & _).
  pose proof (basez_of DW rho _ DW_rng HF HB) as BZ. pose proof BZ as [Bsp Bb Bal BL BB Btop]. rewrite aceil_val in *.
  pose proof (Forall_single _ _ _ HN) as HN1. pose proof (Forall_single _ _ _ HZ) as HZ1. pose proof (tvd_single rho (d, kb 4 k)) as HD1.
  split; [|split].
  - intros o a Ho Hr. eapply (robjs_checkP_sound segs AInv CST ALA rho0 FB FF Ai rho _ [(d, kb 4 k)] fr_vt None extraOH R rho1 tp1 md1 HM HF (T_ok_T0 rho0 _ Ai HTP HTK) HN1 HD1 HZ1 HFR HR);
      [intros o' a' Ho' HE Hr'; exact (extra_client rho o' a' _ _ BZ Hav HP0 HE Hr') | exact Ho | exact Hr].
  - exact (proj1 (siteX Ai rho _ [(d, kb 4 k)] fr_vt None (ss_objs (ax_S Ec)) (Xk_op d k) rho1 tp1 md1 HM HF HB Hav HP0 HTP HTK HBf HFF HN1 HD1 HZ1 HFR HX)).
  - unfold OPP.P0_op. rewrite !rw_call'. rewrite E12, E36, E33, E34.
    assert (HFin : In (uval rho hF, 128, uval rho hFL) (FFx FF rho fr_vt)).
    { apply In_FFx. right. exists (hF, 1%Z, hFL). split; [left; reflexivity | reflexivity]. }
    pose proof (foff_rng rho _ 64 HF HFRF ltac:(lia)) as E64. pose proof (foff_rng rho _ 80 HF HFRF ltac:(lia)) as E80. unfold uval in E64, E80.
    split; [|split; [|split]].
    + destruct Hb as (f & sz & fl & Hin & H1 & H2). exists f, sz, fl. split; [apply In_FFx; left; exact Hin|].
      assert (E248 : uval rho (SAlu ALU_ADD vb (SLit 248)) = uval rho vb + 248) by (apply uval_add_litZ; unfold IMG_HI in *; lia).
      unfold uval in E248, H1, H2. rewrite E248. lia.
    + destruct Hal as (f & sz & fl & Hin & H1 & H2). exists f, sz, fl. split; [apply In_FFx; left; exact Hin|]. unfold uval in H1, H2. lia.
    + exists (uval rho hF), 128, (uval rho hFL). split; [exact HFin|]. rewrite E64. unfold OP.CM, uval. lia.
    + exists (uval rho hF), 128, (uval rho hFL). split; [exact HFin|]. rewrite E80. unfold OP.CM, uval. lia.
Qed.
Lemma X_E_op : ltac2:(tb__ "0|d|
S2eS2eS2eS2eS2eS1dSaA1M0S6S6S6S6Se4G0S7S1dS38Q40A1A1M1S2cG1S0S6S32R10A1SbS104A1A3S0G0SdS2fR11A1A1S2bSaRcS22SaSd5S86Z8ZbS132S15A5S23SaA1A3A3A3S0S1eS31S22S9S14S33S86A1S87A2S22S9SeS12S86A1SbS84S80Z2Z3dA2Z1A2A1A2S23S9A1A3A3S8S2fR12A1A1A2S1fA3S0S1eS94ScS2fR13A1A1S90S4bRdRcS3aS3bA4S39S41RcA1S8fA4A2S1fA3S0S1eSa0S8S2fR14A1A1A1S1fA3S0S1eSeeS8S2fR15A1A1S4bRfReS3aS3bA4S39R10A4S1fA3S0S2eSd4R16R11Pa0S22S20S2cS2cA2M2S21S2cS2cZ40M3Z4M4A4S22G2S21S2cS2cZ50M5G4A4S23G2A1A3A3A4R15A3S0S26S2eA1Sf6R16S7aA2S24S2eR15A2A3S0S1eSffS3dR12R11A2S30R16A1A2S1fA3S0S26G0A1Sb4R17Sd8RfA3S24G0ReA2A3S0S1eSb5R18Sd8R10RfSbbS20S2eS8eA2S2eS28S2eS8eA2S44A4A5S1fA3S0S1eS11cS85R11A2S1fA3S0S1eSc2R12Sf4A2S1fA3S0S1eS10fS85ScS2fR1bA1A1A2S1fA3S0S1eS94ScS2fR1cA1A1S90S43R18R17S3aS3bA4S39S41R17A1S8fA4A2S1fA3S0S1eSa9ScS2fR1dA1A1S89G4S45R18A3A2S1fA3S0S1eSedR16S22S20S6S6A2M6S21S6S6S3aS88G4S3bA2A4S23G6A1M7A3SdeA3S1fA3S0S1eSadS8S2fR1fA1A1SbZ0M8A1G8S41R1aA1S2bSa7SaaR17SdbS10dA1A2S89G4S45R1aA3A3A5S1fA3S0S1eSb0S102S101Sd8Sf4R18ScS2fR20A1A1A4S44A3S1fA3S0S1eSa0S8S2fR21A1A1A1S1fA3S0S1eSa2S8S2fR22A1A1A1S1fA3S0S1eSf5S8S2fR23A1A1S22G6S21S6S6R1fS88G4R1eA2A4G7A3S39S27S25A1M9Sc7R1aA6S1fA3S0S1eScfVXGL;S8S2fR24A1MaA1S22G6S21S6S6R20S88G4R1fA2A4G7A3S39G9SdGaA1Sa1S3dR20R1fA2A8S1fA3S0S6Se3R1dPcA2S10Sc6S114SbZf8A1A3A3S0S6Se3R1eP24A2S113A3S0S6Se3R1fP21A2S10Sc6S87SbG3A1A3A3S0S6Se3R20P22A2S10Sc6S87SbG5A1A3A3S0S1dG6A1MbSebSb6R21Sd8Sd9R29A4SdcA2S22G6S21S6S6R23S88G4R22A2A4G7A3A3S0S1dSa7A1SaaSb6R22Sd8Sd9R2aA4SdbS12P8eA1A1A2S89G4S69R23A3A3S0GbSebSb6R23Sd8SdaR2bA4SdcA2S22G6S21S6S6R25S88G4R24A2A4G7A3A3S0S2eSfdSd8R2cR24R23Sd9S3dR28R27A2A6R2bA3S0S2eSfdSd8R2dR25R24SdaS3dR29R28A2A6R2bA3S7G1VTR;S7bS37VJAv;S48R2cR2bR2aR29A4A1R2fR2R1A5VFAM;R24R23A2McA2Ftp';Frho';S7G1VTR;S7bS37VJAv;S4aR2dR2cR2bR2aA4A1R2fR2R1A5VFAM;R25R24A2A2Ftp';Frho';VTR;S7bS37VJAv;S72S4bR2cR2bS3aS3bA4S41R2bA1A2A1R32R26R25A5GcA2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Ftp0;Fb;Ftp;Frho;FR;Fs;Ff2;Fe2;Fk;Fd;Fobjs;FV0;FV1;FEc;FE1;FE0;").
Proof.
  intros E0 E1 Ec V1 V0 objs d k e2 f2 s R rho tp b tp0 Hbase Ho Hfe0 Hnb0 HB0 HRO0 HE1 HEc HXk He Hchk Htp Hdom Hnf Hnb Hbr Hpass Hpay Hpd HB HFRF HR HX
         E12 E36 E33 E34 Hi1 Hb1 Hi0 HV1 HV0 K1 K0.
  apply (TR_pre (fun w => exists rho', (fun w' => (forall e, eval rho' e = eval rho e) /\ SPA segs (JAv (ndF (tvI d k aw_d aw_k) (bdK k))) E1 rho' tp w') w)).
  { intros [tr [ms md]] Hw. exists (rho_absorb rho [shobj hG 8 11 cells_op DUnknown] (vms md tp ms)). split; [intros e; apply eval_absorb|].
    rewrite <- HE1. unfold ndF.
    apply (JA_shadow_release segs HTOP AInv CST XGL ALA HCST HXGL LFSH NPH Kc rho0 (P0_vt CST FB FF) FB FF BX PTrue HKc HBX HNP
             (tvI d k aw_d aw_k) fr_vt (bdK k) ANone 0%nat 160%positive 1 170%positive hG 8 11 cells_op DUnknown E0 objs [(64, 4); (80, 4)] rho tp tr ms md
             eq_refl ltac:(lia) Hbase Ho ltac:(lia) ltac:(change (fs_frame_size 1) with 128; lia) eq_refl Hfe0 ltac:(vmr) Hnb0); [|exact Hw].
    intros Ai rho1 tp1 md1 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR.
    exact (siteF2 Ai rho _ (tvI d k aw_d aw_k) fr_vt objs rho1 tp1 md1 HM HF HB0 Hav HP0 HT HTK HN HD HZ HFR HRO0). }
  apply TR_exw. intros rho'. apply (TR_pureP _ (forall e, eval rho' e = eval rho e)); [intros w [HE _]; exact HE|]. intros HE.
  eapply TR_pre with (P := SPA segs (JAv (NDA (tv_vt d k aw_d aw_k) fr_vt (bdK k) ANone)) Ec rho' tp).
  { intros w [_ Hw]. unfold tv_vt. apply SPA_swap2. exact (SPA_axforms segs _ xf_op rho' E1 Ec tp w HEc Hw). }
  clear HE. apply TR_facts. intros HF. unfold tv_vt.
  change [(d, kb 4 k); (aw_d, kb 4 aw_k)] with ([(d, kb 4 k)] ++ [(aw_d, kb 4 aw_k)]).
  apply (client_callT segs AInv CST XGL ALA HCST HXGL NPH Kc rho0 (P0_vt CST FB FF) FB FF BX PTrue HKc HBX OPP.P0_op PTrue (fun _ H => H) (fun _ _ _ H => H)
           OP.Pre_op OP.nd0 PD_op NF eq_refl eq_refl eq_refl TR TR_facts TR_ex TR_pre TR_callP CVOP eq_refl
           Ec s R (Xk_op d k) rho' tp [(d, kb 4 k)] [(aw_d, kb 4 aw_k)] fr_vt (bdK k) (bd_vec 4 avt_cnt2 k) ANone (FAM b tp0)
           HXk He Hchk Htp Hdom Hnf Hnb Hbr Hpass eq_refl ltac:(apply payA_of_bud_pay; exact Hpay) Hpd).
  - intros Ai ms HF' HP0 Hav HBf HFF HN HD HZ HFR (rho1 & tp1 & md1 & HM) HT HTK.
    exact (HIN_op Ec d k s R rho' ms Ai rho1 tp1 md1 HB HFRF HR HX E12 E36 E33 E34 HF' HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR).
  - intros [Ld ndL] rho2 tp' Hd Hag. cbn [PD_op In] in Hd. destruct Hd as [Hd|[Hd|[]]]; injection Hd as <- <-;
      cbn [fst snd nd_tv nd_bd nd_am OP.nd1 OP.nd0' ND am_subst app].
    +
      rewrite HV1, Hi1, Hb1. change (NDA ((d, kb 4 k) :: [(e2, kb 4 f2)]) fr_vt (bd_vec 4 Wp1 f2 ++ bd_vec 4 avt_cnt2 k) ANone) with (ndO d k e2 f2). apply K1.
    +
      rewrite HV0, Hi0. change (NDA ((d, kb 4 k) :: [(e2, kb 4 f2)]) fr_vt (bd_subst _ [] ++ bd_vec 4 avt_cnt2 k) ANone) with (ndX d k e2 f2). apply K0.
Qed.

Lemma XH_V_opk1 : ltac2:(tb__ "0|1|
S7S1dS38Q40A1A1M0S2cG0S7fS81Z3bS80Z2Z40A2A2R2A2VTR;S7bS37VJAv;S48S8aS8bS55S56A4A1S131R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. unfold ndO, ndF.
  apply (X_arr V_opk1 Z_opk1 (ax_setX Z_opk1 (X_vt avt_d avt_k oD oK)) T_opk1 xf_opb (X_vt avt_d avt_k oD oK) _ _ rho tp b tp0 58 Z_opk1_eq);
    [vmr|reflexivity|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr| exact T_opk1_eq | innth 18 | lia | lia].
Qed.
Lemma XH_V_opk0 : ltac2:(tb__ "0|1|
S7S1dS38Q40A1A1M0S2cG0S7fS81Z3bS80Z2Z40A2A2R2A2VTR;S7bS37VJAv;S4aS8aS8bS55S56A4A1S130R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. unfold ndX, ndF.
  apply (X_arr V_opk0 Z_opk0 (ax_setX Z_opk0 (X_vt avt_d avt_k oD oK)) T_opk0 xf_opb (X_vt avt_d avt_k oD oK) _ _ rho tp b tp0 58 Z_opk0_eq);
    [vmr|reflexivity|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr| exact T_opk0_eq | innth 19 | lia | lia].
Qed.
Lemma XH_V_opg1 : ltac2:(tb__ "0|1|
S7S1dS38Q40A1A1M0S2cG0S7fS81Z3bS80Z2Z40A2A2R2A2VTR;S7bS37VJAv;S48S59S5aS51S52A4A1S12fR5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. unfold ndO, ndF.
  apply (X_arr V_opg1 Z_opg1 (ax_setX Z_opg1 (X_vt vDg vKg gD gK)) T_opg1 xf_opb (X_vt vDg vKg gD gK) _ _ rho tp b tp0 58 Z_opg1_eq);
    [vmr|reflexivity|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr| exact T_opg1_eq | innth 20 | lia | lia].
Qed.
Lemma XH_V_opg0 : ltac2:(tb__ "0|1|
S7S1dS38Q40A1A1M0S2cG0S7fS81Z3bS80Z2Z40A2A2R2A2VTR;S7bS37VJAv;S4aS59S5aS51S52A4A1S12eR5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. unfold ndX, ndF.
  apply (X_arr V_opg0 Z_opg0 (ax_setX Z_opg0 (X_vt vDg vKg gD gK)) T_opg0 xf_opb (X_vt vDg vKg gD gK) _ _ rho tp b tp0 58 Z_opg0_eq);
    [vmr|reflexivity|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr| exact T_opg0_eq | innth 21 | lia | lia].
Qed.
Lemma XH_E_opk : ltac2:(tb__ "0|1|
S7S1dS38Q40A1A1M0S2cG0S7fS81Z3eS80Z2Z40A2A2R2A2VTR;S7bS37VJAv;S54A1S60R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. unfold ndK, tvP.
  apply (X_E_op E_opk E_opk1 E_opkc V_opk1 V_opk0 objs_opk avt_d avt_k oD oK s_opk R_opk rho tp b tp0);
    [vmr| exact E_opk_objs |vmr|vmr|vmr|vmr| exact E_opk1_eq | exact E_opkc_eq |vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr
    | exact imp_opk1_tv | exact imp_opk1_bd | exact imp_opk0_tv | exact V_opk1_eq | exact V_opk0_eq
    | intros rho' tp'; apply XH_V_opk1; lia | intros rho' tp'; apply XH_V_opk0; lia].
Qed.
Lemma XH_E_opg : ltac2:(tb__ "0|1|
S7S1dS38Q40A1A1M0S2cG0S7fS81Z3eS80Z2Z40A2A2R2A2VTR;S7bS37VJAv;S53A1S5fR5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. unfold ndG, tvG.
  apply (X_E_op E_opg E_opg1 E_opgc V_opg1 V_opg0 objs_opg vDg vKg gD gK s_opg R_opg rho tp b tp0);
    [vmr| exact E_opg_objs |vmr|vmr|vmr|vmr| exact E_opg1_eq | exact E_opgc_eq |vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr
    | exact imp_opg1_tv | exact imp_opg1_bd | exact imp_opg0_tv | exact V_opg1_eq | exact V_opg0_eq
    | intros rho' tp'; apply XH_V_opg1; lia | intros rho' tp'; apply XH_V_opg0; lia].
Qed.

Lemma XH_E_sm : ltac2:(tb__ "0|1|
S7S1dS38Q40A1A1M0S2cG0S7fS81Z62S80Z2Z40A2A2R2A2VTR;S7bS37VJAv;S47A1S61R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply TR_facts. intros HF.
  apply (smalloc_callT segs AE_A AInv CST XGL ALA HCST HXGL NPH Kc rho0 (P0_vt CST FB FF) FB FF BX PTrue HKc TR TR_facts TR_ex TR_pre TR_callP
           1 E_sm0 s_sm R_sm rho tp nd0 160 170 (FAM b tp0) CSM).
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
  - intros Ai ms HF' HP0 Hav HBf HFF HN HD HZ HFR (rho1 & tp1 & md1 & HM) HT HTK. destruct (P0_now rho Hav HP0) as (_ & _ & _ & HC0).
    cbn [nd_tv nd_fr nd0 ND] in HN, HD, HZ, HFR |- *.
    split; [|split].
    + exact (siteP Ai rho _ (tv_vt avt_d avt_k aw_d aw_k) [] None R_sm rho1 tp1 md1 HM HF' ltac:(vmr) Hav HP0 HT HTK HBf HFF HN HD HZ HFR ltac:(vmr)).
    + exact (proj1 (proj2 (siteX Ai rho _ (tv_vt avt_d avt_k aw_d aw_k) [] None (ss_objs (ax_S E_sm0)) (ax_X E_sm0) rho1 tp1 md1 HM HF' ltac:(vmr) Hav HP0 HT HTK HBf HFF HN HD HZ HFR ltac:(vmr)))).
    + split; [change (wsub_get s_sm 12) with (SLit 96); rewrite uval_lit by lia; change (fs_frame_size 1) with 128; lia|].
      unfold ffpairs. change (map (fun y : Z * Z * Z => fst y) FF) with (map fst FF). rewrite HC0. cbn. lia.
  - intros rho' tp'. rewrite T_sm_eq.
    eapply TR_pre with (P := SPA segs (JAv (ndF (tv_vt avt_d avt_k aw_d aw_k) bdPre)) T_sm1 rho' tp').
    { intros w Hw. exact (SPA_axforms segs _ [AXSelect sel_sm] rho' T_sm T_sm1 tp' w T_sm1_eq Hw). }
    apply (TR_pre (fun w => exists rho2, SPA segs (JAv ndP) C_pro rho2 tp' w)).
    { intros w Hw. unfold ndF in Hw.
      destruct (JA_frame_open segs HTOP AInv CST XGL ALA HCST HXGL LFLAG NPH Kc rho0 (P0_vt CST FB FF) FB FF BX PTrue HKc HBX HNP
                  (tv_vt avt_d avt_k aw_d aw_k) fr_vt bdPre ANone 0%nat 160 1 170 T_sm1 objs_sm1 (X_vt avt_d avt_k aw_d aw_k) [] rho' tp' w eq_refl ltac:(lia) eq_refl
                  T_sm1_objs T_sm1_X ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) eq_refl ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc)) as (rho2 & _ & Hw2); [| exact Hw |].
      - intros Ai rho1 tp1 md1 HF2 HP0 Hav HM HT HTK HBf HFF HN HDt HZt HFR. rewrite app_nil_r.
        exact (proj1 (siteX Ai rho' _ (tv_vt avt_d avt_k aw_d aw_k) fr_vt (Some 0%nat) (ss_objs (ax_S T_sm1)) (X_vt avt_d avt_k aw_d aw_k) rho1 tp1 md1
                        HM HF2 ltac:(vmr) Hav HP0 HT HTK HBf HFF HN HDt HZt HFR ltac:(vmr))).
      - exists rho2. rewrite app_nil_r in Hw2. rewrite C_pro0_eq in Hw2. unfold ndP, ndF, tvP, tvI. apply SPA_swap2. rewrite <- C_pro_eq.
        apply (SPA_x_len0 segs (JAv (NDA (tv_vt avt_d avt_k aw_d aw_k) fr_vt bdPre ANone)) C_pro0 160 5 rho2 tp' w); [vmr | lia | vmr | exact Hw2]. }
    apply TR_exw. intros rho2. apply (REENTER C_pro ndP (96, z0)); [innth 1 | rewrite emeas_z0; lia].
Qed.

Lemma exits_okT : ltac2:(tb__ "0|3|
S2eS8eS20S2cS6A2M0S7S1dS38Q40A1A1M1G1SaeS20S20S2eS8eA2M2G0A2S21G2G0S21S2eS8eR6R5A4R4A4S6fA3VTR;S7bS37VJAv;R6A1R7R4R3A5VFAM;S97S21G2G0S21S2eS8eR7R6A4R5A4R4A2R2A2A2F_;Ftp0;Ftp;Frho;FrvX;FndX;FX;").
Proof.
  intros X ndX rvX rho tp tp0 Hin. cbn [In exitsV] in Hin.
  destruct Hin as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[]]]]]]]]]]]]]; injection H as <- <- <-.
  - apply XH_E_sm. rewrite emeas_z0. lia.
  - apply XH_X_A. rewrite emeas_z0. lia.
  - apply XH_E_B. rewrite emeas_z0. lia.
  - apply XH_E_vr. rewrite emeas_z0. lia.
  - apply XH_E_Dk. rewrite emeas_z0. lia.
  - apply XH_E_Dg. rewrite emeas_z0. lia.
  - apply XH_E_opk. rewrite emeas_z0. lia.
  - apply XH_E_opg. rewrite emeas_z0. lia.
  - apply XH_X_rlf. rewrite emeas_z0. lia.
  - apply XH_X_rlo. rewrite emeas_z0. lia.
  - apply POST. innth 0.
  - apply POST. innth 1.
Qed.
End X.

Section Safety.
Variable ok : world -> Prop.
Hypothesis Hok : ltac2:(tb__ "0|0|
S9eS37VKc;Vok;A3").
Hypothesis AC : ltac2:(tb__ "0|0|
S12bS37S126VAInv;VCST;VXGL;A5").

Theorem handle_vt_sum : ltac2:(tb__ "0|0|
S1dS38Q40A1A1Se2S37Vok;S7bS37S96VAInv;VCST;VXGL;VKc;S9fVCST;VFB;VFF;A3VFB;VFF;VBX;S91S47AaS4dVrho0;R1A5Sb3S37S85Vrho0;R1Sf0A5A4Ftp0;").
Proof.
  intros tp0.
  eapply triple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_sound_JA segs AInv CST XGL NPH Kc rho0 (P0_vt CST FB FF) FB FF BX PTrue HKc ALA FUEL_vt cutpcs_vt NPH
                (map edropA cutsV) (map edropA exitsV) ok (Q tp0) Hok (ejcertA_jcertA segs NPH _ _ _ _ _ ejcertV_ok))
         with (ndT := nd0); [|left; reflexivity].
       intros X ndX rho tp Hin. apply in_map_iff in Hin as ([[X' nd'] rv] & E0 & Hin). cbn in E0. injection E0 as <- <-.
       apply (exits_okT (triple segs ok) (fun _ _ w => SPfamGTA segs (map nI (map edropA cutsV)) w \/ Q tp0 w)
                (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok) (@triple_ex segs ok) (TRs_pureP segs ok) (call_soundPA3 segs ok)) with (rvX := rv) (tp0 := tp0).
       - intros FBc FFc BXc rho1 tp1 HB0. apply (vec_reserve_sum AInv CST XGL ALA HCST HXGL Kc HKc FBc FFc BXc HB0 rho1 ok Hok AC tp1).
       - intros FBc FFc BXc rho1 tp1 HB0. apply (OPP.opt_push1_sum AInv CST XGL ALA HCST HXGL Kc HKc FBc FFc BXc HB0 rho1 ok Hok AC tp1).
       - intros Ai rho1 tp1. apply (aca_stack_malloc _ _ _ _ _ AC 1 ltac:(cbn; tauto)); [exact HKc|]. eapply ok_frameA_of_K; [exact Hok|]. intros r p t m (_ & K & _). exact K.
       - intros Cl s R rho1 tp1 nd Q' He Hc Hn Hb Hf Hk.
         apply (pure_callA segs AInv CST XGL NPH Kc rho0 (P0_vt CST FB FF) FB FF BX PTrue HKc ALA ok Cl Pre_sd s R Posts_sd rho1 tp1 nd Q'); try assumption.
         intros rho2 tp2. apply scan_double_sum; [apply frozen_ok_frameA; exact Hok | apply (frozen_stable NF (ss_next (ax_S Cl)) nd rho1); [apply Pos.leb_le; exact Hn | exact Hb]].
       - intros T nd rv' rho1 tp1 b tp2 HinT _. apply (reenter_cutJA segs AInv CST XGL NPH Kc rho0 (P0_vt CST FB FF) FB FF BX PTrue ok (map edropA cutsV) T nd).
         apply in_map_iff. exists (T, nd, rv'). auto.
       - intros P nd rho1 tp1 b tp2 HinP. apply (exit_postGA segs AInv CST XGL NPH Kc (P0_vt CST FB FF) FB FF BX PTrue ok rho0 tp0 nd Posts_vtJ P). exact HinP.
       - exact Hin. }
  intros w Hw. apply JA_pre_intro. exact Hw.
Qed.
End Safety.

Section Existence.
Hypothesis ACX : ltac2:(tb__ "0|0|
S12cS37S126VAInv;VCST;VXGL;A5").

Theorem handle_vt_sum_ex : ltac2:(tb__ "0|0|
S1dS38Q40A1A1Se1S37S7bS37S96VAInv;VCST;VXGL;VKc;S9fVCST;VFB;VFF;A3VFB;VFF;VBX;S91S47AaS4dVrho0;R1A5Sb3S37S85Vrho0;R1Sf0A5A3Ftp0;").
Proof.
  intros tp0.
  eapply etriple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_complete_JA segs AInv CST XGL NPH Kc rho0 (P0_vt CST FB FF) FB FF BX PTrue HKc ALA FUEL_vt cutpcs_vt NPH cutsV exitsV (Q tp0) ejcertV_ok)
         with (ndT := nd0) (rv := (100, z0)); [|left; reflexivity].
       intros X ndX rv rho tp Hin.
       apply (exits_okT (etriple segs) (fun b _ w => SPfamETA segs (map (enodeIA AInv CST XGL NPH Kc rho0 (P0_vt CST FB FF) FB FF BX PTrue) cutsV) b w \/ Q tp0 w)
                (TRe_facts segs) (TRe_ex segs) (TRe_pre segs) (@etriple_ex segs) (TRe_pureP segs) (call_completePA3 segs)) with (tp0 := tp0).
       - intros FBc FFc BXc rho1 tp1 HB0. apply (vec_reserve_sum_ex AInv CST XGL ALA HCST HXGL Kc HKc FBc FFc BXc HB0 rho1 ACX tp1).
       - intros FBc FFc BXc rho1 tp1 HB0. apply (OPP.opt_push1_sum_ex AInv CST XGL ALA HCST HXGL Kc HKc FBc FFc BXc HB0 rho1 ACX tp1).
       - intros Ai rho1 tp1. apply (acx_stack_malloc _ _ _ _ _ ACX 1 ltac:(cbn; tauto)). exact HKc.
       - intros Cl s R rho1 tp1 nd Q' He Hc Hn Hb Hf Hk.
         apply (pure_callA_ex segs AInv CST XGL NPH Kc rho0 (P0_vt CST FB FF) FB FF BX PTrue HKc ALA Cl Pre_sd s R Posts_sd rho1 tp1 nd Q'); try assumption.
         intros rho2 tp2. apply scan_double_sum_ex. apply (frozen_stable NF (ss_next (ax_S Cl)) nd rho1); [apply Pos.leb_le; exact Hn | exact Hb].
       - intros T nd rv' rho1 tp1 b tp2 HinT Hm. apply (ereenter_cutJA segs AInv CST XGL NPH Kc rho0 (P0_vt CST FB FF) FB FF BX PTrue cutsV T nd rv'); [exact HinT | exact Hm].
       - intros P nd rho1 tp1 b tp2 HinP. apply (eexit_postGA segs AInv CST XGL NPH Kc (P0_vt CST FB FF) FB FF BX PTrue rho0 tp0 nd Posts_vtJ P). exact HinP.
       - exact Hin. }
  intros w Hw. apply JA_pre_intro. exact Hw.
Qed.
End Existence.
End Sum.
End Lib_handle_vt_pf.

