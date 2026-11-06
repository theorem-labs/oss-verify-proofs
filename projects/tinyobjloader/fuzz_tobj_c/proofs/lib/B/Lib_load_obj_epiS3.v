(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG SymSummary SymObj SymFrame.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA SummaryA2 MemoFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv ObjXform ObjUnbase TobjJV.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR TobjJAS TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.TobjJAH OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p4.TobjJAD OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.ObjZeroA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import ObjEmptyA PinA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_defs Lib_load_obj_pro Lib_load_obj_pro2 Lib_load_obj_loop Lib_load_obj_disp Lib_load_obj_lglue Lib_load_obj_hv0 Lib_load_obj_bud Lib_load_obj_exits Lib_load_obj_loopE Lib_load_obj_armkit Lib_load_obj_armkit2 Lib_load_obj_avn Lib_load_obj_hvkit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.Asan_memcpyR_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_vec_finalize.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ni.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_exitsR Lib_load_obj_epiD1 Lib_load_obj_epiD2 Lib_load_obj_epiS1 Lib_load_obj_epiS2.
Import ListNotations. Close Scope bv_scope. Open Scope Z_scope. Import ScanDoubleAddr LOAddr LOLAddr.
Module VF. Include Lib_vec_finalize. End VF. Module VFP. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ni.Lib_vec_finalize_pf. End VFP.

Definition L_d1 : axst := Eval vm_compute in skipL B_1 pc_disp 0.

Definition E0_1 : axst := Eval vm_compute in callL B_1.
Definition E_1 : axst := Eval vm_compute in E_vf E0_1 120.
Definition R_1 : list sobj := Eval vm_compute in R_vf E_1.
Definition Tz0_1 : axst := Eval vm_compute in T_vf0 E_1 (SVar 400) VF.P_zero.
Definition TzB_1 : axst := Eval vm_compute in T_vfB Tz0_1 120.
Definition Tz_1 : axst := Eval vm_compute in ax_tidy TzB_1.
Definition B_2 : axst := Eval vm_compute in nextBj junk_b (skipL Tz_1 0x8e5cc 0).

Definition E0_2 : axst := Eval vm_compute in callL B_2.
Definition E_2 : axst := Eval vm_compute in E_vf E0_2 152.
Definition R_2 : list sobj := Eval vm_compute in R_vf E_2.
Definition Tz0_2 : axst := Eval vm_compute in T_vf0 E_2 (SVar 403) VF.P_zero.
Definition TzB_2 : axst := Eval vm_compute in T_vfB Tz0_2 152.
Definition Tz_2 : axst := Eval vm_compute in ax_tidy TzB_2.
Definition B_3 : axst := Eval vm_compute in nextBj junk_b (skipL Tz_2 0x8e62c 0).

Definition E0_3 : axst := Eval vm_compute in callL B_3.
Definition E_3 : axst := Eval vm_compute in E_vf E0_3 184.
Definition R_3 : list sobj := Eval vm_compute in R_vf E_3.
Definition Tz0_3 : axst := Eval vm_compute in T_vf0 E_3 (SVar 406) VF.P_zero.
Definition TzB_3 : axst := Eval vm_compute in T_vfB Tz0_3 184.
Definition Tz_3 : axst := Eval vm_compute in ax_tidy TzB_3.
Definition B_4 : axst := Eval vm_compute in nextBj junk_b (skipL Tz_3 0x8e68c 0).

Definition E0_4 : axst := Eval vm_compute in callL B_4.
Definition E_4 : axst := Eval vm_compute in E_vf E0_4 216.
Definition R_4 : list sobj := Eval vm_compute in R_vf E_4.
Definition Tz0_4 : axst := Eval vm_compute in T_vf0 E_4 (SVar 409) VF.P_zero.
Definition TzB_4 : axst := Eval vm_compute in T_vfB Tz0_4 216.
Definition Tz_4 : axst := Eval vm_compute in ax_tidy TzB_4.
Definition B_5 : axst := Eval vm_compute in nextBj junk_b (skipL Tz_4 0x8e6ec 0).

Definition E0_5 : axst := Eval vm_compute in callL B_5.
Definition E_5 : axst := Eval vm_compute in E_vf E0_5 248.
Definition R_5 : list sobj := Eval vm_compute in R_vf E_5.
Definition Tz0_5 : axst := Eval vm_compute in T_vf0 E_5 (SVar 412) VF.P_zero.
Definition TzB_5 : axst := Eval vm_compute in T_vfB Tz0_5 248.
Definition Tz_5 : axst := Eval vm_compute in ax_tidy TzB_5.
Definition B_6 : axst := Eval vm_compute in nextBj junk_b (skipL Tz_5 0x8e74c 0).

Definition E0_6 : axst := Eval vm_compute in callL B_6.
Definition E_6 : axst := Eval vm_compute in E_vf E0_6 280.
Definition R_6 : list sobj := Eval vm_compute in R_vf E_6.
Definition Tz0_6 : axst := Eval vm_compute in T_vf0 E_6 (SVar 415) VF.P_zero.
Definition TzB_6 : axst := Eval vm_compute in T_vfB Tz0_6 280.
Definition Tz_6 : axst := Eval vm_compute in ax_tidy TzB_6.
Definition B_7 : axst := Eval vm_compute in nextBj junk_1 (skipL Tz_6 0x8e7b0 0).
