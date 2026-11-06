(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "app"; "bool"; "false"; "nat"; "nil"; "true"; "negb"; "orb"; "pair"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bitem"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXUnbase"; "AXMerge"; "AXSelect"; "AXSplit"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_lglue"; "frL"; "tvL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "SAlu"; "sv"; "ss_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "AHead"; "NDA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiD1"; "bd_disp"; "K_disp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loop"; "pH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs"; "vDp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiS2"; "bd_com"; "cAt"; "kAt"; "DUPk"; "DUPv"; "cps_b"; "ent_chk2"; "iW"; "spmZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiS4"; "comOf"; "cps_c"; "dup8"; "E_fu"; "bd8"; "bd9"; "bd_land"; "ekOf"; "iW2"; "nd_d0"; "pc_b8"; "pc_b9"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hv0"; "leafL"; "runL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAG"; "bd_permb"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "@Corelib.Lists.ListDef"; "firstn"; "seq"; "skipn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiD2"; "nobj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_epiS4.FU"; "Pre_fu"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hvkit"; "oidx"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loop.LOLAddr"; "c_vf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF"; "bud_pay2"; "@Stdlib.Lists.List"; "filter"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_epiD1 Lib_load_obj_epiD2 Lib_load_obj_epiS1 Lib_load_obj_epiS2 Lib_load_obj_epiS3 Lib_load_obj_epiS_defs Lib_load_obj_epiS_st2.
Definition nd_d0 : ndesc := ndEp tvL bd_disp.
Import ListNotations. Close Scope bv_scope. Open Scope Z_scope. Import ScanDoubleAddr LOAddr LOLAddr.
Module VF. Include Lib_vec_finalize. End VF. Module VFP. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ni.Lib_vec_finalize_pf. End VFP. Module FU. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nh.Lib_finalize_unknowns. End FU.

Definition pc_b8 : Z := 0x8ebe8.  Definition pc_b9 : Z := 0x8ec48.
Definition cps_c : list Z := ltac2:(tb__ "0|0|
S0S1dS34S0S1dS35S26A3A3").
Definition callC (B : axst) : axst := ltac2:(tb__ "0|0|
S36S37U12cS2bVB;A3S40U0A3").
Definition skipC (B : axst) (pc : Z) (k : nat) : axst := ltac2:(tb__ "0|0|
S36S37U12cS2bVB;A3Vpc;Vk;A3").

Definition L_d7 : axst := Eval vm_compute in skipL B_7 pc_disp 0.
Definition E_fu0 : axst := Eval vm_compute in leafL (runL 300 cps_b B_7) FU.FinUnkAddr.fu_entry 0.
Definition xf_fu (A : axst) : list axform := ltac2:(tb__ "0|2|
S0ScS10S28VA;A1M0S13Nd0M1A1A2S0ScSdG0G1A2S5ScA1A3A3").
Definition E_fu : axst := Eval vm_compute in optL (apply_axforms E_fu0 (xf_fu E_fu0)).
Definition s_fu : wsub := ltac2:(tb__ "0|0|
S0SaS1eS15A2S9S1eS15P13S14S1fS20S13Zd0A1A3A4S41PaS1cS2dA1S1cS3eA1A3A3").
Definition R_fu : list sobj := Eval vm_compute in optR (entails_frA E_fu FU.Pre_fu s_fu).
Definition T_fu0 : axst := Eval vm_compute in ax_add_facts (ss_facts (ax_S E_fu)) (import_postA s_fu FU.Pre_fu FU.P_fu E_fu R_fu).
Definition iW2 (T : axst) : nat := ltac2:(tb__ "0|0|
S3fS29Z350A1S14S1fS20S13Zd0A1A3VT;A3").
Definition xfb_fu (T : axst) : list axform := ltac2:(tb__ "0|2|
S0ScSdS32VT;A1M0Zd0A2S0ScSfS0S4G0S0S4U0M1S43S4S4S7S8S39R1G1A2S39R1G0A2A2A1Li;S3bG1S3dVT;A1A2A3A3A3A1S0ScSeG1A1S5ScA1A3A3A3").
Definition B_fu : axst := Eval vm_compute in optL (apply_axforms T_fu0 (xfb_fu T_fu0)).
Definition T_fu : axst := Eval vm_compute in ax_tidy B_fu.

Definition Lq_8 : axst := Eval vm_compute in leafL (runL 300 cps_c T_fu) pc_b8 0.
Definition B_8 : axst := Eval vm_compute in nextBj junk_c Lq_8.
Definition dup8 : list bitem := ltac2:(tb__ "0|1|
S0SbS25Z0M0G0G0G0Z60A5S0SbS24G0G0G0G0Z40A5S5SbA1A3A3").
Definition bd8 : list bitem := bdAt 7.
Definition brest8 : list bitem := ltac2:(tb__ "0|1|
S1SbS21S22U7M0A1S23G0A1A2S2cA3").
Definition bd9 : list bitem := ltac2:(tb__ "0|1|
S1SbS21S22U8M0A1S23G0A1A2S2cA3").
Definition nd8 : ndesc := ltac2:(tb__ "0|0|
S18S12S11S2eS17S1bS6A2A4").
Definition nd9 : ndesc := ltac2:(tb__ "0|0|
S18S12S11S2fS17S1bS6A2A4").
Definition vSHd : sv := SVar 418.
Definition E0_8 : axst := Eval vm_compute in callC B_8.
Definition E_8 : axst := Eval vm_compute in E_vf E0_8 448.
Definition R_8 : list sobj := Eval vm_compute in R_vf E_8.
Definition Tz0_8 : axst := Eval vm_compute in T_vf0 E_8 vSHd VF.P_zero.
Definition TzB_8 : axst := Eval vm_compute in T_vfB Tz0_8 448.
Definition Tz_8 : axst := Eval vm_compute in ax_tidy TzB_8.

Definition B_9 : axst := Eval vm_compute in nextBj junk_c (skipC Tz_8 pc_b9 0).
Definition C_9v : axst := Eval vm_compute in callC B_9.
Definition L_land : axst := Eval vm_compute in skipC C_9v pc_disp 0.

Definition ndP (bd : list bitem) : ndesc := ltac2:(tb__ "0|0|
S18S12S11Vbd;S17S1bS3A2A4").

Definition L_d6z : axst := Eval vm_compute in skipL Tz_6 pc_disp 0.
Definition L_d6y : axst := Eval vm_compute in skipL Ty_6 pc_disp 0.
Definition L_d6f : axst := Eval vm_compute in skipL Tf_6 pc_disp 0.

Definition ekOf (bd : list bitem) : list bitem := firstn 1 (skipn 1 bd).
Definition comOf (bd : list bitem) : list bitem := ltac2:(tb__ "0|0|
S1SbS3aSbU1Vbd;A3S3cSbU2Vbd;A3A3").
Definition bd_land (bd : list bitem) : list bitem := ltac2:(tb__ "0|0|
S1SbS19S2aVbd;A1A3").
Definition land_chk (L : axst) (bd : list bitem) (hd : sv) : bool := ltac2:(tb__ "0|5|
S2S2L_;M0S38Vbd;S1SbS2aVbd;A1M1S31Vbd;A1M2A3A2G0S38S1SbG1S19A3S30Vbd;A1M3A2G0S42S16S1cVL;A1A1S13Z0M4A1G4G2S19A5S27VL;S1aS18S12S11G3S17Vhd;S3A2A4S33A4S3X2x2S3X2x2S3X2x2").
