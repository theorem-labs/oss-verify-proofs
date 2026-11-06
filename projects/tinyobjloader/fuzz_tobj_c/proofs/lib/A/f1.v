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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ew.

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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA TobjJA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.JcertCutA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs Lib_handle_f_defs Lib_handle_f_s1 Lib_handle_f_s2 Lib_handle_f_s3 Lib_handle_f_s4 Lib_handle_f_s5 Lib_handle_f_s6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_s9 Lib_handle_f_s9b.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require es.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require en.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_nodes.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ez.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require et.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ew.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_handle_f_s7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_handle_f_s8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s9b OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.es.Lib_handle_f_s10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.en.Lib_handle_f_epi OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_nodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ez.Lib_handle_f_s8w OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.et.Lib_handle_f_nodes2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e5.Lib_handle_f_fastcert OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ew.Lib_handle_f_chk0.
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
Module Lib_handle_f_chk7.

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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs Lib_handle_f_defs Lib_handle_f_s1 Lib_handle_f_s2 Lib_handle_f_s3 Lib_handle_f_s4 Lib_handle_f_s5 Lib_handle_f_s6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_s9 Lib_handle_f_s9b.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require es.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require en.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_nodes.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ez.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require et.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ew.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_handle_f_s7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_handle_f_s8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s9b OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.es.Lib_handle_f_s10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.en.Lib_handle_f_epi OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_nodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ez.Lib_handle_f_s8w OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.et.Lib_handle_f_nodes2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e5.Lib_handle_f_fastcert OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ew.Lib_handle_f_chk0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import HFAddr.
Lemma cc_6 : CC 6 K = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_13 : CC 13 T_dg = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_20 : CC 20 JF_fv = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_27 : CC 27 K1Xg = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_34 : CC 34 K2 = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_41 : CC 41 JR_ts = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_48 : CC 48 L14 = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_55 : CC 55 JR_fv4 = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_62 : CC 62 C_Ef2 = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End Lib_handle_f_chk7.

(* [comment removed for export] *)
Module Lib_handle_f_chk6.

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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs Lib_handle_f_defs Lib_handle_f_s1 Lib_handle_f_s2 Lib_handle_f_s3 Lib_handle_f_s4 Lib_handle_f_s5 Lib_handle_f_s6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_s9 Lib_handle_f_s9b.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require es.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require en.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_nodes.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ez.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require et.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ew.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_handle_f_s7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_handle_f_s8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s9b OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.es.Lib_handle_f_s10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.en.Lib_handle_f_epi OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_nodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ez.Lib_handle_f_s8w OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.et.Lib_handle_f_nodes2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e5.Lib_handle_f_fastcert OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ew.Lib_handle_f_chk0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import HFAddr.
Lemma cc_5 : CC 5 L2 = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_12 : CC 12 XA = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_19 : CC 19 JR_fv = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_26 : CC 26 K1 = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_33 : CC 33 T_tdg = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_40 : CC 40 TS = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_47 : CC 47 J = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_54 : CC 54 T_c4 = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_61 : CC 61 JF_sg4 = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_68 : CC 68 T_g3_0 = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End Lib_handle_f_chk6.

(* [comment removed for export] *)
Module Lib_load_obj_certE_pf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@Corelib.Init.Datatypes"; "list"; "prod"; "nat"; "pair"; "bool"; "true"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue"; "ldef"; "tblB"; "P0_lo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ez.Lib_load_obj_loopEf"; "ndE0f"; "ndXEf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "triple"; "assn"; "@Corelib.Init.Logic"; "and"; "ex"; "eq"; "or"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_sub"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud"; "ndLE"; "ndXE"; "ndX0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_epiD1"; "K_disp"; "bd_disp"; "La_errx"; "s_dispA"; "s_dispX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.et.Lib_load_obj_epiD_eqs"; "nd_d0"; "PhisD"; "V_ld"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_loopE"; "K_loopE2"; "X_latchE2"; "K_afterE2"; "s_E"; "X_bodyE2"; "X_errxE2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "PTrue"; "JA"; "ok_frameKA"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "mul"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs"; "NP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_exits"; "K_afterE"; "X_bodyE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop"; "X_latch7"; "X_latchE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ew.Lib_load_obj_certE"; "cutsE2g"; "ndE0d"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "KU"; "bxK"; "bxN"; "bxS"; "bxV"; "bd_nn"; "bd_wpos"; "bsumK"; "bsumV"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF"; "phiK"; "wsub_id_on"; "JAF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@Stdlib.Lists.List"; "In"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "alloc_lawsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV TobjArena ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAS TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require ObjEmptyA PinA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAFb OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.ObjZeroA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.ObjEmptyA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.PinA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs Lib_rom_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_rom_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_defs Lib_load_obj_pro.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_load_obj_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ez.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_pro OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eo.Lib_load_obj_pro2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_load_obj_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f2.Lib_load_obj_disp OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_lglue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_load_obj_hv0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_load_obj_bud OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_load_obj_exits OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f3.Lib_load_obj_loopE OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ez.Lib_load_obj_loopEf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require et.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ew.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f5.Lib_load_obj_epiD1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.et.Lib_load_obj_epiD_eqs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e8.Lib_load_obj_boxkit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ew.Lib_load_obj_certE.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma bd_disp_sums : ltac2:(tb__ "0|0|
S1S14S16S18S44S20R1A2Z0A3S14S16S18S43S20R1A2S33Z14S3cA2A3S14S41S20R1A2S16S8S42S20A1S9A3A2A2A2Frho;").
Proof.
  intros rho. unfold bd_disp, BIc. cbn [bsumV bsumK bi_v bi_k]. unfold bival. cbn [bi_f bi_c lfval]. split; [lia|]. split; [lia|].
  split; [|reflexivity]. unfold bd_nn. repeat constructor; unfold bival; cbn [bi_f bi_c lfval]; lia.
Qed.

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
S4dS1S4SaQ40A1A1S4bOF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
S4cS0VAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S18S49VCST;R1A2S14S31Z0R2A2S32R2S48A2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S18S49VXGL;R1A2S14S31Z0R2A2S32R2S48A2A2F_;Fa;").
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S4S5S5S18S18A2S18A2A1").

Variables BX BXL : bxt.
Hypothesis HBX : BXok_d 7 BX.
Hypothesis HBXL : BXok_d 7 BXL.
Hypothesis HBS : ltac2:(tb__ "0|0|
S31S3fVBXL;A1S3fVBX;A1A2").
Hypothesis HBN : ltac2:(tb__ "0|0|
S31S3eVBXL;A1S3eVBX;A1A2").
Hypothesis HBV : ltac2:(tb__ "0|0|
S31S40VBX;A1S40VBXL;A1A2").
Hypothesis HBK : ltac2:(tb__ "0|0|
S31S34S3dVBX;A1S33Z14S3cA2A2S3dVBXL;A1A2").
Variable rho0 : valuation.
Let P0 : ltac2:(tb__ "0|0|
S1OFr;") := ltac2:(tb__ "0|0|
SdVCST;VFB;VFF;A3").
Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S2fVAInv;VCST;VXGL;S35VKc;Vrho0;VP0;VFB;VFF;VBX;S2eVnd;Ac").
Let JAvL (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S2fVAInv;VCST;VXGL;S35VKc;Vrho0;VP0;VFB;VFF;VBXL;S2eVnd;Ac").
Let JAFvL (Phi : valuation -> Prop) (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S47VAInv;VCST;VXGL;S35VKc;Vrho0;VP0;VFB;VFF;VBXL;S2eVPhi;Vnd;Ad").

Lemma box_disp : ltac2:(tb__ "0|0|
S19S1S4SaQ40A1A1S10S3S0VJAvL;SeA1R4R3R2R1A6S3S0VJAv;S3bA1R5R4R3R2A6F_;Fw;Ftp;Frho;FL;").
Proof.
  intros L rho tp w Hw. destruct (BXok_d_pair _ BX HBX) as [V0 K0]. destruct (bd_disp_sums rho) as (SV & SK & Snn & Swp).
  apply (SPA_rebox AInv CST XGL NP Kc rho0 P0 FB FF PTrue BXL BX tvL frL [] bd_disp (AHead pH false) L rho tp w HBS HBN V0 K0 Swp); [|exact Hw].
  intros _ _. split; [exact Snn|]. rewrite SV, SK. cbn [bsumV bsumK]. unfold bxV, bxK in *. lia.
Qed.
Lemma land_dispA : ltac2:(tb__ "0|0|
S1S4SaQ40A1A1S10S3S0VJAvL;SeA1S21R3R2R1A6S3S0VJAv;S24A1S1fS1aR4S22A2R3R2A6F_;Fw;Ftp;Frho;").
Proof.
  intros rho tp w Hw. pose proof epiD1_checks_join as (_ & Ce & _ & Cid & _).
  pose proof certE_checks_disp as (_ & Cnp & Cnb & Ctv & Cfr & Cbd & Cam & _).
  exact (SPA_entails_JA2 segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc La_errx K_disp s_dispA ndE0d nd_d0 rho tp w Ce Cid Cnp Cnb Ctv Cfr Cbd Cam
           (box_disp La_errx rho tp w Hw)).
Qed.
Lemma land_dispX : ltac2:(tb__ "0|0|
S1S4SaQ40A1A1S10S3S0VJAvL;SeA1S2cR3R2R1A6S3S0VJAv;S24A1S1fS1aR4S23A2R3R2A6F_;Fw;Ftp;Frho;").
Proof.
  intros rho tp w Hw. pose proof epiD1_checks_join as (_ & _ & Ce & _ & Cid & _).
  pose proof certE_checks_disp as (_ & _ & _ & _ & _ & _ & _ & _ & Cnp & Cnb & Ctv & Cfr & Cbd & Cam & _).
  exact (SPA_entails_JA2 segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PTrue HKc X_errxE2 K_disp s_dispX ndE0d nd_d0 rho tp w Ce Cid Cnp Cnb Ctv Cfr Cbd Cam
           (box_disp X_errxE2 rho tp w Hw)).
Qed.

Lemma arr_latchf : ltac2:(tb__ "0|0|
S1S4SaQ40A1A1S10S3S0VJAFvL;ScSfA2S28R3R2R1A6S15S1S1S14SbR1A1S3S0VJAvL;SeA1S27R1R4R3A6A2Lrho2;A2F_;Fw;Ftp;Frho;").
Proof.
  intros rho tp w Hw. destruct (SPA_JAF_elim segs AInv CST XGL NP Kc rho0 P0 FB FF BXL PTrue tblB ndXEf X_latchE2 rho tp w Hw) as [HS HB].
  destruct (latch_absorbE2f AInv CST XGL ALA HCST HXGL Kc HKc FB FF BXL PTrue rho0 rho tp w HB HS) as (rho2 & HT & HS2 & _).
  exists rho2. split; [exact (tblL_ldef rho2 HT) | exact HS2].
Qed.
Lemma arr_latch2 : ltac2:(tb__ "0|0|
S1S4SaQ40A1A1S10S3S0VJAFvL;ScS1dA2S28R3R2R1A6S15S1S1S14SbR1A1S3S0VJAvL;SeA1S27R1R4R3A6A2Lrho2;A2F_;Fw;Ftp;Frho;").
Proof. intros rho tp w Hw. exact (arr_latchf rho tp w (relaxF_latchE2 AInv CST XGL Kc FB FF BXL HBXL PTrue rho0 rho tp w Hw)). Qed.
Lemma arr_latch1 : ltac2:(tb__ "0|0|
S1S4SaQ40A1A1S10S3S0VJAFvL;ScS1dA2S39R3R2R1A6S15S1S1S14SbR1A1S3S0VJAvL;SeA1S27R1R4R3A6A2Lrho2;A2F_;Fw;Ftp;Frho;").
Proof.
  intros rho tp w Hw. destruct (SPA_JAF_elim segs AInv CST XGL NP Kc rho0 P0 FB FF BXL PTrue tblB ndXE X_latchE rho tp w Hw) as [HS HB].
  pose proof certE_checks_sE as (CB & _ & _).
  apply (arr_latch2 (rho_sub rho s_E) tp w). apply SPA_JAF_intro; [|exact (phi_sub V_B tblB tblB_reads s_E rho CB HB)].
  exact (relax_latchE AInv CST XGL ALA Kc HKc FB FF BXL PTrue rho0 rho tp w HS).
Qed.
Lemma arr_latch7 : ltac2:(tb__ "0|0|
S1S4SaQ40A1A1S10S3S0VJAFvL;ScS1eA2S38R3R2R1A6S15S1S1S14SbR1A1S3S0VJAvL;SeA1S27R1R4R3A6A2Lrho2;A2F_;Fw;Ftp;Frho;").
Proof.
  intros rho tp w Hw. destruct (SPA_JAF_elim segs AInv CST XGL NP Kc rho0 P0 FB FF BXL PTrue tblB ndX0 X_latch7 rho tp w Hw) as [HS HB].
  pose proof certE_checks_l7 as (Ce & Cid & Cnp & Cnb & Ctv & Cfr & Cbd & Cam & CB).
  apply (arr_latch2 (rho_sub rho s_l7) tp w). apply SPA_JAF_intro; [|exact (phi_sub V_B tblB tblB_reads s_l7 rho CB HB)].
  exact (SPA_entails_JA2 segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BXL PTrue HKc X_latch7 X_latchE2 s_l7 ndX0 ndXE rho tp w Ce Cid Cnp Cnb Ctv Cfr Cbd Cam HS).
Qed.
Lemma sE_ldef : ltac2:(tb__ "0|0|
S1SbR1A1SbS1aR2S2aA2A1F_;Frho;").
Proof. intros rho HL. pose proof certE_checks_sE as (_ & CL & _). exact (phi_sub V_ld ldef ldef_reads s_E rho CL HL). Qed.
Lemma arr_bodyE : ltac2:(tb__ "0|0|
S1S4SaQ40A1A1S10S3S0VJAvL;S1cA1S37R3R2R1A6S3S0VJAvL;SeA1S2bS1aR4S2aA2R3R2A6F_;Fw;Ftp;Frho;").
Proof.
  intros rho tp w Hw. apply (JA_pot_drop segs AInv CST XGL NP Kc rho0 P0 FB FF BXL PTrue HBXL tvL frL [] pH).
  exact (relax_bodyE AInv CST XGL ALA Kc HKc FB FF BXL PTrue rho0 rho tp w Hw).
Qed.
Lemma arr_afterE : ltac2:(tb__ "0|0|
S1S4SaQ40A1A1S10S3S0VJAvL;S1cA1S36R3R2R1A6S3S0VJAvL;SeA1S29S1aR4S2aA2R3R2A6F_;Fw;Ftp;Frho;").
Proof.
  intros rho tp w Hw. apply (JA_pot_drop segs AInv CST XGL NP Kc rho0 P0 FB FF BXL PTrue HBXL tvL frL [] pH).
  exact (relax_afterE AInv CST XGL ALA Kc HKc FB FF BXL PTrue rho0 rho tp w Hw).
Qed.

Section Safety.
Variable ok : world -> Prop.
Hypothesis Hok : ltac2:(tb__ "0|0|
S30S0VKc;Vok;A3").
Variable Q : assn.
Hypothesis KDISP_T : ltac2:(tb__ "0|0|
S1S4SaQ40A1A1SbR2A1S12S0Vok;S3S0VJAv;S24A1S1fR3R2A5VQ;A4F_;Ftp;Frho;").

Lemma XD_T : ltac2:(tb__ "0|1|
S19S1bS13S1S4SaQ40A1A1M0S10S3S0VJAvL;SeA1R6R3R2R1A6S3S0VJAv;S24A1S1fS1aR4R6A2R3R2A6F_;Fw;Ftp;Frho;S16S8S46S26R3A2S9A3S1G0S12S0Vok;S3S0VJAFvL;SbSeA2R7R2R1A5S10S17R6R1A1VQ;R1A1A2Lw;A4Ftp;Frho;F_;F_;FF;Fs;FL;").
Proof.
  intros L s F HL Hs rho tp. apply (triple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BXL PTrue ldef ok). intros HP.
  eapply triple_conseq; [intros w Hw; exact (HL rho tp w Hw) | intros w Hw; right; exact Hw |].
  apply KDISP_T. exact (phi_sub V_ld ldef ldef_reads s rho Hs HP).
Qed.

Lemma E3_T : ltac2:(tb__ "0|0|
S1S4SaQ40A1A1SbR2A1S12S0Vok;S3S0VJAvL;SeA1S29R3R2A5VQ;A4F_;Ftp;Frho;").
Proof.
  intros rho tp HL. pose proof certE_checks_disp as (_ & _ & _ & _ & _ & _ & _ & CidA & _).
  apply (triple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BXL PTrue (phiK PhisD 0) ok ndE0f K_afterE2 rho tp Q HL).
  apply (cfg_sound_JAF segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BXL PTrue HKc PhisD PhisD_reads 300%nat cps_epi NP (map efdrop cutsE3) (map efdrop exitsE3) ok Q Hok
           (ejcertAF_jcertAF segs NP PhisD _ _ _ _ _ ecertE3_ok)); [|left; reflexivity].
  intros X ndX kX rho1 tp1 [E|[]]. injection E as <- <- <-.
  exact (XD_T La_errx s_dispA _ land_dispA CidA rho1 tp1).
Qed.

Lemma E2_T : ltac2:(tb__ "0|3|
S19S2dS6S5S18S2A2M0S1S4SaQ40A1A1S4aS5S5S5S19S2dA2M1S6A2M2G0A2S7G2G0S7G1S6S7S19S2dR6R5A4R4A4R3A4S3aA3S45S25R5R3A3S12S0Vok;S3S0VJAvL;R7A1R8R4R3A5VQ;A4F_;F_;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp Hin Hphi. pose proof certE_checks_disp as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CidX).
  apply (triple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BXL PTrue (phiK PhisD k) ok nd T rho tp Q Hphi).
  apply (cfg_sound_JAF segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BXL PTrue HKc PhisD PhisD_reads 150%nat cps_loop NP (map efdrop cutsE2g) (map efdrop exitsE2g) ok Q Hok
           (ejcertAF_jcertAF segs NP PhisD _ _ _ _ _ ecertE2g_ok)); [| apply in_map_iff; exists (T, nd, k, rv); split; [reflexivity | exact Hin]].
  intros X ndX kX rho1 tp1 [E|[E|[]]]; injection E as <- <- <-.
  - apply (triple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BXL PTrue (phiK PhisD 0) ok). intros HP.
    eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | exact (E3_T rho1 tp1 HP)].
  - exact (XD_T X_errxE2 s_dispX _ land_dispX CidX rho1 tp1).
Qed.

Lemma loopE_T : ltac2:(tb__ "0|0|
S4SaQ40A1A1S13S10R2R1A1S15S1S1S14SbR1A1S3S0VJAvL;SeA1S27R1R5R3A6A2Lrho2;A2F_;Fw;S12S0Vok;R2VQ;A4F_;FP;Ftp;").
Proof.
  intros tp P HP. eapply triple_conseq; [exact HP | intros w Hw; exact Hw |].
  apply triple_ex. intros rho2. apply triple_pure. intros HL.
  exact (E2_T K_loopE2 ndE0f 0%nat (RL, VLA 26 z0) rho2 tp ltac:(left; reflexivity) HL).
Qed.

Theorem errLf_T : ltac2:(tb__ "0|0|
S1S4SaQ40A1A1S12S0Vok;S3S0VJAFvL;ScSfA2S28R2R1A5VQ;A4Ftp;Frho;").
Proof. intros rho tp. exact (loopE_T tp _ (arr_latchf rho tp)). Qed.
Theorem errL2_T : ltac2:(tb__ "0|0|
S1S4SaQ40A1A1S12S0Vok;S3S0VJAFvL;ScS1dA2S28R2R1A5VQ;A4Ftp;Frho;").
Proof. intros rho tp. exact (loopE_T tp _ (arr_latch2 rho tp)). Qed.
Theorem errL1_T : ltac2:(tb__ "0|0|
S1S4SaQ40A1A1S12S0Vok;S3S0VJAFvL;ScS1dA2S39R2R1A5VQ;A4Ftp;Frho;").
Proof. intros rho tp. exact (loopE_T tp _ (arr_latch1 rho tp)). Qed.
Theorem err7_T : ltac2:(tb__ "0|0|
S1S4SaQ40A1A1S12S0Vok;S3S0VJAFvL;ScS1eA2S38R2R1A5VQ;A4Ftp;Frho;").
Proof. intros rho tp. exact (loopE_T tp _ (arr_latch7 rho tp)). Qed.
Theorem errB_T : ltac2:(tb__ "0|0|
S1S4SaQ40A1A1SbR2A1S12S0Vok;S3S0VJAvL;S1cA1S37R3R2A5VQ;A4F_;Ftp;Frho;").
Proof.
  intros rho tp HL. eapply triple_conseq; [intros w Hw; exact (arr_bodyE rho tp w Hw) | intros w Hw; exact Hw |].
  exact (E2_T X_bodyE2 ndE0f 0%nat (RL, VLA 25 z0) _ tp ltac:(right; left; reflexivity) (sE_ldef rho HL)).
Qed.
Theorem errA_T : ltac2:(tb__ "0|0|
S1S4SaQ40A1A1SbR2A1S12S0Vok;S3S0VJAvL;S1cA1S36R3R2A5VQ;A4F_;Ftp;Frho;").
Proof.
  intros rho tp HL. eapply triple_conseq; [intros w Hw; exact (arr_afterE rho tp w Hw) | intros w Hw; exact Hw |].
  exact (E3_T _ tp (sE_ldef rho HL)).
Qed.
End Safety.

Section Existence.
Variable Q : world -> Prop.
Hypothesis KDISP_E : ltac2:(tb__ "0|0|
S1S4SaQ40A1A1SbR2A1S11S0S3S0VJAv;S24A1S1fR3R2A5VQ;A3F_;Ftp;Frho;").

Lemma XD_E : ltac2:(tb__ "0|1|
S19S1bS10OF_;S1S4SaQ40A1A1M0S10S3S0VJAvL;SeA1R6R3R2R1A6S3S0VJAv;S24A1S1fS1aR4R6A2R3R2A6F_;Fw;Ftp;Frho;S16S8S46S26R3A2S9A3S1G0S11S0S3S0VJAFvL;SbSeA2R7R2R1A5S10S17R6R1A1VQ;R1A1A2Lw;A3Ftp;Frho;F_;F_;FF;Fs;FL;").
Proof.
  intros L s F HL Hs rho tp. apply (etriple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BXL PTrue ldef). intros HP.
  eapply etriple_conseq; [intros w Hw; exact (HL rho tp w Hw) | intros w Hw; right; exact Hw |].
  apply KDISP_E. exact (phi_sub V_ld ldef ldef_reads s rho Hs HP).
Qed.

Lemma E3_E : ltac2:(tb__ "0|0|
S1S4SaQ40A1A1SbR2A1S11S0S3S0VJAvL;SeA1S29R3R2A5VQ;A3F_;Ftp;Frho;").
Proof.
  intros rho tp HL. pose proof certE_checks_disp as (_ & _ & _ & _ & _ & _ & _ & CidA & _).
  apply (etriple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BXL PTrue (phiK PhisD 0) ndE0f K_afterE2 rho tp Q HL).
  refine (cfg_complete_JAF_b segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BXL PTrue HKc PhisD PhisD_reads 300%nat cps_epi NP cutsE3 exitsE3 (fun _ w => Q w)
           (fun b b' w _ Hw => Hw) ecertE3_ok _ K_afterE2 ndE0f 0%nat (400, z0) rho tp _); [|left; reflexivity].
  intros X ndX kX rvX rho1 tp1 [E|[]]. injection E as <- <- <- <-.
  exact (XD_E La_errx s_dispA _ land_dispA CidA rho1 tp1).
Qed.

Lemma E2_E : ltac2:(tb__ "0|3|
S19S2dS6S5S18S2A2M0S1S4SaQ40A1A1S4aS5S5S5S19S2dA2M1S6A2M2G0A2S7G2G0S7G1S6S7S19S2dR6R5A4R4A4R3A4S3aA3S45S25R5R3A3S11S0S3S0VJAvL;R7A1R8R4R3A5VQ;A3F_;F_;Ftp;Frho;Frv;Fk;Fnd;FT;").
Proof.
  intros T nd k rv rho tp Hin Hphi. pose proof certE_checks_disp as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CidX).
  apply (etriple_JAF_in segs AInv CST XGL NP Kc rho0 P0 FB FF BXL PTrue (phiK PhisD k) nd T rho tp Q Hphi).
  refine (cfg_complete_JAF_b segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BXL PTrue HKc PhisD PhisD_reads 150%nat cps_loop NP cutsE2g exitsE2g (fun _ w => Q w)
           (fun b b' w _ Hw => Hw) ecertE2g_ok _ T nd k rv rho tp _); [|exact Hin].
  intros X ndX kX rvX rho1 tp1 [E|[E|[]]]; injection E as <- <- <- <-.
  - apply (etriple_JAF segs AInv CST XGL NP Kc rho0 P0 FB FF BXL PTrue (phiK PhisD 0)). intros HP.
    eapply etriple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw | exact (E3_E rho1 tp1 HP)].
  - exact (XD_E X_errxE2 s_dispX _ land_dispX CidX rho1 tp1).
Qed.

Lemma loopE_E : ltac2:(tb__ "0|0|
S4SaQ40A1A1S10OF_;S10R2R1A1S15S1S1S14SbR1A1S3S0VJAvL;SeA1S27R1R5R3A6A2Lrho2;A2F_;Fw;S11S0R2VQ;A3F_;FP;Ftp;").
Proof.
  intros tp P HP. eapply etriple_conseq; [exact HP | intros w Hw; exact Hw |].
  apply etriple_ex. intros rho2. apply etriple_pure. intros HL.
  exact (E2_E K_loopE2 ndE0f 0%nat (RL, VLA 26 z0) rho2 tp ltac:(left; reflexivity) HL).
Qed.

Theorem errLf_E : ltac2:(tb__ "0|0|
S1S4SaQ40A1A1S11S0S3S0VJAFvL;ScSfA2S28R2R1A5VQ;A3Ftp;Frho;").
Proof. intros rho tp. exact (loopE_E tp _ (arr_latchf rho tp)). Qed.
Theorem errL2_E : ltac2:(tb__ "0|0|
S1S4SaQ40A1A1S11S0S3S0VJAFvL;ScS1dA2S28R2R1A5VQ;A3Ftp;Frho;").
Proof. intros rho tp. exact (loopE_E tp _ (arr_latch2 rho tp)). Qed.
Theorem errL1_E : ltac2:(tb__ "0|0|
S1S4SaQ40A1A1S11S0S3S0VJAFvL;ScS1dA2S39R2R1A5VQ;A3Ftp;Frho;").
Proof. intros rho tp. exact (loopE_E tp _ (arr_latch1 rho tp)). Qed.
Theorem err7_E : ltac2:(tb__ "0|0|
S1S4SaQ40A1A1S11S0S3S0VJAFvL;ScS1eA2S38R2R1A5VQ;A3Ftp;Frho;").
Proof. intros rho tp. exact (loopE_E tp _ (arr_latch7 rho tp)). Qed.
Theorem errB_E : ltac2:(tb__ "0|0|
S1S4SaQ40A1A1SbR2A1S11S0S3S0VJAvL;S1cA1S37R3R2A5VQ;A3F_;Ftp;Frho;").
Proof.
  intros rho tp HL. eapply etriple_conseq; [intros w Hw; exact (arr_bodyE rho tp w Hw) | intros w Hw; exact Hw |].
  exact (E2_E X_bodyE2 ndE0f 0%nat (RL, VLA 25 z0) _ tp ltac:(right; left; reflexivity) (sE_ldef rho HL)).
Qed.
Theorem errA_E : ltac2:(tb__ "0|0|
S1S4SaQ40A1A1SbR2A1S11S0S3S0VJAvL;S1cA1S36R3R2A5VQ;A3F_;Ftp;Frho;").
Proof.
  intros rho tp HL. eapply etriple_conseq; [intros w Hw; exact (arr_afterE rho tp w Hw) | intros w Hw; exact Hw |].
  exact (E3_E _ tp (sE_ldef rho HL)).
Qed.
End Existence.
End Sum.
End Lib_load_obj_certE_pf.

