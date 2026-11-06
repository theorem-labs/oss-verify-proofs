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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ol.

(* [comment removed for export] *)
Module Lib_handle_f_chk3.

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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs Lib_handle_f_defs Lib_handle_f_s1 Lib_handle_f_s2 Lib_handle_f_s3 Lib_handle_f_s4 Lib_handle_f_s5 Lib_handle_f_s6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require od.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_handle_f_s9 Lib_handle_f_s9b Lib_handle_f_s10.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_handle_f_nodes Lib_handle_f_s8w.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oj.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Lib_handle_f_s7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.od.Lib_handle_f_s8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s9b OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Lib_handle_f_epi OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_nodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s8w OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oh.Lib_handle_f_nodes2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Lib_handle_f_fastcert OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oj.Lib_handle_f_chk0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import HFAddr.
Lemma cc_2 : CC 2 C_pre = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_9 : CC 9 T_ms = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_16 : CC 16 JF_mi = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_23 : CC 23 JF_mm = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_30 : CC 30 JF_trg = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_37 : CC 37 K3 = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_44 : CC 44 T_pgoR = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_51 : CC 51 T_g3_4 = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_58 : CC 58 JR_mm4 = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_65 : CC 65 T_f5o = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End Lib_handle_f_chk3.

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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require BudA TobjJA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.JcertCutA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs Lib_handle_f_defs Lib_handle_f_s1 Lib_handle_f_s2 Lib_handle_f_s3 Lib_handle_f_s4 Lib_handle_f_s5 Lib_handle_f_s6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require od.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_handle_f_s9 Lib_handle_f_s9b Lib_handle_f_s10.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_handle_f_nodes Lib_handle_f_s8w.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oj.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Lib_handle_f_s7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.od.Lib_handle_f_s8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s9b OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Lib_handle_f_epi OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_nodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s8w OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oh.Lib_handle_f_nodes2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Lib_handle_f_fastcert OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oj.Lib_handle_f_chk0.
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
Module Lib_handle_f_chk7.

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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs Lib_handle_f_defs Lib_handle_f_s1 Lib_handle_f_s2 Lib_handle_f_s3 Lib_handle_f_s4 Lib_handle_f_s5 Lib_handle_f_s6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require od.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_handle_f_s9 Lib_handle_f_s9b Lib_handle_f_s10.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_handle_f_nodes Lib_handle_f_s8w.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oj.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Lib_handle_f_s7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.od.Lib_handle_f_s8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s9b OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Lib_handle_f_epi OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_nodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s8w OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oh.Lib_handle_f_nodes2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Lib_handle_f_fastcert OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oj.Lib_handle_f_chk0.
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
Lemma cc_69 : CC 69 C_T36 = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End Lib_handle_f_chk7.

(* [comment removed for export] *)
Module Lib_handle_f_chk4.

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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs Lib_handle_f_defs Lib_handle_f_s1 Lib_handle_f_s2 Lib_handle_f_s3 Lib_handle_f_s4 Lib_handle_f_s5 Lib_handle_f_s6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require od.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_handle_f_s9 Lib_handle_f_s9b Lib_handle_f_s10.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_handle_f_nodes Lib_handle_f_s8w.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oj.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Lib_handle_f_s7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.od.Lib_handle_f_s8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s9b OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Lib_handle_f_epi OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_nodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s8w OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oh.Lib_handle_f_nodes2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Lib_handle_f_fastcert OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oj.Lib_handle_f_chk0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import HFAddr.
Lemma cc_3 : CC 3 H = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_10 : CC 10 T_pc = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_17 : CC 17 C36 = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_24 : CC 24 JR_sg = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_31 : CC 31 JR_trb = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_38 : CC 38 K3m = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_45 : CC 45 T_pgiR = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_52 : CC 52 JR_mi4 = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_59 : CC 59 JF_mm4 = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_66 : CC 66 C_rlf = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End Lib_handle_f_chk4.

(* [comment removed for export] *)
Module Lib_handle_f_chk5.

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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs Lib_handle_f_defs Lib_handle_f_s1 Lib_handle_f_s2 Lib_handle_f_s3 Lib_handle_f_s4 Lib_handle_f_s5 Lib_handle_f_s6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require od.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_handle_f_s9 Lib_handle_f_s9b Lib_handle_f_s10.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_handle_f_nodes Lib_handle_f_s8w.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oj.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Lib_handle_f_s7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.od.Lib_handle_f_s8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s9b OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Lib_handle_f_epi OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_nodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s8w OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oh.Lib_handle_f_nodes2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Lib_handle_f_fastcert OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oj.Lib_handle_f_chk0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import HFAddr.
Lemma cc_4 : CC 4 L1 = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_11 : CC 11 T_da = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_18 : CC 18 RJ = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_25 : CC 25 JF_sg = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_32 : CC 32 JF_trb = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_39 : CC 39 K3x = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_46 : CC 46 T_wdg = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_53 : CC 53 JF_mi4 = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_60 : CC 60 JR_sg4 = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_67 : CC 67 C_rlo = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End Lib_handle_f_chk5.

(* [comment removed for export] *)
Module Lib_handle_f_chk.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs"; "NPH"; "@Corelib.Init.Datatypes"; "bool"; "true"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_defs"; "FUEL_hf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_nodes"; "cutpcs_hfF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oh.Lib_handle_f_nodes2"; "cutsF2"; "exitsF2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ejcertA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs Lib_handle_f_defs Lib_handle_f_s1 Lib_handle_f_s2 Lib_handle_f_s3 Lib_handle_f_s4 Lib_handle_f_s5 Lib_handle_f_s6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require od.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_handle_f_s9 Lib_handle_f_s9b Lib_handle_f_s10.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_handle_f_nodes Lib_handle_f_s8w.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require oj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ol.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oc.Lib_handle_f_s7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.od.Lib_handle_f_s8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s9b OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o9.Lib_handle_f_epi OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_nodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_f_s8w OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oh.Lib_handle_f_nodes2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Lib_handle_f_fastcert OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oj.Lib_handle_f_chk0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ol.Lib_handle_f_chk1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ol.Lib_handle_f_chk2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.om.Lib_handle_f_chk3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.om.Lib_handle_f_chk4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.om.Lib_handle_f_chk5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.om.Lib_handle_f_chk6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.om.Lib_handle_f_chk7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import HFAddr.

Lemma ejcertF_ok : ltac2:(tb__ "0|0|
S3S1S9S4S0S5S6S0S7S8A7S2A3").
Proof.
  apply ejcertA_of_cuts; [exact hdr_ok2|].
  change (cuts_okE segs FUEL_hf cutpcs_hfF NPH PE 0 [Pre_hf; C_pro; C_pre; H; L1; L2; K; JR_co; JF_co; T_ms; T_pc; T_da; XA; T_dg; RW; JR_mi; JF_mi; C36; RJ; JR_fv; JF_fv; T_mcq; JR_mm; JF_mm; JR_sg; JF_sg; K1; K1Xg; K1Xb; JR_trg; JF_trg; JR_trb; JF_trb; T_tdg; K2; JR_rp; JF_rp; K3; K3m; K3x; TS; JR_ts; JF_ts; T_md; T_pgoR; T_pgiR; T_wdg; J; L14; T_g1; T_g2; T_g3_4; JR_mi4; JF_mi4; T_c4; JR_fv4; JF_fv4; T_m4; JR_mm4; JF_mm4; JR_sg4; JF_sg4; C_Ef2; C_Eo2; T_f5f; T_f5o; C_rlf; C_rlo; T_g3_0; C_T36] TG = true).
  simple apply cuts_okE_cons; [exact cc_0|].
  simple apply cuts_okE_cons; [exact cc_1|].
  simple apply cuts_okE_cons; [exact cc_2|].
  simple apply cuts_okE_cons; [exact cc_3|].
  simple apply cuts_okE_cons; [exact cc_4|].
  simple apply cuts_okE_cons; [exact cc_5|].
  simple apply cuts_okE_cons; [exact cc_6|].
  simple apply cuts_okE_cons; [exact cc_7|].
  simple apply cuts_okE_cons; [exact cc_8|].
  simple apply cuts_okE_cons; [exact cc_9|].
  simple apply cuts_okE_cons; [exact cc_10|].
  simple apply cuts_okE_cons; [exact cc_11|].
  simple apply cuts_okE_cons; [exact cc_12|].
  simple apply cuts_okE_cons; [exact cc_13|].
  simple apply cuts_okE_cons; [exact cc_14|].
  simple apply cuts_okE_cons; [exact cc_15|].
  simple apply cuts_okE_cons; [exact cc_16|].
  simple apply cuts_okE_cons; [exact cc_17|].
  simple apply cuts_okE_cons; [exact cc_18|].
  simple apply cuts_okE_cons; [exact cc_19|].
  simple apply cuts_okE_cons; [exact cc_20|].
  simple apply cuts_okE_cons; [exact cc_21|].
  simple apply cuts_okE_cons; [exact cc_22|].
  simple apply cuts_okE_cons; [exact cc_23|].
  simple apply cuts_okE_cons; [exact cc_24|].
  simple apply cuts_okE_cons; [exact cc_25|].
  simple apply cuts_okE_cons; [exact cc_26|].
  simple apply cuts_okE_cons; [exact cc_27|].
  simple apply cuts_okE_cons; [exact cc_28|].
  simple apply cuts_okE_cons; [exact cc_29|].
  simple apply cuts_okE_cons; [exact cc_30|].
  simple apply cuts_okE_cons; [exact cc_31|].
  simple apply cuts_okE_cons; [exact cc_32|].
  simple apply cuts_okE_cons; [exact cc_33|].
  simple apply cuts_okE_cons; [exact cc_34|].
  simple apply cuts_okE_cons; [exact cc_35|].
  simple apply cuts_okE_cons; [exact cc_36|].
  simple apply cuts_okE_cons; [exact cc_37|].
  simple apply cuts_okE_cons; [exact cc_38|].
  simple apply cuts_okE_cons; [exact cc_39|].
  simple apply cuts_okE_cons; [exact cc_40|].
  simple apply cuts_okE_cons; [exact cc_41|].
  simple apply cuts_okE_cons; [exact cc_42|].
  simple apply cuts_okE_cons; [exact cc_43|].
  simple apply cuts_okE_cons; [exact cc_44|].
  simple apply cuts_okE_cons; [exact cc_45|].
  simple apply cuts_okE_cons; [exact cc_46|].
  simple apply cuts_okE_cons; [exact cc_47|].
  simple apply cuts_okE_cons; [exact cc_48|].
  simple apply cuts_okE_cons; [exact cc_49|].
  simple apply cuts_okE_cons; [exact cc_50|].
  simple apply cuts_okE_cons; [exact cc_51|].
  simple apply cuts_okE_cons; [exact cc_52|].
  simple apply cuts_okE_cons; [exact cc_53|].
  simple apply cuts_okE_cons; [exact cc_54|].
  simple apply cuts_okE_cons; [exact cc_55|].
  simple apply cuts_okE_cons; [exact cc_56|].
  simple apply cuts_okE_cons; [exact cc_57|].
  simple apply cuts_okE_cons; [exact cc_58|].
  simple apply cuts_okE_cons; [exact cc_59|].
  simple apply cuts_okE_cons; [exact cc_60|].
  simple apply cuts_okE_cons; [exact cc_61|].
  simple apply cuts_okE_cons; [exact cc_62|].
  simple apply cuts_okE_cons; [exact cc_63|].
  simple apply cuts_okE_cons; [exact cc_64|].
  simple apply cuts_okE_cons; [exact cc_65|].
  simple apply cuts_okE_cons; [exact cc_66|].
  simple apply cuts_okE_cons; [exact cc_67|].
  simple apply cuts_okE_cons; [exact cc_68|].
  simple apply cuts_okE_cons; [exact cc_69|].
  apply cuts_okE_nil.
Qed.
End Lib_handle_f_chk.

