(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f1 Lib_tess_run2d Lib_tess_run2d_ex Lib_tess_polygon_chk.
From Stdlib Require FunctionalExtensionality.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ev ex f0.

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
Module Lib_handle_f_chk4.

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
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs"; "NPH"; "@Corelib.Init.Datatypes"; "bool"; "true"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_defs"; "FUEL_hf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_nodes"; "cutpcs_hfF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.et.Lib_handle_f_nodes2"; "cutsF2"; "exitsF2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ejcertA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ey.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_handle_f_s7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_handle_f_s8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s9b OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.es.Lib_handle_f_s10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.en.Lib_handle_f_epi OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_nodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ez.Lib_handle_f_s8w OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.et.Lib_handle_f_nodes2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e5.Lib_handle_f_fastcert OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ew.Lib_handle_f_chk0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ey.Lib_handle_f_chk1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f1.Lib_handle_f_chk2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fo.Lib_handle_f_chk3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fo.Lib_handle_f_chk4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fo.Lib_handle_f_chk5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f1.Lib_handle_f_chk6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f1.Lib_handle_f_chk7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import HFAddr.

Lemma ejcertF_ok : ltac2:(tb__ "0|0|
S3S1S9S4S0S5S6S0S7S8A7S2A3").
Proof.
  apply ejcertA_of_cuts; [exact hdr_ok2|].
  change (cuts_okE segs FUEL_hf cutpcs_hfF NPH PE 0 [Pre_hf; C_pro; C_pre; H; L1; L2; K; JR_co; JF_co; T_ms; T_pc; T_da; XA; T_dg; RW; JR_mi; JF_mi; C36; RJ; JR_fv; JF_fv; T_mcq; JR_mm; JF_mm; JR_sg; JF_sg; K1; K1Xg; K1Xb; JR_trg; JF_trg; JR_trb; JF_trb; T_tdg; K2; JR_rp; JF_rp; K3; K3m; K3x; TS; JR_ts; JF_ts; T_md; T_pgoR; T_pgiR; T_wdg; J; L14; T_g1; T_g2; T_g3_4; JR_mi4; JF_mi4; T_c4; JR_fv4; JF_fv4; T_m4; JR_mm4; JF_mm4; JR_sg4; JF_sg4; C_Ef2; C_Eo2; T_f5f; T_f5o; C_rlf; C_rlo; T_g3_0] TG = true).
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
  apply cuts_okE_nil.
Qed.
End Lib_handle_f_chk.

(* [comment removed for export] *)
Module Lib_tess_polygon_pf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "valuation"; "sobj"; "SLit"; "ss_facts"; "sprop"; "ss_objs"; "SVar"; "ss_next"; "cell"; "SAlu"; "holds"; "rw"; "DUnknown"; "eval"; "ob_base"; "obj_hi_of"; "obj_lo_of"; "obj_range"; "mkObj"; "sv_eqb"; "DZero"; "agree_below"; "ob_hi"; "ob_lo"; "soff"; "sprop_below"; "sprop_eqb"; "SPUle"; "swf"; "@Corelib.Init.Logic"; "eq"; "and"; "or"; "ex"; "True"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "leafA"; "la_state"; "ax_base"; "@Corelib.Init.Datatypes"; "list"; "prod"; "pair"; "nil"; "bool"; "cons"; "true"; "option"; "Some"; "fst"; "nat"; "snd"; "app"; "None"; "andb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "mul"; "pow"; "opp"; "sub"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "uval"; "bitem"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "smatchA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "entails_frA"; "call_checkA"; "call_checkPA"; "import_postA"; "J_ofPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fo.Lib_tess_polygon_pf"; "P0_pg"; "inFB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "PTrue"; "frinA"; "TPA"; "nd_below"; "tvinA"; "fbinA"; "ffinA"; "JA_pre"; "emeasA"; "ANone"; "JA"; "JLA"; "NDA"; "frozen"; "nodeIA"; "ok_frameKA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "axform"; "AXSplit"; "AXSelect"; "@Stdlib.Lists.List"; "In"; "forallb"; "nth_error"; "existsb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "AE_A"; "JL_pure"; "V_FL"; "J_pure_pre"; "L_stack_free"; "Pre_stack_free"; "JL_stack_free"; "JL_stack_malloc"; "J_memset_pre"; "J_stack_free_pre"; "J_stack_malloc_pre"; "L_memset"; "L_stack_malloc"; "Pre_memset"; "Pre_stack_malloc"; "alloc_contractsA"; "alloc_contractsA_ex"; "alloc_lawsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_geom"; "topG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_tess_polygon_states"; "pN"; "X_pg"; "gF"; "pSCR"; "O_pp2d"; "vF"; "vFL"; "pOUT"; "pPTS"; "Pre_pg"; "n12"; "o12"; "pNXT"; "pPRV"; "pRFX"; "P_inv"; "P_ok"; "pg_base_facts"; "spo"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_tess_polygon_cstates"; "ndF"; "objs_butlast"; "E_f8a0"; "E_ms0"; "T_f8a1"; "T_f8b1"; "T_s00_1"; "nd0"; "Pre_sf"; "reshapeA"; "E_f8a2"; "E_f8b0"; "E_f8b1"; "E_s00_0"; "E_s00_1"; "E_sc3_0"; "E_sc4_0"; "L_sf"; "O_pp2d_lit"; "T_f8a0"; "T_f8a2"; "T_f8b0"; "T_pure"; "T_s00_0"; "T_sc3_0"; "T_sc4_0"; "T_sm0"; "T_sm1"; "xf_shback"; "xf_shcall"; "E_f8a"; "E_f8a1"; "E_f8b"; "E_ms"; "E_ms1"; "E_r2_0"; "E_s00"; "E_sc3"; "E_sc3_1"; "E_sc4"; "E_sc4_1"; "E_sfI"; "E_sfI0"; "E_sfK"; "E_sfK0"; "E_sm0"; "T_r2_0"; "T_sc3_1"; "T_sc4_1"; "cutsE"; "xf_wback"; "C_body0"; "C_fin";
"C_pro0"; "C_pro2"; "C_s1"; "E_r2"; "E_r2_1"; "L_00"; "L_f8"; "L_ms"; "L_sm"; "Pre_00"; "Pre_f8"; "Pre_ms"; "Pre_sm"; "R_f8a"; "R_f8b"; "R_ms"; "R_r2"; "R_s00"; "R_sc3"; "R_sc4"; "R_sfI"; "R_sfK"; "R_sm"; "T_r2"; "T_sc3"; "T_sc4"; "T_sfI"; "T_sfK"; "exitsE"; "s_f8a"; "s_f8b"; "s_ms"; "s_r2"; "s_s00"; "s_sc3"; "s_sc4"; "s_sfI"; "s_sfK"; "s_sm"; "sel_last"; "shc_f8a"; "shc_ms"; "xf_r2back"; "xf_r2call"; "z0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fo.Lib_tess_polygon_pf.Sum"; "baseF"; "extraX"; "extraO"; "Posts_pg"; "basez"; "robjs_checkP"; "in_callers"; "JL"; "extra_tab"; "extz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "call_linkP"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "wsub_get"; "rho_absorb"; "rho_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS"; "xrs_checkL"; "shadow_release_stateA"; "shobj"; "shadow_reopen_stateA"; "flag_carve_stateA"; "robjs_checkF"; "frame_open_stateA"; "robj_ownframe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_tess_scale2d"; "Pre_sc"; "P_sc"; "Posts_sc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "T_ok"; "tvd"; "tvz"; "FBx"; "remove_nth"; "T0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "T_afterA"; "ccount"; "call_checkTA"; "is_shadowZ"; "payA"; "robj_stackA"; "site_okA"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SLL"; "ALU_SRL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e1.Lib_tess_run2d_states"; "Pre_r2"; "Posts_r2"; "P_ret"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA"; "infrFF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "pclMA"; "FFx"; "T_afterA3"; "xrs_okL"; "robjs_okL"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Asan_set_shadow_iface"; "L_set_shadow"; "Pre_set_shadow"; "set_shadow_contractA"; "set_shadow_contractA_ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "SHADOW_OFF"; "fs_frame_size"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "jnodeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_tess_polygon_states.TessPolygonAddr"; "asan_memset_ret"; "pg_ms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3"; "import_okPA3"; "import_postA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR"; "robjs_okF"; "xrs_ok47"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAS AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.JcertCutA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Asan_set_shadow_iface Lib_tess_scale2d.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_tess_run2d Lib_tess_run2d_ex Lib_tess_polygon_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_tess_polygon_chk.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Asan_set_shadow_iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_tess_scale2d OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e1.Lib_tess_run2d_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_tess_run2d OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_tess_run2d_ex OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_tess_polygon_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_tess_polygon_cstates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eh.Lib_tess_polygon_chk0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_tess_polygon_chk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import TessPolygonAddr.

Definition inFB (FB : list (Z * Z)) (x n : Z) : Prop := ltac2:(tb__ "0|0|
S23S0S0S23S0S0S21S6aS2dS0S0A2S2eS0S0R2R1A4VFB;A3S21S3cR2Vx;A2S3cS3dVx;Vn;A2S3dR2R1A2A2A2A2Lm;A2Lb;A2").

Definition P0_pg (FB : list (Z * Z)) (FF : list (Z * Z * Z)) (r : valuation) : Prop := ltac2:(tb__ "0|4|
S21S20S36S123Z6S10bS2dS2dS0S0A2M0S0A2G0S35G0S0A2VFF;A4A2U0A3S21S130VFF;S44Q40M1SeVr;PcA2A2Z48A3S21S130VFF;S44G1SeVr;PdA2A2Z18A3S21S54VFB;S44G1SeVr;PfA2A2S3fZcM2S44G1SeVr;PeA2A2M3A2A3S21S54VFB;S44G1SeVr;P10A2A2S3fG2S42G3Z2A2A2A3S54VFB;S44G1SeVr;P11A2A2S44G1SeVr;P12A2A2A3A2A2A2A2A2").

Lemma T_sm0_eq : ltac2:(tb__ "0|1|
S20S26S122S7cS6eZ6M0A2Sc5Sf3Se3S7aS6eG0A2A5Sb2A3"). Proof. vm_compute. reflexivity. Qed.
Lemma T_sm1_eq : ltac2:(tb__ "0|0|
S20S33S26A1S66Sb2S31S67S69Sf4Sb2U3A2A1S2fS67A1A3A2S34S26Sb3A2A3"). Proof. vm_compute. reflexivity. Qed.
Lemma C_pro0_eq : ltac2:(tb__ "0|1|
S20S26S117Sb3S99Sb3A1S38S2dS2S2A2M0S84S2fG0A1A3P6eS13eZ6A1A5ScdA3"). Proof. vm_compute. reflexivity. Qed.
Lemma E_f8a0_objs : ltac2:(tb__ "0|0|
S20S2cS4A1S8S27S9aA1A1S38S4S99S9aA1S31S4S113S85Z0Z200Sf5S17A5S2fS4A1A3A3A3"). Proof. vm_compute. reflexivity. Qed.
Lemma E_f8a1_eq : ltac2:(tb__ "0|0|
S20S26S112S9aS99S9aA1P6eS2fS2dS0S0A2A1A4Sb7A3"). Proof. vm_compute. reflexivity. Qed.
Lemma E_f8a2_eq : ltac2:(tb__ "0|0|
S20S26S114Sb7S84S85Z4Z104A5Sa2A3"). Proof. vm_compute. reflexivity. Qed.
Lemma E_f8a_eq : ltac2:(tb__ "0|0|
S20S33S26A1S66Sa2Sb5Sa2A1A2S34S26Sb6A2A3"). Proof. vm_compute. reflexivity. Qed.
Lemma T_f8a0_eq : ltac2:(tb__ "0|1|
S20S26S122S139S6eZf8M0A2Sb6SeaSdaS138G0A1A5SabA3"). Proof. vm_compute. reflexivity. Qed.
Lemma T_f8a1_eq : ltac2:(tb__ "0|0|
S20S33S26A1S66SabSb4SabA1A2S34S26S9cA2A3"). Proof. vm_compute. reflexivity. Qed.
Lemma T_f8a1_objs : ltac2:(tb__ "0|0|
S20S2cS4A1S8S27S9cA1A1S38S4S99S9cA1S31S4S113S85Z4Z104S2fSbA1SfA5S2fS4A1A3A3A3"). Proof. vm_compute. reflexivity. Qed.
Lemma T_f8a2_eq : ltac2:(tb__ "0|0|
S20S26S112S9cS99S9cA1P6eS2fS2dS0S0A2A1A4SacA3"). Proof. vm_compute. reflexivity. Qed.
Lemma C_pro2_eq : ltac2:(tb__ "0|0|
S20S26S114SacS28SacA1S85Z104Z114A5SceA3"). Proof. vm_compute. reflexivity. Qed.

Lemma E_ms0_objs : ltac2:(tb__ "0|0|
S20S2cS4A1S8S27S9bA1A1S38S4S99S9bA1S31S4S113S85Z104Z114Sf6SfA5S2fS4A1A3A3A3"). Proof. vm_compute. reflexivity. Qed.
Lemma E_ms1_eq : ltac2:(tb__ "0|0|
S20S26S112S9bS99S9bA1P6eS2fS2dS0S0A2A1A4SbaA3"). Proof. vm_compute. reflexivity. Qed.
Lemma E_ms_eq : ltac2:(tb__ "0|0|
S20S33S26A1S66SbaS31S67S68U7S5Z10A1A2S2fS67A1A3A2S34S26Sb9A2A3"). Proof. vm_compute. reflexivity. Qed.
Lemma C_body0_eq : ltac2:(tb__ "0|0|
S20S26S122S7bS145A1Sb9SecSdcS79S144A1A5ScbA3"). Proof. vm_compute. reflexivity. Qed.
Lemma E_s00_1_eq : ltac2:(tb__ "0|0|
S20S26S114Sa5S28Sa5A1S85Z4Z104A5Sa6A3"). Proof. vm_compute. reflexivity. Qed.
Lemma E_s00_eq : ltac2:(tb__ "0|0|
S20S33S26A1S66Sa6Sb5Sa6A1A2S34S26SbcA2A3"). Proof. vm_compute. reflexivity. Qed.
Lemma T_s00_0_eq : ltac2:(tb__ "0|1|
S20S26S122S139S6eZ0M0A2SbcSeeSdeS138G0A1A5SafA3"). Proof. vm_compute. reflexivity. Qed.
Lemma T_s00_1_eq : ltac2:(tb__ "0|0|
S20S33S26A1S66SafSb4SafA1A2S34S26S9eA2A3"). Proof. vm_compute. reflexivity. Qed.
Lemma T_s00_1_objs : ltac2:(tb__ "0|0|
S20S2cS4A1S8S27S9eA1A1S38S4S99S9eA1S31S4S113S85Z4Z104S2fSbA1S17A5S2fS4A1A3A3A3"). Proof. vm_compute. reflexivity. Qed.
Lemma C_s1_eq : ltac2:(tb__ "0|0|
S20S26S112S9eS99S9eA1P6eS2fS2dS0S0A2A1A4ScfA3"). Proof. vm_compute. reflexivity. Qed.
Lemma E_f8b1_eq : ltac2:(tb__ "0|0|
S20S26S114Sa3S28Sa3A1S85Z4Z104A5Sa4A3"). Proof. vm_compute. reflexivity. Qed.
Lemma E_f8b_eq : ltac2:(tb__ "0|0|
S20S33S26A1S66Sa4Sb5Sa4A1A2S34S26Sb8A2A3"). Proof. vm_compute. reflexivity. Qed.
Lemma T_f8b0_eq : ltac2:(tb__ "0|1|
S20S26S122S139S6eZf8M0A2Sb8SebSdbS138G0A1A5SadA3"). Proof. vm_compute. reflexivity. Qed.
Lemma T_f8b1_eq : ltac2:(tb__ "0|0|
S20S33S26A1S66SadSb4SadA1A2S34S26S9dA2A3"). Proof. vm_compute. reflexivity. Qed.
Lemma T_f8b1_objs : ltac2:(tb__ "0|0|
S20S2cS4A1S8S27S9dA1A1S38S4S99S9dA1S31S4S113S85Z4Z104S2fSbA1SfA5S2fS4A1A3A3A3"). Proof. vm_compute. reflexivity. Qed.
Lemma C_fin_eq : ltac2:(tb__ "0|0|
S20S26S112S9dS99S9dA1P6eS2fS2dS0S0A2A1A4SccA3"). Proof. vm_compute. reflexivity. Qed.
Lemma E_sc3_0_p2d : ltac2:(tb__ "0|0|
S20S33S4A1S6cS4S8S27Sa7A1A1U7A3S34S4S87S2fSbA1A1A2A3"). Proof. vm_compute. reflexivity. Qed.
Lemma E_sc3_1_eq : ltac2:(tb__ "0|0|
S20S26Sa1Sa7U7SaaZ3A1A3SbeA3"). Proof. vm_compute. reflexivity. Qed.
Lemma E_sc3_eq : ltac2:(tb__ "0|0|
S20S33S26A1S66SbeS31S67S68U1S5N10A1A2S2fS67A1A3A2S34S26SbdA2A3"). Proof. vm_compute. reflexivity. Qed.
Lemma T_sc3_0_eq : ltac2:(tb__ "0|0|
S20S26SaeS119SbdSefSdfS11aA5Sb0A3"). Proof. vm_compute. reflexivity. Qed.
Lemma T_sc3_0_p2d : ltac2:(tb__ "0|0|
S20S33S4A1S6cS4S8S27Sb0A1A1U1A3S34S4S15S86S5Z0A1S5Z30A1S2fSbA1SfA5A2A3"). Proof. vm_compute. reflexivity. Qed.
Lemma T_sc3_1_eq : ltac2:(tb__ "0|0|
S20S26Sa1Sb0U1S87S2fSbA1A1A3Sc7A3"). Proof. vm_compute. reflexivity. Qed.
Lemma T_sc3_eq : ltac2:(tb__ "0|0|
S20S33S26A1S66Sc7ScaA2S34S26Se5A2A3"). Proof. vm_compute. reflexivity. Qed.
Lemma E_sc4_0_p2d : ltac2:(tb__ "0|0|
S20S33S4A1S6cS4S8S27Sa8A1A1U7A3S34S4S87S2fSbA1A1A2A3"). Proof. vm_compute. reflexivity. Qed.
Lemma E_sc4_1_eq : ltac2:(tb__ "0|0|
S20S26Sa1Sa8U7SaaZ4A1A3Sc0A3"). Proof. vm_compute. reflexivity. Qed.
Lemma E_sc4_eq : ltac2:(tb__ "0|0|
S20S33S26A1S66Sc0S31S67S68U1S5N10A1A2S2fS67A1A3A2S34S26SbfA2A3"). Proof. vm_compute. reflexivity. Qed.
Lemma T_sc4_0_eq : ltac2:(tb__ "0|0|
S20S26SaeS119SbfSf0Se0S11aA5Sb1A3"). Proof. vm_compute. reflexivity. Qed.
Lemma T_sc4_0_p2d : ltac2:(tb__ "0|0|
S20S33S4A1S6cS4S8S27Sb1A1A1U1A3S34S4S15S86S5Z0A1S5Z40A1S2fSbA1SfA5A2A3"). Proof. vm_compute. reflexivity. Qed.
Lemma T_sc4_1_eq : ltac2:(tb__ "0|0|
S20S26Sa1Sb1U1S87S2fSbA1A1A3Sc8A3"). Proof. vm_compute. reflexivity. Qed.
Lemma T_sc4_eq : ltac2:(tb__ "0|0|
S20S33S26A1S66Sc8ScaA2S34S26Se6A2A3"). Proof. vm_compute. reflexivity. Qed.
Lemma E_r2_eq : ltac2:(tb__ "0|0|
S20S33S26A1S66SbbSf8A2S34S26Sd1A2A3").     Proof. vm_compute. reflexivity. Qed.
Lemma T_r2_0_eq : ltac2:(tb__ "0|0|
S20S26SaeS12dSd0SedSddS12fA5Sc6A3"). Proof. vm_compute. reflexivity. Qed.
Lemma T_r2_eq : ltac2:(tb__ "0|0|
S20S33S26A1S66Sc6Sf7A2S34S26Se4A2A3"). Proof. vm_compute. reflexivity. Qed.
Lemma E_sfI_eq : ltac2:(tb__ "0|0|
S20S26S115Sc2P78A2Sc1A3"). Proof. vm_compute. reflexivity. Qed.
Lemma E_sfK_eq : ltac2:(tb__ "0|0|
S20S26S115Sc4P78A2Sc3A3"). Proof. vm_compute. reflexivity. Qed.
Lemma T_sfI_eq : ltac2:(tb__ "0|1|
S20S26S133S73S6eZ6M0A2Sc1Sf1Se1S72S6eG0A2S84A6Se7A3"). Proof. vm_compute. reflexivity. Qed.
Lemma T_sfK_eq : ltac2:(tb__ "0|1|
S20S26S133S73S6eZ6M0A2Sc3Sf2Se2S72S6eG0A2S84A6Se8A3"). Proof. vm_compute. reflexivity. Qed.

Section Sum.
Let HTOP : InitState.segs_top segs <= IMG_HI := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eb.Lib_arena_alloc.HTOP_ok.
Variable AInv : ltac2:(tb__ "0|0|
S80S3S2cS43Q40A1A1S96OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
S7fS3bVAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S0S143VCST;R1A2S21S3cZ0R2A2S3eR2S13cA2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S0S143VXGL;R1A2S21S3cZ0R2A2S3eR2S13cA2A2F_;Fa;").
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
S31S2dS26S4cA2M0S2eS26S4cS92S105S9fA1M1A4S31G0S2eS26S4cS93G1A4S2fG0A1A3A3").
Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S60VAInv;VCST;VXGL;S4bVKc;Vrho0;S53VFB;VFF;A2VFB;VFF;VBX;S56Vnd;Ac").
Let nI : ltac2:(tb__ "0|0|
S2dS26S55A2S142Fn;") := ltac2:(tb__ "0|0|
S64VAInv;VCST;VXGL;S4bVKc;Vrho0;S53VFB;VFF;A2VFB;VFF;VBX;S56Ab").
Let Q (tp0 : list word) : assn := ltac2:(tb__ "0|0|
S4dS3bS4bVrho0;Vtp0;S101A5").

Definition baseF (F : list sprop) : bool := ltac2:(tb__ "0|0|
S6bS7S7S6dS7S1dR1A1VF;A3Lp;S94A3").

Definition frameB (F : list sprop) : bool := ltac2:(tb__ "0|0|
S6dS7S1dS1eScS12aS88S5Z1000A1A3S9P1eA1A2A1VF;A3").

Record basez (rho : valuation) : Prop := BZ {
  bz_sp : uval rho (SVar 30) + 2624 <= uval rho (SVar 10) <= 2 ^ 47;
  bz_D : uval rho (SVar V_DEPTH) = uval rho (SVar V_DEPTH) - 0 /\ 2 ^ 64 - 2 ^ 40 <= uval rho (SVar V_DEPTH) <= 2 ^ 64 - PG_DEPTH;
  bz_win : uval rho (SVar 30) <= uval rho (SVar 10) - 320 + (uval rho (SVar V_DEPTH) - 2 ^ 64);
  bz_n : 3 <= uval rho pN <= 2 ^ 20;
  bz_res : uval rho (SVar 13) + 24 <= 140737479966720;
  bz_scr : 4096 <= uval rho pSCR /\ uval rho (SVar 18) <= 2 ^ 26 /\ uval rho pSCR + uval rho (SVar 18) <= 140737479966720;
  bz_need : 16 * uval rho pN + 2 * uval rho A16 + (uval rho pN + 7) / 8 <= uval rho (SVar 18);
  bz_a16 : uval rho A16 = 4 * uval rho pN + 15 - (4 * uval rho pN + 15) mod 16;
  bz_top : aceil <= uval rho (SVar 30) <= 140737479966720 }.

Lemma uval_spo : ltac2:(tb__ "0|2|
S3S0S21S3cZ0S41R1A1M0A2S3cG0S45R2S9PaA1M1A2A2A2S20S0S45R3S95R2A1A2S3dS45R3G1A2R2A2A3F_;Fk;Frho;").
Proof.
  intros rho k Hk. unfold spo, uval in *. rewrite U_add, U_lit. pose proof (U_range (eval rho (SVar 10))) as R. unfold M64v in *.
  set (x := bv_unsigned (eval rho (SVar 10))) in *. rewrite Zplus_mod_idemp_r. apply Z.mod_small. lia.
Qed.

Lemma basez_of : ltac2:(tb__ "0|0|
S3S2cS7A1S10aS7SdR2A1R1A3S20S30SfeR2A1S32A3S102R4A1F_;F_;FF;Frho;").
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
  assert (EP : uval rho psp = uval rho (SVar 10) - 320) by (unfold psp; apply uval_spo; lia). rewrite EP in W2.
  assert (EA : uval rho (SAlu ALU_ADD psp (SVar V_DEPTH)) = uval rho (SVar 10) - 320 + (uval rho (SVar V_DEPTH) - 2 ^ 64)).
  { unfold uval at 1. rewrite U_add. change (bv_unsigned (eval rho psp)) with (uval rho psp). change (bv_unsigned (eval rho (SVar V_DEPTH))) with (uval rho (SVar V_DEPTH)).
    rewrite EP. unfold M64v in *. unfold H63v in *.
    replace (uval rho (SVar 10) - 320 + uval rho (SVar V_DEPTH)) with ((uval rho (SVar 10) - 320 + (uval rho (SVar V_DEPTH) - 2 ^ 64)) + 1 * 2 ^ 64) by lia.
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
S3S108S4bVrho0;R1A3S53VFB;VFF;Vrho0;A3S21S20S36S123Z6S10bS2dS2dS0S0A2M0S0A2G0S35G0S0A2VFF;A4A2U0A3S21S130VFF;S45R3S9PcA1A2Z48A3S21S130VFF;S45R3S9PdA1A2Z18A3S21S54VFB;S45R3S8bA2S3fZcM1S45R3S83A2M2A2A3S21S54VFB;S45R3S8aA2S3fG1S42G2Z2A2A2A3S54VFB;S45R3S86A2S45R3S9P12A1A2A3A2A2A2A2A2F_;F_;Frho;").
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
S31S2dS2dS2S2A2M0S2A2M1S2eG0S2S2eS2S2S9PcA1S5Z0A1M2A4S5Z48A1A4S31G1S2eG0S2S2eS2S2S9PdA1M3G2A4M4S5Z18A1M5A4S31G1S2eG0S2G4S5Z10A1M6A4S31G1S2eG0S2S2eS2S2G3G6A4G5A4S31G1S2eG0S2S2eS2S2S8bG2A4S8dA4S31G1S2eG0S2S2eS2S2S8aG2A4S8eA4S31G1S2eG0S2S2eS2S2S86G2A4ScS12bS83S5Z4A1A3A4S31G1S2eG0S2S2eS2S2S8fG2A4ScS12bS83S5Z2A1A3M7A4S31G1S2eG0S2S2eS2S2S90G2A4G7A4S31G1S2eG0S2S2eS2S2S91G2A4ScS12cScS12aS83S5Z7A1A3S5Z3A1A3A4S2fG1A1A3A3A3A3A3A3A3A3A3A3").
Definition extraO (o : sobj) : bool := ltac2:(tb__ "0|3|
S6dS2dS2dS2S2A2M0S2A2M1G1S3aS3aS16S11Vo;A1S35S2S2S35G0S2R1A3M2A3A2S16S1aVo;A1S37S2S2G2A3A2A2S16S19Vo;A1S37G0S2R1A3A2A2Lt;S106A3").
Definition extraX_tab : list (sv * sv) := ltac2:(tb__ "0|2|
S31S2dS2S2A2M0S2eS2S2S9PcA1S5Z48A1A4S31G0S2eS2S2S9PdA1S5Z18A1A4S31G0S2eS2S2S8bS8dA4S31G0S2eS2S2S8aS8eA4S31G0S2eS2S2S86ScS12bS83S5Z4A1A3A4S31G0S2eS2S2S8fScS12bS83S5Z2A1A3M1A4S31G0S2eS2S2S90G1A4S31G0S2eS2S2S91ScS12cScS12aS83S5Z7A1A3S5Z3A1A3A4S2fG0A1A3A3A3A3A3A3A3A3").
Definition extraX (r : sv * sv) : bool := existsb (xr_eqb r) extraX_tab.

Definition in_callers (rho : valuation) (a : Z) : Prop := ltac2:(tb__ "0|7|
S22S21S3cS45Vrho;S9PcA1A2M0Va;A2S3eVa;S3dG0Z48A2A2A2S22S21S3cS45Vrho;S9PdA1A2M1Va;A2S3eVa;S3dG1Z18A2A2A2S22S21S3cS45Vrho;S8bA2M2Va;A2S3eVa;S3dG2S3fZcM3S45Vrho;S83A2M4A2A2A2A2S22S21S3cS45Vrho;S8aA2M5Va;A2S3eVa;S3dG5S3fG3S42G4Z2A2A2A2A2A2S21S3cS45Vrho;S86A2M6Va;A2S3eVa;S3dG6S45Vrho;S9P12A1A2A2A2A2A2A2A2A2").

Lemma uval_add_neglit : ltac2:(tb__ "0|0|
S3S2S0S3eR1Z0A2S3cS41R2A1S45R4R3A2A2S3cS41S40Z2Z3fA2A1R3A2S20S0S45R6ScS12aR5S5R4A1A3A2S3dS45R6R5A2R4A2A3F_;F_;F_;Fk;Fa;Frho;").
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
S3S102R1A1S107R2A1F_;Frho;").
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
S3S4S0S102R3A1S20S30S100R3A1S32A3S21S3cS35S0S0S14R5R4A2M0A3R3A2S3eR3S37S0S0G0A3A2A2S104R6R4A2F_;F_;F_;Fa;Fo;Frho;").
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
S3S2dS2S2A2S0S102R3A1S20S30SffR3A1S32A3S21S3cS45R5S35S2S2R4A3A2M0R3A2S3eR3S3dG0S45R5S37S2S2R4A3A2A2A2A2S104R6R4A2F_;F_;F_;Fa;Fr;Frho;").
Proof.
  intros rho r a BZ HE Hr. pose proof (extz_of rho BZ) as [E12 Eo12 E16 E4 Er EN EP ERF EA EF]. destruct BZ as [Bsp BD Bwin Bn Bres Bscr Bneed Ba16 Btop].
  rewrite aceil_val in *. pose proof (Z.mod_pos_bound (4 * uval rho pN + 15) 16 ltac:(lia)) as M16B. assert (HD8 : 0 <= (uval rho pN + 7) / 8) by (apply Z.div_pos; lia).
  unfold extraX in HE. apply existsb_exists in HE as (t & Hin & Heq). apply xr_eqb_sound in Heq. subst t.
  unfold in_callers. cbn [extraX_tab In] in Hin.
  destruct Hin as [E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]; destruct r as [b l]; injection E as <- <-; cbn [fst snd] in Hr;
    rewrite ?uval_lit in Hr by lia; rewrite ?E12, ?Eo12, ?E16, ?E4, ?Er, ?EN, ?EP, ?ERF in Hr; unfold pPTS, pOUT, pSCR in *; lia.
Qed.

Lemma in_callers_pclMA : ltac2:(tb__ "0|0|
S3S0S2cS2dS2S2A2A1S2cS2dS2dS2S0A2S2A2A1S108S4bVrho0;R4A3S53VFB;VFF;Vrho0;A3S104R6R5A2S131VCST;Vrho0;S11fVFB;R7R5A3S132VFF;R7R4A3R6A5F_;F_;F_;Ffrs;Fkept;Fa;Frho;").
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
S6bS4S4S30S30L_;M0S127Vfacts;R1A2S32G0S118Vfr;U0Vskip;R1A4S32S100R1A1X30x2X30x2Lo;VR;A3").

Ltac top_rng H := match type of H with context [topG ?G] => let TG := fresh "TG" in pose proof (topG_range G) as TG end.

Lemma robjs_checkP_sound : ltac2:(tb__ "0|4|
S80S3S2cS7A1S2cS2dS2S2A2A1S2cS2dS2dS2S0A2S2A2M0A1M1S33S36A1M2S2cS4A1S3S2cS43Q40A1A1S96VAInv;RaR3R2R1A4S10aS7SdRaA1R9A3S20S30SfeRaA1S32A3S108S4bVrho0;RcA3S53VFB;VFF;Vrho0;A3S11cReS121Vrho0;A1A2S57VFF;R10RfRcA4S20S30S103RfRdRcRbA4S32A3G2G1Lskip;RdS36S120G0R1RfA3Li;ReX33x2G1S4S0S6aS4R2RfA3S21S3cS35S0S0S14R15R3A2M3A3R2A2S3eR2S37S0S0G3A3A2A2S131VCST;Vrho0;S11fVFB;R16R14A3S132VFF;R16R5A3R3A5F_;F_;Fa;Fo;Tfrs;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FR;Fskip;Ffr;Ftv;Ffacts;Frho;FAi;").
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
S80S3S2cS43Q40A1A1S96S2cS2dS0S0A2M0A1S2cS2dG0S0A2A1S0VAInv;R7R6R5R4A4S5bR4R8A2S5cR4R9A2S131VCST;Vrho0;R6R5R4A5S21S3cZ0R5A2S3eR5S40Z2Z2fA2A2A2F_;F_;F_;F_;Fa;FFFc;FFBc;Fmd1;Ftp1;Frho1;FAi;").
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
S80S3S2cS7A1S2cS2dS2S2A2A1M0S2cS2dS2dS2S0A2S2A2M1A1M2S33S36A1M3S2cS4A1G0S3S2cS43Q40A1A1S96VAInv;RbR3R2R1A4S10aS7SdRbA1RaA3S20S30SfeRbA1S32A3S108S4bVrho0;RdA3S53VFB;VFF;Vrho0;A3S58Vrho0;R10A2S11cR10S82S81R11A1A1A2S5aVFB;R12R11RfA4S11dR12R10A2S11eR13R11A2S57VFF;R15R14R11A4S20S30S111VXGL;R14R13R12R11R10SffRfA8S32A3S134VCST;VXGL;Vrho0;VFB;VFF;R16R14G3G2Lskip;R12S36S120G1R1R14A3Li;R13X33x2R10A9F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FX;Fobjs;Fskip;Ffr;Ftv;Ffacts;Frho;FAi;").
Proof.
  intros Ai rho facts tv fr skip objs X rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HN HD HZ HFR Hchk.
  apply (xrs_checkL_sound segs AInv CST XGL ALA rho0 FB FF Ai rho facts tv fr skip objs extraX X rho1 tp1 md1 HM HF (T_ok_T0 rho0 _ Ai HT HTK) HN HD HZ HFR Hchk).
  intros r a Hr HE Ha. left. apply in_callers_pclMA; [exact Hav | exact HP0 |]. eapply extraX_sound; [eapply basez_of; [exact HF | exact HB] | exact HE | exact Ha].
Qed.

Lemma robjs_okF_site : ltac2:(tb__ "0|0|
S80S3S2cS7A1S2cS2dS2S2A2A1S2cS2dS2dS2S0A2S2A2A1S2cS4A1S3S2cS43Q40A1A1S96VAInv;R9R3R2R1A4S10aS7SdR9A1R8A3S20S30SfeR9A1S32A3S108S4bVrho0;RbA3S53VFB;VFF;Vrho0;A3S58Vrho0;ReA2S11cReS82S81RfA1A1A2S5aVFB;R10RfRdA4S11dR10ReA2S11eR11RfA2S57VFF;R13R12RfA4S20S30S116R12R11R10S39S36A1S100RfA6S32A3S148VCST;Vrho0;VFB;VFF;R14R12R11R10A8F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FR;Ffr;Ftv;Ffacts;Frho;FAi;").
Proof.
  intros Ai rho facts tv fr R rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HN HD HZ HFR Hchk o a Ho Hr.
  apply (robjs_checkF_sound segs AInv CST ALA rho0 FB FF Ai rho facts tv fr None extraO R rho1 tp1 md1 HM HF (T_ok_T0 rho0 _ Ai HT HTK) HN HD HZ HFR Hchk) with (o := o); [|exact Ho|exact Hr].
  intros o' a' Ho' HE Hr'. left. apply in_callers_pclMA; [exact Hav | exact HP0 |]. eapply extraO_sound; [eapply basez_of; [exact HF | exact HB] | exact HE | exact Hr'].
Qed.

Lemma frozen_stableA' : ltac2:(tb__ "0|0|
S1S1S55S3S140S4bR3A2S20S30S59R4R3A2S32A3S4aS3bR6S63VAInv;VCST;VXGL;S4bVKc;Vrho0;S53VFB;VFF;A2VFB;VFF;VBX;S56R4R3AdA3F_;F_;Frho;Fnd;Fm;Fn;").
Proof.
  intros n m nd rho Hm Hb r r' tp tr md md' _ Hme (Ai & kc & HJ). exists Ai, kc.
  eapply (JAi_stable segs AInv CST XGL NF Kc rho0 (P0_pg FB FF) FB FF BX PTrue HKc ALA m nd Ai kc rho rho tp tr md md'); [exact Hm | exact Hb | apply agree_below_refl | exact Hme | exact HJ].
Qed.

Lemma payA_nil : ltac2:(tb__ "0|2|
S2cS7A1S126S4bVrho0;S53VFB;VFF;A2R1S5Z0M0A1G0S2fS46A1M1G1A8Ffacts;").
Proof.
  intros facts. split; [reflexivity|]. split; [lia|]. intros rho HF _ _ Hn. unfold pay_sem. rewrite uval_lit by lia. split; [cbn; lia|]. split; [cbn; lia | exact Hn].
Qed.

Section X.
Variable TR : assn -> assn -> Prop.
Variable FAM : ltac2:(tb__ "0|0|
S0S2cS43Q40A1A1SfaF_;F_;").
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S48S26S3S2cS43Q40A1A1SfaS10aS7SdR3A1S6S27R4A1A1A3VTR;S47S3bR6R5R4R3A5R2A2M0F_;G0F_;FQ;Ftp;Frho;FS;FJ;").
Hypothesis TR_ex : forall (T : Type) (J : T -> jpredA) S rho tp (Q : assn),
  (forall x, TR (SPA segs (J x) S rho tp) Q) -> TR (SPA segs (fun r p t m => exists x, J x r p t m) S rho tp) Q.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
SfaSfaSfaSfbR3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_false : ltac2:(tb__ "0|0|
SfaSfaSfbS25R3R1A1A1Fw;VTR;R3R2A2F_;FQ;FP;").
Hypothesis TR_exw : forall (T : Type) (P : T -> assn) (Q : assn), (forall a, TR (P a) Q) -> TR (fun w => exists a, P a w) Q.
Hypothesis TR_callP : ltac2:(tb__ "0|5|
S48S48S26S26S10cS2cS4A1M0S2cS2dS26S4cA2M1A1S2cS2dS2S2A2M2A1SfaS3S2cS43Q40A1A1M3G2S6aG2R1R5A3S6aG2R2S28RbA1A3F_;Fr;S20S33G0A1S4eRaR9R8A3S34G0R7A2A3S20S30S50RbRaR9R8S10bG1S26S35S26S4cA2R7A4A5S32A3S3G3VTR;S47S3bRfRdR2R1A5S4dS3bSaS27RdA1A1R2R1RaA5A2Ftp1;Frho1;S2cS97A1M4S129S96S49S3bR9R8R10S2eG4S136R3S137R2R1A2A4A5R13RaR9R4R2A4R13S10fS10eRbRfS110R3RaR4A3A3R10A2RaR5R3A4F_;F_;Fmd;Fms;Ftr;S26S4cG4S129S96S3G3G4S129S96S6aG1S2eS26S4cRaR9A4R14A3S49S3bR12R11R19S2eG4S136R9S137R8R7A2A4A5R1cR13R12RaR8A4S108SaS27R1aA1A1S10fS10eR14R18S110R9R13RaA3A3R19A2R8A3S49S3bR9R8ReS2eG4S136R7S137R6R5A2A4A5ReS10fS10eR16R1aS110RbR15RcA3A3R1bA2R15RaR9R8R6A6S21S146R17S110RcR16RdA3R1bR1cR1dR10R1eR19RbA9S3S109R18S110RdR17ReA3R1cR1dS27R1eA1S27R1fA1S27R11A1R1RcA9VTR;S47S3bS52R11S10fS10eR19R1dS110ReR18RfA3A3R1eA2R18RdRcA5S147R1eR1fR12R20R1dR1bA6R2RcA5R1aA2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S47S3bR11RfR8R7A5R9A2F_;F_;F_;F_;F_;F_;Ftp;Frho;FQ;FXk;FPosts;FR;Fs;FPre;FC;FJp;FJ;").

Hypothesis CSM : ltac2:(tb__ "0|2|
S80S3S2cS43Q40A1A1VTR;S47S3bS78VAInv;Z6M0R3VKc;A4Sd9R2R1A5S4dS3bS4bR2R1S31S2dS26S4cA2M1S2eS26S4cSd5S75VAInv;VCST;VXGL;G0R3VKc;A6A4S2fG1A1A3A5A2Ftp1;Frho1;FAi;").
Hypothesis CSF : ltac2:(tb__ "0|2|
S80S3S2cS43Q40A1A1VTR;S47S3bS77VAInv;Z6M0R3VKc;A4Sa0R2R1A5S4dS3bS4bR2R1S31S2dS26S4cA2M1S2eS26S4cSa9S74VAInv;VCST;VXGL;G0R3VKc;A6A4S2fG1A1A3A5A2Ftp1;Frho1;FAi;").
Hypothesis CF8 : ltac2:(tb__ "0|1|
S80S3S2cS43Q40A1A1VTR;S47S3bS71VAInv;R3VKc;A3Sd7R2R1A5S4dS3bS4bR2R1S31S2dS26S4cA2M0S2eS26S4cSd3S6fVAInv;VCST;VXGL;R3VKc;A5A4S2fG0A1A3A5A2Ftp1;Frho1;FAi;").
Hypothesis C00 : ltac2:(tb__ "0|1|
S80S3S2cS43Q40A1A1VTR;S47S3bS71VAInv;R3VKc;A3Sd6R2R1A5S4dS3bS4bR2R1S31S2dS26S4cA2M0S2eS26S4cSd2S6fVAInv;VCST;VXGL;R3VKc;A5A4S2fG0A1A3A5A2Ftp1;Frho1;FAi;").
Hypothesis CMS : ltac2:(tb__ "0|1|
S80S3S2cS43Q40A1A1VTR;S47S3bS76VAInv;R3VKc;A3Sd8R2R1A5S4dS3bS4bR2R1S31S2dS26S4cA2M0S2eS26S4cSd4S6fVAInv;VCST;VXGL;R3VKc;A5A4S2fG0A1A3A5A2Ftp1;Frho1;FAi;").

Hypothesis CALL_sc : ltac2:(tb__ "0|2|
S26S10cS2cS4A1M0S3S2cS43Q40A1A1S55SfaS20S33G0A1S4eR7S119R6A3S34G0R5A2A3S20S30S4fR8S119R7R6S10bS29S26S2aS11bA4A5S32A3S20S30S13fS4bSaS27R9A1A1A2S32A3S20S30S59SaS27RaA1A1R5A2S32A3S20S30S6bS7S1cSaS27RbA1M1A1A1S6G1A1A3S32A3S29S3S6aS29R2S11bA3S18SaS27RfA1A1RcR2A3VTR;S47S3bVJAv;RbA1S141S6S27R10A1A1S51RfS119S2aR4A1R10ReA5A2R3RcA5RaA2F_;F_;Frho';FL;VTR;S47S3bVJAv;R8A1RdRaR9A5R7A2F_;F_;F_;F_;F_;F_;FQ;Fnd;Ftp;Frho;FR;Fs;FCl;").
Hypothesis CALL_r2 : ltac2:(tb__ "0|2|
S26S10cS2cS4A1M0S3S2cS43Q40A1A1S55SfaS20S33G0A1S4eR7S12dR6A3S34G0R5A2A3S20S30S4fR8S12dR7R6S10bS29S26S2aS12eA4A5S32A3S20S30S13fS4bSaS27R9A1A1A2S32A3S20S30S59SaS27RaA1A1R5A2S32A3S20S30S6bS7S1cSaS27RbA1M1A1A1S6G1A1A3S32A3S29S3S6aS29R2S12eA3S18SaS27RfA1A1RcR2A3VTR;S47S3bVJAv;RbA1S141S6S27R10A1A1S51RfS12dS2aR4A1R10ReA5A2R3RcA5RaA2F_;F_;Frho';FL;VTR;S47S3bVJAv;R8A1RdRaR9A5R7A2F_;F_;F_;F_;F_;F_;FQ;Fnd;Ftp;Frho;FR;Fs;FCl;").
Hypothesis REENTER : ltac2:(tb__ "0|4|
S26S55S2dS0S2A2M0S3S2cS43Q40A1A1M1S0G1S6aS2dS2dS26S55A2M2G0A2S2eG2G0S2eS26S55R7R6A4R5A4Sc9A3S21S3cZ0S5eS2eG2G0S2eS26S55R8R7A4R6A4R5A2M3A2S3eG3R3A2A2VTR;S47S3bVJAv;R8A1R9R6R5A5VFAM;R4R3A2A2F_;F_;Ftp0;Fb;Ftp;Frho;Frv;Fnd;FT;").
Hypothesis POST : ltac2:(tb__ "0|1|
S26S55S3S2cS43Q40A1A1M0S0G0S6aS2dS26S4cA2S2eS26S4cR6S105R5A1A4S101A3VTR;S47S3bVJAv;R6A1R7R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;Fnd;FP;").

Ltac meas := unfold emeasA; cbn [eda_rank eda_var fst snd z0 eval]; rewrite lit_unsigned; cbn; lia.

Tactic Notation "innth" integer(k) := cbn [In cutsE]; do k right; left; reflexivity.

Lemma X_E_sm : ltac2:(tb__ "0|1|
S3S2cS43Q40A1A1M0S0G0S3cS3fZ61S40Z2Z40A2A2R2A2VTR;S47S3bVJAv;S9fA1Sc5R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
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
S26S10cS2cS4A1S3S2cS2dS2dS2S0A2S2A2A1S20S30SfeS6S27R5A1A1A1S32A3S20S30S103S6S27R6A1A1R2S39S36A1M0R4A4S32A3S20S30S111VXGL;S6S27R7A1M1A1S2fS2dS2S2A2A1M2R3G0S8G1A1SffS28R7A1A8S32A3S128VAInv;VCST;VXGL;S4bVrho0;S53VFB;VFF;A2VFB;VFF;R8R7R6R5S62G2R4S2fS46A1S5fA4S39S0A1S80S129S24L_;L_;AfF_;F_;F_;Ffr;Frho;FR;Fs;FE;").
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
S3S2cS43Q40A1A1M0S0G0S3cS3fZ5fS40Z2Z40A2A2R2A2VTR;S47S3bVJAv;S98A1S9aR5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
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
S3S2cS43Q40A1A1M0S0G0S3cS3fZ5dS40Z2Z40A2A2R2A2VTR;S47S3bVJAv;S98A1S9bR5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
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
  apply TR_exw. intros rho1. apply TR_facts. intros HF.
  apply (purec_callT_xp segs AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_pg FB FF) FB FF BX PTrue HKc TR TR_facts TR_ex TR_pre TR_callP
           XP_memset Pre_ms [L_ms] E_ms s_ms R_ms rho1 tp ndF [] (FAM b tp0)).
  - intros Ai rho2 tp2. cbn [map]. exact (CMS Ai rho2 tp2).
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
  - intros Ai tr ms md Hsm HM HX'. exact (XP_memset_site segs AInv CST XGL ALA HCST HXGL Ai E_ms pg_ms s_ms R_ms rho1 tp tr ms md Hsm HM HX' ltac:(first [assumption | vm_compute; reflexivity])).
  - intros L rho' tp' [<-|[]]. cbn [nd_tv nd_fr nd_bd nd_am]. unfold Pre_ms, L_ms. rewrite C_body0_eq.
    apply (REENTER C_body0 ndF (92, z0)); [innth 3 | meas].
Qed.

Lemma X_E_s00 : ltac2:(tb__ "0|1|
S3S2cS43Q40A1A1M0S0G0S3cS3fZ57S40Z2Z40A2A2R2A2VTR;S47S3bVJAv;S98A1Sa5R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
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
S3S2cS43Q40A1A1M0S0G0S3cS3fZ2dS40Z2Z40A2A2R2A2VTR;S47S3bVJAv;S98A1Sa3R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
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
S3S0S7S21S3cZ0R2A2S3eR2S40Z2Z40A2A2A2SdR4R2A2S20S0S44Q40M0S10R5S83A2A2S44G0S10R5S5R4A1A2A2A3F_;SdR5R3A2S20S0S45R6S83A2R5A3F_;F_;F_;Ff;Fk;Frho;").
Proof. intros rho k f Hk Hf H. pose proof (Hf H) as E. cbn [eval] in E. rewrite (u64_lit k Hk) in E. exact E. Qed.

Lemma reshape_rng : ltac2:(tb__ "0|5|
S3S0S21S3cZ3R1A2S3cR1Z4A2A2S20S0S45R3S83A2R2A3S21S20S0S3dS44Q40M0S10R4S11SaaR3A1M1A1A2A2M2S13R4G1A2A2S3dS44G0S10R4S11S87S2fSbA1A1M3A1A2A2M4S13R4G3A2A2A3S20S0S3dG2S12R4G1A2A2S3dG4S12R4G3A2A2A3A2F_;F_;Fk;Frho;").
Proof.
  intros rho k Hk Hn. unfold O_pp2d_lit, O_pp2d, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. split; [reflexivity|].
  assert (A : uval rho (SAlu ALU_SLL (SLit k) (SLit 4)) = 16 * k).
  { unfold uval. rewrite U_sll_lit, U_lit. change (2 ^ (4 mod 64)) with 16. unfold M64v. rewrite (Z.mod_small k) by lia. rewrite Z.mod_small by lia. lia. }
  assert (B : uval rho (SAlu ALU_SLL pN (SLit 4)) = 16 * uval rho pN).
  { unfold uval. rewrite U_sll_lit. change (2 ^ (4 mod 64)) with 16. unfold M64v. change (bv_unsigned (eval rho pN)) with (uval rho pN). rewrite Hn, Z.mod_small by lia. lia. }
  rewrite !soff_smallu by (rewrite ?A, ?B; lia). rewrite A, B, Hn. lia.
Qed.
Lemma reshape_rng_lit : ltac2:(tb__ "0|6|
S3S0S21S3cZ3R1A2S3cR1Z4A2A2S20S0S45R3S83A2R2A3S21S20S0S3dS44Q40M0S10R4S11S87S2fSbA1M1A1M2A1A2A2M3S13R4G2A2A2S3dS44G0S10R4S11S15S86S5Z0A1S5S3fZ10R3A2A1G1SfA5M4A1A2A2M5S13R4G4A2A2A3S20S0S3dG3S12R4G2A2A2S3dG5S12R4G4A2A2A3A2F_;F_;Fk;Frho;").
Proof.
  intros rho k Hk Hn. unfold O_pp2d, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. split; [reflexivity|].
  assert (B : uval rho (SAlu ALU_SLL pN (SLit 4)) = 16 * uval rho pN).
  { unfold uval. rewrite U_sll_lit. change (2 ^ (4 mod 64)) with 16. unfold M64v. change (bv_unsigned (eval rho pN)) with (uval rho pN). rewrite Hn, Z.mod_small by lia. lia. }
  rewrite soff_smallu by (rewrite B; lia). rewrite soff_lit_small by lia. rewrite B, Hn. lia.
Qed.

Lemma X_E_sc3 : ltac2:(tb__ "0|1|
S3S2cS43Q40A1A1M0S0G0S3cS3fZ42S40Z2Z40A2A2R2A2VTR;S47S3bVJAv;S98A1Sa7R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
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
S3S2cS43Q40A1A1M0S0G0S3cS3fZ42S40Z2Z40A2A2R2A2VTR;S47S3bVJAv;S98A1Sa8R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
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
S3S2cS43Q40A1A1M0S0G0S3cS3fZ42S40Z2Z40A2A2R2A2VTR;S47S3bVJAv;S98A1SbbR5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
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
S26S10cS2cS4A1S3S20S30SfeS6S27R4A1A1A1S32A3S20S30S103S6S27R5A1A1S31S2dS2dS2S0A2M0S2A2M1S2eG0S2S2eS2S0S88Z6A4S89A4M2S2fG1A1A3M3S34S36U0M4A2M5R3A4S32A3S20S30S111VXGL;S6S27R6A1M6A1S2fS2dS2S2A2A1M7G3G5S8G6A1SffS84A8S32A3S20S2S10dR6PcM8A2S88A3S20S2S10dR7S70A2S89A3S80S10aS7SdR7A1S6S27RaA1A1A3S53VFB;VFF;Vrho0;A3S108S4bVrho0;R9A3S5bVFB;R4A2S5cVFF;R5A2S5aVFB;R6RcG7A4S11dRdG7A2S11eReG7A2S57VFF;R9RfG3A4S23S3S3S23S2cS43Q40A1A1M9G9S23S96S96VAInv;RdR3R2R1A4Lmd1;A2Ltp1;A2Lrho1;A2S58Vrho0;RbA2S11cR12S82S81RcA1A1A2S21S135VCST;Vrho0;VFB;VFF;R13G7S120G1G4G3A3MaR14A8S21S134VCST;VXGL;Vrho0;VFB;VFF;R13G7GaS84A9S21S20S0S45R13S10dR15G8A2A2S45R13S35S2S0S35G0S2G2A3A3A2A3S20S0S45R13S10dR15S70A2A2S45R13S37G0S2G2A3A2A3A2A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FAi;F_;F_;F_;F_;F_;Frho;FR;Fs;FE;").
Proof.
  intros E s R rho HB HR HX Hs12 Hs16 Ai HF HP0 Hav HBf HFF HN HD HZ HFR (rho1 & tp1 & md1 & HM) HT HTK.
  split; [|split; [|rewrite Hs12, Hs16; cbn [fst snd]; split; reflexivity]].
  - intros o a Ho Hr. eapply (robjs_checkP_sound Ai rho _ [] [(vF, 6, vFL)] (Some 0%nat) R rho1 tp1 md1 HM HF HB Hav HP0 (T_ok_T0 rho0 _ Ai HT HTK) HFR HR); [exact Ho | exact Hr].
  - exact (xrs_ok_site Ai rho _ [] [(vF, 6, vFL)] (Some 0%nat) (ss_objs (ax_S E)) X_pg rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HN HD HZ HFR HX).
Qed.

Lemma flag_carve_site : ltac2:(tb__ "0|8|
S26S3S20S30SfeS6S27R2A1A1A1S32A3S20S30S116S6S27R3A1M0A1S2fS2dS2S2A2A1M1S31S2dS2dS2S0A2M2S2A2M3S2eG2S2S2eS2S0S88Z6A4S89A4S2fG3A1A3M4S39S36A1M5S100S8G0A1A6S32A3S20S30S111VXGL;S6S27R4A1M6A1G1G4G5S8G6A1SffS28R4A1A8S32A3S80S3S2cS43Q40A1A1S96S10aS7SdR8A1S6S27R9A1A1A3S53VFB;VFF;Vrho0;A3S108S4bVrho0;RaA3VAInv;R7R6R5R4A4S58Vrho0;R8A2S11cRdS82S81R9A1A1A2S5bVFB;RaA2S5cVFF;RbA2S5aVFB;RcR10G1A4S11dR11G1A2S11eR12G1A2S57VFF;RfR13G4A4S21S4S0S6aS4R2S8S27R17A1A1A3S21S3cS35S0S0S14R17R3A2M7A3R2A2S3eR2S37S0S0G7A3A2A2S22S131VCST;Vrho0;S11fVFB;R18G1A3S132VFF;R18G4A3R3A5S22S21S3cZ0R3A2S3eR3S13cA2A2S125R3A1A2A2F_;F_;Fa;Fo;S149R14S28R15A1A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FAi;F_;F_;F_;Frho;FE;").
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
S26S26S26S10cS2cS4A1M0S26S3S2cS43Q40A1A1M1S0G1S20S26S115RaP78A2R9A3S20S30S1fS27RaA1A1S32A3S20S2S2bRcA1S5S13dA1A3S20S30SfeS6S27RdA1A1A1S32A3S20S30S116S6S27ReA1M2A1S2fS2dS2S2A2M3A1M4S31S2dS2dS2S0A2M5S2A2M6S2eG5S2S2eS2S0S88Z6A4S89A4S2fG6A1A3M7S39S36A1M8S100S8G2A1A6S32A3S20S30S111VXGL;S6S27RfA1M9A1G4G7G8S8G9A1SffS28RfA1MaA8S32A3S20S2cG3A1GaS84A3S20S33G0A1S4eR10Sa0ReA3S34G0RdA2A3S20S30S50R11Sa0RfReS31S26Sa9S2fS26A1A3A5S32A3S20S30S124S4bR10A2S32A3S20S30S13fS4bSaS27R13A1A1A2S32A3S20S30S59SaS27R14A1A1S98A2S32A3S20S30SfeS6S27R15A1A1A1S32A3S20S30S103S6S27R16A1A1G7S34S36U0A2MbR13A4S32A3S20S30S111VXGL;S6S27R17A1McA1G4G7GbS8GcA1SffS84A8S32A3S20S2S10dR16PcA2S88A3S20S2S10dR17S70A2S89A3S20S26S133Sa0R1aR18R17Sa9S84A6R19A3S6aS2dS2dS26S55A2MdS2dS0S2A2MeA2S2eGdGeS2eS26S55R1aS9fA4S2eS0S2ZaSf9A4A4Sc9A3S3cS3fZfS40Z2Z40A2A2R15A2VTR;S47S3bVJAv;S98A1R1eR18R17A5VFAM;R16R15A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Ftp0;Fb;Ftp;Frho;FP;FR;Fs;FT;FE;FE0;").
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
S3S2cS43Q40A1A1M0S0G0S3cS3fZfS40Z2Z40A2A2R2A2VTR;S47S3bVJAv;S98A1Sc2R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  apply (X_E_sf E_sfI0 E_sfI T_sfI s_sfI R_sfI P_inv rho tp b tp0 E_sfI_eq); try (vm_compute; reflexivity); try reflexivity; try exact Hb; try exact T_sfI_eq.
  innth 31.
Qed.
Lemma X_E_sfK : ltac2:(tb__ "0|1|
S3S2cS43Q40A1A1M0S0G0S3cS3fZfS40Z2Z40A2A2R2A2VTR;S47S3bVJAv;S98A1Sc4R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  apply (X_E_sf E_sfK0 E_sfK T_sfK s_sfK R_sfK P_ok rho tp b tp0 E_sfK_eq); try (vm_compute; reflexivity); try reflexivity; try exact Hb; try exact T_sfK_eq.
  innth 32.
Qed.

Lemma exits_okT : ltac2:(tb__ "0|3|
S26S55S2dS0S2A2M0S3S2cS43Q40A1A1M1G1S6aS2dS2dS26S55A2M2G0A2S2eG2G0S2eS26S55R6R5A4R4A4Se9A3VTR;S47S3bVJAv;R6A1R7R4R3A5VFAM;S5eS2eG2G0S2eS26S55R7R6A4R5A4R4A2R2A2A2F_;Ftp0;Ftp;Frho;FrvX;FndX;FX;").
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
S7dS3bS6eVAInv;VCST;VXGL;A5").
Hypothesis SSC : ltac2:(tb__ "0|0|
S0S6aS0R1S31S0Z0S31S0Zf8S2fS0A1A3A3A3S13aS3bS6eVAInv;VCST;VXGL;R2A6F_;Fxx;").

Theorem tess_polygon_sum : ltac2:(tb__ "0|0|
S2cS43Q40A1A1SfdS3bVok;S47S3bS5dVAInv;VCST;VXGL;VKc;S53VFB;VFF;A2VFB;VFF;VBX;S56S9fAaS8cVrho0;R1A5S4dS3bS4bVrho0;R1S101A5A4Ftp0;").
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
       - intros Ai rho1 tp1. apply (aca_asan_memset _ _ _ _ _ AC); [exact HKc|]. eapply ok_frameA_of_K; [exact Hok|]. intros r p t m (_ & K & _). exact K.
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
S7eS3bS6eVAInv;VCST;VXGL;A5").
Hypothesis SSCX : ltac2:(tb__ "0|0|
S0S6aS0R1S31S0Z0S31S0Zf8S2fS0A1A3A3A3S13bS3bS6eVAInv;VCST;VXGL;R2A6F_;Fxx;").

Theorem tess_polygon_sum_ex : ltac2:(tb__ "0|0|
S2cS43Q40A1A1SfcS3bS47S3bS5dVAInv;VCST;VXGL;VKc;S53VFB;VFF;A2VFB;VFF;VBX;S56S9fAaS8cVrho0;R1A5S4dS3bS4bVrho0;R1S101A5A3Ftp0;").
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
       - intros Ai rho1 tp1. apply (acx_asan_memset _ _ _ _ _ ACX). exact HKc.
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
Module Lib_handle_f_pf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "valuation"; "sprop"; "sobj"; "holds"; "SLit"; "SAlu"; "ss_facts"; "ss_next"; "DUnknown"; "ss_objs"; "soff"; "mkObj"; "SPUle"; "cell"; "eval"; "sprop_eqb"; "SMd"; "odefault"; "sv_eqb"; "dflt_writable"; "obj_wf"; "sv_below"; "SExt"; "SPUlt"; "agree_below"; "ob_dflt"; "obj_range"; "ob_base"; "ob_cells"; "obj_hi_of"; "obj_lo_of"; "SPBranch"; "sprop_below"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "or"; "not"; "True"; "@Corelib.Init.Datatypes"; "list"; "pair"; "prod"; "bool"; "true"; "cons"; "nil"; "andb"; "nat"; "app"; "option"; "Some"; "None"; "fst"; "snd"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "leafA"; "xr_ok"; "ax_base"; "la_state"; "xr_below"; "ax_setS"; "entailsA"; "mkLeafA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "uval"; "bitem"; "bd_subst"; "bd_wpos"; "BXok_d"; "bxt"; "BUD"; "bd_nn"; "bsumK"; "bsumV"; "bd_below"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "pow"; "modulo"; "mul"; "lt"; "sub"; "opp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "emeasA"; "ANone"; "NDA"; "PTrue"; "nd_tv"; "nd_bd"; "tvinA"; "nd_below"; "JA_pre"; "TPA"; "frinA"; "nd_am"; "nd_fr"; "fbinA"; "ffinA"; "JAi"; "am_subst"; "fr_sub_eqb"; "JA"; "JLA"; "am_eqb"; "amode"; "frozen"; "nodeIA"; "ok_frameKA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "smatchA"; "stableA"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "firstn"; "skipn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_defs"; "fr_hf"; "pA"; "pQ"; "ndR"; "reshapeA"; "am2"; "mi_c"; "nd0"; "E_co0"; "E_ms0"; "Pre_hf"; "mi_n"; "pDco"; "xfo"; "E_sm0"; "L_ms"; "L_sm"; "PD_vn"; "Pre_ms"; "Pre_sm"; "X_pro"; "co_need"; "pKco"; "pT0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs"; "NPH"; "kb"; "hG"; "hF"; "tE"; "tL"; "tB"; "tI"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "M_MUL"; "ALU_SUB"; "ALU_SLL"; "BC_LTU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_nodes"; "z0"; "ndLL"; "VL"; "ndTS"; "VR"; "ndFV"; "ndL4a"; "ndL4b"; "ndTR"; "ndJ"; "ndJN"; "ndL4c"; "ndMI"; "ndMM"; "ndRP"; "ndP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_handle_f_iface"; "P0_hf"; "P0_hf_b"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "entails_frA"; "import_subA"; "call_checkPA"; "import_postA"; "J_ofPA"; "call_checkA"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_geom"; "topG"; "@Stdlib.Lists.List"; "In"; "existsb"; "nth_error"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve"; "B32"; "two47"; "B_EW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "call_linkP"; "wsub_dom_below";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s6"; "s_pg"; "Xk_pg"; "E_md0"; "E_pg0"; "objs_butlast"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_defs.HFAddr"; "DW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "rho_sub"; "rho_absorb"; "wsub_get"; "sv_subst"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS"; "shobj"; "shadow_release_stateA"; "xrs_checkL"; "robjs_checkF"; "shadow_reopen_stateA"; "flag_carve_stateA"; "release_objs_ok"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_defs.VN"; "Pre_vr"; "P_grown"; "P_keep"; "P_fail"; "nd0"; "tv0"; "bdP"; "tvP"; "vKn"; "vN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s5"; "pKts"; "needA"; "pDts"; "pKrp"; "E_rp0"; "E_ts0"; "pDrp"; "need_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fo.Lib_handle_f_pf"; "VM"; "DW_rng"; "r8f"; "x16f"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s2"; "ndEf"; "ndEo"; "ndXA"; "vr_need"; "E_fv0"; "E_mc0"; "E_mi0"; "E_mm0"; "NMI"; "E_dg0"; "L_mc1"; "Pre_mc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "tvz"; "tvd"; "T_ok"; "FBx"; "import_tv"; "tv_sub_eqb"; "remove_nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eg.Lib_builderH_pf"; "extraOH"; "extraXH"; "extraOH_client"; "frozen_stableH"; "payA_sameH"; "siteFH"; "siteHH"; "sitePH"; "siteXH"; "site_pureH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fo.Lib_handle_f_pf.Sum"; "HNPH"; "Posts_hfJ"; "JLh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_handle_f_s8"; "pL"; "E_g1_0"; "E_g2_0"; "E_g3_0"; "XLJ"; "cMI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eh.Lib_builder_pf"; "baseF"; "basez"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.et.Lib_handle_f_gdefs"; "fF"; "release_chk"; "triAF"; "purec_chk"; "rsFk"; "vlF"; "vr3F"; "vrLF"; "xff_chk"; "bF"; "coF"; "feF"; "gF"; "land_chk"; "live3F"; "liveF"; "liveRp"; "liveTri"; "liveTs"; "pure_chk"; "reopen_chk"; "roomF"; "rsF"; "slotF"; "vrF"; "vr_chk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fo.Lib_handle_f_pf.AR"; "o4A"; "o16A"; "orfx"; "pNXT'"; "pPRV'"; "pRFX'"; "oNXTe"; "oPRV"; "oPRVe"; "oRFX"; "oRFXe"; "a16"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fo.Lib_handle_f_pf.PGP"; "P0_pg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "JL_pure"; "AE_A"; "J_pure_pre"; "JL_stack_malloc"; "J_memcpy_pre"; "J_memset_pre"; "J_stack_malloc_pre"; "alloc_contractsA"; "alloc_contractsA_ex"; "alloc_lawsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ey.Lib_handle_f_gdefs4"; "E_pgF"; "R_pgF"; "PD_pgF"; "Pre_pgF"; "F_pgC"; "facts_sub"; "pgEF"; "pg_call_chkF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.et.Lib_handle_f_nodes2"; "cutsF2"; "exitsF2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fo.Lib_handle_f_pf.PGC"; "nd0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_handle_f_s7"; "pNT"; "E_wdg0"; "XJ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA";
"ax_add_facts"; "jnodeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_setX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "FFx"; "PostsC"; "T_afterA3"; "pclMA"; "xrs_inclb"; "xr_eqb"; "pd_okA"; "pdescA"; "robjs_okF"; "xrs_okF"; "xrs_okL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "ccount"; "T_afterA"; "payA"; "xrs_okA"; "call_checkTA"; "is_shadowZ"; "robjs_okA"; "site_okA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "SHADOW_OFF"; "Sh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s4"; "pKtr"; "E_tdg0"; "E_trb0"; "E_trg0"; "pDtr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "apply_axforms"; "AXSelect"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAT"; "robjs_checkP"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.en.Lib_handle_f_epi"; "E_f5f0"; "E_f5o0"; "NREL"; "P_fail"; "P_ok"; "XEf42"; "XEo42"; "nd_fail"; "nd_ok"; "L_f5"; "Pre_f5"; "X_rlf"; "X_rlo"; "sel_rel"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ew.Lib_handle_f_gdefs2"; "pgF"; "carve_chk"; "liveLF"; "pg0F"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eu.Lib_handle_f_gdefs3"; "release0_chk"; "is_shx"; "reopenS_chk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ey.Lib_handle_f_gdefs5"; "releaseP_chk"; "reopenC_chk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fo.Lib_handle_f_pf.VNP"; "P0_vr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s1"; "E_da0"; "E_pc0"; "xslot"; "pc_need"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.es.Lib_handle_f_s10"; "XEf6a"; "XEf6b"; "XEo6"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s3"; "E_sg0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ez.Lib_handle_f_s8w"; "E_mi4_0_0"; "E_mi4_0_4"; "E_mi4_1w"; "L_win"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s9"; "E_c4_0"; "E_fv4_0"; "E_m4_0"; "E_mi4_1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s9b"; "E_mm4_0"; "E_sg4_0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA"; "infrFF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Asan_set_shadow_iface"; "set_shadow_contractA"; "set_shadow_contractA_ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs"; "vAL"; "vb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_defs.PG"; "P_inv"; "P_ok"; "Pre_pg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fo.Lib_handle_f_pf.Sum.X"; "PD_pg"; "pure_rule"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_shx"; "gcs"; "shadow_reopen_cells_stateA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsSymJump"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3"; "import_okPA3"; "import_postA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR"; "robjs_okF"; "xrs_ok47"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj ExampleMemcpy Glue3 SymSoundW.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CFGA GlueA SummaryA SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV ObjXform ObjUnbase TobjJVAz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAT AxArrA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAM2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxArrA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.ObjZeroA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double Lib_parse_corner2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Asan_set_shadow_iface.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_parse_corner2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.Lib_diag_append OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Asan_set_shadow_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eg.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_defs Lib_handle_f_s1 Lib_handle_f_s2 Lib_handle_f_s3 Lib_handle_f_s4 Lib_handle_f_s5 Lib_handle_f_s6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require er.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_s9 Lib_handle_f_s9b.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require es.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require en.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_nodes.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ev.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_shx.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ez.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require et.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ew.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ey.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ex.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require f0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eb.Lib_vec_reserve_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eh.Lib_builder_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eg.Lib_builderH_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ep.Lib_handle_f_s7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.er.Lib_handle_f_s8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_s9b OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.es.Lib_handle_f_s10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.en.Lib_handle_f_epi OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_nodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ev.Lib_handle_f_eqs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ev.Lib_handle_f_eqs2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_handle_f_shx OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ez.Lib_handle_f_s8w OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.et.Lib_handle_f_nodes2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.et.Lib_handle_f_gdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ew.Lib_handle_f_gdefs2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eu.Lib_handle_f_gdefs3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ey.Lib_handle_f_gdefs4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ey.Lib_handle_f_gdefs5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eu.Lib_handle_f_g1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eu.Lib_handle_f_g1b OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eu.Lib_handle_f_g2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eu.Lib_handle_f_g3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eu.Lib_handle_f_g4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ex.Lib_handle_f_g5a OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ex.Lib_handle_f_g5b OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ey.Lib_handle_f_g5c OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ex.Lib_handle_f_g5d OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ex.Lib_handle_f_g5d2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ex.Lib_handle_f_g5d3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ex.Lib_handle_f_g5d4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ey.Lib_handle_f_g6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ey.Lib_handle_f_g7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f0.Lib_handle_f_g8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.f0.Lib_handle_f_g9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fo.Lib_handle_f_chk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_tess_polygon_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_handle_f_arith.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eq.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eq.Lib_handle_f_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Import ScanDoubleAddr VRAddr RA.ReallocAddr ParseCornerAddr DiagAppendAddr HFAddr.
Close Scope bv_scope.
Open Scope Z_scope.
Module VNP. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Lib_vec_reserveN_pf. End VNP.
Module PGP. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fo.Lib_tess_polygon_pf. End PGP.
Module PGC. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_tess_polygon_cstates. End PGC.
Module AR. Include Lib_handle_f_arith. End AR.

Lemma DW_rng : 0 <= DW < 2 ^ 40. Proof. unfold DW. lia. Qed.
Lemma sz_rng : 0 <= 512 < 2 ^ 40. Proof. lia. Qed.

Definition VM (e c : sv) (pos : Z) : sv := ltac2:(tb__ "0|0|
S8S9dS96Z40S8S9fVe;Vc;A3A2S7Vpos;A1A3").
Lemma VR_VM : ltac2:(tb__ "0|0|
S2S0S24S2Sa6R2R1A2Sf9S99R2R1A3A3Fpos;Fc;"). Proof. reflexivity. Qed.
Lemma VL_VM : ltac2:(tb__ "0|0|
S0S24S2Sa4R1A1Sf9S161S11dR1A3A3Fpos;"). Proof. reflexivity. Qed.
Lemma VM_val : ltac2:(tb__ "0|2|
S3S2S2S0S25S50S45R4R2A2S45R4R3A2M0A2S50G0S52Z2Z28A2A2A2S25S50Z0R2A2S55R2Z40M1A2A2S24S0S45R6Sf9R5R4R3A3A2S51S54G1S56S45R6R5A2S45R6R4A2A2A2R3A2A3F_;F_;Fa;Fc;Fe;Frho;").
Proof.
  intros rho e c a [Hce He] Ha. pose proof (uval_range rho c) as Rc. pose proof (uval_range rho e) as Re.
  assert (ES : uval rho (SAlu ALU_SUB e c) = uval rho e - uval rho c).
  { destruct (U_sub_q rho e c) as [k Hk]. unfold U in Hk. unfold uval in *.
    pose proof (bv_urange (eval rho (SAlu ALU_SUB e c))) as R. change (bv_modulus 64) with (2 ^ 64) in R. nia. }
  assert (EM : uval rho (kb 64 (SAlu ALU_SUB e c)) = 64 * (uval rho e - uval rho c)).
  { unfold kb. rewrite uval_mul_lit by lia. rewrite ES. reflexivity. }
  unfold VM. rewrite uval_add_litZ by (rewrite ?EM; lia). rewrite EM. lia.
Qed.

Lemma vrF_bound : ltac2:(tb__ "0|1|
S3S2aS4A1S2S79S4S6R3A1R2A3S24S2dS13dR2R3A2S2eA3S25S50S45R5R3A2S45R5S99A2M0A2S50G0S52Z2Z28A2A2A2F_;F_;Fq;FF;Frho;").
Proof.
  intros rho F q HF HV. unfold vrF in HV. apply andb_prop in HV as [HV H3]. apply andb_prop in HV as [H1 H2].
  pose proof (holds_mem _ _ _ HF H2) as F2. pose proof (holds_mem _ _ _ HF H3) as F3.
  rewrite h_ule in F2, F3. unfold two26 in F3. rewrite uval_lit in F3 by lia.
  assert (F1 : uval rho q <= uval rho tE).
  { apply orb_prop in H1 as [H1|H1]; pose proof (holds_mem _ _ _ HF H1) as F1; [rewrite h_ule in F1 | rewrite h_ult in F1]; lia. }
  lia.
Qed.

Lemma uval_add_neglit : ltac2:(tb__ "0|0|
S3S2S0S55R1Z0A2S50S57R2A1S45R4R3A2A2S50S57S52Z2Z3fA2A1R3A2S24S0S45R6S8S9dR5S7R4A1A3A2S51S45R6R5A2R4A2A3F_;F_;F_;Fk;Fa;Frho;").
Proof.
  intros rho a k Hk Ha Hk2. unfold uval in *. rewrite U_add, U_lit. pose proof (U_range (eval rho a)) as R. unfold M64v in *.
  rewrite Zplus_mod_idemp_r. apply Z.mod_small. lia.
Qed.
Lemma vlF_bound : ltac2:(tb__ "0|1|
S3S2aS4A1S79S4S6R2A1R1A3S24S2dS12aR2A1S2eA3S25S50S45R4S11dA2S45R4S161A2M0A2S50G0S52Z2Z28A2A2A2F_;F_;FF;Frho;").
Proof.
  intros rho F HF HV. unfold vlF in HV.
  apply andb_prop in HV as [HV H4]. apply andb_prop in HV as [HV H3]. apply andb_prop in HV as [H1 H2].
  pose proof (holds_mem _ _ _ HF H1) as F1. pose proof (holds_mem _ _ _ HF H2) as F2. pose proof (holds_mem _ _ _ HF H3) as F3. pose proof (holds_mem _ _ _ HF H4) as F4.
  rewrite h_ult in F1. rewrite h_ule in F2, F4. rewrite uval_lit in F4 by lia.
  cbn [holds eval branch_taken] in F3. unfold bv_ltu in F3. rewrite lit_unsigned in F3 by lia. apply Z.ltb_lt in F3. change (bv_unsigned (eval rho pA)) with (uval rho pA) in F3.
  unfold am2 in F2. rewrite uval_add_neglit in F2 by lia. lia.
Qed.

Lemma uval_sub_nw : ltac2:(tb__ "0|0|
S3S2S2S50S45R3R1A2S45R3R2A2A2S24S0S45R4S8S9fR3R2A3A2S56S45R4R3A2S45R4R2A2A2A3F_;Fb;Fa;Frho;").
Proof.
  intros rho a b H. pose proof (uval_range rho a) as Ra. pose proof (uval_range rho b) as Rb.
  destruct (U_sub_q rho a b) as [k Hk]. unfold U in Hk. unfold uval in *.
  pose proof (bv_urange (eval rho (SAlu ALU_SUB a b))) as R. change (bv_modulus 64) with (2 ^ 64) in R. nia.
Qed.
Lemma uval_kb : ltac2:(tb__ "0|1|
S3S0S2S25S50Z0R2A2S55R2S52Z2M0Z20A2A2A2S55S54R3S45R4R2A2A2S52G0Z40A2A2S24S0S45R5S96R4R3A2A2S54R4S45R5R3A2A2A3F_;F_;Fk;Fe;Frho;").
Proof. intros rho e k He H. unfold kb. pose proof (uval_range rho k). apply uval_mul_lit; lia. Qed.
Lemma uval_mulc : ltac2:(tb__ "0|1|
S3S2S0S25S50Z0R1A2S55R1S52Z2M0Z20A2A2A2S55S54R2S45R4R3A2A2S52G0Z40A2A2S24S0S45R5S13S9eR4S7R3A1A3A2S54R3S45R5R4A2A2A3F_;F_;Fe;Fc;Frho;").
Proof. intros rho c e He H. rewrite uval_mul_comm. apply uval_mul_lit; lia. Qed.
Ltac hfact HF H f := pose proof (holds_mem _ _ f HF ltac:(assumption)) as H.

Lemma co_need_ok : ltac2:(tb__ "0|0|
S3S2aS4A1S79S4S6R2A1R1A3S24S2dS12fR2A1S2eA3S79S4S6R4A1S92S7fA1A3F_;F_;FF;Frho;").
Proof.
  intros rho F HF C. unfold coF in C.
  apply andb_prop in C as [C H7]. apply andb_prop in C as [C H6]. apply andb_prop in C as [C H5]. apply andb_prop in C as [C H4].
  apply andb_prop in C as [C H3]. apply andb_prop in C as [H1 H2].
  pose proof (holds_mem _ _ _ HF H1) as F1. pose proof (holds_mem _ _ _ HF H2) as F2. pose proof (holds_mem _ _ _ HF H3) as F3.
  pose proof (holds_mem _ _ _ HF H5) as F5. pose proof (holds_mem _ _ _ HF H6) as F6. pose proof (holds_mem _ _ _ HF H7) as F7.
  assert (F4 : uval rho pT0 <= uval rho pQ).
  { apply orb_prop in H4 as [H4|H4]; pose proof (holds_mem _ _ _ HF H4) as F4; [rewrite h_ule in F4 | rewrite h_ult in F4]; lia. }
  rewrite h_ule in F2, F3, F5, F6, F7. unfold B32 in F2. unfold two26 in F7. rewrite uval_lit in F2 by lia. rewrite uval_lit in F7 by lia.
  pose proof (uval_range rho co_n) as R1. pose proof (uval_range rho tI) as R2. pose proof (uval_range rho pQ) as R3.
  unfold room_r in F1. rewrite h_ule in F1. change (1 * 12) with 12 in F1.
  assert (E1 : uval rho (kb 12 co_n) = 12 * uval rho co_n) by (apply uval_kb; lia).
  assert (E2 : uval rho (kb 12 tE) = 12 * uval rho tE) by (apply uval_kb; lia).
  assert (E3 : uval rho (kb 12 tI) = 12 * uval rho tI) by (apply uval_kb; lia).
  assert (E4 : uval rho (SLit (B_EW - 12)) = B_EW - 12) by (apply uval_lit; unfold B_EW; lia).
  rewrite !uval_add_small in F1 by (rewrite ?E1, ?E2, ?E3, ?E4; unfold B_EW; lia). rewrite E1, E2, E3, E4 in F1.
  assert (E5 : uval rho (SAlu ALU_SUB pQ tI) = uval rho pQ - uval rho tI) by (apply uval_sub_nw; lia).
  assert (E6 : uval rho (NCO pQ) = uval rho co_n + (uval rho pQ - uval rho tI)) by (unfold NCO; rewrite uval_add_small by (rewrite E5; lia); rewrite E5; lia).
  unfold co_need. constructor; [|constructor]. rewrite h_ule. rewrite uval_kb by (rewrite ?E6; lia). rewrite E6, uval_lit by (unfold B_EW; lia). unfold B_EW in *. lia.
Qed.

Lemma pc_need_ok : ltac2:(tb__ "0|0|
S3S2aS4A1S79S4S6R2A1R1A3S24S2dS31Sc6S4S12SfS7fS99A2A1R2A3Sc6S4S12SfS99S9aA2A1R2A3A2S2eA3S79S4S6R4A1S1a3S94S7fA2A3F_;F_;FF;Frho;").
Proof.
  intros rho F HF C. apply andb_prop in C as [H1 H2]. pose proof (holds_mem _ _ _ HF H1) as F1. pose proof (holds_mem _ _ _ HF H2) as F2. rewrite h_ule in F1, F2.
  unfold pc_need. constructor; [|constructor]. rewrite h_ule.
  assert (E : uval rho (SAlu ALU_ADD pT0 (SAlu ALU_SUB pQ pT0)) = uval rho pQ).
  { unfold uval. cbn [eval]. rewrite add_val, sub_val, Zplus_mod_idemp_r.
    pose proof (bv_urange (eval rho pQ)) as R. change (bv_modulus 64) with (2 ^ 64) in R.
    replace (bv_unsigned (eval rho pT0) + (bv_unsigned (eval rho pQ) - bv_unsigned (eval rho pT0))) with (bv_unsigned (eval rho pQ)) by lia.
    apply Z.mod_small. lia. }
  rewrite E. lia.
Qed.

Lemma xslot_val : ltac2:(tb__ "0|1|
S3S2S2S24S0S45R3S38S2S2S1a2R2R1A2A3A2S53S51S45R3S96ZcM0R1A2A2G0A2S52Z2Z40A2A2A3Fc;Fd;Frho;").
Proof.
  intros rho d c. unfold xslot, slot. cbn [snd]. unfold uval. cbn [eval]. rewrite sub_val, !add_val.
  rewrite lit_unsigned by lia. rewrite Zplus_mod_idemp_l, Zminus_mod_idemp_l. f_equal. lia.
Qed.
Lemma xslot_len : ltac2:(tb__ "0|2|
S3S2aS4A1S2S2S2S79S4S6R5A1R4A3S24S2dS13cR3R2R5A3S2eA3S27S50S51S45R7S38S2S2S1a2R5R4A2A3A2M0Z8A2S45R7S96ZcR3A2A2M1A2S24S0G0G1A3A2F_;F_;Fk;Fc;Fd;FF;Frho;").
Proof.
  intros rho F d c k HF C. unfold slotF in C. apply andb_prop in C as [C H3]. apply andb_prop in C as [H1 H2].
  pose proof (holds_mem _ _ _ HF H1) as F1. pose proof (holds_mem _ _ _ HF H2) as F2. pose proof (holds_mem _ _ _ HF H3) as F3.
  rewrite h_ule in F1, F2, F3. unfold B32 in F3. rewrite uval_lit in F3 by lia.
  pose proof (uval_range rho c) as Rc. pose proof (uval_range rho k) as Rk. pose proof (uval_range rho d) as Rd.
  assert (Ek : uval rho (kb 12 k) = 12 * uval rho k) by (apply uval_kb; lia).
  assert (Ec : uval rho (kb 12 c) = 12 * uval rho c) by (apply uval_kb; lia).
  rewrite uval_add_litZ in F1 by (rewrite ?Ec; lia). rewrite Ec, Ek in F1.
  assert (El : uval rho (snd (xslot d c)) = 12 * uval rho c + 12).
  { rewrite xslot_val, Ec. apply Z.mod_small. lia. }
  rewrite El, Ek. lia.
Qed.

Lemma vr_need_core : ltac2:(tb__ "0|0|
S3S0S2S2S25S55Z0R3A2S50R3ZcA2A2S50S45R5R3A2S45R5R2A2A2S50S54R5S45R6R3A2A2ScbA2S79S4S6R7A1S100R6R5R4A3A3F_;F_;F_;Fn;Fw;Fe;Frho;").
Proof.
  intros rho e w n He Hwn Hn. pose proof (uval_range rho w) as Rw. unfold B_EW in Hn.
  assert (Ew : uval rho (kb e w) = e * uval rho w) by (apply uval_kb; nia).
  assert (En : uval rho (kb e n) = e * uval rho n) by (apply uval_kb; nia).
  unfold vr_need. repeat constructor; rewrite h_ule; rewrite ?Ew, ?En; try (rewrite uval_lit by (unfold B_EW, two48; lia)); unfold B_EW, two48; nia.
Qed.
Tactic Notation "rdF" hyp(HF) hyp(C) ident(H) := let X := fresh in apply andb_prop in C as [C X]; pose proof (holds_mem _ _ _ HF X) as H; clear X.

Lemma roomF_vals : ltac2:(tb__ "0|6|
S3S2aS4A1S0S0S0S2S2S79S4S6R7A1R6A3S24S2dS13aR6R5R4R3R2R7A6S2eA3S25S55Z0M0R7A2M1S50R7ZcA2A2S25G1S50R7Z3A2A2S25S50G0R7A2S50R7Z40A2A2S50S45RcS7eA2S52Z2M2Z20A2A2S25S50S45RdR8A2S45RdR7A2M3A2S25S50G3Sc9A2S25S50S51S54RbG3A2S54S54RaRbA2S56S45RdS99A2M4S45RdS9cA2M5A2A2A2S56ScbR9A2A2S25S50S51S45RdS7eA2G5A2G4A2S50G4S52G2Z1aA2A2A2A2A2A2F_;F_;F_;F_;F_;F_;Fn;Fc;Fsl;Fr;Fe;FF;Frho;").
Proof.
  intros rho F e r sl c n HF C He Hr Hsl HA. unfold roomF in C.
  rdF HF C F7. rdF HF C F6. rdF HF C F5. rdF HF C F4. rdF HF C F3. rdF HF C F2. pose proof (holds_mem _ _ _ HF C) as F1.
  rewrite h_ule in F1, F2, F5, F6, F7. unfold B32 in F2. unfold two26 in F7. rewrite uval_lit in F2 by lia. rewrite uval_lit in F7 by lia.
  unfold arity_fact in F4. rewrite h_ule in F4. pose proof (uval_range rho tI) as RI. pose proof (uval_range rho pA) as RA. pose proof (uval_range rho n) as Rn.
  rewrite uval_add_small in F4 by lia.
  unfold room_r in F3. rewrite h_ule in F3.
  assert (Hre : 0 < r * e <= 36) by nia. assert (HtE : uval rho tE <= 2 ^ 26) by lia. assert (HtI : uval rho tI <= 2 ^ 26) by lia.
  set (re := r * e) in *.
  assert (E1 : uval rho (kb e n) = e * uval rho n) by (apply uval_kb; nia).
  assert (E2 : uval rho (kb re tE) = re * uval rho tE) by (apply uval_kb; nia).
  assert (E3 : uval rho (kb re tI) = re * uval rho tI) by (apply uval_kb; nia).
  assert (E4 : uval rho (SLit (B_EW - sl)) = B_EW - sl) by (apply uval_lit; unfold B_EW; lia).
  assert (B1 : e * uval rho n <= 2 ^ 36) by nia. assert (B2 : re * uval rho tE <= 2 ^ 32) by nia. assert (B3 : re * uval rho tI <= 2 ^ 32) by nia.
  rewrite !uval_add_small in F3 by (rewrite ?E1, ?E2, ?E3, ?E4; unfold B_EW; lia). rewrite E1, E2, E3, E4 in F3.
  unfold B32, B_EW in *. repeat split; nia.
Qed.
Lemma vr_mi3_ok : ltac2:(tb__ "0|2|
S3S2aS4A1S79S4S6R2A1R1A3S24S2dS12bZcM0Z3M1Z24S83S88R2A6S2eA3S79S4S6R4A1S100G0S8S9dS83S7G1A1A3S105S7eA1A3A3F_;F_;FF;Frho;").
Proof.
  intros rho F HF C. unfold vr3F in C. rdF HF C FA. cbn [holds eval branch_taken] in FA. unfold bv_ltu, bv_eqb in FA. apply Z.eqb_eq in FA. rewrite lit_unsigned in FA by lia.
  assert (A3 : uval rho pA = 3) by exact FA.
  destruct (roomF_vals rho F 12 3 36 mi_c mi_n HF C ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (V1 & V2 & V3 & V4 & V5).
  pose proof (uval_range rho mi_c) as Rc.
  assert (EW : uval rho (SAlu ALU_ADD mi_c (SLit 3)) = uval rho mi_c + 3) by (apply uval_add_litZ; unfold B32 in *; lia).
  assert (EN : uval rho (NMI pA) = uval rho mi_n + 9) by (unfold NMI; rewrite uval_add_small by (rewrite uval_kb by lia; unfold B32 in *; lia); rewrite uval_kb by lia; lia).
  apply vr_need_core; [lia | rewrite EW, EN; lia | rewrite EN; unfold B_EW in *; lia].
Qed.
Lemma vr_fv3_ok : ltac2:(tb__ "0|2|
S3S2aS4A1S2S2S79S4S6R4A1R3A3S24S2dS12bZ4M0Z1M1Z8R3R2R4A6S2eA3S79S4S6R6A1S100G0S8S9dR4S7G1A1A3S8S9dR3S7eA3A3A3F_;F_;Fn;Fc;FF;Frho;").
Proof.
  intros rho F c n HF C. unfold vr3F in C. rdF HF C FA. cbn [holds eval branch_taken] in FA. unfold bv_ltu, bv_eqb in FA. apply Z.eqb_eq in FA. rewrite lit_unsigned in FA by lia.
  assert (A3 : uval rho pA = 3) by exact FA.
  destruct (roomF_vals rho F 4 1 8 c n HF C ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (V1 & V2 & V3 & V4 & V5).
  pose proof (uval_range rho c) as Rc.
  assert (EW : uval rho (SAlu ALU_ADD c (SLit 1)) = uval rho c + 1) by (apply uval_add_litZ; unfold B32 in *; lia).
  assert (EN : uval rho (SAlu ALU_ADD n pA) = uval rho n + 3) by (rewrite uval_add_small by (unfold B32 in *; lia); lia).
  apply vr_need_core; [lia | rewrite EW, EN; lia | rewrite EN; unfold B_EW in *; lia].
Qed.

Lemma loop_vals : ltac2:(tb__ "0|4|
S3S2aS4A1S79S4S6R2A1R1A3S24S2dS31S31S31Sc6S4S12S1aS11dS161A2A1R2A3Sc6S4S12SfS161S82A2A1R2A3A2Sc6S4S12S22Sa1S7Z2M0A1S7eA3A1R2A3A2Sc6S4S12SfS7eS7S52G0Z14A2M1A1A2A1R2A3A2S2eA3S25S50S51S45R4S11dA2Z3M2A2S45R4S7eA2M3A2S25S50G2G3A2S50G3G1A2A2A2F_;F_;FF;Frho;").
Proof.
  intros rho F HF C. rdF HF C F4. rdF HF C F3. rdF HF C F2. pose proof (holds_mem _ _ _ HF C) as F1.
  rewrite h_ult in F1. rewrite h_ule in F2, F4. rewrite uval_lit in F4 by lia.
  cbn [holds eval branch_taken] in F3. unfold bv_ltu in F3. rewrite lit_unsigned in F3 by lia. apply Z.ltb_lt in F3. change (bv_unsigned (eval rho pA)) with (uval rho pA) in F3.
  unfold am2 in F2. rewrite uval_add_neglit in F2 by lia. lia.
Qed.
Lemma vr_mi4_ok : ltac2:(tb__ "0|2|
S3S2aS4A1S79S4S6R2A1R1A3S24S2dS12cZcM0Z3M1Z24S83S88R2A6S2eA3S79S4S6R4A1S100G0S8S9dS122S11dA1S7G1A1A3S105S7eA1A3A3F_;F_;FF;Frho;").
Proof.
  intros rho F HF C. unfold vrLF in C.
  apply andb_prop in C as [C L4]. apply andb_prop in C as [C L3]. apply andb_prop in C as [C L2]. apply andb_prop in C as [C L1].
  destruct (loop_vals rho F HF ltac:(rewrite L1, L2, L3, L4; reflexivity)) as [W1 W2].
  destruct (roomF_vals rho F 12 3 36 mi_c mi_n HF C ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (V1 & V2 & V3 & V4 & V5).
  pose proof (uval_range rho mi_c) as Rc. pose proof (uval_range rho pL) as RL.
  assert (EkL : uval rho (kb 3 pL) = 3 * uval rho pL) by (apply uval_kb; lia).
  assert (EkA : uval rho (kb 3 pA) = 3 * uval rho pA) by (apply uval_kb; lia).
  assert (EC : uval rho (cMI pL) = uval rho mi_c + 3 * uval rho pL) by (unfold cMI; rewrite uval_add_small by (rewrite EkL; unfold B32 in *; lia); rewrite EkL; lia).
  assert (EW : uval rho (SAlu ALU_ADD (cMI pL) (SLit 3)) = uval rho mi_c + 3 * uval rho pL + 3) by (rewrite uval_add_litZ by (rewrite ?EC; unfold B32 in *; lia); rewrite EC; lia).
  assert (EN : uval rho (NMI pA) = uval rho mi_n + 3 * uval rho pA) by (unfold NMI; rewrite uval_add_small by (rewrite EkA; unfold B32 in *; lia); rewrite EkA; lia).
  apply vr_need_core; [lia | rewrite EW, EN; lia | rewrite EN; unfold B_EW in *; lia].
Qed.
Lemma vr_fv4_ok : ltac2:(tb__ "0|2|
S3S2aS4A1S2S2S79S4S6R4A1R3A3S24S2dS12cZ4M0Z1M1Z8R3R2R4A6S2eA3S79S4S6R6A1S100G0S8S9dS8S9dR4S11dA3S7G1A1A3S8S9dR3S7eA3A3A3F_;F_;Fn;Fc;FF;Frho;").
Proof.
  intros rho F c n HF C. unfold vrLF in C.
  apply andb_prop in C as [C L4]. apply andb_prop in C as [C L3]. apply andb_prop in C as [C L2]. apply andb_prop in C as [C L1].
  destruct (loop_vals rho F HF ltac:(rewrite L1, L2, L3, L4; reflexivity)) as [W1 W2].
  destruct (roomF_vals rho F 4 1 8 c n HF C ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (V1 & V2 & V3 & V4 & V5).
  pose proof (uval_range rho c) as Rc. pose proof (uval_range rho pL) as RL.
  assert (EC : uval rho (SAlu ALU_ADD c pL) = uval rho c + uval rho pL) by (apply uval_add_small; unfold B32 in *; lia).
  assert (EW : uval rho (SAlu ALU_ADD (SAlu ALU_ADD c pL) (SLit 1)) = uval rho c + uval rho pL + 1) by (rewrite uval_add_litZ by (rewrite ?EC; unfold B32 in *; lia); rewrite EC; lia).
  assert (EN : uval rho (SAlu ALU_ADD n pA) = uval rho n + uval rho pA) by (rewrite uval_add_small by (unfold B32 in *; lia); lia).
  apply vr_need_core; [lia | rewrite EW, EN; lia | rewrite EN; unfold B_EW in *; lia].
Qed.

Lemma triA_vals : ltac2:(tb__ "0|1|
S3S2aS4A1S79S4S6R2A1R1A3S24S2dS127R2A1S2eA3S25S50Z4S45R4S7eA2M0A2S50G0S52Z2Z14A2A2A2F_;F_;FF;Frho;").
Proof.
  intros rho F HF C. unfold triAF in C. rdF HF C F3. rdF HF C F2. pose proof (holds_mem _ _ _ HF C) as F1.
  rewrite h_ule in F3. rewrite uval_lit in F3 by lia.
  cbn [holds eval branch_taken] in F2. unfold bv_ltu in F2. rewrite lit_unsigned in F2 by lia. apply Z.ltb_lt in F2. change (bv_unsigned (eval rho pA)) with (uval rho pA) in F2.
  cbn [holds eval branch_taken] in F1. unfold bv_eqb in F1.
  assert (NE : uval rho pA <> 3).
  { intros E3. apply F1. apply Z.eqb_eq. rewrite lit_unsigned by lia. exact E3. }
  lia.
Qed.
Lemma ts_need_ok : ltac2:(tb__ "0|0|
S3S2aS4A1S79S4S6R2A1R1A3S24S2dS127R2A1S2eA3S79S4S6R4A1Sf7A3F_;F_;FF;Frho;").
Proof. intros rho F HF C. exact (AR.need_facts_ok rho (triA_vals rho F HF C)). Qed.

Lemma k_nz_w : ltac2:(tb__ "0|1|
S3S2S2S6R3SfR2R1A2A2S6R4SfR2S7Sc9A1A2A2S50Z1S45R5R4A2A2S25S50S45R6R4A2M0Sc9A2S28S24S0G0Z0A3A1A2F_;F_;F_;Fk;Fw;Frho;").
Proof. intros rho w k H1 H2 Hw. rewrite h_ule in H1, H2. unfold B32 in *. rewrite uval_lit in H2 by lia. lia. Qed.
Lemma k_nz_3 : ltac2:(tb__ "0|1|
S3S2aS4A1S2S2S79S4S6R4A1R3A3S24S2dS133R3R2R4A3S2eA3S25S50S45R6R3A2M0Sc9A2S28S24S0G0Z0A3A1A2F_;F_;Fk;Fa;FF;Frho;").
Proof.
  intros rho F a k HF C. unfold live3F in C. rdF HF C F3. rdF HF C F2. pose proof (holds_mem _ _ _ HF C) as F1.
  cbn [holds eval branch_taken] in F1. unfold bv_eqb in F1. apply Z.eqb_eq in F1. rewrite lit_unsigned in F1 by lia.
  apply (k_nz_w rho a k F2 F3). unfold uval. rewrite F1. lia.
Qed.
Lemma uval_sll1 : ltac2:(tb__ "0|1|
S3S2S55S45R2R1A2S52Z2M0Z3eA2A2S24S0S45R3S8Sa0R2S7Z1A1A3A2S54G0S45R3R2A2A2A3F_;Fa;Frho;").
Proof.
  intros rho a Ha. pose proof (uval_range rho a). unfold uval in *. cbn [eval]. rewrite sll_val. change (1 mod 64) with 1. rewrite Z.shiftl_mul_pow2 by lia.
  change (2 ^ 1) with 2. rewrite Z.mod_small by lia. lia.
Qed.
Lemma k_nz_tri : ltac2:(tb__ "0|1|
S3S2aS4A1S2S79S4S6R3A1R2A3S24S2dS136R2R3A2S2eA3S25S50S45R5R3A2M0Sc9A2S28S24S0G0Z0A3A1A2F_;F_;Fk;FF;Frho;").
Proof.
  intros rho F k HF C. unfold liveTri in C. rdF HF C F4. rdF HF C F3. rdF HF C F2. pose proof (holds_mem _ _ _ HF C) as F1.
  rewrite h_ule in F3. rewrite uval_lit in F3 by lia.
  cbn [holds eval branch_taken] in F2. unfold bv_ltu in F2. rewrite lit_unsigned in F2 by lia. apply Z.ltb_lt in F2. change (bv_unsigned (eval rho pA)) with (uval rho pA) in F2.
  assert (E2 : uval rho am2 = uval rho pA - 2) by (unfold am2; apply uval_add_neglit; lia).
  apply (k_nz_w rho _ k F1 F4). rewrite uval_add_small by (rewrite uval_sll1 by (rewrite E2; lia); rewrite E2; lia). rewrite uval_sll1 by (rewrite E2; lia). rewrite E2. lia.
Qed.
Lemma k_nz_rp : ltac2:(tb__ "0|1|
S3S2aS4A1S2S79S4S6R3A1R2A3S24S2dS135R2R3A2S2eA3S25S50S45R5R3A2M0Sc9A2S28S24S0G0Z0A3A1A2F_;F_;Fk;FF;Frho;").
Proof.
  intros rho F k HF C. unfold liveRp in C. rdF HF C F4. rdF HF C F3. rdF HF C F2. pose proof (holds_mem _ _ _ HF C) as F1.
  rewrite h_ule in F3. rewrite uval_lit in F3 by lia.
  cbn [holds eval branch_taken] in F2. unfold bv_ltu in F2. rewrite lit_unsigned in F2 by lia. apply Z.ltb_lt in F2. change (bv_unsigned (eval rho pA)) with (uval rho pA) in F2.
  apply (k_nz_w rho _ k F1 F4). rewrite uval_add_small by (rewrite uval_sll1 by lia; lia). rewrite uval_sll1 by lia. lia.
Qed.
Lemma k_nz_ts : ltac2:(tb__ "0|1|
S3S2aS4A1S2S79S4S6R3A1R2A3S24S2dS137R2R3A2S2eA3S25S50S45R5R3A2M0Sc9A2S28S24S0G0Z0A3A1A2F_;F_;Fk;FF;Frho;").
Proof.
  intros rho F k HF C. unfold liveTs in C. rdF HF C F3. apply andb_prop in C as [C CT]. pose proof (holds_mem _ _ _ HF C) as F1.
  pose proof (triA_vals rho F HF CT) as HA.
  apply (k_nz_w rho _ k F1 F3). pose proof (AR.U_needA rho HA) as N. unfold uval. unfold AR.needA, AR.M16, AR.M32, AR.pA in N. unfold needA, M16, M32, pA.
  rewrite N. unfold uval, pA in HA. cbn [eval] in HA. pose proof (Z.mod_pos_bound (8 * bv_unsigned (rw rho 418) + 30) 32 ltac:(lia)). pose proof (Z.mod_pos_bound ((bv_unsigned (rw rho 418) + 7) / 8 + 15) 16 ltac:(lia)).
  pose proof (Z.div_pos (bv_unsigned (rw rho 418) + 7) 8 ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma g_need_ok : ltac2:(tb__ "0|2|
S3S2aS4A1S2S79S4S6R3A1R2A3S24S2dS131R3A1S2eA3S55S45R5R3A2S45R5S7eA2A2S79S4S6R6A1S2fS4SfS8S9dS8S9dS89S13S9eR4S7ZcM0A1M1A3A3G1A3S8S9dS89S96G0S93A2A3A2S30S4A1A3A3F_;F_;F_;Fm;FF;Frho;").
Proof.
  intros rho F m HF C Hm. unfold gF in C. rdF HF C F5. rdF HF C F4. rdF HF C F3. rdF HF C F2. pose proof (holds_mem _ _ _ HF C) as F1.
  rewrite h_ule in F1, F2, F3, F4, F5. unfold two47, RA.two47 in F1. unfold B32 in F2, F3. rewrite uval_lit in F1 by lia. rewrite uval_lit in F2 by lia.
  rewrite uval_lit in F3 by lia. rewrite uval_lit in F5 by lia.
  pose proof (uval_range rho m) as Rm. pose proof (uval_range rho pDco) as Rd.
  assert (EK : uval rho (kb 12 pKco) = 12 * uval rho pKco) by (apply uval_kb; lia).
  assert (EA : uval rho (kb 12 pA) = 12 * uval rho pA) by (apply uval_kb; lia). rewrite EK, EA in F4.
  assert (EM : uval rho (SMd M_MUL m (SLit 12)) = 12 * uval rho m) by (apply uval_mulc; lia).
  assert (E1 : uval rho (SAlu ALU_ADD pDco (SMd M_MUL m (SLit 12))) = uval rho pDco + 12 * uval rho m) by (rewrite uval_add_small by (rewrite EM; lia); rewrite EM; lia).
  assert (E2 : uval rho (SAlu ALU_ADD (SAlu ALU_ADD pDco (SMd M_MUL m (SLit 12))) (SLit 12)) = uval rho pDco + 12 * uval rho m + 12) by (rewrite uval_add_litZ by (rewrite ?E1; lia); rewrite E1; lia).
  assert (E3 : uval rho (SAlu ALU_ADD pDco (kb 12 pKco)) = uval rho pDco + 12 * uval rho pKco) by (rewrite uval_add_small by (rewrite EK; lia); rewrite EK; lia).
  constructor; [|constructor]. rewrite h_ule. rewrite E2, E3. lia.
Qed.

Section TSX.
Variable rho : valuation.
Let a := uval rho pA.
Let d := uval rho pDts.
Hypothesis Ha : 4 <= a <= 2 ^ 20.
Hypothesis Hd : d <= 2 ^ 47.
Let x16 : ltac2:(tb__ "0|0|
S0") := ltac2:(tb__ "0|1|
S56S51S54Z4Va;A2ZfA2M0S53G0Z10A2A2").
Let r8 := (a + 7) / 8.
Lemma dts_range : 0 <= d. Proof using. pose proof (uval_range rho pDts). subst d. lia. Qed.
Lemma V_o16A : ltac2:(tb__ "0|0|
S24S0S45Vrho;S140A2S54Z10Va;A2A3"). Proof using Ha. exact (AR.U_o16A rho Ha). Qed.
Lemma V_o4A : ltac2:(tb__ "0|0|
S24S0S45Vrho;S13fA2S54Z4Va;A2A3"). Proof using Ha. exact (AR.U_o4A rho Ha). Qed.
Lemma V_a16 : ltac2:(tb__ "0|0|
S24S0S45Vrho;S14aA2Vx16;A3"). Proof using Ha. exact (AR.U_a16 rho Ha). Qed.
Lemma V_orfx : ltac2:(tb__ "0|0|
S24S0S45Vrho;S141A2Vr8;A3"). Proof using Ha. exact (AR.U_orfx rho Ha). Qed.
Lemma V_oNXTe : ltac2:(tb__ "0|0|
S24S0S45Vrho;S145A2S51S54Z10Va;A2S54Z4Va;A2A2A3"). Proof using Ha. exact (AR.U_oNXTe rho Ha). Qed.
Lemma V_oPRV : ltac2:(tb__ "0|0|
S24S0S45Vrho;S146A2S51S54Z10Va;A2Vx16;A2A3"). Proof using Ha. exact (AR.U_oPRV rho Ha). Qed.
Lemma V_oPRVe : ltac2:(tb__ "0|0|
S24S0S45Vrho;S147A2S51S51S54Z10Va;A2Vx16;A2S54Z4Va;A2A2A3"). Proof using Ha. exact (AR.U_oPRVe rho Ha). Qed.
Lemma V_oRFX : ltac2:(tb__ "0|0|
S24S0S45Vrho;S148A2S51S51S54Z10Va;A2Vx16;A2Vx16;A2A3"). Proof using Ha. exact (AR.U_oRFX rho Ha). Qed.
Lemma V_oRFXe : ltac2:(tb__ "0|0|
S24S0S45Vrho;S149A2S51S51S51S54Z10Va;A2Vx16;A2Vx16;A2Vr8;A2A3"). Proof using Ha. exact (AR.U_oRFXe rho Ha). Qed.
Lemma V_x16 : ltac2:(tb__ "0|1|
S25S25S50S54Z4Va;A2M0Vx16;A2S50Vx16;S51G0ZfA2A2A2S24S0S53Vx16;Z10A2Z0A3A2").
Proof using Ha. pose proof (Z.mod_pos_bound (4 * a + 15) 16 ltac:(lia)). pose proof (Z.div_mod (4 * a + 15) 16 ltac:(lia)). subst x16. split; [lia|].
  replace (4 * a + 15 - (4 * a + 15) mod 16) with (16 * ((4 * a + 15) / 16)) by lia. rewrite Z.mul_comm. apply Z_mod_mult. Qed.
Lemma V_r8 : ltac2:(tb__ "0|0|
S25S50Z0Vr8;A2S50Vr8;S51Va;Z7A2A2A2"). Proof using Ha. subst r8. split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]. Qed.
Lemma V_pNXT : ltac2:(tb__ "0|0|
S24S0S45Vrho;S142A2S51Vd;S54Z10Va;A2A2A3").
Proof using Ha Hd. pose proof dts_range. unfold AR.pNXT'. rewrite uval_add_small by (change (uval rho (SVar AR.vDTS)) with d; rewrite V_o16A; lia). change (uval rho (SVar AR.vDTS)) with d. rewrite V_o16A. lia. Qed.
Lemma V_pPRV : ltac2:(tb__ "0|0|
S24S0S45Vrho;S143A2S51S51Vd;S54Z10Va;A2A2Vx16;A2A3").
Proof using Ha Hd. pose proof dts_range. pose proof V_x16. unfold AR.pPRV'. rewrite uval_add_small by (rewrite V_pNXT, V_a16; lia). rewrite V_pNXT, V_a16. lia. Qed.
Lemma V_pRFX : ltac2:(tb__ "0|0|
S24S0S45Vrho;S144A2S51S51S51Vd;S54Z10Va;A2A2Vx16;A2Vx16;A2A3").
Proof using Ha Hd. pose proof dts_range. pose proof V_x16. unfold AR.pRFX'. rewrite uval_add_small by (rewrite V_pPRV, V_a16; lia). rewrite V_pPRV, V_a16. lia. Qed.
Lemma V_needA : ltac2:(tb__ "0|3|
S24S0S45Vrho;Sf1A2S51S51S56S51S54Z8Va;A2Z1eA2M0S53G0Z20A2A2S54Z10M1Va;A2A2S56S51Vr8;ZfA2M2S53G2G1A2A2A2A3").
Proof using Ha. exact (AR.U_needA rho Ha). Qed.
Lemma soffU : ltac2:(tb__ "0|0|
S2S55S45Vrho;R1A2S52Z2Z3fA2A2S24S0SdVrho;R2A2S45Vrho;R2A2A3F_;Fe;").
Proof using. intros e He. apply soff_smallu. exact He. Qed.

Lemma nxt_eqs_f : ltac2:(tb__ "0|1|
S25S24S0S51S45Vrho;S142A2M0SdVrho;S7Z0A1A2A2S51Vd;SdVrho;S140A2A2A3S24S0S51G0SdVrho;S13fA2A2S51Vd;SdVrho;S145A2A2A3A2").
Proof using Ha Hd. pose proof dts_range. pose proof V_x16. rewrite V_pNXT, soff_lit_small by lia. rewrite !soffU by (rewrite ?V_o16A, ?V_o4A, ?V_oNXTe; lia). rewrite V_o16A, V_o4A, V_oNXTe. lia. Qed.
Lemma prv_eqs_f : ltac2:(tb__ "0|1|
S25S24S0S51S45Vrho;S143A2M0SdVrho;S7Z0A1A2A2S51Vd;SdVrho;S146A2A2A3S24S0S51G0SdVrho;S13fA2A2S51Vd;SdVrho;S147A2A2A3A2").
Proof using Ha Hd. pose proof dts_range. pose proof V_x16. rewrite V_pPRV, soff_lit_small by lia. rewrite !soffU by (rewrite ?V_oPRV, ?V_o4A, ?V_oPRVe; lia). rewrite V_oPRV, V_o4A, V_oPRVe. lia. Qed.
Lemma rfx_eqs_f : ltac2:(tb__ "0|1|
S25S24S0S51S45Vrho;S144A2M0SdVrho;S7Z0A1A2A2S51Vd;SdVrho;S148A2A2A3S24S0S51G0SdVrho;S141A2A2S51Vd;SdVrho;S149A2A2A3A2").
Proof using Ha Hd. pose proof dts_range. pose proof V_x16. pose proof V_r8. rewrite V_pRFX, soff_lit_small by lia. rewrite !soffU by (rewrite ?V_oRFX, ?V_orfx, ?V_oRFXe; lia). rewrite V_oRFX, V_orfx, V_oRFXe. lia. Qed.
End TSX.

Lemma xr_ok_subrange : ltac2:(tb__ "0|2|
S3S2aS5A1S0S2S2S2S2S0S0S24S0S45R9R4A2S51S45R9R6A2R2A2A3S50Z0M0R3A2S24S0S53S51S45RbR8A2R4A2Z8M1A2G0A3S50S51R5S45RcR6A2A2R4A2S50R5S45RdR9A2A2S27S24S0S53S51S45ReRbA2R6A2G1A2G0A3S24S0S51R7S45ReR8A2A2S45ReRaA2A3A2S3eRfReRdS2bS2S2RcRbA4A4S3eR10RfReS2bS2S2RbRaA4A4F_;F_;F_;F_;F_;F_;F_;FM;Fo;Fl';Fb';Fl;Fb;Foff;Fobjs;Frho;").
Proof.
  intros rho objs off b l b' l' o M Eb Ho Hal HM1 HM2 HM (HB8 & HBL & Hall). unfold xr_ok. cbn [fst snd] in *. unfold uval in *.
  pose proof (bv_urange (eval rho l')) as Rl'. change (bv_modulus 64) with (2 ^ 64) in Rl'.
  rewrite Eb. split; [exact Hal|]. split; [lia|]. intros x Hx.
  destruct (Hall x ltac:(lia)) as (G1 & G2 & G3 & v & Gv & Gd). split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. exists v. split; [exact Gv|].
  destruct Gd as [Gd|[Gv2 Ga]]; [left; exact Gd|]. destruct HM as [HM|HM].
  - exfalso. assert (x / 8 < (bv_unsigned (eval rho b) + M) / 8).
    { apply Z.div_lt_upper_bound; [lia|]. rewrite <- (Z_div_exact_2 (bv_unsigned (eval rho b) + M) 8) by lia. lia. }
    pose proof (Z.div_le_mono (bv_unsigned (eval rho b) + M) (bv_unsigned (eval rho b) + bv_unsigned (eval rho l)) 8 ltac:(lia) ltac:(lia)). lia.
  - right. replace (bv_unsigned (eval rho b) + o + bv_unsigned (eval rho l')) with (bv_unsigned (eval rho b) + bv_unsigned (eval rho l)) by lia. split; [exact Gv2 | exact Ga].
Qed.
Lemma publish_sub_imp : ltac2:(tb__ "0|7|
S74S3aS2S2S2S2S3S2aS77Q40A1A1Sb4S24S2dSc6S2cS2S2A2M0S16cS2bS2S2R7R6A4A1S3cR8A1A3S2eA3S24S2dS41SaS3bR9A1A1S2bS2S2R6R5A4A2S2eA3S79S4S6R5A1S9S3bRaA1A1A3S24S0S53S45R6RaA2Z8M1A2Z0M2A3S26S0S0S26S0S0S25S24S0S45R9RbA2S51S45R9RdA2M3R2A2M4A3S25S50G2R2A2S25S24S0S53G4G1A2G2A3S25S50S51R2S45R9RaA2A2M5R1A2S25S50R1S45R9RcA2M6A2S27S24S0S53S51G3R1A2G1A2G2A3S24S0G5G6A3A2A2A2A2A2A2LM;A2Lo;A2F_;F_;S73S58RcRbR6R5R4A6S73S58RdS166RcS2fG0S2bS2S2R9R8A4S3cRcA1A3A2R7R6R5A6F_;F_;F_;F_;Fw;Ftp;Frho;Fl';Fb';Fl;Fb;FA;FJ;").
Proof.
  intros J A b l b' l' rho tp w Hin Hb Hsem Hx. apply SPA_x_publish; [exact Hb | | exact Hx].
  pose proof Hx as [(Hsm & _ & _ & Hsh & _) _].
  apply existsb_exists in Hin as (r & Hr & Heq). unfold xr_eqb in Heq. apply andb_prop in Heq as [Q1 Q2]. apply sv_eqb_sound in Q1. apply sv_eqb_sound in Q2.
  destruct r as [rb rl]. cbn in Q1, Q2. subst rb rl.
  assert (HX : xr_ok rho (ss_objs (ax_S A)) (bv_unsigned (eval rho (ax_base A))) (b, l)) by (unfold shadow_ok in Hsh; exact (proj1 (Forall_forall _ _) Hsh _ Hr)).
  destruct (Hsem (smatchA_facts segs _ _ _ _ (proj1 Hx)) (proj1 HX)) as (o & M & E1 & E2 & E3 & E4 & E5 & E6).
  exact (xr_ok_subrange rho _ _ b l b' l' o M E1 E2 E3 E4 E5 E6 HX).
Qed.

Lemma reshape_gen : ltac2:(tb__ "0|3|
S74S3aS32S5S5S3S2aS77Q40M0A1A1Sb4S24S34S5A1Sc7S5ScS3bR7A1A1R6A3S35S5R5A2A3S24S2aS10A1S1fR5A1S30S10A1A3S24S14S1cR6A1SbA3S24S2dS16S1cR8A1A1S2eA3S24S2dS17SaS3bRbA1A1R8A2S2eA3S79S4S6R8A1S9S3bRcA1A1A3S25S24S0S51S78G0S11R9S1eRaA1A2A2M1S21R9RaA2A2S51S78G0S11R9S1eRbA1A2A2M2S21R9RbA2A2A3S24S0S51G1S20R9RaA2A2S51G2S20R9RbA2A2A3A2F_;S73S58ReRdR9R8R7A6S73S58RfS81ReRdRbA3RaR9R8A6F_;F_;F_;F_;F_;F_;F_;Fwd;Ftp;Frho;Fo';Fo;Fi;FA;FJ;").
Proof. intros J A i o o' rho tp wd Hn Hc Hd Hw Hwf Hrg Hx. unfold reshapeA. exact (SPA_reshape segs _ rho A i o o' tp wd Hn Hc Hd Hw Hwf Hrg Hx). Qed.

Lemma tsx_vals : ltac2:(tb__ "0|2|
S3S2aS4A1S79S4S6R2A1R1A3S24S2dS31S127R2A1Sc6S4S12SfSf2S7ScaA1A2A1R2A3A2S2eA3S25S25S50Z4S45R4S7eA2M0A2S50G0S52Z2M1Z14A2A2A2S50S45R4Sf2A2S52G1Z2fA2A2A2F_;F_;FF;Frho;").
Proof.
  intros rho F HF C. apply andb_prop in C as [C1 C2]. pose proof (holds_mem _ _ _ HF C2) as F2. rewrite h_ule in F2. unfold two47, RA.two47 in F2. rewrite uval_lit in F2 by lia.
  split; [exact (triA_vals rho F HF C1) | lia].
Qed.

Lemma mod8_add : ltac2:(tb__ "0|3|
S0S0S24S0S53R2Z8M0A2Z0M1A3M2G2S24S0S53S51R4R3A2G0A2G1A3F_;F_;Fn;FB;").
Proof. intros B n HB Hn. rewrite Z.add_mod, HB, Hn by lia. reflexivity. Qed.
Lemma mod8_of16 : ltac2:(tb__ "0|1|
S0S24S0S53R1Z10A2Z0M0A3S24S0S53R2Z8A2G0A3F_;Fn;").
Proof. intros n H. pose proof (Z.div_mod n 16 ltac:(lia)). rewrite H in H0. replace n with ((n / 16 * 2) * 8) by lia. apply Z_mod_mult. Qed.
Lemma mod8_mul8 : ltac2:(tb__ "0|1|
S0S24S0S53S54Z8M0R1A2G0A2Z0A3Fk;"). Proof. intros k. rewrite Z.mul_comm. apply Z_mod_mult. Qed.
Lemma mod16_mul16 : ltac2:(tb__ "0|1|
S0S24S0S53S54Z10M0R1A2G0A2Z0A3Fk;"). Proof. intros k. rewrite Z.mul_comm. apply Z_mod_mult. Qed.

Definition x16f (a : Z) : Z := ltac2:(tb__ "0|1|
S56S51S54Z4Va;A2ZfA2M0S53G0Z10A2A2").
Definition r8f (a : Z) : Z := (a + 7) / 8.
Section TSX2.
Variable rho : valuation.
Let a := uval rho pA.
Let d := uval rho pDts.
Hypothesis Ha : 4 <= a <= 2 ^ 20.
Hypothesis Hd : d <= 2 ^ 47.

Lemma xsub_pts : ltac2:(tb__ "0|7|
S50S45Vrho;S96Z3S7eA2A2S45Vrho;Sf3A2M0A2S50G0Sc9A2S24S0S53S45Vrho;Sf6A2M1Z8M2A2Z0M3A3S26S0S0S26S0S0S25S24S0G1S51G1R2A2M4A3S25S50G3R2A2S25S24S0S53G4G2A2G3A3S25S50S51R2S45Vrho;S13S9eS7eS7ZcA1A3A2A2M5R1A2S25S50R1S45Vrho;S96Z4Sf3A2A2M6A2S27S24S0S53S51G1R1A2G2A2G3A3S24S0G5G6A3A2A2A2A2A2A2LM;A2Lo;A2F_;F_;F_;").
Proof using Ha.
  intros H3 HK HB8. unfold B32 in HK. rewrite uval_kb in H3 by (subst a; lia). change (uval rho pA) with a in H3.
  rewrite uval_mulc by (subst a; lia). rewrite uval_kb by lia. change (uval rho pA) with a.
  assert (Z0 : (uval rho pDrp + 0) mod 8 = 0) by (rewrite Z.add_0_r; exact HB8).
  destruct (Z.eq_dec (3 * a) (uval rho pKrp)) as [E|NE].
  - exists 0, (12 * a). repeat split; first [lia | exact Z0 | right; lia].
  - destruct (Z.Even_or_Odd a) as [[k Hk]|[k Hk]].
    + assert (M8 : (uval rho pDrp + 12 * a) mod 8 = 0) by (apply mod8_add; [exact HB8|]; replace (12 * a) with (8 * (3 * k)) by lia; apply mod8_mul8).
      exists 0, (12 * a). repeat split; first [lia | exact Z0 | left; exact M8].
    + assert (M8 : (uval rho pDrp + (12 * a + 4)) mod 8 = 0) by (apply mod8_add; [exact HB8|]; replace (12 * a + 4) with (8 * (3 * k + 2)) by lia; apply mod8_mul8).
      exists 0, (12 * a + 4). repeat split; first [lia | exact Z0 | left; exact M8].
Qed.

Lemma xsub_out : ltac2:(tb__ "0|7|
S50S45Vrho;S96Z3S82A2A2S45Vrho;S17dA2M0A2S50G0Sc9A2S24S0S53S45Vrho;S181A2M1Z8M2A2Z0M3A3S26S0S0S26S0S0S25S24S0G1S51G1R2A2M4A3S25S50G3R2A2S25S24S0S53G4G2A2G3A3S25S50S51R2S45Vrho;S13S9eS82S7ZcA1A3A2A2M5R1A2S25S50R1S45Vrho;S96Z4S17dA2A2M6A2S27S24S0S53S51G1R1A2G2A2G3A3S24S0G5G6A3A2A2A2A2A2A2LM;A2Lo;A2F_;F_;F_;").
Proof using Ha.
  intros H3 HK HB8. unfold B32 in HK.
  assert (E2 : uval rho am2 = a - 2) by (unfold am2; subst a; apply uval_add_neglit; lia).
  rewrite uval_kb in H3 by (rewrite ?E2; lia). rewrite E2 in H3. rewrite uval_mulc by (rewrite ?E2; lia). rewrite uval_kb by lia. rewrite E2.
  assert (Z0 : (uval rho pDtr + 0) mod 8 = 0) by (rewrite Z.add_0_r; exact HB8).
  destruct (Z.eq_dec (3 * (a - 2)) (uval rho pKtr)) as [E|NE].
  - exists 0, (12 * (a - 2)). repeat split; first [lia | exact Z0 | right; lia].
  - destruct (Z.Even_or_Odd a) as [[k Hk]|[k Hk]].
    + assert (M8 : (uval rho pDtr + 12 * (a - 2)) mod 8 = 0) by (apply mod8_add; [exact HB8|]; replace (12 * (a - 2)) with (8 * (3 * k - 3)) by lia; apply mod8_mul8).
      exists 0, (12 * (a - 2)). repeat split; first [lia | exact Z0 | left; exact M8].
    + assert (M8 : (uval rho pDtr + (12 * (a - 2) + 4)) mod 8 = 0) by (apply mod8_add; [exact HB8|]; replace (12 * (a - 2) + 4) with (8 * (3 * k - 1)) by lia; apply mod8_mul8).
      exists 0, (12 * (a - 2) + 4). repeat split; first [lia | exact Z0 | left; exact M8].
Qed.

Lemma needA_facts : ltac2:(tb__ "0|5|
S50S45Vrho;Sf1A2M0S45Vrho;Sf0A2A2S25S50S51S51S51S54Z10M1Va;A2SfcVa;A1M2A2G2A2SfbVa;A1M3A2G0A2S25S24S0S53G0G1A2Z0M4A3S25S50S54Z4Va;A2G2A2S25S24S0S53G2G1A2G4A3S50G4G3A2A2A2A2A2F_;").
Proof using Ha.
  intros HN. unfold x16f, r8f in *. pose proof (V_needA rho Ha) as N. change (uval rho pA) with a in N.
  pose proof (V_x16 rho Ha) as [X1 X2]. change (uval rho pA) with a in X1, X2.
  pose proof (V_r8 rho Ha) as R. change (uval rho pA) with a in R.
  pose proof (AR.ts_arith a (uval rho needA) Ha) as T. cbv zeta in T. specialize (T ltac:(rewrite N; lia)).
  destruct T as (A1 & A2 & [A3a A3b] & A4 & A5 & A6 & A7).
  split; [lia|]. split; [|split; [lia | split; [exact X2 | lia]]].
  rewrite N. pose proof (Z.mod_pos_bound (8 * a + 30) 32 ltac:(lia)). pose proof (Z.mod_pos_bound ((a + 7) / 8 + 15) 16 ltac:(lia)).
  pose proof (Z.div_mod (8 * a + 30) 32 ltac:(lia)). pose proof (Z.div_mod ((a + 7) / 8 + 15) 16 ltac:(lia)).
  replace (8 * a + 30 - (8 * a + 30) mod 32 + 16 * a + ((a + 7) / 8 + 15 - ((a + 7) / 8 + 15) mod 16)) with (16 * (2 * ((8 * a + 30) / 32) + a + ((a + 7) / 8 + 15) / 16)) by lia.
  apply mod16_mul16.
Qed.
Lemma mod8_16a : ltac2:(tb__ "0|2|
S0S0S24S0S53R2Z8M0A2Z0M1A3S24S0S53S51R3S54Z10R2A2A2G0A2G1A3F_;Fx;FB;").
Proof. intros B x HB. apply mod8_add; [exact HB|]. replace (16 * x) with (8 * (2 * x)) by lia. apply mod8_mul8. Qed.
Lemma xsub_p2d : ltac2:(tb__ "0|6|
S50S45Vrho;Sf1A2S45Vrho;Sf0A2A2S24S0S53S45Vrho;Sf2A2M0Z8M1A2Z0M2A3S26S0S0S26S0S0S25S24S0G0S51G0R2A2M3A3S25S50G2R2A2S25S24S0S53G3G1A2G2A3S25S50S51R2S45Vrho;S140A2A2M4R1A2S25S50R1S45Vrho;S96Z1Sf0A2A2M5A2S27S24S0S53S51G0R1A2G1A2G2A3S24S0G4G5A3A2A2A2A2A2A2LM;A2Lo;A2F_;F_;").
Proof using Ha.
  intros HN HB8. destruct (needA_facts HN) as (N1 & N2 & N3 & N4 & N5). unfold x16f, r8f in *. rewrite (V_o16A rho Ha). change (uval rho pA) with a.
  pose proof (uval_range rho pKts). rewrite uval_kb by lia.
  assert (Z0 : (uval rho pDts + 0) mod 8 = 0) by (rewrite Z.add_0_r; exact HB8).
  pose proof (mod8_16a _ a HB8) as M8.
  exists 0, (16 * a). repeat split; first [lia | exact Z0 | left; exact M8].
Qed.
Lemma xsub_nxt : ltac2:(tb__ "0|6|
S50S45Vrho;Sf1A2S45Vrho;Sf0A2A2S24S0S53S45Vrho;Sf2A2M0Z8M1A2Z0M2A3S26S0S0S26S0S0S25S24S0S45Vrho;S142A2S51G0R2A2M3A3S25S50G2R2A2S25S24S0S53G3G1A2G2A3S25S50S51R2S45Vrho;S13fA2A2M4R1A2S25S50R1S45Vrho;S96Z1Sf0A2A2M5A2S27S24S0S53S51G0R1A2G1A2G2A3S24S0G4G5A3A2A2A2A2A2A2LM;A2Lo;A2F_;F_;").
Proof using Ha Hd.
  intros HN HB8. destruct (needA_facts HN) as (N1 & N2 & N3 & N4 & N5). unfold x16f, r8f in *. rewrite (V_pNXT rho Ha Hd), (V_o4A rho Ha). change (uval rho pA) with a. change (uval rho pDts) with d in HB8 |- *.
  pose proof (uval_range rho pKts). rewrite uval_kb by lia. set (x := 4 * a + 15 - (4 * a + 15) mod 16) in *.
  pose proof (mod8_16a _ a HB8) as M1. assert (M2 : (d + (16 * a + x)) mod 8 = 0) by (rewrite Z.add_assoc; apply mod8_add; [exact M1 | exact (mod8_of16 _ N4)]).
  exists (16 * a), (16 * a + x). repeat split; first [lia | exact M1 | left; exact M2].
Qed.
Lemma xsub_prv : ltac2:(tb__ "0|6|
S50S45Vrho;Sf1A2S45Vrho;Sf0A2A2S24S0S53S45Vrho;Sf2A2M0Z8M1A2Z0M2A3S26S0S0S26S0S0S25S24S0S45Vrho;S143A2S51G0R2A2M3A3S25S50G2R2A2S25S24S0S53G3G1A2G2A3S25S50S51R2S45Vrho;S13fA2A2M4R1A2S25S50R1S45Vrho;S96Z1Sf0A2A2M5A2S27S24S0S53S51G0R1A2G1A2G2A3S24S0G4G5A3A2A2A2A2A2A2LM;A2Lo;A2F_;F_;").
Proof using Ha Hd.
  intros HN HB8. destruct (needA_facts HN) as (N1 & N2 & N3 & N4 & N5). unfold x16f, r8f in *. rewrite (V_pPRV rho Ha Hd), (V_o4A rho Ha). change (uval rho pA) with a. change (uval rho pDts) with d in HB8 |- *.
  pose proof (uval_range rho pKts). rewrite uval_kb by lia. set (x := 4 * a + 15 - (4 * a + 15) mod 16) in *.
  pose proof (mod8_16a _ a HB8) as M0.
  assert (M1 : (d + (16 * a + x)) mod 8 = 0) by (rewrite Z.add_assoc; apply mod8_add; [exact M0 | exact (mod8_of16 _ N4)]).
  assert (M2 : (d + (16 * a + x + x)) mod 8 = 0) by (rewrite !Z.add_assoc; apply mod8_add; [apply mod8_add; [exact M0 | exact (mod8_of16 _ N4)] | exact (mod8_of16 _ N4)]).
  exists (16 * a + x), (16 * a + x + x). repeat split; first [lia | exact M1 | left; exact M2].
Qed.
Lemma xsub_rfx : ltac2:(tb__ "0|6|
S50S45Vrho;Sf1A2S45Vrho;Sf0A2A2S24S0S53S45Vrho;Sf2A2M0Z8M1A2Z0M2A3S26S0S0S26S0S0S25S24S0S45Vrho;S144A2S51G0R2A2M3A3S25S50G2R2A2S25S24S0S53G3G1A2G2A3S25S50S51R2S45Vrho;S141A2A2M4R1A2S25S50R1S45Vrho;S96Z1Sf0A2A2M5A2S27S24S0S53S51G0R1A2G1A2G2A3S24S0G4G5A3A2A2A2A2A2A2LM;A2Lo;A2F_;F_;").
Proof using Ha Hd.
  intros HN HB8. destruct (needA_facts HN) as (N1 & N2 & N3 & N4 & N5). unfold x16f, r8f in *. rewrite (V_pRFX rho Ha Hd), (V_orfx rho Ha). change (uval rho pA) with a. change (uval rho pDts) with d in HB8 |- *.
  pose proof (uval_range rho pKts). rewrite uval_kb by lia. set (x := 4 * a + 15 - (4 * a + 15) mod 16) in *. set (r := (a + 7) / 8) in *.
  pose proof (mod8_16a _ a HB8) as M0.
  assert (M1 : (d + (16 * a + x + x)) mod 8 = 0) by (rewrite !Z.add_assoc; apply mod8_add; [apply mod8_add; [exact M0 | exact (mod8_of16 _ N4)] | exact (mod8_of16 _ N4)]).
  assert (M2 : (d + uval rho needA) mod 8 = 0) by (apply mod8_add; [exact HB8 | exact (mod8_of16 _ N2)]).
  exists (16 * a + x + x), (uval rho needA). repeat split; first [lia | exact M1 | left; exact M2].
Qed.
End TSX2.

Lemma pg_vals : ltac2:(tb__ "0|5|
S3S2aS4A1S79S4S6R2A1R1A3S24S2dS196R2A1S2eA3S25S25S50Z4S45R4S7eA2M0A2S50G0S52Z2M1Z14A2A2A2S25S50S45R4Sf2A2S52G1Z2fA2A2S25S50S45R4S96Z3M2S7eA2A2S45R4Sf3A2M3A2S25S50G3Sc9A2S25S50S45R4S96G2S82A2A2S45R4S17dA2M4A2S25S50G4Sc9A2S50S45R4Sf1A2S45R4Sf0A2A2A2A2A2A2A2A2F_;F_;FF;Frho;").
Proof.
  intros rho F HF C. unfold pgF in C. rdF HF C F7. rdF HF C F6. rdF HF C F5. rdF HF C F4. rdF HF C F3. rdF HF C F2.
  pose proof (triA_vals rho F HF C) as HA. rewrite h_ule in F2, F3, F4, F5, F6, F7. unfold two47, RA.two47 in F2. unfold B32 in F4, F6 |- *.
  rewrite uval_lit in F2 by lia. rewrite uval_lit in F4 by lia. rewrite uval_lit in F6 by lia. repeat split; lia.
Qed.

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
Sc2S3S2aS77Q40A1A1Sc0OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
S155S58VAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S0S1b3VCST;R1A2S25S50Z0R2A2S55R2S17aA2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S0S1b3VXGL;R1A2S25S50Z0R2A2S55R2S17aA2A2F_;Fa;").
Hypothesis LFLAG : law_flag_stmt AInv.
Hypothesis LFSH : law_fshadow_stmt AInv.
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S2aS2cS2cS0S0A2S0A2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 6 BX.
Let HNP : NP_okA NF := NP_okA_intro NF eq_refl.
Variable rho0 : valuation.
Let HTOP : InitState.segs_top segs <= IMG_HI := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eb.Lib_arena_alloc.HTOP_ok.
Lemma HNPH : (NF <= NPH)%positive. Proof. unfold NF, NPH. lia. Qed.

Definition JLh (nd : ndesc) : jpostA := ltac2:(tb__ "0|0|
S6dVAInv;VCST;VXGL;VKc;Sb2VCST;VFB;VFF;A3VFB;VFF;VBX;S5dVnd;Aa").
Definition Posts_hfJ : list (axst * jpostA) := ltac2:(tb__ "0|1|
S2fS2cS3aSb8A2M0S2bS3aSb8S18bS11cS18fA1A4S2fG0S2bS3aSb8S18cS11cS190A1A4S30G0A1A3A3").
Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S6cVAInv;VCST;VXGL;S95VKc;Vrho0;Sb2VCST;VFB;VFF;A3VFB;VFF;VBX;S5dVnd;Ac").
Let nI : ltac2:(tb__ "0|0|
S2cS3aS59A2S165Fn;") := ltac2:(tb__ "0|0|
S71VAInv;VCST;VXGL;S95VKc;Vrho0;Sb2VCST;VFB;VFF;A3VFB;VFF;VBX;S5dAb").
Let Q (tp0 : list word) : assn := ltac2:(tb__ "0|0|
Sb9S58S95Vrho0;Vtp0;S11bA5").

Let siteP : ltac2:(tb__ "0|0|
Sc2S3S2aS4A1S2aS2cS2S2A2A1S2aS2cS2cS2S0A2S2A2A1S34S32A1S2aS5A1S3S2aS77Q40A1A1Sc0VAInv;RaR3R2R1A4S79S4S6RaA1R9A3S24S2dS123Sd7RaA2S2eA3SccS95Vrho0;RcA3Sb2VCST;VFB;VFF;Vrho0;A4S63Vrho0;RfA2S10bRfSc4Sc3R10A1A1A2S67VFB;R11A2S68VFF;R12A2S60VFB;R13R12R10A4S10aR13R11A2S109R14R12A2S64VFF;R16R15R12A4S24S2dS185R15R14R13R12S110R11A6S2eA3S178VCST;R18S36S0A1R17R12A5F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FR;Fskip;Ffr;Ftv;Ffacts;Frho;FAi;") := ltac2:(tb__ "0|0|
S117VAInv;VCST;VALA;S95S11aVFB;VFF;Vrho0;Sb2VCST;VFB;VFF;A3Sb3VCST;VFB;VFF;A3Sd7SfaAc").
Let siteF : ltac2:(tb__ "0|0|
Sc2S3S2aS4A1S2aS2cS2S2A2A1S2aS2cS2cS2S0A2S2A2A1S2aS5A1S3S2aS77Q40A1A1Sc0VAInv;R9R3R2R1A4S79S4S6R9A1R8A3S24S2dS123Sd7R9A2S2eA3SccS95Vrho0;RbA3Sb2VCST;VFB;VFF;Vrho0;A4S63Vrho0;ReA2S10bReSc4Sc3RfA1A1A2S60VFB;R10RfRdA4S10aR10ReA2S109R11RfA2S64VFF;R13R12RfA4S24S2dSe1R12R11R10S36S32A1S110RfA6S2eA3S1c3VCST;Vrho0;VFB;VFF;R14R12R11R10A8F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FR;Ffr;Ftv;Ffacts;Frho;FAi;") := ltac2:(tb__ "0|0|
S115VAInv;VCST;VALA;S95S11aVFB;VFF;Vrho0;Sb2VCST;VFB;VFF;A3Sb3VCST;VFB;VFF;A3Sd7SfaAc").
Let siteH : ltac2:(tb__ "0|1|
Sc2S3S2aS4A1S2aS2cS2S2A2A1S2aS2cS2cS2S0A2S2A2A1S2aS5A1S3S2aS77Q40A1A1Sc0VAInv;R9R3R2R1A4S79S4S6R9A1R8A3S24S2dS123Sd7R9A2S2eA3SccS95Vrho0;RbA3Sb2VCST;VFB;VFF;Vrho0;A4S63Vrho0;ReA2S10bReSc4Sc3RfA1A1A2S60VFB;R10RfRdA4S10aR10ReA2S109R11RfA2S64VFF;R13R12RfA4S24S2dSe1R12R11R10S36S32A1S110RfA6S2eA3S5S0Sc5S5R2R12A3S25S50S37S0S0S1dR17R3A2M0A3R2A2S55R2S38S0S0G0A3A2A2S27S16aVCST;Vrho0;S10cVFB;R18R16A3S167VFF;R18R15A3R3A5S27S25S50Z0R3A2S55R3S17aA2A2S177R3A1A2A2F_;F_;Fa;Fo;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FR;Ffr;Ftv;Ffacts;Frho;FAi;") := ltac2:(tb__ "0|0|
S116VAInv;VCST;VALA;S95S11aVFB;VFF;Vrho0;Sb2VCST;VFB;VFF;A3Sb3VCST;VFB;VFF;A3Sd7SfaAc").
Let siteX : ltac2:(tb__ "0|4|
Sc2S3S2aS4A1S2aS2cS2S2A2A1M0S2aS2cS2cS2S0A2S2A2M1A1M2S34S32A1M3S2aS5A1G0S3S2aS77Q40A1A1Sc0VAInv;RbR3R2R1A4S79S4S6RbA1RaA3S24S2dS123Sd7RbA2S2eA3SccS95Vrho0;RdA3Sb2VCST;VFB;VFF;Vrho0;A4S63Vrho0;R10A2S10bR10Sc4Sc3R11A1A1A2S67VFB;R12A2S68VFF;R13A2S60VFB;R14R13R11A4S10aR14R12A2S109R15R13A2S64VFF;R17R16R13A4S24S2dSe0VXGL;R16R15R14R13R12S111R11A8S2eA3S25S171VCST;VXGL;Vrho0;VFB;VFF;R18R16G3G2Lskip;R14S32S10fG1R1R16A3Li;R15X34x2R12A9S25S175VCST;VXGL;R19S36S0A1R18R12A6S1c4R18R12A2A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FX;Fobjs;Fskip;Ffr;Ftv;Ffacts;Frho;FAi;") := ltac2:(tb__ "0|0|
S118VAInv;VCST;VXGL;VALA;VHCST;VHXGL;S95S11aVFB;VFF;Vrho0;Sb2VCST;VFB;VFF;A3Sb3VCST;VFB;VFF;A3Sd7SfaAf").
Let site_pure : ltac2:(tb__ "0|2|
S3aSd8S2aS5A1S3S2aS2cS2S2A2A1S2aS2cS2cS2S0A2S2A2A1S2aS46A1S24S2dS123Sd7S9S3bR7A1A1A2S2eA3S24S2dS185S9S3bR8A1A1R4R3S36S32A1M0S110R6A6S2eA3S24S2dSe0VXGL;S9S3bR9A1M1A1R5R4G0ScG1A1S111S3cR9A1A8S2eA3S179VAInv;VCST;VXGL;S95Vrho0;Sb2VCST;VFB;VFF;A3VFB;VFF;RaR9R8R7S5cR6R5R4S5bA4S36S0A1Sc2Se5S29L_;L_;AfF_;F_;F_;Fbd;Ffr;Ftv;Frho;FR;Fs;FE;") := ltac2:(tb__ "0|0|
S119VAInv;VCST;VXGL;VALA;VHCST;VHXGL;S95S11aVFB;VFF;Vrho0;Sb2VCST;VFB;VFF;A3Sb3VCST;VFB;VFF;A3Sd7SfaAf").
Let payA_same : ltac2:(tb__ "0|1|
S2aS4A1S2aS46A1S24S2dS48R1A1S2eA3S174S95Vrho0;Sb2VCST;VFB;VFF;A3R3S7Z0M0A1G0R2R2A8F_;Fbd;Ffacts;") := ltac2:(tb__ "0|0|
S114S95Vrho0;Sb2VCST;VFB;VFF;A3A3").
Let frozen_stable : ltac2:(tb__ "0|0|
S1S1S59S3S187S95R3A2S24S2dS61R4R3A2S2eA3S76S58R6S70VAInv;VCST;VXGL;S95VKc;Vrho0;Sb2VCST;VFB;VFF;A3VFB;VFF;VBX;S5dR4R3AdA3F_;F_;Frho;Fnd;Fm;Fn;") := ltac2:(tb__ "0|0|
S113VAInv;VCST;VXGL;VALA;S95VKc;VHKc;VFB;VFF;VBX;Vrho0;Sb2VCST;VFB;VFF;A3Ac").
Let extra_client : ltac2:(tb__ "0|1|
S3S5S0S2aS2cS2S2A2A1S2aS2cS2cS2S0A2S2A2A1S124Sd7R5A2SccS95Vrho0;R6A3Sb2VCST;VFB;VFF;Vrho0;A4S24S2dS110R7A1S2eA3S25S50S37S0S0S1dR9R8A2M0A3R7A2S55R7S38S0S0G0A3A2A2S16aVCST;Vrho0;S10cVFB;RaR7A3S167VFF;RaR6A3R8A5F_;F_;F_;F_;F_;Ffrs;Fkept;Fa;Fo;Frho;") := ltac2:(tb__ "0|0|
S112VCST;S95S11aVFB;VFF;Vrho0;Sb2VCST;VFB;VFF;A3Sb3VCST;VFB;VFF;A3Sd7A9").

Lemma P0_now : ltac2:(tb__ "0|4|
S3SccS95Vrho0;R1A3Sb2VCST;VFB;VFF;Vrho0;A4S25S0S25S50S45R4S9bA2M0R1A2S55R1S51G0S45R4S9aA2A2A2A2S16aVCST;Vrho0;VFB;VFF;R2A5F_;Fa;S25S1b2VFF;S45R3S1b7A2Z518A3S25S1b2VFF;S45R3S1b6A2Z30A3S25S24S32S172Z3S7aS2cS2cS0S0A2M1S0A2G1S37G1S0A2VFF;A4M2A2U0M3A3S24S32S172Z6G2A2G3A3A2A2A2A2F_;F_;Frho;").
Proof.
  intros rho Hav HP. destruct (P0b_nowH CST NPH HNPH FB FF rho0 (P0_hf CST FB FF) (P0_hf_b CST FB FF) rho Hav HP) as (A & B & C).
  destruct HP as (_ & D & E). auto 6.
Qed.

Lemma tvz_in : ltac2:(tb__ "0|2|
S3S2aS2cS2S2A2M0A1S2S0S2S109R5R4A2Sc5G0S2bS2S2R4S96R3R2A2A4R5A3S25S55Z0M1R4A2S50R4ZcA2A2S50S45R8R4A2Sc9A2S28S24S0S45R9R5A2G1A3A1S28S24S0S45RaR8A2G1A3A1F_;F_;F_;F_;F_;Fk;Fe;Fd;Ftv;Frho;").
Proof.
  intros rho tv d e k HZ Hin He HK Hk Hd. pose proof (proj1 (Forall_forall _ _) HZ _ Hin) as X. cbv beta in X. unfold tnz, tvv in X. cbn [fst snd] in X.
  unfold uval in Hd, Hk, HK. specialize (X ltac:(intros H; exact (H Hd))). unfold B32 in HK.
  pose proof (uval_mul_lit rho e k ltac:(lia) ltac:(unfold uval; nia)) as E12. unfold uval, kb in E12. unfold kb in X. rewrite E12 in X. nia.
Qed.

Lemma foff_rng : ltac2:(tb__ "0|0|
S3S2aS4A1S0S79S4S6R3A1R2A3S24S2dS125R3A1S2eA3S25S50Z0R3A2S50R3Z200A2A2S24S0S45R6S8S9dS98S7R4A1A3A2S51S45R6S98A2R4A2A3F_;F_;F_;Foff;FF;Fr;").
Proof. intros r F off HF HFR Ho. unfold hF. apply (frame_off_rng hG 160 512 off r F sz_rng Ho HF HFR). Qed.

Lemma slot_rng : ltac2:(tb__ "0|1|
S3S2aS4A1S2S2S0S25S50Z0R1A2S50R1Z40A2A2S79S4S6R6A1R5A3S24S2dSc6S4S12SfR5S7Z800000000000A1A2A1R6A3S2eA3S24S2dSc6S4S12SfR5S7Sc9A1A2A1R7A3S2eA3S25S24S0S45R9S8S9dR7R6A3A2S51S45R9R7A2S45R9R6A2M0A2A3S25S24S0SdR9R6A2G0A3S24S0SdR9S8S9dR6S7R5A1A3A2S51G0R5A2A3A2A2F_;F_;F_;F_;Fw;Fcm;Fd;FF;Fr;").
Proof.
  intros r F d cm w Hw HF Hd Hs.
  pose proof (holds_mem _ _ _ HF Hd) as F1. pose proof (holds_mem _ _ _ HF Hs) as F2.
  rewrite h_ule in F1, F2. unfold B32 in F2. rewrite uval_lit in F1 by lia. rewrite uval_lit in F2 by lia.
  pose proof (uval_range r cm) as Rc. pose proof (uval_range r d) as Rd.
  assert (A12 : uval r (SAlu ALU_ADD cm (SLit w)) = uval r cm + w) by (apply uval_add_litZ; lia).
  split; [apply uval_add_small; lia|]. split; [apply soff_smallu; lia|]. rewrite <- A12. apply soff_smallu. rewrite A12. lia.
Qed.

Section X.
Variable TR : assn -> assn -> Prop.
Variable FAM : ltac2:(tb__ "0|0|
S0S2aS77Q40A1A1Sb5F_;F_;").
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S74S3aS3S2aS77Q40A1A1Sb5S79S4S6R3A1S9S3bR4A1A1A3VTR;S73S58R6R5R4R3A5R2A2M0F_;G0F_;FQ;Ftp;Frho;FS;FJ;").
Hypothesis TR_ex : forall (T : Type) (J : T -> jpredA) S rho tp (Q : assn),
  (forall x, TR (SPA segs (J x) S rho tp) Q) -> TR (SPA segs (fun r p t m => exists x, J x r p t m) S rho tp) Q.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
Sb5Sb5Sb5Sb4R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_exw : forall (T : Type) (P : T -> assn) (Q : assn), (forall a, TR (P a) Q) -> TR (fun w => exists a, P a w) Q.
Hypothesis TR_pureP : ltac2:(tb__ "0|1|
Sb5OSb5Sb4R4R1A1R4F_;Fw;R3VTR;R5R3A2M0F_;G0F_;F_;FQ;FX;FP;").
Hypothesis TR_post : ltac2:(tb__ "0|0|
Sb5Sb5Sb5Sb4R3R1A1R3R2A1F_;Fw;VTR;R4R3A2VTR;R5R3A2F_;F_;FQ';FQ;FP;").
Hypothesis TR_callP : ltac2:(tb__ "0|5|
S74S74S3aS3aSd8S2aS5A1M0S2aS2cS3aSb8A2M1A1S2aS2cS2S2A2M2A1Sb5S3S2aS77Q40A1A1M3G2Sc5G2R1R5A3Sc5G2R2S3cRbA1A3F_;Fr;S24S34G0A1SbaRaR9R8A3S35G0R7A2A3S24S2dSbcRbRaR9R8S7aG1S3aS37S3aSb8A2R7A4A5S2eA3S3G3VTR;S73S58RfRdR2R1A5Sb9S58SaS3bRdA1A1R2R1RaA5A2Ftp1;Frho1;S2aSc1A1M4Se5Sc0S75S58R9R8R10S2bG4Sd5R3Sd6R2R1A2A4A5R13RaR9R4R2A4R13Sd9SdaRbRfSf8R3RaR4A3A3R10A2RaR5R3A4F_;F_;Fmd;Fms;Ftr;S3aSb8G4Se5Sc0S3G3G4Se5Sc0Sc5G1S2bS3aSb8RaR9A4R14A3S75S58R12R11R19S2bG4Sd5R9Sd6R8R7A2A4A5R1cR13R12RaR8A4SccSaS3bR1aA1A1Sd9SdaR14R18Sf8R9R13RaA3A3R19A2R8A3S75S58R9R8ReS2bG4Sd5R7Sd6R6R5A2A4A5ReSd9SdaR16R1aSf8RbR15RcA3A3R1bA2R15RaR9R8R6A6S25S1c1R17Sf8RcR16RdA3R1bR1cR1dR10R1eR19RbA9S3ScdR18Sf8RdR17ReA3R1cR1dS3bR1eA1S3bR1fA1S3bR11A1R1RcA9VTR;S73S58SbeR11Sd9SdaR19R1dSf8ReR18RfA3A3R1eA2R18RdRcA5S1c2R1eR1fR12R20R1dR1bA6R2RcA5R1aA2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S73S58R11RfR8R7A5R9A2F_;F_;F_;F_;F_;F_;Ftp;Frho;FQ;FXk;FPosts;FR;Fs;FPre;FC;FJp;FJ;").

Hypothesis CVRESN : ltac2:(tb__ "0|1|
S2aS2cS0S0A2M0A1S2aS2cG0S0A2A1S4aS3S2aS77Q40A1A1S49Z3R3A2VTR;S73S58S62VAInv;VCST;VXGL;VKc;S19fR6R5A2R6R5R4S5dSeaAaSe6R3R2A5Sb9S58Sd4R3R2S168VAInv;VCST;VXGL;VKc;S19fS5dS8eR6R5R4AaA5A2F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Definition PD_pg : list (axst * ndesc) := ltac2:(tb__ "0|1|
S2fS2cS3aS59A2M0S2bS3aS59S1b8S160A4S2fG0S2bS3aS59S1b9S160A4S30G0A1A3A3").
Hypothesis CPG : ltac2:(tb__ "0|1|
S2aS2cS0S0A2M0A1S2aS2cG0S0A2A1S4aS3S2aS77Q40A1A1S49Z5R3A2VTR;S73S58S62VAInv;VCST;VXGL;VKc;S14bR6R5A2R6R5R4S5dS160AaS1baR3R2A5Sb9S58Sd4R3R2S168VAInv;VCST;VXGL;VKc;S14bS5dS1bbR6R5R4AaA5A2F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").

Hypothesis CSM : ltac2:(tb__ "0|2|
Sc2S3S2aS77Q40A1A1VTR;S73S58S152VAInv;Z3M0R3VKc;A4S90R2R1A5Sb9S58Sd4R2R1S2fS2cS3aSb8A2M1S2bS3aSb8S8dS14fVAInv;VCST;VXGL;G0R3VKc;A6A4S30G1A1A3A5A2Ftp1;Frho1;FAi;").
Hypothesis CMEMSET : ltac2:(tb__ "0|1|
Sc2S3S2aS77Q40A1A1VTR;S73S58S151VAInv;R3VKc;A3S8fR2R1A5Sb9S58Sd4R2R1S2fS2cS3aSb8A2M0S2bS3aSb8S8cS14cVAInv;VCST;VXGL;R3VKc;A5A4S30G0A1A3A5A2Ftp1;Frho1;FAi;").
Hypothesis CMEMCPY : ltac2:(tb__ "0|2|
Sc2S3S2aS77Q40A1A1VTR;S73S58S150VAInv;R3VKc;A3S108R2R1A5Sb9S58Sd4R2R1S2fS2cS3aSb8A2M0S2bS3aSb8S107S14cVAInv;VCST;VXGL;R3VKc;A5A4M1S2fG0G1S30G0A1A3A3A5A2Ftp1;Frho1;FAi;").
Hypothesis CF5 : ltac2:(tb__ "0|1|
Sc2S3S2aS77Q40A1A1VTR;S73S58S14eVAInv;R3VKc;A3S192R2R1A5Sb9S58Sd4R2R1S2fS2cS3aSb8A2M0S2bS3aSb8S191S14cVAInv;VCST;VXGL;R3VKc;A5A4S30G0A1A3A5A2Ftp1;Frho1;FAi;").

Definition pure_rule (Pre : axst) (Posts : list leafA) : Prop := ltac2:(tb__ "0|2|
S3aSd8S2aS5A1M0S3S2aS77Q40A1A1S59Sb5S24S34G0A1SbaR7VPre;R6A3S35G0R5A2A3S24S2dSbfR8VPre;R7R6S7aS3dS3aS40VPosts;A4A5S2eA3S24S2dS186S95SaS3bR9A1A1A2S2eA3S24S2dS61SaS3bRaA1A1R5A2S2eA3S24S2dSc8S4S23SaS3bRbA1M1A1A1S9G1A1A3S2eA3S3dS3Sc5S3dR2VPosts;A3S1bSaS3bRfA1A1RcR2A3VTR;S73S58VJAv;RbA1S164S9S3bR10A1A1SbdRfVPre;S40R4A1R10ReA5A2R3RcA5RaA2F_;F_;Frho';FL;VTR;S73S58VJAv;R8A1RdRaR9A5R7A2F_;F_;F_;F_;F_;F_;FQ;Fnd;Ftp;Frho;FR;Fs;FCl;").
Hypothesis CALL_pc : pure_rule Pre_pc Posts_pc.
Hypothesis CALL_da : pure_rule Pre_da Posts_da.
Hypothesis REENTER : ltac2:(tb__ "0|4|
S3aS59S2cS0S2A2M0S3S2aS77Q40A1A1M1S0G1Sc5S2cS2cS3aS59A2M2G0A2S2bG2G0S2bS3aS59R7R6A4R5A4S15eA3S25S50Z0S5aS2bG2G0S2bS3aS59R8R7A4R6A4R5A2M3A2S55G3R3A2A2VTR;S73S58VJAv;R8A1R9R6R5A5VFAM;R4R3A2A2F_;F_;Ftp0;Fb;Ftp;Frho;Frv;Fnd;FT;").
Hypothesis POST : ltac2:(tb__ "0|1|
S3aS59S3S2aS77Q40A1A1M0S0G0Sc5S2cS3aSb8A2S2bS3aSb8R6S11cR5A1A4S11bA3VTR;S73S58VJAv;R6A1R7R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;Fnd;FP;").

Ltac vmr := first [ lazymatch goal with |- @eq ?T ?t ?v => tryif first [ has_evar t | has_evar v ] then fail else vm_cast_no_check (@eq_refl T v) end
                  | vm_compute; reflexivity ].
Ltac peel H n := apply andb_prop in H as [H n].
Tactic Notation "innth" integer(n) := cbn [In cutsF2 exitsF2 Posts_hfJ PD_vn PD_pg]; do n right; left; reflexivity.

Lemma emeas_z0 : ltac2:(tb__ "0|0|
S3aS59S0S3S24S0S5aS2bS2cS3aS59A2S2cS0S2A2S2bS3aS59R4R3A4S2bS0S2R2Sa2A4A4R1A2S54R2S52Z2Z40A2A2A3Frho;Fr;Fnd;FT;").
Proof. intros. unfold emeasA, z0. cbn [eda_rank eda_var fst snd eval]. rewrite lit_unsigned by lia. lia. Qed.
Lemma emeas_eq : ltac2:(tb__ "0|1|
S3aS59S0S2S3S3S2S24S77Q40A1S11R2R1A2S11R3R1A2A3Fe;S24S0S5aS2bS2cS3aS59A2S2cS0S2A2S2bS3aS59R7R6A4S2bS0S2R5R4A4A4M0R2A2S5aG0R3A2A3F_;Frho';Frho;Fv;Fr;Fnd;FT;").
Proof. intros. unfold emeasA. cbn [eda_rank eda_var fst snd]. rewrite H. reflexivity. Qed.
Lemma emeas_lb : ltac2:(tb__ "0|0|
S3aS59S0S2S3S50Z0R3A2S50S54R4S52Z2Z40A2A2S5aS2bS2cS3aS59A2S2cS0S2A2S2bS3aS59R6R5A4S2bS0S2R4R3A4A4R2A2A2F_;Frho;Fv;Fr;Fnd;FT;").
Proof. intros. unfold emeasA. cbn [eda_rank eda_var fst snd]. pose proof (bv_urange (eval rho v)). lia. Qed.
Lemma emeas_ub : ltac2:(tb__ "0|0|
S3aS59S0S2S3S55S5aS2bS2cS3aS59A2S2cS0S2A2S2bS3aS59R5R4A4S2bS0S2R3R2A4A4R1A2S54S51R3Z1A2S52Z2Z40A2A2A2Frho;Fv;Fr;Fnd;FT;").
Proof. intros. unfold emeasA. cbn [eda_rank eda_var fst snd]. pose proof (bv_urange (eval rho v)). change (bv_modulus 64) with (2 ^ 64) in H. lia. Qed.

Lemma VM_meas : ltac2:(tb__ "0|7|
S3aS3aS59S59S0S2S2S0S0S3S3S50Z0M0R7A2S25S50S45R3R6A2S45R3R7A2M1A2S50G1S52Z2Z28A2A2A2S24S77Q40A1M2S11R3R8A2S11R4R8A2M3A3S24G2G3S11R5R8A2A3S50G0R8A2S55R9R8A2S55R9Z40A2S25S50G0S5aS2bS2cS3aS59A2M4S2cS0S2A2M5S2bS3aS59R11RfA4S2bS0S2ReSf9RdRcRbA3A4A4R8A2M6A2S55G6S5aS2bG4G5S2bS3aS59R12R10A4S2bS0S2ReSf9RdRcRaA3A4A4R9A2A2A2F_;F_;F_;F_;F_;F_;F_;Frho';Frho;Fb;Fa;Fc;Fe;Frk;FndT;FndX;FT;FX;").
Proof.
  intros X T ndX ndT rk e c a b rho rho' Hrk Hb He Hc Ha Hab Hb64. unfold emeasA. cbn [eda_rank eda_var fst snd].
  assert (EQ : uval rho' (VM e c a) = uval rho (VM e c a)) by (unfold uval, VM, kb; cbn [eval]; rewrite He, Hc; reflexivity).
  pose proof (VM_val rho e c a Hb ltac:(lia)) as V1. pose proof (VM_val rho e c b Hb ltac:(lia)) as V2. unfold uval in EQ, V1, V2.
  pose proof (bv_urange (eval rho' (VM e c a))). rewrite EQ, V1, V2. lia.
Qed.

Lemma VM_meas_sub : ltac2:(tb__ "0|5|
S3aS3aS59S59S0S2S2S0S0S3S3Sd8S1S50Z0M0R9A2S25S50S45R5R8A2S45R5R9A2M1A2S50G1S52Z2Z28A2A2A2SccR3R6R5A3S24S2dS18R4RbA2S2eA3S24S2dS18R5RbA2S2eA3S24S2dS15SdcR7RdA2RdA2S2eA3S24S2dS15SdcR8RdA2RdA2S2eA3S50G0RdA2S55ReRdA2S55ReZ40A2S25S50G0S5aS2bS2cS3aS59A2M2S2cS0S2A2M3S2bS3aS59R16R14A4S2bS0S2R13Sf9R12R11R10A3A4A4Sd9RdRcA2A2M4A2S55G4S5aS2bG2G3S2bS3aS59R17R15A4S2bS0S2R13Sf9R12R11RfA3A4A4ReA2A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fn;Fs;Frho';Frho;Fb;Fa;Fc;Fe;Frk;FndT;FndX;FT;FX;").
Proof.
  intros X T ndX ndT rk e c a b rho rho' s n Hrk Hb Hag Hbe Hbc Hse Hsc Ha Hab Hb64.
  apply sv_eqb_sound in Hse. apply sv_eqb_sound in Hsc.
  apply (VM_meas X T ndX ndT rk e c a b rho (rho_sub rho' s) Hrk Hb); [| |exact Ha|exact Hab|exact Hb64].
  - rewrite <- eval_subst, Hse. symmetry. exact (eval_agree_vals n rho rho' e Hag Hbe).
  - rewrite <- eval_subst, Hsc. symmetry. exact (eval_agree_vals n rho rho' c Hag Hbc).
Qed.

Lemma VM_meas_ag : ltac2:(tb__ "0|5|
S3aS3aS59S59S0S2S2S0S0S3S3S1S50Z0M0R8A2S25S50S45R4R7A2S45R4R8A2M1A2S50G1S52Z2Z28A2A2A2SccR3R5R4A3S24S2dS18R4RaA2S2eA3S24S2dS18R5RaA2S2eA3S50G0RaA2S55RbRaA2S55RbZ40A2S25S50G0S5aS2bS2cS3aS59A2M2S2cS0S2A2M3S2bS3aS59R13R11A4S2bS0S2R10Sf9RfReRdA3A4A4RaA2M4A2S55G4S5aS2bG2G3S2bS3aS59R14R12A4S2bS0S2R10Sf9RfReRcA3A4A4RbA2A2A2F_;F_;F_;F_;F_;F_;F_;F_;Fn;Frho';Frho;Fb;Fa;Fc;Fe;Frk;FndT;FndX;FT;FX;").
Proof.
  intros X T ndX ndT rk e c a b rho rho' n Hrk Hb Hag Hbe Hbc Ha Hab Hb64.
  apply (VM_meas X T ndX ndT rk e c a b rho rho' Hrk Hb); [| |exact Ha|exact Hab|exact Hb64].
  - symmetry. exact (eval_agree_vals n rho rho' e Hag Hbe).
  - symmetry. exact (eval_agree_vals n rho rho' c Hag Hbc).
Qed.

Lemma BUD_transfer_eq : ltac2:(tb__ "0|1|
Sd8S2aS46A1M0G0S2cS0S0A2S0S0S0S3S24G0S47R8R7A2R6A3S4bR7R6R5R4R3R2A6S4bR9R7R6R5R4Sd9R3RaA2A6F_;F_;Frho;FKf;FKm;FV;FBXv;Fbfrom;Fbto;Fs;").
Proof.
  intros s bto bfrom BXv V Km Kf rho E H. pose proof H as (A1 & A2 & A3 & A4 & A5 & Hw & Hn & B1 & B2). subst bfrom.
  rewrite bsumV_subst in B1. rewrite bsumK_subst in B2. rewrite bd_wpos_subst in Hw. apply bd_nn_subst in Hn.
  unfold BUD. repeat (split; [assumption|]). lia.
Qed.
Lemma JAi_transfer_eq : ltac2:(tb__ "0|1|
Sd8S1S59S59Sc2S0S3S3S2aS77Q40A1A1S2aSc1A1Sc0S24S2dSddRbS95A2S2eA3S187S95RbA2S24S2dS61RcRbA2S2eA3S24S2dS10eReS5eRcA1S5eRbA1A3S2eA3S24S2dS6bRfS66RdA1S66RcA1A3S2eA3S24S2aS46A1S47R10S5fRdA1A2S5fReA1A3S24S6fS6aR11S65ReA1A2S65RfA1A3S1bR11RcRbA3S69VAInv;VCST;VXGL;S95VKc;Vrho0;Sb2VCST;VFB;VFF;A3M0VFB;VFF;VBX;S5dR11RfReRdRbRaR9A12S69VAInv;VCST;VXGL;S95VKc;Vrho0;G0VFB;VFF;VBX;S5dR11R10RfSd9RdR14A2RcRbRaA12F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd;Ftr;Ftp;Frho';Frho;Fkc;FAi;Fndj;Fndi;Fn;Fs;").
Proof.
  intros s n ndi ndj Ai kc rho rho' tp tr md H1 H2 H3 H5 H6 H7 Ham Hag HJ.
  destruct (nd_below_split n ndi H3) as (Hbt & Hbf & Hbb & Hba).
  destruct HJ as (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & HFR & HK & HP0 & HXA & HBU & HPA & HCK & HCN).
  pose proof (agree_below_vals _ _ _ Hag) as Hav'.
  pose proof (rho_sub_agree s NPH rho' H1) as Hids.
  destruct (tv_sub_eqb_sound s _ _ rho' H5) as [M1 M2].
  assert (Hrm0 : forall a, rm rho' a = rm rho a).
  { intros a. destruct Hag as (_ & _ & Hm). symmetry. apply Hm. }
  assert (Hrm : forall a, rm (rho_sub rho' s) a = rm rho a).
  { intros a. cbn [rho_sub rm]. apply Hrm0. }
  split; [|split; [exact Hk|split; [|split; [exact HT|split; [exact HB|split; [exact HFF|split; [split; [|split]|split; [|split; [|split; [exact HP0|split; [|split; [|split; [exact HPA|split; [exact HCK|]]]]]]]]]]]]]].
  - eapply agree_vals_trans; [exact Hav|]. eapply agree_vals_trans; [eapply agree_vals_le; [exact H2|exact Hav']|].
    apply agree_below_vals. exact Hids.
  - eapply (law_vars _ _ _ ALA); [exact HM|]. apply functional_extensionality. exact Hrm.
  - eapply tvinA_map; [exact M1 | exact M2 |]. eapply tvinA_agree; [exact Hav' | exact Hbt | exact HN].
  - eapply tvd_map; [exact M1 | exact M2 |]. eapply tvd_agree; [exact Hav' | exact Hbt | exact HD].
  - eapply tvz_map; [exact M1 | exact M2 |]. eapply tvz_agree; [exact Hav' | exact Hbt | exact HZ].
  - eapply fr_sub_eqb_sound; [exact H6|]. eapply frinA_agree; [exact Hav' | exact Hbf | exact HFR].
  - eapply keptFA_eq_r; [exact HK | exact Hrm].
  - eapply XA_subst; [exact M1 |]. rewrite Ham. eapply XA_agree; [exact Hav' | exact Hrm0 | exact Hba | exact Hbt | exact HXA].
  - rewrite <- apot_subst, Ham, (apot_agree (nd_am ndi) n rho rho' Hav' Hrm0 Hba).
    eapply BUD_transfer_eq; [exact H7 |]. eapply BUD_agree; [exact Hav' | exact Hbb | exact HBU].
  - eapply capN_map; [exact M1|]. exact (capN_agree n BX Ai rho rho' _ Hav' Hbt HCN).
Qed.
Lemma SPA_entails_JA_eq : ltac2:(tb__ "0|1|
S3aS3aSd8S59S59S3S2aS77Q40A1A1Sb4S24S2dS43R8R7R6A3S2eA3S24S2dSddR7S95A2S2eA3S24S2dS186S95SaS3bRaA1A1A2S2eA3S24S2dS61SaS3bRbA1A1R8A2S2eA3S24S2dS10eRaS5eR9A1S5eR8A1A3S2eA3S24S2dS6bRbS66RaA1S66R9A1A3S2eA3S24S2aS46A1S47RcS5fRaA1A2S5fRbA1A3S24S2dS6eS6aRdS65RbA1A2S65RcA1A2S2eA3S73S58VJAv;RdA1M0R10RbRaR9A6S73S58G0R10Sd9RcRfA2RbRaA6F_;F_;F_;F_;F_;F_;F_;F_;F_;Fw;Ftp;Frho;Fndj;Fndi;Fs;FT;FL;").
Proof.
  intros L T s ndi ndj rho tp w He Hid Hnp Hnb Htv Hfr Hbd Ham [Hsm HJ]. apply Pos.leb_le in Hnp. apply am_eqb_sound in Ham.
  split; [eapply smatchA_entails; [exact He | exact Hsm]|].
  destruct w as [tr [ms md]]. cbn [w_tr w_cfg cfg_model] in HJ |- *. destruct HJ as (Ai & kc & HJ). exists Ai, kc.
  exact (JAi_transfer_eq s (ss_next (ax_S L)) ndi ndj Ai kc rho rho tp tr md Hid Hnp Hnb Htv Hfr Hbd Ham (agree_below_refl _ _) HJ).
Qed.

Lemma forallb_firstn : forall {A} (f : A -> bool) n (l : list A), forallb f l = true -> forallb f (firstn n l) = true.
Proof.
  intros A f n. induction n as [|n IH]; intros [|x l] H; cbn in *; try reflexivity.
  apply andb_prop in H as [H1 H2]. rewrite H1, (IH l H2). reflexivity.
Qed.
Lemma bsum_firstn : ltac2:(tb__ "0|1|
S2aS46A1S32S3S24S2dS48R3A1S2eA3S4cR4R2A2S25S50S4eS7bS46R4R5A3M0R3A2S4eR5R3A2A2S25S50S4dG0R3A2S4dR5R3A2A2S4cG0R3A2A2A2F_;F_;Frho;Fn;Fb;").
Proof.
  intros b. induction b as [|it r IH]; intros [|n] rho Hw Hn; cbn.
  - repeat split; try lia. constructor.
  - repeat split; try lia. constructor.
  - pose proof (bsum_nonneg (it :: r) rho Hw Hn) as [N1 N2]. cbn in N1, N2. repeat split; try lia. constructor.
  - unfold bd_wpos in Hw. cbn in Hw. apply andb_prop in Hw as [Hi Hw]. apply andb_prop in Hi as [Hv Hk]. apply Z.leb_le in Hv. apply Z.leb_le in Hk.
    inversion Hn as [|x l Hit Hr]; subst.
    destruct (IH n rho Hw Hr) as (I1 & I2 & I3). repeat split; try nia. constructor; [exact Hit | exact I3].
Qed.
Lemma payA_firstn : ltac2:(tb__ "0|1|
S2aS4A1S2aS46A1S32S24S2dS48R2A1S2eA3S174S95Vrho0;Sb2VCST;VFB;VFF;A3R4S7Z0M0A1G0R3S7bS46R2R3A3A8F_;Fn;Fb;Ffacts;").
Proof.
  intros facts b n Hw. split; [exact (forallb_firstn _ n b Hw)|]. split; [lia|].
  intros rho _ _ _ Hn. destruct (bsum_firstn b n rho Hw Hn) as (I1 & I2 & I3). unfold pay_sem. rewrite uval_lit by lia. split; [lia|]. split; [lia | exact I3].
Qed.
Lemma drop_imp : ltac2:(tb__ "0|0|
S3aS2aS2cS2S2A2A1S2aS2cS2cS2S0A2S2A2A1S2aS46A1S32S3S2aS77Q40A1A1Sb4S24S2dS48R5A1S2eA3S73S58VJAv;S5cR8R7R6S5bA4A1R9R4R3R2A6S73S58VJAv;S5cR9R8S7bS46R6R7A3S5bA4A1RaR5R4R3A6F_;F_;Fw;Ftp;Frho;Fn;Fbd;Ffr;Ftv;FA;").
Proof.
  intros A tv fr bd n rho tp w Hw Hx.
  exact (JA_repay segs AInv CST XGL NPH Kc rho0 (P0_hf CST FB FF) FB FF BX PTrue tv fr bd (firstn n bd) ANone A rho tp w (payA_firstn _ bd n Hw) Hx).
Qed.

Lemma live_holds : ltac2:(tb__ "0|1|
S59S3S2aS77Q40A1A1S2aSc1A1Sc0S2S0S2VJAv;R8R7R6R5R4A5Sc5S2cS2S2A2S2bS2S2R4S96R3R2A2A4S5eR9A1A3S25S55Z0M0R4A2S50R4ZcA2A2S50S45RaR4A2Sc9A2S28S24S0S45RbR5A2G0A3A1S6RcSfS7S17aA1R8A2A2F_;F_;F_;F_;F_;Fk;Fe;Fd;Fmd;Ftr;Ftp;Frho;Fnd;").
Proof.
  intros nd rho tp tr md d e k HJ Hin He HK Hk.
  assert (TNZ : tnz rho (d, kb e k)).
  { destruct HJ as (Ai & kc & _ & _ & _ & _ & _ & _ & (_ & _ & HZ) & _). unfold tnz. cbn [fst]. exact (tvz_in rho _ d e k HZ Hin He HK Hk). }
  pose proof (JA_tv_facts segs AInv CST XGL NPH Kc rho0 (P0_hf CST FB FF) FB FF BX PTrue ALA _ _ _ _ _ (d, kb e k) eq_refl HJ Hin TNZ) as TF.
  apply (proj1 (Forall_forall _ _) TF). unfold tv_factsA. cbn [fst snd]. do 5 right. left. reflexivity.
Qed.

Lemma k_nz_lit : ltac2:(tb__ "0|2|
S3S2aS4A1S2S0S2S79S4S6R5A1R4A3S25S55Z0M0R3A2S55R3S52Z2Z20A2A2A2S24S2dS134R5R4R3R6A4S2eA3S25S50S45R8R4A2M1Sc9A2S28S24S0G1G0A3A1A2F_;F_;F_;Fk;Fc;Fx;FF;Frho;").
Proof.
  intros rho F x c k HF Hc C. unfold liveF in C. apply andb_prop in C as [C H3]. apply andb_prop in C as [H1 H2].
  pose proof (holds_mem _ _ _ HF H1) as F1. pose proof (holds_mem _ _ _ HF H2) as F2. rewrite h_ule in F1, F2. unfold B32 in *. rewrite uval_lit in F2 by lia.
  assert (F3 : uval rho x <= 2 ^ 32) by (apply orb_prop in H3 as [H3|H3]; pose proof (holds_mem _ _ _ HF H3) as F3; rewrite h_ule in F3; [rewrite uval_lit in F3 by lia|]; lia).
  pose proof (uval_range rho x) as Rx. rewrite uval_add_litZ in F1 by lia. lia.
Qed.

Lemma xff_imp : ltac2:(tb__ "0|0|
S74S3aS3aS3aS2aS182A1S2aS4A1S3S2aS77Q40A1A1Sb4S24S34S3aA1S183R8R5A2S35S3aR7A2A3S24S3aS164R5R8A2R7A3S24S2dS12dR9R6A2S2eA3S2aSc1A1Sc0ReR8R7R2R1A4S79S4S6R9A1S9S3bRdA1A1A3S79S4S6RaA1RbA3F_;F_;Fmd;Ftr;S73S58RdRcR7R6R5A6S73S58ReRbR8R7R6A6F_;F_;F_;F_;F_;Fw;Ftp;Frho;FF;Fxf;FT2;FT1;FT0;FJ;").
Proof.
  intros J T0 T1 T2 xf F rho tp w HT1 HT2 Hb HF Hw. rewrite <- HT2. unfold xff_chk in Hb.
  change (ax_add_facts F T1) with (ax_with_facts T1 (F ++ ss_facts (ax_S T1))).
  apply (SPA_refacts_JA segs); [| exact Hb | intros tr md HJ HF1; apply Forall_app; split; [exact (HF tr md HJ HF1) | exact HF1]].
  exact (SPA_axforms segs _ xf rho T0 T1 tp w HT1 Hw).
Qed.

Lemma facts_imp : ltac2:(tb__ "0|0|
S74S3aS3aS2aS4A1S3S2aS77Q40A1A1Sb4S24S3aS164R4R6A2R5A3S24S2dS12dR7R5A2S2eA3S2aSc1A1Sc0RbR7R6R2R1A4S79S4S6R8A1S9S3bRbA1A1A3S79S4S6R9A1RaA3F_;F_;Fmd;Ftr;S73S58RaR9R6R5R4A6S73S58RbR9R7R6R5A6F_;F_;F_;F_;Fw;Ftp;Frho;FF;FT2;FT1;FJ;").
Proof.
  intros J T1 T2 F rho tp w HT2 Hb HF Hw. rewrite <- HT2. unfold xff_chk in Hb.
  change (ax_add_facts F T1) with (ax_with_facts T1 (F ++ ss_facts (ax_S T1))).
  apply (SPA_refacts_JA segs); [exact Hw | exact Hb | intros tr md HJ HF1; apply Forall_app; split; [exact (HF tr md HJ HF1) | exact HF1]].
Qed.

Lemma slot_rng2 : ltac2:(tb__ "0|1|
S3S2S2S2S0S25S50Z0R1A2S50R1Z40A2A2S24S0S45R6R3A2S45R6R4A2A3S50S45R7R6A2Z800000000000A2S50S45R8R6A2S52Z2Z28A2A2S25S24S0S45R9S8S9dR8R6A3A2S51S45R9R8A2S45R9R7A2M0A2A3S25S24S0SdR9R7A2G0A3S24S0SdR9S8S9dR7S7R5A1A3A2S51G0R5A2A3A2A2F_;F_;F_;F_;Fw;Fcm';Fcm;Fd;Fr;").
Proof.
  intros r d cm cm' w Hw Hc Hd Hs. pose proof (uval_range r cm) as Rc. pose proof (uval_range r d) as Rd.
  assert (A12 : uval r (SAlu ALU_ADD cm (SLit w)) = uval r cm + w) by (apply uval_add_litZ; lia).
  split; [rewrite uval_add_small by lia; lia|]. split; [apply soff_smallu; lia|]. rewrite <- A12. apply soff_smallu. rewrite A12. lia.
Qed.
Lemma reshape_fwd : ltac2:(tb__ "0|3|
S74S3aS32S2S2S2S0S14S3S2aS77Q40A1A1Sb4S24S34S5A1Sc7S5ScS3bRaA1A1R9A3S35S5SeR8R7S8S9dR7S7R5A1A3S30S10A1M0R4A5A2A3S24S2dS16R5A1S2eA3S24S2dS17SaS3bRcA1A1SeS8S9dRaR8A3S7Z0M1A1M2S7R7A1G0SbA5A2S2eA3S25S50G1R8A2S50R8Z40A2A2S3S24S0S45R1RbA2S45R1RcA2A3Fr;S79S4S6R8A1S9S3bRfA1A1A3S25S50S45R9ReA2Z800000000000A2S50S45R9RdA2S52Z2Z28A2A2A2F_;S73S58R11R10R9R8R7A6S73S58R12S81R11R10SeS8S9dRfRdA3G2S7RcA1G0SbA5A3RaR9R8A6F_;F_;F_;F_;F_;F_;F_;Fwd;Ftp;Frho;Fdfl;Fw;Fcm';Fcm;Fd;Fi;FA;FJ;").
Proof.
  intros J A i d cm cm' w dfl rho tp wd Hn Hdw Hwf Hw Hc Hb Hx. unfold reshapeA.
  apply (SPA_reshape segs _ rho A i _ _ tp wd Hn); [reflexivity | reflexivity | exact Hdw | exact Hwf | | exact Hx].
  intros HF. destruct (Hb HF) as [Bd Bc]. destruct (slot_rng2 rho d cm cm' w Hw (Hc rho) Bd Bc) as (A1 & A2 & A3).
  unfold obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite !soff_lit_small by lia. rewrite A2, A3.
  change (bv_unsigned (eval rho (SAlu ALU_ADD d cm'))) with (uval rho (SAlu ALU_ADD d cm')). rewrite A1. unfold uval. lia.
Qed.
Lemma reshape_bwd : ltac2:(tb__ "0|2|
S74S3aS32S2S2S2S0S14S3S2aS77Q40A1A1Sb4S24S34S5A1Sc7S5ScS3bRaA1A1R9A3S35S5SeS8S9dR8R6A3S7Z0M0A1S7R5A1S30S10A1M1R4A5A2A3S24S2dS16R5A1S2eA3S24S2dS17SaS3bRcA1A1SeRaR9S8S9dR9S7R7A1A3G1SbA5A2S2eA3S25S50G0R8A2S50R8Z40A2A2S3S24S0S45R1RbA2S45R1RcA2A3Fr;S79S4S6R8A1S9S3bRfA1A1A3S25S50S45R9ReA2Z800000000000A2S50S45R9RdA2S52Z2Z28A2A2A2F_;S73S58R11R10R9R8R7A6S73S58R12S81R11R10SeRfReS8S9dReS7RcA1A3G1SbA5A3RaR9R8A6F_;F_;F_;F_;F_;F_;F_;Fwd;Ftp;Frho;Fdfl;Fw;Fcm';Fcm;Fd;Fi;FA;FJ;").
Proof.
  intros J A i d cm cm' w dfl rho tp wd Hn Hdw Hwf Hw Hc Hb Hx. unfold reshapeA.
  apply (SPA_reshape segs _ rho A i _ _ tp wd Hn); [reflexivity | reflexivity | exact Hdw | exact Hwf | | exact Hx].
  intros HF. destruct (Hb HF) as [Bd Bc]. destruct (slot_rng2 rho d cm cm' w Hw (Hc rho) Bd Bc) as (A1 & A2 & A3).
  unfold obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite !soff_lit_small by lia. rewrite A2, A3.
  change (bv_unsigned (eval rho (SAlu ALU_ADD d cm'))) with (uval rho (SAlu ALU_ADD d cm')). rewrite A1. unfold uval. lia.
Qed.

Lemma rs_bnd_lit : ltac2:(tb__ "0|0|
S3S2aS4A1S2S2S79S4S6R4A1R3A3S24S2dS13bR3R2R4A3S2eA3S25S50S45R6R4A2Z800000000000A2S50S45R6R3A2S52Z2Z28A2A2A2F_;F_;Fcm;Fd;FF;Frho;").
Proof.
  intros rho F d cm HF C. unfold rsF in C. apply andb_prop in C as [H1 H2]. pose proof (holds_mem _ _ _ HF H1) as F1. pose proof (holds_mem _ _ _ HF H2) as F2.
  rewrite h_ule in F1, F2. unfold B32 in F2. rewrite uval_lit in F1 by lia. rewrite uval_lit in F2 by lia. lia.
Qed.
Lemma rs_bnd_kb : ltac2:(tb__ "0|1|
S3S2aS4A1S2S0S2S2S79S4S6R6A1R5A3S25S55Z0R4A2S50R4ZcA2A2S24S2dS129R6R4R3R7A4S2eA3S25S50S45R9R7A2Z800000000000A2S25S50S45R9S96R6R5A2A2M0S52Z2Z28A2A2S24S0S45R9S13S9eR5S7R6A1A3A2G0A3A2A2F_;F_;F_;Fk;Fc;Fe;Fd;FF;Frho;").
Proof.
  intros rho F d e c k HF He C. unfold rsFk in C. rdF HF C F3. rdF HF C F2. pose proof (holds_mem _ _ _ HF C) as F1.
  rewrite h_ule in F1, F2, F3. unfold B32 in F3. rewrite uval_lit in F1 by lia. rewrite uval_lit in F3 by lia. pose proof (uval_range rho c) as Rc.
  assert (E1 : uval rho (kb e c) = e * uval rho c) by (apply uval_kb; nia).
  assert (E2 : uval rho (SMd M_MUL c (SLit e)) = e * uval rho c) by (apply uval_mulc; nia).
  rewrite E1, E2. nia.
Qed.
Lemma uval_sext32 : ltac2:(tb__ "0|0|
S3S2S24S0S45R2S19S39Q20R1A3A2S53S45R2R1A2S52Z2Z20A2A2A3Fe;Frho;").
Proof. intros rho e. unfold uval. cbn [eval]. change 32%N with (8 * N.of_nat 4)%N. rewrite ext_low_false_unsigned by lia. reflexivity. Qed.
Lemma rs_bnd_gz : ltac2:(tb__ "0|0|
S3S2aS4A1S2S2S79S4S6R4A1R3A3S24S2dSc6S4S12SfR3S7ScaA1A2A1R4A3S2eA3S25S50S45R6R4A2Z800000000000A2S50S45R6S13S9eS19S39Q20R3A3S7ZcA1A3A2S52Z2Z28A2A2A2F_;F_;Fe0;Fd;FF;Frho;").
Proof.
  intros rho F d e0 HF H1. pose proof (holds_mem _ _ _ HF H1) as F1. rewrite h_ule in F1. unfold two47, RA.two47 in F1. rewrite uval_lit in F1 by lia.
  pose proof (uval_range rho e0). pose proof (Z.mod_pos_bound (uval rho e0) (2 ^ 32) ltac:(lia)).
  rewrite uval_mulc by (rewrite ?uval_sext32; lia). rewrite uval_sext32. lia.
Qed.
Lemma rs_bnd_gv : ltac2:(tb__ "0|1|
S3S2aS4A1S2S2S79S4S6R4A1R3A3S24S2dS31S31Sc6S4S12SfR3S7ScaA1A2A1R4A3Sc6S4S12S1aR2S7eA2A1R4A3A2Sc6S4S12SfS7eS7S52Z2M0Z14A2A1A2A1R4A3A2S2eA3S25S50S45R6R4A2Z800000000000A2S50S45R6S13S9eR3S7ZcA1A3A2S52G0Z28A2A2A2F_;F_;Fv;Fd;FF;Frho;").
Proof.
  intros rho F d v HF C. rdF HF C F3. rdF HF C F2. pose proof (holds_mem _ _ _ HF C) as F1.
  rewrite h_ule in F1, F3. rewrite h_ult in F2. unfold two47, RA.two47 in F1. rewrite uval_lit in F1 by lia. rewrite uval_lit in F3 by lia.
  rewrite uval_mulc by lia. lia.
Qed.
Lemma rs_bnd_mc : ltac2:(tb__ "0|0|
S3S2aS4A1S2S0S2S2S79S4S6R6A1R5A3S25S55Z0R4A2S50R4ZcA2A2S24S2dS129R6R4R3R7A4S2eA3S25S50S45R9R7A2Z800000000000A2S50S45R9S13S9eR5S7R6A1A3A2S52Z2Z28A2A2A2F_;F_;F_;Fk;Fc;Fe;Fd;FF;Frho;").
Proof. intros rho F d e c k HF He C. destruct (rs_bnd_kb rho F d e c k HF He C) as (A1 & A2 & A3). rewrite A3. split; assumption. Qed.
Lemma uval_mulc_kb : ltac2:(tb__ "0|0|
S3S2S0S24S0S45R3S13S9eR2S7R1A1A3A2S45R3S96R1R2A2A2A3Fe;Fc;Fr;").
Proof. intros. unfold kb. apply uval_mul_comm. Qed.
Lemma sext_lt : ltac2:(tb__ "0|0|
S3S2S2S6R3S1aR2R1A2A2S55S45R4S19S39Q20R3A3A2S45R4R2A2A2F_;Fb;Fv;Frho;").
Proof. intros rho v b H. rewrite h_ult in H. rewrite uval_sext32. pose proof (uval_range rho v). pose proof (Z.mod_le (uval rho v) (2 ^ 32) ltac:(lia) ltac:(lia)). lia. Qed.

Lemma reshape_ffwd : ltac2:(tb__ "0|3|
S74S3aS32S0S0S14S3S2aS77Q40A1A1Sb4S24S34S5A1Sc7S5ScS3bR8A1A1R7A3S35S5SeS98S7R6A1S7R5A1S30S10A1M0R4A5A2A3S24S2dS16R5A1S2eA3S24S2dS17SaS3bRaA1A1SeS8S9dS98S7R8A1A3S7Z0M1A1M2S7S56R7R8A2A1G0SbA5A2S2eA3S25S50G1R9A2S50R9R8A2A2S50R9Z200A2S24S2dS125S9S3bRdA1A1A1S2eA3S73S58RfReR9R8R7A6S73S58R10S81RfReSeS8S9dS98S7RdA1A3G2S7S56RcRdA2A1G0SbA5A3RaR9R8A6F_;F_;F_;F_;F_;F_;F_;Fwd;Ftp;Frho;Fdfl;Fb;Fa;Fi;FA;FJ;").
Proof.
  intros J A i a b dfl rho tp wd Hn Hdw Hwf Hab Hb HfF Hx. unfold reshapeA.
  apply (SPA_reshape segs _ rho A i _ _ tp wd Hn); [reflexivity | reflexivity | exact Hdw | exact Hwf | | exact Hx].
  intros HF. pose proof (foff_rng rho _ a HF HfF ltac:(lia)) as A1.
  unfold obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite !soff_lit_small by lia.
  change (bv_unsigned (eval rho (SAlu ALU_ADD hF (SLit a)))) with (uval rho (SAlu ALU_ADD hF (SLit a))). rewrite A1. unfold uval. lia.
Qed.

Lemma reshape_ffwd_c : ltac2:(tb__ "0|3|
S74S3aS32S0S0S2aS10A1S14S3S2aS77Q40A1A1Sb4S24S34S5A1Sc7S5ScS3bR9A1A1R8A3S35S5SeS98S7R7A1S7R6A1R5R4A5A2A3S24S2dS16R5A1S2eA3S24S2dS17SaS3bRbA1A1SeS8S9dS98S7R9A1A3S7Z0M0A1M1S7S56R8R9A2A1S30S10A1M2SbA5A2S2eA3S25S50G0RaA2S50RaR9A2A2S50RaZ200A2S24S2dS125S9S3bReA1A1A1S2eA3S73S58R10RfR9R8R7A6S73S58R11S81R10RfSeS8S9dS98S7ReA1A3G1S7S56RdReA2A1G2SbA5A3RaR9R8A6F_;F_;F_;F_;F_;F_;F_;Fwd;Ftp;Frho;Fdfl;Fcs;Fb;Fa;Fi;FA;FJ;").
Proof.
  intros J A i a b cs dfl rho tp wd Hn Hdw Hwf Hab Hb HfF Hx. unfold reshapeA.
  apply (SPA_reshape segs _ rho A i _ _ tp wd Hn); [reflexivity | reflexivity | exact Hdw | exact Hwf | | exact Hx].
  intros HF. pose proof (foff_rng rho _ a HF HfF ltac:(lia)) as A1.
  unfold obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite !soff_lit_small by lia.
  change (bv_unsigned (eval rho (SAlu ALU_ADD hF (SLit a)))) with (uval rho (SAlu ALU_ADD hF (SLit a))). rewrite A1. unfold uval. lia.
Qed.
Lemma reshape_fbwd : ltac2:(tb__ "0|2|
S74S3aS32S0S0S14S3S2aS77Q40A1A1Sb4S24S34S5A1Sc7S5ScS3bR8A1A1R7A3S35S5SeS8S9dS98S7R6A1A3S7Z0M0A1S7S56R5R6A2A1S30S10A1M1R4A5A2A3S24S2dS16R5A1S2eA3S24S2dS17SaS3bRaA1A1SeS98S7R8A1S7R7A1G1SbA5A2S2eA3S25S50G0R9A2S50R9R8A2A2S50R9Z200A2S24S2dS125S9S3bRdA1A1A1S2eA3S73S58RfReR9R8R7A6S73S58R10S81RfReSeS98S7RdA1S7RcA1G1SbA5A3RaR9R8A6F_;F_;F_;F_;F_;F_;F_;Fwd;Ftp;Frho;Fdfl;Fb;Fa;Fi;FA;FJ;").
Proof.
  intros J A i a b dfl rho tp wd Hn Hdw Hwf Hab Hb HfF Hx. unfold reshapeA.
  apply (SPA_reshape segs _ rho A i _ _ tp wd Hn); [reflexivity | reflexivity | exact Hdw | exact Hwf | | exact Hx].
  intros HF. pose proof (foff_rng rho _ a HF HfF ltac:(lia)) as A1.
  unfold obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite !soff_lit_small by lia.
  change (bv_unsigned (eval rho (SAlu ALU_ADD hF (SLit a)))) with (uval rho (SAlu ALU_ADD hF (SLit a))). rewrite A1. unfold uval. lia.
Qed.

Lemma xr_ok_prefix : ltac2:(tb__ "0|2|
S3S2aS5A1S0S2S2S2S2S24S77Q40A1S11R7R2A2S11R7R4A2A3S27S50S51S45R8R2A2M0Z8A2S45R8R4A2M1A2S24S0G0G1A3A2S3eR9R8R7S2bS2S2R6R5A4A4S3eRaR9R8S2bS2S2R5R4A4A4F_;F_;F_;Fl';Fb';Fl;Fb;Foff;Fobjs;Frho;").
Proof.
  intros rho objs off b l b' l' Eb Hl (HB8 & HBL & Hall). unfold xr_ok. cbn [fst snd] in *. rewrite Eb. unfold uval in Hl.
  pose proof (bv_urange (eval rho l')) as Rl'. change (bv_modulus 64) with (2 ^ 64) in Rl'.
  split; [exact HB8|]. split; [lia|]. intros a Ha.
  destruct (Hall a ltac:(lia)) as (G1 & G2 & G3 & v & Gv & Gd). split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. exists v. split; [exact Gv|].
  destruct Gd as [Gd|[Gv2 Ga]]; [left; exact Gd|]. destruct Hl as [Hl|Hl].
  - exfalso. pose proof (Z.mul_div_le (bv_unsigned (eval rho b) + bv_unsigned (eval rho l)) 8 ltac:(lia)).
    pose proof (Z.div_mod a 8 ltac:(lia)). pose proof (Z.mod_pos_bound a 8 ltac:(lia)). nia.
  - right. rewrite Hl. split; [exact Gv2 | exact Ga].
Qed.
Lemma publish_prefix_imp : ltac2:(tb__ "0|4|
S74S3aS2S2S2S2S3S2aS77Q40A1M0A1Sb4S24S2dSc6S2cS2S2A2M1S16cS2bS2S2R7R6A4A1S3cR8A1A3S2eA3S24S2dS41SaS3bR9A1A1S2bS2S2R6R5A4A2S2eA3S79S4S6R5A1S9S3bRaA1A1A3S25S24G0S11R6R8A2S11R6RaA2A3S27S50S51S45R6R7A2M2Z8A2S45R6R9A2M3A2S24S0G2G3A3A2A2F_;S73S58RcRbR6R5R4A6S73S58RdS166RcS2fG1S2bS2S2R9R8A4S3cRcA1A3A2R7R6R5A6F_;F_;F_;F_;Fw;Ftp;Frho;Fl';Fb';Fl;Fb;FA;FJ;").
Proof.
  intros J A b l b' l' rho tp w Hin Hb Hsem Hx. apply SPA_x_publish; [exact Hb | | exact Hx].
  pose proof Hx as [(Hsm & _ & _ & Hsh & _) _]. destruct (Hsem (smatchA_facts segs _ _ _ _ (proj1 Hx))) as [E1 E2].
  apply existsb_exists in Hin as (r & Hr & Heq). unfold xr_eqb in Heq. apply andb_prop in Heq as [Q1 Q2]. apply sv_eqb_sound in Q1. apply sv_eqb_sound in Q2.
  destruct r as [rb rl]. cbn in Q1, Q2. subst rb rl.
  apply (xr_ok_prefix rho _ _ b l b' l' E1 E2). unfold shadow_ok in Hsh. exact (proj1 (Forall_forall _ _) Hsh _ Hr).
Qed.
Lemma subX_imp : ltac2:(tb__ "0|0|
S74S3aS3aS2aS2cS2S2A2A1S3S2aS77Q40A1A1Sb4S24S3aS166R6R4A2R5A3S24S2dS16bR5S3cR7A1A2S2eA3S73S58R9R8R5R4R3A6S73S58RaR8R6R5R4A6F_;F_;F_;Fw;Ftp;Frho;FX';FB;FA;FJ;").
Proof. intros J A B X' rho tp w HB Hi Hx. rewrite <- HB. apply (SPA_x_sub segs); [exact (xrs_inclb_sound _ _ Hi) | exact Hx]. Qed.

Lemma reopen_imp : ltac2:(tb__ "0|1|
S3aS2aS2cS2S2A2A1M0G0S2aS46A1S0S0S3S2aS77Q40A1A1Sb4S24S2dS139VXGL;R9R8R7R5R4A6S2eA3S73S58VJAv;S5cR8S7dR7S5bA4A1RaR4R3R2A6S73S58VJAv;S5cR9S7dR8S5bA4A1Se2RbRaS97R7R6A5R5R4R3A6F_;F_;Fw;Ftp;Frho;Fk2;Fk1;Fbd;Ftv;FX';FA;").
Proof.
  intros A X' tv bd k1 k2 rho tp w CK Hw.
  unfold reopen_chk in CK. peel CK HXL. peel CK HRO. peel CK HB. peel CK Hwf. peel CK HXi. peel CK Hfe. peel CK Hk3. peel CK Hk2. peel CK Hk1. rename CK into Hbase.
  apply sv_eqb_sound in Hbase. apply Z.leb_le in Hk1. apply Z.leb_le in Hk2. apply Z.leb_le in Hk3.
  apply (JA_shadow_reopen segs HTOP AInv CST XGL ALA HCST HXGL LFSH NPH Kc rho0 (P0_hf CST FB FF) FB FF BX PTrue HKc HBX HNP
           tv fr_hf bd ANone 0%nat 160%positive 3 170%positive hG k1 k2 A X' rho tp w eq_refl ltac:(lia) Hbase Hk1
           ltac:(change (fs_frame_size 3) with 512; lia) Hfe (xrs_inclb_sound _ _ HXi) Hwf); [|exact Hw].
  intros Ai rho1 tp1 md1 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR. split.
  - exact (siteF Ai rho _ tv fr_hf _ rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HN HD HZ HFR HRO).
  - intros r y Hr Hy. left. exact (proj1 (siteX Ai rho _ tv fr_hf (Some 0%nat) _ _ rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HBf HFF HN HD HZ HFR HXL) r y Hr Hy).
Qed.

Lemma carve_imp : ltac2:(tb__ "0|1|
S3aS2aS5A1M0S5S0S0S2aS2cS2S2A2A1S2aS46A1S3S2aS77Q40A1A1Sb4S24G0ScS3bRaA1A1S33S5R9S2fS5R8S30S5A1A3A3A3S24S5R9SdeS97R8R7S1fR9A1S1cR9A1A5A3S50Z0R9A2S25S50RaR9A2S50R9Z40A2A2S24S2dS197VXGL;ReRdR9A4S2eA3S73S58VJAv;S5cRaS7dR9S5bA4A1RfR8R7R6A6S73S58VJAv;S5cRbS7dRaS5bA4A1Se3R10PaaA2R9R8R7A6F_;F_;F_;F_;F_;F_;Fw;Ftp;Frho;Fbd;Ftv;Fk2;Fk1;Fsh;Fobjs;FA;").
Proof.
  intros A objs sh k1 k2 tv bd rho tp w Ho Hsh Hk1 Hk2 CK Hw.
  unfold carve_chk in CK. peel CK HXL. peel CK HRO. peel CK HFRF. peel CK HB. peel CK Hwf. rename CK into Hbase. apply sv_eqb_sound in Hbase.
  apply (JA_flag_carve segs HTOP AInv CST XGL ALA HCST HXGL LFLAG NPH Kc rho0 (P0_hf CST FB FF) FB FF BX PTrue HKc HBX HNP
           tv fr_hf bd ANone 0%nat 160%positive 3 170%positive A rho tp w eq_refl ltac:(lia) Hbase Hwf); [|exact Hw].
  intros Ai rho1 tp1 md1 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR. split.
  - intros o a Hoi Hr. rewrite Ho in Hoi. apply in_app_or in Hoi as [Hoi|[<-|[]]].
    + exact (siteH Ai rho _ tv fr_hf _ rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HN HD HZ HFR HRO o a Hoi Hr).
    + right. right. rewrite Hsh in Hr. exact (shobj_range_hse hG 160 512 k1 k2 rho _ a sz_rng Hk1 ltac:(change (512 / 8) with 64; lia) HF HFRF Hr).
  - exact (proj2 (proj2 (siteX Ai rho _ tv fr_hf (Some 0%nat) _ _ rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HBf HFF HN HD HZ HFR HXL))).
Qed.

Lemma k_nz_L : ltac2:(tb__ "0|1|
S3S2aS4A1S2S79S4S6R3A1R2A3S24S2dS198R2R3A2S2eA3S25S50S45R5R3A2M0Sc9A2S28S24S0G0Z0A3A1A2F_;F_;Fk;FF;Frho;").
Proof.
  intros rho F k HF C. unfold liveLF in C. rdF HF C F3. rdF HF C F2. pose proof (holds_mem _ _ _ HF C) as F1.
  cbn [holds eval branch_taken] in F2. unfold bv_ltu in F2. rewrite lit_unsigned in F2 by lia. apply Z.ltb_lt in F2. change (bv_unsigned (eval rho pA)) with (uval rho pA) in F2.
  apply (k_nz_w rho pA k F1 F3). lia.
Qed.

Lemma release_imp : ltac2:(tb__ "0|3|
S3aS2aS5A1M0S0S0S2aS10A1S14S2aS2cS0S0A2A1S2aS2cS2S2A2A1S2aS46A1S3S2aS77Q40A1A1S2aSc1A1M1Se5Sc0S24S2dS126ReRdRcRbRaR9R8R7R6A9S2eA3S24G0ScS3bRfA1A1S33S5ReS2fS5SdeS97RdRcRbRaA5S30S5A1M2A3A3A3S73S58VJAv;S5cR9S7dR8S5bA4A1R10R7R6S2bG1Sd5R5Sd6R4R3A2A4A6S73S58VJAv;S5cRaS7dR9S5bA4A1SdfR11R10Pa0RbA4SdaR8S2fS5SdeS97RfReRdRcA5G2A3Sf8R4R7R5A3A3R7S2bG1Sd5R6Sd6R5R4A2A4A6F_;F_;F_;Fmd;Fms;Ftr;Ftp;Frho;Fbd;Ftv;FL;Fd;Fcells;Fk2;Fk1;Fobjs;FA;").
Proof.
  intros A objs k1 k2 cells d L tv bd rho tp tr ms md CK Ho Hw.
  unfold release_chk in CK. peel CK HRO. peel CK HB. peel CK Hnb. peel CK HL. peel CK Hfe. peel CK Hdw. peel CK Hk3. peel CK Hk2. peel CK Hk1. rename CK into Hbase.
  apply sv_eqb_sound in Hbase. apply Z.leb_le in Hk1. apply Z.leb_le in Hk2. apply Z.leb_le in Hk3.
  apply (JA_shadow_release segs HTOP AInv CST XGL ALA HCST HXGL LFSH NPH Kc rho0 (P0_hf CST FB FF) FB FF BX PTrue HKc HBX HNP
           tv fr_hf bd ANone 0%nat 160%positive 3 170%positive hG k1 k2 cells d A objs L rho tp tr ms md
           eq_refl ltac:(lia) Hbase Ho Hk1 ltac:(change (fs_frame_size 3) with 512; lia) Hdw Hfe HL Hnb); [|exact Hw].
  intros Ai rho1 tp1 md1 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR.
  exact (siteF Ai rho _ tv fr_hf objs rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HN HD HZ HFR HRO).
Qed.

Lemma release0_imp : ltac2:(tb__ "0|3|
S3aS2aS5A1M0S0S0S2aS10A1S14S2aS2cS2S2A2A1S2aS46A1S3S2aS77Q40A1A1S2aSc1A1M1Se5Sc0S24S2dS19aRdRbRaR8A4S2eA3S24G0ScS3bReA1A1S33S5RdS2fS5SdeS97RcRbRaR9A5S30S5A1M2A3A3A3S73S58VJAv;S5cR9S7dR8S5bA4A1RfR7R6S2bG1Sd5R5Sd6R4R3A2A4A6S73S58VJAv;S5cRaS7dR9S5bA4A1SdfR10RfPa0S30S2cS0S0A2A1A4SdaR8S2fS5SdeS97ReRdRcRbA5G2A3Sf8R4R7R5A3A3R7S2bG1Sd5R6Sd6R5R4A2A4A6F_;F_;F_;Fmd;Fms;Ftr;Ftp;Frho;Fbd;Ftv;Fd;Fcells;Fk2;Fk1;Fobjs;FA;").
Proof.
  intros A objs k1 k2 cells d tv bd rho tp tr ms md CK Ho Hw.
  unfold release0_chk in CK. peel CK Hfe. peel CK Hdw. peel CK Hk3. peel CK Hk2. rename CK into Hk1.
  apply Z.leb_le in Hk1. apply Z.leb_le in Hk2. apply Z.leb_le in Hk3.
  exact (JA_shadow_release0 segs HTOP AInv CST XGL ALA HCST HXGL LFSH NPH Kc rho0 (P0_hf CST FB FF) FB FF BX PTrue HKc HBX HNP
           tv fr_hf bd ANone 0%nat 160%positive 3 170%positive hG k1 k2 cells d A objs rho tp tr ms md
           eq_refl ltac:(lia) Ho Hk1 ltac:(change (fs_frame_size 3) with 512; lia) Hdw Hfe Hw).
Qed.

Lemma is_shx_out : ltac2:(tb__ "0|2|
S3S2aS4A1S5S0S0S0S79S4S6R6A1R5A3S24S2dS125R6A1S2eA3S24S2dS19bR5R4R6A3S2eA3S50Z0R6A2S50R7R6A2S50R7Z40A2S25S50S37S0S0S1dRcRaA2M0A3R7A2S55R7S38S0S0G0A3A2A2S28S25S50S51S17cS45RdS98A2A1M1RaA2R8A2S55R8S51G1R9A2A2A2A1F_;F_;F_;F_;F_;F_;F_;Fa;Fk2;Fk1;Fo;FF;Frho;").
Proof.
  intros rho F o k1 k2 a HF HFR HS Hk1 Hk2 Hk3 Hr Ha. pose proof (framez_of hG 160 512 rho F sz_rng HF HFR) as [G1 G2 G3].
  unfold is_shx in HS. destruct o as [b lo hi cs d]. cbn [ob_base ob_lo ob_hi] in HS.
  destruct b as [ | g | | | | | | ]; try discriminate. destruct lo as [lo| | | | | | | ]; try discriminate. destruct hi as [hi| | | | | | | ]; try discriminate.
  peel HS Hd. peel HS H4. peel HS H3. peel HS H2. apply Pos.eqb_eq in HS. subst g.
  apply Z.leb_le in H2. apply Z.leb_le in H3. apply Z.leb_le in H4.
  unfold obj_range, obj_lo_of, obj_hi_of in Hr. cbn [ob_base ob_lo ob_hi fst snd] in Hr.
  unfold SHADOW_OFF in *. rewrite !soff_lit_small in Hr by lia.
  change (bv_unsigned (eval rho (SVar hG))) with (uval rho (SVar hG)) in Hr. rewrite G1 in Hr. unfold hF, Sh, SHADOW_OFF in Ha.
  apply orb_prop in Hd as [Hd|Hd]; apply Z.leb_le in Hd; lia.
Qed.
Lemma reopenS_imp : ltac2:(tb__ "0|1|
S3aS2aS2cS2S2A2A1M0G0S2aS46A1S0S0S3S2aS77Q40A1A1Sb4S24S2dS19cVXGL;R9R8R7R5R4A6S2eA3S73S58VJAv;S5cR8S7dR7S5bA4A1RaR4R3R2A6S73S58VJAv;S5cR9S7dR8S5bA4A1Se2RbRaS97R7R6A5R5R4R3A6F_;F_;Fw;Ftp;Frho;Fk2;Fk1;Fbd;Ftv;FX';FA;").
Proof.
  intros A X' tv bd k1 k2 rho tp w CK Hw.
  unfold reopenS_chk in CK. peel CK HXL. peel CK HRO. peel CK HFRF. peel CK HB. peel CK Hwf. peel CK HXi. peel CK Hfe. peel CK Hk3. peel CK Hk2. peel CK Hk1. rename CK into Hbase.
  apply sv_eqb_sound in Hbase. apply Z.leb_le in Hk1. apply Z.leb_le in Hk2. apply Z.leb_le in Hk3.
  apply (JA_shadow_reopenS segs HTOP AInv CST XGL ALA HCST HXGL LFSH NPH Kc rho0 (P0_hf CST FB FF) FB FF BX PTrue HKc HBX HNP
           tv fr_hf bd ANone 0%nat 160%positive 3 170%positive hG k1 k2 A X' rho tp w eq_refl ltac:(lia) Hbase Hk1
           ltac:(change (fs_frame_size 3) with 512; lia) Hfe (xrs_inclb_sound _ _ HXi) Hwf); [|exact Hw].
  intros Ai rho1 tp1 md1 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR. split.
  - intros o a Hoi Hr. destruct (is_shx k1 k2 o) eqn:ES.
    + right. exact (is_shx_out rho _ o k1 k2 a HF HFRF ES Hk1 Hk2 Hk3 Hr).
    + left. refine (siteF Ai rho _ tv fr_hf _ rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HN HD HZ HFR HRO o a _ Hr).
      apply filter_In. split; [exact Hoi | rewrite ES; reflexivity].
  - intros r y Hr Hy. destruct (xloc_ok k1 k2 r) eqn:EL.
    + right. unfold xloc_ok in EL. destruct r as [ra rl]. destruct ra as [ | | op ra1 ra2 | | | | | ]; try discriminate. destruct op; try discriminate.
      destruct ra1 as [ | p0 | | | | | | ]; try discriminate. destruct ra2 as [off| | | | | | | ]; try discriminate. destruct rl as [len| | | | | | | ]; try discriminate.
      peel EL Hwc. peel EL H3. peel EL H2. peel EL H1. apply Pos.eqb_eq in EL. subst p0. apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3.
      exists off, len. change (fs_frame_size 3) with 512. repeat split; try assumption; reflexivity.
    + left. refine (proj1 (siteX Ai rho _ tv fr_hf (Some 0%nat) _ _ rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HBf HFF HN HD HZ HFR HXL) r y _ Hy).
      apply filter_In. split; [exact Hr | rewrite EL; reflexivity].
Qed.

Lemma releaseP_imp : ltac2:(tb__ "0|3|
S3aS2aS5A1M0S0S0S2aS10A1S14S2aS2cS0S0A2A1S2aS2cS2S2A2A1S2aS46A1S3S2aS77Q40A1A1S2aSc1A1M1Se5Sc0S24S2dS19dReRdRcRbRaR9R8R7R6A9S2eA3S24G0ScS3bRfA1A1S33S5ReS2fS5SdeS97RdRcRbRaA5S30S5A1M2A3A3A3S73S58VJAv;S5cR9S7dR8S5bA4A1R10R7R6S2bG1Sd5R5Sd6R4R3A2A4A6S73S58VJAv;S5cRaS7dR9S5bA4A1SdfR11R10Pa0RbA4SdaR8S2fS5SdeS97RfReRdRcA5G2A3Sf8R4R7R5A3A3R7S2bG1Sd5R6Sd6R5R4A2A4A6F_;F_;F_;Fmd;Fms;Ftr;Ftp;Frho;Fbd;Ftv;FL;Fd;Fcells;Fk2;Fk1;Fobjs;FA;").
Proof.
  intros A objs k1 k2 cells d L tv bd rho tp tr ms md CK Ho Hw.
  unfold releaseP_chk in CK. peel CK HRO. peel CK HB. peel CK Hnb. peel CK HL. peel CK Hfe. peel CK Hdw. peel CK Hk3. peel CK Hk2. peel CK Hk1. rename CK into Hbase.
  apply sv_eqb_sound in Hbase. apply Z.leb_le in Hk1. apply Z.leb_le in Hk2. apply Z.leb_le in Hk3.
  apply (JA_shadow_releaseP segs HTOP AInv CST XGL ALA HCST HXGL LFSH NPH Kc rho0 (P0_hf CST FB FF) FB FF BX PTrue HKc HBX HNP
           tv fr_hf bd ANone 0%nat 160%positive 3 170%positive hG k1 k2 cells d A objs L rho tp tr ms md
           eq_refl ltac:(lia) Hbase Ho Hk1 ltac:(change (fs_frame_size 3) with 512; lia) Hdw Hfe HL Hnb); [|exact Hw].
  intros Ai rho1 tp1 md1 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR.
  exact (siteF Ai rho _ tv fr_hf objs rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HN HD HZ HFR HRO).
Qed.
Lemma reopenC_imp : ltac2:(tb__ "0|1|
S3aS2aS2cS2S2A2A1M0G0S2aS46A1S0S0S0S0S3S2aS77Q40A1A1Sb4S24S2dS19eVXGL;RbRaR9R7R6R5R4A8S2eA3S73S58VJAv;S5cRaS7dR9S5bA4A1RcR4R3R2A6S26S0S0S25S27S24S0R1Z0A3S24S0R1S53S51R8R7A2Z8A2A3A2S73S58VJAv;S5cRcS7dRbS5bA4A1S1beReRdS97RaR9S1bdR8R7R1A3A6R6R5R4A6A2LbL;A2F_;F_;Fw;Ftp;Frho;Flen;Foff;Fk2;Fk1;Fbd;Ftv;FX';FA;").
Proof.
  intros A X' tv bd k1 k2 off len rho tp w CK Hw.
  unfold reopenC_chk in CK. peel CK HXL. peel CK HRO. peel CK HFRF. peel CK HB. peel CK Hwfm. peel CK Hwf0. peel CK Hq2. peel CK Hq1. peel CK Hols. peel CK Hm1.
  peel CK Hl1. peel CK Ho8. peel CK Ho0. peel CK HiL. peel CK HXi. peel CK Hfe. peel CK Hk3. peel CK Hk2. peel CK Hk1. rename CK into Hbase.
  apply sv_eqb_sound in Hbase. apply Z.leb_le in Hk1. apply Z.leb_le in Hk2. apply Z.leb_le in Hk3. apply Z.leb_le in Ho0. apply Z.eqb_eq in Ho8.
  apply Z.leb_le in Hl1. apply Z.leb_le in Hm1. apply Z.leb_le in Hols. apply Z.leb_le in Hq1. apply Z.ltb_lt in Hq2.
  apply (JA_shadow_reopen_cells segs HTOP AInv CST XGL ALA HCST HXGL LFSH NPH Kc rho0 (P0_hf CST FB FF) FB FF BX PTrue HKc HBX HNP
           tv fr_hf bd ANone 0%nat 160%positive 3 170%positive hG k1 k2 off len A X' rho tp w eq_refl ltac:(lia) Hbase Hk1
           ltac:(change (fs_frame_size 3) with 512; lia) Hfe (xrs_inclb_sound _ _ HXi) (xrs_inclb_sound _ _ HiL _ (or_introl eq_refl)) Ho0 Ho8 Hl1 Hm1
           ltac:(change (fs_frame_size 3) with 512; exact Hols) Hq1 Hq2); [| |exact Hw].
  - intros bL [->| ->]; assumption.
  - intros Ai rho1 tp1 md1 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR. split.
    + intros o a Hoi Hr. destruct (is_shx k1 k2 o) eqn:ES.
      * right. exact (is_shx_out rho _ o k1 k2 a HF HFRF ES Hk1 Hk2 Hk3 Hr).
      * left. refine (siteF Ai rho _ tv fr_hf _ rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HN HD HZ HFR HRO o a _ Hr).
        apply filter_In. split; [exact Hoi | rewrite ES; reflexivity].
    + intros r y Hr Hy. destruct (xloc_ok k1 k2 r) eqn:EL.
      * right. unfold xloc_ok in EL. destruct r as [ra rl]. destruct ra as [ | | op ra1 ra2 | | | | | ]; try discriminate. destruct op; try discriminate.
        destruct ra1 as [ | p0 | | | | | | ]; try discriminate. destruct ra2 as [off'| | | | | | | ]; try discriminate. destruct rl as [len'| | | | | | | ]; try discriminate.
        peel EL Hwc. peel EL H3. peel EL H2. peel EL H1. apply Pos.eqb_eq in EL. subst p0. apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3.
        exists off', len'. change (fs_frame_size 3) with 512. repeat split; try assumption; reflexivity.
      * left. refine (proj1 (siteX Ai rho _ tv fr_hf (Some 0%nat) _ _ rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HBf HFF HN HD HZ HFR HXL) r y _ Hy).
        apply filter_In. split; [exact Hr | rewrite EL; reflexivity].
Qed.

Lemma facts_sub_holds : ltac2:(tb__ "0|1|
S3S2aS4A1M0G0S24S2dS15bR2R1A2S2eA3S79S4S6R4A1R2A3S79S4S6R5A1R4A3F_;F_;FG;FF;Frho;").
Proof.
  intros rho F G H HG. apply Forall_forall. intros p Hp. exact (holds_mem rho G p HG (proj1 (forallb_forall _ _) H p Hp)).
Qed.

Lemma TR_absorb : ltac2:(tb__ "0|3|
Sb5S3aS59S3S2aS77Q40A1M0A1Sb5S2aSc1A1M1Se5Sc0R9S2bG1Sd5R3Sd6R2R1A2A4A1S26S3S3S25S2S24G0S11R2R1A2M2S11R9R1A2A3Fe;S73S58VJAv;R9A1RaR1R7S2bG1Sd5R5Sd6R4R3A2A4A6A2Lrho';A2F_;Fmd;Fms;Ftr;S3S2S24G0G2S11R6R1A2A3Fe;VTR;S73S58VJAv;R7A1R8R2R5A5R4A2F_;Frho';VTR;R8R3A2F_;F_;FQ';Ftp;Frho;Fnd;FS;FP;").
Proof.
  intros P S nd rho tp Q' HP HS.
  apply (TR_pre (fun w => exists rho', (fun w' => (forall e, eval rho' e = eval rho e) /\ SPA segs (JAv nd) S rho' tp w') w)).
  { intros [tr [ms md]] Hw. destruct (HP tr ms md Hw) as (rho' & HE & Hw'). exists rho'. split; [exact HE | exact Hw']. }
  apply TR_exw. intros rho'. apply (TR_pureP _ (forall e, eval rho' e = eval rho e)); [intros w [HE _]; exact HE|]. intros HE.
  eapply TR_pre; [intros w [_ Hw]; exact Hw|]. exact (HS rho' HE).
Qed.

Lemma land_imp : ltac2:(tb__ "0|2|
S3aS3aSd8S2aS2cS2S2A2A1M0G0S2aS46A1M1G1G0G1S3S2aS77Q40A1A1Sb4S24S2dS132RcRbRaR9R8R7R6R5A8S2eA3S24G1S47RbR5A2R7A3S73S58VJAv;S5cRbS7dR9S5bA4A1ReR5R4R3A6S73S58VJAv;S5cR8S7dR7S5bA4A1ReSd9R6RdA2R5R4A6F_;F_;F_;Fw;Ftp;Frho;FbdC;FtvC;Fbd2;Fbd1;Ftv2;Ftv1;Fs;FC;FL;").
Proof.
  intros L C s tv1 tv2 bd1 bd2 tvC bdC rho tp w CK Hbd Hw.
  unfold land_chk in CK. peel CK Hfr. peel CK Htv. peel CK Hnb. peel CK Hnp. peel CK Hid. peel CK He. peel CK Hbp. rename CK into Htp.
  apply (SPA_entails_JA_eq L C s (NDA tv2 fr_hf bd2 ANone) (NDA tvC fr_hf bdC ANone) rho tp w He Hid Hnp Hnb Htv Hfr Hbd eq_refl).
  apply (SPA_bd_permb segs AInv CST XGL NPH Kc rho0 (P0_hf CST FB FF) FB FF BX PTrue tv2 fr_hf bd1 bd2 ANone L rho tp w Hbp).
  exact (SPA_tv_permb segs AInv CST XGL NPH Kc rho0 (P0_hf CST FB FF) FB FF BX PTrue tv1 tv2 fr_hf bd1 ANone L rho tp w Htp Hw).
Qed.

Lemma tvx_app_l : ltac2:(tb__ "0|2|
Sc2S3S2aS2cS2S2A2M0A1M1G1S60VFB;R4R3S33G0R2R1A3A4S10aR4S33G0R3R2A3A2S109R5S33G0R4R3A3A2S25S60VFB;R7R6R5A4S25S10aR6R5A2S109R6R5A2A2A2F_;F_;F_;Fl2;Fl1;Frho;FAi;").
Proof.
  intros Ai rho l1 l2 HN HD HZ. unfold tvinA, tvz in *. apply Forall_app in HN as [HN _]. apply Forall_app in HZ as [HZ _].
  split; [exact HN|]. split; [exact (tvd_app_l rho l1 l2 HD) | exact HZ].
Qed.

Lemma X_pureT : ltac2:(tb__ "0|1|
S3aS3aS3aS3aS59Sd8S2aS5A1M0S3S2aS77Q40A1A1Sb5S1bcRaS2fS3dS44R9S1bfA2S30S3dA1A3A2S24S34G0A1SbaR9RbR6A3S35G0R5A2A3S24S2dS138RcRbRaR8R7R6A6S2eA3S24S3aS164S9S3bRbA1A1SbdR8RdRcRbR7A5A2RaA3S3S1bSaS3bRdA1A1R8R1A3VTR;S73S58VJAv;RcA1RdR2R8A5R7A2F_;Frho';VTR;S73S58VJAv;RbA1RdR8R7A5R6A2F_;F_;F_;F_;F_;FQ';Ftp;Frho;FR;Fs;Fnd;FT0;FE;FP;FPre;").
Proof.
  intros Pre P E T0 nd s R rho tp Q' CALL He CK HT0 HK.
  unfold pure_chk in CK. peel CK Hfb. peel CK Hnb. peel CK Hnf. rename CK into Hchk.
  apply (CALL E s R rho tp nd _ He Hchk Hnf Hnb Hfb).
  intros L rho' HL Hag. cbn [In] in HL. destruct HL as [<-|[]]. cbn [la_state]. rewrite HT0. exact (HK rho' Hag).
Qed.

Lemma X_purecT : ltac2:(tb__ "0|3|
Sc2S3OF_;F_;S3aS2aS3aA1S3aS2aS2cS2S2A2A1S2aS46A1Sd8S2aS5A1M0S3S2aS77Q40A1A1M1Sb5Sc2S3G1VTR;S73S58S3G1S2aSc1A1M2Sc0S25S14eVAInv;R7VKc;R4R3R2R1A7R12R7R4A2A2Lm;Lt;Lp;Lr;RdR2R1A5Sb9S58Sd4R2R1S7aS3aS2cS3aSb8A2S3aS2bS3aSb8R1S14cVAInv;VCST;VXGL;R4VKc;A5A4LL;RcA4A5A2Ftp1;Frho1;FAi;Sc2G2Se5Sc0S75S58R8R7RdS2bG2Sd5R3Sd6R2R1A2A4A5VAInv;R5R9R8R2A4S175VCST;VXGL;R6S36S0A1RaS3cRfA1A6R13R7Sd9SdaRbRcSf8R4RaR5A3A3RdA2A2F_;F_;F_;Fmd;Fms;Ftr;FAi;S24S1SaS3bRcA1A1Sd4A3S24S2S3fRdA1S7S17bA1A3S24S34G0A1SbaRcReR9A3S35G0R8A2A3S24S2dS128VXGL;RfReRdRcRbRaR9A8S2eA3S3aS3G1Sc5S3aR3R12A3SccSaS3bR12A1A1RdR3A3S79S4S6ReA1S9S3bR13A1A1A3VTR;S73S58VJAv;S5cR13S7dR12S5bA4A1S173R16R14R11R10R6A5R5R4A5RdA2F_;F_;F_;Ftp';Frho';FL;VTR;S73S58VJAv;S5cReS7dRdS5bA4A1RfRaR9A5R8A2F_;F_;F_;F_;F_;F_;F_;FQ';Ftp;Frho;FR;Fs;Fbd;Ftv;FE;FLs;FPre;FXP;").
Proof.
  intros XP Pre Ls E tv bd s R rho tp Q' CALLEE HXP HNF HbP He CK HK.
  unfold purec_chk in CK. peel CK HX. peel CK HR. peel CK HB. peel CK Hshape. peel CK Hwp. peel CK Hnb. peel CK Hnf. peel CK Htp. rename CK into Hchk.
  apply TR_facts. intros HF.
  apply (purec_callT_ag_xp segs AInv CST XGL ALA HCST HXGL NPH Kc rho0 (P0_hf CST FB FF) FB FF BX PTrue HKc TR TR_facts TR_ex TR_pre TR_callP
           XP Pre Ls E s R rho tp (NDA tv fr_hf bd ANone) bd Q' CALLEE HNF HbP He Hchk Htp Hnf Hnb).
  - destruct (nd_below_split _ _ Hnb) as (_ & _ & Hbb & _). exact Hbb.
  - cbn [nd_bd]. apply payA_same. exact Hwp.
  - exact Hshape.
  - exact (site_pure E s R rho tv fr_hf bd HB HR HX).
  - exact HXP.
  - intros L rho' tp' HL Hag. cbn [nd_tv nd_fr nd_am]. exact (HK L rho' tp' HL Hag HF).
Qed.

Lemma X_purecT0 : ltac2:(tb__ "0|2|
S3aS2aS3aA1S3aS2aS2cS2S2A2A1S2aS46A1Sd8S2aS5A1M0S3S2aS77Q40A1A1M1Sb5Sc2S3G1VTR;S73S58S14eVAInv;R3VKc;A3RdR2R1A5Sb9S58Sd4R2R1S7aS3aS2cS3aSb8A2S3aS2bS3aSb8R1S14cVAInv;VCST;VXGL;R4VKc;A5A4LL;RcA4A5A2Ftp1;Frho1;FAi;S24S1SaS3bRbA1A1Sd4A3S24S2S3fRcA1S7S17bA1A3S24S34G0A1SbaRbRdR8A3S35G0R7A2A3S24S2dS128VXGL;ReRdRcRbRaR9R8A8S2eA3S3aS3G1Sc5S3aR3R11A3SccSaS3bR11A1A1RcR3A3S79S4S6RdA1S9S3bR12A1A1A3VTR;S73S58VJAv;S5cR12S7dR11S5bA4A1S173R15R13R10RfR6A5R5R4A5RcA2F_;F_;F_;Ftp';Frho';FL;VTR;S73S58VJAv;S5cRdS7dRcS5bA4A1ReR9R8A5R7A2F_;F_;F_;F_;F_;F_;FQ';Ftp;Frho;FR;Fs;Fbd;Ftv;FE;FLs;FPre;").
Proof.
  intros Pre Ls E tv bd s R rho tp Q' CALLEE HNF HbP He CK HK.
  unfold purec_chk in CK. peel CK HX. peel CK HR. peel CK HB. peel CK Hshape. peel CK Hwp. peel CK Hnb. peel CK Hnf. peel CK Htp. rename CK into Hchk.
  apply TR_facts. intros HF.
  apply (purec_callT_ag segs AInv CST XGL ALA HCST HXGL NPH Kc rho0 (P0_hf CST FB FF) FB FF BX PTrue HKc TR TR_facts TR_ex TR_pre TR_callP
           Pre Ls E s R rho tp (NDA tv fr_hf bd ANone) bd Q' CALLEE HNF HbP He Hchk Htp Hnf Hnb).
  - destruct (nd_below_split _ _ Hnb) as (_ & _ & Hbb & _). exact Hbb.
  - cbn [nd_bd]. apply payA_same. exact Hwp.
  - exact Hshape.
  - exact (site_pure E s R rho tv fr_hf bd HB HR HX).
  - intros L rho' tp' HL Hag. cbn [nd_tv nd_fr nd_am]. exact (HK L rho' tp' HL Hag HF).
Qed.

Lemma X_VR : ltac2:(tb__ "0|8|
S3aS2aS2cS2S2A2M0A1M1S2S2S0S0S2aS46A1M2G2Sd8S2aS5A1M3G1S3S2aS77Q40A1A1M4Sb5S3aS3aS3aS2S2G2G2S24S2dS13eVXGL;R15R14R13R12R11R10RfReRdRcRbAcS2eA3S24S34G3A1SbaR16Se6ReA3S35G3RdA2A3S24S3aS169Se6R17RfReSe8RdA6R9A3S24G1S10dSbbR10Se6Se8R18A4SebA2S2fG0S2bS2S2R16S96R14R15A2A4S30G0A1M5A3A3S24G2S47SbbR11Se6Se8R19A4S5fSeaA1A2R6A3S24S3aS169Se6R1aR12R11Se9R10A6RbA3S24G1S10dSbbR13Se6Se9R1bA4SebA2S2fG0S2bS2S2R19S96R17R18A2A4G5A3A3S24S3aS169Se6R1cR14R13Se7R12A6RcA3S24G1S10dSbbR15Se6Se7R1dA4SedA2S2fG0S2bS2S2RcS96R19RbA2A4G5A3A3S24G2S47SbbR16Se6Se7R1eA4SecSefSeeA2A2RaA3S3G4SccSaS3bR21A1A1R16R2A3S79S4S6R17A1S9S3bR22A1M6A1A3VTR;S73S58VJAv;S5cS33G0R22S2fG0S2bS2S2R21S96R1fR20A2A4G5A3A3S7dS33S46R10R1cA3S5bA4A1R15R4R3A5R16A2F_;F_;Ftp';Frho';S3G4SccSaG6A1R17R2A3S79S4S6R18A1S9S3bR23A1M7A1A3VTR;S73S58VJAv;S5cS33G0R23S2fG0S2bS2S2R22S96R20R21A2A4G5A3A3S7dR1dS5bA4A1R15R4R3A5R17A2F_;F_;Ftp';Frho';S3G4SccSaG7A1R18R2A3S79S4S6R19A1S9S3bR24A1A1A3VTR;S73S58VJAv;S5cS33G0R24S2fG0S2bS2S2R14S96R21R13A2A4G5A3A3S7dS33S46R11R1eA3S5bA4A1R15R4R3A5R18A2F_;F_;Ftp';Frho';VTR;S73S58VJAv;S5cS33G0R21S2fG0S2bS2S2R20S96R1eR1fA2A4G5A3A3S7dR1cS5bA4A1R22R17R16A5R15A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FbdG;FbdK;FkG;FdG;FTG;FTF;FTK;FQ';Ftp;Frho;FXk;FR;Fs;Fbrest;Fbd;Foff;Fe;Fk;Fd;Fkept;FE;").
Proof.
  intros E kept d k e off bd brest s R Xk rho tp Q' TK TF TG dG kG bdK bdG C He HTK HiK HbK HTF HiF HTG HiG HbG KK KF KG.
  unfold vr_chk in C. peel C Hoff2. peel C Hoff1. peel C Hs12. peel C Hs14. peel C Hs15. peel C Hs17. peel C HkB. peel C He2. peel C He1.
  peel C HX. peel C HR. peel C HB. peel C Hpd. peel C Hwp. peel C Hperm. peel C Htvs. peel C Hbb. peel C Hnb. peel C Hnp. peel C Hdom. peel C Hta. peel C Hchk. rename C into HXk.
  apply sv_eqb_sound in Hs12. apply sv_eqb_sound in Hs14. apply sv_eqb_sound in Hs15. apply sv_eqb_sound in Hs17.
  apply Z.leb_le in Hoff1. apply Z.leb_le in Hoff2. apply Z.ltb_lt in He1. apply Z.leb_le in He2.
  eapply TR_pre; [intros w Hw; exact (SPA_bd_permb segs AInv CST XGL NPH Kc rho0 (P0_hf CST FB FF) FB FF BX PTrue _ fr_hf bd _ ANone E rho tp w Hperm Hw)|].
  apply TR_facts. intros HF.
  apply (client_callT segs AInv CST XGL ALA HCST HXGL NPH Kc rho0 (P0_hf CST FB FF) FB FF BX PTrue HKc HBX VNP.P0_vr PTrue (fun _ H => H) (fun _ _ _ H => H)
           VN.Pre_vr VN.nd0 PD_vn NF eq_refl eq_refl eq_refl TR TR_facts TR_ex TR_pre TR_callP CVRESN eq_refl
           E s R Xk rho tp kept [(d, kb e k)] fr_hf (bd_subst s (nd_bd VN.nd0) ++ brest) brest ANone Q' HXk He Hchk Hta Hdom Hnp Hnb Hbb Htvs eq_refl).
  - apply payA_same. exact Hwp.
  - exact Hpd.
  - intros Ai ms HF' HP0 Hav HBf HFF HN HD HZ HFR (rho1 & tp1 & md1 & HM) HT HTK'.
    destruct (tvx_app_l Ai rho kept _ HN HD HZ) as (HN1 & HD1 & HZ1).
    destruct (P0_now rho Hav HP0) as (_ & Hb & Hal & _).
    pose proof (basez_of DW rho _ DW_rng HF HB) as BZ. pose proof BZ as [Bsp Bb Bal BL BB Btop].
    split; [|split].
    + intros o a Ho Hr. eapply (robjs_checkP_sound segs AInv CST ALA rho0 FB FF Ai rho _ kept fr_hf None extraOH R rho1 tp1 md1 HM HF (T_ok_T0 rho0 _ Ai HT HTK') HN1 HD1 HZ1 HFR HR);
        [intros o' a' Ho' HE Hr'; exact (extra_client rho o' a' _ _ BZ Hav HP0 HE Hr') | exact Ho | exact Hr].
    + exact (proj1 (siteX Ai rho _ kept fr_hf None (ss_objs (ax_S E)) Xk rho1 tp1 md1 HM HF HB Hav HP0 HT HTK' HBf HFF HN1 HD1 HZ1 HFR HX)).
    + unfold VNP.P0_vr. rewrite !rw_call', Hs17, Hs15, Hs14, Hs12.
      change (bv_unsigned (eval rho k)) with (uval rho k). change (bv_unsigned (eval rho d)) with (uval rho d).
      change (bv_unsigned (eval rho vAL)) with (uval rho vAL). change (bv_unsigned (eval rho (xbo off))) with (uval rho (xbo off)).
      split; [|split].
      * pose proof (holds_mem _ _ (SPUle k (SLit B32)) HF HkB) as FK. rewrite h_ule in FK. unfold B32 in FK. rewrite uval_lit in FK by lia.
        intros HK. apply (tvz_in rho _ d e k HZ); [apply in_or_app; right; left; reflexivity | lia | unfold B32; lia | exact HK].
      * destruct Hb as (f & sz & fl & Hin & H1 & H2). exists f, sz, fl. split; [apply In_FFx; left; exact Hin|].
        assert (EO : uval rho (xbo off) = uval rho vb + off) by (unfold xbo; apply uval_add_litZ; unfold IMG_HI in *; lia).
        rewrite EO. unfold uval in H1, H2 |- *. lia.
      * destruct Hal as (f & sz & fl & Hin & H1 & H2). exists f, sz, fl. split; [apply In_FFx; left; exact Hin|]. unfold uval in H1, H2 |- *. lia.
  - intros [Ld ndL] rho' tp' Hd Hag. cbn [PD_vn In] in Hd. destruct Hd as [Hd|[Hd|[Hd|[]]]]; injection Hd as <- <-;
      cbn [fst snd nd_tv nd_bd nd_am VN.nd0 ND am_subst app].
    + rewrite HTK, HiK. change (nd_bd VN.nd0) with (VN.bdP VN.vN VN.vK) in HbK. cbn [nd_bd VN.nd0 ND] . rewrite HbK. exact (KK rho' tp' Hag HF).
    + rewrite HTF, HiF. cbn [bd_subst map app]. exact (KF rho' tp' Hag HF).
    + rewrite HTG, HiG, HbG. exact (KG rho' tp' Hag HF).
Qed.

Lemma XH_E_sm : ltac2:(tb__ "0|1|
S3S2aS77Q40A1A1M0S0G0S50S54Z62S52Z2Z40A2A2R2A2VTR;S73S58VJAv;S84A1S8bR5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  pose proof (sm_chk XGL) as C. peel C Hs12. peel C HX. peel C HR. peel C HB. peel C HpF. peel C HvF. peel C HpR. peel C HvR. peel C Hwp. peel C Hnb. peel C Hnp. peel C Hta. rename C into Hchk.
  apply sv_eqb_sound in HvF. apply sv_eqb_sound in HvR. apply sv_eqb_sound in Hs12.
  apply (smalloc_callT segs AE_A AInv CST XGL ALA HCST HXGL NPH Kc rho0 (P0_hf CST FB FF) FB FF BX PTrue HKc TR TR_facts TR_ex TR_pre TR_callP
           3 E_sm0 s_sm R_sm rho tp nd0 160 170 (FAM b tp0) CSM ltac:(lia) R_sm_eq Hchk Hta Hnp Hnb Hwp HvR HpR HvF HpF (fun A A' _ => I)).
  -
    intros Ai ms HF' HP0 Hav HBf HFF HN HD HZ HFR (rho1 & tp1 & md1 & HM) HT HTK. destruct (P0_now rho Hav HP0) as (_ & _ & _ & HC0 & _).
    cbn [nd_tv nd_fr nd0 ND] in HN, HD, HZ, HFR |- *.
    split; [|split].
    + exact (siteP Ai rho _ tv0 [] None R_sm rho1 tp1 md1 HM HF' HB Hav HP0 HT HTK HBf HFF HN HD HZ HFR HR).
    + exact (proj1 (proj2 (siteX Ai rho _ tv0 [] None (ss_objs (ax_S E_sm0)) (ax_X E_sm0) rho1 tp1 md1 HM HF' HB Hav HP0 HT HTK HBf HFF HN HD HZ HFR HX))).
    + split; [rewrite Hs12; rewrite uval_lit by lia; change (fs_frame_size 3) with 512; lia|].
      unfold ffpairs. change (map (fun y : Z * Z * Z => fst y) FF) with (map fst FF). rewrite HC0. cbn. lia.
  -
    intros rho' tp'. pose proof T_sm_eq as ET. unfold Pre_sm, L_sm in ET. cbn [nd_tv nd_fr nd_bd nd_am nd0 ND]. rewrite ET. clear ET.
    eapply TR_pre with (P := SPA segs (JAv ndP) T_sm1 rho' tp').
    { intros w Hw. exact (SPA_axforms segs _ [AXSelect (sel_last T_sm 3)] rho' T_sm T_sm1 tp' w T_sm1_eq Hw). }
    pose proof (sm1_chk XGL) as C. peel C Hlt. peel C Hal. peel C HX1. peel C HB1. peel C Hnb1. peel C Hnp1. rename C into Hwf1.
    apply (TR_pre (fun w => exists rho2, SPA segs (JAv ndP) C_pro rho2 tp' w)).
    { intros w Hw.
      destruct (JA_frame_open segs HTOP AInv CST XGL ALA HCST HXGL LFLAG NPH Kc rho0 (P0_hf CST FB FF) FB FF BX PTrue HKc HBX HNP
                  tv0 fr_hf (bd_hf tI mi_n mi_k fv_n fv_k mm_n mm_k sg_n sg_k co_n co_k rp_n rp_k tr_n tr_k ts_n ts_k) ANone 0%nat 160 3 170
                  T_sm1 objs_sm1 X_hf0 [] rho' tp' w eq_refl ltac:(lia) eq_refl T_sm1_objs T_sm1_X Hwf1 Hnp1 Hnb1) as (rho2 & _ & Hw2); [| exact Hw |].
      - intros Ai rho1 tp1 md1 HF2 HP0 Hav HM HT HTK HBf HFF HN HDt HZt HFR.
        exact (proj1 (siteX Ai rho' _ tv0 fr_hf (Some 0%nat) (ss_objs (ax_S T_sm1)) (X_hf0 ++ []) rho1 tp1 md1 HM HF2 HB1 Hav HP0 HT HTK HBf HFF HN HDt HZt HFR HX1)).
      - exists rho2. rewrite app_nil_r in Hw2. change (fs_frame_size 3) with 512 in Hw2. rewrite C_pro0_eq in Hw2. rewrite <- C_pro_eq.
        exact (SPA_x_len0 segs (JAv ndP) C_pro0 160 5 rho2 tp' w Hal ltac:(lia) Hlt Hw2). }
    apply TR_exw. intros rho2. apply (REENTER C_pro ndP (96, z0)); [innth 1 | rewrite emeas_z0; lia].
Qed.

Lemma XH_X_pro : ltac2:(tb__ "0|1|
S3S2aS77Q40A1A1M0S0G0S50S54Z5eS52Z2Z40A2A2R2A2VTR;S73S58VJAv;Sb1A1S91R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  apply (TR_absorb _ C_pre ndP rho tp).
  { intros tr ms md Hw. exists (rho_absorb rho [shobj hG 0 64 cells_pro DZero] (vms md tp ms)). split; [intros e; apply eval_absorb|].
    rewrite <- C_pre_eq. exact (release_imp X_pro objs_pro 0 64 cells_pro DZero [] tv0 _ rho tp tr ms md pro_chk X_pro_objs Hw). }
  intros rho' HE. apply (REENTER C_pre ndP (92, z0)); [innth 2 | rewrite emeas_z0; lia].
Qed.

Lemma XH_E_co : ltac2:(tb__ "0|1|
S3S2aS77Q40A1A1M0G0VTR;S73S58VJAv;SabA1S85R3R2A5VFAM;S5aS2bS2cS3aS59A2S2cS0S2A2S2bS3aS59S85SabA4S2bS0S2Z50Sa6S7fZ3bA2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_facts. intros HF0. pose proof (vrF_bound rho _ pQ HF0 co_vrF) as VB.
  pose proof co_meas as CM. peel CM MbQ. peel CM MbE. peel CM Mg2. peel CM Mg1. peel CM Mk2. rename CM into Mk1.

  eapply TR_pre with (P := SPA segs (JAv (NDA (kept_co ++ [(pDco, kb 12 pKco)]) fr_hf (bd_loop pQ pKco) ANone)) E_co rho tp).
  { intros w Hw. apply (SPA_tv_permb segs AInv CST XGL NPH Kc rho0 (P0_hf CST FB FF) FB FF BX PTrue _ _ fr_hf _ ANone E_co rho tp w co_tvp).
    apply (xff_imp _ E_co0 E_co1 E_co (xf_vr 19 720) (co_need pQ) rho tp w E_co1_eq E_co_eq2 co_xff); [|exact Hw].
    intros tr md _ HF1. exact (co_need_ok rho _ HF1 co_coF). }
  apply (X_VR E_co kept_co pDco pKco 12 720 (bd_loop pQ pKco) brest_co s_co R_co (Xkeep pDco) rho tp _ T_cok0 T_cof0 T_cog0 (SVar 520) (SVar 521) bdK_co bdG_co
           (co_chk XGL) R_co_eq T_cok0_eq co_iK co_bK T_cof0_eq co_iF T_cog0_eq co_iG co_bG).
  -
    intros rho' tp' Hag HF.
    eapply TR_pre; [|apply (REENTER JR_co ndR (80, VR pQ 58) (rho_sub rho' s_cok)); [innth 7 |
      rewrite !VR_VM; exact (VM_meas_sub E_co0 JR_co ndJ ndR 80 tE pQ 58 59 rho rho' s_cok _ ltac:(lia) VB Hag MbE MbQ Mk1 Mk2 ltac:(lia) ltac:(lia) ltac:(lia))]].
    intros w Hw. unfold ndR, ndL. apply (land_imp T_coks JR_co s_cok _ tv2_cok _ bd2_cok _ _ rho' tp' w cok_land cok_bd).
    apply (xff_imp _ T_cok0 T_cok T_coks xf_back [SPUle (SLit IMG_HI) pDco] rho' tp' w T_cok_eq eq_refl cok_xff); [|exact Hw].
    intros tr md HJ HF1. destruct (k_nz_lit rho' _ pA 1 pKco HF1 ltac:(lia) cok_live) as [K1 K2].
    constructor; [|constructor]. exact (live_holds _ rho' tp' tr md pDco 12 pKco HJ ltac:(cbn; tauto) ltac:(lia) K1 K2).
  -
    intros rho' tp' Hag HF.
    eapply TR_pre; [|apply (REENTER JF_co ndFc (30, z0) (rho_sub rho' s_cof)); [innth 8 | rewrite emeas_z0; pose proof (emeas_lb E_co0 ndJ 80 (VR pQ 59) rho); lia]].
    intros w Hw. unfold ndFc. apply (land_imp T_cof JF_co s_cof _ tv2_cof _ (firstn 1 brest_co) _ _ rho' tp' w cof_land cof_bd).
    apply (drop_imp T_cof _ fr_hf brest_co 1 rho' tp' w cof_wp). exact (SPA_axforms segs _ xf_back rho' T_cof0 T_cof tp' w T_cof_eq Hw).
  -
    intros rho' tp' Hag HF.
    eapply TR_pre; [|apply (REENTER JR_co ndR (80, VR pQ 58) (rho_sub rho' s_cog)); [innth 7 |
      rewrite !VR_VM; exact (VM_meas_sub E_co0 JR_co ndJ ndR 80 tE pQ 58 59 rho rho' s_cog _ ltac:(lia) VB Hag MbE MbQ Mg1 Mg2 ltac:(lia) ltac:(lia) ltac:(lia))]].
    intros w Hw. unfold ndR, ndL. apply (land_imp T_cog JR_co s_cog _ tv2_cog _ bd2_cog _ _ rho' tp' w cog_land cog_bd).
    exact (SPA_axforms segs _ xf_back rho' T_cog0 T_cog tp' w T_cog_eq Hw).
Qed.

Lemma XH_E_ms : ltac2:(tb__ "0|1|
S3S2aS77Q40A1A1M0G0VTR;S73S58VJAv;S80A1S86R3R2A5VFAM;S5aS2bS2cS3aS59A2S2cS0S2A2S2bS3aS59S86S80A4S2bS0S2Z50Sa6S7fZ39A2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_facts. intros HF0. pose proof (vrF_bound rho _ pQ HF0 ms_vrF) as VB. pose proof ms_meas as CM. peel CM MbQ. rename CM into MbE.
  eapply TR_pre with (P := SPA segs (JAv ndR) E_ms rho tp).
  { intros w Hw. rewrite <- E_ms_eq. apply (reshape_fwd _ E_ms1 33 pD2 (kb 12 pA) (kb 12 pA) 12 DUnknown rho tp w ms_o33 eq_refl ms_wf ltac:(lia) (fun r => eq_refl) (fun HF => rs_bnd_lit rho _ _ _ HF ms_rs)).
    exact (SPA_axforms segs _ xf_ms rho E_ms0 E_ms1 tp w E_ms1_eq Hw). }
  unfold ndR, ndL.
  apply (X_purecT XP_memset Pre_ms [L_ms] E_ms (tv_body pD2 pK2) (bd_loop pQ pK2) s_ms R_ms rho tp _ (fun Ai rho1 tp1 => CMEMSET Ai rho1 tp1)
           (fun Ai tr ms md Hsm HM HX => XP_memset_site segs AInv CST XGL ALA HCST HXGL Ai E_ms memset_pc s_ms R_ms rho tp tr ms md Hsm HM HX R_ms_eq)
           eq_refl eq_refl R_ms_eq (ms_chk XGL)).
  intros L rho' tp' HL Hag HF. destruct HL as [<-|[]].
  eapply TR_pre; [|apply (REENTER T_ms ndR (80, VR pQ 56) rho'); [innth 9 |
    rewrite !VR_VM; exact (VM_meas_ag E_ms0 T_ms ndR ndR 80 tE pQ 56 57 rho rho' _ ltac:(lia) VB Hag MbE MbQ ltac:(lia) ltac:(lia) ltac:(lia))]].
  intros w Hw. unfold ndR, ndL. apply (SPA_axforms segs _ _ rho' T_ms1 T_ms tp' w T_ms_eq).
  rewrite <- T_ms1_eq. apply (reshape_bwd _ T_ms0 1 pD2 (kb 12 pA) (kb 12 pA) 12 DZero rho' tp' w tms_o1 eq_refl tms_wf ltac:(lia) (fun r => eq_refl) (fun HF => rs_bnd_lit rho' _ _ _ HF tms_rs)).
  rewrite <- T_ms0_eq. exact Hw.
Qed.

Lemma XH_E_pc : ltac2:(tb__ "0|1|
S3S2aS77Q40A1A1M0G0VTR;S73S58VJAv;S80A1S1a1R3R2A5VFAM;S5aS2bS2cS3aS59A2S2cS0S2A2S2bS3aS59S1a1S80A4S2bS0S2Z50Sa6S7fZ37A2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_facts. intros HF0. pose proof (vrF_bound rho _ pQ HF0 pc_vrF) as VB. pose proof pc_meas as CM. peel CM MbQ. rename CM into MbE.
  eapply TR_pre with (P := SPA segs (JAv ndR) E_pc rho tp).
  { intros w Hw. apply (facts_imp _ _ E_pc (pc_need pT0 pQ) rho tp w E_pc_eq3 pc_xff); [intros tr md _ HF1; exact (pc_need_ok rho _ HF1 pc_pcF)|].
    apply (publish_prefix_imp _ E_pc2 pD2 (kb 12 pK2) pD2 _ rho tp w pc_xin pc_xb); [intros HF1; split; [reflexivity | exact (xslot_len rho _ pD2 pA pK2 HF1 pc_slotF)]|].
    rewrite <- E_pc2_eq. apply (reshape_fwd _ E_pc1 34 pD2 (kb 12 pA) (kb 12 pA) 12 DUnknown rho tp w pc_o34 eq_refl pc_wf ltac:(lia) (fun r => eq_refl) (fun HF => rs_bnd_lit rho _ _ _ HF pc_rs)).
    exact (SPA_axforms segs _ xf_pc rho E_pc0 E_pc1 tp w E_pc1_eq Hw). }
  apply (X_pureT Pre_pc P_ret E_pc T_pc0 ndR s_pc R_pc rho tp _ CALL_pc R_pc_eq pc_chk T_pc0_eq).
  intros rho' Hag. pose proof (agree_below_vals _ _ _ Hag) as Hag'.
  eapply TR_pre; [|apply (REENTER T_pc ndR (80, VR pQ 54) rho'); [innth 10 |
    rewrite !VR_VM; exact (VM_meas_ag E_pc0 T_pc ndR ndR 80 tE pQ 54 55 rho rho' _ ltac:(lia) VB Hag' MbE MbQ ltac:(lia) ltac:(lia) ltac:(lia))]].
  intros w Hw. apply (subX_imp _ T_pc2 T_pc (X_body pD2 pK2) rho' tp w T_pc_eq2 pc_xsub).
  apply (SPA_axforms segs _ _ rho' T_pc1 T_pc2 tp w T_pc2_eq). rewrite <- T_pc1_eq.
  apply (reshape_bwd _ T_pc0 2 pD2 (kb 12 pA) (kb 12 pA) 12 DUnknown rho' tp w tpc_o2 eq_refl tpc_wf ltac:(lia) (fun r => eq_refl) (fun HF => rs_bnd_lit rho' _ _ _ HF tpc_rs)). exact Hw.
Qed.

Lemma XH_E_da : ltac2:(tb__ "0|1|
S3S2aS77Q40A1A1M0G0VTR;S73S58VJAv;S80A1S1a0R3R2A5VFAM;S5aS2bS2cS3aS59A2S2cS0S2A2S2bS3aS59S1a0S80A4S2bS0S2Z50Sa6S7fZ35A2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_facts. intros HF0. pose proof (vrF_bound rho _ pQ HF0 da_vrF) as VB. pose proof da_meas as CM. peel CM MbQ. rename CM into MbE.
  eapply TR_pre; [intros w Hw; exact (SPA_axforms segs _ [AXSplit 0 (SLit (-96))] rho E_da0 E_da tp w E_da_eq Hw)|].
  apply (X_pureT Pre_da P_da E_da T_da0 ndR s_da R_da rho tp _ CALL_da R_da_eq da_chk T_da0_eq).
  intros rho' Hag. pose proof (agree_below_vals _ _ _ Hag) as Hag'.
  eapply TR_pre; [|apply (REENTER T_da ndR (80, VR pQ 52) rho'); [innth 11 |
    rewrite !VR_VM; exact (VM_meas_ag E_da0 T_da ndR ndR 80 tE pQ 52 53 rho rho' _ ltac:(lia) VB Hag' MbE MbQ ltac:(lia) ltac:(lia) ltac:(lia))]].
  intros w Hw. apply (subX_imp _ T_da2 T_da (X_body pD2 pK2) rho' tp w T_da_eq2 da_xsub). exact (SPA_axforms segs _ _ rho' T_da0 T_da2 tp w T_da2_eq Hw).
Qed.
Lemma XH_E_dg : ltac2:(tb__ "0|1|
S3S2aS77Q40A1A1M0S0G0S50S54Z45S52Z2Z40A2A2R2A2VTR;S73S58VJAv;SffA1S106R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  eapply TR_pre; [intros w Hw; exact (SPA_axforms segs _ [AXSplit 0 (SLit (-96))] rho E_dg0 E_dg tp w E_dg_eq Hw)|].
  apply (X_pureT Pre_da P_da E_dg T_dg0 ndXA s_dg R_dg rho tp _ CALL_da R_dg_eq dg_chk T_dg0_eq).
  intros rho' Hag.
  eapply TR_pre; [|apply (REENTER T_dg ndXA (68, z0) rho'); [innth 13 | rewrite emeas_z0; lia]].
  intros w Hw. apply (subX_imp _ T_dg2 T_dg (X_body pDco pKco) rho' tp w T_dg_eq2 dg_xsub). exact (SPA_axforms segs _ _ rho' T_dg0 T_dg2 tp w T_dg2_eq Hw).
Qed.

Lemma XH_E_mi0 : ltac2:(tb__ "0|1|
S3S2aS77Q40A1A1M0G0VTR;S73S58VJAv;SffA1S103R3R2A5VFAM;S5aS2bS2cS3aS59A2S2cS0S2A2S2bS3aS59S103SffA4S2bS0S2Z41Sa2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  change (JAv ndXA) with (JAv (NDA (nd_tv ndXA) fr_hf (nd_bd ndXA) ANone)).
  eapply TR_pre with (P := SPA segs (JAv (NDA (kept_mi ++ [(mi_d, (kb 12 mi_k))]) fr_hf (nd_bd ndXA) ANone)) E_mi rho tp).
  { intros w Hw. apply (SPA_tv_permb segs AInv CST XGL NPH Kc rho0 (P0_hf CST FB FF) FB FF BX PTrue _ _ fr_hf _ ANone E_mi rho tp w mi_tvp).
    apply (xff_imp _ E_mi0 E_mi1x E_mi (xf_vr 15 496) (vr_need 12 (SAlu ALU_ADD mi_c (SLit 3)) (NMI pA)) rho tp w E_mi1x_eq E_mi_eq2 mi_xff); [|exact Hw].
    intros tr md _ HF1. exact (vr_mi3_ok rho _ HF1 mi_needF). }
  apply (X_VR E_mi kept_mi mi_d mi_k 12 496 (nd_bd ndXA) brest_mi s_mi R_mi (XkeepF mi_d (X_body pDco pKco)) rho tp _ T_mik0 T_mif0 T_mig0 (SVar 520) (SVar 521) bdK_mi bdG_mi
           (mi_chk XGL) R_mi_eq T_mik0_ta mi_iK mi_bK T_mif0_ta mi_iF T_mig0_ta mi_iG mi_bG).
  -
    intros rho' tp' Hag HF.
    eapply TR_pre; [|apply (REENTER JR_mi ndMI (64, z0) (rho_sub rho' s_mik)); [innth 15 | rewrite !emeas_z0; lia]].
    intros w Hw. apply (land_imp (shadow_reopen_stateA T_miks (ax_X T_miks) hG 4 5) JR_mi s_mik (kept_mi ++ [(mi_d, (kb 12 mi_k))]) tv2_mik (bdK_mi ++ brest_mi) bd2_mik _ _ rho' tp' w mik_land mik_bd).
    apply (reopen_imp T_miks (ax_X T_miks) (kept_mi ++ [(mi_d, (kb 12 mi_k))]) _ 4 5 rho' tp' w (mik_ro0 XGL)).
    apply (xff_imp _ T_mik0 T_mik T_miks (xf_backV 14 28 496) [SPUle (SLit IMG_HI) mi_d; co_live] rho' tp' w T_mik_ap T_miks_eq2 mik_xff); [|exact Hw].
    intros tr md HJ HF1.
    constructor; [exact (let K := k_nz_lit rho' _ mi_c 3 mi_k HF1 ltac:(lia) mik_live in live_holds _ rho' tp' tr md mi_d 12 mi_k HJ ltac:(cbn; tauto) ltac:(lia) (proj1 K) (proj2 K))|constructor; [exact (let K := k_nz_3 rho' _ pA pKco HF1 mik_colive in live_holds _ rho' tp' tr md pDco 12 pKco HJ ltac:(cbn; tauto) ltac:(lia) (proj1 K) (proj2 K))|constructor]].
  -
    intros rho' tp' Hag HF.
    eapply TR_pre; [|apply (REENTER JF_mi ndMIf (20, z0) (rho_sub rho' s_mif)); [innth 16 | rewrite !emeas_z0; lia]].
    intros w Hw. apply (land_imp T_mifs JF_mi s_mif (kept_mi ++ [(mi_d, (kb 12 mi_k))]) tv2_mif (firstn 1 brest_mi) (firstn 1 brest_mi) _ _ rho' tp' w mif_land mif_bd).
    apply (drop_imp _ _ fr_hf brest_mi 1 rho' tp' w mif_wp).
    apply (xff_imp _ T_mif0 T_mif T_mifs (xf_backV 14 28 496) [co_live] rho' tp' w T_mif_ap T_mifs_eq2 mif_xff); [|exact Hw].
    intros tr md HJ HF1.
    constructor; [exact (let K := k_nz_3 rho' _ pA pKco HF1 mif_colive in live_holds _ rho' tp' tr md pDco 12 pKco HJ ltac:(cbn; tauto) ltac:(lia) (proj1 K) (proj2 K))|constructor].
  -
    intros rho' tp' Hag HF.
    eapply TR_pre; [|apply (REENTER JR_mi ndMI (64, z0) (rho_sub rho' s_mig)); [innth 15 | rewrite !emeas_z0; lia]].
    intros w Hw. apply (land_imp (shadow_reopen_stateA T_migs (ax_X T_migs) hG 4 5) JR_mi s_mig (kept_mi ++ [(SVar 520, (kb 12 (SVar 521)))]) tv2_mig (bdG_mi ++ brest_mi) bd2_mig _ _ rho' tp' w mig_land mig_bd).
    apply (reopen_imp T_migs (ax_X T_migs) (kept_mi ++ [(SVar 520, (kb 12 (SVar 521)))]) _ 4 5 rho' tp' w (mig_ro0 XGL)).
    apply (xff_imp _ T_mig0 T_mig T_migs (xf_backV 14 28 496) [co_live] rho' tp' w T_mig_ap T_migs_eq2 mig_xff); [|exact Hw].
    intros tr md HJ HF1.
    constructor; [exact (let K := k_nz_3 rho' _ pA pKco HF1 mig_colive in live_holds _ rho' tp' tr md pDco 12 pKco HJ ltac:(cbn; tauto) ltac:(lia) (proj1 K) (proj2 K))|constructor].
Qed.

Lemma XH_E_fv0 : ltac2:(tb__ "0|1|
S3S2aS77Q40A1A1M0G0VTR;S73S58VJAv;SaeA1S101R3R2A5VFAM;S5aS2bS2cS3aS59A2S2cS0S2A2S2bS3aS59S101SaeA4S2bS0S2Z3bSa2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  apply (TR_absorb _ E_fv1 ndMI rho tp).
  { intros tr ms md Hw. exists (rho_absorb rho [shobj hG 4 5 cells_fv DUnknown] (vms md tp ms)). split; [intros ee; apply eval_absorb|].
    rewrite <- E_fv1_eq. exact (release_imp E_fv0 objs_fv0 4 5 cells_fv DUnknown [(32, 4)] _ _ rho tp tr ms md fv_rel fv_robjs Hw). }
  intros rho1 HE1.
  change (JAv ndMI) with (JAv (NDA (nd_tv ndMI) fr_hf (nd_bd ndMI) ANone)).
  eapply TR_pre with (P := SPA segs (JAv (NDA (kept_fv ++ [(fv_d, (kb 4 fv_k))]) fr_hf (nd_bd ndMI) ANone)) E_fv rho1 tp).
  { intros w Hw. apply (SPA_tv_permb segs AInv CST XGL NPH Kc rho0 (P0_hf CST FB FF) FB FF BX PTrue _ _ fr_hf _ ANone E_fv rho1 tp w fv_tvp).
    apply (xff_imp _ E_fv1 E_fv1x E_fv (xf_vr 16 528) (vr_need 4 (SAlu ALU_ADD fv_c (SLit 1)) (NFV pA)) rho1 tp w E_fv1x_eq E_fv_eq2 fv_xff); [|exact Hw].
    intros tr md _ HF1. exact (vr_fv3_ok rho1 _ fv_c fv_n HF1 fv_needF). }
  apply (X_VR E_fv kept_fv fv_d fv_k 4 528 (nd_bd ndMI) brest_fv s_fv R_fv (XkeepF fv_d XF1) rho1 tp _ T_fvk0 T_fvf0 T_fvg0 (SVar 520) (SVar 521) bdK_fv bdG_fv
           (fv_chk XGL) R_fv_eq T_fvk0_ta fv_iK fv_bK T_fvf0_ta fv_iF T_fvg0_ta fv_iG fv_bG).
  -
    intros rho' tp' Hag HF.
    eapply TR_pre; [|apply (REENTER JR_fv ndFV (58, z0) (rho_sub rho' s_fvk)); [innth 19 | rewrite !emeas_z0; lia]].
    intros w Hw. apply (land_imp T_fvks JR_fv s_fvk (kept_fv ++ [(fv_d, (kb 4 fv_k))]) tv2_fvk (bdK_fv ++ brest_fv) bd2_fvk _ _ rho' tp' w fvk_land fvk_bd).
    apply (xff_imp _ T_fvk0 T_fvk T_fvks (xf_backV 15 29 528) [SPUle (SLit IMG_HI) fv_d] rho' tp' w T_fvk_ap T_fvks_eq2 fvk_xff); [|exact Hw].
    intros tr md HJ HF1.
    constructor; [exact (let K := k_nz_lit rho' _ fv_c 1 fv_k HF1 ltac:(lia) fvk_live in live_holds _ rho' tp' tr md fv_d 4 fv_k HJ ltac:(cbn; tauto) ltac:(lia) (proj1 K) (proj2 K))|constructor].
  -
    intros rho' tp' Hag HF.
    eapply TR_pre; [|apply (REENTER JF_fv ndFVf (20, z0) (rho_sub rho' s_fvf)); [innth 20 | rewrite !emeas_z0; lia]].
    intros w Hw. apply (land_imp (shadow_reopen_stateA T_fvf (X_face pDmi fv_d mm_d sg_d pDco rp_d tr_d ts_d pKmi fv_k mm_k sg_k pKco rp_k tr_k ts_k) hG 4 5) JF_fv s_fvf (kept_fv ++ [(fv_d, (kb 4 fv_k))]) tv2_fvf (firstn 1 brest_fv) (firstn 1 brest_fv) _ _ rho' tp' w fvf_land fvf_bd).
    apply (drop_imp _ _ fr_hf brest_fv 1 rho' tp' w fvf_wp).
    apply (reopen_imp T_fvf (X_face pDmi fv_d mm_d sg_d pDco rp_d tr_d ts_d pKmi fv_k mm_k sg_k pKco rp_k tr_k ts_k) (kept_fv ++ [(fv_d, (kb 4 fv_k))]) _ 4 5 rho' tp' w (fvf_ro0 XGL)).
    exact (SPA_axforms segs _ (xf_backV 15 29 528) rho' T_fvf0 T_fvf tp' w T_fvf_ap Hw).
  -
    intros rho' tp' Hag HF.
    eapply TR_pre; [|apply (REENTER JR_fv ndFV (58, z0) (rho_sub rho' s_fvg)); [innth 19 | rewrite !emeas_z0; lia]].
    intros w Hw. apply (land_imp T_fvg JR_fv s_fvg (kept_fv ++ [(SVar 520, (kb 4 (SVar 521)))]) tv2_fvg (bdG_fv ++ brest_fv) bd2_fvg _ _ rho' tp' w fvg_land fvg_bd).
    exact (SPA_axforms segs _ (xf_backV 15 29 528) rho' T_fvg0 T_fvg tp' w T_fvg_ap Hw).
Qed.

Lemma XH_E_mm0 : ltac2:(tb__ "0|1|
S3S2aS77Q40A1A1M0G0VTR;S73S58VJAv;Sa7A1S104R3R2A5VFAM;S5aS2bS2cS3aS59A2S2cS0S2A2S2bS3aS59S104Sa7A4S2bS0S2Z37Sa2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  change (JAv ndFV) with (JAv (NDA (nd_tv ndFV) fr_hf (nd_bd ndFV) ANone)).
  eapply TR_pre with (P := SPA segs (JAv (NDA (kept_mm ++ [(mm_d, (kb 4 mm_k))]) fr_hf (nd_bd ndFV) ANone)) E_mm rho tp).
  { intros w Hw. apply (SPA_tv_permb segs AInv CST XGL NPH Kc rho0 (P0_hf CST FB FF) FB FF BX PTrue _ _ fr_hf _ ANone E_mm rho tp w mm_tvp).
    apply (xff_imp _ E_mm0 E_mm1x E_mm (xf_vr 17 560) (vr_need 4 (SAlu ALU_ADD mm_c (SLit 1)) (NMM pA)) rho tp w E_mm1x_eq E_mm_eq2 mm_xff); [|exact Hw].
    intros tr md _ HF1. exact (vr_fv3_ok rho _ mm_c mm_n HF1 mm_needF). }
  apply (X_VR E_mm kept_mm mm_d mm_k 4 560 (nd_bd ndFV) brest_mm s_mm R_mm (XkeepF mm_d (XFV pDfv pKfv)) rho tp _ T_mmk0 T_mmf0 T_mmg0 (SVar 560) (SVar 561) bdK_mm bdG_mm
           (mm_chk XGL) R_mm_eq T_mmk0_ta mm_iK mm_bK T_mmf0_ta mm_iF T_mmg0_ta mm_iG mm_bG).
  -
    intros rho' tp' Hag HF.
    eapply TR_pre; [|apply (REENTER JR_mm ndMM (54, z0) (rho_sub rho' s_mmk)); [innth 22 | rewrite !emeas_z0; lia]].
    intros w Hw. apply (land_imp T_mmks JR_mm s_mmk (kept_mm ++ [(mm_d, (kb 4 mm_k))]) tv2_mmk (bdK_mm ++ brest_mm) bd2_mmk _ _ rho' tp' w mmk_land mmk_bd).
    apply (xff_imp _ T_mmk0 T_mmk T_mmks (xf_backV 16 30 560) [SPUle (SLit IMG_HI) mm_d] rho' tp' w T_mmk_ap T_mmks_eq2 mmk_xff); [|exact Hw].
    intros tr md HJ HF1.
    constructor; [exact (let K := k_nz_lit rho' _ mm_c 1 mm_k HF1 ltac:(lia) mmk_live in live_holds _ rho' tp' tr md mm_d 4 mm_k HJ ltac:(cbn; tauto) ltac:(lia) (proj1 K) (proj2 K))|constructor].
  -
    intros rho' tp' Hag HF.
    eapply TR_pre; [|apply (REENTER JF_mm ndMMf (20, z0) (rho_sub rho' s_mmf)); [innth 23 | rewrite !emeas_z0; lia]].
    intros w Hw. apply (land_imp (shadow_reopen_stateA T_mmf (XMM mm_d mm_k) hG 4 5) JF_mm s_mmf (kept_mm ++ [(mm_d, (kb 4 mm_k))]) tv2_mmf (firstn 1 brest_mm) (firstn 1 brest_mm) _ _ rho' tp' w mmf_land mmf_bd).
    apply (drop_imp _ _ fr_hf brest_mm 1 rho' tp' w mmf_wp).
    apply (reopen_imp T_mmf (XMM mm_d mm_k) (kept_mm ++ [(mm_d, (kb 4 mm_k))]) _ 4 5 rho' tp' w (mmf_ro0 XGL)).
    exact (SPA_axforms segs _ (xf_backV 16 30 560) rho' T_mmf0 T_mmf tp' w T_mmf_ap Hw).
  -
    intros rho' tp' Hag HF.
    eapply TR_pre; [|apply (REENTER JR_mm ndMM (54, z0) (rho_sub rho' s_mmg)); [innth 22 | rewrite !emeas_z0; lia]].
    intros w Hw. apply (land_imp T_mmg JR_mm s_mmg (kept_mm ++ [(SVar 560, (kb 4 (SVar 561)))]) tv2_mmg (bdG_mm ++ brest_mm) bd2_mmg _ _ rho' tp' w mmg_land mmg_bd).
    exact (SPA_axforms segs _ (xf_backV 16 30 560) rho' T_mmg0 T_mmg tp' w T_mmg_ap Hw).
Qed.

Lemma XH_E_sg0 : ltac2:(tb__ "0|1|
S3S2aS77Q40A1A1M0G0VTR;S73S58VJAv;SafA1S1a7R3R2A5VFAM;S5aS2bS2cS3aS59A2S2cS0S2A2S2bS3aS59S1a7SafA4S2bS0S2Z35Sa2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  change (JAv ndMM) with (JAv (NDA (nd_tv ndMM) fr_hf (nd_bd ndMM) ANone)).
  eapply TR_pre with (P := SPA segs (JAv (NDA (kept_sg ++ [(sg_d, (kb 4 sg_k))]) fr_hf (nd_bd ndMM) ANone)) E_sg rho tp).
  { intros w Hw. apply (SPA_tv_permb segs AInv CST XGL NPH Kc rho0 (P0_hf CST FB FF) FB FF BX PTrue _ _ fr_hf _ ANone E_sg rho tp w sg_tvp).
    apply (xff_imp _ E_sg0 E_sg1x E_sg (xf_vr 18 592) (vr_need 4 (SAlu ALU_ADD sg_c (SLit 1)) (NSG pA)) rho tp w E_sg1x_eq E_sg_eq2 sg_xff); [|exact Hw].
    intros tr md _ HF1. exact (vr_fv3_ok rho _ sg_c sg_n HF1 sg_needF). }
  apply (X_VR E_sg kept_sg sg_d sg_k 4 592 (nd_bd ndMM) brest_sg s_sg R_sg (XkeepF sg_d (XMM pDmm pKmm)) rho tp _ T_sgk0 T_sgf0 T_sgg0 (SVar 656) (SVar 657) bdK_sg bdG_sg
           (sg_chk XGL) R_sg_eq T_sgk0_ta sg_iK sg_bK T_sgf0_ta sg_iF T_sgg0_ta sg_iG sg_bG).
  -
    intros rho' tp' Hag HF.
    eapply TR_pre; [|apply (REENTER JR_sg ndSG (52, z0) (rho_sub rho' s_sgk)); [innth 24 | rewrite !emeas_z0; lia]].
    intros w Hw. apply (land_imp (shadow_reopen_stateA T_sgks (XnoL T_sgks) hG 4 5) JR_sg s_sgk (kept_sg ++ [(sg_d, (kb 4 sg_k))]) tv2_sgk (bdK_sg ++ brest_sg) bd2_sgk _ _ rho' tp' w sgk_land sgk_bd).
    apply (reopen_imp T_sgks (XnoL T_sgks) (kept_sg ++ [(sg_d, (kb 4 sg_k))]) _ 4 5 rho' tp' w (sgk_ro0 XGL)).
    apply (xff_imp _ T_sgk0 T_sgk T_sgks (xf_backV 17 31 592) [SPUle (SLit IMG_HI) sg_d] rho' tp' w T_sgk_ap T_sgks_eq2 sgk_xff); [|exact Hw].
    intros tr md HJ HF1.
    constructor; [exact (let K := k_nz_lit rho' _ sg_c 1 sg_k HF1 ltac:(lia) sgk_live in live_holds _ rho' tp' tr md sg_d 4 sg_k HJ ltac:(cbn; tauto) ltac:(lia) (proj1 K) (proj2 K))|constructor].
  -
    intros rho' tp' Hag HF.
    eapply TR_pre; [|apply (REENTER JF_sg ndSGf (20, z0) (rho_sub rho' s_sgf)); [innth 25 | rewrite !emeas_z0; lia]].
    intros w Hw. apply (land_imp (shadow_reopen_stateA T_sgf (XnoL T_sgf) hG 4 5) JF_sg s_sgf (kept_sg ++ [(sg_d, (kb 4 sg_k))]) tv2_sgf (firstn 1 brest_sg) (firstn 1 brest_sg) _ _ rho' tp' w sgf_land sgf_bd).
    apply (drop_imp _ _ fr_hf brest_sg 1 rho' tp' w sgf_wp).
    apply (reopen_imp T_sgf (XnoL T_sgf) (kept_sg ++ [(sg_d, (kb 4 sg_k))]) _ 4 5 rho' tp' w (sgf_ro0 XGL)).
    exact (SPA_axforms segs _ (xf_backV 17 31 592) rho' T_sgf0 T_sgf tp' w T_sgf_ap Hw).
  -
    intros rho' tp' Hag HF.
    eapply TR_pre; [|apply (REENTER JR_sg ndSG (52, z0) (rho_sub rho' s_sgg)); [innth 24 | rewrite !emeas_z0; lia]].
    intros w Hw. apply (land_imp (shadow_reopen_stateA T_sgg (XnoL T_sgg) hG 4 5) JR_sg s_sgg (kept_sg ++ [(SVar 656, (kb 4 (SVar 657)))]) tv2_sgg (bdG_sg ++ brest_sg) bd2_sgg _ _ rho' tp' w sgg_land sgg_bd).
    apply (reopen_imp T_sgg (XnoL T_sgg) (kept_sg ++ [(SVar 656, (kb 4 (SVar 657)))]) _ 4 5 rho' tp' w (sgg_ro0 XGL)).
    exact (SPA_axforms segs _ (xf_backV 17 31 592) rho' T_sgg0 T_sgg tp' w T_sgg_ap Hw).
Qed.

Lemma XH_E_mc0 : ltac2:(tb__ "0|1|
S3S2aS77Q40A1A1M0G0VTR;S73S58VJAv;Sa7A1S102R3R2A5VFAM;S5aS2bS2cS3aS59A2S2cS0S2A2S2bS3aS59S102Sa7A4S2bS0S2Z39Sa2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. change (JAv ndFV) with (JAv (NDA (nd_tv ndFV) fr_hf (nd_bd ndFV) ANone)).
  eapply TR_pre with (P := SPA segs (JAv (NDA (nd_tv ndFV) fr_hf (nd_bd ndFV) ANone)) E_mc rho tp).
  { intros w Hw. rewrite <- E_mc_eq. unfold a0_mc.
    apply (reshape_fwd _ E_mc1 32 pDfv (kb 4 fv_c) (SMd M_MUL fv_c (SLit 4)) 4 DUnknown rho tp w mc_o32 eq_refl mc_wf ltac:(lia) (fun r => uval_mulc_kb r fv_c 4)
             (fun HF => let B := rs_bnd_kb rho _ pDfv 4 fv_c fv_n HF ltac:(lia) mc_bnd in conj (proj1 B) (proj1 (proj2 B)))).
    exact (SPA_axforms segs _ xf_mcf rho E_mc0 E_mc1 tp w E_mc1_eq Hw). }
  apply (X_purecT XP_memcpy Pre_mc [L_mc1; L_mc1] E_mc (nd_tv ndFV) (nd_bd ndFV) s_mcf R_mcf rho tp _ (fun Ai rho1 tp1 => CMEMCPY Ai rho1 tp1)
           (fun Ai tr ms md Hsm HM HX => XP_memcpy_site segs AInv CST XGL ALA HCST HXGL Ai E_mc memcpy_pc s_mcf R_mcf rho tp tr ms md Hsm HM HX R_mcf_eq)
           eq_refl eq_refl R_mcf_eq (mc_chk XGL)).
  intros L0 rho' tp' HL Hag HF. assert (HL' : L0 = L_mc1) by (destruct HL as [<-|[<-|[]]]; reflexivity). subst L0.
  eapply TR_pre; [|apply (REENTER T_mcq ndFV (56, z0) rho'); [innth 21 | rewrite !emeas_z0; lia]].
  intros w Hw. change (JAv ndFV) with (JAv (NDA (nd_tv ndFV) fr_hf (nd_bd ndFV) ANone)).
  apply (SPA_axforms segs _ _ rho' T_mc1 T_mcq tp' w T_mcq_eq). rewrite <- T_mc1_eq.
  apply (reshape_bwd _ T_mc0 1 pDfv (kb 4 fv_c) (SMd M_MUL fv_c (SLit 4)) 4 DUnknown rho' tp' w mc_to1 eq_refl mc_twf ltac:(lia) (fun r => uval_mulc_kb r fv_c 4)
           (fun HF => let B := rs_bnd_kb rho' _ pDfv 4 fv_c fv_n HF ltac:(lia) mc_tbnd in conj (proj1 B) (proj1 (proj2 B)))).
  rewrite <- T_mc0_eq. exact Hw.
Qed.

Lemma XH_E_md0 : ltac2:(tb__ "0|1|
S3S2aS77Q40A1A1M0G0VTR;S73S58VJAv;Sa5A1Sd1R3R2A5VFAM;S5aS2bS2cS3aS59A2S2cS0S2A2S2bS3aS59Sd1Sa5A4S2bS0S2Z35Sa2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. change (JAv ndTS) with (JAv (NDA (nd_tv ndTS) fr_hf (nd_bd ndTS) ANone)).
  apply (TR_absorb _ E_md1 (NDA (nd_tv ndTS) fr_hf (nd_bd ndTS) ANone) rho tp).
  { intros tr ms md Hw. exists (rho_absorb rho [shobj hG 6 15 cells_md DUnknown] (vms md tp ms)). split; [intros ee; apply eval_absorb|].
    rewrite <- E_md1_eq. exact (release_imp E_md0 (objs_butlast E_md0) 6 15 cells_md DUnknown [(48, 72)] _ _ rho tp tr ms md md_rel md_robjs Hw). }
  intros rho1 HE1.
  eapply TR_pre with (P := SPA segs (JAv (NDA (nd_tv ndTS) fr_hf (nd_bd ndTS) ANone)) E_md rho1 tp).
  { intros w Hw. apply (SPA_axforms segs _ [AXUnbase 2 56] rho1 E_mdx E_md tp w E_md_ub). exact (SPA_axforms segs _ xf_md rho1 E_md1 E_mdx tp w E_mdx_eq Hw). }
  apply (X_purecT XP_memset Pre_ms [L_ms] E_md (nd_tv ndTS) (nd_bd ndTS) s_md R_md rho1 tp _ (fun Ai rho2 tp2 => CMEMSET Ai rho2 tp2)
           (fun Ai tr ms md Hsm HM HX => XP_memset_site segs AInv CST XGL ALA HCST HXGL Ai E_md memset_pc s_md R_md rho1 tp tr ms md Hsm HM HX R_md_eq)
           eq_refl eq_refl R_md_eq (md_chk XGL)).
  intros L0 rho' tp' HL Hag HF. destruct HL as [<-|[]].
  eapply TR_pre; [|apply (REENTER T_md ndTS (52, z0) rho'); [innth 43 | rewrite !emeas_z0; lia]].
  intros w Hw. change (JAv ndTS) with (JAv (NDA (nd_tv ndTS) fr_hf (nd_bd ndTS) ANone)).
  rewrite <- T_md_eq. unfold reopenX. apply (reopenS_imp T_md3 (ax_X T_md3) (nd_tv ndTS) _ 20 23 rho' tp' w (md_ro XGL)).
  apply (SPA_axforms segs _ _ rho' T_md2 T_md3 tp' w T_md3_eq). rewrite <- T_md2_eq2.
  apply (SPA_zero_cells segs _ rho' T_md1 1 cs_md (ax_S T_md2) tp' w T_md2_zc T_md2_wf).
  apply (SPA_axforms segs _ [AXRebase 1] rho' T_md0 T_md1 tp' w T_md1_rb). rewrite <- T_md0_eq. exact Hw.
Qed.

Lemma XH_E_trg0 : ltac2:(tb__ "0|1|
S3S2aS77Q40A1A1M0G0VTR;S73S58VJAv;SffA1S180R3R2A5VFAM;S5aS2bS2cS3aS59A2S2cS0S2A2S2bS3aS59S180SffA4S2bS0S2Z3fSa2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  change (JAv ndXA) with (JAv (NDA (nd_tv ndXA) fr_hf (nd_bd ndXA) ANone)).
  eapply TR_pre with (P := SPA segs (JAv (NDA (kept_trg ++ [(tr_d, (kb 4 tr_k))]) fr_hf (nd_bd ndXA) ANone)) E_trg rho tp).
  { intros w Hw. apply (SPA_tv_permb segs AInv CST XGL NPH Kc rho0 (P0_hf CST FB FF) FB FF BX PTrue _ _ fr_hf _ ANone E_trg rho tp w trg_tvp).
    rewrite <- E_trg_eq2. exact (SPA_axforms segs _ (xf_vr 21 784) rho E_trg0 E_trg1x tp w E_trg1x_eq Hw). }
  apply (X_VR E_trg kept_trg tr_d tr_k 4 784 (nd_bd ndXA) brest_trg s_trg R_trg (XkeepF tr_d (X_body pDco pKco)) rho tp _ T_trgk0 T_trgf0 T_trgg0 (SVar 520) (SVar 521) bdK_trg bdG_trg
           (trg_chk XGL) R_trg_eq T_trgk0_ta trg_iK trg_bK T_trgf0_ta trg_iF T_trgg0_ta trg_iG trg_bG).
  -
    intros rho' tp' Hag HF.
    eapply TR_pre; [|apply (REENTER JR_trg ndTR (62, z0) (rho_sub rho' s_trgk)); [innth 29 | rewrite !emeas_z0; lia]].
    intros w Hw. apply (land_imp T_trgk JR_trg s_trgk (kept_trg ++ [(tr_d, (kb 4 tr_k))]) tv2_trgk (bdK_trg ++ brest_trg) bd2_trgk _ _ rho' tp' w trgk_land trgk_bd).
    apply (xff_imp _ T_trgk0 T_trgk1 T_trgk (xf_backV 20 34 784) [SPUle (SLit IMG_HI) tr_d] rho' tp' w T_trgk1_ap T_trgk_eq2 trgk_xff); [|exact Hw].
    intros tr md HJ HF1.
    constructor; [exact (let K := k_nz_tri rho' _ tr_k HF1 trgk_live in live_holds _ rho' tp' tr md tr_d 4 tr_k HJ ltac:(cbn; tauto) ltac:(lia) (proj1 K) (proj2 K))|constructor].
  -
    intros rho' tp' Hag HF.
    eapply TR_pre; [|apply (REENTER JF_trg ndTRf (20, z0) (rho_sub rho' s_trgf)); [innth 30 | rewrite !emeas_z0; lia]].
    intros w Hw. apply (land_imp T_trgf JF_trg s_trgf (kept_trg ++ [(tr_d, (kb 4 tr_k))]) tv2_trgf (firstn 1 brest_trg) (firstn 1 brest_trg) _ _ rho' tp' w trgf_land trgf_bd).
    apply (drop_imp _ _ fr_hf brest_trg 1 rho' tp' w trgf_wp).
    exact (SPA_axforms segs _ (xf_backV 20 34 784) rho' T_trgf0 T_trgf tp' w T_trgf_ap Hw).
  -
    intros rho' tp' Hag HF.
    eapply TR_pre; [|apply (REENTER JR_trg ndTR (62, z0) (rho_sub rho' s_trgg)); [innth 29 | rewrite !emeas_z0; lia]].
    intros w Hw. apply (land_imp T_trgg JR_trg s_trgg (kept_trg ++ [(SVar 520, (kb 4 (SVar 521)))]) tv2_trgg (bdG_trg ++ brest_trg) bd2_trgg _ _ rho' tp' w trgg_land trgg_bd).
    exact (SPA_axforms segs _ (xf_backV 20 34 784) rho' T_trgg0 T_trgg tp' w T_trgg_ap Hw).
Qed.

Lemma XH_E_trb0 : ltac2:(tb__ "0|1|
S3S2aS77Q40A1A1M0G0VTR;S73S58VJAv;SffA1S17fR3R2A5VFAM;S5aS2bS2cS3aS59A2S2cS0S2A2S2bS3aS59S17fSffA4S2bS0S2Z3fSa2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  change (JAv ndXA) with (JAv (NDA (nd_tv ndXA) fr_hf (nd_bd ndXA) ANone)).
  eapply TR_pre with (P := SPA segs (JAv (NDA (kept_trb ++ [(tr_d, (kb 4 tr_k))]) fr_hf (nd_bd ndXA) ANone)) E_trb rho tp).
  { intros w Hw. apply (SPA_tv_permb segs AInv CST XGL NPH Kc rho0 (P0_hf CST FB FF) FB FF BX PTrue _ _ fr_hf _ ANone E_trb rho tp w trb_tvp).
    rewrite <- E_trb_eq2. exact (SPA_axforms segs _ (xf_vr 21 784) rho E_trb0 E_trb1x tp w E_trb1x_eq Hw). }
  apply (X_VR E_trb kept_trb tr_d tr_k 4 784 (nd_bd ndXA) brest_trb s_trb R_trb (XkeepF tr_d (X_body pDco pKco)) rho tp _ T_trbk0 T_trbf0 T_trbg0 (SVar 520) (SVar 521) bdK_trb bdG_trb
           (trb_chk XGL) R_trb_eq T_trbk0_ta trb_iK trb_bK T_trbf0_ta trb_iF T_trbg0_ta trb_iG trb_bG).
  -
    intros rho' tp' Hag HF.
    eapply TR_pre; [|apply (REENTER JR_trb ndTR (62, z0) (rho_sub rho' s_trbk)); [innth 31 | rewrite !emeas_z0; lia]].
    intros w Hw. apply (land_imp T_trbk JR_trb s_trbk (kept_trb ++ [(tr_d, (kb 4 tr_k))]) tv2_trbk (bdK_trb ++ brest_trb) bd2_trbk _ _ rho' tp' w trbk_land trbk_bd).
    apply (xff_imp _ T_trbk0 T_trbk1 T_trbk (xf_backV 20 34 784) [SPUle (SLit IMG_HI) tr_d] rho' tp' w T_trbk1_ap T_trbk_eq2 trbk_xff); [|exact Hw].
    intros tr md HJ HF1.
    constructor; [exact (let K := k_nz_tri rho' _ tr_k HF1 trbk_live in live_holds _ rho' tp' tr md tr_d 4 tr_k HJ ltac:(cbn; tauto) ltac:(lia) (proj1 K) (proj2 K))|constructor].
  -
    intros rho' tp' Hag HF.
    eapply TR_pre; [|apply (REENTER JF_trb ndTRf (20, z0) (rho_sub rho' s_trbf)); [innth 32 | rewrite !emeas_z0; lia]].
    intros w Hw. apply (land_imp T_trbf JF_trb s_trbf (kept_trb ++ [(tr_d, (kb 4 tr_k))]) tv2_trbf (firstn 1 brest_trb) (firstn 1 brest_trb) _ _ rho' tp' w trbf_land trbf_bd).
    apply (drop_imp _ _ fr_hf brest_trb 1 rho' tp' w trbf_wp).
    exact (SPA_axforms segs _ (xf_backV 20 34 784) rho' T_trbf0 T_trbf tp' w T_trbf_ap Hw).
  -
    intros rho' tp' Hag HF.
    eapply TR_pre; [|apply (REENTER JR_trb ndTR (62, z0) (rho_sub rho' s_trbg)); [innth 31 | rewrite !emeas_z0; lia]].
    intros w Hw. apply (land_imp T_trbg JR_trb s_trbg (kept_trb ++ [(SVar 520, (kb 4 (SVar 521)))]) tv2_trbg (bdG_trb ++ brest_trb) bd2_trbg _ _ rho' tp' w trbg_land trbg_bd).
    exact (SPA_axforms segs _ (xf_backV 20 34 784) rho' T_trbg0 T_trbg tp' w T_trbg_ap Hw).
Qed.

Lemma XH_E_rp0 : ltac2:(tb__ "0|1|
S3S2aS77Q40A1A1M0G0VTR;S73S58VJAv;SaaA1Sf4R3R2A5VFAM;S5aS2bS2cS3aS59A2S2cS0S2A2S2bS3aS59Sf4SaaA4S2bS0S2Z3dSa2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  change (JAv ndTR) with (JAv (NDA (nd_tv ndTR) fr_hf (nd_bd ndTR) ANone)).
  eapply TR_pre with (P := SPA segs (JAv (NDA (kept_rp ++ [(rp_d, (kb 4 rp_k))]) fr_hf (nd_bd ndTR) ANone)) E_rp rho tp).
  { intros w Hw. apply (SPA_tv_permb segs AInv CST XGL NPH Kc rho0 (P0_hf CST FB FF) FB FF BX PTrue _ _ fr_hf _ ANone E_rp rho tp w rp_tvp).
    rewrite <- E_rp_eq2. exact (SPA_axforms segs _ (xf_vr 20 752) rho E_rp0 E_rp1x tp w E_rp1x_eq Hw). }
  apply (X_VR E_rp kept_rp rp_d rp_k 4 752 (nd_bd ndTR) brest_rp s_rp R_rp (XkeepF rp_d (XTR pDtr pKtr)) rho tp _ T_rpk0 T_rpf0 T_rpg0 (SVar 520) (SVar 521) bdK_rp bdG_rp
           (rp_chk XGL) R_rp_eq T_rpk0_ta rp_iK rp_bK T_rpf0_ta rp_iF T_rpg0_ta rp_iG rp_bG).
  -
    intros rho' tp' Hag HF.
    eapply TR_pre; [|apply (REENTER JR_rp ndRP (60, z0) (rho_sub rho' s_rpk)); [innth 35 | rewrite !emeas_z0; lia]].
    intros w Hw. apply (land_imp T_rpk JR_rp s_rpk (kept_rp ++ [(rp_d, (kb 4 rp_k))]) tv2_rpk (bdK_rp ++ brest_rp) bd2_rpk _ _ rho' tp' w rpk_land rpk_bd).
    apply (xff_imp _ T_rpk0 T_rpk1 T_rpk (xf_backV 19 33 752) [SPUle (SLit IMG_HI) rp_d] rho' tp' w T_rpk1_ap T_rpk_eq2 rpk_xff); [|exact Hw].
    intros tr md HJ HF1.
    constructor; [exact (let K := k_nz_rp rho' _ rp_k HF1 rpk_live in live_holds _ rho' tp' tr md rp_d 4 rp_k HJ ltac:(cbn; tauto) ltac:(lia) (proj1 K) (proj2 K))|constructor].
  -
    intros rho' tp' Hag HF.
    eapply TR_pre; [|apply (REENTER JF_rp ndRPf (20, z0) (rho_sub rho' s_rpf)); [innth 36 | rewrite !emeas_z0; lia]].
    intros w Hw. apply (land_imp T_rpf JF_rp s_rpf (kept_rp ++ [(rp_d, (kb 4 rp_k))]) tv2_rpf (firstn 1 brest_rp) (firstn 1 brest_rp) _ _ rho' tp' w rpf_land rpf_bd).
    apply (drop_imp _ _ fr_hf brest_rp 1 rho' tp' w rpf_wp).
    exact (SPA_axforms segs _ (xf_backV 19 33 752) rho' T_rpf0 T_rpf tp' w T_rpf_ap Hw).
  -
    intros rho' tp' Hag HF.
    eapply TR_pre; [|apply (REENTER JR_rp ndRP (60, z0) (rho_sub rho' s_rpg)); [innth 35 | rewrite !emeas_z0; lia]].
    intros w Hw. apply (land_imp T_rpg JR_rp s_rpg (kept_rp ++ [(SVar 520, (kb 4 (SVar 521)))]) tv2_rpg (bdG_rp ++ brest_rp) bd2_rpg _ _ rho' tp' w rpg_land rpg_bd).
    exact (SPA_axforms segs _ (xf_backV 19 33 752) rho' T_rpg0 T_rpg tp' w T_rpg_ap Hw).
Qed.

Lemma XH_E_ts0 : ltac2:(tb__ "0|1|
S3S2aS77Q40A1A1M0G0VTR;S73S58VJAv;Sb0A1Sf5R3R2A5VFAM;S5aS2bS2cS3aS59A2S2cS0S2A2S2bS3aS59Sf5Sb0A4S2bS0S2Z37Sa2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  change (JAv ndRP) with (JAv (NDA (nd_tv ndRP) fr_hf (nd_bd ndRP) ANone)).
  eapply TR_pre with (P := SPA segs (JAv (NDA (kept_ts ++ [(ts_d, (kb 1 ts_k))]) fr_hf (nd_bd ndRP) ANone)) E_ts rho tp).
  { intros w Hw. apply (SPA_tv_permb segs AInv CST XGL NPH Kc rho0 (P0_hf CST FB FF) FB FF BX PTrue _ _ fr_hf _ ANone E_ts rho tp w ts_tvp).
    apply (xff_imp _ E_ts0 E_ts1x E_ts (xf_vr 22 816) need_facts rho tp w E_ts1x_eq E_ts_eq2 ts_xff); [|exact Hw].
    intros tr md _ HF1. exact (ts_need_ok rho _ HF1 ts_needF). }
  apply (X_VR E_ts kept_ts ts_d ts_k 1 816 (nd_bd ndRP) brest_ts s_ts R_ts (XkeepF ts_d (XRT pDrp pKrp ts_d ts_k)) rho tp _ T_tsk0 T_tsf0 T_tsg0 (SVar 520) (SVar 521) bdK_ts bdG_ts
           (ts_chk XGL) R_ts_eq T_tsk0_ta ts_iK ts_bK T_tsf0_ta ts_iF T_tsg0_ta ts_iG ts_bG).
  -
    intros rho' tp' Hag HF.
    eapply TR_pre; [|apply (REENTER JR_ts ndTS (54, z0) (rho_sub rho' s_tsk)); [innth 41 | rewrite !emeas_z0; lia]].
    intros w Hw. apply (land_imp (shadow_reopen_stateA T_tsk (ax_X T_tsk) hG 6 15) JR_ts s_tsk (kept_ts ++ [(ts_d, (kb 1 ts_k))]) tv2_tsk (bdK_ts ++ brest_ts) bd2_tsk _ _ rho' tp' w tsk_land tsk_bd).
    apply (reopen_imp T_tsk (ax_X T_tsk) (kept_ts ++ [(ts_d, (kb 1 ts_k))]) _ 6 15 rho' tp' w (tsk_ro0 XGL)).
    apply (xff_imp _ T_tsk0 T_tsk1 T_tsk (xf_backV 21 35 816) [SPUle (SLit IMG_HI) ts_d] rho' tp' w T_tsk1_ap T_tsk_eq2 tsk_xff); [|exact Hw].
    intros tr md HJ HF1.
    constructor; [exact (let K := k_nz_ts rho' _ ts_k HF1 tsk_live in live_holds _ rho' tp' tr md ts_d 1 ts_k HJ ltac:(cbn; tauto) ltac:(lia) (proj1 K) (proj2 K))|constructor].
  -
    intros rho' tp' Hag HF.
    eapply TR_pre; [|apply (REENTER JF_ts ndTSf (20, z0) (rho_sub rho' s_tsf)); [innth 42 | rewrite !emeas_z0; lia]].
    intros w Hw. apply (land_imp T_tsf JF_ts s_tsf (kept_ts ++ [(ts_d, (kb 1 ts_k))]) tv2_tsf (firstn 1 brest_ts) (firstn 1 brest_ts) _ _ rho' tp' w tsf_land tsf_bd).
    apply (drop_imp _ _ fr_hf brest_ts 1 rho' tp' w tsf_wp).
    exact (SPA_axforms segs _ (xf_backV 21 35 816) rho' T_tsf0 T_tsf tp' w T_tsf_ap Hw).
  -
    intros rho' tp' Hag HF.
    eapply TR_pre; [|apply (REENTER JR_ts ndTS (54, z0) (rho_sub rho' s_tsg)); [innth 41 | rewrite !emeas_z0; lia]].
    intros w Hw. apply (land_imp (shadow_reopen_stateA T_tsg (ax_X T_tsg) hG 6 15) JR_ts s_tsg (kept_ts ++ [(SVar 520, (kb 1 (SVar 521)))]) tv2_tsg (bdG_ts ++ brest_ts) bd2_tsg _ _ rho' tp' w tsg_land tsg_bd).
    apply (reopen_imp T_tsg (ax_X T_tsg) (kept_ts ++ [(SVar 520, (kb 1 (SVar 521)))]) _ 6 15 rho' tp' w (tsg_ro0 XGL)).
    exact (SPA_axforms segs _ (xf_backV 21 35 816) rho' T_tsg0 T_tsg tp' w T_tsg_ap Hw).
Qed.

Lemma XH_E_tdg0 : ltac2:(tb__ "0|1|
S3S2aS77Q40A1A1M0G0VTR;S73S58VJAv;SaaA1S17eR3R2A5VFAM;S5aS2bS2cS3aS59A2S2cS0S2A2S2bS3aS59S17eSaaA4S2bS0S2Z3dSa2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  eapply TR_pre; [intros w Hw; exact (SPA_axforms segs _ [AXSplit 0 (SLit (-96))] rho E_tdg0 E_tdg tp w E_tdg_eq Hw)|].
  apply (X_pureT Pre_da P_da E_tdg T_tdg0 ndTR s_tdg R_tdg rho tp _ CALL_da R_tdg_eq tdg_chk T_tdg0_eq). intros rho' Hag.
  eapply TR_pre; [|apply (REENTER T_tdg ndTR (60, z0) rho'); [innth 33 | rewrite !emeas_z0; lia]].
  intros w Hw. apply (subX_imp _ T_tdg2 T_tdg (XTR pDtr pKtr) rho' tp w T_tdg_eq2 tdg_xsub). exact (SPA_axforms segs _ _ rho' T_tdg0 T_tdg2 tp w T_tdg2_eq Hw).
Qed.
Lemma XH_E_wdg0 : ltac2:(tb__ "0|1|
S3S2aS77Q40A1A1M0G0VTR;S73S58VJAv;Sa5A1S162R3R2A5VFAM;S5aS2bS2cS3aS59A2S2cS0S2A2S2bS3aS59S162Sa5A4S2bS0S2Z31Sa2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  eapply TR_pre; [intros w Hw; exact (SPA_axforms segs _ [AXSplit 0 (SLit (-96))] rho E_wdg0 E_wdg tp w E_wdg_eq Hw)|].
  apply (X_pureT Pre_da P_da E_wdg T_wdg0 ndTS s_wdg R_wdg rho tp _ CALL_da R_wdg_eq wdg_chk T_wdg0_eq). intros rho' Hag.
  eapply TR_pre; [|apply (REENTER T_wdg ndTS (48, z0) rho'); [innth 46 | rewrite !emeas_z0; lia]].
  intros w Hw. apply (subX_imp _ T_wdg2 T_wdg XT rho' tp w T_wdg_eq2 wdg_xsub). exact (SPA_axforms segs _ _ rho' T_wdg0 T_wdg2 tp w T_wdg2_eq Hw).
Qed.

Lemma XH_XJ : ltac2:(tb__ "0|1|
S3S2aS77Q40A1A1M0G0VTR;S73S58VJAv;SacA1S163R3R2A5VFAM;S5aS2bS2cS3aS59A2S2cS0S2A2S2bS3aS59S163SacA4S2bS0S2Z2fSa2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. change (JAv ndJN) with (JAv (NDA (nd_tv ndJN) fr_hf (nd_bd ndJN) ANone)).
  apply (TR_absorb _ XJ1 (NDA (nd_tv ndJN) fr_hf (nd_bd ndJN) ANone) rho tp).
  { intros tr ms md Hw. exists (rho_absorb rho [shobj hG 20 23 [] DUnknown] (vms md tp ms)). split; [intros ee; apply eval_absorb|].
    rewrite <- XJ1_eq. exact (release0_imp XJ objs_XJ 20 23 [] DUnknown _ _ rho tp tr ms md XJ_rel XJ_objs Hw). }
  intros rho1 _.
  apply (TR_absorb _ J (NDA (nd_tv ndJN) fr_hf (nd_bd ndJN) ANone) rho1 tp).
  { intros tr ms md Hw. exists (rho_absorb rho1 [shobj hG 6 15 [] DUnknown] (vms md tp ms)). split; [intros ee; apply eval_absorb|].
    rewrite <- J_eq2. exact (release_imp XJ1 objs_J 6 15 [] DUnknown [] _ _ rho1 tp tr ms md XJ1_rel XJ1_objs Hw). }
  intros rho2 _. apply (REENTER J ndJN (46, z0)); [innth 47 | rewrite !emeas_z0; lia].
Qed.

Lemma XH_XLJ : ltac2:(tb__ "0|1|
S3S2aS77Q40A1A1M0G0VTR;S73S58VJAv;Sa3A1S121R3R2A5VFAM;S5aS2bS2cS3aS59A2S2cS0S2A2S2bS3aS59S121Sa3A4S2bS0S2Z2dSa2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. change (JAv ndLL) with (JAv (NDA (nd_tv ndLL) fr_hf (nd_bd ndLL) ANone)).
  eapply TR_pre; [|apply (REENTER L14 ndLL (40, VL 60) rho); [innth 48 |
    rewrite emeas_z0; pose proof (emeas_ub L14 ndLL 40 (VL 60) rho); pose proof (emeas_lb L14 ndLL 40 (VL 60) rho ltac:(lia)); lia]].
  intros w Hw. change (JAv ndLL) with (JAv (NDA (nd_tv ndLL) fr_hf (nd_bd ndLL) ANone)).
  rewrite <- L14_eq2. apply (reopenS_imp XLJ1 (ax_X XLJf) (nd_tv ndLL) _ 38 39 rho tp w (XLJ_ro1 XGL)).
  rewrite <- XLJ1_eq. apply (reopen_imp XLJf (ax_X XLJf) (nd_tv ndLL) _ 28 33 rho tp w (XLJ_ro0 XGL)).
  apply (facts_imp _ XLJ XLJf [co_live] rho tp w eq_refl XLJ_xff); [|exact Hw].
  intros tr md HJ HF1. destruct (k_nz_L rho _ pKco HF1 XLJ_live) as [K1 K2].
  constructor; [exact (live_holds _ rho tp tr md pDco 12 pKco HJ ltac:(cbn; tauto) ltac:(lia) K1 K2) | constructor].
Qed.

Lemma X_arr1 : ltac2:(tb__ "0|7|
S3aS3aS2aS5A1M0S0S0S2aS2cS2S2A2A1S2aS46A1S3S2aS77Q40A1A1M1G1S0S0S32S24S2dS126RdRbRaR9S30S10A1M2SbS30S2cS0S0A2A1M3R8R7A9S2eA3S24G0ScS3bReA1A1S33S5RcS2fS5SdeS97RbRaG2SbA5S30S5A1A3A3A3S24S3aSdfRfRdPa0G3A4ReA3Sc5S2cS2cS3aS59A2M4S2cS0S2A2M5A2S2bG4G5S2bS3aS59RfS5cRbS7dRaS5bA4A4S2bS0S2R5Sa2A4A4S15eA3S25S50Z0R6A2S55R6R7A2A2VTR;S73S58VJAv;S5cRdS7dRcS5bA4M6A1R12RbRaA5VFAM;S5aS2bG4G5S2bS3aS59R12G6A4S2bS0S2R8Sa2A4A4RbA2R9A2A2F_;F_;F_;F_;F_;Fcut;FrkC;Frk;Ftp0;Ftp;Frho;Fbd;Ftv;Fk2;Fk1;Fobjs;FC;FA;").
Proof.
  intros A C objs k1 k2 tv bd rho tp tp0 rk rkC cut CK Ho HC Hin Hrk.
  apply (TR_absorb _ C (NDA tv fr_hf bd ANone) rho tp).
  { intros tr ms md Hw. exists (rho_absorb rho [shobj hG k1 k2 [] DUnknown] (vms md tp ms)). split; [intros ee; apply eval_absorb|].
    rewrite <- HC. exact (release_imp A objs k1 k2 [] DUnknown [] _ _ rho tp tr ms md CK Ho Hw). }
  intros rho1 _. apply (REENTER C (NDA tv fr_hf bd ANone) (rkC, z0)); [exact Hin | rewrite !emeas_z0; lia].
Qed.
Lemma X_arr2 : ltac2:(tb__ "0|9|
S3aS3aS3aS2aS5A1M0G0S0S0S0S0S2aS2cS2S2A2A1S2aS46A1S3S2aS77Q40A1A1M1G1S0S0S24S2dS19aR10RbRaSbA4S2eA3S24G0ScS3bR11A1A1S33S5ReS2fS5SdeS97RcRbS30S10A1M2SbA5S30S5A1M3A3A3A3S24S3aSdfR12RfPa0M4S30S2cS0S0A2A1M5A4R11A3S24S2dS126R12RfRcRbG2SbG5RaR9A9S2eA3S24G0ScS3bR13A1A1S33S5R10S2fS5SdeS97RdRcG2SbA5G3A3A3A3S24S3aSdfR14R11G4G5A4R13A3Sc5S2cS2cS3aS59A2M6S2cS0S2A2M7A2S2bG6G7S2bS3aS59R14S5cRdS7dRcS5bA4A4S2bS0S2R7Sa2A4A4S15eA3S25S50Z0R8A2S55R8R9A2A2VTR;S73S58VJAv;S5cRfS7dReS5bA4M8A1R18RdRcA5VFAM;S5aS2bG6G7S2bS3aS59R18G8A4S2bS0S2RaSa2A4A4RdA2RbA2A2F_;F_;F_;F_;F_;F_;F_;F_;FrkC;Frk;Ftp0;Ftp;Frho;Fbd;Ftv;Fk4;Fk3;Fk2;Fk1;Fobjs2;Fobjs1;FC;FB;FA;").
Proof.
  intros A B C objs1 objs2 k1 k2 k3 k4 tv bd rho tp tp0 rk rkC CK1 Ho1 HB CK2 Ho2 HC Hin Hrk.
  apply (TR_absorb _ B (NDA tv fr_hf bd ANone) rho tp).
  { intros tr ms md Hw. exists (rho_absorb rho [shobj hG k1 k2 [] DUnknown] (vms md tp ms)). split; [intros ee; apply eval_absorb|].
    rewrite <- HB. exact (release0_imp A objs1 k1 k2 [] DUnknown tv bd rho tp tr ms md CK1 Ho1 Hw). }
  intros rho1 HE1. rewrite <- (emeas_eq A (NDA tv fr_hf bd ANone) rk z0 rho rho1 HE1).
  apply (TR_absorb _ C (NDA tv fr_hf bd ANone) rho1 tp).
  { intros tr ms md Hw. exists (rho_absorb rho1 [shobj hG k3 k4 [] DUnknown] (vms md tp ms)). split; [intros ee; apply eval_absorb|].
    rewrite <- HC. exact (release_imp B objs2 k3 k4 [] DUnknown [] _ _ rho1 tp tr ms md CK2 Ho2 Hw). }
  intros rho2 _. apply (REENTER C (NDA tv fr_hf bd ANone) (rkC, z0)); [exact Hin | rewrite !emeas_z0; lia].
Qed.
Lemma XH_XEf42 : ltac2:(tb__ "0|1|
S3S2aS77Q40A1A1M0G0VTR;S73S58VJAv;SfdA1S18dR3R2A5VFAM;S5aS2bS2cS3aS59A2S2cS0S2A2S2bS3aS59S18dSfdA4S2bS0S2Z10Sa2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof. intros. unfold ndEf. apply (X_arr1 XEf42 C_Ef2 objs_Ef42 4 5 tvQ _ rho tp tp0 16 14 62 XEf42_rel XEf42_objs XEf42_eq2); [innth 62 | lia]. Qed.
Lemma XH_XEo42 : ltac2:(tb__ "0|1|
S3S2aS77Q40A1A1M0G0VTR;S73S58VJAv;SfeA1S18eR3R2A5VFAM;S5aS2bS2cS3aS59A2S2cS0S2A2S2bS3aS59S18eSfeA4S2bS0S2Z10Sa2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof. intros. unfold ndEo. apply (X_arr1 XEo42 C_Eo2 objs_Eo42 4 5 tvQ _ rho tp tp0 16 14 63 XEo42_rel XEo42_objs XEo42_eq2); [innth 63 | lia]. Qed.
Lemma XH_XEf6a : ltac2:(tb__ "0|1|
S3S2aS77Q40A1A1M0G0VTR;S73S58VJAv;SfdA1S1a4R3R2A5VFAM;S5aS2bS2cS3aS59A2S2cS0S2A2S2bS3aS59S1a4SfdA4S2bS0S2Z10Sa2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof. intros. unfold ndEf. apply (X_arr2 XEf6a XEf6a1 C_Ef2 objs_Ef6a objs_Ef6a1 28 33 38 39 tvQ _ rho tp tp0 16 14 XEf6a_rel XEf6a_objs XEf6a1_eq XEf6a1_rel XEf6a1_objs XEf6a_eq2); [innth 62 | lia]. Qed.
Lemma XH_XEf6b : ltac2:(tb__ "0|1|
S3S2aS77Q40A1A1M0G0VTR;S73S58VJAv;SfdA1S1a5R3R2A5VFAM;S5aS2bS2cS3aS59A2S2cS0S2A2S2bS3aS59S1a5SfdA4S2bS0S2Z10Sa2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof. intros. unfold ndEf. apply (X_arr2 XEf6b XEf6b1 C_Ef2 objs_Ef6b objs_Ef6b1 38 39 28 33 tvQ _ rho tp tp0 16 14 XEf6b_rel XEf6b_objs XEf6b1_eq XEf6b1_rel XEf6b1_objs XEf6b_eq2); [innth 62 | lia]. Qed.
Lemma XH_XEo6 : ltac2:(tb__ "0|1|
S3S2aS77Q40A1A1M0G0VTR;S73S58VJAv;SfeA1S1a6R3R2A5VFAM;S5aS2bS2cS3aS59A2S2cS0S2A2S2bS3aS59S1a6SfeA4S2bS0S2Z10Sa2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof. intros. unfold ndEo. apply (X_arr2 XEo6 XEo61 C_Eo2 objs_Eo6 objs_Eo61 38 39 28 33 tvQ _ rho tp tp0 16 14 XEo6_rel XEo6_objs XEo61_eq XEo61_rel XEo61_objs XEo6_eq2); [innth 63 | lia]. Qed.

Lemma ccount_FFx3 : ltac2:(tb__ "0|3|
S3S0S28S24S0R1Z3A3A1S24S32S172R2S7aS2cS2cS0S0A2M0S0A2M1G0S37G0S0A2M2S167VFF;R3S7dA3A4A2S172R2S7aG1G0G2VFF;A4A2A3F_;Fc;Frho;").
Proof.
  intros rho c Hc. unfold FFx, fr_hf. cbn [map app]. rewrite map_app. cbn [map fst frv snd]. unfold ccount. rewrite filter_app. cbn [List.filter].
  unfold is_cls at 2. cbn [snd]. replace (fs_frame_size 3 =? fs_frame_size c) with false.
  - cbn. rewrite app_nil_r. reflexivity.
  - symmetry. apply Z.eqb_neq. unfold fs_frame_size. intros E. destruct (Z.leb_spec 0 c) as [H0|H0].
    + rewrite !Z.shiftl_mul_pow2 in E by lia. assert (E2 : 2 ^ c = 2 ^ 3) by nia. apply Z.pow_inj_r in E2; lia.
    + rewrite (Z.shiftl_mul_pow2 64 3) in E by lia. rewrite (Z.shiftl_div_pow2 64 c) in E by lia.
      pose proof (Z.pow_pos_nonneg 2 (- c) ltac:(lia) ltac:(lia)) as HP.
      assert (HD : 64 / 2 ^ (- c) <= 64) by (apply Z.div_le_upper_bound; nia). change (2 ^ 3) with 8 in E. lia.
Qed.

Lemma pg_call_chkF_unf : pg_call_chkF XGL = ltac:(let t := eval unfold pg_call_chkF in (pg_call_chkF XGL) in exact t).
Proof. let t := eval unfold pg_call_chkF in (pg_call_chkF XGL) in exact (@eq_refl bool t). Qed.

Lemma CPGF : ltac2:(tb__ "0|1|
S2aS2cS0S0A2M0A1S2aS2cG0S0A2A1S4aS3S2aS77Q40A1A1S49Z5R3A2VTR;S73S58S62VAInv;VCST;VXGL;VKc;S14bR6R5A2R6R5R4S5dS160AaS159R3R2A5Sb9S58Sd4R3R2S168VAInv;VCST;VXGL;VKc;S14bS5dS158R6R5R4AaA5A2F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Proof.
  intros FBc FFc BXc rho1 tp1 HB0.
  pose proof Pre_pgS_chk as C. peel C HFb. peel C HFs. peel C HSs. rename C into HSb.
  apply (TR_pureP _ (Forall (holds rho1) F_pg)).
  { intros w Hw. exact (facts_sub_holds rho1 _ _ HFs (SPA_facts_hold segs _ rho1 Pre_pgF tp1 w Hw)). }
  intros HFp.
  apply (TR_post _ (LQPA segs NF rho1 tp1 (PostsC AInv CST XGL Kc PGP.P0_pg PTrue PD_pg FBc FFc BXc))).
  { intros w (L & JL & rho' & tp' & Hin & Hag & Hsm & HJL).
    assert (HFp' : Forall (holds rho') F_pg).
    { apply Forall_forall. intros p Hp. apply (proj1 (holds_agree_vals NF rho1 rho' p Hag (proj1 (forallb_forall _ _) HFb p Hp))).
      exact (proj1 (Forall_forall _ _) HFp p Hp). }
    pose proof P_F_below as PB. peel PB PBi.
    cbn [PostsC PD_pg map In fst snd] in Hin. destruct Hin as [E|[E|[]]]; injection E as <- <-.
    - exists P_invF, (JLA AInv CST XGL Kc (PGP.P0_pg FBc FFc) FBc FFc BXc PTrue PGC.nd0), rho', tp'.
      split; [left; reflexivity|]. split; [exact Hag|]. split; [|exact HJL].
      rewrite <- P_invF_eq.
      exact (proj1 (SPA_refacts segs (fun _ _ _ _ => True) rho' PG.P_inv _ tp' w (conj Hsm I) PBi (fun HF => proj2 (Forall_app _ _ _) (conj HFp' HF)))).
    - exists P_okF, (JLA AInv CST XGL Kc (PGP.P0_pg FBc FFc) FBc FFc BXc PTrue PGC.nd0), rho', tp'.
      split; [right; left; reflexivity|]. split; [exact Hag|]. split; [|exact HJL].
      rewrite <- P_okF_eq.
      exact (proj1 (SPA_refacts segs (fun _ _ _ _ => True) rho' PG.P_ok _ tp' w (conj Hsm I) PB (fun HF => proj2 (Forall_app _ _ _) (conj HFp' HF)))). }
  eapply TR_pre; [|exact (CPG FBc FFc BXc rho1 tp1 HB0)].
  intros w Hw. apply (SPA_axforms segs _ [AXMerge 3] rho1 Pre_pgS PG.Pre_pg tp1 w Pre_pg_merge).
  rewrite <- Pre_pgS_drop. apply (SPA_refacts segs _ rho1 Pre_pgF _ tp1 w Hw HSb). intros HF. exact (facts_sub_holds rho1 _ _ HSs HF).
Qed.

Lemma pg_F_ok : ltac2:(tb__ "0|0|
S3S2aS4A1S79S4S6R2A1R1A3S24S2dS196R2A1S2eA3S24S2dS15cR3A1S2eA3S79S4S6R5A1S15aA3F_;F_;F_;FF;Frho;").
Proof.
  intros rho F HF CP CE.
  destruct (pg_vals rho F HF CP) as (VA & VD & V3 & VK & VT3 & VKT & VN).
  unfold pgEF in CE. rdF HF CE FKts. rdF HF CE Fhf. rdF HF CE Ftr. rdF HF CE Frp. rdF HF CE Ftop. rdF HF CE Efr. rdF HF CE Ets. rdF HF CE Etr. pose proof (holds_mem _ _ _ HF CE) as Erp.
  rewrite h_ule in FKts, Fhf, Ftr, Frp, Ftop, Efr, Ets, Etr, Erp. unfold B32 in *.
  rewrite uval_lit in FKts by lia. rewrite uval_lit in Fhf by lia. rewrite uval_lit in Ftr by lia. rewrite uval_lit in Frp by lia. rewrite uval_lit in Ftop by lia.
  set (T := uval rho (SVar 30)) in *.
  pose proof (uval_range rho pDrp) as R1. pose proof (uval_range rho pDtr) as R2. pose proof (uval_range rho pDts) as R3. pose proof (uval_range rho hF) as R4.
  pose proof (uval_range rho pKrp) as R5. pose proof (uval_range rho pKtr) as R6. pose proof (uval_range rho pKts) as R7.
  assert (EKrp : uval rho (kb 4 pKrp) = 4 * uval rho pKrp) by (apply uval_kb; lia).
  assert (EKtr : uval rho (kb 4 pKtr) = 4 * uval rho pKtr) by (apply uval_kb; lia).
  assert (EKts : uval rho (kb 1 pKts) = uval rho pKts) by (rewrite uval_kb by lia; lia).
  rewrite uval_add_small in Erp by (rewrite EKrp; lia). rewrite uval_add_small in Etr by (rewrite EKtr; lia). rewrite uval_add_small in Ets by (rewrite EKts; lia).
  rewrite uval_add_litZ in Efr by lia. rewrite EKrp in Erp. rewrite EKtr in Etr. rewrite EKts in Ets.
  assert (E3a : uval rho (kb 3 pA) = 3 * uval rho pA) by (apply uval_kb; lia).
  assert (Eam : uval rho am2 = uval rho pA - 2) by (unfold am2; apply uval_add_neglit; lia).
  assert (E3t : uval rho (kb 3 am2) = 3 * (uval rho pA - 2)) by (rewrite <- Eam; apply uval_kb; rewrite ?Eam; lia).
  assert (E12a : uval rho (SMd M_MUL pA (SLit 12)) = 12 * uval rho pA) by (apply uval_mulc; lia).
  assert (E12t : uval rho (SMd M_MUL am2 (SLit 12)) = 12 * (uval rho pA - 2)) by (rewrite <- Eam; apply uval_mulc; rewrite ?Eam; lia).
  set (a := uval rho pA) in *. set (d := uval rho pDts) in *.
  pose proof (V_o16A rho VA) as O16. pose proof (V_o4A rho VA) as O4. pose proof (V_a16 rho VA) as A16. pose proof (V_orfx rho VA) as ORF.
  pose proof (V_pNXT rho VA VD) as PN. pose proof (V_pPRV rho VA VD) as PP. pose proof (V_pRFX rho VA VD) as PR. pose proof (V_needA rho VA) as NA.
  pose proof (V_x16 rho VA) as [X16 _]. pose proof (V_r8 rho VA) as R8.
  fold a in O16, O4, A16, ORF, PN, PP, PR, NA, X16, R8. fold d in PN, PP, PR.
  set (x16 := 4 * a + 15 - (4 * a + 15) mod 16) in *. set (r8 := (a + 7) / 8) in *.
  assert (NB : 16 * a + x16 + x16 + r8 <= uval rho needA).
  { rewrite NA. assert (E32 : (8 * a + 30) mod 32 = 2 * ((4 * a + 15) mod 16)) by (replace (8 * a + 30) with (2 * (4 * a + 15)) by lia; replace 32 with (2 * 16) by lia; apply Z.mul_mod_distr_l; lia).
    pose proof (Z.mod_pos_bound (r8 + 15) 16 ltac:(lia)). subst x16. lia. }
  subst x16 r8. subst a d.
  unfold F_pgC. change (SAlu ALU_ADD (SVar 350) (SAlu ALU_SLL (SVar 418) (SLit 4))) with AR.pNXT'.
  change (SAlu ALU_SLL (SVar 418) (SLit 4)) with AR.o16A. change (SAlu ALU_SLL (SVar 418) (SLit 2)) with AR.o4A.
  change (SAlu ALU_SRL (SAlu ALU_ADD (SVar 418) (SLit 7)) (SLit 3)) with AR.orfx.
  change (SAlu ALU_AND (SAlu ALU_ADD AR.o4A (SLit 15)) (SLit 18446744073709551600)) with AR.a16.
  change (SAlu ALU_ADD AR.pNXT' AR.a16) with AR.pPRV'. change (SAlu ALU_ADD AR.pPRV' AR.a16) with AR.pRFX'.
  change (SVar 160) with hF. change (SVar 346) with pDrp. change (SVar 343) with pDtr. change (SVar 350) with pDts. change (SVar 418) with pA.
  change (SAlu ALU_ADD pA (SLit (-2))) with am2.
  repeat (apply Forall_cons; [rewrite h_ule; rewrite ?(uval_lit rho 140737488355328) by lia; rewrite ?(uval_lit rho 1099511627776) by lia; rewrite ?(uval_lit rho 72) by lia|]); [..|constructor].
  all: try (rewrite uval_add_litZ by lia; lia).
  all: try (rewrite uval_add_small by (rewrite ?E12a, ?E12t, ?PN, ?PP, ?PR, ?O16, ?O4, ?ORF; lia); rewrite ?E12a, ?E12t, ?PN, ?PP, ?PR, ?O16, ?O4, ?ORF; lia).
  all: rewrite ?E12a, ?E12t, ?PN, ?PP, ?PR, ?O16, ?O4, ?ORF; lia.
Qed.

Lemma HIN_pg : ltac2:(tb__ "0|1|
S3Se5Sc2S3S2aS77Q40A1A1Sc0S79S4S6R6A1S9S3bS156A1A1A3Sb2VCST;VFB;VFF;Vrho0;A4SccS95Vrho0;R8A3VAInv;R7R6R5R4A4S63Vrho0;R8A2S10bRbSc4Sc3R9A1A1A2S67VFB;RaA2S68VFF;RbA2S60VFB;RcReS5eSa5A1M0A4S10aRfG0A2S109R10G0A2S64VFF;RfR11S7dA4S25S16fVCST;Vrho0;VFB;VFF;R12G0S7dS157A8S25S170VCST;VXGL;Vrho0;VFB;VFF;R12G0S7dSd0A9S14bS10cVFB;R12G0A3S167VFF;R12S7dA3Sd9SdaR12S157R11A3ScfA2A3A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FAi;Fms;Frho;").
Proof.
  intros rho ms Ai rho1 tp1 md1 HF HP0 Hav HM HTP HTK HBf HFF HN HD HZ HFR. destruct (P0_now rho Hav HP0) as (_ & _ & _ & _ & HC6).
  pose proof (pg_chkF XGL) as C. rewrite pg_call_chkF_unf in C.
  peel C HP0F. peel C Hs18. peel C Hs17. peel C Hs16. peel C Hs15. peel C Hs14. peel C Hs13. peel C Hs12. peel C HX. peel C HR. peel C HB. clear C.
  apply sv_eqb_sound in Hs12. apply sv_eqb_sound in Hs13. apply sv_eqb_sound in Hs14. apply sv_eqb_sound in Hs15. apply sv_eqb_sound in Hs16. apply sv_eqb_sound in Hs17. apply sv_eqb_sound in Hs18.
  pose proof (basez_of DW rho _ DW_rng HF HB) as BZ.
  unfold pg0F in HP0F. peel HP0F Gtr. peel HP0F Grp. peel HP0F Lts. peel HP0F Ltr. peel HP0F Lrp. rename HP0F into HfF.
  pose proof (holds_mem _ _ _ HF Lrp) as Frp. pose proof (holds_mem _ _ _ HF Ltr) as Ftr. pose proof (holds_mem _ _ _ HF Lts) as Fts.
  pose proof (holds_mem _ _ _ HF Grp) as Crp. pose proof (holds_mem _ _ _ HF Gtr) as Ctr.
  rewrite h_ule in Frp, Ftr, Fts, Crp, Ctr. unfold IMG_HI in Frp, Ftr, Fts. rewrite uval_lit in Frp by lia. rewrite uval_lit in Ftr by lia. rewrite uval_lit in Fts by lia.
  destruct (pg_vals rho _ HF pgF_callF) as (VA & VD & V3 & VK & VT3 & VKT & VN).
  split; [|split].
  - intros o a Ho Hr. eapply (robjs_checkP_sound segs AInv CST ALA rho0 FB FF Ai rho _ (nd_tv ndTS) fr_hf None extraOH R_pgF rho1 tp1 md1 HM HF (T_ok_T0 rho0 _ Ai HTP HTK) HN HD HZ HFR HR);
      [intros o' a' Ho' HE Hr'; exact (extra_client rho o' a' _ _ BZ Hav HP0 HE Hr') | exact Ho | exact Hr].
  - exact (proj1 (siteX Ai rho _ (nd_tv ndTS) fr_hf None (ss_objs (ax_S E_pgF)) Xk_pg rho1 tp1 md1 HM HF HB Hav HP0 HTP HTK HBf HFF HN HD HZ HFR HX)).
  - unfold PGP.P0_pg. rewrite !rw_call', Hs12, Hs13, Hs14, Hs15, Hs16, Hs17, Hs18.
    change (bv_unsigned (eval rho (xfo 48))) with (uval rho (xfo 48)). change (bv_unsigned (eval rho (xfo 160))) with (uval rho (xfo 160)).
    change (bv_unsigned (eval rho pA)) with (uval rho pA). change (bv_unsigned (eval rho pDrp)) with (uval rho pDrp). change (bv_unsigned (eval rho pDtr)) with (uval rho pDtr).
    change (bv_unsigned (eval rho pDts)) with (uval rho pDts). change (bv_unsigned (eval rho needA)) with (uval rho needA).
    assert (E48 : uval rho (xfo 48) = uval rho hF + 48) by (unfold xfo; exact (foff_rng rho _ 48 HF HfF ltac:(lia))).
    assert (E160 : uval rho (xfo 160) = uval rho hF + 160) by (unfold xfo; exact (foff_rng rho _ 160 HF HfF ltac:(lia))).
    assert (InF : In (uval rho hF, 512, uval rho hFL) (FFx FF rho fr_hf)).
    { apply In_FFx. right. exists (hF, 3, hFL). split; [left; reflexivity | reflexivity]. }
    assert (Erp : uval rho (kb 4 pKrp) = 4 * uval rho pKrp) by (apply uval_kb; unfold B32 in VK; lia).
    assert (Etr : uval rho (kb 4 pKtr) = 4 * uval rho pKtr) by (apply uval_kb; unfold B32 in VKT; lia).
    assert (E3a : uval rho (kb 3 pA) = 3 * uval rho pA) by (apply uval_kb; lia).
    assert (Eam : uval rho am2 = uval rho pA - 2) by (unfold am2; apply uval_add_neglit; lia).
    assert (E3t : uval rho (kb 3 am2) = 3 * (uval rho pA - 2)) by (rewrite <- Eam; apply uval_kb; rewrite ?Eam; lia).
    assert (InB : forall d k, In (d, k) (nd_tv ndTS) -> uval rho d <> 0 -> In (uval rho d, uval rho k) (FBx FB rho (nd_tv ndTS))).
    { intros d k Hin Hnz. apply In_FBx. right. exists (d, k). split; [exact Hin|]. split; [|reflexivity]. unfold tnz. cbn [fst]. unfold uval in Hnz. exact Hnz. }
    split; [rewrite (ccount_FFx3 rho 6 ltac:(lia)); exact HC6|].
    split; [exists (uval rho hF), 512, (uval rho hFL); split; [exact InF | rewrite E48; lia]|].
    split; [exists (uval rho hF), 512, (uval rho hFL); split; [exact InF | rewrite E160; lia]|].
    split; [exists (uval rho pDrp), (uval rho (kb 4 pKrp)); split; [apply InB; [cbn; tauto | lia] | rewrite Erp; lia]|].
    split; [exists (uval rho pDtr), (uval rho (kb 4 pKtr)); split; [apply InB; [cbn; tauto | lia] | rewrite Etr; lia]|].
    exists (uval rho pDts), (uval rho (kb 1 pKts)); split; [apply InB; [cbn; tauto | lia] | rewrite uval_kb by (pose proof (uval_range rho pKts); lia); lia].
Qed.

Lemma XH_E_pg0 : ltac2:(tb__ "0|1|
S3S2aS77Q40A1A1M0G0VTR;S73S58VJAv;Sa5A1Sd2R3R2A5VFAM;S5aS2bS2cS3aS59A2S2cS0S2A2S2bS3aS59Sd2Sa5A4S2bS0S2Z33Sa2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. rewrite emeas_z0. change (JAv ndTS) with (JAv (NDA (nd_tv ndTS) fr_hf (nd_bd ndTS) ANone)).

  apply (TR_absorb _ E_pg0r (NDA (nd_tv ndTS) fr_hf (nd_bd ndTS) ANone) rho tp).
  { intros tr ms md Hw. exists (rho_absorb rho [shobj hG 20 23 cells_pg DUnknown] (vms md tp ms)). split; [intros ee; apply eval_absorb|].
    rewrite <- E_pg0r_eq. exact (release_imp E_pg0 (objs_butlast E_pg0) 20 23 cells_pg DUnknown [(160, 24)] _ _ rho tp tr ms md pg_rel pg_robjs Hw). }
  intros rho1 _. clear rho. rename rho1 into rho.

  pose proof pg_wf43 as W43. peel W43 F43. pose proof pg_wf45 as W45. peel W45 F45. pose proof pg_wf47 as W47. peel W47 F47.
  pose proof pgx_rfx as X1. peel X1 X1b. pose proof pgx_prv as X2. peel X2 X2b. pose proof pgx_nxt as X3. peel X3 X3b.
  pose proof pgx_p2d as X4. peel X4 X4b. pose proof pgx_out as X5. peel X5 X5b. pose proof pgx_pts as X6. peel X6 X6b.
  eapply TR_pre with (P := SPA segs (JAv (NDA (nd_tv ndTS) fr_hf (nd_bd ndTS) ANone)) E_pg rho tp).
  { intros w Hw. unfold E_pg, X_sub. cbn [app].
    apply (publish_sub_imp _ (ax_setX E_pg4 (xOUT :: xP2D :: xNXT :: xPRV :: xRFX :: ax_X E_pg4)) pDrp (kb 4 pKrp) _ _ rho tp w X6 X6b);
      [intros HF HB8; destruct (pg_vals rho _ HF pg_pgF4) as (VA & VD & V3 & VK & VT3 & VKT & VN); exact (xsub_pts rho VA V3 VK HB8)|].
    apply (publish_sub_imp _ (ax_setX E_pg4 (xP2D :: xNXT :: xPRV :: xRFX :: ax_X E_pg4)) pDtr (kb 4 pKtr) _ _ rho tp w X5 X5b);
      [intros HF HB8; destruct (pg_vals rho _ HF pg_pgF4) as (VA & VD & V3 & VK & VT3 & VKT & VN); exact (xsub_out rho VA VT3 VKT HB8)|].
    apply (publish_sub_imp _ (ax_setX E_pg4 (xNXT :: xPRV :: xRFX :: ax_X E_pg4)) pDts (kb 1 pKts) _ _ rho tp w X4 X4b);
      [intros HF HB8; destruct (pg_vals rho _ HF pg_pgF4) as (VA & VD & V3 & VK & VT3 & VKT & VN); exact (xsub_p2d rho VA VN HB8)|].
    apply (publish_sub_imp _ (ax_setX E_pg4 (xPRV :: xRFX :: ax_X E_pg4)) pDts (kb 1 pKts) _ _ rho tp w X3 X3b);
      [intros HF HB8; destruct (pg_vals rho _ HF pg_pgF4) as (VA & VD & V3 & VK & VT3 & VKT & VN); exact (xsub_nxt rho VA VD VN HB8)|].
    apply (publish_sub_imp _ (ax_setX E_pg4 (xRFX :: ax_X E_pg4)) pDts (kb 1 pKts) _ _ rho tp w X2 X2b);
      [intros HF HB8; destruct (pg_vals rho _ HF pg_pgF4) as (VA & VD & V3 & VK & VT3 & VKT & VN); exact (xsub_prv rho VA VD VN HB8)|].
    apply (publish_sub_imp _ E_pg4 pDts (kb 1 pKts) _ _ rho tp w X1 X1b);
      [intros HF HB8; destruct (pg_vals rho _ HF pg_pgF4) as (VA & VD & V3 & VK & VT3 & VKT & VN); exact (xsub_rfx rho VA VD VN HB8)|].
    rewrite <- E_pg4_eq2. apply (reshape_gen _ E_pg3b 47 O_rfx O_rfx' rho tp w pg_o47 eq_refl eq_refl eq_refl W47);
      [intros HF; destruct (pg_vals rho _ HF F47) as (VA & VD & _); exact (rfx_eqs_f rho VA VD)|].
    rewrite <- E_pg3b_eq. apply (reshape_gen _ E_pg3a 45 O_prv O_prv' rho tp w pg_o45 eq_refl eq_refl eq_refl W45);
      [intros HF; destruct (pg_vals rho _ HF F45) as (VA & VD & _); exact (prv_eqs_f rho VA VD)|].
    rewrite <- E_pg3a_eq. apply (reshape_gen _ E_pg3 43 O_nxt O_nxt' rho tp w pg_o43 eq_refl eq_refl eq_refl W43);
      [intros HF; destruct (pg_vals rho _ HF F43) as (VA & VD & _); exact (nxt_eqs_f rho VA VD)|].
    apply (SPA_axforms segs _ xf_pg2 rho E_pg2 E_pg3 tp w E_pg3_eq). apply (SPA_axforms segs _ xf_pg1 rho E_pg1 E_pg2 tp w E_pg2_eq).
    apply (facts_imp _ E_pg0r E_pg1 AR.ts_facts rho tp w E_pg1_eq2 pg_xff); [|exact Hw].
    intros tr md _ HF1. pose proof pg_tsF as TF. peel TF TN. exact (AR.ts_facts_ok rho (triA_vals rho _ HF1 TF) (holds_mem _ _ _ HF1 TN)). }

  eapply TR_pre with (P := SPA segs (JAv (NDA (nd_tv ndTS) fr_hf (nd_bd ndTS) ANone)) E_pgF rho tp).
  { intros w Hw. apply (facts_imp _ E_pgS E_pgF F_pgC rho tp w E_pgF_eq pgF_xff); [|exact (SPA_axforms segs _ [AXSplit 5 (SLit 16)] rho E_pg E_pgS tp w E_pgS_eq Hw)].
    intros tr md _ HF1. pose proof pgF_site as CS. peel CS CE. exact (pg_F_ok rho _ HF1 CS CE). }

  pose proof (pg_chkF XGL) as C. rewrite pg_call_chkF_unf in C.
  peel C HP0F. peel C Hs18. peel C Hs17. peel C Hs16. peel C Hs15. peel C Hs14. peel C Hs13. peel C Hs12. peel C HX. peel C HR. peel C HB. peel C Hpd. peel C Hwp. peel C Hbb. peel C Hnb. peel C Hnp. peel C Hdom. peel C Hta. peel C Hchk. rename C into HXk.
  rewrite <- (app_nil_r (nd_tv ndTS)). apply TR_facts. intros HF.
  apply (client_callT segs AInv CST XGL ALA HCST HXGL NPH Kc rho0 (P0_hf CST FB FF) FB FF BX PTrue HKc HBX PGP.P0_pg PTrue (fun _ H => H) (fun _ _ _ H => H)
           Pre_pgF PGC.nd0 PD_pgF NF eq_refl eq_refl eq_refl TR TR_facts TR_ex TR_pre TR_callP CPGF eq_refl
           E_pgF s_pg R_pgF Xk_pg rho tp (nd_tv ndTS) [] fr_hf (nd_bd ndTS) (nd_bd ndTS) ANone _ HXk R_pgF_eq Hchk Hta Hdom Hnp Hnb Hbb eq_refl eq_refl).
  - cbn [nd_bd PGC.nd0 bd_subst map app]. apply payA_same. exact Hwp.
  - exact Hpd.
  - intros Ai ms HF' HP0 Hav HBf HFF HN HD HZ HFR (rho1 & tp1 & md1 & HM) HT HTK'. rewrite app_nil_r in HN, HD, HZ.
    exact (HIN_pg rho ms Ai rho1 tp1 md1 HF' HP0 Hav HM HT HTK' HBf HFF HN HD HZ HFR).
  - pose proof T_pg0_chk as TC. peel TC TCis. peel TC TCib. peel TC TCos. rename TC into TCob.
    intros [Ld ndL] rho' tp' Hd Hag. cbn [PD_pgF In] in Hd. destruct Hd as [Hd|[Hd|[]]]; injection Hd as <- <-;
      cbn [fst snd nd_tv nd_bd nd_am PGC.nd0 import_tv bd_subst map app am_subst]; rewrite app_nil_r.
    +
      pose proof pgi_wf8 as W8. peel W8 Fw8. pose proof pgi_wf9 as W9. peel W9 Fw9. pose proof pgi_wf10 as W10. peel W10 Fw10.
      eapply TR_pre; [|apply (REENTER T_pgiR ndTS (50, z0) rho'); [innth 45 | rewrite !emeas_z0; lia]].
      intros w Hw. change (JAv ndTS) with (JAv (NDA (nd_tv ndTS) fr_hf (nd_bd ndTS) ANone)).
      rewrite <- T_pgiR_eq2. apply (reopenS_imp T_pgiR1 XT (nd_tv ndTS) _ 20 23 rho' tp' w (pgi_ro2 XGL)).
      rewrite <- T_pgiR1_eq. apply (reopen_imp T_pgi XT (nd_tv ndTS) _ 6 15 rho' tp' w (pgi_ro1 XGL)).
      apply (subX_imp _ T_pgi4 T_pgi XT6 rho' tp' w T_pgi_eq2 pgi_xsub). apply (SPA_axforms segs _ xf_pgb2 rho' T_pgi3 T_pgi4 tp' w T_pgi4_eq).
      rewrite <- T_pgi3_eq2. apply (SPA_arr_merge segs _ rho' T_pgi2 34 (ax_S T_pgi3) tp' w T_pgi3_am). apply (SPA_axforms segs _ xf_pgb1 rho' T_pgi1 T_pgi2 tp' w T_pgi2_eq).
      rewrite <- T_pgi1_eq2. apply (SPA_zero_cells segs _ rho' T_pgic 3 cs_pgi (ax_S T_pgi1) tp' w T_pgi1_zc T_pgi1_wf).
      rewrite <- T_pgic_eq2. apply (reshape_gen _ T_pgib 10 O_rfx1 O_rfx0 rho' tp' w pgi_o10 eq_refl eq_refl eq_refl W10);
        [intros HF2; destruct (pg_vals rho' _ HF2 Fw10) as (VA & VD & _); pose proof (rfx_eqs_f rho' VA VD) as [E1 E2]; split; [symmetry; exact E1 | symmetry; exact E2]|].
      rewrite <- T_pgib_eq. apply (reshape_gen _ T_pgia 9 O_prv1 O_prv0 rho' tp' w pgi_o9 eq_refl eq_refl eq_refl W9);
        [intros HF2; destruct (pg_vals rho' _ HF2 Fw9) as (VA & VD & _); pose proof (prv_eqs_f rho' VA VD) as [E1 E2]; split; [symmetry; exact E1 | symmetry; exact E2]|].
      rewrite <- T_pgia_eq. apply (reshape_gen _ T_pgi0 8 O_nxt1 O_nxt0 rho' tp' w pgi_o8 eq_refl eq_refl eq_refl W8);
        [intros HF2; destruct (pg_vals rho' _ HF2 Fw8) as (VA & VD & _); pose proof (nxt_eqs_f rho' VA VD) as [E1 E2]; split; [symmetry; exact E1 | symmetry; exact E2]|].
      rewrite <- T_pgi0_drop. apply (SPA_refacts segs _ rho' T_pgi0F _ tp' w); [rewrite <- T_pgi0F_ta; exact Hw | exact TCib | intros HF3; exact (facts_sub_holds rho' _ _ TCis HF3)].
    +
      pose proof pgo_wf8 as W8. peel W8 Fw8. pose proof pgo_wf9 as W9. peel W9 Fw9. pose proof pgo_wf10 as W10. peel W10 Fw10.
      eapply TR_pre; [|apply (REENTER T_pgoR ndTS (50, z0) rho'); [innth 44 | rewrite !emeas_z0; lia]].
      intros w Hw. change (JAv ndTS) with (JAv (NDA (nd_tv ndTS) fr_hf (nd_bd ndTS) ANone)).
      rewrite <- T_pgoR_eq2. apply (reopenS_imp T_pgoR1 XT (nd_tv ndTS) _ 20 23 rho' tp' w (pgo_ro2 XGL)).
      rewrite <- T_pgoR1_eq. apply (reopen_imp T_pgo XT (nd_tv ndTS) _ 6 15 rho' tp' w (pgo_ro1 XGL)).
      apply (subX_imp _ T_pgo4 T_pgo XT6 rho' tp' w T_pgo_eq2 pgo_xsub). apply (SPA_axforms segs _ xf_pgb2 rho' T_pgo3 T_pgo4 tp' w T_pgo4_eq).
      rewrite <- T_pgo3_eq2. apply (SPA_arr_merge segs _ rho' T_pgo2 34 (ax_S T_pgo3) tp' w T_pgo3_am). apply (SPA_axforms segs _ xf_pgb1 rho' T_pgo1 T_pgo2 tp' w T_pgo2_eq).
      rewrite <- T_pgo1_eq2. apply (reshape_gen _ T_pgob 10 O_rfx1 O_rfx0 rho' tp' w pgo_o10 eq_refl eq_refl eq_refl W10);
        [intros HF2; destruct (pg_vals rho' _ HF2 Fw10) as (VA & VD & _); pose proof (rfx_eqs_f rho' VA VD) as [E1 E2]; split; [symmetry; exact E1 | symmetry; exact E2]|].
      rewrite <- T_pgob_eq. apply (reshape_gen _ T_pgoa 9 O_prv1 O_prv0 rho' tp' w pgo_o9 eq_refl eq_refl eq_refl W9);
        [intros HF2; destruct (pg_vals rho' _ HF2 Fw9) as (VA & VD & _); pose proof (prv_eqs_f rho' VA VD) as [E1 E2]; split; [symmetry; exact E1 | symmetry; exact E2]|].
      rewrite <- T_pgoa_eq. apply (reshape_gen _ T_pgo0 8 O_nxt1 O_nxt0 rho' tp' w pgo_o8 eq_refl eq_refl eq_refl W8);
        [intros HF2; destruct (pg_vals rho' _ HF2 Fw8) as (VA & VD & _); pose proof (nxt_eqs_f rho' VA VD) as [E1 E2]; split; [symmetry; exact E1 | symmetry; exact E2]|].
      rewrite <- T_pgo0_drop. apply (SPA_refacts segs _ rho' T_pgo0F _ tp' w); [rewrite <- T_pgo0F_ta; exact Hw | exact TCob | intros HF3; exact (facts_sub_holds rho' _ _ TCos HF3)].
Qed.

Lemma XH_E_g1_0 : ltac2:(tb__ "0|1|
S3S2aS77Q40A1A1M0G0VTR;S73S58VJAv;Sa3A1S11eR3R2A5VFAM;S5aS2bS2cS3aS59A2S2cS0S2A2S2bS3aS59S11eSa3A4S2bS0S2Z28Sa4Z3bA1A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_facts. intros HF0. pose proof (vlF_bound rho _ HF0 g1_vlF) as VB. pose proof g1_meas as CM. peel CM MbL. rename CM into MbN.
  change (JAv ndLL) with (JAv (NDA (nd_tv ndLL) fr_hf (nd_bd ndLL) ANone)).
  apply (TR_absorb _ E_g1_1x (NDA (nd_tv ndLL) fr_hf (nd_bd ndLL) ANone) rho tp).
  { intros tr ms md Hw. exists (rho_absorb rho [shobj hG 38 39 cells_g1b DUnknown] (vms md tp ms)). split; [intros ee; apply eval_absorb|].
    rewrite <- E_g1_1x_eq. exact (release0_imp E_g1_0 (objs_butlast E_g1_0) 38 39 cells_g1b DUnknown _ _ rho tp tr ms md g1_rel1 g1_robjs1 Hw). }
  intros rho1 HE1. rewrite <- (emeas_eq E_g1_0 ndLL 40 (VL 59) rho rho1 HE1).
  assert (VB1 : uval rho1 pL <= uval rho1 pNT <= 2 ^ 40) by (unfold uval; rewrite !HE1; exact VB). clear VB HE1. rename VB1 into VB.
  apply (TR_absorb _ E_g1_3 (NDA (nd_tv ndLL) fr_hf (nd_bd ndLL) ANone) rho1 tp).
  { intros tr ms md Hw. exists (rho_absorb rho1 [shobj hG 28 33 cells_g1a DUnknown] (vms md tp ms)). split; [intros ee; apply eval_absorb|].
    rewrite <- E_g1_3x_eq. exact (release_imp E_g1_1x (objs_butlast E_g1_1x) 28 33 cells_g1a DUnknown [(224, 36)] _ _ rho1 tp tr ms md g1_rel2 g1_robjs2 Hw). }
  intros rho2 HE2. rewrite <- (emeas_eq E_g1_0 ndLL 40 (VL 59) rho1 rho2 HE2).
  assert (VB2 : uval rho2 pL <= uval rho2 pNT <= 2 ^ 40) by (unfold uval; rewrite !HE2; exact VB). clear VB HE2. rename VB2 into VB. rename rho into rho00. rename rho2 into rho.
  pose proof g1_wf2 as W2. peel W2 W2f. pose proof g1_twf1 as TW. peel TW TWf.
  eapply TR_pre with (P := SPA segs (JAv (NDA (nd_tv ndLL) fr_hf (nd_bd ndLL) ANone)) E_g1 rho tp).
  { intros w Hw.
    apply (facts_imp _ E_g1c E_g1 (g_need E_g1_3) rho tp w E_g1_eq3 g1_xff);
      [intros tr md _ HF1; rewrite g1_gneed; pose proof g1_gF as GC; peel GC GV; exact (g_need_ok rho _ (SExt false 32 (SVar 481)) HF1 GC (sext_lt rho _ _ (holds_mem _ _ _ HF1 GV)))|].
    rewrite <- E_g1c_eq. apply (reshape_fwd _ E_g1b 35 pDco off_g1 off_g1 12 DUnknown rho tp w g1_oi eq_refl g1_wfi ltac:(lia) (fun r => eq_refl) (fun HF => rs_bnd_gz rho _ pDco (SVar 481) HF g1_bnd)).
    rewrite <- E_g1b_eq. apply (reshape_ffwd _ E_g1a 2 224 236 DUnknown rho tp w g1_o2 eq_refl W2 ltac:(lia) ltac:(lia) W2f).
    exact (SPA_axforms segs _ xf_g1 rho E_g1_3 E_g1a tp w E_g1a_eq Hw). }
  apply (X_purecT XP_memcpy Pre_mc [L_mc1; L_mc1] E_g1 (nd_tv ndLL) (nd_bd ndLL) (s_g E_g1) R_g1 rho tp _ (fun Ai rho1 tp1 => CMEMCPY Ai rho1 tp1)
           (fun Ai tr ms md Hsm HM HX => XP_memcpy_site segs AInv CST XGL ALA HCST HXGL Ai E_g1 memcpy_pc (s_g E_g1) R_g1 rho tp tr ms md Hsm HM HX R_g1_eq2)
           eq_refl eq_refl R_g1_eq2 (g1_chk XGL)).
  intros L0 rho' tp' HL Hag HF. assert (HL' : L0 = L_mc1) by (destruct HL as [<-|[<-|[]]]; reflexivity). subst L0.
  eapply TR_pre; [|apply (REENTER T_g1 ndLL (40, VL 58) rho'); [innth 49 |
    rewrite !VL_VM; exact (VM_meas_ag E_g1_0 T_g1 ndLL ndLL 40 pNT pL 58 59 rho rho' _ ltac:(lia) VB Hag MbN MbL ltac:(lia) ltac:(lia) ltac:(lia))]].
  intros w Hw. change (JAv ndLL) with (JAv (NDA (nd_tv ndLL) fr_hf (nd_bd ndLL) ANone)).
  apply (SPA_axforms segs _ _ rho' T_g1v T_g1 tp' w T_g1_eq2).
  rewrite <- T_g1v_eq. apply (reshape_bwd _ T_g1u 2 pDco off_g1 off_g1 12 DUnknown rho' tp' w g1_to2 eq_refl g1_twf2 ltac:(lia) (fun r => eq_refl) (fun HF => rs_bnd_gz rho' _ pDco (SVar 481) HF g1_tbnd)).
  rewrite <- T_g1u_eq. apply (reshape_fbwd _ T_g1t 1 224 236 DUnknown rho' tp' w g1_to1 eq_refl TW ltac:(lia) ltac:(lia) TWf).
  rewrite <- T_g1t_eq. exact Hw.
Qed.

Lemma XH_E_g2_0 : ltac2:(tb__ "0|1|
S3S2aS77Q40A1A1M0G0VTR;S73S58VJAv;Sa3A1S11fR3R2A5VFAM;S5aS2bS2cS3aS59A2S2cS0S2A2S2bS3aS59S11fSa3A4S2bS0S2Z28Sa4Z39A1A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_facts. intros HF0. pose proof (vlF_bound rho _ HF0 g2_vlF) as VB. pose proof g2_meas as CM. peel CM MbL. rename CM into MbN.
  change (JAv ndLL) with (JAv (NDA (nd_tv ndLL) fr_hf (nd_bd ndLL) ANone)).
  pose proof g2_wf2 as W2. peel W2 W2f. pose proof g2_twf1 as TW. peel TW TWf.
  eapply TR_pre with (P := SPA segs (JAv (NDA (nd_tv ndLL) fr_hf (nd_bd ndLL) ANone)) E_g2 rho tp).
  { intros w Hw.
    apply (facts_imp _ E_g2c E_g2 (g_need E_g2_0) rho tp w E_g2_eq3 g2_xff);
      [intros tr md _ HF1; rewrite g2_gneed; pose proof g2_gF as GC; peel GC GV; exact (g_need_ok rho _ (SVar 482) HF1 GC (proj1 (h_ult _ _ _) (holds_mem _ _ _ HF1 GV)))|].
    rewrite <- E_g2c_eq. apply (reshape_fwd _ E_g2b 35 pDco off_g2 off_g2 12 DUnknown rho tp w g2_oi eq_refl g2_wfi ltac:(lia) (fun r => eq_refl) (fun HF => rs_bnd_gv rho _ pDco (SVar 482) HF g2_bnd)).
    rewrite <- E_g2b_eq. apply (reshape_ffwd _ E_g2a 2 236 248 DUnknown rho tp w g2_o2 eq_refl W2 ltac:(lia) ltac:(lia) W2f).
    exact (SPA_axforms segs _ xf_g2 rho E_g2_0 E_g2a tp w E_g2a_eq Hw). }
  apply (X_purecT XP_memcpy Pre_mc [L_mc1; L_mc1] E_g2 (nd_tv ndLL) (nd_bd ndLL) (s_g E_g2) R_g2 rho tp _ (fun Ai rho1 tp1 => CMEMCPY Ai rho1 tp1)
           (fun Ai tr ms md Hsm HM HX => XP_memcpy_site segs AInv CST XGL ALA HCST HXGL Ai E_g2 memcpy_pc (s_g E_g2) R_g2 rho tp tr ms md Hsm HM HX R_g2_eq2)
           eq_refl eq_refl R_g2_eq2 (g2_chk XGL)).
  intros L0 rho' tp' HL Hag HF. assert (HL' : L0 = L_mc1) by (destruct HL as [<-|[<-|[]]]; reflexivity). subst L0.
  eapply TR_pre; [|apply (REENTER T_g2 ndLL (40, VL 56) rho'); [innth 50 |
    rewrite !VL_VM; exact (VM_meas_ag E_g2_0 T_g2 ndLL ndLL 40 pNT pL 56 57 rho rho' _ ltac:(lia) VB Hag MbN MbL ltac:(lia) ltac:(lia) ltac:(lia))]].
  intros w Hw. change (JAv ndLL) with (JAv (NDA (nd_tv ndLL) fr_hf (nd_bd ndLL) ANone)).
  apply (SPA_axforms segs _ _ rho' T_g2v T_g2 tp' w T_g2_eq2).
  rewrite <- T_g2v_eq. apply (reshape_bwd _ T_g2u 2 pDco off_g2 off_g2 12 DUnknown rho' tp' w g2_to2 eq_refl g2_twf2 ltac:(lia) (fun r => eq_refl) (fun HF => rs_bnd_gv rho' _ pDco (SVar 482) HF g2_tbnd)).
  rewrite <- T_g2u_eq. apply (reshape_fbwd _ T_g2t 1 236 248 DUnknown rho' tp' w g2_to1 eq_refl TW ltac:(lia) ltac:(lia) TWf).
  rewrite <- T_g2t_eq. exact Hw.
Qed.

Lemma XH_E_g3_0 : ltac2:(tb__ "0|1|
S3S2aS77Q40A1A1M0G0VTR;S73S58VJAv;Sa3A1S120R3R2A5VFAM;S5aS2bS2cS3aS59A2S2cS0S2A2S2bS3aS59S120Sa3A4S2bS0S2Z28Sa4Z37A1A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_facts. intros HF0. pose proof (vlF_bound rho _ HF0 g3_vlF) as VB. pose proof g3_meas as CM. peel CM MbL. rename CM into MbN.
  change (JAv ndLL) with (JAv (NDA (nd_tv ndLL) fr_hf (nd_bd ndLL) ANone)).
  pose proof g3_wf2 as W2. peel W2 W2f. pose proof g3_twf1 as TW. peel TW TWf.
  eapply TR_pre with (P := SPA segs (JAv (NDA (nd_tv ndLL) fr_hf (nd_bd ndLL) ANone)) E_g3 rho tp).
  { intros w Hw.
    apply (facts_imp _ E_g3c E_g3 (g_need E_g3_0) rho tp w E_g3_eq3 g3_xff);
      [intros tr md _ HF1; rewrite g3_gneed; pose proof g3_gF as GC; peel GC GV; exact (g_need_ok rho _ (SVar 483) HF1 GC (proj1 (h_ult _ _ _) (holds_mem _ _ _ HF1 GV)))|].
    rewrite <- E_g3c_eq. apply (reshape_fwd _ E_g3b 35 pDco off_g3 off_g3 12 DUnknown rho tp w g3_oi eq_refl g3_wfi ltac:(lia) (fun r => eq_refl) (fun HF => rs_bnd_gv rho _ pDco (SVar 483) HF g3_bnd)).
    rewrite <- E_g3b_eq. apply (reshape_ffwd _ E_g3a 2 248 260 DUnknown rho tp w g3_o2 eq_refl W2 ltac:(lia) ltac:(lia) W2f).
    exact (SPA_axforms segs _ xf_g3 rho E_g3_0 E_g3a tp w E_g3a_eq Hw). }
  apply (X_purecT XP_memcpy Pre_mc [L_mc1; L_mc1] E_g3 (nd_tv ndLL) (nd_bd ndLL) (s_g E_g3) R_g3 rho tp _ (fun Ai rho1 tp1 => CMEMCPY Ai rho1 tp1)
           (fun Ai tr ms md Hsm HM HX => XP_memcpy_site segs AInv CST XGL ALA HCST HXGL Ai E_g3 memcpy_pc (s_g E_g3) R_g3 rho tp tr ms md Hsm HM HX R_g3_eq2)
           eq_refl eq_refl R_g3_eq2 (g3_chk XGL)).
  intros L0 rho' tp' HL Hag HF. assert (HL' : L0 = L_mc1) by (destruct HL as [<-|[<-|[]]]; reflexivity). subst L0.

  apply (TR_pre (fun w => exists bL, (bL = 0 \/ bL = (224 + 36) mod 8)
                   /\ SPA segs (JAv (NDA (nd_tv ndLL) fr_hf (nd_bd ndLL) ANone)) (shadow_reopen_cells_stateA G3back (Xw G3back) hG 28 39 (gcs 224 36 bL)) rho' tp' w)).
  { intros w Hw. change (JAv ndLL) with (JAv (NDA (nd_tv ndLL) fr_hf (nd_bd ndLL) ANone)) in Hw.
    apply (reopenC_imp G3back (Xw G3back) (nd_tv ndLL) _ 28 39 224 36 rho' tp' w (g3_roC XGL)). rewrite <- G3back_eq.
    apply (SPA_axforms segs _ _ rho' T_g3v T_g3w tp' w T_g3w_eq).
    rewrite <- T_g3v_eq. apply (reshape_bwd _ T_g3u 2 pDco off_g3 off_g3 12 DUnknown rho' tp' w g3_to2 eq_refl g3_twf2 ltac:(lia) (fun r => eq_refl) (fun HF => rs_bnd_gv rho' _ pDco (SVar 483) HF g3_tbnd)).
    rewrite <- T_g3u_eq. apply (reshape_fbwd _ T_g3t 1 248 260 DUnknown rho' tp' w g3_to1 eq_refl TW ltac:(lia) ltac:(lia) TWf).
    rewrite <- T_g3t_eq. exact Hw. }
  apply TR_exw. intros bL. apply (TR_pureP _ (bL = 0 \/ bL = (224 + 36) mod 8)); [intros w [HbL _]; exact HbL|]. intros HbL.
  assert (MS : 0 <= emeasA (T_g3_0, ndLL, (40, VL 54)) rho' < emeasA (E_g3_0, ndLL, (40, VL 55)) rho).
  { rewrite !VL_VM. exact (VM_meas_ag E_g3_0 T_g3_0 ndLL ndLL 40 pNT pL 54 55 rho rho' _ ltac:(lia) VB Hag MbN MbL ltac:(lia) ltac:(lia) ltac:(lia)). }
  change (JAv (NDA (nd_tv ndLL) fr_hf (nd_bd ndLL) ANone)) with (JAv ndLL).
  destruct HbL as [-> | ->].
  - eapply TR_pre; [intros w [_ Hw]; rewrite T_g3_0_eq in Hw; exact Hw|]. apply (REENTER T_g3_0 ndLL (40, VL 54) rho'); [innth 68 | exact MS].
  - eapply TR_pre; [intros w [_ Hw]; change ((224 + 36) mod 8) with 4 in Hw; rewrite T_g3_4_eq in Hw; exact Hw|].
    apply (REENTER T_g3_4 ndLL (40, VL 54) rho'); [innth 51 | exact MS].
Qed.

Lemma XH_E_c4_0 : ltac2:(tb__ "0|1|
S3S2aS77Q40A1A1M0G0VTR;S73S58VJAv;Sa8A1S1acR3R2A5VFAM;S5aS2bS2cS3aS59A2S2cS0S2A2S2bS3aS59S1acSa8A4S2bS0S2Z28Sa4Z33A1A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_facts. intros HF0. pose proof (vlF_bound rho _ HF0 c4_vlF) as VB. pose proof c4_meas as CM. peel CM MbL. rename CM into MbN.
  change (JAv ndL4a) with (JAv (NDA (nd_tv ndL4a) fr_hf (nd_bd ndL4a) ANone)).
  pose proof c4_wf2 as W2. peel W2 W2f. pose proof c4_twf2 as TW. peel TW TWf.
  eapply TR_pre with (P := SPA segs (JAv (NDA (nd_tv ndL4a) fr_hf (nd_bd ndL4a) ANone)) E_c4 rho tp).
  { intros w Hw.
    rewrite <- E_c4_eq3.
    rewrite <- E_c4c_eq. apply (reshape_fwd _ E_c4b 31 pDm4 off_c4 off_c4 36 DUnknown rho tp w c4_oi eq_refl c4_wfi ltac:(lia) (fun r => eq_refl) (fun HF => rs_bnd_mc rho _ pDm4 12 (cMI pL) pKm4 HF ltac:(lia) c4_bnd)).
    rewrite <- E_c4b_eq. apply (reshape_ffwd _ E_c4a 2 224 260 DUnknown rho tp w c4_o2 eq_refl W2 ltac:(lia) ltac:(lia) W2f).
    exact (SPA_axforms segs _ xf_c4 rho E_c4_0 E_c4a tp w E_c4a_eq Hw). }
  apply (X_purecT XP_memcpy Pre_mc [L_mc1; L_mc1] E_c4 (nd_tv ndL4a) (nd_bd ndL4a) s_c4 R_c4 rho tp _ (fun Ai rho1 tp1 => CMEMCPY Ai rho1 tp1)
           (fun Ai tr ms md Hsm HM HX => XP_memcpy_site segs AInv CST XGL ALA HCST HXGL Ai E_c4 memcpy_pc s_c4 R_c4 rho tp tr ms md Hsm HM HX R_c4_eq2)
           eq_refl eq_refl R_c4_eq2 (c4_chk XGL)).
  intros L0 rho' tp' HL Hag HF. assert (HL' : L0 = L_mc1) by (destruct HL as [<-|[<-|[]]]; reflexivity). subst L0.
  eapply TR_pre; [|apply (REENTER T_c4 ndL4a (40, VL 50) rho'); [innth 54 |
    rewrite !VL_VM; exact (VM_meas_ag E_c4_0 T_c4 ndL4a ndL4a 40 pNT pL 50 51 rho rho' _ ltac:(lia) VB Hag MbN MbL ltac:(lia) ltac:(lia) ltac:(lia))]].
  intros w Hw. change (JAv ndL4a) with (JAv (NDA (nd_tv ndL4a) fr_hf (nd_bd ndL4a) ANone)).
  apply (SPA_axforms segs _ _ rho' T_c4v T_c4 tp' w T_c4_eq2).
  rewrite <- T_c4v_eq. apply (reshape_fbwd _ T_c4u 2 224 260 DUnknown rho' tp' w c4_to2 eq_refl TW ltac:(lia) ltac:(lia) TWf).
  rewrite <- T_c4u_eq. apply (reshape_bwd _ T_c4t 1 pDm4 off_c4 off_c4 36 DUnknown rho' tp' w c4_to1 eq_refl c4_twf1 ltac:(lia) (fun r => eq_refl) (fun HF => rs_bnd_mc rho' _ pDm4 12 (cMI pL) pKm4 HF ltac:(lia) c4_tbnd)).
  rewrite <- T_c4t_eq. exact Hw.
Qed.

Lemma XH_E_m4_0 : ltac2:(tb__ "0|1|
S3S2aS77Q40A1A1M0G0VTR;S73S58VJAv;Sa9A1S1aeR3R2A5VFAM;S5aS2bS2cS3aS59A2S2cS0S2A2S2bS3aS59S1aeSa9A4S2bS0S2Z28Sa4Z2fA1A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_facts. intros HF0. pose proof (vlF_bound rho _ HF0 m4_vlF) as VB. pose proof m4_meas as CM. peel CM MbL. rename CM into MbN.
  change (JAv ndL4b) with (JAv (NDA (nd_tv ndL4b) fr_hf (nd_bd ndL4b) ANone)).
  pose proof m4_wf2 as W2. peel W2 W2f. pose proof m4_twf2 as TW. peel TW TWf.
  eapply TR_pre with (P := SPA segs (JAv (NDA (nd_tv ndL4b) fr_hf (nd_bd ndL4b) ANone)) E_m4 rho tp).
  { intros w Hw.
    rewrite <- E_m4_eq3.
    rewrite <- E_m4c_eq. apply (reshape_fwd _ E_m4b 32 pDf4 off_m4 off_m4 4 DUnknown rho tp w m4_oi eq_refl m4_wfi ltac:(lia) (fun r => eq_refl) (fun HF => rs_bnd_mc rho _ pDf4 4 (cFV pL) pKf4 HF ltac:(lia) m4_bnd)).
    rewrite <- E_m4b_eq. apply (reshape_ffwd_c _ E_m4a 2 304 308 [mkCell (SLit 304) 4 (SLit 3)] DUnknown rho tp w m4_o2 eq_refl W2 ltac:(lia) ltac:(lia) W2f).
    exact (SPA_axforms segs _ xf_m4 rho E_m4_0 E_m4a tp w E_m4a_eq Hw). }
  apply (X_purecT XP_memcpy Pre_mc [L_mc1; L_mc1] E_m4 (nd_tv ndL4b) (nd_bd ndL4b) s_m4 R_m4 rho tp _ (fun Ai rho1 tp1 => CMEMCPY Ai rho1 tp1)
           (fun Ai tr ms md Hsm HM HX => XP_memcpy_site segs AInv CST XGL ALA HCST HXGL Ai E_m4 memcpy_pc s_m4 R_m4 rho tp tr ms md Hsm HM HX R_m4_eq2)
           eq_refl eq_refl R_m4_eq2 (m4_chk XGL)).
  intros L0 rho' tp' HL Hag HF. assert (HL' : L0 = L_mc1) by (destruct HL as [<-|[<-|[]]]; reflexivity). subst L0.
  eapply TR_pre; [|apply (REENTER T_m4 ndL4b (40, VL 46) rho'); [innth 57 |
    rewrite !VL_VM; exact (VM_meas_ag E_m4_0 T_m4 ndL4b ndL4b 40 pNT pL 46 47 rho rho' _ ltac:(lia) VB Hag MbN MbL ltac:(lia) ltac:(lia) ltac:(lia))]].
  intros w Hw. change (JAv ndL4b) with (JAv (NDA (nd_tv ndL4b) fr_hf (nd_bd ndL4b) ANone)).
  apply (SPA_axforms segs _ _ rho' T_m4v T_m4 tp' w T_m4_eq2).
  rewrite <- T_m4v_eq. apply (reshape_fbwd _ T_m4u 2 304 308 DUnknown rho' tp' w m4_to2 eq_refl TW ltac:(lia) ltac:(lia) TWf).
  rewrite <- T_m4u_eq. apply (reshape_bwd _ T_m4t 1 pDf4 off_m4 off_m4 4 DUnknown rho' tp' w m4_to1 eq_refl m4_twf1 ltac:(lia) (fun r => eq_refl) (fun HF => rs_bnd_mc rho' _ pDf4 4 (cFV pL) pKf4 HF ltac:(lia) m4_tbnd)).
  rewrite <- T_m4t_eq. exact Hw.
Qed.

Lemma XH_E_mi4_w : ltac2:(tb__ "0|4|
S3aS2aS10A1S24S2dS19dR2Sd3R2A1Z1cM0Z27M1R1SbS1abS5eSa3A1S5fSa3A1A9S2eA3S24S2aS5A1ScS3bR3A1A1S33S5Sd3R3A1S2fS5SdeS97G0G1R2SbA5S30S5A1A3A3A3S24S3aS166S1aaR4A1S3cS1afA1M2A2S1afA3S24S2dS16bG2S3cS1aaR5A1A1A2S2eA3S24S2dS12aS9S3bR6A1A1A1S2eA3S3S2aS77Q40A1A1M3G3VTR;S73S58VJAv;Sa3A1RaR3R2A5VFAM;S5aS2bS2cS3aS59A2S2cS0S2A2S2bS3aS59RaSa3A4S2bS0S2Z28Sa4Z35A1A4A4R3A2R1A2A2Ftp0;Ftp;Frho;F_;F_;F_;F_;F_;Fcells;FE0;").
Proof.
  intros E0 cells w_rel w_robjs w_eq w_incl w_vlF rho tp tp0.
  apply TR_facts. intros HF0. pose proof (vlF_bound rho _ HF0 w_vlF) as VB.
  pose proof mi4_meas as CM. peel CM MbL. peel CM MbN. peel CM Mg2. peel CM Mg1. peel CM Mk2. rename CM into Mk1.
  apply (TR_absorb _ E_mi4_1 ndLL rho tp).
  { intros tr ms md Hw. exists (rho_absorb rho [shobj hG 28 39 cells DUnknown] (vms md tp ms)). split; [intros ee; apply eval_absorb|].
    apply (subX_imp _ (E_mi4_1w E0) E_mi4_1 (ax_X E_mi4_1) _ tp _ w_eq w_incl). unfold E_mi4_1w.
    change (JAv ndLL) with (JAv (NDA (nd_tv ndLL) fr_hf (nd_bd ndLL) ANone)) in Hw |- *.
    exact (releaseP_imp E0 (objs_butlast E0) 28 39 cells DUnknown L_win _ _ rho tp tr ms md w_rel w_robjs Hw). }
  intros rho1 HE1.
  rewrite <- (emeas_eq E0 ndLL 40 (VL 53) rho rho1 HE1).
  assert (VB1 : uval rho1 pL <= uval rho1 pNT <= 2 ^ 40) by (unfold uval; rewrite !HE1; exact VB). clear VB HE1. rename VB1 into VB.
  change (JAv ndLL) with (JAv (NDA (nd_tv ndLL) fr_hf (nd_bd ndLL) ANone)).
  eapply TR_pre with (P := SPA segs (JAv (NDA (kept_mi4 ++ [(lDmi, (kb 12 lKmi))]) fr_hf (nd_bd ndLL) ANone)) E_mi4 rho1 tp).
  { intros w Hw. apply (SPA_tv_permb segs AInv CST XGL NPH Kc rho0 (P0_hf CST FB FF) FB FF BX PTrue _ _ fr_hf _ ANone E_mi4 rho1 tp w mi4_tvp).
    apply (xff_imp _ E_mi4_1 E_mi41x E_mi4 (xf_vr 15 496) (vr_need 12 (SAlu ALU_ADD (cMI pL) (SLit 3)) (NMI pA)) rho1 tp w E_mi41x_eq E_mi4_eq2 mi4_xff); [|exact Hw].
    intros tr md _ HF1. exact (vr_mi4_ok rho1 _ HF1 mi4_needF). }
  apply (X_VR E_mi4 kept_mi4 lDmi lKmi 12 496 (nd_bd ndLL) brest_mi4 s_mi4 R_mi4 (XkeepF lDmi (ax_X E_mi4_1)) rho1 tp _ T_mi4k0 T_mi4f0 T_mi4g0 (SVar 679) (SVar 680) bdK_mi4 bdG_mi4
           (mi4_chk XGL) R_mi4_eq T_mi4k0_ta mi4_iK mi4_bK T_mi4f0_ta mi4_iF T_mi4g0_ta mi4_iG mi4_bG).
  -
    intros rho' tp' Hag HF.
    eapply TR_pre; [|apply (REENTER JR_mi4 ndL4a (40, VL 52) (rho_sub rho' s_mi4k)); [innth 52 | rewrite !VL_VM; exact (VM_meas_sub E0 JR_mi4 ndLL ndL4a 40 pNT pL 52 53 rho1 rho' s_mi4k _ ltac:(lia) VB Hag MbN MbL Mk1 Mk2 ltac:(lia) ltac:(lia) ltac:(lia))]].
    intros w Hw. apply (land_imp T_mi4k JR_mi4 s_mi4k (kept_mi4 ++ [(lDmi, (kb 12 lKmi))]) tv2_mi4k (bdK_mi4 ++ brest_mi4) bd2_mi4k _ _ rho' tp' w mi4k_land mi4k_bd).
    apply (xff_imp _ T_mi4k0 T_mi4k1 T_mi4k (xf_backV 14 28 496) [SPUle (SLit IMG_HI) lDmi] rho' tp' w T_mi4k1_ap T_mi4k_eq2 mi4k_xff); [|exact Hw].
    intros tr md HJ HF1.
    constructor; [exact (let K := k_nz_lit rho' _ (cMI pL) 3 lKmi HF1 ltac:(lia) mi4k_live in live_holds _ rho' tp' tr md lDmi 12 lKmi HJ ltac:(cbn; tauto) ltac:(lia) (proj1 K) (proj2 K))|constructor].
  -
    intros rho' tp' Hag HF.
    eapply TR_pre; [|apply (REENTER JF_mi4 ndL4af (20, z0) (rho_sub rho' s_mi4f)); [innth 53 | rewrite emeas_z0; pose proof (emeas_lb E0 ndLL 40 (VL 53) rho1 ltac:(lia)); lia]].
    intros w Hw. apply (land_imp (shadow_reopen_stateA (shadow_reopen_stateA T_mi4f (XnoLoc T_mi4f) hG 38 39) (XnoLoc T_mi4f) hG 28 33) JF_mi4 s_mi4f (kept_mi4 ++ [(lDmi, (kb 12 lKmi))]) tv2_mi4f (firstn 1 brest_mi4) (firstn 1 brest_mi4) _ _ rho' tp' w mi4f_land mi4f_bd).
    apply (drop_imp _ _ fr_hf brest_mi4 1 rho' tp' w mi4f_wp).
    apply (reopenS_imp (shadow_reopen_stateA T_mi4f (XnoLoc T_mi4f) hG 38 39) (XnoLoc T_mi4f) (kept_mi4 ++ [(lDmi, (kb 12 lKmi))]) _ 28 33 rho' tp' w (mi4f_ro1 XGL)).
    apply (reopen_imp T_mi4f (XnoLoc T_mi4f) (kept_mi4 ++ [(lDmi, (kb 12 lKmi))]) _ 38 39 rho' tp' w (mi4f_ro0 XGL)).
    exact (SPA_axforms segs _ (xf_backV 14 28 496) rho' T_mi4f0 T_mi4f tp' w T_mi4f_ap Hw).
  -
    intros rho' tp' Hag HF.
    eapply TR_pre; [|apply (REENTER JR_mi4 ndL4a (40, VL 52) (rho_sub rho' s_mi4g)); [innth 52 | rewrite !VL_VM; exact (VM_meas_sub E0 JR_mi4 ndLL ndL4a 40 pNT pL 52 53 rho1 rho' s_mi4g _ ltac:(lia) VB Hag MbN MbL Mg1 Mg2 ltac:(lia) ltac:(lia) ltac:(lia))]].
    intros w Hw. apply (land_imp T_mi4g JR_mi4 s_mi4g (kept_mi4 ++ [(SVar 679, (kb 12 (SVar 680)))]) tv2_mi4g (bdG_mi4 ++ brest_mi4) bd2_mi4g _ _ rho' tp' w mi4g_land mi4g_bd).
    exact (SPA_axforms segs _ (xf_backV 14 28 496) rho' T_mi4g0 T_mi4g tp' w T_mi4g_ap Hw).
Qed.

Lemma XH_E_mi4_0_0 : ltac2:(tb__ "0|1|
S3S2aS77Q40A1A1M0G0VTR;S73S58VJAv;Sa3A1S1a8R3R2A5VFAM;S5aS2bS2cS3aS59A2S2cS0S2A2S2bS3aS59S1a8Sa3A4S2bS0S2Z28Sa4Z35A1A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof. exact (XH_E_mi4_w E_mi4_0_0 cells_w0 w0_rel w0_robjs w0_eq w0_incl w0_vlF). Qed.
Lemma XH_E_mi4_0_4 : ltac2:(tb__ "0|1|
S3S2aS77Q40A1A1M0G0VTR;S73S58VJAv;Sa3A1S1a9R3R2A5VFAM;S5aS2bS2cS3aS59A2S2cS0S2A2S2bS3aS59S1a9Sa3A4S2bS0S2Z28Sa4Z35A1A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof. exact (XH_E_mi4_w E_mi4_0_4 cells_w4 w4_rel w4_robjs w4_eq w4_incl w4_vlF). Qed.

Lemma XH_E_fv4_0 : ltac2:(tb__ "0|1|
S3S2aS77Q40A1A1M0G0VTR;S73S58VJAv;Sa8A1S1adR3R2A5VFAM;S5aS2bS2cS3aS59A2S2cS0S2A2S2bS3aS59S1adSa8A4S2bS0S2Z28Sa4Z31A1A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  apply TR_facts. intros HF0. pose proof (vlF_bound rho _ HF0 fv4_vlF) as VB.
  pose proof fv4_meas as CM. peel CM MbL. peel CM MbN. peel CM Mg2. peel CM Mg1. peel CM Mk2. rename CM into Mk1.
  change (JAv ndL4a) with (JAv (NDA (nd_tv ndL4a) fr_hf (nd_bd ndL4a) ANone)).
  eapply TR_pre with (P := SPA segs (JAv (NDA (kept_fv4 ++ [(lDfv, (kb 4 lKfv))]) fr_hf (nd_bd ndL4a) ANone)) E_fv4 rho tp).
  { intros w Hw. apply (SPA_tv_permb segs AInv CST XGL NPH Kc rho0 (P0_hf CST FB FF) FB FF BX PTrue _ _ fr_hf _ ANone E_fv4 rho tp w fv4_tvp).
    apply (xff_imp _ E_fv4_0 E_fv41x E_fv4 (xf_vr 16 528) (vr_need 4 (SAlu ALU_ADD (cFV pL) (SLit 1)) (NFV pA)) rho tp w E_fv41x_eq E_fv4_eq2 fv4_xff); [|exact Hw].
    intros tr md _ HF1. exact (vr_fv4_ok rho _ fv_c fv_n HF1 fv4_needF). }
  apply (X_VR E_fv4 kept_fv4 lDfv lKfv 4 528 (nd_bd ndL4a) brest_fv4 s_fv4 R_fv4 (XkeepF lDfv (ax_X E_fv4_0)) rho tp _ T_fv4k0 T_fv4f0 T_fv4g0 (SVar 560) (SVar 561) bdK_fv4 bdG_fv4
           (fv4_chk XGL) R_fv4_eq T_fv4k0_ta fv4_iK fv4_bK T_fv4f0_ta fv4_iF T_fv4g0_ta fv4_iG fv4_bG).
  -
    intros rho' tp' Hag HF.
    eapply TR_pre; [|apply (REENTER JR_fv4 ndL4b (40, VL 48) (rho_sub rho' s_fv4k)); [innth 55 | rewrite !VL_VM; exact (VM_meas_sub E_fv4_0 JR_fv4 ndL4a ndL4b 40 pNT pL 48 49 rho rho' s_fv4k _ ltac:(lia) VB Hag MbN MbL Mk1 Mk2 ltac:(lia) ltac:(lia) ltac:(lia))]].
    intros w Hw. apply (land_imp T_fv4k JR_fv4 s_fv4k (kept_fv4 ++ [(lDfv, (kb 4 lKfv))]) tv2_fv4k (bdK_fv4 ++ brest_fv4) bd2_fv4k _ _ rho' tp' w fv4k_land fv4k_bd).
    apply (xff_imp _ T_fv4k0 T_fv4k1 T_fv4k (xf_backV 15 29 528) [SPUle (SLit IMG_HI) lDfv] rho' tp' w T_fv4k1_ap T_fv4k_eq2 fv4k_xff); [|exact Hw].
    intros tr md HJ HF1.
    constructor; [exact (let K := k_nz_lit rho' _ (cFV pL) 1 lKfv HF1 ltac:(lia) fv4k_live in live_holds _ rho' tp' tr md lDfv 4 lKfv HJ ltac:(cbn; tauto) ltac:(lia) (proj1 K) (proj2 K))|constructor].
  -
    intros rho' tp' Hag HF.
    eapply TR_pre; [|apply (REENTER JF_fv4 ndL4bf (20, z0) (rho_sub rho' s_fv4f)); [innth 56 | rewrite emeas_z0; pose proof (emeas_lb E_fv4_0 ndL4a 40 (VL 49) rho ltac:(lia)); lia]].
    intros w Hw. apply (land_imp (shadow_reopen_stateA (shadow_reopen_stateA T_fv4f (XnoLoc T_fv4f) hG 38 39) (XnoLoc T_fv4f) hG 28 33) JF_fv4 s_fv4f (kept_fv4 ++ [(lDfv, (kb 4 lKfv))]) tv2_fv4f (firstn 1 brest_fv4) (firstn 1 brest_fv4) _ _ rho' tp' w fv4f_land fv4f_bd).
    apply (drop_imp _ _ fr_hf brest_fv4 1 rho' tp' w fv4f_wp).
    apply (reopenS_imp (shadow_reopen_stateA T_fv4f (XnoLoc T_fv4f) hG 38 39) (XnoLoc T_fv4f) (kept_fv4 ++ [(lDfv, (kb 4 lKfv))]) _ 28 33 rho' tp' w (fv4f_ro1 XGL)).
    apply (reopen_imp T_fv4f (XnoLoc T_fv4f) (kept_fv4 ++ [(lDfv, (kb 4 lKfv))]) _ 38 39 rho' tp' w (fv4f_ro0 XGL)).
    exact (SPA_axforms segs _ (xf_backV 15 29 528) rho' T_fv4f0 T_fv4f tp' w T_fv4f_ap Hw).
  -
    intros rho' tp' Hag HF.
    eapply TR_pre; [|apply (REENTER JR_fv4 ndL4b (40, VL 48) (rho_sub rho' s_fv4g)); [innth 55 | rewrite !VL_VM; exact (VM_meas_sub E_fv4_0 JR_fv4 ndL4a ndL4b 40 pNT pL 48 49 rho rho' s_fv4g _ ltac:(lia) VB Hag MbN MbL Mg1 Mg2 ltac:(lia) ltac:(lia) ltac:(lia))]].
    intros w Hw. apply (land_imp T_fv4g JR_fv4 s_fv4g (kept_fv4 ++ [(SVar 560, (kb 4 (SVar 561)))]) tv2_fv4g (bdG_fv4 ++ brest_fv4) bd2_fv4g _ _ rho' tp' w fv4g_land fv4g_bd).
    exact (SPA_axforms segs _ (xf_backV 15 29 528) rho' T_fv4g0 T_fv4g tp' w T_fv4g_ap Hw).
Qed.

Lemma XH_E_mm4_0 : ltac2:(tb__ "0|1|
S3S2aS77Q40A1A1M0G0VTR;S73S58VJAv;Sa9A1S1b0R3R2A5VFAM;S5aS2bS2cS3aS59A2S2cS0S2A2S2bS3aS59S1b0Sa9A4S2bS0S2Z28Sa4Z2dA1A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  apply TR_facts. intros HF0. pose proof (vlF_bound rho _ HF0 mm4_vlF) as VB.
  pose proof mm4_meas as CM. peel CM MbL. peel CM MbN. peel CM Mg2. peel CM Mg1. peel CM Mk2. rename CM into Mk1.
  change (JAv ndL4b) with (JAv (NDA (nd_tv ndL4b) fr_hf (nd_bd ndL4b) ANone)).
  eapply TR_pre with (P := SPA segs (JAv (NDA (kept_mm4 ++ [(lDmm, (kb 4 lKmm))]) fr_hf (nd_bd ndL4b) ANone)) E_mm4 rho tp).
  { intros w Hw. apply (SPA_tv_permb segs AInv CST XGL NPH Kc rho0 (P0_hf CST FB FF) FB FF BX PTrue _ _ fr_hf _ ANone E_mm4 rho tp w mm4_tvp).
    apply (xff_imp _ E_mm4_0 E_mm41x E_mm4 (xf_vr 17 560) (vr_need 4 (SAlu ALU_ADD (cMM pL) (SLit 1)) (NMM pA)) rho tp w E_mm41x_eq E_mm4_eq2 mm4_xff); [|exact Hw].
    intros tr md _ HF1. exact (vr_fv4_ok rho _ mm_c mm_n HF1 mm4_needF). }
  apply (X_VR E_mm4 kept_mm4 lDmm lKmm 4 560 (nd_bd ndL4b) brest_mm4 s_mm4 R_mm4 (XkeepF lDmm (ax_X E_mm4_0)) rho tp _ T_mm4k0 T_mm4f0 T_mm4g0 (SVar 560) (SVar 561) bdK_mm4 bdG_mm4
           (mm4_chk XGL) R_mm4_eq T_mm4k0_ta mm4_iK mm4_bK T_mm4f0_ta mm4_iF T_mm4g0_ta mm4_iG mm4_bG).
  -
    intros rho' tp' Hag HF.
    eapply TR_pre; [|apply (REENTER JR_mm4 ndL4c (40, VL 44) (rho_sub rho' s_mm4k)); [innth 58 | rewrite !VL_VM; exact (VM_meas_sub E_mm4_0 JR_mm4 ndL4b ndL4c 40 pNT pL 44 45 rho rho' s_mm4k _ ltac:(lia) VB Hag MbN MbL Mk1 Mk2 ltac:(lia) ltac:(lia) ltac:(lia))]].
    intros w Hw. apply (land_imp T_mm4k JR_mm4 s_mm4k (kept_mm4 ++ [(lDmm, (kb 4 lKmm))]) tv2_mm4k (bdK_mm4 ++ brest_mm4) bd2_mm4k _ _ rho' tp' w mm4k_land mm4k_bd).
    apply (xff_imp _ T_mm4k0 T_mm4k1 T_mm4k (xf_backV 16 30 560) [SPUle (SLit IMG_HI) lDmm] rho' tp' w T_mm4k1_ap T_mm4k_eq2 mm4k_xff); [|exact Hw].
    intros tr md HJ HF1.
    constructor; [exact (let K := k_nz_lit rho' _ (cMM pL) 1 lKmm HF1 ltac:(lia) mm4k_live in live_holds _ rho' tp' tr md lDmm 4 lKmm HJ ltac:(cbn; tauto) ltac:(lia) (proj1 K) (proj2 K))|constructor].
  -
    intros rho' tp' Hag HF.
    eapply TR_pre; [|apply (REENTER JF_mm4 ndL4cf (20, z0) (rho_sub rho' s_mm4f)); [innth 59 | rewrite emeas_z0; pose proof (emeas_lb E_mm4_0 ndL4b 40 (VL 45) rho ltac:(lia)); lia]].
    intros w Hw. apply (land_imp (shadow_reopen_stateA (shadow_reopen_stateA T_mm4f (XnoLoc T_mm4f) hG 28 33) (XnoLoc T_mm4f) hG 38 39) JF_mm4 s_mm4f (kept_mm4 ++ [(lDmm, (kb 4 lKmm))]) tv2_mm4f (firstn 1 brest_mm4) (firstn 1 brest_mm4) _ _ rho' tp' w mm4f_land mm4f_bd).
    apply (drop_imp _ _ fr_hf brest_mm4 1 rho' tp' w mm4f_wp).
    apply (reopenS_imp (shadow_reopen_stateA T_mm4f (XnoLoc T_mm4f) hG 28 33) (XnoLoc T_mm4f) (kept_mm4 ++ [(lDmm, (kb 4 lKmm))]) _ 38 39 rho' tp' w (mm4f_ro1 XGL)).
    apply (reopen_imp T_mm4f (XnoLoc T_mm4f) (kept_mm4 ++ [(lDmm, (kb 4 lKmm))]) _ 28 33 rho' tp' w (mm4f_ro0 XGL)).
    exact (SPA_axforms segs _ (xf_backV 16 30 560) rho' T_mm4f0 T_mm4f tp' w T_mm4f_ap Hw).
  -
    intros rho' tp' Hag HF.
    eapply TR_pre; [|apply (REENTER JR_mm4 ndL4c (40, VL 44) (rho_sub rho' s_mm4g)); [innth 58 | rewrite !VL_VM; exact (VM_meas_sub E_mm4_0 JR_mm4 ndL4b ndL4c 40 pNT pL 44 45 rho rho' s_mm4g _ ltac:(lia) VB Hag MbN MbL Mg1 Mg2 ltac:(lia) ltac:(lia) ltac:(lia))]].
    intros w Hw. apply (land_imp T_mm4g JR_mm4 s_mm4g (kept_mm4 ++ [(SVar 560, (kb 4 (SVar 561)))]) tv2_mm4g (bdG_mm4 ++ brest_mm4) bd2_mm4g _ _ rho' tp' w mm4g_land mm4g_bd).
    exact (SPA_axforms segs _ (xf_backV 16 30 560) rho' T_mm4g0 T_mm4g tp' w T_mm4g_ap Hw).
Qed.

Lemma XH_E_sg4_0 : ltac2:(tb__ "0|1|
S3S2aS77Q40A1A1M0G0VTR;S73S58VJAv;SadA1S1b1R3R2A5VFAM;S5aS2bS2cS3aS59A2S2cS0S2A2S2bS3aS59S1b1SadA4S2bS0S2Z28Sa4Z2bA1A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  apply TR_facts. intros HF0. pose proof (vlF_bound rho _ HF0 sg4_vlF) as VB.
  pose proof sg4_meas as CM. peel CM MbL. peel CM MbN. peel CM Mg2. peel CM Mg1. peel CM Mk2. rename CM into Mk1.
  change (JAv ndL4c) with (JAv (NDA (nd_tv ndL4c) fr_hf (nd_bd ndL4c) ANone)).
  eapply TR_pre with (P := SPA segs (JAv (NDA (kept_sg4 ++ [(lDsg, (kb 4 lKsg))]) fr_hf (nd_bd ndL4c) ANone)) E_sg4 rho tp).
  { intros w Hw. apply (SPA_tv_permb segs AInv CST XGL NPH Kc rho0 (P0_hf CST FB FF) FB FF BX PTrue _ _ fr_hf _ ANone E_sg4 rho tp w sg4_tvp).
    apply (xff_imp _ E_sg4_0 E_sg41x E_sg4 (xf_vr 18 592) (vr_need 4 (SAlu ALU_ADD (cSG pL) (SLit 1)) (NSG pA)) rho tp w E_sg41x_eq E_sg4_eq2 sg4_xff); [|exact Hw].
    intros tr md _ HF1. exact (vr_fv4_ok rho _ sg_c sg_n HF1 sg4_needF). }
  apply (X_VR E_sg4 kept_sg4 lDsg lKsg 4 592 (nd_bd ndL4c) brest_sg4 s_sg4 R_sg4 (XkeepF lDsg (ax_X E_sg4_0)) rho tp _ T_sg4k0 T_sg4f0 T_sg4g0 (SVar 656) (SVar 657) bdK_sg4 bdG_sg4
           (sg4_chk XGL) R_sg4_eq T_sg4k0_ta sg4_iK sg4_bK T_sg4f0_ta sg4_iF T_sg4g0_ta sg4_iG sg4_bG).
  -
    intros rho' tp' Hag HF.
    eapply TR_pre; [|apply (REENTER JR_sg4 ndL4d (40, VL 42) (rho_sub rho' s_sg4k)); [innth 60 | rewrite !VL_VM; exact (VM_meas_sub E_sg4_0 JR_sg4 ndL4c ndL4d 40 pNT pL 42 43 rho rho' s_sg4k _ ltac:(lia) VB Hag MbN MbL Mk1 Mk2 ltac:(lia) ltac:(lia) ltac:(lia))]].
    intros w Hw. apply (land_imp (shadow_reopen_stateA (shadow_reopen_stateA T_sg4k (XnoLoc T_sg4k) hG 28 33) (XnoLoc T_sg4k) hG 38 39) JR_sg4 s_sg4k (kept_sg4 ++ [(lDsg, (kb 4 lKsg))]) tv2_sg4k (bdK_sg4 ++ brest_sg4) bd2_sg4k _ _ rho' tp' w sg4k_land sg4k_bd).
    apply (reopenS_imp (shadow_reopen_stateA T_sg4k (XnoLoc T_sg4k) hG 28 33) (XnoLoc T_sg4k) (kept_sg4 ++ [(lDsg, (kb 4 lKsg))]) _ 38 39 rho' tp' w (sg4k_ro1 XGL)).
    apply (reopen_imp T_sg4k (XnoLoc T_sg4k) (kept_sg4 ++ [(lDsg, (kb 4 lKsg))]) _ 28 33 rho' tp' w (sg4k_ro0 XGL)).
    apply (xff_imp _ T_sg4k0 T_sg4k1 T_sg4k (xf_backV 17 31 592) [SPUle (SLit IMG_HI) lDsg] rho' tp' w T_sg4k1_ap T_sg4k_eq2 sg4k_xff); [|exact Hw].
    intros tr md HJ HF1.
    constructor; [exact (let K := k_nz_lit rho' _ (cSG pL) 1 lKsg HF1 ltac:(lia) sg4k_live in live_holds _ rho' tp' tr md lDsg 4 lKsg HJ ltac:(cbn; tauto) ltac:(lia) (proj1 K) (proj2 K))|constructor].
  -
    intros rho' tp' Hag HF.
    eapply TR_pre; [|apply (REENTER JF_sg4 ndL4df (20, z0) (rho_sub rho' s_sg4f)); [innth 61 | rewrite emeas_z0; pose proof (emeas_lb E_sg4_0 ndL4c 40 (VL 43) rho ltac:(lia)); lia]].
    intros w Hw. apply (land_imp (shadow_reopen_stateA (shadow_reopen_stateA T_sg4f (XnoLoc T_sg4f) hG 28 33) (XnoLoc T_sg4f) hG 38 39) JF_sg4 s_sg4f (kept_sg4 ++ [(lDsg, (kb 4 lKsg))]) tv2_sg4f (firstn 1 brest_sg4) (firstn 1 brest_sg4) _ _ rho' tp' w sg4f_land sg4f_bd).
    apply (drop_imp _ _ fr_hf brest_sg4 1 rho' tp' w sg4f_wp).
    apply (reopenS_imp (shadow_reopen_stateA T_sg4f (XnoLoc T_sg4f) hG 28 33) (XnoLoc T_sg4f) (kept_sg4 ++ [(lDsg, (kb 4 lKsg))]) _ 38 39 rho' tp' w (sg4f_ro1 XGL)).
    apply (reopen_imp T_sg4f (XnoLoc T_sg4f) (kept_sg4 ++ [(lDsg, (kb 4 lKsg))]) _ 28 33 rho' tp' w (sg4f_ro0 XGL)).
    exact (SPA_axforms segs _ (xf_backV 17 31 592) rho' T_sg4f0 T_sg4f tp' w T_sg4f_ap Hw).
  -
    intros rho' tp' Hag HF.
    eapply TR_pre; [|apply (REENTER JR_sg4 ndL4d (40, VL 42) (rho_sub rho' s_sg4g)); [innth 60 | rewrite !VL_VM; exact (VM_meas_sub E_sg4_0 JR_sg4 ndL4c ndL4d 40 pNT pL 42 43 rho rho' s_sg4g _ ltac:(lia) VB Hag MbN MbL Mg1 Mg2 ltac:(lia) ltac:(lia) ltac:(lia))]].
    intros w Hw. apply (land_imp (shadow_reopen_stateA (shadow_reopen_stateA T_sg4g (XnoLoc T_sg4g) hG 28 33) (XnoLoc T_sg4g) hG 38 39) JR_sg4 s_sg4g (kept_sg4 ++ [(SVar 656, (kb 4 (SVar 657)))]) tv2_sg4g (bdG_sg4 ++ brest_sg4) bd2_sg4g _ _ rho' tp' w sg4g_land sg4g_bd).
    apply (reopenS_imp (shadow_reopen_stateA T_sg4g (XnoLoc T_sg4g) hG 28 33) (XnoLoc T_sg4g) (kept_sg4 ++ [(SVar 656, (kb 4 (SVar 657)))]) _ 38 39 rho' tp' w (sg4g_ro1 XGL)).
    apply (reopen_imp T_sg4g (XnoLoc T_sg4g) (kept_sg4 ++ [(SVar 656, (kb 4 (SVar 657)))]) _ 28 33 rho' tp' w (sg4g_ro0 XGL)).
    exact (SPA_axforms segs _ (xf_backV 17 31 592) rho' T_sg4g0 T_sg4g tp' w T_sg4g_ap Hw).
Qed.

Lemma XH_E_f5o0 : ltac2:(tb__ "0|1|
S3S2aS77Q40A1A1M0G0VTR;S73S58VJAv;SfeA1S189R3R2A5VFAM;S5aS2bS2cS3aS59A2S2cS0S2A2S2bS3aS59S189SfeA4S2bS0S2ZdSa2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. change (JAv ndEo) with (JAv (NDA (nd_tv ndEo) fr_hf (nd_bd ndEo) ANone)).
  eapply TR_pre with (P := SPA segs (JAv (NDA (nd_tv ndEo) fr_hf (nd_bd ndEo) ANone)) E_f5o rho tp).
  { intros w Hw. apply (SPA_axforms segs _ [AXUnbase (ilast E_f5o1) SHB] rho E_f5o1 E_f5o tp w E_f5o_eq2). rewrite <- E_f5o1_eq.
    exact (reopen_imp E_f5o0 (XR E_f5o0) (nd_tv ndEo) _ 0 64 rho tp w (f5o_ro XGL) Hw). }
  apply (X_purecT0 Pre_f5 [L_f5] E_f5o (nd_tv ndEo) (nd_bd ndEo) s_f5o R_f5o rho tp _ (fun Ai rho1 tp1 => CF5 Ai rho1 tp1) eq_refl eq_refl R_f5o_eq (f5o_chk XGL)).
  intros L0 rho' tp' HL Hag HF. destruct HL as [<-|[]].
  eapply TR_pre; [|apply (REENTER T_f5o ndEo (12, z0) rho'); [innth 65 | rewrite !emeas_z0; lia]].
  intros w Hw. change (JAv ndEo) with (JAv (NDA (nd_tv ndEo) fr_hf (nd_bd ndEo) ANone)). rewrite <- T_f5o_eq2.
  apply (carve_imp T_f5o1 objs_f5o1 sh_f5o1 0 64 (nd_tv ndEo) _ rho' tp' w T_f5o1_objs sh_f5o1_eq ltac:(lia) ltac:(lia) (f5o_carve XGL)).
  apply (SPA_axforms segs _ _ rho' T_f5o0 T_f5o1 tp' w T_f5o1_eq). unfold Pre_f5, L_f5 in *. rewrite <- T_f5o0_eq. exact Hw.
Qed.
Lemma XH_E_f5f0 : ltac2:(tb__ "0|1|
S3S2aS77Q40A1A1M0G0VTR;S73S58VJAv;SfdA1S188R3R2A5VFAM;S5aS2bS2cS3aS59A2S2cS0S2A2S2bS3aS59S188SfdA4S2bS0S2ZdSa2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. change (JAv ndEf) with (JAv (NDA (nd_tv ndEf) fr_hf (nd_bd ndEf) ANone)).
  eapply TR_pre with (P := SPA segs (JAv (NDA (nd_tv ndEf) fr_hf (nd_bd ndEf) ANone)) E_f5f rho tp).
  { intros w Hw. apply (SPA_axforms segs _ [AXUnbase (ilast E_f5f1) SHB] rho E_f5f1 E_f5f tp w E_f5f_eq2). rewrite <- E_f5f1_eq.
    exact (reopen_imp E_f5f0 (XR E_f5f0) (nd_tv ndEf) _ 0 64 rho tp w (f5f_ro XGL) Hw). }
  apply (X_purecT0 Pre_f5 [L_f5] E_f5f (nd_tv ndEf) (nd_bd ndEf) s_f5f R_f5f rho tp _ (fun Ai rho1 tp1 => CF5 Ai rho1 tp1) eq_refl eq_refl R_f5f_eq (f5f_chk XGL)).
  intros L0 rho' tp' HL Hag HF. destruct HL as [<-|[]].
  eapply TR_pre; [|apply (REENTER T_f5f ndEf (12, z0) rho'); [innth 64 | rewrite !emeas_z0; lia]].
  intros w Hw. change (JAv ndEf) with (JAv (NDA (nd_tv ndEf) fr_hf (nd_bd ndEf) ANone)). rewrite <- T_f5f_eq2.
  apply (carve_imp T_f5f1 objs_f5f1 sh_f5f1 0 64 (nd_tv ndEf) _ rho' tp' w T_f5f1_objs sh_f5f1_eq ltac:(lia) ltac:(lia) (f5f_carve XGL)).
  apply (SPA_axforms segs _ _ rho' T_f5f0 T_f5f1 tp' w T_f5f1_eq). unfold Pre_f5, L_f5 in *. rewrite <- T_f5f0_eq. exact Hw.
Qed.

Lemma X_X_rl : ltac2:(tb__ "0|5|
S3aS3aS3aS2aS2cS2S2A2A1S2aS46A1S3S2aS77Q40A1A1M0S0G0S0S24S34S3aA1S183RaS2fS182S184S195A1S30S182A1A3A2S35S3aR9A2A3S24S3aS42RaS1c0S3bRaA1M1S7bS5S18aScG1A1A3A2A2R9A3S24S2dS31S31Se4Pa0PaaS97Z3S7cS5S18aScS3bRbA1M2A1A3A5S130S9G2A1A1A2S61SaG2A1S5cR9S7dR8S5bA4A2A2S2eA3Sc5S2cS2cS3aS59A2M3S2cS0S2A2M4A2S2bG3G4S2bS3aS59RbS5cRaS30S2cS2cS2S0A2S2A2A1R9S5bA4A4S2bS0S2R4Sa2A4A4S15eA3S50Z0R5A2S50S54S51R6Z1A2S52Z2Z40A2A2R8A2VTR;S73S58VJAv;S5cRdS7dRcS5bA4A1R10RbRaA5VFAM;R9R8A2A2F_;F_;F_;F_;F_;F_;Frk;Ftp0;Fb;Ftp;Frho;Fbd;Ftv;FC;FX1;FX;").
Proof.
  intros X X1 C tv bd rho tp b tp0 rk HX1 HC CK HinC Hrk Hb. peel CK Hnb. peel CK Hfe. rename CK into HR.
  apply (TR_pre (fun w => exists rho', SPA segs (JAv (NDA tv [] bd ANone)) C rho' tp w)).
  { intros [tr [ms md]] Hw. pose proof (SPA_axforms segs _ [AXSelect sel_rel] rho X X1 tp _ HX1 Hw) as Hw1.
    exists (rho_absorb rho (skipn NREL (ss_objs (ax_S X1))) (vms md tp ms)). rewrite <- HC.
    change (ax_setS X1 (set_objs (ax_S X1) (firstn NREL (ss_objs (ax_S X1))))) with (drop_lastA X1 (firstn NREL (ss_objs (ax_S X1)))).
    change (@nil (sv * Z * sv)) with (remove_nth 0 fr_hf).
    apply (JA_release_inline segs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eb.Lib_arena_alloc.HTOP_ok AInv CST XGL ALA HCST HXGL LFLAG LFSH NPH Kc rho0 (P0_hf CST FB FF) FB FF BX PTrue HKc HBX HNP
             tv fr_hf bd ANone 0%nat 160%positive 3 170%positive hG X1 (firstn NREL (ss_objs (ax_S X1))) (skipn NREL (ss_objs (ax_S X1))) rho tp tr ms md);
      [reflexivity | lia | symmetry; apply firstn_skipn | exact HR | exact Hfe | exact Hnb | intros A1 A2 _; exact I | exact Hw1]. }
  apply TR_exw. intros rho'. apply (REENTER C (NDA tv [] bd ANone) (rk, z0)); [exact HinC | rewrite emeas_z0; lia].
Qed.
Lemma XH_X_rlo : ltac2:(tb__ "0|1|
S3S2aS77Q40A1A1M0S0G0S50S54ZbS52Z2Z40A2A2R2A2VTR;S73S58VJAv;SfeA1S194R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof. intros rho tp b tp0 Hb. unfold ndEo. apply (X_X_rl X_rlo X_rlo1 C_rlo tvQ _ rho tp b tp0 10 X_rlo1_eq C_rlo_eq2 rlo_chk); [innth 67 | lia | lia]. Qed.
Lemma XH_X_rlf : ltac2:(tb__ "0|1|
S3S2aS77Q40A1A1M0S0G0S50S54ZbS52Z2Z40A2A2R2A2VTR;S73S58VJAv;SfdA1S193R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof. intros rho tp b tp0 Hb. unfold ndEf. apply (X_X_rl X_rlf X_rlf1 C_rlf tvQ _ rho tp b tp0 10 X_rlf1_eq C_rlf_eq2 rlf_chk); [innth 66 | lia | lia]. Qed.

Lemma X_P_ok : ltac2:(tb__ "0|1|
S3S2aS77Q40A1A1M0S0G0VTR;S73S58VJAv;S190A1S18cR4R3A5VFAM;R2R1A2A2Ftp0;Fb;Ftp;Frho;").
Proof. intros. apply POST. innth 1. Qed.
Lemma X_P_fail : ltac2:(tb__ "0|1|
S3S2aS77Q40A1A1M0S0G0VTR;S73S58VJAv;S18fA1S18bR4R3A5VFAM;R2R1A2A2Ftp0;Fb;Ftp;Frho;").
Proof. intros. apply POST. innth 0. Qed.

Lemma exits_okT : ltac2:(tb__ "0|3|
S3aS59S2cS0S2A2M0S3S2aS77Q40A1A1M1G1Sc5S2cS2cS3aS59A2M2G0A2S2bG2G0S2bS3aS59R6R5A4R4A4S15fA3VTR;S73S58VJAv;R6A1R7R4R3A5VFAM;S5aS2bG2G0S2bS3aS59R7R6A4R5A4R4A2R2A2A2F_;Ftp0;Ftp;Frho;FrvX;FndX;FX;").
Proof.
  intros X ndX rvX rho tp tp0 Hin. cbn [In exitsF2] in Hin.
  destruct Hin as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]];
    injection H as <- <- <-.
  - apply XH_E_sm. rewrite emeas_z0. lia.
  - apply XH_X_pro. rewrite emeas_z0. lia.
  - apply XH_E_co.
  - apply XH_E_ms.
  - apply XH_E_pc.
  - apply XH_E_da.
  - apply XH_E_dg. rewrite emeas_z0. lia.
  - apply XH_E_mi0.
  - apply XH_E_fv0.
  - apply XH_E_mc0.
  - apply XH_E_mm0.
  - apply XH_E_sg0.
  - apply XH_XEf42.
  - apply XH_XEo42.
  - apply XH_E_trg0.
  - apply XH_E_trb0.
  - apply XH_E_tdg0.
  - apply XH_E_rp0.
  - apply XH_E_ts0.
  - apply XH_E_md0.
  - apply XH_E_pg0.
  - apply XH_E_wdg0.
  - apply XH_XJ.
  - apply XH_XLJ.
  - apply XH_E_g1_0.
  - apply XH_E_g2_0.
  - apply XH_E_g3_0.
  - apply XH_E_mi4_0_4.
  - apply XH_E_c4_0.
  - apply XH_E_fv4_0.
  - apply XH_E_m4_0.
  - apply XH_E_mm4_0.
  - apply XH_E_sg4_0.
  - apply XH_XEf6a.
  - apply XH_XEf6b.
  - apply XH_XEo6.
  - apply XH_E_f5f0.
  - apply XH_E_f5o0.
  - apply XH_X_rlf. rewrite emeas_z0. lia.
  - apply XH_X_rlo. rewrite emeas_z0. lia.
  - apply X_P_fail.
  - apply X_P_ok.
  - apply XH_E_mi4_0_0.
Qed.
End X.

Section Safety.
Variable ok : world -> Prop.
Hypothesis Hok : ltac2:(tb__ "0|0|
S72S58VKc;Vok;A3").
Hypothesis AC : ltac2:(tb__ "0|0|
S153S58S14dVAInv;VCST;VXGL;A5").
Hypothesis SSC : ltac2:(tb__ "0|0|
S0Sc5S0R1S2fS0Z0S2fS0Zf5S2fS0Zf8S30S0A1A3A3A3A3S1b4S58S14dVAInv;VCST;VXGL;R2A6F_;Fxx;").

Theorem handle_f_sum : ltac2:(tb__ "0|0|
S2aS77Q40A1A1Sb7S58Vok;S73S58S62VAInv;VCST;VXGL;VKc;Sb2VCST;VFB;VFF;A3VFB;VFF;VBX;S5dS84AaS87Vrho0;R1A5Sb9S58S95Vrho0;R1S11bA5A4Ftp0;").
Proof.
  intros tp0.
  eapply triple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_sound_JA segs AInv CST XGL NPH Kc rho0 (P0_hf CST FB FF) FB FF BX PTrue HKc ALA FUEL_hf cutpcs_hfF NPH
                (map edropA cutsF2) (map edropA exitsF2) ok (Q tp0) Hok (ejcertA_jcertA segs NPH _ _ _ _ _ ejcertF_ok))
         with (ndT := nd0); [|left; reflexivity].
       intros X ndX rho tp Hin. apply in_map_iff in Hin as ([[X' nd'] rv] & E0 & Hin). cbn in E0. injection E0 as <- <-.
       apply (exits_okT (triple segs ok) (fun _ _ w => SPfamGTA segs (map nI (map edropA cutsF2)) w \/ Q tp0 w)
                (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok) (@triple_ex segs ok) (TRs_pureP segs ok) (fun P Q Q' HQ HT => @triple_conseq segs ok P P Q Q' (fun w Hw => Hw) HQ HT) (call_soundPA3 segs ok)) with (rvX := rv) (tp0 := tp0).
       - intros FBc FFc BXc rho1 tp1 HB0. apply (VNP.vec_reserveN_sum AInv CST XGL ALA HCST HXGL Kc HKc FBc FFc BXc HB0 rho1 ok Hok AC tp1).
       - intros FBc FFc BXc rho1 tp1 HB0. apply (PGP.tess_polygon_sum AInv CST XGL ALA HCST HXGL LFLAG LFSH Kc HKc FBc FFc BXc HB0 rho1 ok Hok AC).
         intros xx Hxx. apply SSC. cbn in Hxx |- *. tauto.
       - intros Ai rho1 tp1. apply (aca_stack_malloc _ _ _ _ _ AC 3 ltac:(cbn; tauto)); [exact HKc|]. eapply ok_frameA_of_K; [exact Hok|]. intros r p t m (_ & K & _). exact K.
       - intros Ai rho1 tp1. apply (aca_asan_memset _ _ _ _ _ AC); [exact HKc|]. eapply ok_frameA_of_K; [exact Hok|]. intros r p t m (_ & K & _). exact K.
       - intros Ai rho1 tp1. apply (aca_asan_memcpy _ _ _ _ _ AC); [exact HKc|]. eapply ok_frameA_of_K; [exact Hok|]. intros r p t m (_ & K & _). exact K.
       - intros Ai rho1 tp1. apply (SSC 245 ltac:(cbn; tauto)); [exact HKc|]. eapply ok_frameA_of_K; [exact Hok|]. intros r p t m (_ & K & _). exact K.
       - intros Cl s R rho1 tp1 nd Q' He Hc Hn Hb Hf Hk.
         apply (pure_callA segs AInv CST XGL NPH Kc rho0 (P0_hf CST FB FF) FB FF BX PTrue HKc ALA ok Cl Pre_pc s R Posts_pc rho1 tp1 nd Q'); try assumption.
         intros rho2 tp2. apply parse_corner_sum; [apply frozen_ok_frameA; exact Hok | apply (frozen_stable NF (ss_next (ax_S Cl)) nd rho1); [apply Pos.leb_le; exact Hn | exact Hb]].
       - intros Cl s R rho1 tp1 nd Q' He Hc Hn Hb Hf Hk.
         apply (pure_callA segs AInv CST XGL NPH Kc rho0 (P0_hf CST FB FF) FB FF BX PTrue HKc ALA ok Cl Pre_da s R Posts_da rho1 tp1 nd Q'); try assumption.
         intros rho2 tp2. apply diag_append_sum; [apply frozen_ok_frameA; exact Hok | apply (frozen_stable NF (ss_next (ax_S Cl)) nd rho1); [apply Pos.leb_le; exact Hn | exact Hb]].
       - intros T nd rv' rho1 tp1 b tp2 HinT _. apply (reenter_cutJA segs AInv CST XGL NPH Kc rho0 (P0_hf CST FB FF) FB FF BX PTrue ok (map edropA cutsF2) T nd).
         apply in_map_iff. exists (T, nd, rv'). auto.
       - intros P nd rho1 tp1 b tp2 HinP. apply (exit_postGA segs AInv CST XGL NPH Kc (P0_hf CST FB FF) FB FF BX PTrue ok rho0 tp0 nd Posts_hfJ P). exact HinP.
       - exact Hin. }
  intros w Hw. apply JA_pre_intro. exact Hw.
Qed.
End Safety.

Section Existence.
Hypothesis ACX : ltac2:(tb__ "0|0|
S154S58S14dVAInv;VCST;VXGL;A5").
Hypothesis SSCX : ltac2:(tb__ "0|0|
S0Sc5S0R1S2fS0Z0S2fS0Zf5S2fS0Zf8S30S0A1A3A3A3A3S1b5S58S14dVAInv;VCST;VXGL;R2A6F_;Fxx;").

Theorem handle_f_sum_ex : ltac2:(tb__ "0|0|
S2aS77Q40A1A1Sb6S58S73S58S62VAInv;VCST;VXGL;VKc;Sb2VCST;VFB;VFF;A3VFB;VFF;VBX;S5dS84AaS87Vrho0;R1A5Sb9S58S95Vrho0;R1S11bA5A3Ftp0;").
Proof.
  intros tp0.
  eapply etriple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_complete_JA segs AInv CST XGL NPH Kc rho0 (P0_hf CST FB FF) FB FF BX PTrue HKc ALA FUEL_hf cutpcs_hfF NPH cutsF2 exitsF2 (Q tp0) ejcertF_ok)
         with (ndT := nd0) (rv := (100, z0)); [|left; reflexivity].
       intros X ndX rv rho tp Hin.
       apply (exits_okT (etriple segs) (fun b _ w => SPfamETA segs (map (enodeIA AInv CST XGL NPH Kc rho0 (P0_hf CST FB FF) FB FF BX PTrue) cutsF2) b w \/ Q tp0 w)
                (TRe_facts segs) (TRe_ex segs) (TRe_pre segs) (@etriple_ex segs) (TRe_pureP segs) (fun P Q Q' HQ HT => @etriple_conseq segs P P Q Q' (fun w Hw => Hw) HQ HT) (call_completePA3 segs)) with (tp0 := tp0).
       - intros FBc FFc BXc rho1 tp1 HB0. apply (VNP.vec_reserveN_sum_ex AInv CST XGL ALA HCST HXGL Kc HKc FBc FFc BXc HB0 rho1 ACX tp1).
       - intros FBc FFc BXc rho1 tp1 HB0. apply (PGP.tess_polygon_sum_ex AInv CST XGL ALA HCST HXGL LFLAG LFSH Kc HKc FBc FFc BXc HB0 rho1 ACX).
         intros xx Hxx. apply SSCX. cbn in Hxx |- *. tauto.
       - intros Ai rho1 tp1. apply (acx_stack_malloc _ _ _ _ _ ACX 3 ltac:(cbn; tauto)). exact HKc.
       - intros Ai rho1 tp1. apply (acx_asan_memset _ _ _ _ _ ACX). exact HKc.
       - intros Ai rho1 tp1. apply (acx_asan_memcpy _ _ _ _ _ ACX). exact HKc.
       - intros Ai rho1 tp1. apply (SSCX 245 ltac:(cbn; tauto)). exact HKc.
       - intros Cl s R rho1 tp1 nd Q' He Hc Hn Hb Hf Hk.
         apply (pure_callA_ex segs AInv CST XGL NPH Kc rho0 (P0_hf CST FB FF) FB FF BX PTrue HKc ALA Cl Pre_pc s R Posts_pc rho1 tp1 nd Q'); try assumption.
         intros rho2 tp2. apply parse_corner_sum_ex. apply (frozen_stable NF (ss_next (ax_S Cl)) nd rho1); [apply Pos.leb_le; exact Hn | exact Hb].
       - intros Cl s R rho1 tp1 nd Q' He Hc Hn Hb Hf Hk.
         apply (pure_callA_ex segs AInv CST XGL NPH Kc rho0 (P0_hf CST FB FF) FB FF BX PTrue HKc ALA Cl Pre_da s R Posts_da rho1 tp1 nd Q'); try assumption.
         intros rho2 tp2. apply diag_append_sum_ex. apply (frozen_stable NF (ss_next (ax_S Cl)) nd rho1); [apply Pos.leb_le; exact Hn | exact Hb].
       - intros T nd rv' rho1 tp1 b tp2 HinT Hm. apply (ereenter_cutJA segs AInv CST XGL NPH Kc rho0 (P0_hf CST FB FF) FB FF BX PTrue cutsF2 T nd rv'); [exact HinT | exact Hm].
       - intros P nd rho1 tp1 b tp2 HinP. apply (eexit_postGA segs AInv CST XGL NPH Kc (P0_hf CST FB FF) FB FF BX PTrue rho0 tp0 nd Posts_hfJ P). exact HinP.
       - exact Hin. }
  intros w Hw. apply JA_pre_intro. exact Hw.
Qed.
End Existence.
End Sum.

Theorem handle_f_ok : handle_f_stmt.
Proof.
  intros AInv CST XGL ALA HCST HXGL LFLAG LFSH Kc HKc FB FF BX HBX rho0 ok Hok AC SSC tp0.
  exact (handle_f_sum AInv CST XGL ALA HCST HXGL LFLAG LFSH Kc HKc FB FF BX HBX rho0 ok Hok AC SSC tp0).
Qed.
Theorem handle_f_ok_ex : handle_f_stmt_ex.
Proof.
  intros AInv CST XGL ALA HCST HXGL LFLAG LFSH Kc HKc FB FF BX HBX rho0 ACX SSCX tp0.
  exact (handle_f_sum_ex AInv CST XGL ALA HCST HXGL LFLAG LFSH Kc HKc FB FF BX HBX rho0 ACX SSCX tp0).
Qed.

End Lib_handle_f_pf.

