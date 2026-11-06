(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nr o5.

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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require BudA TobjJA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.JcertCutA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs Lib_handle_l Lib_handle_l_s2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nr.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_l OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_l_s2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nr.Lib_handle_l_chk0.
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
Module Lib_handle_l_chk2.

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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs Lib_handle_l Lib_handle_l_s2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nr.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_l OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_l_s2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nr.Lib_handle_l_chk0.
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
Module Lib_handle_l_chk3.

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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs Lib_handle_l Lib_handle_l_s2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nr.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_l OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_l_s2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nr.Lib_handle_l_chk0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import HLAddr.
Lemma cc_13 : CC 13 T_fail0 = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_14 : CC 14 C_ck = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_15 : CC 15 C_cg = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_16 : CC 16 C_mk = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_17 : CC 17 C_mg = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_18 : CC 18 C_rlk = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_19 : CC 19 C_rlg = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End Lib_handle_l_chk3.

(* [comment removed for export] *)
Module Lib_handle_l_chk4.

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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs Lib_handle_l Lib_handle_l_s2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nr.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_l OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_l_s2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nr.Lib_handle_l_chk0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import HLAddr.
Lemma cc_20 : CC 20 C_fa0 = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_21 : CC 21 C_fa1 = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_22 : CC 22 XN = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_23 : CC 23 C_few = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_24 : CC 24 C_ok = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_25 : CC 25 T_keep2 = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_26 : CC 26 T_grown2 = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_27 : CC 27 T_fail2 = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_28 : CC 28 C_c2k = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_29 : CC 29 C_c2g = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_30 : CC 30 C_e8k = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_31 : CC 31 C_e8g = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_32 : CC 32 C_f2a = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_33 : CC 33 C_f2b = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_34 : CC 34 C_epf = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_35 : CC 35 C_epo = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_36 : CC 36 C_rlf = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cc_37 : CC 37 C_rlo = true. Proof. vm_cast_no_check (@eq_refl bool true). Qed.
End Lib_handle_l_chk4.

(* [comment removed for export] *)
Module Lib_handle_l_chk.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs"; "NPH"; "@Corelib.Init.Datatypes"; "bool"; "true"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_l_s2"; "cutsL"; "exitsL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_l"; "FUEL_hl"; "cutpcs_hl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.JcertCutA"; "ejcert_hdr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ejcertA"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs Lib_handle_l Lib_handle_l_s2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nr.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_l OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_l_s2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nr.Lib_handle_l_chk0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oa.Lib_handle_l_chk1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oa.Lib_handle_l_chk2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oa.Lib_handle_l_chk3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oa.Lib_handle_l_chk4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import HLAddr.

Lemma hdr_ok : ltac2:(tb__ "0|0|
S3S1S9S0S4A2S2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma ejcertL_ok : ltac2:(tb__ "0|0|
S3S1SaS6S0S7S8S0S4S5A7S2A3").
Proof.
  apply ejcertA_of_cuts; [exact hdr_ok|].
  change (cuts_okE segs FUEL_hl cutpcs_hl NPH PE 0 [Pre_hl; C_pro; C_pre; H; L1; L2; K; C_unp; T_pc; T_da; J; T_keep; T_grown; T_fail0; C_ck; C_cg; C_mk; C_mg; C_rlk; C_rlg; C_fa0; C_fa1; XN; C_few; C_ok; T_keep2; T_grown2; T_fail2; C_c2k; C_c2g; C_e8k; C_e8g; C_f2a; C_f2b; C_epf; C_epo; C_rlf; C_rlo] TG = true).
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
  apply cuts_okE_nil.
Qed.
End Lib_handle_l_chk.

(* [comment removed for export] *)
Module Lib_handle_l_pf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "or"; "True"; "ex"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "g8"; "has_facts"; "ax_base"; "leafA"; "la_state"; "ax_setS"; "entailsA"; "mkLeafA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "valuation"; "sprop"; "ss_facts"; "SLit"; "SPUle"; "ss_objs"; "holds"; "sobj"; "ss_next"; "sprop_eqb"; "swf"; "eval"; "SPEq"; "SVar"; "sv_below"; "SAlu"; "obj_range"; "soff"; "sprop_below"; "agree_below"; "cell"; "dflt_writable"; "odefault"; "@Corelib.Init.Datatypes"; "list"; "prod"; "bool"; "true"; "pair"; "cons"; "nat"; "nil"; "Some"; "None"; "option"; "fst"; "andb"; "snd"; "app"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "ANone"; "NDA"; "emeasA"; "PTrue"; "TPA"; "frinA"; "nd_below"; "tvinA"; "fbinA"; "ffinA"; "JA_pre"; "JA"; "JLA"; "fr_sub_eqb"; "frozen"; "nodeIA"; "ok_frameKA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@stdpp.bitvector.definitions"; "bv"; "@Stdlib.ZArith.BinInt.Z"; "le"; "pow"; "lt"; "mul"; "sub"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "smatchA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_l"; "fr_hl"; "pQ"; "pK"; "pD"; "X_hl"; "tv_hl"; "nd0"; "E_da0"; "E_pc0"; "E_unp0"; "E_vr0"; "Pre_hl"; "R_v"; "X_r2g"; "X_r2k"; "X_rpg"; "X_rpk"; "E_sm0"; "E_vr"; "L_sm"; "PD_vn"; "Pre_sm"; "X_pro"; "Xk_v"; "pC"; "pC1"; "pT0"; "s_v"; "slot_facts"; "xf_cm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs"; "NPH"; "hG"; "hF"; "tE"; "kb"; "lc_d"; "lc_k"; "tL"; "PROG"; "lc_c"; "tB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oa.Lib_handle_l_pf"; "P0_hl"; "bF"; "P0_hl_b"; "fF"; "vrF"; "DW_rng"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_l_s2"; "VR"; "cutsL"; "epi_state"; "ndJ"; "tvN"; "z0"; "ndG"; "ndK"; "ndT"; "tvL"; "C_epf"; "P_fail"; "P_ok"; "R_v2"; "ndN"; "ndX"; "ndX2"; "nd_fail"; "nd_ok"; "E_da2"; "E_vc"; "E_vc0"; "X_e8g"; "X_e8k"; "X_f2a"; "X_f2b"; "X_f7a"; "X_f7b"; "X_fp0"; "X_fp1"; "X_ok0"; "X_rlf"; "X_rlo"; "Xk_v2"; "bdL"; "exitsL"; "lcc1"; "ndEf"; "ndEo"; "ndF"; "ndNs"; "ndO"; "ndOg"; "ndP"; "s_v2"; "sel_rel"; "slot4_facts"; "tvY"; "xf_e8"; "yCUR"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "firstn"; "skipn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "uval"; "bitem"; "BXok_d"; "bd_subst"; "bd_wpos"; "bud_le"; "bxt"; "@Stdlib.Lists.List"; "In"; "existsb"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o1.Lib_builderH_pf"; "extraOH"; "extraXH"; "extraOH_client"; "frozen_stableH"; "payA_sameH"; "siteFH"; "siteHH"; "sitePH"; "siteXH"; "site_pureH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_l.HLAddr"; "DW"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "entails_frA"; "call_checkA"; "import_postA"; "J_ofPA"; "call_checkPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "etriple"; "triple";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "call_linkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS"; "robjs_checkF"; "shadow_reopen_stateA"; "xrs_checkL"; "release_objs_ok"; "shadow_release_stateA"; "shobj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "topG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "SHADOW_OFF"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "tvd"; "tvz"; "T_ok"; "FBx"; "remove_nth"; "tv_sub_eqb"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oa.Lib_handle_l_pf.Sum"; "HNPH"; "Posts_hlJ"; "JLh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "rho_sub"; "wsub"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ny.Lib_builder_pf"; "baseF"; "P0_builder"; "basez"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "axform"; "AXSelect"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oa.Lib_handle_l_pf.VNP"; "P0_vr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve"; "B32"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "FFx"; "pclMA"; "xrs_inclb"; "robjs_okF"; "xrs_okF"; "PostsC"; "xrs_okL"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "jnodeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_setX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA"; "infrFF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "ccount"; "is_shadowZ"; "payA"; "robjs_okA"; "site_okA"; "xrs_okA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAT"; "robjs_checkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "AE_A"; "JL_stack_malloc"; "J_stack_malloc_pre"; "alloc_contractsA"; "alloc_contractsA_ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs"; "vAL"; "vb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oa.Lib_handle_l_pf.Sum.X"; "pure_rule"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oa.Lib_handle_l_pf.VN"; "Pre_vr"; "nd0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double"; "two26"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsSymJump"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3"; "import_okPA3"; "import_postA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR"; "robjs_okF"; "xrs_ok47"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ny.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_handle_l Lib_handle_l_s2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nn.Lib_vec_reserve_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ny.Lib_builder_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o1.Lib_builderH_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_l OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_handle_l_s2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o5.Lib_handle_l_eqs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.oa.Lib_handle_l_chk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Import ScanDoubleAddr VRAddr RA.ReallocAddr ParseCornerAddr DiagAppendAddr HLAddr.
Close Scope bv_scope.
Open Scope Z_scope.
Module VN. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n9.Lib_vec_reserveN. End VN.
Module VNP. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nu.Lib_vec_reserveN_pf. End VNP.

Definition P0_hl (CST : list (Z * Z)) (FB : list (Z * Z)) (FF : list (Z * Z * Z)) (r : valuation) : Prop := ltac2:(tb__ "0|1|
S1SfcVCST;VFB;VFF;Vr;A4S0S31S114Z1SbaS2cS2cS6S6A2M0S6A2G0S36G0S6A2VFF;A4A2U0A3A2").
Lemma P0_hl_b : ltac2:(tb__ "0|2|
S2bS2cS6S6A2M0A1M1G1S2bS2cG0S6A2A1S14S81R4R3R2R1A4SfcR5R4R3R2A4F_;Fr;FFF;FFB;FCST;").
Proof. intros CST FB FF r [H _]. exact H. Qed.

Definition bF (F : list sprop) : bool := baseF DW F.
Definition fF (F : list sprop) : bool := frameF hG 160 128 F.
Lemma DW_rng : 0 <= DW < 2 ^ 40. Proof. unfold DW. lia. Qed.
Lemma sz_rng : 0 <= 128 < 2 ^ 40. Proof. lia. Qed.

Definition vrF (q : sv) (F : list sprop) : bool := ltac2:(tb__ "0|0|
S37S37Sc5S15S1dS18Vq;S79A2A1VF;A3Sc5S15S1dS18S79S7dA2A1VF;A3A2Sc5S15S1dS18S7dS17S126A1A2A1VF;A3A2").
Lemma VR_val : ltac2:(tb__ "0|3|
S14S2bS15A1S13S6Sb9S15S1aR4A1R3A3S0S2dS85R3R4A2S2eA3S1S4eZ0M0R3A2S50R3Z40M1A2A2S1S0S6SbdR7S87R5R4A2A2S53S51G1S52SbdR7S79A2SbdR7R5A2A2M2A2R4A2A3S1S4eG0G2A2S4eG2S4fZ2Z1aA2A2A2A2F_;F_;F_;Fa;Fq;FF;Frho;").
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
S14S14S2bS15A1S13S6S6Sb9S15S1aR6A1R4A3S0S2dS85R4R5A2S2eA3S0S4dQ40A1M0S1fR7S79A2S1fR8S79A2A3S0G0S1fR8R6A2S1fR9R6A2A3S4eZ0M1R6A2S50R7R6A2S50R7Z40A2S1S4eG1SbdRcS87RaR9A2A2M2A2S50G2SbdRdS87RaR8A2A2A2A2F_;F_;F_;F_;F_;F_;F_;Fb;Fa;Fq;FF;Frho';Frho;").
Proof.
  intros rho rho' F q a b HF HV H1 H2 Ha Hab Hb.
  assert (EQ : uval rho' (VR q a) = uval rho (VR q a)).
  { unfold uval, VR, kb. cbn [eval]. rewrite H1, H2. reflexivity. }
  rewrite EQ. destruct (VR_val rho F q a HF HV ltac:(lia)) as [-> R1]. destruct (VR_val rho F q b HF HV ltac:(lia)) as [-> _]. lia.
Qed.

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
Se7S14S2bS4dQ40A1A1Sd2OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : alloc_lawsA segs AInv CST.
Hypothesis HCST : ltac2:(tb__ "0|0|
S6S120VCST;R1A2S1S4eZ0R2A2S50R2SebA2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S6S120VXGL;R1A2S1S4eZ0R2A2S50R2SebA2A2F_;Fa;").
Hypothesis LFLAG : law_flag_stmt AInv.
Hypothesis LFSH : law_fshadow_stmt AInv.
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S2bS2cS2cS6S6A2S6A2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 5 BX.
Let HNP : NP_okA NF := NP_okA_intro NF eq_refl.
Variable rho0 : valuation.
Let HTOP : InitState.segs_top segs <= IMG_HI := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nn.Lib_arena_alloc.HTOP_ok.
Lemma HNPH : (NF <= NPH)%positive. Proof. unfold NF, NPH. lia. Qed.

Definition JLh (nd : ndesc) : jpostA := ltac2:(tb__ "0|0|
S47VAInv;VCST;VXGL;VKc;S81VCST;VFB;VFF;A3VFB;VFF;VBX;S3eVnd;Aa").
Definition Posts_hlJ : list (axst * jpostA) := ltac2:(tb__ "0|1|
S30S2cS8Sd4A2M0S2fS8Sd4S92Sf5S98A1A4S30G0S2fS8Sd4S93Sf5S99A1A4S32G0A1A3A3").
Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S46VAInv;VCST;VXGL;S76VKc;Vrho0;S81VCST;VFB;VFF;A3VFB;VFF;VBX;S3eVnd;Ac").
Let nI : ltac2:(tb__ "0|0|
S2cS8S3aA2S110Fn;") := ltac2:(tb__ "0|0|
S4aVAInv;VCST;VXGL;S76VKc;Vrho0;S81VCST;VFB;VFF;A3VFB;VFF;VBX;S3eAb").
Let Q (tp0 : list word) : assn := ltac2:(tb__ "0|0|
Sd5S4cS76Vrho0;Vtp0;Sf4A5").

Let siteP : ltac2:(tb__ "0|0|
Se7S14S2bS15A1S2bS2cS13S13A2A1S2bS2cS2cS13S6A2S13A2A1S35S31A1S2bS1bA1S14S2bS4dQ40A1A1Sd2VAInv;RaR3R2R1A4Sb9S15S1aRaA1R9A3S0S2dSfbSd1RaA2S2eA3SdfS76Vrho0;RcA3S81VCST;VFB;VFF;Vrho0;A4S3fVrho0;RfA2SeeRfSe9Se8R10A1A1A2S43VFB;R11A2S44VFF;R12A2S42VFB;R13R12R10A4SecR13R11A2SedR14R12A2S40VFF;R16R15R12A4S0S2dS11aR15R14R13R12Sc7R11A6S2eA3S117VCST;R18S34S6A1R17R12A5F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FR;Fskip;Ffr;Ftv;Ffacts;Frho;FAi;") := ltac2:(tb__ "0|0|
SceVAInv;VCST;VALA;S76Sf3VFB;VFF;Vrho0;S81VCST;VFB;VFF;A3S83VCST;VFB;VFF;A3Sd1S86Ac").
Let siteF : ltac2:(tb__ "0|0|
Se7S14S2bS15A1S2bS2cS13S13A2A1S2bS2cS2cS13S6A2S13A2A1S2bS1bA1S14S2bS4dQ40A1A1Sd2VAInv;R9R3R2R1A4Sb9S15S1aR9A1R8A3S0S2dSfbSd1R9A2S2eA3SdfS76Vrho0;RbA3S81VCST;VFB;VFF;Vrho0;A4S3fVrho0;ReA2SeeReSe9Se8RfA1A1A2S42VFB;R10RfRdA4SecR10ReA2SedR11RfA2S40VFF;R13R12RfA4S0S2dSe1R12R11R10S34S31A1Sc7RfA6S2eA3S12cVCST;Vrho0;VFB;VFF;R14R12R11R10A8F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FR;Ffr;Ftv;Ffacts;Frho;FAi;") := ltac2:(tb__ "0|0|
SccVAInv;VCST;VALA;S76Sf3VFB;VFF;Vrho0;S81VCST;VFB;VFF;A3S83VCST;VFB;VFF;A3Sd1S86Ac").
Let siteH : ltac2:(tb__ "0|1|
Se7S14S2bS15A1S2bS2cS13S13A2A1S2bS2cS2cS13S6A2S13A2A1S2bS1bA1S14S2bS4dQ40A1A1Sd2VAInv;R9R3R2R1A4Sb9S15S1aR9A1R8A3S0S2dSfbSd1R9A2S2eA3SdfS76Vrho0;RbA3S81VCST;VFB;VFF;Vrho0;A4S3fVrho0;ReA2SeeReSe9Se8RfA1A1A2S42VFB;R10RfRdA4SecR10ReA2SedR11RfA2S40VFF;R13R12RfA4S0S2dSe1R12R11R10S34S31A1Sc7RfA6S2eA3S1bS6Sc4S1bR2R12A3S1S4eS36S6S6S24R17R3A2M0A3R2A2S50R2S38S6S6G0A3A2A2S3S104VCST;Vrho0;SefVFB;R18R16A3S103VFF;R18R15A3R3A5S3S1S4eZ0R3A2S50R3SebA2A2S115R3A1A2A2F_;F_;Fa;Fo;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FR;Ffr;Ftv;Ffacts;Frho;FAi;") := ltac2:(tb__ "0|0|
ScdVAInv;VCST;VALA;S76Sf3VFB;VFF;Vrho0;S81VCST;VFB;VFF;A3S83VCST;VFB;VFF;A3Sd1S86Ac").
Let siteX : ltac2:(tb__ "0|4|
Se7S14S2bS15A1S2bS2cS13S13A2A1M0S2bS2cS2cS13S6A2S13A2M1A1M2S35S31A1M3S2bS1bA1G0S14S2bS4dQ40A1A1Sd2VAInv;RbR3R2R1A4Sb9S15S1aRbA1RaA3S0S2dSfbSd1RbA2S2eA3SdfS76Vrho0;RdA3S81VCST;VFB;VFF;Vrho0;A4S3fVrho0;R10A2SeeR10Se9Se8R11A1A1A2S43VFB;R12A2S44VFF;R13A2S42VFB;R14R13R11A4SecR14R12A2SedR15R13A2S40VFF;R17R16R13A4S0S2dSe3VXGL;R16R15R14R13R12Sc8R11A8S2eA3S1S109VCST;VXGL;Vrho0;VFB;VFF;R18R16G3G2Lskip;R14S31Sf0G1R1R16A3Li;R15X35x2R12A9S1S119VCST;VXGL;R19S34S6A1R18R12A6S12dR18R12A2A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FX;Fobjs;Fskip;Ffr;Ftv;Ffacts;Frho;FAi;") := ltac2:(tb__ "0|0|
ScfVAInv;VCST;VXGL;VALA;VHCST;VHXGL;S76Sf3VFB;VFF;Vrho0;S81VCST;VFB;VFF;A3S83VCST;VFB;VFF;A3Sd1S86Af").
Let site_pure : ltac2:(tb__ "0|2|
S8Sf8S2bS1bA1S14S2bS2cS13S13A2A1S2bS2cS2cS13S6A2S13A2A1S2bSbeA1S0S2dSfbSd1S16S9R7A1A1A2S2eA3S0S2dS11aS16S9R8A1A1R4R3S34S31A1M0Sc7R6A6S2eA3S0S2dSe3VXGL;S16S9R9A1M1A1R5R4G0S19G1A1Sc8SaR9A1A8S2eA3S118VAInv;VCST;VXGL;S76Vrho0;S81VCST;VFB;VFF;A3VFB;VFF;RaR9R8R7S3cR6R5R4S3bA4S34S6A1Se7Sf2S4L_;L_;AfF_;F_;F_;Fbd;Ffr;Ftv;Frho;FR;Fs;FE;") := ltac2:(tb__ "0|0|
Sd0VAInv;VCST;VXGL;VALA;VHCST;VHXGL;S76Sf3VFB;VFF;Vrho0;S81VCST;VFB;VFF;A3S83VCST;VFB;VFF;A3Sd1S86Af").
Let payA_same : ltac2:(tb__ "0|1|
S2bS15A1S2bSbeA1S0S2dSc1R1A1S2eA3S116S76Vrho0;S81VCST;VFB;VFF;A3R3S17Z0M0A1G0R2R2A8F_;Fbd;Ffacts;") := ltac2:(tb__ "0|0|
ScbS76Vrho0;S81VCST;VFB;VFF;A3A3").
Let frozen_stable : ltac2:(tb__ "0|0|
S7S7S3aS14S10eS76R3A2S0S2dS41R4R3A2S2eA3S57S4cR6S49VAInv;VCST;VXGL;S76VKc;Vrho0;S81VCST;VFB;VFF;A3VFB;VFF;VBX;S3eR4R3AdA3F_;F_;Frho;Fnd;Fm;Fn;") := ltac2:(tb__ "0|0|
ScaVAInv;VCST;VXGL;VALA;S76VKc;VHKc;VFB;VFF;VBX;Vrho0;S81VCST;VFB;VFF;A3Ac").
Let extra_client : ltac2:(tb__ "0|1|
S14S1bS6S2bS2cS13S13A2A1S2bS2cS2cS13S6A2S13A2A1SfdSd1R5A2SdfS76Vrho0;R6A3S81VCST;VFB;VFF;Vrho0;A4S0S2dSc7R7A1S2eA3S1S4eS36S6S6S24R9R8A2M0A3R7A2S50R7S38S6S6G0A3A2A2S104VCST;Vrho0;SefVFB;RaR7A3S103VFF;RaR6A3R8A5F_;F_;F_;F_;F_;Ffrs;Fkept;Fa;Fo;Frho;") := ltac2:(tb__ "0|0|
Sc9VCST;S76Sf3VFB;VFF;Vrho0;S81VCST;VFB;VFF;A3S83VCST;VFB;VFF;A3Sd1A9").

Lemma P0_now : ltac2:(tb__ "0|2|
S14SdfS76Vrho0;R1A3S81VCST;VFB;VFF;Vrho0;A4S1S6S1S4eSbdR4S80A2M0R1A2S50R1S53G0SbdR4S7dA2A2A2A2S104VCST;Vrho0;VFB;VFF;R2A5F_;Fa;S1S113VFF;SbdR3S122A2Z518A3S1S113VFF;SbdR3S121A2Z30A3S0S31S114Z1SbaS2cS2cS6S6A2M1S6A2G1S36G1S6A2VFF;A4A2U0A3A2A2A2F_;F_;Frho;").
Proof.
  intros rho Hav HP. destruct (P0b_nowH CST NPH HNPH FB FF rho0 (P0_hl CST FB FF) (P0_hl_b CST FB FF) rho Hav HP) as (A & B & C).
  destruct HP as [_ D]. auto.
Qed.

Lemma JA_tv_swap2 : ltac2:(tb__ "0|1|
S2cS13S13A2M0G0S2bG0A1S2bS2cS2cS13S6A2S13A2A1S2bSbeA1S14S2bS4dQ40A1A1S2bSd3A1Sd2VJAv;S3cS30G0R9S30G0R8R7A3A3R6R5S3bA4R4R3R2R1A5VJAv;S3cS30G0R9S30G0RaR8A3A3R7R6S3bA4R5R4R3R2A5F_;Fmd;Ftr;Ftp;Frho;Fbd;Ffr;Fr;Fb;Fa;").
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
S2cS13S13A2M0G0S2bG0A1S2bS2cS2cS13S6A2S13A2A1S2bSbeA1S8S14S2bS4dQ40A1A1SdcS54S4cVJAv;S3cS30G0R9S30G0R8R7A3A3R6R5S3bA4A1R4R3R2R1A6S54S4cVJAv;S3cS30G0R9S30G0RaR8A3A3R7R6S3bA4A1R5R4R3R2A6F_;Fw;Ftp;Frho;FS;Fbd;Ffr;Fr;Fb;Fa;").
Proof. intros a b r fr bd S rho tp w [Hsm HJ]. split; [exact Hsm | apply JA_tv_swap2; exact HJ]. Qed.

Lemma tvz_kd : ltac2:(tb__ "0|2|
S14S6S13S13S2bS2cS13S13A2M0A1SedR5S30G0S2fS13S13R3S7aR4R2A2A4R1A3A2S1S50Z0M1R5A2S4eR5ZcA2A2S4eSbdR7R4A2S102A2S2S0S6SbdR8R5A2G1A3A1S2S0S6SbdR9R7A2G1A3A1F_;F_;F_;F_;Fr;Fk;Fd;Fe;Frho;").
Proof.
  intros rho e d k r HZ He HK Hk Hd. apply Forall_inv in HZ. unfold tnz, tvv in HZ. cbn [fst snd] in HZ. unfold uval in Hd, Hk, HK.
  specialize (HZ ltac:(intros H; exact (H Hd))). unfold B32 in HK.
  pose proof (uval_mul_lit rho e k ltac:(lia) ltac:(unfold uval; nia)) as E12. unfold uval, kb in E12. unfold kb in HZ. rewrite E12 in HZ. nia.
Qed.

Lemma slot_holds : ltac2:(tb__ "0|1|
S14S2bS15A1S13Sb9S15S1aR3A1R2A3S0S2dSc5S15S1dS18S71R2A2A1R3A3S2eA3S0S2dSc5S15S1dS18R3S17S102A1M0A2A1R4A3S2eA3S0S2dSc5S15S1dS18S70R4A2A1R5A3S2eA3S0S2dSc5S15S1dS18S7aZcR5A2G0A2A1R6A3S2eA3Sb9S15S1aR8A1S74R6A1A3F_;F_;F_;F_;F_;Fk;FF;Frho;").
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
Lemma slot4_holds : ltac2:(tb__ "0|1|
S14S2bS15A1S13Sb9S15S1aR3A1R2A3S0S2dSc5S15S1dS18SabR2A2A1R3A3S2eA3S0S2dSc5S15S1dS18R3S17S102A1M0A2A1R4A3S2eA3S0S2dSc5S15S1dS18S7fR4A2A1R5A3S2eA3S0S2dSc5S15S1dS18S7aZ4R5A2G0A2A1R6A3S2eA3Sb9S15S1aR8A1Sb5R6A1A3F_;F_;F_;F_;F_;Fk;FF;Frho;").
Proof.
  intros rho F k HF H1 H2 H3 H5.
  pose proof (holds_mem _ _ _ HF H1) as F1. pose proof (holds_mem _ _ _ HF H2) as F2. pose proof (holds_mem _ _ _ HF H3) as F3. pose proof (holds_mem _ _ _ HF H5) as F5.
  rewrite h_ule in F1, F2, F3, F5. unfold B32 in *. rewrite uval_lit in F2 by lia. rewrite uval_lit in F5 by lia.
  pose proof (uval_range rho lc_c) as RC. pose proof (uval_range rho k) as Rk.
  unfold lcc1 in F1. rewrite uval_add_litZ in F1 by lia.
  assert (E4k : uval rho (kb 4 k) = 4 * uval rho k) by (unfold kb; apply uval_mul_lit; lia). rewrite E4k in F5.
  assert (E4c : uval rho (cmul4 lc_c) = 4 * uval rho lc_c) by (unfold cmul4; rewrite uval_mul_comm; apply uval_mul_lit; lia).
  unfold slot4_facts.
  constructor; [|constructor; [|constructor; [|constructor]]]; rewrite h_ule.
  - rewrite uval_add_litZ by (rewrite ?E4c; lia). rewrite E4c, E4k. lia.
  - rewrite E4c, E4k. lia.
  - unfold B32. rewrite E4c, uval_lit by lia. lia.
Qed.

Lemma foff_rng : ltac2:(tb__ "0|0|
S14S2bS15A1S6Sb9S15S1aR3A1R2A3S0S2dS84R3A1S2eA3S1S4eZ0R3A2S4eR3Z80A2A2S0S6SbdR6S23S10cS78S17R4A1A3A2S53SbdR6S78A2R4A2A3F_;F_;F_;Foff;FF;Fr;").
Proof. intros r F off HF HFR Ho. unfold hF. apply (frame_off_rng hG 160 128 off r F sz_rng Ho HF HFR). Qed.
Lemma slot_rng : ltac2:(tb__ "0|1|
S14S2bS15A1S13S13S6S1S4eZ0R1A2S4eR1ZcA2A2Sb9S15S1aR6A1R5A3S0S2dSc5S15S1dS18R5S17Z800000000000A1A2A1R6A3S2eA3S0S2dSc5S15S1dS18R5S17S102A1A2A1R7A3S2eA3S1S0S6SbdR9S23S10cR7R6A3A2S53SbdR9R7A2SbdR9R6A2M0A2A3S1S0S6S25R9R6A2G0A3S0S6S25R9S23S10cR6S17R5A1A3A2S53G0R5A2A3A2A2F_;F_;F_;F_;Fw;Fcm;Fd;FF;Fr;").
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
S6S2bS4dQ40A1A1SdbF_;F_;").
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S55S8S14S2bS4dQ40A1A1SdbSb9S15S1aR3A1S16S9R4A1A1A3VTR;S54S4cR6R5R4R3A5R2A2M0F_;G0F_;FQ;Ftp;Frho;FS;FJ;").
Hypothesis TR_ex : forall (T : Type) (J : T -> jpredA) S rho tp (Q : assn),
  (forall x, TR (SPA segs (J x) S rho tp) Q) -> TR (SPA segs (fun r p t m => exists x, J x r p t m) S rho tp) Q.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
SdbSdbSdbSdcR3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_exw : forall (T : Type) (P : T -> assn) (Q : assn), (forall a, TR (P a) Q) -> TR (fun w => exists a, P a w) Q.
Hypothesis TR_pureP : ltac2:(tb__ "0|1|
SdbOSdbSdcR4R1A1R4F_;Fw;R3VTR;R5R3A2M0F_;G0F_;F_;FQ;FX;FP;").
Hypothesis TR_callP : ltac2:(tb__ "0|5|
S55S55S8S8Sf8S2bS1bA1M0S2bS2cS8Sd4A2M1A1S2bS2cS13S13A2M2A1SdbS14S2bS4dQ40A1A1M3G2Sc4G2R1R5A3Sc4G2R2SaRbA1A3F_;Fr;S0S35G0A1Sd6RaR9R8A3S33G0R7A2A3S0S2dSdaRbRaR9R8SbaG1S8S36S8Sd4A2R7A4A5S2eA3S14G3VTR;S54S4cRfRdR2R1A5Sd5S4cS1cS9RdA1A1R2R1RaA5A2Ftp1;Frho1;S2bSd3A1M4Sf2Sd2S56S4cR9R8R10S2fG4S10aR3S10bR2R1A2A4A5R13RaR9R4R2A4R13Sf7Sf6RbRfSfaR3RaR4A3A3R10A2RaR5R3A4F_;F_;Fmd;Fms;Ftr;S8Sd4G4Sf2Sd2S14G3G4Sf2Sd2Sc4G1S2fS8Sd4RaR9A4R14A3S56S4cR12R11R19S2fG4S10aR9S10bR8R7A2A4A5R1cR13R12RaR8A4SdfS1cS9R1aA1A1Sf7Sf6R14R18SfaR9R13RaA3A3R19A2R8A3S56S4cR9R8ReS2fG4S10aR7S10bR6R5A2A4A5ReSf7Sf6R16R1aSfaRbR15RcA3A3R1bA2R15RaR9R8R6A6S1S12aR17SfaRcR16RdA3R1bR1cR1dR10R1eR19RbA9S14Se0R18SfaRdR17ReA3R1cR1dS9R1eA1S9R1fA1S9R11A1R1RcA9VTR;S54S4cSd9R11Sf7Sf6R19R1dSfaReR18RfA3A3R1eA2R18RdRcA5S12bR1eR1fR12R20R1dR1bA6R2RcA5R1aA2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S54S4cR11RfR8R7A5R9A2F_;F_;F_;F_;F_;F_;Ftp;Frho;FQ;FXk;FPosts;FR;Fs;FPre;FC;FJp;FJ;").

Hypothesis CVRESN : ltac2:(tb__ "0|1|
S2bS2cS6S6A2M0A1S2bS2cG0S6A2A1Sc3S14S2bS4dQ40A1A1SbfZ3R3A2VTR;S54S4cS45VAInv;VCST;VXGL;VKc;S101R6R5A2R6R5R4S3eS125AaS124R3R2A5Sd5S4cS112R3R2S108VAInv;VCST;VXGL;VKc;S101S3eS6cR6R5R4AaA5A2F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Hypothesis CSM : ltac2:(tb__ "0|2|
Se7S14S2bS4dQ40A1A1VTR;S54S4cS11dVAInv;Z1M0R3VKc;A4S6dR2R1A5Sd5S4cS112R2R1S30S2cS8Sd4A2M1S2fS8Sd4S6bS11cVAInv;VCST;VXGL;G0R3VKc;A6A4S32G1A1A3A5A2Ftp1;Frho1;FAi;").

Definition pure_rule (Pre : axst) (Posts : list leafA) : Prop := ltac2:(tb__ "0|2|
S8Sf8S2bS1bA1M0S14S2bS4dQ40A1A1S3aSdbS0S35G0A1Sd6R7VPre;R6A3S33G0R5A2A3S0S2dSd7R8VPre;R7R6SbaSeS8SfVPosts;A4A5S2eA3S0S2dS10dS76S1cS9R9A1A1A2S2eA3S0S2dS41S1cS9RaA1A1R5A2S2eA3S0S2dSc6S15S26S1cS9RbA1M1A1A1S16G1A1A3S2eA3SeS14Sc4SeR2VPosts;A3S27S1cS9RfA1A1RcR2A3VTR;S54S4cVJAv;RbA1S10fS16S9R10A1A1Sd8RfVPre;SfR4A1R10ReA5A2R3RcA5RaA2F_;F_;Frho';FL;VTR;S54S4cVJAv;R8A1RdRaR9A5R7A2F_;F_;F_;F_;F_;F_;FQ;Fnd;Ftp;Frho;FR;Fs;FCl;").
Hypothesis CALL_pc : pure_rule Pre_pc Posts_pc.
Hypothesis CALL_da : pure_rule Pre_da Posts_da.
Hypothesis REENTER : ltac2:(tb__ "0|4|
S8S3aS2cS6S13A2M0S14S2bS4dQ40A1A1M1S6G1Sc4S2cS2cS8S3aA2M2G0A2S2fG2G0S2fS8S3aR7R6A4R5A4S88A3S1S4eZ0S3dS2fG2G0S2fS8S3aR8R7A4R6A4R5A2M3A2S50G3R3A2A2VTR;S54S4cVJAv;R8A1R9R6R5A5VFAM;R4R3A2A2F_;F_;Ftp0;Fb;Ftp;Frho;Frv;Fnd;FT;").
Hypothesis POST : ltac2:(tb__ "0|1|
S8S3aS14S2bS4dQ40A1A1M0S6G0Sc4S2cS8Sd4A2S2fS8Sd4R6Sf5R5A1A4Sf4A3VTR;S54S4cVJAv;R6A1R7R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;Fnd;FP;").

Ltac meas := unfold emeasA; cbn [eda_rank eda_var fst snd z0 eval]; rewrite lit_unsigned; cbn; lia.

Ltac vmr := first [ lazymatch goal with |- @eq ?T ?t ?v => tryif first [ has_evar t | has_evar v ] then fail else vm_cast_no_check (@eq_refl T v) end
                  | vm_compute; reflexivity ].
Tactic Notation "innth" integer(n) := cbn [In cutsL exitsL Posts_hlJ PD_vr PD_vn]; do n right; left; reflexivity.

Lemma loop_meas : ltac2:(tb__ "0|5|
S14S14S2bS15A1S7S6S6S8S8S3aS3aSb9S15S1aRaA1R8A3S0S2dS85S59R9A2S2eA3SdfR9RcRbA3S0S2dS22RaS79A2S2eA3S0S2dS22RbS59A2S2eA3S4eZ0M0RbA2S50RcRbA2S50RcZ40A2S1S4eG0S3dS2fS2cS8S3aA2M1S2cS6S13A2M2S2fS8S3aRbR9A4S2fS6S13Z50M3S87S59ReA2A4A4R11A2M4A2S50G4S3dS2fG1G2S2fS8S3aRcRaA4S2fS6S13G3S87S59RdA2A4A4R12A2A2A2F_;F_;F_;F_;F_;F_;F_;F_;FndT;FndX;FT;FX;Fb;Fa;Fn;FF;Frho';Frho;").
Proof.
  intros rho rho' F n a b X T ndX ndT HF HV Hag HbE HbQ Ha Hab Hb. unfold emeasA. cbn [eda_rank eda_var fst snd].
  pose proof (VR_meas rho rho' F pQ a b HF HV (eq_sym (eval_agree_vals n rho rho' tE Hag HbE)) (eq_sym (eval_agree_vals n rho rho' pQ Hag HbQ)) Ha Hab Hb) as M.
  unfold uval in M. lia.
Qed.
Lemma loop_meas_same : ltac2:(tb__ "0|5|
S14S2bS15A1S6S6S8S8S3aS3aSb9S15S1aR8A1R7A3S0S2dS85S59R8A2S2eA3S4eZ0M0R8A2S50R9R8A2S50R9Z40A2S1S4eG0S3dS2fS2cS8S3aA2M1S2cS6S13A2M2S2fS8S3aR8R6A4S2fS6S13Z50M3S87S59RbA2A4A4RdA2M4A2S50G4S3dS2fG1G2S2fS8S3aR9R7A4S2fS6S13G3S87S59RaA2A4A4RdA2A2A2F_;F_;F_;F_;F_;FndT;FndX;FT;FX;Fb;Fa;FF;Frho;").
Proof.
  intros rho F a b X T ndX ndT HF HV Ha Hab Hb. unfold emeasA. cbn [eda_rank eda_var fst snd].
  pose proof (VR_meas rho rho F pQ a b HF HV eq_refl eq_refl Ha Hab Hb) as M. unfold uval in M. lia.
Qed.
Lemma emeas_z0 : ltac2:(tb__ "0|0|
S8S3aS6S14S0S6S3dS2fS2cS8S3aA2S2cS6S13A2S2fS8S3aR4R3A4S2fS6S13R2S8cA4A4R1A2S51R2S4fZ2Z40A2A2A3Frho;Fr;Fnd;FT;").
Proof. intros. unfold emeasA. cbn [eda_rank eda_var fst snd z0 eval]. rewrite lit_unsigned by lia. lia. Qed.
Lemma emeas_eq : ltac2:(tb__ "0|1|
S8S3aS6S13S14S14S13S0S4dQ40A1S1fR2R1A2S1fR3R1A2A3Fe;S0S6S3dS2fS2cS8S3aA2S2cS6S13A2S2fS8S3aR7R6A4S2fS6S13R5R4A4A4M0R2A2S3dG0R3A2A3F_;Frho';Frho;Fv;Fr;Fnd;FT;").
Proof. intros. unfold emeasA. cbn [eda_rank eda_var fst snd]. rewrite H. reflexivity. Qed.

Lemma X_reopen : ltac2:(tb__ "0|7|
S8S8S2bS2cS13S13A2A1S2bSbeA1S6S6S14S2bS4dQ40A1A1M0S6G0S2cS6S13A2M1S0S13SdRbA1S17SeaA1A3S4eZ0M2R8A2S1S4eR9R8A2S4eR8Z10A2A2S0S2dScS30S15S20SbS77A1S78A2S30S15S18S21S77A1S17S52S4fZ2Z3dA2Z1A2A1A2S32S15A1A3A3S16S9ReA1A1A2S2eA3S0S2dS1eS9Se2RfSaRfA1S77RbRaA5A1A1S2eA3S0S2dS82S16S9R10A1A1A1S2eA3S0S2dSe1S16S9R11A1M3A1RfS58S34S31A1Sc7S19G3A1A6S2eA3S0S2dSe3VXGL;S16S9R12A1M4A1R10S58S33S31U0A2S19G4A1Sc8SaR12A1A8S2eA3S0S8Se2R13SaR13A1S77RfReA5R12A3Sc4S2cS2cS8S3aA2M5G1A2S2fG5G1S2fS8S3aR13S3cR12S58R11S3bA4A4RaA4S88A3S1S4eG2S3dS2fG5G1S2fS8S3aR14S3cR13S58R12S3bA4A4RbA4RfA2M6A2S50G6RdA2A2VTR;S54S4cVJAv;S3cR14S58R13S3bA4A1R16R10RfA5VFAM;ReRdA2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Frv;Ftp0;Fb;Ftp;Frho;Fk2;Fk1;Fbd;Ftv;FC;FA;").
Proof.
  intros A C tv bd k1 k2 rho tp b tp0 rv Hbase Hk1 Hk2 Hfe Hwf HB HRO HXL HC HinC Hm.
  eapply TR_pre; [|apply (REENTER C (NDA tv fr_hl bd ANone) rv); [exact HinC | exact Hm]].
  intros w Hw. rewrite <- HC.
  apply (JA_shadow_reopen segs HTOP AInv CST XGL ALA HCST HXGL LFSH NPH Kc rho0 (P0_hl CST FB FF) FB FF BX PTrue HKc HBX HNP
           tv fr_hl bd ANone 0%nat 160%positive 1 170%positive hG k1 k2 A (ax_X A) rho tp w eq_refl ltac:(lia) Hbase Hk1
           ltac:(change (fs_frame_size 1) with 128; lia) Hfe (fun r H => H) Hwf); [|exact Hw].
  intros Ai rho1 tp1 md1 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR. split.
  - exact (siteF Ai rho _ tv fr_hl _ rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HN HD HZ HFR HRO).
  - intros r y Hr Hy. left. exact (proj1 (siteX Ai rho _ tv fr_hl (Some 0%nat) _ _ rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HBf HFF HN HD HZ HFR HXL) r y Hr Hy).
Qed.
Lemma XH_E_unp : ltac2:(tb__ "0|1|
S14S2bS4dQ40A1A1M0G0VTR;S54S4cVJAv;S8aA1S61R3R2A5VFAM;S3dS2fS2cS8S3aA2S2cS6S13A2S2fS8S3aS61S8aA4S2fS6S13Z50S87S59Z3bA2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_facts. intros HF. unfold ndJ, ndF.
  apply (X_reopen E_unp0 C_unp tvL (bdL pK pQ) 4 6 rho tp _ tp0 (80, VR pQ 58) eq_refl ltac:(lia) ltac:(lia));
    [vmr|vmr|vmr|vmr|vmr| exact C_unp_eq | innth 7 | exact (loop_meas_same rho _ 58 59 E_unp0 C_unp _ _ HF ltac:(vmr) ltac:(lia) ltac:(lia) ltac:(lia))].
Qed.

Lemma XH_X_ok0 : ltac2:(tb__ "0|1|
S14S2bS4dQ40A1A1M0S6G0S4eS51Z26S4fZ2Z40A2A2R2A2VTR;S54S4cVJAv;S95A1Sa5R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. unfold ndN, ndF, tvL, tvI.
  eapply TR_pre; [intros w Hw; exact (SPA_swap2 _ _ [] _ _ _ _ _ _ Hw)|]. change [(pD, kb 12 pK); (lc_d, kb 4 lc_k)] with tvN.
  apply (X_reopen X_ok0 C_ok tvN (bdL pK pX) 8 9 rho tp b tp0 (36, z0) eq_refl ltac:(lia) ltac:(lia));
    [vmr|vmr|vmr|vmr|vmr| exact C_ok_eq | innth 24 | rewrite emeas_z0; lia].
Qed.

Lemma reenter_abs : ltac2:(tb__ "0|6|
S8S3aS2cS6S13A2M0S14S2bS4dQ40A1M1A1M2S6G2SdbSc4S2cS2cS8S3aA2M3G0A2S2fG3G0S2fS8S3aR8R7A4R6A4S88A3SdcR3R1A1S5S14S14S1S13S0G1S1fR2R1A2M4S1fRaR1A2A3Fe;S54S4cVJAv;RbA1RcR1R8R3A6A2Lrho';A2F_;Fw;S14S13S0G1G4S1fR9R1A2A3Fe;S1S4eZ0S3dS2fG3G0S2fS8S3aRcRbA4RaA4R2A2M5A2S50G5R7A2A2F_;Frho';VTR;R4VFAM;R6R5A2A2F_;F_;F_;FP;Ftp0;Fb;Ftp;Frho;Frv;Fnd;FC;").
Proof.
  intros C nd rv rho tp b tp0 P HinC HP Hm. eapply TR_pre; [exact HP|]. apply TR_exw. intros rho'.
  apply (TR_pureP _ (forall e, eval rho' e = eval rho e)); [intros w [HE _]; exact HE|]. intros HE.
  eapply TR_pre; [intros w [_ Hw]; exact Hw|]. apply (REENTER C nd rv); [exact HinC | exact (Hm rho' HE)].
Qed.
Lemma X_release : ltac2:(tb__ "0|7|
S8S8S2bS1bA1M0S6S6S2bS28A1S2aS2bS2cS13S13A2A1S2bSbeA1S14S2bS4dQ40A1M1A1M2S6G2S2cS6S13A2M3S0S13SdReA1S17SeaA1A3S4eZ0M4RcA2S1S4eRdRcA2S4eRcZ10A2A2S0S2dS29RbA1S2eA3S0G0S19S9R12A1A1S39S1bR10S30S1bSe6S77RfReRdRcA5S32S1bA1A3A3A3S0S2dScS30S15S20SbS77A1S78A2S30S15S18S21S77A1S17S52S4fZ2Z3dA2Z1A2A1A2S32S15A1A3A3S16S9R13A1A1A2S2eA3S0S2dS41S1cS9R14A1A1S3cRdS58RcS3bA4A2S2eA3S0S2dS82S16S9R15A1A1A1S2eA3S0S2dSe1S16S9R16A1A1RfS58S34S31A1Sc7R14A6S2eA3S0S8Se5R17R15Pa0S32S2cS6S6A2A1A4R16A3Sc4S2cS2cS8S3aA2M5G3A2S2fG5G3S2fS8S3aR17S3cR11S58R10S3bA4A4RbA4S88A3S14S13S0G1S1fR2R1A2S1fR12R1A2A3Fe;S1S4eG4S3dS2fG5G3S2fS8S3aR1aS3cR14S58R13S3bA4A4ReA4R2A2M6A2S50G6R10A2A2F_;Frho';VTR;S54S4cVJAv;S3cR13S58R12S3bA4A1R1aR11R10A5VFAM;RfReA2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Frv;Ftp0;Fb;Ftp;Frho;Fbd;Ftv;Fd;Fcells;Fk2;Fk1;Fobjs;FC;FA;").
Proof.
  intros A C objs k1 k2 cells d tv bd rho tp b tp0 rv Hbase Hk1 Hk2 Hdw Ho Hfe Hnb HB HRO HC HinC Hm.
  apply (reenter_abs C (NDA tv fr_hl bd ANone) rv rho tp b tp0); [exact HinC | | exact Hm].
  intros [tr [ms md]] Hw. exists (rho_absorb rho [shobj hG k1 k2 cells d] (vms md tp ms)). split; [intros e; apply eval_absorb|].
  rewrite <- HC.
  apply (JA_shadow_release segs HTOP AInv CST XGL ALA HCST HXGL LFSH NPH Kc rho0 (P0_hl CST FB FF) FB FF BX PTrue HKc HBX HNP
           tv fr_hl bd ANone 0%nat 160%positive 1 170%positive hG k1 k2 cells d A objs [] rho tp tr ms md
           eq_refl ltac:(lia) Hbase Ho Hk1 ltac:(change (fs_frame_size 1) with 128; lia) Hdw Hfe eq_refl Hnb); [|exact Hw].
  intros Ai rho1 tp1 md1 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR.
  exact (siteF Ai rho _ tv fr_hl objs rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HN HD HZ HFR HRO).
Qed.
Lemma XH_X_pro : ltac2:(tb__ "0|1|
S14S2bS4dQ40A1A1M0S6G0S4eS51Z5eS4fZ2Z40A2A2R2A2VTR;S54S4cVJAv;Sb2A1S6eR5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. unfold ndP, ndF.
  apply (X_release X_pro C_pre objs_pro 0 16 cells_pro DZero _ _ rho tp b tp0 (92, z0) eq_refl ltac:(lia) ltac:(lia) eq_refl X_pro_objs);
    [vmr|vmr|vmr|vmr| exact C_pre_eq | innth 2 | intros rho' _; rewrite emeas_z0; lia].
Qed.
Lemma XH_X_r2k : ltac2:(tb__ "0|1|
S14S2bS4dQ40A1A1M0G0VTR;S54S4cVJAv;S8eA1S66R3R2A5VFAM;S3dS2fS2cS8S3aA2S2cS6S13A2S2fS8S3aS66S8eA4S2fS6S13Z50S87S59Z1cA2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_facts. intros HF. unfold ndK, ndF.
  apply (X_release X_r2k C_rlk objs_r2k 4 6 cells_r2k DUnknown _ _ rho tp _ tp0 (80, VR pQ 27) eq_refl ltac:(lia) ltac:(lia) eq_refl X_r2k_objs);
    [vmr|vmr|vmr|vmr| exact C_rlk_eq | innth 18 |].
  intros rho' HE. rewrite (emeas_eq C_rlk _ 80 (VR pQ 27) rho rho' HE).
  exact (loop_meas_same rho _ 27 28 X_r2k C_rlk _ _ HF ltac:(vmr) ltac:(lia) ltac:(lia) ltac:(lia)).
Qed.
Lemma XH_X_r2g : ltac2:(tb__ "0|1|
S14S2bS4dQ40A1A1M0G0VTR;S54S4cVJAv;S8dA1S65R3R2A5VFAM;S3dS2fS2cS8S3aA2S2cS6S13A2S2fS8S3aS65S8dA4S2fS6S13Z50S87S59Z1cA2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. apply TR_facts. intros HF. unfold ndG, ndF.
  apply (X_release X_r2g C_rlg objs_r2g 4 6 cells_r2g DUnknown _ _ rho tp _ tp0 (80, VR pQ 27) eq_refl ltac:(lia) ltac:(lia) eq_refl X_r2g_objs);
    [vmr|vmr|vmr|vmr| exact C_rlg_eq | innth 19 |].
  intros rho' HE. rewrite (emeas_eq C_rlg _ 80 (VR pQ 27) rho rho' HE).
  exact (loop_meas_same rho _ 27 28 X_r2g C_rlg _ _ HF ltac:(vmr) ltac:(lia) ltac:(lia) ltac:(lia)).
Qed.

Lemma X_pure : ltac2:(tb__ "0|6|
S8S8S8S8S8S8S3aS2bSffA1Sf8S2bS1bA1M0S14S2bS4dQ40A1A1M1G1S6S6S123RfS30SeS12ReS128A2S32SeA1A3A2S0S35G0A1Sd6ReR10R8A3S33G0R7A2A3S0S2dSd7RfR11R9R8S30S8R10S32S8A1A3A5S2eA3S0S2dS10dS76S1cS9R10A1A1A2S2eA3S0S2dS41S1cS9R11A1A1RdA2S2eA3S0S2dSc6S15S26S1cS9R12A1M2A1A1S16G2A1A3S2eA3S0S8S10fS16S9R13A1A1Sd8RdR15R14R13RcA5A2R12A3S0S35S8A1SfeR13RfA2S33S8R12A2A3Sc4S2cS2cS8S3aA2M3S2cS6S13A2M4A2S2fG3G4S2fS8S3aR13R11A4S2fS6S13Z50M5S87S59RaA2A4A4S88A3S0S2dS85S59S16S9R16A1A1A2S2eA3S0S2dS22S1cS9R17A1A1S79A2S2eA3S0S2dS22S1cS9R18A1A1S59A2S2eA3S4eZ0ReA2S50RfReA2S50RfZ40A2VTR;S54S4cVJAv;R18A1R1cR14R13A5VFAM;S3dS2fG3G4S2fS8S3aR19R18A4S2fS6S13G5S87S59R10A2A4A4R14A2R12A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fbpos;Fa;Ftp0;Ftp;Frho;FR;Fs;Fxf2;Fndx;FX0;FT;FT0;FE;FP;FPre;").
Proof.
  intros Pre P E T0 T X0 ndx xf2 s R rho tp tp0 a bpos CALL He Hchk Hnf Hnb Hfb HT0 HT HinT HV HbE HbQ Ha Hab Hb.
  apply TR_facts. intros HF.
  apply (CALL E s R rho tp ndx _ He Hchk Hnf Hnb Hfb).
  intros L rho' HL Hag. cbn [In] in HL. destruct HL as [<-|[]]. cbn [la_state]. rewrite HT0.
  eapply TR_pre; [intros w Hw; exact (SPA_axforms segs _ xf2 rho' T0 T tp w HT Hw)|].
  apply (REENTER T ndx (80, VR pQ a)); [exact HinT|].
  exact (loop_meas rho rho' _ _ a bpos X0 T ndx ndx HF HV (agree_below_vals _ _ _ Hag) HbE HbQ Ha Hab Hb).
Qed.

Lemma XH_E_pc : ltac2:(tb__ "0|1|
S14S2bS4dQ40A1A1M0G0VTR;S54S4cVJAv;S8aA1S60R3R2A5VFAM;S3dS2fS2cS8S3aA2S2cS6S13A2S2fS8S3aS60S8aA4S2fS6S13Z50S87S59Z39A2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  apply (TR_pre (fun w => exists rho', (fun w' => (forall e, eval rho' e = eval rho e) /\ SPA segs (JAv ndJ) E_pc1 rho' tp w') w)).
  { intros [tr [ms md]] Hw. exists (rho_absorb rho [shobj hG 4 6 cells_unp DUnknown] (vms md tp ms)). split; [intros e; apply eval_absorb|].
    rewrite <- E_pc1_eq. unfold ndJ, ndF.
    apply (JA_shadow_release segs HTOP AInv CST XGL ALA HCST HXGL LFSH NPH Kc rho0 (P0_hl CST FB FF) FB FF BX PTrue HKc HBX HNP
             tvL fr_hl (bdL pK pQ) ANone 0%nat 160%positive 1 170%positive hG 4 6 cells_unp DUnknown E_pc0 objs_pc0 [(32, 12)] rho tp tr ms md
             eq_refl ltac:(lia) eq_refl E_pc0_objs ltac:(lia) ltac:(change (fs_frame_size 1) with 128; lia) eq_refl ltac:(vmr) ltac:(vmr) ltac:(vmr)); [|exact Hw].
    intros Ai rho1 tp1 md1 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR.
    exact (siteF Ai rho _ tvL fr_hl objs_pc0 rho1 tp1 md1 HM HF ltac:(vmr) Hav HP0 HT HTK HN HD HZ HFR ltac:(vmr)). }
  apply TR_exw. intros rho'. apply (TR_pureP _ (forall e, eval rho' e = eval rho e)); [intros w [HE _]; exact HE|]. intros HE.
  eapply TR_pre; [intros w [_ Hw]; exact (SPA_axforms segs _ xf_pc rho' E_pc1 E_pc tp w E_pc_eq Hw)|].
  rewrite <- (emeas_eq E_pc0 ndJ 80 (VR pQ 57) rho rho' HE).
  apply (X_pure Pre_pc P_ret E_pc T_pc0 T_pc E_pc0 ndJ xf_tpc s_pc R_pc rho' tp tp0 56 57 CALL_pc);
    [vmr|vmr|vmr|vmr|vmr| exact T_pc0_eq | exact T_pc_eq | innth 8 |vmr|vmr|vmr|lia|lia|lia].
Qed.

Lemma XH_E_da : ltac2:(tb__ "0|1|
S14S2bS4dQ40A1A1M0G0VTR;S54S4cVJAv;S8aA1S5fR3R2A5VFAM;S3dS2fS2cS8S3aA2S2cS6S13A2S2fS8S3aS5fS8aA4S2fS6S13Z50S87S59Z37A2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  eapply TR_pre; [intros w Hw; exact (SPA_axforms segs _ [AXSplit 0 (SLit (-96))] rho E_da0 E_da tp w E_da_eq Hw)|].
  apply (X_pure Pre_da P_da E_da T_da0 T_da E_da0 ndJ xf_tda s_da R_da rho tp tp0 54 55 CALL_da);
    [vmr|vmr|vmr|vmr|vmr| exact T_da0_eq | exact T_da_eq | innth 9 |vmr|vmr|vmr|lia|lia|lia].
Qed.

Lemma X_epi : ltac2:(tb__ "0|8|
S8S8S2bS2cS13S13A2A1S2bSbeA1S14S2bS4dQ40A1A1M0S6G0S6S0S13SdR9A1S17SeaA1A3S0S2dScS30S15S20SbS77A1S78A2S30S15S18S21S77A1S17S52S4fZ2M1Z3dA2Z1M2A2A1A2S32S15A1A3A3S16S9RaA1A1A2S2eA3S0S2dS1eS9Se2RbSaRbA1S77Z0M3Z10A5A1A1S2eA3S0S2dS1eS9S89RcA1A1A1S2eA3S0S2dS82S16S9RdA1A1A1S2eA3S0S2dS84S16S9ReA1A1A1S2eA3S0S2dSe1S16S9RfA1M4A1RdS58S34S31A1Sc7S19G4A1A6S2eA3S0S2dSe3VXGL;S16S9R10A1M5A1ReS58S33S31U0A2S19G5A1Sc8SaR10A1A8S2eA3S0S8S89R11A1R10A3Sc4S2cS2cS8S3aA2M6S2cS6S13A2M7A2S2fG6G7S2fS8S3aR11S3cR10S58RfS3bA4A4S2fS6S13RaS8cA4A4S88A3S4eG3RbA2S4eS51S53RcG2A2S4fG1Z40A2A2ReA2VTR;S54S4cVJAv;S3cR13S58R12S3bA4A1R15R11R10A5VFAM;RfReA2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Frk;Ftp0;Fb;Ftp;Frho;Fbd;Ftv;FC;FY;").
Proof.
  intros Y C tv bd rho tp b tp0 rk Hbase Hfe Hwf1 Hwf2 HB HFRF HRO HXL HC HinC Hrk Hb.
  eapply TR_pre; [|apply (REENTER C (NDA tv fr_hl bd ANone) (rk, z0)); [exact HinC | rewrite emeas_z0; lia]].
  intros w Hw. rewrite <- HC. unfold epi_state.
  apply (JA_flag_carve segs HTOP AInv CST XGL ALA HCST HXGL LFLAG NPH Kc rho0 (P0_hl CST FB FF) FB FF BX PTrue HKc HBX HNP
           tv fr_hl bd ANone 0%nat 160%positive 1 170%positive (shadow_reopen_stateA Y (ax_X Y) hG 0 16) rho tp w eq_refl ltac:(lia)).
  - exact Hbase.
  - exact Hwf2.
  - intros Ai rho1 tp1 md1 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR. cbn [shadow_reopen_stateA ax_S ss_facts ss_objs ax_X] in HF |- *. split.
    + intros o a Ho Hr. apply in_app_or in Ho as [Ho|[<-|[]]].
      * exact (siteH Ai rho _ tv fr_hl _ rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HN HD HZ HFR HRO o a Ho Hr).
      * right. right. exact (shobj_range_hse hG 160 128 0 16 rho _ a sz_rng ltac:(lia) ltac:(cbn; lia) HF HFRF Hr).
    + exact (proj2 (proj2 (siteX Ai rho _ tv fr_hl (Some 0%nat) _ _ rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HBf HFF HN HD HZ HFR HXL))).
  - apply (JA_shadow_reopen segs HTOP AInv CST XGL ALA HCST HXGL LFSH NPH Kc rho0 (P0_hl CST FB FF) FB FF BX PTrue HKc HBX HNP
             tv fr_hl bd ANone 0%nat 160%positive 1 170%positive hG 0 16 Y (ax_X Y) rho tp w eq_refl ltac:(lia) Hbase ltac:(lia)
             ltac:(change (fs_frame_size 1) with 128; lia) Hfe (fun r H => H) Hwf1); [|exact Hw].
    intros Ai rho1 tp1 md1 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR. split.
    + exact (siteF Ai rho _ tv fr_hl _ rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HN HD HZ HFR HRO).
    + intros r y Hr Hy. left. exact (proj1 (siteX Ai rho _ tv fr_hl (Some 0%nat) _ _ rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HBf HFF HN HD HZ HFR HXL) r y Hr Hy).
Qed.
Lemma XH_E_da2 : ltac2:(tb__ "0|1|
S14S2bS4dQ40A1A1M0S6G0S4eS51Z26S4fZ2Z40A2A2R2A2VTR;S54S4cVJAv;S95A1S9aR5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  eapply TR_pre; [intros w Hw; exact (SPA_axforms segs _ [AXSplit 0 (SLit (-96))] rho E_da2 E_da2x tp w E_da2x_eq Hw)|].
  apply (CALL_da E_da2x s_da2 R_da2 rho tp ndN _); [vmr|vmr|vmr|vmr|vmr|].
  intros L rho' HL Hag. cbn [In Posts_da] in HL. destruct HL as [<-|[]]. cbn [la_state]. rewrite T_da2_eq.
  eapply TR_pre; [intros w Hw; exact (SPA_axforms segs _ xf_tda2 rho' T_da2 Y_few tp w Y_few_eq Hw)|].
  unfold ndN, ndF, tvL, tvI. eapply TR_pre; [intros w Hw; exact (SPA_swap2 _ _ [] _ _ _ _ _ _ Hw)|]. change [(pD, kb 12 pK); (lc_d, kb 4 lc_k)] with tvN.
  apply (X_epi Y_few C_few tvN (bdL pK pX) rho' tp b tp0 30); [vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr| exact C_few_eq | innth 23 | lia | lia].
Qed.

Lemma Forall_single : forall {A} (P : A -> Prop) a l, Forall P (a :: l) -> Forall P [a].
Proof. intros A P a l H. constructor; [exact (Forall_inv H) | constructor]. Qed.
Lemma tvd_single : ltac2:(tb__ "0|1|
S14S2cS13S13A2M0SecR2S30G0R1S32G0A1A3A2Ft;Frho;"). Proof. intros rho t. cbn. split; [intros t' [] | exact I]. Qed.

Lemma HIN_v : ltac2:(tb__ "0|2|
S14Sf2Se7S14S2bS4dQ40A1A1Sd2Sb9S15S1aR6A1S16S9S6aA1A1A3S81VCST;VFB;VFF;Vrho0;A4SdfS76Vrho0;R8A3VAInv;R7R6R5R4A4S3fVrho0;R8A2SeeRbSe9Se8R9A1A1A2S43VFB;RaA2S44VFF;RbA2S42VFB;RcReS90A4SecRfS90A2SedR10S90A2S40VFF;RfR11S58A4S1S106VCST;Vrho0;VFB;VFF;R12S30S2cS13S13A2M0S2fS13S13S7bS7aZ4S7cA2A4S32G0A1A3M1S58S64A8S1S107VCST;VXGL;Vrho0;VFB;VFF;R12G1S58S6fA9S101SefVFB;R12G1A3S103VFF;R12S58A3Sf7Sf6R12S64R11A3S73A2A3A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FAi;Fms;Frho;").
Proof.
  intros rho ms Ai rho1 tp1 md1 HF HP0 Hav HM HTP HTK HBf HFF HN HD HZ HFR. destruct (P0_now rho Hav HP0) as (HT & Hb & Hal & _).
  assert (HB : bF (ss_facts (ax_S E_vr)) = true) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
  pose proof (basez_of DW rho _ DW_rng HF HB) as BZ. pose proof BZ as [Bsp Bb Bal BL BB Btop]. rewrite aceil_val in *.
  pose proof (Forall_single _ _ _ HN) as HN1. pose proof (Forall_single _ _ _ HZ) as HZ1. pose proof (tvd_single rho (lc_d, kb 4 lc_k)) as HD1.
  split; [|split].
  - intros o a Ho Hr. eapply (robjs_checkP_sound segs AInv CST ALA rho0 FB FF Ai rho _ [(lc_d, kb 4 lc_k)] fr_hl None extraOH R_v rho1 tp1 md1 HM HF (T_ok_T0 rho0 _ Ai HTP HTK) HN1 HD1 HZ1 HFR ltac:(vmr));
      [intros o' a' Ho' HE Hr'; exact (extra_client rho o' a' _ _ BZ Hav HP0 HE Hr') | exact Ho | exact Hr].
  - exact (proj1 (siteX Ai rho _ [(lc_d, kb 4 lc_k)] fr_hl None (ss_objs (ax_S E_vr)) Xk_v rho1 tp1 md1 HM HF HB Hav HP0 HTP HTK HBf HFF HN1 HD1 HZ1 HFR ltac:(vmr))).
  - unfold VNP.P0_vr. rewrite !rw_call'.
    change (wsub_get s_v 17) with pK. change (wsub_get s_v 15) with pD. change (wsub_get s_v 14) with vAL. change (wsub_get s_v 12) with (xbo 624).
    split; [|split].
    + pose proof (holds_mem _ _ (SPUle pK (SLit B32)) HF ltac:(vmr)) as FK. rewrite h_ule in FK. unfold B32 in FK. rewrite uval_lit in FK by lia.
      intros HK. apply Forall_inv_tail in HZ. apply (tvz_kd rho 12 pD pK [] HZ); [lia | unfold B32; lia | exact HK].
    + destruct Hb as (f & sz & fl & Hin & H1 & H2). exists f, sz, fl. split; [apply In_FFx; left; exact Hin|].
      assert (E624 : uval rho (xbo 624) = uval rho vb + 624) by (unfold xbo; apply uval_add_litZ; unfold IMG_HI in *; lia).
      unfold uval in E624, H1, H2. rewrite E624. lia.
    + destruct Hal as (f & sz & fl & Hin & H1 & H2). exists f, sz, fl. split; [apply In_FFx; left; exact Hin|]. unfold uval in H1, H2. lia.
Qed.

Lemma XH_E_vr : ltac2:(tb__ "0|1|
S14S2bS4dQ40A1A1M0G0VTR;S54S4cVJAv;S8aA1S62R3R2A5VFAM;S3dS2fS2cS8S3aA2S2cS6S13A2S2fS8S3aS62S8aA4S2fS6S13Z50S87S59Z34A2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  eapply TR_pre with (P := SPA segs (JAv ndJ) E_vr rho tp).
  { intros w Hw. exact (SPA_axforms segs _ xf_vr rho E_vr0 E_vr tp w E_vr_eq Hw). }
  apply TR_facts. intros HF. unfold ndJ, ndF, tvL, tvI.
  change [(lc_d, kb 4 lc_k); (pD, kb 12 pK)] with ([(lc_d, kb 4 lc_k)] ++ [(pD, kb 12 pK)]).
  apply (client_callT segs AInv CST XGL ALA HCST HXGL NPH Kc rho0 (P0_hl CST FB FF) FB FF BX PTrue HKc HBX VNP.P0_vr PTrue (fun _ H => H) (fun _ _ _ H => H)
           VN.Pre_vr VN.nd0 PD_vn NF eq_refl eq_refl eq_refl TR TR_facts TR_ex TR_pre TR_callP CVRESN eq_refl
           E_vr s_v R_v Xk_v rho tp [(lc_d, kb 4 lc_k)] [(pD, kb 12 pK)] fr_hl (bdL pK pQ) bdX ANone (FAM (emeasA (E_vr0, ndJ, (80, VR pQ 52)) rho) tp0)).
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
  - intros [Ld ndL] rho' tp' Hd Hag. cbn [PD_vn In] in Hd. destruct Hd as [Hd|[Hd|[Hd|[]]]]; injection Hd as <- <-;
      cbn [fst snd nd_tv nd_bd nd_am VN.nd0 ND am_subst app].
    +
      rewrite T_keep0_eq, imp_keep_tv, imp_keep_bd. change ([(lc_d, kb 4 lc_k)] ++ [(pD, kb 12 pK)]) with tvL. change ([PHIN pQ pK; KLG pK] ++ bdX) with (bdJK pK).
      eapply TR_pre; [|apply (REENTER T_keep ndK (80, VR pQ 51)); [innth 11 | exact (loop_meas rho rho' _ _ 51 52 E_vr0 T_keep ndJ ndK HF ltac:(vmr) Hag ltac:(vmr) ltac:(vmr) ltac:(lia) ltac:(lia) ltac:(lia))]].
      intros w Hw. rewrite <- T_keep_eq. apply (SPA_refacts_JA segs); [exact Hw | vmr |].
      intros tr md HJ HF2. apply Forall_app. split; [|exact HF2]. apply Forall_app. split.
      * apply (slot_holds rho' _ pK HF2); vmr.
      * assert (TNZ : tnz rho' (pD, kb 12 pK)).
        { destruct HJ as (Ai & kc & Hav' & _ & _ & _ & _ & _ & (_ & _ & HZ') & _).
          pose proof (holds_mem _ _ (SPUle pC1 pK) HF2 ltac:(vmr)) as F1. pose proof (holds_mem _ _ (SPUle pK (SLit B32)) HF2 ltac:(vmr)) as F4.
          pose proof (holds_mem _ _ (SPUle pC pK) HF2 ltac:(vmr)) as F3.
          rewrite h_ule in F1, F3, F4. unfold B32 in F4. rewrite uval_lit in F4 by lia. pose proof (uval_range rho' pC) as RC.
          unfold pC1 in F1. rewrite uval_add_litZ in F1 by lia. unfold tnz. cbn [fst]. cbn [nd_tv] in HZ'. apply Forall_inv_tail in HZ'.
          apply (tvz_kd rho' 12 pD pK [] HZ'); unfold B32; lia. }
        pose proof (JA_tv_facts segs AInv CST XGL NPH Kc rho0 (P0_hl CST FB FF) FB FF BX PTrue ALA _ _ _ _ _ (pD, kb 12 pK) eq_refl HJ (or_intror (or_introl eq_refl)) TNZ) as TF.
        constructor; [|constructor]. apply (proj1 (Forall_forall _ _) TF). unfold tv_factsA. cbn [fst snd]. do 5 right. left. reflexivity.
    +
      rewrite T_fail0_eq, imp_fail_tv. change ([(lc_d, kb 4 lc_k)] ++ [(pD, kb 12 pK)]) with tvL. change (bd_subst _ [] ++ bdX) with bdX.
      apply (REENTER T_fail0 ndX (30, z0)); [innth 13|]. rewrite emeas_z0. unfold emeasA. cbn [eda_rank eda_var fst snd]. pose proof (bv_urange (eval rho (VR pQ 52))). lia.
    +
      rewrite T_grown0_eq, imp_grown_tv, imp_grown_bd. change ([(lc_d, kb 4 lc_k)] ++ [(vDg, kb 12 vKg)]) with tvG. change ([PHIN pQ vKg; KLG vKg] ++ bdX) with (bdJK vKg).
      eapply TR_pre; [|apply (REENTER T_grown ndG (80, VR pQ 51)); [innth 12 | exact (loop_meas rho rho' _ _ 51 52 E_vr0 T_grown ndJ ndG HF ltac:(vmr) Hag ltac:(vmr) ltac:(vmr) ltac:(lia) ltac:(lia) ltac:(lia))]].
      intros w Hw. rewrite <- T_grown_eq. apply (SPA_refacts_JA segs); [exact Hw | vmr |].
      intros tr md _ HF2. apply Forall_app. split; [|exact HF2]. apply (slot_holds rho' _ vKg HF2); vmr.
Qed.

Lemma HIN_v2 : ltac2:(tb__ "0|2|
S14Sf2Se7S14S2bS4dQ40A1A1Sd2Sb9S15S1aR6A1S16S9S9bA1A1A3S81VCST;VFB;VFF;Vrho0;A4SdfS76Vrho0;R8A3VAInv;R7R6R5R4A4S3fVrho0;R8A2SeeRbSe9Se8R9A1A1A2S43VFB;RaA2S44VFF;RbA2S42VFB;RcReS8bA4SecRfS8bA2SedR10S8bA2S40VFF;RfR11S58A4S1S106VCST;Vrho0;VFB;VFF;R12S30S2cS13S13A2M0S2fS13S13S5bS7aZcS5aA2A4S32G0A1A3M1S58S94A8S1S107VCST;VXGL;Vrho0;VFB;VFF;R12G1S58Sa8A9S101SefVFB;R12G1A3S103VFF;R12S58A3Sf7Sf6R12S94R11A3Sb3A2A3A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FAi;Fms;Frho;").
Proof.
  intros rho ms Ai rho1 tp1 md1 HF HP0 Hav HM HTP HTK HBf HFF HN HD HZ HFR. destruct (P0_now rho Hav HP0) as (HT & Hb & Hal & _).
  assert (HB : bF (ss_facts (ax_S E_vc)) = true) by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
  pose proof (basez_of DW rho _ DW_rng HF HB) as BZ. pose proof BZ as [Bsp Bb Bal BL BB Btop]. rewrite aceil_val in *.
  pose proof (Forall_single _ _ _ HN) as HN1. pose proof (Forall_single _ _ _ HZ) as HZ1. pose proof (tvd_single rho (pD, kb 12 pK)) as HD1.
  split; [|split].
  - intros o a Ho Hr. eapply (robjs_checkP_sound segs AInv CST ALA rho0 FB FF Ai rho _ [(pD, kb 12 pK)] fr_hl None extraOH R_v2 rho1 tp1 md1 HM HF (T_ok_T0 rho0 _ Ai HTP HTK) HN1 HD1 HZ1 HFR ltac:(vmr));
      [intros o' a' Ho' HE Hr'; exact (extra_client rho o' a' _ _ BZ Hav HP0 HE Hr') | exact Ho | exact Hr].
  - exact (proj1 (siteX Ai rho _ [(pD, kb 12 pK)] fr_hl None (ss_objs (ax_S E_vc)) Xk_v2 rho1 tp1 md1 HM HF HB Hav HP0 HTP HTK HBf HFF HN1 HD1 HZ1 HFR ltac:(vmr))).
  - unfold VNP.P0_vr. rewrite !rw_call'.
    change (wsub_get s_v2 17) with lc_k. change (wsub_get s_v2 15) with lc_d. change (wsub_get s_v2 14) with vAL. change (wsub_get s_v2 12) with (xbo 656).
    split; [|split].
    + pose proof (holds_mem _ _ (SPUle lc_k (SLit B32)) HF ltac:(vmr)) as FK. rewrite h_ule in FK. unfold B32 in FK. rewrite uval_lit in FK by lia.
      intros HK. apply Forall_inv_tail in HZ. apply (tvz_kd rho 4 lc_d lc_k [] HZ); [lia | unfold B32; lia | exact HK].
    + destruct Hb as (f & sz & fl & Hin & H1 & H2). exists f, sz, fl. split; [apply In_FFx; left; exact Hin|].
      assert (E656 : uval rho (xbo 656) = uval rho vb + 656) by (unfold xbo; apply uval_add_litZ; unfold IMG_HI in *; lia).
      unfold uval in E656, H1, H2. rewrite E656. lia.
    + destruct Hal as (f & sz & fl & Hin & H1 & H2). exists f, sz, fl. split; [apply In_FFx; left; exact Hin|]. unfold uval in H1, H2. lia.
Qed.

Lemma XH_E_vc : ltac2:(tb__ "0|1|
S14S2bS4dQ40A1A1M0S6G0S4eS51Z22S4fZ2Z40A2A2R2A2VTR;S54S4cVJAv;SafA1S9cR5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  apply (TR_pre (fun w => exists rho', (fun w' => (forall e, eval rho' e = eval rho e) /\ SPA segs (JAv ndNs) E_vc1 rho' tp w') w)).
  { intros [tr [ms md]] Hw. exists (rho_absorb rho [shobj hG 8 9 cells_vc DUnknown] (vms md tp ms)). split; [intros e; apply eval_absorb|].
    rewrite <- E_vc1_eq. unfold ndNs, ndF.
    apply (JA_shadow_release segs HTOP AInv CST XGL ALA HCST HXGL LFSH NPH Kc rho0 (P0_hl CST FB FF) FB FF BX PTrue HKc HBX HNP
             tvN fr_hl (bdL pK pX) ANone 0%nat 160%positive 1 170%positive hG 8 9 cells_vc DUnknown E_vc0 objs_vc0 [(64, 4)] rho tp tr ms md
             eq_refl ltac:(lia) eq_refl E_vc0_objs ltac:(lia) ltac:(change (fs_frame_size 1) with 128; lia) eq_refl ltac:(vmr) ltac:(vmr) ltac:(vmr)); [|exact Hw].
    intros Ai rho1 tp1 md1 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR.
    exact (siteF Ai rho _ tvN fr_hl objs_vc0 rho1 tp1 md1 HM HF ltac:(vmr) Hav HP0 HT HTK HN HD HZ HFR ltac:(vmr)). }
  apply TR_exw. intros rho'. apply (TR_pureP _ (forall e, eval rho' e = eval rho e)); [intros w [HE _]; exact HE|]. intros HE.
  eapply TR_pre; [intros w [_ Hw]; exact (SPA_axforms segs _ xf_vc rho' E_vc1 E_vc tp w E_vc_eq Hw)|].
  clear HE. apply TR_facts. intros HF. unfold ndNs, ndF, tvN, tv_hl.
  change [(pD, kb 12 pK); (lc_d, kb 4 lc_k)] with ([(pD, kb 12 pK)] ++ [(lc_d, kb 4 lc_k)]).
  apply (client_callT segs AInv CST XGL ALA HCST HXGL NPH Kc rho0 (P0_hl CST FB FF) FB FF BX PTrue HKc HBX VNP.P0_vr PTrue (fun _ H => H) (fun _ _ _ H => H)
           VN.Pre_vr VN.nd0 PD_vn NF eq_refl eq_refl eq_refl TR TR_facts TR_ex TR_pre TR_callP CVRESN eq_refl
           E_vc s_v2 R_v2 Xk_v2 rho' tp [(pD, kb 12 pK)] [(lc_d, kb 4 lc_k)] fr_hl (bdL pK pX) bdX2 ANone (FAM b tp0)).
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
  - intros Ai ms HF' HP0 Hav HBf HFF HN HD HZ HFR (rho1 & tp1 & md1 & HM) HT HTK. exact (HIN_v2 rho' ms Ai rho1 tp1 md1 HF' HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR).
  - intros [Ld ndL] rho2 tp' Hd Hag. cbn [PD_vr PD_vn In] in Hd. destruct Hd as [Hd|[Hd|[Hd|[]]]]; injection Hd as <- <-;
      cbn [fst snd nd_tv nd_bd nd_am VN.nd0 ND am_subst app].
    +
      rewrite T_keep2_0_eq, imp_keep2_tv, imp_keep2_bd. change ([(pD, kb 12 pK)] ++ [(lc_d, kb 4 lc_k)]) with tvN. change (bd_vec 4 lcn1 lc_k ++ bdX2) with (bdO lc_k).
      eapply TR_pre; [|apply (REENTER T_keep2 ndO (32, z0)); [innth 25 | rewrite emeas_z0; lia]].
      intros w Hw. rewrite <- T_keep2_eq. apply (SPA_refacts_JA segs); [exact Hw | vmr |].
      intros tr md HJ HF2. apply Forall_app. split; [|exact HF2]. apply Forall_app. split.
      * apply (slot4_holds rho2 _ lc_k HF2); vmr.
      * assert (TNZ : tnz rho2 (lc_d, kb 4 lc_k)).
        { destruct HJ as (Ai & kc & Hav' & _ & _ & _ & _ & _ & (_ & _ & HZ') & _).
          pose proof (holds_mem _ _ (SPUle lcc1 lc_k) HF2 ltac:(vmr)) as F1. pose proof (holds_mem _ _ (SPUle lc_k (SLit B32)) HF2 ltac:(vmr)) as F4.
          pose proof (holds_mem _ _ (SPUle lc_c lc_k) HF2 ltac:(vmr)) as F3.
          rewrite h_ule in F1, F3, F4. unfold B32 in F4. rewrite uval_lit in F4 by lia. pose proof (uval_range rho2 lc_c) as RC.
          unfold lcc1 in F1. rewrite uval_add_litZ in F1 by lia. unfold tnz. cbn [fst]. cbn [nd_tv] in HZ'. apply Forall_inv_tail in HZ'.
          apply (tvz_kd rho2 4 lc_d lc_k [] HZ'); unfold B32; lia. }
        pose proof (JA_tv_facts segs AInv CST XGL NPH Kc rho0 (P0_hl CST FB FF) FB FF BX PTrue ALA _ _ _ _ _ (lc_d, kb 4 lc_k) eq_refl HJ (or_intror (or_introl eq_refl)) TNZ) as TF.
        constructor; [|constructor]. apply (proj1 (Forall_forall _ _) TF). unfold tv_factsA. cbn [fst snd]. do 5 right. left. reflexivity.
    +
      rewrite T_fail2_eq, imp_fail2_tv. change ([(pD, kb 12 pK)] ++ [(lc_d, kb 4 lc_k)]) with tvN. change (bd_subst _ [] ++ bdX2) with bdX2.
      apply (REENTER T_fail2 ndX2 (32, z0)); [innth 27 | rewrite emeas_z0; lia].
    +
      rewrite T_grown2_0_eq, imp_grown2_tv, imp_grown2_bd. change ([(pD, kb 12 pK)] ++ [(vDg, kb 4 vKg)]) with tvN2. change (bd_vec 4 lcn1 vKg ++ bdX2) with (bdO vKg).
      eapply TR_pre; [|apply (REENTER T_grown2 ndOg (32, z0)); [innth 26 | rewrite emeas_z0; lia]].
      intros w Hw. rewrite <- T_grown2_eq. apply (SPA_refacts_JA segs); [exact Hw | vmr |].
      intros tr md _ HF2. apply Forall_app. split; [|exact HF2]. apply (slot4_holds rho2 _ vKg HF2); vmr.
Qed.

Lemma X_cm : ltac2:(tb__ "0|9|
S8S8S8S13S13S2bS2cS13S13A2A1S2bSbeA1S14S2bS4dQ40A1A1M0G0S0S35S8A1SfeRaS75A2S33S8R9A2A3S0S13SdRaA1S17SeaA1A3S0S2dScS30S15S20SbS77A1S78A2S30S15S18S21S77A1S17S52S4fZ2Z3dA2Z1A2A1A2S32S15A1A3A3S16S9RbA1A1A2S2eA3S0S2dS105S5cRaR9S7bS7cA4SaRcA1A2S2eA3S0S2dS1eS9Se2RdS5cRbRaS7bS7cA4S77Z4M1Z6M2A5A1A1S2eA3S0S2dS82S16S9ReA1A1A1S2eA3S0S2dSe1S16S9RfA1M3A1RbS58S34S31A1Sc7S19G3A1A6S2eA3S0S2dSe3VXGL;S16S9R10A1M4A1RcS58S33S31U0A2S19G4A1Sc8S5cReRdS7bS7cA4A8S2eA3S0S8Se2R11S5cRfReS7bS7cA4S77G1G2A5R10A3Sc4S2cS2cS8S3aA2M5S2cS6S13A2M6A2S2fG5G6S2fS8S3aR11S3cReS58RdS3bA4A4S2fS6S13Z50M7S87S59Z1dA2A4A4S88A3S0S2dS85S59S16S9R14A1A1A2S2eA3VTR;S54S4cVJAv;S3cR10S58RfS3bA4M8A1R15ReRdA5VFAM;S3dS2fG5G6S2fS8S3aR15G8A4S2fS6S13G7S87S59Z1eA2A4A4ReA2RcA2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Ftp0;Ftp;Frho;Fbd;Ftv;Fk;Fd;FC;FY;FX;").
Proof.
  intros X Y C d k tv bd rho tp tp0 HY Hbase Hfe HXi Hwf HB HRO HXL HC HinC HV.
  apply TR_facts. intros HF.
  eapply TR_pre; [|apply (REENTER C (NDA tv fr_hl bd ANone) (80, VR pQ 29)); [exact HinC | exact (loop_meas_same rho _ 29 30 X C _ _ HF HV ltac:(lia) ltac:(lia) ltac:(lia))]].
  intros w Hw. rewrite <- HC.
  pose proof (SPA_axforms segs _ xf_cm rho X Y tp w HY Hw) as Hw2.
  apply (JA_shadow_reopen segs HTOP AInv CST XGL ALA HCST HXGL LFSH NPH Kc rho0 (P0_hl CST FB FF) FB FF BX PTrue HKc HBX HNP
           tv fr_hl bd ANone 0%nat 160%positive 1 170%positive hG 4 6 Y (X_hl d k lc_d lc_k) rho tp w eq_refl ltac:(lia) Hbase ltac:(lia)
           ltac:(change (fs_frame_size 1) with 128; lia) Hfe (xrs_inclb_sound _ _ HXi) Hwf); [|exact Hw2].
  intros Ai rho1 tp1 md1 HF2 HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR. split.
  - exact (siteF Ai rho _ tv fr_hl _ rho1 tp1 md1 HM HF2 HB Hav HP0 HT HTK HN HD HZ HFR HRO).
  - intros r y Hr Hy. left. exact (proj1 (siteX Ai rho _ tv fr_hl (Some 0%nat) _ _ rho1 tp1 md1 HM HF2 HB Hav HP0 HT HTK HBf HFF HN HD HZ HFR HXL) r y Hr Hy).
Qed.
Lemma XH_X_rpk : ltac2:(tb__ "0|1|
S14S2bS4dQ40A1A1M0G0VTR;S54S4cVJAv;S8eA1S68R3R2A5VFAM;S3dS2fS2cS8S3aA2S2cS6S13A2S2fS8S3aS68S8eA4S2fS6S13Z50S87S59Z1eA2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. unfold ndK, ndF.
  apply (X_cm X_rpk Y_rpk C_mk pD pK _ _ rho tp tp0); [exact Y_rpk_eq |vmr|vmr|vmr|vmr|vmr|vmr|vmr| exact C_mk_eq | innth 16 | vmr].
Qed.
Lemma XH_X_rpg : ltac2:(tb__ "0|1|
S14S2bS4dQ40A1A1M0G0VTR;S54S4cVJAv;S8dA1S67R3R2A5VFAM;S3dS2fS2cS8S3aA2S2cS6S13A2S2fS8S3aS67S8dA4S2fS6S13Z50S87S59Z1eA2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0. unfold ndG, ndF.
  apply (X_cm X_rpg Y_rpg C_mg vDg vKg _ _ rho tp tp0); [exact Y_rpg_eq |vmr|vmr|vmr|vmr|vmr|vmr|vmr| exact C_mg_eq | innth 17 | vmr].
Qed.

Lemma X_arr : ltac2:(tb__ "0|9|
S8S8S8S8S2bSffA1S2bS2cS13S13A2A1M0G0S2bSbeA1S14S2bS4dQ40A1A1M1S6G1S6S0S35S8A1SfeRdR9A2S33S8RcA2A3S0S2dS105R9SaRdA1A2S2eA3S0S8S111ReRaA2RdA3S0G0SaReA1RbA3S0S13SdRfA1S17SeaA1A3S0S2dScS30S15S20SbS77A1S78A2S30S15S18S21S77A1S17S52S4fZ2M2Z3dA2Z1M3A2A1A2S32S15A1A3A3S16S9R10A1A1A2S2eA3S0S2dS1eS9Se2R11SaR11A1S77Z0M4Z10A5A1A1S2eA3S0S2dS1eS9S89R12A1A1A1S2eA3S0S2dS82S16S9R13A1A1A1S2eA3S0S2dS84S16S9R14A1A1A1S2eA3S0S2dSe1S16S9R15A1M5A1R11S58S34S31A1Sc7S19G5A1A6S2eA3S0S2dSe3VXGL;S16S9R16A1M6A1R12S58S33S31U0A2S19G6A1Sc8SaR16A1A8S2eA3S0S8S89R17A1R16A3Sc4S2cS2cS8S3aA2M7S2cS6S13A2M8A2S2fG7G8S2fS8S3aR17S3cR14S58R13S3bA4A4S2fS6S13ReS8cA4A4S88A3S4eG4RfA2S4eS51S53R10G3A2S4fG2Z40A2A2R12A2VTR;S54S4cVJAv;S3cR17S58R16S3bA4A1R1dR15R14A5VFAM;R13R12A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Frk;Ftp0;Fb;Ftp;Frho;Fbd;Ftv;FXc;Fxf;FC;FY;FZ;FX;").
Proof.
  intros X Z Y C xf Xc tv bd rho tp b tp0 rk HZ HXZ HY HXY Hbase Hfe Hwf1 Hwf2 HB HFRF HRO HXL HC HinC Hrk Hb.
  eapply TR_pre with (P := SPA segs (JAv (NDA tv fr_hl bd ANone)) Y rho tp).
  { intros w Hw. rewrite <- HY. apply (SPA_x_sub segs); [exact (xrs_inclb_sound _ _ HXZ)|]. exact (SPA_axforms segs _ xf rho X Z tp w HZ Hw). }
  apply (X_epi Y C tv bd rho tp b tp0 rk Hbase Hfe Hwf1 Hwf2 HB HFRF HRO HXL HC HinC Hrk Hb).
Qed.
Lemma XH_X_fp0 : ltac2:(tb__ "0|1|
S14S2bS4dQ40A1A1M0S6G0S4eS51Z1cS4fZ2Z40A2A2R2A2VTR;S54S4cVJAv;S96A1Sa3R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. unfold ndX, ndF, tvL, tvI. eapply TR_pre; [intros w Hw; exact (SPA_swap2 _ _ [] _ _ _ _ _ _ Hw)|]. change [(pD, kb 12 pK); (lc_d, kb 4 lc_k)] with tvN.
  apply (X_arr X_fp0 Z_fp0 Y_fp0 C_fa0 xf_f (X_hl pD pK lc_d lc_k) tvN bdX rho tp b tp0 26 Z_fp0_eq); [vmr| exact Y_fp0_eq |vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr| exact C_fa0_eq | innth 20 | lia | lia].
Qed.
Lemma XH_X_fp1 : ltac2:(tb__ "0|1|
S14S2bS4dQ40A1A1M0S6G0S4eS51Z1cS4fZ2Z40A2A2R2A2VTR;S54S4cVJAv;S96A1Sa4R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. unfold ndX, ndF, tvL, tvI. eapply TR_pre; [intros w Hw; exact (SPA_swap2 _ _ [] _ _ _ _ _ _ Hw)|]. change [(pD, kb 12 pK); (lc_d, kb 4 lc_k)] with tvN.
  apply (X_arr X_fp1 Z_fp1 Y_fp1 C_fa1 xf_f (X_hl pD pK lc_d lc_k) tvN bdX rho tp b tp0 26 Z_fp1_eq); [vmr| exact Y_fp1_eq |vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr| exact C_fa1_eq | innth 21 | lia | lia].
Qed.

Lemma X_e8 : ltac2:(tb__ "0|6|
S8S8S8S8S13S13S2bSbeA1S14S2bS4dQ40A1A1M0S6G0S0S35S8A1SfeRbSb7A2S33S8RaA2A3S0S2dS105S5cS5bS5aR8R7A4SaRbA1A2S2eA3S0S8S111RcS5cS5bS5aR9R8A4A2RbA3S0S2bS2cS13S13A2A1SaRcA1S5cS5bS5aRaR9A4A3S0S13SdRdA1S17SeaA1A3S0S2dScS30S15S20SbS77A1S78A2S30S15S18S21S77A1S17S52S4fZ2M1Z3dA2Z1A2A1A2S32S15A1A3A3S16S9ReA1A1A2S2eA3S0S2dS1eS9Se2RfSaRfA1S77Z0Z10A5A1A1S2eA3S0S2dS1eS9S89R10A1A1A1S2eA3S0S2dS82S16S9R11A1A1A1S2eA3S0S2dS84S16S9R12A1A1A1S2eA3S0S2dSe1S16S9R13A1M2A1S5dS5bS5aR11R10A4S58S34S31A1Sc7S19G2A1A6S2eA3S0S2dSe3VXGL;S16S9R14A1M3A1S5dS5bS5aR12R11A4S58S33S31U0A2S19G3A1Sc8SaR14A1A8S2eA3S0S8S89R15A1R14A3Sc4S2cS2cS8S3aA2M4S2cS6S13A2M5A2S2fG4G5S2fS8S3aR15S3cS5dS5bS5aR14R13A4S58R12S3bA4A4S2fS6S13Z18S8cA4A4S88A3S4eS51Z1aS4fG1Z40A2A2R10A2VTR;S54S4cVJAv;S3cS5dS5bS5aR16R15A4S58R14S3bA4A1R1aR13R12A5VFAM;R11R10A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Ftp0;Fb;Ftp;Frho;Fbd;Fk2;Fd2;FC;FY;FZ;FX;").
Proof.
  intros X Z Y C d2 k2 bd rho tp b tp0 HZ HXZ HY HXY Hbase Hfe Hwf2 Hwf3 HB HFRF HRO HXL HC HinC Hb.
  apply (X_arr X Z Y C xf_e8 (X_hl pD pK d2 k2) (tv_hl pD pK d2 k2) bd rho tp b tp0 24 HZ HXZ HY HXY Hbase Hfe Hwf2 Hwf3 HB HFRF HRO HXL HC HinC ltac:(lia) ltac:(lia)).
Qed.
Lemma XH_X_e8k : ltac2:(tb__ "0|1|
S14S2bS4dQ40A1A1M0S6G0S4eS51Z1aS4fZ2Z40A2A2R2A2VTR;S54S4cVJAv;Sb0A1S9eR5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. unfold ndO, ndF, tvN.
  apply (X_e8 X_e8k Z_e8k Y_e8k C_e8k lc_d lc_k (bdO lc_k) rho tp b tp0); [exact Z_e8k_eq |vmr| exact Y_e8k_eq |vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr| exact C_e8k_eq | innth 30 | exact Hb].
Qed.
Lemma XH_X_e8g : ltac2:(tb__ "0|1|
S14S2bS4dQ40A1A1M0S6G0S4eS51Z1aS4fZ2Z40A2A2R2A2VTR;S54S4cVJAv;Sb1A1S9dR5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. unfold ndOg, ndF, tvN2.
  apply (X_e8 X_e8g Z_e8g Y_e8g C_e8g vDg vKg (bdO vKg) rho tp b tp0); [exact Z_e8g_eq |vmr| exact Y_e8g_eq |vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr| exact C_e8g_eq | innth 31 | exact Hb].
Qed.
Lemma XH_X_f2a : ltac2:(tb__ "0|1|
S14S2bS4dQ40A1A1M0S6G0S4eS51Z1aS4fZ2Z40A2A2R2A2VTR;S54S4cVJAv;S97A1S9fR5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. unfold ndX2, ndF.
  apply (X_arr X_f2a Z_f2a Y_f2a C_f2a xf_f2 (X_hl pD pK lc_d lc_k) tvN bdX2 rho tp b tp0 24 Z_f2a_eq); [vmr| exact Y_f2a_eq |vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr| exact C_f2a_eq | innth 32 | lia | lia].
Qed.
Lemma XH_X_f2b : ltac2:(tb__ "0|1|
S14S2bS4dQ40A1A1M0S6G0S4eS51Z1aS4fZ2Z40A2A2R2A2VTR;S54S4cVJAv;S97A1Sa0R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. unfold ndX2, ndF.
  apply (X_arr X_f2b Z_f2b Y_f2b C_f2b xf_f2 (X_hl pD pK lc_d lc_k) tvN bdX2 rho tp b tp0 24 Z_f2b_eq); [vmr| exact Y_f2b_eq |vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr| exact C_f2b_eq | innth 33 | lia | lia].
Qed.

Lemma epi_glue : ltac2:(tb__ "0|2|
S8S2bS2cS13S13A2A1S2bSbeA1S14S2bS4dQ40A1A1SdcS0S13SdR6A1S17SeaA1A3S0S2dScS30S15S20SbS77A1S78A2S30S15S18S21S77A1S17S52S4fZ2Z3dA2Z1A2A1A2S32S15A1A3A3S16S9R7A1A1A2S2eA3S0S2dS1eS9Se2R8SaR8A1S77Z0Z10A5A1A1S2eA3S0S2dS1eS9S89R9A1A1A1S2eA3S0S2dS82S16S9RaA1A1A1S2eA3S0S2dS84S16S9RbA1A1A1S2eA3S0S2dSe1S16S9RcA1M0A1RbS58S34S31A1Sc7S19G0A1A6S2eA3S0S2dSe3VXGL;S16S9RdA1M1A1RcS58S33S31U0A2S19G1A1Sc8SaRdA1A8S2eA3S54S4cVJAv;S3cRdS58RcS3bA4A1ReRbRaR9A6S54S4cVJAv;S3cReS58RdS3bA4A1S89RfA1RcRbRaA6F_;F_;F_;F_;F_;F_;F_;F_;F_;Fw;Ftp;Frho;Fbd;Ftv;FY;").
Proof.
  intros Y tv bd rho tp w Hbase Hfe Hwf1 Hwf2 HB HFRF HRO HXL Hw. unfold epi_state.
  apply (JA_flag_carve segs HTOP AInv CST XGL ALA HCST HXGL LFLAG NPH Kc rho0 (P0_hl CST FB FF) FB FF BX PTrue HKc HBX HNP
           tv fr_hl bd ANone 0%nat 160%positive 1 170%positive (shadow_reopen_stateA Y (ax_X Y) hG 0 16) rho tp w eq_refl ltac:(lia)).
  - exact Hbase.
  - exact Hwf2.
  - intros Ai rho1 tp1 md1 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR. cbn [shadow_reopen_stateA ax_S ss_facts ss_objs ax_X] in HF |- *. split.
    + intros o a Ho Hr. apply in_app_or in Ho as [Ho|[<-|[]]].
      * exact (siteH Ai rho _ tv fr_hl _ rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HN HD HZ HFR HRO o a Ho Hr).
      * right. right. exact (shobj_range_hse hG 160 128 0 16 rho _ a sz_rng ltac:(lia) ltac:(cbn; lia) HF HFRF Hr).
    + exact (proj2 (proj2 (siteX Ai rho _ tv fr_hl (Some 0%nat) _ _ rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HBf HFF HN HD HZ HFR HXL))).
  - apply (JA_shadow_reopen segs HTOP AInv CST XGL ALA HCST HXGL LFSH NPH Kc rho0 (P0_hl CST FB FF) FB FF BX PTrue HKc HBX HNP
             tv fr_hl bd ANone 0%nat 160%positive 1 170%positive hG 0 16 Y (ax_X Y) rho tp w eq_refl ltac:(lia) Hbase ltac:(lia)
             ltac:(change (fs_frame_size 1) with 128; lia) Hfe (fun r H => H) Hwf1); [|exact Hw].
    intros Ai rho1 tp1 md1 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR. split.
    + exact (siteF Ai rho _ tv fr_hl _ rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HN HD HZ HFR HRO).
    + intros r y Hr Hy. left. exact (proj1 (siteX Ai rho _ tv fr_hl (Some 0%nat) _ _ rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HBf HFF HN HD HZ HFR HXL) r y Hr Hy).
Qed.

Lemma X_f7 : ltac2:(tb__ "0|6|
S8S8Sf8S14S2bS4dQ40A1A1M0S6G0S0S13SdR7A1S17SeaA1A3S0S2dScS30S15S20SbS77A1S78A2S30S15S18S21S77A1S17S52S4fZ2M1Z3dA2Z1A2A1A2S32S15A1A3A3S16S9R8A1A1A2S2eA3S0S2dS1eS9Se2R9SaR9A1S77Z0Z10M2A5A1A1S2eA3S0S2dS1eS9S89RaA1A1A1S2eA3S0S2dS82S16S9RbA1A1A1S2eA3S0S2dS84S16S9RcA1A1A1S2eA3S0S2dSe1S16S9RdA1M3A1S8bS58S34S31A1Sc7S19G3A1A6S2eA3S0S2dSe3VXGL;S16S9ReA1M4A1S8bS58S33S31U0A2S19G4A1Sc8SaReA1A8S2eA3S0S8S89RfA1ReA3S0Sf8S127S76S9RfA1S9S91A1A3ReA3S0S2dS11R10S91RfA3S2eA3S0S2dSf9R10S76A2S2eA3S0S2dS10dS76S1cS9R12A1A1A2S2eA3S0S2dS41S1cS9R13A1A1SaeS8bSa9S5aS72A2M5A2A2S2eA3S0S2dSf1R13S8bSb6A3S2eA3S0S2dS48R14S58S58A3S2eA3S0S2dSc2S16S9R16A1A1Sc0R15S30SbeS7eZ48Sb8A2S32SbeA1A3A2G5A3S2eA3S4eS51G2S4fG1Z40A2A2R13A2VTR;S54S4cVJAv;S8fA1R19R16R15A5VFAM;R14R13A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Ftp0;Fb;Ftp;Frho;Fs;FZ;FX;").
Proof.
  intros X Z s rho tp b tp0 Hbase Hfe Hwf1 Hwf2 HB HFRF HRO HXL HZ Hs He Hid Hnp Hnb Htv Hfr Hbd Hb.
  unfold ndT, ndF, tvL, tvI. eapply TR_pre; [intros w Hw; exact (SPA_swap2 _ _ [] _ _ _ _ _ _ Hw)|]. change [(pD, kb 12 pK); (lc_d, kb 4 lc_k)] with tvN.
  eapply TR_pre; [|apply (REENTER C_epf ndEf (14, z0) (rho_sub rho s)); [innth 34 | rewrite emeas_z0; lia]].
  intros w Hw. unfold ndEf, ndF.
  apply (SPA_entails_JA segs AInv CST XGL ALA NPH Kc rho0 (P0_hl CST FB FF) FB FF BX PTrue HKc Z C_epf s (NDA tvN fr_hl (bdL pK pT0) ANone) (NDA tvY fr_hl [PROG 72 yCUR] ANone) rho tp w
           He Hid Hnp Hnb Htv Hfr Hbd eq_refl).
  rewrite <- HZ. exact (epi_glue X tvN (bdL pK pT0) rho tp w Hbase Hfe Hwf1 Hwf2 HB HFRF HRO HXL Hw).
Qed.
Definition s_f7a : wsub := Eval vm_compute in infer_sub NPH (ax_S Z_f7a) (ax_S C_epf).
Definition s_f7b : wsub := Eval vm_compute in infer_sub NPH (ax_S Z_f7b) (ax_S C_epf).
Lemma XH_X_f7a : ltac2:(tb__ "0|1|
S14S2bS4dQ40A1A1M0S6G0S4eS51Z10S4fZ2Z40A2A2R2A2VTR;S54S4cVJAv;S8fA1Sa1R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply (X_f7 X_f7a Z_f7a s_f7a rho tp b tp0); [vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr| exact Z_f7a_eq |vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr| exact Hb].
Qed.
Lemma XH_X_f7b : ltac2:(tb__ "0|1|
S14S2bS4dQ40A1A1M0S6G0S4eS51Z10S4fZ2Z40A2A2R2A2VTR;S54S4cVJAv;S8fA1Sa2R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply (X_f7 X_f7b Z_f7b s_f7b rho tp b tp0); [vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr| exact Z_f7b_eq |vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr| exact Hb].
Qed.

Lemma X_X_rl : ltac2:(tb__ "0|7|
S8S8S8S2bS2cS13S13A2A1S2bSbeA1S14S2bS4dQ40A1A1M0S6G0S6S0S35S8A1SfeRaS30SffS100Sb4A1S32SffA1A3A2S33S8R9A2A3S0S8S10RaS129S9RaA1M1SbbS1bU15M2S19G1A1A3A2A2R9A3S0S2dSe4Pa0PaaS77Z1M3SbcS1bG2S19S9RbA1A1A3A5S2eA3S0S2dScS30S15S20SbS77A1S78A2S30S15S18S21S77A1S17S52S4fZ2M4Z3dA2G3A2A1A2S32S15A1A3A3S16S9RcA1A1A2S2eA3S0S2dS41S1cS9RdA1A1S3cRbS58RaS3bA4A2S2eA3Sc4S2cS2cS8S3aA2M5S2cS6S13A2M6A2S2fG5G6S2fS8S3aRdS3cRcS32S2cS2cS13S6A2S13A2A1RbS3bA4A4S2fS6S13R6S8cA4A4S88A3S4eZ0R7A2S4eS51S53R8G3A2S4fG4Z40A2A2RaA2VTR;S54S4cVJAv;S3cRfS58ReS3bA4A1R12RdRcA5VFAM;RbRaA2A2F_;F_;F_;F_;F_;F_;F_;F_;Frk;Ftp0;Fb;Ftp;Frho;Fbd;Ftv;FC;FX1;FX;").
Proof.
  intros X X1 C tv bd rho tp b tp0 rk HX1 HC HR Hfe Hnb HinC Hrk Hb.
  apply (TR_pre (fun w => exists rho', SPA segs (JAv (NDA tv [] bd ANone)) C rho' tp w)).
  { intros [tr [ms md]] Hw. pose proof (SPA_axforms segs _ [AXSelect sel_rel] rho X X1 tp _ HX1 Hw) as Hw1.
    exists (rho_absorb rho (skipn 21 (ss_objs (ax_S X1))) (vms md tp ms)). rewrite <- HC.
    change (ax_setS X1 (set_objs (ax_S X1) (firstn 21 (ss_objs (ax_S X1))))) with (drop_lastA X1 (firstn 21 (ss_objs (ax_S X1)))).
    change (@nil (sv * Z * sv)) with (remove_nth 0 fr_hl).
    apply (JA_release_inline segs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nn.Lib_arena_alloc.HTOP_ok AInv CST XGL ALA HCST HXGL LFLAG LFSH NPH Kc rho0 (P0_hl CST FB FF) FB FF BX PTrue HKc HBX HNP
             tv fr_hl bd ANone 0%nat 160%positive 1 170%positive hG X1 (firstn 21 (ss_objs (ax_S X1))) (skipn 21 (ss_objs (ax_S X1))) rho tp tr ms md);
      [reflexivity | lia | symmetry; apply firstn_skipn | exact HR | exact Hfe | exact Hnb | intros A1 A2 _; exact I | exact Hw1]. }
  apply TR_exw. intros rho'. apply (REENTER C (NDA tv [] bd ANone) (rk, z0)); [exact HinC | rewrite emeas_z0; lia].
Qed.
Lemma XH_X_rlo : ltac2:(tb__ "0|1|
S14S2bS4dQ40A1A1M0S6G0S4eS51ZcS4fZ2Z40A2A2R2A2VTR;S54S4cVJAv;SadA1Sa7R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. unfold ndEo, ndF. apply (X_X_rl X_rlo _ C_rlo _ _ rho tp b tp0 10 X_rlo_eq); [vmr|vmr|vmr|vmr| innth 37 | lia | lia].
Qed.
Lemma XH_X_rlf : ltac2:(tb__ "0|1|
S14S2bS4dQ40A1A1M0S6G0S4eS51ZcS4fZ2Z40A2A2R2A2VTR;S54S4cVJAv;SacA1Sa6R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. unfold ndEf, ndF. apply (X_X_rl X_rlf _ C_rlf _ _ rho tp b tp0 10 X_rlf_eq); [vmr|vmr|vmr|vmr| innth 36 | lia | lia].
Qed.

Lemma XH_E_sm : ltac2:(tb__ "0|1|
S14S2bS4dQ40A1A1M0S6G0S4eS51Z62S4fZ2Z40A2A2R2A2VTR;S54S4cVJAv;S5eA1S69R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. unfold nd0, ND, tv_hl. eapply TR_pre; [intros w Hw; exact (SPA_swap2 _ _ [] _ _ _ _ _ _ Hw)|].
  change (NDA [(lc_d, kb 4 lc_k); (li_d, kb 12 li_k)] [] (bd_hl li_n li_k lc_n lc_k tI) ANone) with nd0'.
  apply TR_facts. intros HF.
  apply (smalloc_callT segs AE_A AInv CST XGL ALA HCST HXGL NPH Kc rho0 (P0_hl CST FB FF) FB FF BX PTrue HKc TR TR_facts TR_ex TR_pre TR_callP
           1 E_sm0 s_sm R_sm rho tp nd0' 160 170 (FAM b tp0) CSM).
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
    cbn [nd_tv nd_fr nd0' ND] in HN, HD, HZ, HFR |- *.
    split; [|split].
    + exact (siteP Ai rho _ (tvI li_d li_k lc_d lc_k) [] None R_sm rho1 tp1 md1 HM HF' ltac:(vmr) Hav HP0 HT HTK HBf HFF HN HD HZ HFR ltac:(vmr)).
    + exact (proj1 (proj2 (siteX Ai rho _ (tvI li_d li_k lc_d lc_k) [] None (ss_objs (ax_S E_sm0)) (ax_X E_sm0) rho1 tp1 md1 HM HF' ltac:(vmr) Hav HP0 HT HTK HBf HFF HN HD HZ HFR ltac:(vmr)))).
    + split; [change (wsub_get s_sm 12) with (SLit 96); rewrite uval_lit by lia; change (fs_frame_size 1) with 128; lia|].
      unfold ffpairs. change (map (fun y : Z * Z * Z => fst y) FF) with (map fst FF). rewrite HC0. cbn. lia.
  -
    intros rho' tp'. rewrite T_sm_eq.
    eapply TR_pre with (P := SPA segs (JAv ndP) T_sm1 rho' tp').
    { intros w Hw. exact (SPA_axforms segs _ [AXSelect sel_sm] rho' T_sm T_sm1 tp' w T_sm1_eq Hw). }
    apply (TR_pre (fun w => exists rho2, SPA segs (JAv ndP) C_pro rho2 tp' w)).
    { intros w Hw.
      destruct (JA_frame_open segs HTOP AInv CST XGL ALA HCST HXGL LFLAG NPH Kc rho0 (P0_hl CST FB FF) FB FF BX PTrue HKc HBX HNP
                  (tvI li_d li_k lc_d lc_k) fr_hl (bd_hl li_n li_k lc_n lc_k tI) ANone 0%nat 160 1 170
                  T_sm1 objs_sm1 (X_hl li_d li_k lc_d lc_k) [] rho' tp' w eq_refl ltac:(lia) eq_refl T_sm1_objs T_sm1_X
                  ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) eq_refl ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc)) as (rho2 & _ & Hw2); [| exact Hw |].
      - intros Ai rho1 tp1 md1 HF2 HP0 Hav HM HT HTK HBf HFF HN HDt HZt HFR. rewrite app_nil_r.
        exact (proj1 (siteX Ai rho' _ (tvI li_d li_k lc_d lc_k) fr_hl (Some 0%nat) (ss_objs (ax_S T_sm1)) (X_hl li_d li_k lc_d lc_k) rho1 tp1 md1 HM HF2 ltac:(vmr) Hav HP0 HT HTK HBf HFF HN HDt HZt HFR ltac:(vmr))).
      - exists rho2. rewrite app_nil_r in Hw2. rewrite C_pro0_eq in Hw2. rewrite <- C_pro_eq.
        apply (SPA_x_len0 segs (JAv ndP) C_pro0 160 5 rho2 tp' w); [vmr | lia | vmr | exact Hw2]. }
    apply TR_exw. intros rho2. apply (REENTER C_pro ndP (96, z0)); [innth 1 | rewrite emeas_z0; lia].
Qed.

Lemma X_P_ok : ltac2:(tb__ "0|1|
S14S2bS4dQ40A1A1M0S6G0VTR;S54S4cVJAv;S99A1S93R4R3A5VFAM;R2R1A2A2Ftp0;Fb;Ftp;Frho;").
Proof. intros. apply POST. innth 1. Qed.
Lemma X_P_fail : ltac2:(tb__ "0|1|
S14S2bS4dQ40A1A1M0S6G0VTR;S54S4cVJAv;S98A1S92R4R3A5VFAM;R2R1A2A2Ftp0;Fb;Ftp;Frho;").
Proof. intros. apply POST. innth 0. Qed.

Lemma exits_okT : ltac2:(tb__ "0|3|
S8S3aS2cS6S13A2M0S14S2bS4dQ40A1A1M1G1Sc4S2cS2cS8S3aA2M2G0A2S2fG2G0S2fS8S3aR6R5A4R4A4SaaA3VTR;S54S4cVJAv;R6A1R7R4R3A5VFAM;S3dS2fG2G0S2fS8S3aR7R6A4R5A4R4A2R2A2A2F_;Ftp0;Ftp;Frho;FrvX;FndX;FX;").
Proof.
  intros X ndX rvX rho tp tp0 Hin. cbn [In exitsL] in Hin.
  destruct Hin as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[]]]]]]]]]]]]]]]]]]]]]]]]]];
    injection H as <- <- <-.
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
  - apply XH_X_fp0. rewrite emeas_z0. lia.
  - apply XH_X_fp1. rewrite emeas_z0. lia.
  - apply XH_X_f7a. rewrite emeas_z0. lia.
  - apply XH_X_f7b. rewrite emeas_z0. lia.
  - apply XH_X_ok0. rewrite emeas_z0. lia.
  - apply XH_E_da2. rewrite emeas_z0. lia.
  - apply XH_E_vc. rewrite emeas_z0. lia.
  - apply XH_X_e8k. rewrite emeas_z0. lia.
  - apply XH_X_e8g. rewrite emeas_z0. lia.
  - apply XH_X_f2a. rewrite emeas_z0. lia.
  - apply XH_X_f2b. rewrite emeas_z0. lia.
  - apply XH_X_rlf. rewrite emeas_z0. lia.
  - apply XH_X_rlo. rewrite emeas_z0. lia.
  - apply X_P_fail.
  - apply X_P_ok.
Qed.
End X.

Section Safety.
Variable ok : world -> Prop.
Hypothesis Hok : ltac2:(tb__ "0|0|
S4bS4cVKc;Vok;A3").
Hypothesis AC : ltac2:(tb__ "0|0|
S11eS4cS11bVAInv;VCST;VXGL;A5").

Theorem handle_l_sum : ltac2:(tb__ "0|0|
S2bS4dQ40A1A1SdeS4cVok;S54S4cS45VAInv;VCST;VXGL;VKc;S81VCST;VFB;VFF;A3VFB;VFF;VBX;S3eS5eAaS63Vrho0;R1A5Sd5S4cS76Vrho0;R1Sf4A5A4Ftp0;").
Proof.
  intros tp0.
  eapply triple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_sound_JA segs AInv CST XGL NPH Kc rho0 (P0_hl CST FB FF) FB FF BX PTrue HKc ALA FUEL_hl cutpcs_hl NPH
                (map edropA cutsL) (map edropA exitsL) ok (Q tp0) Hok (ejcertA_jcertA segs NPH _ _ _ _ _ ejcertL_ok))
         with (ndT := nd0); [|left; reflexivity].
       intros X ndX rho tp Hin. apply in_map_iff in Hin as ([[X' nd'] rv] & E0 & Hin). cbn in E0. injection E0 as <- <-.
       apply (exits_okT (triple segs ok) (fun _ _ w => SPfamGTA segs (map nI (map edropA cutsL)) w \/ Q tp0 w)
                (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok) (@triple_ex segs ok) (TRs_pureP segs ok) (call_soundPA3 segs ok)) with (rvX := rv) (tp0 := tp0).
       - intros FBc FFc BXc rho1 tp1 HB0. apply (VNP.vec_reserveN_sum AInv CST XGL ALA HCST HXGL Kc HKc FBc FFc BXc HB0 rho1 ok Hok AC tp1).
       - intros Ai rho1 tp1. apply (aca_stack_malloc _ _ _ _ _ AC 1 ltac:(cbn; tauto)); [exact HKc|]. eapply ok_frameA_of_K; [exact Hok|]. intros r p t m (_ & K & _). exact K.
       - intros Cl s R rho1 tp1 nd Q' He Hc Hn Hb Hf Hk.
         apply (pure_callA segs AInv CST XGL NPH Kc rho0 (P0_hl CST FB FF) FB FF BX PTrue HKc ALA ok Cl Pre_pc s R Posts_pc rho1 tp1 nd Q'); try assumption.
         intros rho2 tp2. apply parse_corner_sum; [apply frozen_ok_frameA; exact Hok | apply (frozen_stable NF (ss_next (ax_S Cl)) nd rho1); [apply Pos.leb_le; exact Hn | exact Hb]].
       - intros Cl s R rho1 tp1 nd Q' He Hc Hn Hb Hf Hk.
         apply (pure_callA segs AInv CST XGL NPH Kc rho0 (P0_hl CST FB FF) FB FF BX PTrue HKc ALA ok Cl Pre_da s R Posts_da rho1 tp1 nd Q'); try assumption.
         intros rho2 tp2. apply diag_append_sum; [apply frozen_ok_frameA; exact Hok | apply (frozen_stable NF (ss_next (ax_S Cl)) nd rho1); [apply Pos.leb_le; exact Hn | exact Hb]].
       - intros T nd rv' rho1 tp1 b tp2 HinT _. apply (reenter_cutJA segs AInv CST XGL NPH Kc rho0 (P0_hl CST FB FF) FB FF BX PTrue ok (map edropA cutsL) T nd).
         apply in_map_iff. exists (T, nd, rv'). auto.
       - intros P nd rho1 tp1 b tp2 HinP. apply (exit_postGA segs AInv CST XGL NPH Kc (P0_hl CST FB FF) FB FF BX PTrue ok rho0 tp0 nd Posts_hlJ P). exact HinP.
       - exact Hin. }
  intros w Hw. apply JA_pre_intro. exact Hw.
Qed.
End Safety.

Section Existence.
Hypothesis ACX : ltac2:(tb__ "0|0|
S11fS4cS11bVAInv;VCST;VXGL;A5").

Theorem handle_l_sum_ex : ltac2:(tb__ "0|0|
S2bS4dQ40A1A1SddS4cS54S4cS45VAInv;VCST;VXGL;VKc;S81VCST;VFB;VFF;A3VFB;VFF;VBX;S3eS5eAaS63Vrho0;R1A5Sd5S4cS76Vrho0;R1Sf4A5A3Ftp0;").
Proof.
  intros tp0.
  eapply etriple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_complete_JA segs AInv CST XGL NPH Kc rho0 (P0_hl CST FB FF) FB FF BX PTrue HKc ALA FUEL_hl cutpcs_hl NPH cutsL exitsL (Q tp0) ejcertL_ok)
         with (ndT := nd0) (rv := (100, z0)); [|left; reflexivity].
       intros X ndX rv rho tp Hin.
       apply (exits_okT (etriple segs) (fun b _ w => SPfamETA segs (map (enodeIA AInv CST XGL NPH Kc rho0 (P0_hl CST FB FF) FB FF BX PTrue) cutsL) b w \/ Q tp0 w)
                (TRe_facts segs) (TRe_ex segs) (TRe_pre segs) (@etriple_ex segs) (TRe_pureP segs) (call_completePA3 segs)) with (tp0 := tp0).
       - intros FBc FFc BXc rho1 tp1 HB0. apply (VNP.vec_reserveN_sum_ex AInv CST XGL ALA HCST HXGL Kc HKc FBc FFc BXc HB0 rho1 ACX tp1).
       - intros Ai rho1 tp1. apply (acx_stack_malloc _ _ _ _ _ ACX 1 ltac:(cbn; tauto)). exact HKc.
       - intros Cl s R rho1 tp1 nd Q' He Hc Hn Hb Hf Hk.
         apply (pure_callA_ex segs AInv CST XGL NPH Kc rho0 (P0_hl CST FB FF) FB FF BX PTrue HKc ALA Cl Pre_pc s R Posts_pc rho1 tp1 nd Q'); try assumption.
         intros rho2 tp2. apply parse_corner_sum_ex. apply (frozen_stable NF (ss_next (ax_S Cl)) nd rho1); [apply Pos.leb_le; exact Hn | exact Hb].
       - intros Cl s R rho1 tp1 nd Q' He Hc Hn Hb Hf Hk.
         apply (pure_callA_ex segs AInv CST XGL NPH Kc rho0 (P0_hl CST FB FF) FB FF BX PTrue HKc ALA Cl Pre_da s R Posts_da rho1 tp1 nd Q'); try assumption.
         intros rho2 tp2. apply diag_append_sum_ex. apply (frozen_stable NF (ss_next (ax_S Cl)) nd rho1); [apply Pos.leb_le; exact Hn | exact Hb].
       - intros T nd rv' rho1 tp1 b tp2 HinT Hm. apply (ereenter_cutJA segs AInv CST XGL NPH Kc rho0 (P0_hl CST FB FF) FB FF BX PTrue cutsL T nd rv'); [exact HinT | exact Hm].
       - intros P nd rho1 tp1 b tp2 HinP. apply (eexit_postGA segs AInv CST XGL NPH Kc (P0_hl CST FB FF) FB FF BX PTrue rho0 tp0 nd Posts_hlJ P). exact HinP.
       - exact Hin. }
  intros w Hw. apply JA_pre_intro. exact Hw.
Qed.
End Existence.
End Sum.

End Lib_handle_l_pf.

